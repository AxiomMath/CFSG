module

public import CFSG.GH74.Uniqueness.SU.SU8Main
public import CFSG.GH74.Uniqueness.SU.SU8UFrat
public import CFSG.GH74.Uniqueness.SU.SU8UK

public section

namespace CFSG.GH74.Uniqueness.SU.SU8

open Subgroup CFSG.GH74.Uniqueness.Bender CFSG.GH74.Uniqueness.SU.SU8.Setup
  CFSG.GH74.Uniqueness.SU.SU8.UConf

namespace U34

variable {G : Type} [Group G] [Finite G] {z : G} {S L A : Subgroup G}

@[expose] def phiL (hLH : L ≤ Hz z) : ↥L →* ↥(hbarImage (Hz z) L) :=
  ((bar (Hz z)).comp (Subgroup.inclusion hLH)).codRestrict _ (fun l => bar_mem_hbarImage l.2)

omit [Finite G] in
theorem phiL_surjective (hLH : L ≤ Hz z) : Function.Surjective (phiL hLH) := by
  intro y
  obtain ⟨x, hxL, hxy⟩ := mem_hbarImage.mp y.2
  exact ⟨⟨x, hxL⟩, Subtype.ext hxy⟩

theorem phiL_ker_odd (hLH : L ≤ Hz z) : Odd (Nat.card (phiL hLH).ker) := by
  let j : ↥(phiL hLH).ker →* ↥(pPrimeCore 2 ↥(Hz z)) :=
    ((Subgroup.inclusion hLH).comp (phiL hLH).ker.subtype).codRestrict _ (fun k => by
      have h1 : phiL hLH k.1 = 1 := k.2
      have h2 : bar (Hz z) (Subgroup.inclusion hLH k.1) = 1 := congrArg Subtype.val h1
      exact bar_eq_one_iff.mp h2)
  have hj : Function.Injective j := by
    intro a b hab
    have h1 : Subgroup.inclusion hLH a.1 = Subgroup.inclusion hLH b.1 := congrArg Subtype.val hab
    exact Subtype.ext (Subgroup.inclusion_injective hLH h1)
  exact Odd.of_dvd_nat (odd_card_core (Hz z)) (Subgroup.card_dvd_of_injective j hj)

omit [Finite G] in
theorem conj_mem_Hz {x u g : G} (hx : x * u * x⁻¹ = z) (hg : u * g = g * u) :
    x * g * x⁻¹ ∈ Hz z := by
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  rw [Set.mem_singleton_iff.mp hw, ← hx]
  calc x * u * x⁻¹ * (x * g * x⁻¹) = x * (u * g) * x⁻¹ := by group
    _ = x * (g * u) * x⁻¹ := by rw [hg]
    _ = x * g * x⁻¹ * (x * u * x⁻¹) := by group

omit [Finite G] in
@[expose] def cxHom {x u : G} (hx : x * u * x⁻¹ = z) (R : Subgroup ↥L)
    (hc : ∀ r : ↥R, u * (((r : ↥R) : ↥L) : G) = (((r : ↥R) : ↥L) : G) * u) : ↥R →* ↥(Hz z) where
  toFun r := ⟨x * (((r : ↥R) : ↥L) : G) * x⁻¹, conj_mem_Hz hx (hc r)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by
    simp only [Subgroup.coe_mul]
    group)

omit [Finite G] in
theorem cxHom_injective {x u : G} (hx : x * u * x⁻¹ = z) (R : Subgroup ↥L)
    (hc : ∀ r : ↥R, u * (((r : ↥R) : ↥L) : G) = (((r : ↥R) : ↥L) : G) * u) :
    Function.Injective (cxHom hx R hc) := by
  intro a b hab
  have h1 : x * (((a : ↥R) : ↥L) : G) * x⁻¹ = x * (((b : ↥R) : ↥L) : G) * x⁻¹ :=
    congrArg Subtype.val hab
  have h2 : (((a : ↥R) : ↥L) : G) = (((b : ↥R) : ↥L) : G) := mul_left_cancel (mul_right_cancel h1)
  exact Subtype.ext (Subtype.ext h2)

end U34

open U34 in
theorem Hyp20A.false_of_unitary
    {G : Type} [Group G] [Finite G] {z : G} {S L A : Subgroup G}
    (hyp : Hyp20A z S L A) (hZ : center ↥(hbarImage (Hz z) L) = ⊥) {e : ℕ}
    (hBT : BenderType ↥(hbarImage (Hz z) L) 2 3 e) : False := by
  have o := out203 hyp hZ
  have hLH : L ≤ Hz z := hyp.L_le
  have hcardAL : Nat.card ↥(A ⊓ L) = 4 := by rw [o.act.card_AL]; norm_num
  obtain ⟨⟨u₀, hu₀⟩, hu₀1⟩ : ∃ u : ↥(A ⊓ L), u ≠ 1 := by
    have h1 : 1 < Nat.card ↥(A ⊓ L) := by omega
    exact Subgroup.ne_bot_iff_exists_ne_one.mp ((Subgroup.one_lt_card_iff_ne_bot _).mp h1)
  have hu₀1' : u₀ ≠ 1 := fun h => hu₀1 (Subtype.ext h)
  obtain ⟨x, hxN, hx⟩ := o.trans u₀ hu₀.1 hu₀1' z hyp.z_mem.1 hyp.z_ne_one
  have hA₀ : ∀ a ∈ (A ⊓ L).subgroupOf L, a * a = 1 := by
    intro a ha
    have h1 : (a : G) ∈ A ⊓ L := Subgroup.mem_subgroupOf.mp ha
    exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_one]; exact hyp.A_exp _ h1.1)
  have hA₀card : Nat.card ((A ⊓ L).subgroupOf L) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : A ⊓ L ≤ L)).toEquiv]
    exact hcardAL
  obtain ⟨R, y, d⟩ := UFrat.exists_conf (phiL hLH) (phiL_surjective hLH) (phiL_ker_odd hLH)
    ((A ⊓ L).subgroupOf L) hA₀ hA₀card (fun P => UK.exists_kconf hBT P)
  have hu₀A₀ : (⟨u₀, hu₀.2⟩ : ↥L) ∈ (A ⊓ L).subgroupOf L := Subgroup.mem_subgroupOf.mpr hu₀
  have hc : ∀ r : ↥R, u₀ * (((r : ↥R) : ↥L) : G) = (((r : ↥R) : ↥L) : G) * u₀ := by
    intro r
    have := d.Z_central _ hu₀A₀ r r.2
    exact congrArg Subtype.val this
  let ε : ↥R →* Hbar (Hz z) := (bar (Hz z)).comp (cxHom hx R hc)
  have hε : Function.Injective ε := by
    intro a b hab
    have h1 : (cxHom hx R hc a)⁻¹ * cxHom hx R hc b ∈ pPrimeCore 2 ↥(Hz z) :=
      bar_eq_bar_iff.mp hab
    rw [← map_inv, ← map_mul] at h1
    have hR2 : IsPGroup 2 ↥R := IsPGroup.of_card (n := 6) (by rw [d.card_R]; norm_num)
    obtain ⟨k, hk⟩ := hR2 (a⁻¹ * b)
    have h2 : (cxHom hx R hc (a⁻¹ * b)) ^ (2 ^ k) = 1 := by rw [← map_pow, hk, map_one]
    have h3 : cxHom hx R hc (a⁻¹ * b) = 1 := eq_one_of_mem_odd (odd_card_core (Hz z)) h1 h2
    have h4 : a⁻¹ * b = 1 := cxHom_injective hx R hc (by rw [h3, map_one])
    exact inv_mul_eq_one.mp h4
  have hyfix : (y : G) * u₀ * (y : G)⁻¹ = u₀ := by
    have := d.y_fix _ hu₀A₀
    exact congrArg Subtype.val this
  have hyc : u₀ * (y : G) = (y : G) * u₀ := by
    calc u₀ * (y : G) = ((y : G) * u₀ * (y : G)⁻¹) * (y : G) := by rw [hyfix]
      _ = (y : G) * u₀ := by group
  let yH : ↥(Hz z) := ⟨x * (y : G) * x⁻¹, conj_mem_Hz hx hyc⟩
  have hyb : ∀ r : ↥R, bar (Hz z) yH * ε r * (bar (Hz z) yH)⁻¹ =
      ε ⟨y * (r : ↥L) * y⁻¹, d.y_norm r r.2⟩ := by
    intro r
    show bar (Hz z) yH * bar (Hz z) (cxHom hx R hc r) * (bar (Hz z) yH)⁻¹ =
      bar (Hz z) (cxHom hx R hc ⟨y * (r : ↥L) * y⁻¹, d.y_norm r r.2⟩)
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show x * (y : G) * x⁻¹ * (x * (((r : ↥R) : ↥L) : G) * x⁻¹) * (x * (y : G) * x⁻¹)⁻¹ =
      x * ((y * ((r : ↥R) : ↥L) * y⁻¹ : ↥L) : G) * x⁻¹
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  obtain ⟨hzH, hzc⟩ := mem_centralizerBar.mp hyp.z_mem.2
  have hεz : ε ⟨⟨u₀, hu₀.2⟩, d.Z_le hu₀A₀⟩ = bar (Hz z) ⟨z, hzH⟩ := by
    show bar (Hz z) (cxHom hx R hc ⟨⟨u₀, hu₀.2⟩, d.Z_le hu₀A₀⟩) = bar (Hz z) ⟨z, hzH⟩
    congr 1
    exact Subtype.ext hx
  have hzC : ε ⟨⟨u₀, hu₀.2⟩, d.Z_le hu₀A₀⟩ ∈
      centralizer ((hbarImage (Hz z) L : Subgroup (Hbar (Hz z))) : Set (Hbar (Hz z))) := by
    rw [hεz, Subgroup.mem_centralizer_iff]
    intro k hk
    obtain ⟨l, hlL, rfl⟩ := mem_hbarImage.mp hk
    exact hzc l hlL
  have hZC : ∀ (w : ↥L) (hw : w ∈ (A ⊓ L).subgroupOf L),
      ε ⟨w, d.Z_le hw⟩ ∈
        centralizer ((hbarImage (Hz z) L : Subgroup (Hbar (Hz z))) : Set (Hbar (Hz z))) →
      w = 1 ∨ w = ⟨u₀, hu₀.2⟩ := by
    intro w hw hwC
    have hwAL : (w : G) ∈ A ⊓ L := Subgroup.mem_subgroupOf.mp hw
    have hxw : x * (w : G) * x⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hxN w).mp hwAL.1
    have hxwH : x * (w : G) * x⁻¹ ∈ Hz z := (cxHom hx R hc ⟨w, d.Z_le hw⟩).2
    have hxwC : x * (w : G) * x⁻¹ ∈ centralizerBar (Hz z) L := by
      refine mem_centralizerBar.mpr ⟨hxwH, fun l hl => ?_⟩
      exact Subgroup.mem_centralizer_iff.mp hwC (bar (Hz z) l) (bar_mem_hbarImage hl)
    rcases o.AC_eq hyp ⟨hxw, hxwC⟩ with h1 | h1
    · left
      apply Subtype.ext
      calc (w : G) = x⁻¹ * (x * (w : G) * x⁻¹) * x := by group
        _ = 1 := by rw [h1]; group
    · right
      apply Subtype.ext
      calc (w : G) = x⁻¹ * (x * (w : G) * x⁻¹) * x := by group
        _ = x⁻¹ * z * x := by rw [h1]
        _ = x⁻¹ * (x * u₀ * x⁻¹) * x := by rw [hx]
        _ = u₀ := by group
  have hz1 : (⟨u₀, hu₀.2⟩ : ↥L) ≠ 1 := fun h => hu₀1' (congrArg Subtype.val h)
  have hU := UAbs.UData.of_conf d ε hε (bar (Hz z) yH) hyb
    (K := hbarImage (Hz z) L) hz1 hu₀A₀ hzC hZC
  have hKn : (hbarImage (Hz z) L).Normal := hbarImage_normal hLH hyp.L_normal
  have hKC : hbarImage (Hz z) L ⊓
      centralizer ((hbarImage (Hz z) L : Subgroup (Hbar (Hz z))) : Set (Hbar (Hz z))) = ⊥ := by
    rw [eq_bot_iff]
    intro k hk
    have hmem : (⟨k, hk.1⟩ : ↥(hbarImage (Hz z) L)) ∈ center ↥(hbarImage (Hz z) L) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hk.2 (g : Hbar (Hz z)) g.2)
    rw [hZ, Subgroup.mem_bot] at hmem
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hmem)
  exact UAbs.UData.false_of hU hKC (UH.habel_of_outer_comm _ (UK.outer_comm hBT)) (UK.K6 hBT)

theorem noUnitary : NoUnitaryStmt := by
  intro G _ _ z S L A hyp hZ ⟨e, hBT⟩
  exact hyp.false_of_unitary hZ hBT

end CFSG.GH74.Uniqueness.SU.SU8
