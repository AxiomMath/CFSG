module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.TabClass8Split
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19UHSFusion

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.QuasithinUnique.Id2519 CFSG.QuasithinUnique.Id2519.UHS CFSG.Sporadic.Schreier

theorem card_centralizer_of_invol
    {s : PP} (hs2 : s * s = 1) (hs1 : s ≠ 1) {D : Subgroup PP}
    (hD : Nat.card D = 360) (hDle : D ≤ Subgroup.centralizer ({s} : Set PP)) :
    Nat.card (Subgroup.centralizer ({s} : Set PP)) = 2880 := by
  have hord : orderOf (s : Equiv.Perm (Fin 3850)) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [sq]; exact hs2) hs1
  rcases hs_invol_cover s.2 hord with h | h
  · exfalso
    obtain ⟨c, hc, hce⟩ := hsE1_conj _ h
    have hconj : IsConj (⟨hsGen 0, hsGen_mem 0 (by norm_num)⟩ : PP) s :=
      isConj_iff.2 ⟨⟨c, hc⟩, Subtype.ext hce.symm⟩
    have h1 := card_centralizer_of_isConj hconj
    rw [card_centralizer_a0] at h1
    have h2 := Subgroup.card_dvd_of_le hDle
    rw [hD, ← h1] at h2
    norm_num at h2
  · obtain ⟨c, hc, hce⟩ := hsE2_conj _ h
    have hconj : IsConj (⟨hsC, hsC_mem⟩ : PP) s :=
      isConj_iff.2 ⟨⟨c, hc⟩, Subtype.ext hce.symm⟩
    rw [← card_centralizer_of_isConj hconj]
    exact card_centralizer_c

theorem card_alt_six_c8 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem arith_class8 {z h a b i : ℕ} (hz : 0 < z) (hX : 2 ^ b * i = z * 44352000)
    (hi : ¬ 2 ∣ i) (hh : 2 ^ a ∣ h) (hhz : h ∣ z * 2880) : a + 3 ≤ b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hi0 : i ≠ 0 := fun h0 => hi (h0 ▸ dvd_zero 2)
  have h44 : padicValNat 2 44352000 = 9 := by
    have : (44352000 : ℕ) = 2 ^ 9 * 86625 := by norm_num
    rw [this, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
  have h2880 : padicValNat 2 2880 = 6 := by
    have : (2880 : ℕ) = 2 ^ 6 * 45 := by norm_num
    rw [this, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
  have h1 : padicValNat 2 (2 ^ b * i) = b := by
    rw [padicValNat.mul (by positivity) hi0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hi, add_zero]
  have h2 : padicValNat 2 (z * 44352000) = padicValNat 2 z + 9 := by
    rw [padicValNat.mul hz.ne' (by norm_num), h44]
  have h3 : a ≤ padicValNat 2 (z * 2880) := by
    have hdvd : 2 ^ a ∣ z * 2880 := hh.trans hhz
    exact (padicValNat_dvd_iff_le (by positivity)).1 hdvd
  have h4 : padicValNat 2 (z * 2880) = padicValNat 2 z + 6 := by
    rw [padicValNat.mul hz.ne' (by norm_num), h2880]
  rw [hX] at h1
  omega

theorem tabClass8HS
    : TabClass8HS := by
  intro G _ _ X K t hXq ht ht2 hcomm hKcomp hpat P hP htP
  obtain ⟨hA6, ⟨e⟩, l, hl, hlt⟩ := hpat
  set Z : Subgroup ↥X := Subgroup.center ↥X with hZdef
  let π : ↥X →* (↥X ⧸ Z) := QuotientGroup.mk' Z
  let θ : (↥X ⧸ Z) ≃* PP :=
    (e.trans hsPermEquiv).trans (MulEquiv.subgroupCongr hsP_eq_original)
  set c : G := t * l⁻¹ with hcdef
  have hcx : ∀ x ∈ X, c * x = x * c := by
    intro x hx
    calc c * x = t * (l⁻¹ * x * l) * l⁻¹ := by rw [hcdef]; group
      _ = t * (t⁻¹ * x * t) * l⁻¹ := by rw [← hlt x hx]
      _ = x * c := by rw [hcdef]; group
  have hct : t = c * l := by rw [hcdef]; group
  have hcc : c * c * (l * l) = 1 := by
    calc c * c * (l * l) = c * (c * l) * l := by group
      _ = c * (l * c) * l := by rw [hcx l hl]
      _ = (c * l) * (c * l) := by group
      _ = t * t := by rw [← hct]
      _ = 1 := ht2
  have hl2Z : (⟨l * l, X.mul_mem hl hl⟩ : ↥X) ∈ Z := by
    rw [hZdef, Subgroup.mem_center_iff]
    intro g
    refine Subtype.ext ?_
    change (g : G) * (l * l) = l * l * (g : G)
    have hll : l * l = (c * c)⁻¹ := eq_inv_of_mul_eq_one_right hcc
    have hcomm' : Commute (c * c) (g : G) := by
      have h1 := hcx g g.2
      show c * c * g = g * (c * c)
      calc c * c * g = c * (c * g) := by group
        _ = c * (g * c) := by rw [h1]
        _ = (c * g) * c := by group
        _ = (g * c) * c := by rw [h1]
        _ = g * (c * c) := by group
    rw [hll]
    exact (hcomm'.inv_left).eq.symm
  set ℓ : PP := θ (π ⟨l, hl⟩) with hℓdef
  have hℓ2 : ℓ * ℓ = 1 := by
    rw [hℓdef, ← map_mul, ← map_mul]
    have : π (⟨l, hl⟩ * ⟨l, hl⟩) = 1 := (QuotientGroup.eq_one_iff _).2 hl2Z
    rw [this, map_one]
  have hℓ1 : ℓ ≠ 1 := by
    intro h1
    have h2 : π ⟨l, hl⟩ = 1 := θ.injective (by rw [← hℓdef, h1, map_one])
    have h3 : (⟨l, hl⟩ : ↥X) ∈ Z := (QuotientGroup.eq_one_iff _).1 h2
    have hlc : ∀ x ∈ X, x * l = l * x := by
      intro x hx
      have := (Subgroup.mem_center_iff.1 h3) ⟨x, hx⟩
      exact congrArg Subtype.val this
    have hcent : ∀ x ∈ X, t * x = x * t := by
      intro x hx
      rw [hct]
      calc c * l * x = c * (l * x) := by group
        _ = c * (x * l) := by rw [hlc x hx]
        _ = (c * x) * l := by group
        _ = (x * c) * l := by rw [hcx x hx]
        _ = x * (c * l) := by group
    have hle : ⁅X, Subgroup.zpowers t⁆ ≤ ⊥ := by
      rw [Subgroup.commutator_le]
      intro x hx g hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      have hk : x * t ^ k = t ^ k * x :=
        ((Commute.zpow_left (show Commute t x from hcent x hx) k)).eq.symm
      rw [Subgroup.mem_bot, commutatorElement_def, hk]
      group
    rw [hcomm] at hle
    have hone : ∀ x : ↥X, x = 1 := fun x => Subtype.ext (Subgroup.mem_bot.mp (hle x.2))
    have hq := hXq.2.1
    have : Nontrivial (↥X ⧸ Subgroup.center ↥X) := hq.toNontrivial
    obtain ⟨a, b, hab⟩ := exists_pair_ne (↥X ⧸ Subgroup.center ↥X)
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (by rw [hone a', hone b'])
  have hKle : K ≤ X ⊓ Subgroup.centralizer ({t} : Set G) := hKcomp.1
  have hKX : K ≤ X := hKle.trans inf_le_left
  have hcommL : ∀ x ∈ X, (x * t = t * x ↔ x * l = l * x) := by
    intro x hx
    have hxc := hcx x hx
    rw [hct]
    constructor
    · intro h
      have h' : c * (x * l) = c * (l * x) := by
        calc c * (x * l) = (c * x) * l := by group
          _ = (x * c) * l := by rw [hxc]
          _ = x * (c * l) := by group
          _ = (c * l) * x := h
          _ = c * (l * x) := by group
      exact mul_left_cancel h'
    · intro h
      calc x * (c * l) = (x * c) * l := by group
        _ = (c * x) * l := by rw [hxc]
        _ = c * (x * l) := by group
        _ = c * (l * x) := by rw [h]
        _ = c * l * x := by group
  have hKl : ∀ k ∈ K, k * l = l * k := fun k hk =>
    (hcommL k (hKX hk)).1 (Subgroup.mem_centralizer_singleton_iff.mp (hKle hk).2)
  obtain ⟨e6⟩ := hA6
  have hKcard : Nat.card K = 360 := (Nat.card_congr e6.toEquiv).trans card_alt_six_c8
  have hKc1 : ∀ k : ↥K, (∀ k' : ↥K, k' * k = k * k') → k = 1 := by
    intro k hk
    have hmem : e6 k ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨k', rfl⟩ := e6.surjective y
      rw [← map_mul, ← map_mul, hk k']
    rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hmem
    exact e6.injective (by rw [hmem, map_one])
  let f : ↥K →* PP := θ.toMonoidHom.comp (π.comp (Subgroup.inclusion hKX))
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have h1 : π (Subgroup.inclusion hKX k) = 1 := θ.injective (by simpa [f] using hk)
    have h2 : Subgroup.inclusion hKX k ∈ Z := (QuotientGroup.eq_one_iff _).1 h1
    refine hKc1 k fun k' => ?_
    have h3 := (Subgroup.mem_center_iff.1 h2) (Subgroup.inclusion hKX k')
    have h4 : Subgroup.inclusion hKX (k' * k) = Subgroup.inclusion hKX (k * k') := by
      rw [map_mul, map_mul]
      exact h3
    exact Subgroup.inclusion_injective hKX h4
  have hD : Nat.card f.range = 360 := by
    rw [Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv.symm, hKcard]
  have hDle : f.range ≤ Subgroup.centralizer ({ℓ} : Set PP) := by
    rintro _ ⟨k, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have : (Subgroup.inclusion hKX k) * ⟨l, hl⟩ = ⟨l, hl⟩ * (Subgroup.inclusion hKX k) :=
      Subtype.ext (hKl k k.2)
    show θ (π (Subgroup.inclusion hKX k)) * θ (π ⟨l, hl⟩) =
      θ (π ⟨l, hl⟩) * θ (π (Subgroup.inclusion hKX k))
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, this]
  have hC : Nat.card (Subgroup.centralizer ({ℓ} : Set PP)) = 2880 :=
    card_centralizer_of_invol hℓ2 hℓ1 hD hDle
  let Hc : Subgroup ↥X := (Subgroup.centralizer ({t} : Set G)).subgroupOf X
  let g3 : ↥Hc →* PP := θ.toMonoidHom.comp (π.comp Hc.subtype)
  have hg3le : g3.range ≤ Subgroup.centralizer ({ℓ} : Set PP) := by
    rintro _ ⟨h, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hh : (h : ↥X) * ⟨l, hl⟩ = ⟨l, hl⟩ * (h : ↥X) := by
      have h1 : ((h : ↥X) : G) * t = t * ((h : ↥X) : G) :=
        Subgroup.mem_centralizer_singleton_iff.1 h.2
      exact Subtype.ext ((hcommL _ (h : ↥X).2).1 h1)
    show θ (π (h : ↥X)) * θ (π ⟨l, hl⟩) = θ (π ⟨l, hl⟩) * θ (π (h : ↥X))
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hh]
  have hker : Nat.card g3.ker ∣ Nat.card Z := by
    have hmem : ∀ x : ↥g3.ker, ((x : ↥Hc) : ↥X) ∈ Z := by
      intro x
      have h1 : g3 (x : ↥Hc) = 1 := x.2
      have h2 : π ((x : ↥Hc) : ↥X) = 1 := θ.injective (by simpa [g3] using h1)
      exact (QuotientGroup.eq_one_iff _).1 h2
    let ι : ↥g3.ker →* ↥Z := (Hc.subtype.comp g3.ker.subtype).codRestrict Z hmem
    have hι : Function.Injective ι := by
      intro x y hxy
      have h1 := congrArg (fun z : ↥Z => (z : ↥X)) hxy
      exact Subtype.ext (Subtype.ext h1)
    exact Subgroup.card_dvd_of_injective ι hι
  have hHc : Nat.card Hc ∣ Nat.card Z * 2880 := by
    have h1 := Subgroup.card_ker_mul_card_range g3
    rw [← h1]
    have h2 : Nat.card g3.range ∣ 2880 := by
      have := Subgroup.card_dvd_of_le hg3le
      rwa [hC] at this
    exact Nat.mul_dvd_mul hker h2
  obtain ⟨hPX, hP2, hPodd⟩ := hP
  have hXcard : Nat.card ↥X = Nat.card Z * 44352000 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
    have h2 : Nat.card (↥X ⧸ Z) = 44352000 := by
      rw [Nat.card_congr θ.toEquiv, card_PP]
    rw [h1, h2, mul_comm]
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card).1 hP2
  have hidx : Nat.card P * (P.subgroupOf X).index = Nat.card ↥X := by
    have h1 := Subgroup.card_mul_index (P.subgroupOf X)
    have h2 : Nat.card (P.subgroupOf X) = Nat.card P :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPX).toEquiv
    rwa [h2] at h1
  have hC2P : Subgroup.centralizer ({t} : Set G) ⊓ P ≤ P := inf_le_right
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 (hP2.to_le hC2P)
  have h2a : 2 ^ a ∣ Nat.card Hc := by
    have h1 : Nat.card Hc = Nat.card (Subgroup.centralizer ({t} : Set G) ⊓ X : Subgroup G) := by
      have h0 : Hc = (Subgroup.centralizer ({t} : Set G) ⊓ X).subgroupOf X :=
        (Subgroup.inf_subgroupOf_right _ _).symm
      rw [h0]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    rw [h1, ← ha]
    exact Subgroup.card_dvd_of_le (inf_le_inf_left _ hPX)
  have hz : 0 < Nat.card Z := Nat.card_pos
  have hab : a + 3 ≤ b := by
    refine arith_class8 hz ?_ hPodd h2a hHc
    rw [← hb, hidx, hXcard]
  have hr := Subgroup.relIndex_mul_card (H := Subgroup.centralizer ({t} : Set G)) (K := P)
  rw [ha, hb] at hr
  have hpow : 2 ^ b = 2 ^ (b - a) * 2 ^ a := by
    rw [← pow_add, Nat.sub_add_cancel (by omega)]
  have hr2 : (Subgroup.centralizer ({t} : Set G)).relIndex P = 2 ^ (b - a) :=
    Nat.eq_of_mul_eq_mul_right (by positivity) (hr.trans hpow)
  rw [hr2]
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ (b - a) := Nat.pow_le_pow_right (by norm_num) (by omega)

end CFSG.QuasithinUnique.DoubleA3
