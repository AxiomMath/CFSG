module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ExcHyper
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019A1
import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HeisLift
import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcArith

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.PSL2Table
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
open scoped MatrixGroups

theorem dvd_of_lt_card_aut_L2 {F : Type} [Field F] [Finite F]
    (hF : CFSG.GH74.GLS.IVK.L2Field F) {K : Type} [Group K] [Finite K]
    (e : K ≃* CFSG.GH74.GLS.IVK.L2 F) {p r n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime)
    (hpr : p ≠ r) (hFn : Nat.card F = r ^ n) {A : Subgroup (MulAut K)} (hA : IsElemAbelian p A)
    (hcard : p < Nat.card A) : p ∣ n := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (MulAut K) := Finite.of_injective (fun f : MulAut K => (f : K → K))
    (fun f g h => MulEquiv.ext (congrFun h))
  have hpF : ¬ p ∣ Nat.card F := by
    rw [hFn]
    intro hd
    exact hpr ((Nat.prime_dvd_prime_iff_eq hp hr).1 (hp.dvd_of_dvd_pow hd))
  set Δ := CFSG.GH74.GLS.IVK.innDiagSub e with hΔ
  set I := CFSG.GH74.GLS.IVK.innAut K with hI
  haveI hΔn : Δ.Normal := CFSG.GH74.GLS.IVK.innDiagSub_normal e
  have hsup : Δ ⊔ CFSG.GH74.GLS.IVK.fieldAutSub e = ⊤ :=
    CFSG.GH74.GLS.IVK.innDiagSub_sup_fieldAutSub e
  have hrel : I.relIndex Δ = 2 := CFSG.GH74.GLS.IVK.innAut_relIndex_two e hF
  set π : MulAut K →* MulAut K ⧸ Δ := QuotientGroup.mk' Δ with hπ
  have hsurj : Function.Surjective (π.comp (CFSG.GH74.GLS.IVK.fieldAutSub e).subtype) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have hg : g ∈ Δ ⊔ CFSG.GH74.GLS.IVK.fieldAutSub e := hsup ▸ Subgroup.mem_top g
    rw [← SetLike.mem_coe, Subgroup.normal_mul] at hg
    obtain ⟨d, hd, f, hf, rfl⟩ := hg
    refine ⟨⟨f, hf⟩, ?_⟩
    show QuotientGroup.mk f = QuotientGroup.mk (d * f)
    rw [QuotientGroup.eq]
    have := hΔn.conj_mem d hd f⁻¹
    simpa [mul_assoc] using this
  have hΦ : Nat.card (CFSG.GH74.GLS.IVK.fieldAutSub e) = n := by
    have equ : ↥(CFSG.GH74.GLS.IVK.fieldAutSub e) ≃* (F ≃+* F) :=
      (MonoidHom.ofInjective (CFSG.GH74.GLS.IVK.fieldAutHom_injective e)).symm
    rw [Nat.card_congr equ.toEquiv]
    exact CFSG.GH74.GLS.IVK.card_ringAut F r n hr hFn
  have hQdvd : Nat.card (MulAut K ⧸ Δ) ∣ n := hΦ ▸ Subgroup.card_dvd_of_surjective hsurj
  set ρ : ↥A →* MulAut K ⧸ Δ := π.comp A.subtype with hρ
  have hApow : ∀ a : ↥A, a ^ p = 1 := fun a => Subtype.ext (by simpa using hA.2 a a.2)
  have hsplit : Nat.card A = Nat.card ρ.range * Nat.card ρ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker]
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv]
  have hAp : IsPGroup p A := isPGroup_of_isElemAbelian hA
  have hker : Nat.card ρ.ker ≤ p := by
    have hYp : IsPGroup p ↥(A ⊓ Δ) := hAp.to_le inf_le_left
    have hrelY : I.relIndex (A ⊓ Δ) ≤ 2 := by
      have := Subgroup.relIndex_le_of_le_right (H := I) (inf_le_right : A ⊓ Δ ≤ Δ)
        (by rw [hrel]; norm_num)
      rwa [hrel] at this
    obtain ⟨k, hk⟩ := hYp.exists_card_eq
    have hdvd : I.relIndex (A ⊓ Δ) ∣ p ^ k := hk ▸ Subgroup.relIndex_dvd_card I (A ⊓ Δ)
    have hodd : Odd (I.relIndex (A ⊓ Δ)) :=
      Odd.of_dvd_nat ((hp.odd_of_ne_two hp2).pow) hdvd
    have hne0 : I.relIndex (A ⊓ Δ) ≠ 0 := ne_zero_of_dvd_ne_zero (pow_ne_zero k hp.ne_zero) hdvd
    have h1 : I.relIndex (A ⊓ Δ) = 1 := by
      obtain ⟨m, hm⟩ := hodd
      omega
    have hYI : A ⊓ Δ ≤ I := Subgroup.relIndex_eq_one.1 h1
    have hkerI : ρ.ker ≤ (I ⊓ A).subgroupOf A := by
      intro x hx
      have hxΔ : (x : MulAut K) ∈ Δ := (QuotientGroup.eq_one_iff _).1 hx
      exact ⟨hYI ⟨x.2, hxΔ⟩, x.2⟩
    have hle : Nat.card ρ.ker ≤ Nat.card ↥(I ⊓ A) :=
      calc Nat.card ρ.ker ≤ Nat.card ↥((I ⊓ A).subgroupOf A) := Subgroup.card_le_of_le hkerI
        _ = Nat.card ↥(I ⊓ A) := Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    refine hle.trans ?_
    have hinj : Function.Injective (MulAut.conj : K →* MulAut K) :=
      CFSG.GH74.GLS.IVK.conj_injective_of_L2 e
    have hXle : I ⊓ A ≤ (MulAut.conj : K →* MulAut K).range := inf_le_left
    have hmapX' : ((I ⊓ A).comap (MulAut.conj : K →* MulAut K)).map (MulAut.conj : K →* MulAut K) =
        I ⊓ A := by
      rw [Subgroup.map_comap_eq, inf_eq_right.2 hXle]
    have hcardX' : Nat.card ↥((I ⊓ A).comap (MulAut.conj : K →* MulAut K)) = Nat.card ↥(I ⊓ A) := by
      have h : Nat.card ↥(((I ⊓ A).comap (MulAut.conj : K →* MulAut K)).map
          (MulAut.conj : K →* MulAut K)) =
          Nat.card ↥((I ⊓ A).comap (MulAut.conj : K →* MulAut K)) :=
        Subgroup.card_map_of_injective hinj
      rw [hmapX'] at h
      exact h.symm
    set X' : Subgroup K := (I ⊓ A).comap (MulAut.conj : K →* MulAut K) with hX'
    have hX'pow : ∀ x : ↥X', x ^ p = 1 := by
      intro x
      apply Subtype.ext
      apply hinj
      have hx : (MulAut.conj (x : K) : MulAut K) ∈ A := x.2.2
      have := hA.2 _ hx
      simpa [map_pow] using this
    have hX'p : IsPGroup p ↥X' := fun x => ⟨1, by simpa using hX'pow x⟩
    haveI : Group.IsNilpotent ↥X' := hX'p.isNilpotent
    obtain ⟨m, hm⟩ := hX'p.exists_card_eq
    have hX'odd : Odd (Nat.card ↥X') := hm ▸ (hp.odd_of_ne_two hp2).pow
    rw [← hcardX']
    rcases CFSG.GH74.GLS.IVK.Proofs2.ivk_1_2l F hF K e X' hX'odd inferInstance with
      ⟨hcycX, -⟩ | ⟨p', -, -, hdvdF⟩
    · haveI := hcycX
      exact card_le_of_isCyclic_of_pow_eq_one hp.pos hX'pow
    · rcases Nat.eq_zero_or_pos m with h0 | hpos
      · rw [hm, h0, pow_zero]; exact hp.one_lt.le
      · exfalso
        apply hpF
        exact (dvd_pow_self p hpos.ne').trans (hm ▸ hdvdF)
  by_contra hpn
  have hrange : Nat.card ρ.range = 1 := by
    have hRp : IsPGroup p ρ.range := hAp.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
    obtain ⟨k, hk⟩ := hRp.exists_card_eq
    have hdvd : p ^ k ∣ n := hk ▸ (Subgroup.card_subgroup_dvd_card ρ.range).trans hQdvd
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [hk, h0, pow_zero]
    · exact absurd ((dvd_pow_self p hpos.ne').trans hdvd) hpn
  rw [hsplit, hrange, one_mul] at hcard
  omega

section Model

variable {F : Type} [Field F]

private theorem unip_pow (t : F) (k : ℕ) : unip t ^ k = unip ((k : F) * t) := by
  induction k with
  | zero => simp [unip_zero]
  | succ k ih =>
    rw [pow_succ, ih, ← unip_add]
    congr 1
    push_cast
    ring

private theorem mk_unip_pow_char {q : ℕ} [CharP F q] (t : F) :
    (mk (unip t) : PSL(2, F)) ^ q = 1 := by
  rw [← map_pow, unip_pow, CharP.cast_eq_zero, zero_mul, unip_zero, map_one]

private theorem mk_unip_add (s t : F) :
    (mk (unip (s + t)) : PSL(2, F)) = mk (unip s) * mk (unip t) := by
  rw [unip_add, map_mul]

private theorem mk_diag_conj_unip (c : Fˣ) (t : F) :
    (mk (diag c) : PSL(2, F)) * mk (unip t) * (mk (diag c))⁻¹ = mk (unip ((c : F) ^ 2 * t)) := by
  rw [← map_inv, ← map_mul, ← map_mul, diag_conj_unip]

end Model

private theorem sixteen_lt {q n : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hn : 3 ≤ n)
    (hn3 : q = 3 → 5 ≤ n) : 16 * (q - 1) < q ^ n - 1 := by
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  have h4 : q ≠ 4 := by
    rintro rfl
    exact absurd hq (by norm_num)
  rcases (show q = 3 ∨ 5 ≤ q by omega) with rfl | h5
  · have h5 := hn3 rfl
    have : 3 ^ 5 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) h5
    omega
  · have h1 : q ^ 3 ≤ q ^ n := Nat.pow_le_pow_right (by omega) hn
    have h2 : 25 * q ≤ q ^ 3 := by
      rw [pow_succ, pow_two]
      exact Nat.mul_le_mul_right q (by nlinarith)
    omega

theorem false_of_L2_of_card_le {J : Type} [Group J] [Finite J] {F : Type} [Field F] [Finite F]
    (e : J ⧸ Subgroup.center J ≃* CFSG.GH74.GLS.IVK.L2 F) {q n : ℕ} [hq : Fact q.Prime]
    (hq2 : q ≠ 2) (hFn : Nat.card F = q ^ n) (hn : 3 ≤ n) (hn3 : q = 3 → 5 ≤ n)
    (hZ : ¬ q ∣ Nat.card (Subgroup.center J)) {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) (hW17 : Nat.card W ≤ 2 ^ 17) (ρ : J →* MulAut W)
    (hρ : ∀ x : J, x ^ q = 1 → ρ x = 1 → x ∈ Subgroup.center J) : False := by
  classical
  haveI : Finite (MulAut W) := Finite.of_injective (fun f : MulAut W => (f : W → W))
    (fun f g h => MulEquiv.ext (congrFun h))
  have hqp : q.Prime := hq.out
  haveI := Fintype.ofFinite F
  have hFcard : Fintype.card F = q ^ n := by rw [← Nat.card_eq_fintype_card]; exact hFn
  haveI : CharP F q := charP_of_card_eq_prime_pow hFcard
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff F q] at this
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).1 this)
  let π : J →* PSL(2, F) :=
    (CFSG.GH74.GLS.IVK.toPSL e).toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center J))
  have hπ : Function.Surjective π :=
    (CFSG.GH74.GLS.IVK.toPSL e).surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center J := by
    ext x
    rw [MonoidHom.mem_ker]
    change CFSG.GH74.GLS.IVK.toPSL e (QuotientGroup.mk x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hKle : π.ker ≤ Subgroup.center J := hker.le
  have hKq : ¬ q ∣ Nat.card π.ker := by rw [hker]; exact hZ
  have huniq : ∀ {x y : J}, x ^ q = 1 → y ^ q = 1 → π x = π y → x = y :=
    fun hx hy h => eq_of_map_eq_of_pow_eq_one π hKle hKq hx hy h
  have hconjq : ∀ {a b : J}, a ^ q = 1 → (b * a * b⁻¹) ^ q = 1 := fun {a b} ha => by
    rw [conj_pow, ha, mul_one, mul_inv_cancel]
  have hcomm : ∀ {a b : J}, a ^ q = 1 → π a * π b = π b * π a → a * b = b * a := by
    intro a b ha hab
    have h : b⁻¹ * a * b⁻¹⁻¹ = a := by
      refine huniq (hconjq ha) ha ?_
      rw [inv_inv, map_mul, map_mul, map_inv, mul_assoc, hab, inv_mul_cancel_left]
    rw [inv_inv] at h
    calc a * b = b * (b⁻¹ * a * b) := by group
      _ = b * a := by rw [h]
  choose u hu hup using fun t : F => exists_map_eq_pow_eq_one π hπ hKq (mk_unip_pow_char (q := q) t)
  have hu_add : ∀ s t, u (s + t) = u s * u t := by
    intro s t
    have hst : Commute (u s) (u t) := hcomm (hup s) (by
      rw [hu, hu, ← mk_unip_add, ← mk_unip_add, add_comm])
    refine huniq (hup _) ?_ ?_
    · rw [hst.mul_pow, hup, hup, one_mul]
    · rw [map_mul, hu, hu, hu, mk_unip_add]
  have hu0 : u 0 = 1 := by
    have h := hu_add 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  have hu_center : ∀ t, u t ∈ Subgroup.center J → t = 0 := by
    intro t ht
    have h1 : π (u t) = 1 := by rw [← MonoidHom.mem_ker, hker]; exact ht
    rw [hu] at h1
    exact (mk_unip_eq_one_iff h2 t).1 h1
  have hρu : ∀ s t, ρ (u s) = ρ (u t) → s = t := by
    intro s t hst
    have hsub : u s = u (s - t) * u t := by rw [← hu_add, sub_add_cancel]
    have h1 : ρ (u (s - t)) = 1 := by
      rw [hsub, map_mul] at hst
      exact mul_eq_right.1 hst
    exact sub_eq_zero.1 (hu_center _ (hρ _ (hup _) h1))
  obtain ⟨c, hc⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hcord : orderOf c = q ^ n - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hc, Nat.card_units, hFn]
  obtain ⟨h, hh⟩ := hπ (mk (diag c))
  have hconj : ∀ t, h * u t * h⁻¹ = u ((c : F) ^ 2 * t) := by
    intro t
    refine huniq (hconjq (hup t)) (hup _) ?_
    rw [map_mul, map_mul, map_inv, hh, hu, hu, mk_diag_conj_unip]
  have hconjk : ∀ (k : ℕ) (t : F), h ^ k * u t * (h ^ k)⁻¹ = u ((c : F) ^ (2 * k) * t) := by
    intro k
    induction k with
    | zero => intro t; simp
    | succ k ih =>
      intro t
      calc h ^ (k + 1) * u t * (h ^ (k + 1))⁻¹ = h * (h ^ k * u t * (h ^ k)⁻¹) * h⁻¹ := by group
        _ = u ((c : F) ^ (2 * (k + 1)) * t) := by
          rw [ih, hconj]
          congr 1
          ring
  let φ : Multiplicative F →* J :=
    { toFun := fun a => u (Multiplicative.toAdd a)
      map_one' := hu0
      map_mul' := fun a b => hu_add _ _ }
  set A : Subgroup (MulAut W) := (ρ.comp φ).range with hAdef
  have hmemA : ∀ x, x ∈ A ↔ ∃ t, ρ (u t) = x := by
    intro x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨Multiplicative.toAdd a, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨Multiplicative.ofAdd t, rfl⟩
  set g : MulAut W := ρ h with hg
  have hgk : ∀ (k : ℕ) (t : F), g ^ k * ρ (u t) * (g ^ k)⁻¹ = ρ (u ((c : F) ^ (2 * k) * t)) := by
    intro k t
    rw [hg, ← map_pow, ← map_inv, ← map_mul, ← map_mul, hconjk]
  have hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    obtain ⟨s, rfl⟩ := (hmemA a).1 ha
    obtain ⟨t, rfl⟩ := (hmemA b).1 hb
    rw [← map_mul, ← map_mul, ← hu_add, ← hu_add, add_comm]
  have hAq : ∀ a ∈ A, a ^ q = 1 := by
    intro a ha
    obtain ⟨t, rfl⟩ := (hmemA a).1 ha
    rw [← map_pow, hup, map_one]
  have hA1 : A ≠ ⊥ := by
    intro hbot
    have h1 : ρ (u 1) ∈ A := (hmemA _).2 ⟨1, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    have := hρu 1 0 (by rw [h1, hu0, map_one])
    exact one_ne_zero this
  have hnorm : g ∈ Subgroup.normalizer (A : Set (MulAut W)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨t, rfl⟩ := (hmemA x).1 hx
      have := hgk 1 t
      rw [pow_one] at this
      rw [this]
      exact (hmemA _).2 ⟨_, rfl⟩
    · intro hx
      obtain ⟨s, hs⟩ := (hmemA _).1 hx
      have hcne : (c : F) ≠ 0 := c.ne_zero
      have h1 := hgk 1 (((c : F)⁻¹) ^ 2 * s)
      rw [pow_one, show (c : F) ^ (2 * 1) * (((c : F)⁻¹) ^ 2 * s) = s by
        field_simp, hs] at h1
      have hx' : x = ρ (u (((c : F)⁻¹) ^ 2 * s)) := (mul_left_cancel (mul_right_cancel h1)).symm
      rw [hx']
      exact (hmemA _).2 ⟨_, rfl⟩
  have hcomm_iff : ∀ (k : ℕ) (x : MulAut W), g ^ k * x = x * g ^ k ↔ g ^ k * x * (g ^ k)⁻¹ = x :=
    fun k x => (mul_inv_eq_iff_eq_mul).symm
  have hsemi : ∀ k : ℕ, (∃ a ∈ A, a ≠ 1 ∧ g ^ k * a = a * g ^ k) →
      ∀ a ∈ A, g ^ k * a = a * g ^ k := by
    rintro k ⟨a, ha, ha1, hak⟩ b hb
    obtain ⟨t, rfl⟩ := (hmemA a).1 ha
    obtain ⟨s, rfl⟩ := (hmemA b).1 hb
    have ht : t ≠ 0 := by
      rintro rfl
      exact ha1 (by rw [hu0, map_one])
    rw [hcomm_iff, hgk] at hak ⊢
    have h1 := hρu _ _ hak
    have hck : (c : F) ^ (2 * k) = 1 := by
      have : ((c : F) ^ (2 * k) - 1) * t = 0 := by rw [sub_mul, h1, one_mul, sub_self]
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right ht)
    rw [hck, one_mul]
  obtain ⟨d, hd, hcen, hcard⟩ := exists_orbit_two_pow_le hW hq2 hA hAq hA1 hnorm hsemi
  have hc1 : (c : F) ^ (2 * (d * (q - 1))) = 1 := by
    have h1 := hcen _ ((hmemA _).2 ⟨1, rfl⟩)
    rw [hcomm_iff, hgk] at h1
    have := hρu _ _ h1
    rwa [mul_one] at this
  have hdvd : q ^ n - 1 ∣ 2 * (d * (q - 1)) := by
    rw [← hcord]
    apply orderOf_dvd_of_pow_eq_one
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, hc1, Units.val_one])
  have ht := CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.two_le_orderOf_two_zmod (p := q) hq2
  have hle : orderOf (2 : ZMod q) * d ≤ 17 :=
    (Nat.pow_le_pow_iff_right (by norm_num)).1 (hcard.trans hW17)
  have hd8 : d ≤ 8 := by nlinarith
  have hq1 : 0 < q - 1 := by have := hqp.two_le; omega
  have h16 : q ^ n - 1 ≤ 16 * (q - 1) :=
    (Nat.le_of_dvd (by positivity) hdvd).trans (by nlinarith)
  exact absurd h16 (not_le.2 (sixteen_lt hqp hq2 hn hn3))

end CFSG.LocalAnalysis.GLTheoremA.S2019
