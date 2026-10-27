module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33Spor

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.SR

open CFSG Subgroup

theorem not_isPGroup_of_pow {G : Type*} [Group G] {g : G} {m : ℕ} (hm : Odd m)
    (hg : g ^ m = 1) (h1 : g ≠ 1) : ¬ IsPGroup 2 G := by
  intro hP
  have hc := hP.orderOf_coprime (Nat.coprime_two_left.mpr hm) g
  have h2 : orderOf g = 1 :=
    Nat.Coprime.eq_one_of_dvd hc (orderOf_dvd_of_pow_eq_one hg)
  exact h1 (orderOf_eq_one_iff.mp h2)

theorem not_isPGroup_of_prime_dvd {G : Type*} [Group G] [Finite G] {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (h : q ∣ Nat.card G) : ¬ IsPGroup 2 G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hP
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hP
  rw [hn] at h
  exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h))

theorem not_isPGroup_of_three_dvd {G : Type*} [Group G] [Finite G] (h : 3 ∣ Nat.card G) :
    ¬ IsPGroup 2 G :=
  not_isPGroup_of_prime_dvd Nat.prime_three (by norm_num) h

theorem not_isPGroup_of_le {G : Type*} [Group G] {H K : Subgroup G} (hHK : H ≤ K)
    (hH : ¬ IsPGroup 2 H) : ¬ IsPGroup 2 K :=
  fun hK => hH (hK.to_le hHK)

theorem not_isPGroup_of_surjective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) (hH : ¬ IsPGroup 2 H) : ¬ IsPGroup 2 G :=
  fun hG => hH (hG.of_surjective f hf)

theorem not_isPGroup_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (hH : ¬ IsPGroup 2 H) : ¬ IsPGroup 2 G :=
  fun hG => hH (hG.of_equiv e)

theorem isPGroup_fixedPoints_map {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (a : MulAut Y) (h : IsPGroup 2 ↥(fixedPoints a)) :
    IsPGroup 2 ↥(fixedPoints (MulAut.congr e a)) := by
  have hmem : ∀ y : ↥(fixedPoints (MulAut.congr e a)),
      (e.symm.toMonoidHom.comp (fixedPoints (MulAut.congr e a)).subtype) y ∈ fixedPoints a := by
    intro y
    have hy : e (a (e.symm y)) = y := y.2
    change a (e.symm y) = e.symm y
    rw [← e.symm_apply_apply (a (e.symm y)), hy]
  refine h.of_injective ((e.symm.toMonoidHom.comp
    (fixedPoints (MulAut.congr e a)).subtype).codRestrict _ hmem) ?_
  intro y z hyz
  have h' := congrArg Subtype.val hyz
  exact Subtype.ext (e.symm.injective h')

theorem sporNoTwoFix_of_mulEquiv {s : TauCeti.SporadicName} {P : Type} [Group P]
    (eP : Blueprint.NativeSporadic.Carrier s ≃* P)
    (h : ∀ a : MulAut P, orderOf a = 2 → ¬ IsPGroup 2 ↥(fixedPoints a)) : SporNoTwoFix s := by
  intro Y _ _ ⟨e⟩ a ha hP
  exact h (MulAut.congr (e.trans eP) a) ((orderOf_congr _ a).trans ha)
    (isPGroup_fixedPoints_map (e.trans eP) a hP)

theorem not_isPGroup_fixedPoints_conj {P : Type} [Group P] (hZ : center P = ⊥)
    (hC : ∀ t : P, orderOf t = 2 → ¬ IsPGroup 2 ↥(centralizer ({t} : Set P))) {t : P}
    (ht : orderOf (MulAut.conj t) = 2) : ¬ IsPGroup 2 ↥(fixedPoints (MulAut.conj t)) := by
  rw [← Hin.centralizer_eq_fixedPoints_conj]
  refine hC t ?_
  rw [← orderOf_injective _ (Hin.conj_injective_of_center hZ) t]
  exact ht

theorem forall_of_inner {P : Type} [Group P] (hZ : center P = ⊥)
    (hinn : ∀ a : MulAut P, ∃ t : P, a = MulAut.conj t)
    (hC : ∀ t : P, orderOf t = 2 → ¬ IsPGroup 2 ↥(centralizer ({t} : Set P))) :
    ∀ a : MulAut P, orderOf a = 2 → ¬ IsPGroup 2 ↥(fixedPoints a) := by
  intro a ha
  obtain ⟨t, rfl⟩ := hinn a
  exact not_isPGroup_fixedPoints_conj hZ hC ha

theorem not_isPGroup_fixedPoints_of_conj {M : Type} [Group M] {P : Subgroup M} {a : MulAut P}
    {x : M} (hx : ∀ p : P, ((a p : P) : M) = x * p * x⁻¹)
    (h : ¬ IsPGroup 2 ↥(P ⊓ centralizer ({x} : Set M))) : ¬ IsPGroup 2 ↥(fixedPoints a) := by
  intro hP
  apply h
  have hmem : ∀ z : ↥(P ⊓ centralizer ({x} : Set M)),
      Subgroup.inclusion (inf_le_left : P ⊓ centralizer ({x} : Set M) ≤ P) z ∈ fixedPoints a := by
    intro z
    have hz : (z : M) * x = x * z := mem_centralizer_singleton_iff.mp z.2.2
    change a (Subgroup.inclusion inf_le_left z) = Subgroup.inclusion inf_le_left z
    apply Subtype.ext
    rw [hx]
    change x * (z : M) * x⁻¹ = z
    rw [← hz, mul_inv_cancel_right]
  refine hP.of_injective ((Subgroup.inclusion
    (inf_le_left : P ⊓ centralizer ({x} : Set M) ≤ P)).codRestrict _ hmem) ?_
  intro y z hyz
  have h' := congrArg (fun w : ↥(fixedPoints a) => ((w : P) : M)) hyz
  exact Subtype.ext h'

theorem not_isPGroup_inf_centralizer_conj {M : Type*} [Group M] {H : Subgroup M} {g : M}
    (hg : g ∈ H) {t : M} (h : ¬ IsPGroup 2 ↥(H ⊓ centralizer ({t} : Set M))) :
    ¬ IsPGroup 2 ↥(H ⊓ centralizer ({g * t * g⁻¹} : Set M)) := by
  intro hP
  apply h
  have hmem : ∀ z : ↥(H ⊓ centralizer ({t} : Set M)),
      g * (z : M) * g⁻¹ ∈ H ⊓ centralizer ({g * t * g⁻¹} : Set M) := by
    intro z
    refine Subgroup.mem_inf.mpr ⟨H.mul_mem (H.mul_mem hg z.2.1) (H.inv_mem hg), ?_⟩
    have hz : (z : M) * t = t * z := mem_centralizer_singleton_iff.mp z.2.2
    rw [mem_centralizer_singleton_iff]
    calc g * (z : M) * g⁻¹ * (g * t * g⁻¹) = g * ((z : M) * t) * g⁻¹ := by group
      _ = g * (t * z) * g⁻¹ := by rw [hz]
      _ = g * t * g⁻¹ * (g * z * g⁻¹) := by group
  refine hP.of_injective (((MulAut.conj g).toMonoidHom.comp
    (H ⊓ centralizer ({t} : Set M)).subtype).codRestrict _ hmem) ?_
  intro y z hyz
  have h' : g * (y : M) * g⁻¹ = g * z * g⁻¹ := congrArg Subtype.val hyz
  exact Subtype.ext (by simpa using h')

end CFSG.ComponentClassification.HarrisLit.L33.SR
