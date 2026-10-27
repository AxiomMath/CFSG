module

public import CFSG.CharacterTheory.Semidihedral.NormalForm

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.S16A

open Subgroup CFSG.Open

variable {Q : Type*} [Group Q] [Finite Q]

namespace Grp

theorem card_centralizer_le {S : Subgroup Q} (hS2 : S.index = 2) (y : Q) :
    Nat.card ↥(centralizer ({y} : Set Q)) ≤ 2 * Nat.card ↥(S ⊓ centralizer ({y} : Set Q)) := by
  haveI : S.Normal := normal_of_index_eq_two hS2
  have h1 : S.relIndex (centralizer ({y} : Set Q)) ≤ 2 :=
    Nat.le_of_dvd (by norm_num) (hS2 ▸ relIndex_dvd_index_of_normal S _)
  calc Nat.card ↥(centralizer ({y} : Set Q))
      = S.relIndex (centralizer ({y} : Set Q)) * Nat.card ↥(S ⊓ centralizer ({y} : Set Q)) :=
        (relIndex_mul_card (H := S) (K := centralizer ({y} : Set Q))).symm
    _ ≤ 2 * Nat.card ↥(S ⊓ centralizer ({y} : Set Q)) := Nat.mul_le_mul_right _ h1

theorem card_le_two_mul_ncard_conjugatesOf {S : Subgroup Q} (hS2 : S.index = 2) {y : Q}
    (hC : Nat.card ↥(S ⊓ centralizer ({y} : Set Q)) = 2) :
    Nat.card S ≤ 2 * (conjugatesOf y).ncard := by
  have h1 := Subgroup.index_centralizer_eq_ncard y
  have h2 := Subgroup.card_mul_index (centralizer ({y} : Set Q))
  have h3 := card_centralizer_le hS2 y
  have h4 := Subgroup.card_mul_index S
  rw [hS2] at h4
  rw [hC] at h3
  rw [h1] at h2
  have h5 : Nat.card Q ≤ 4 * (conjugatesOf y).ncard := by
    rw [← h2]
    calc Nat.card ↥(centralizer ({y} : Set Q)) * (conjugatesOf y).ncard
        ≤ (2 * 2) * (conjugatesOf y).ncard := Nat.mul_le_mul_right _ h3
      _ = 4 * (conjugatesOf y).ncard := by norm_num
  omega

theorem exists_mem_of_isConj {S : Subgroup Q} (hS2 : S.index = 2) {x y : Q} (hx : x ∉ S)
    (h : IsConj x y) : ∃ u ∈ S, u * x * u⁻¹ = y := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  by_cases hcS : c ∈ S
  · exact ⟨c, hcS, hc⟩
  · refine ⟨c * x, ?_, ?_⟩
    · rw [mul_mem_iff_of_index_two hS2]
      exact iff_of_false hcS hx
    · rw [← hc]
      group

theorem conjugatesOf_subset_compl {S : Subgroup Q} [hN : S.Normal] {x : Q} (hx : x ∉ S) :
    conjugatesOf x ⊆ (S : Set Q)ᶜ := by
  intro z hz hzS
  obtain ⟨c, hc⟩ := isConj_iff.1 hz
  apply hx
  have h := hN.conj_mem z hzS c⁻¹
  rw [← hc] at h
  simpa [mul_assoc] using h

theorem inf_centralizer_eq_of_isMulCommutative {S : Subgroup Q} (hS : IsMulCommutative S)
    (hS2 : S.index = 2) {t : Q} (htS : t ∉ S) {x : Q} (hx : x ∉ S) :
    S ⊓ centralizer ({x} : Set Q) = S ⊓ centralizer ({t} : Set Q) := by
  haveI := hS
  have hc : x * t⁻¹ ∈ S := by
    rw [mul_mem_iff_of_index_two hS2]
    exact iff_of_false hx (by simpa using htS)
  have hxc : x = (x * t⁻¹) * t := by group
  generalize x * t⁻¹ = c at hc hxc
  subst hxc
  ext u
  simp only [mem_inf, mem_centralizer_singleton_iff]
  refine and_congr_right fun huS => ?_
  have huc : u * c = c * u := setLike_mul_comm (s := S) huS hc
  rw [← mul_assoc u c t, huc, mul_assoc c u t, mul_assoc c t u]
  exact mul_right_inj c

theorem index_zpowers_r_one (n : ℕ) [NeZero n] :
    (zpowers (DihedralGroup.r (1 : ZMod n))).index = 2 := by
  have h1 := Subgroup.card_mul_index (zpowers (DihedralGroup.r (1 : ZMod n)))
  rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one, DihedralGroup.nat_card] at h1
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  exact Nat.eq_of_mul_eq_mul_left hn (by rw [h1, mul_comm])

theorem exists_cyclic_index_two_of_equiv {G : Type*} [Group G] (e : Q ≃* G) (g : G)
    (hg : (zpowers g).index = 2) : ∃ R : Subgroup Q, IsCyclic R ∧ R.index = 2 := by
  refine ⟨zpowers (e.symm g), inferInstance, ?_⟩
  have h : zpowers (e.symm g) = (zpowers g).map (e.symm : G →* Q) :=
    (MonoidHom.map_zpowers (e.symm : G →* Q) g).symm
  rw [h]
  exact (Subgroup.index_map_equiv (zpowers g) e.symm).trans hg

theorem mem_of_mem_cyclic_index_two {R S : Subgroup Q} (hR : IsCyclic R) (hS2 : S.index = 2)
    (h4 : 4 ∣ Nat.card R) {y : Q} (hyR : y ∈ R) (hy2 : y * y = 1) : y ∈ S := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := R)
  have hord : orderOf g = Nat.card R := orderOf_eq_card_of_forall_mem_zpowers hg
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨y, hyR⟩)
  have hsq : g ^ (k + k) = 1 := by
    rw [zpow_add, hk]
    exact Subtype.ext (by simpa using hy2)
  have hdvd : (orderOf g : ℤ) ∣ k + k := orderOf_dvd_iff_zpow_eq_one.2 hsq
  rw [hord] at hdvd
  obtain ⟨c, hc⟩ := h4
  obtain ⟨d, hd⟩ := hdvd
  have hk2 : k = 2 * ((c : ℤ) * d) := by
    have hc' : (Nat.card R : ℤ) = 4 * c := by exact_mod_cast hc
    rw [hc'] at hd
    linarith
  have hy : y = ((g ^ ((c : ℤ) * d) : R) : Q) * ((g ^ ((c : ℤ) * d) : R) : Q) := by
    have h1 : (⟨y, hyR⟩ : R) = g ^ ((c : ℤ) * d) * g ^ ((c : ℤ) * d) := by
      rw [← zpow_add, ← two_mul, ← hk2, hk]
    exact congrArg Subtype.val h1
  rw [hy]
  exact mul_self_mem_of_index_two hS2 _

end Grp

theorem two_orbits_of_abelian {S : Subgroup Q} (hS : IsMulCommutative S) (hS2 : S.index = 2) {t : Q}
    (htS : t ∉ S) (ht2 : t * t = 1) (hC : Nat.card ↥(S ⊓ centralizer ({t} : Set Q)) = 2)
    {x₁ x₂ x₃ : Q} (h₁ : x₁ ∉ S) (h₂ : x₂ ∉ S) (h₃ : x₃ ∉ S) :
    (∃ u ∈ S, u * x₁ * u⁻¹ = x₂) ∨ (∃ u ∈ S, u * x₁ * u⁻¹ = x₃) ∨
      ∃ u ∈ S, u * x₂ * u⁻¹ = x₃ := by
  haveI hN : S.Normal := normal_of_index_eq_two hS2
  have hcls : ∀ x : Q, x ∉ S → Nat.card S ≤ 2 * (conjugatesOf x).ncard := fun x hx =>
    Grp.card_le_two_mul_ncard_conjugatesOf hS2
      (by rw [Grp.inf_centralizer_eq_of_isMulCommutative hS hS2 htS hx]; exact hC)
  by_contra hcon
  push Not at hcon
  obtain ⟨n12, n13, n23⟩ := hcon
  have hdisj : ∀ {a b : Q}, a ∉ S → (∀ u ∈ S, u * a * u⁻¹ ≠ b) →
      Disjoint (conjugatesOf a) (conjugatesOf b) := by
    intro a b ha hab
    refine Set.disjoint_left.2 fun z hza hzb => ?_
    obtain ⟨u, huS, hu⟩ := Grp.exists_mem_of_isConj hS2 ha (hza.trans hzb.symm)
    exact hab u huS hu
  have d12 := hdisj h₁ n12
  have d13 := hdisj h₁ n13
  have d23 := hdisj h₂ n23
  have hsub : conjugatesOf x₁ ∪ conjugatesOf x₂ ∪ conjugatesOf x₃ ⊆ (S : Set Q)ᶜ :=
    Set.union_subset (Set.union_subset (Grp.conjugatesOf_subset_compl h₁)
      (Grp.conjugatesOf_subset_compl h₂)) (Grp.conjugatesOf_subset_compl h₃)
  have hcard := Set.ncard_le_ncard hsub
  rw [Set.ncard_union_eq (Set.disjoint_union_left.2 ⟨d13, d23⟩), Set.ncard_union_eq d12,
    Set.ncard_compl] at hcard
  have hS' : Nat.card S = (S : Set Q).ncard := Nat.card_coe_set_eq (S : Set Q)
  have h4 := Subgroup.card_mul_index S
  rw [hS2] at h4
  have hpos : 0 < Nat.card S := Nat.card_pos
  have := hcls x₁ h₁
  have := hcls x₂ h₂
  have := hcls x₃ h₃
  omega

theorem exists_cyclic_index_two
    (hQ : (∃ m : ℕ, 1 ≤ m ∧ Nonempty (Q ≃* DihedralGroup (2 ^ m))) ∨
      ∃ k : ℕ, 4 ≤ k ∧ Nonempty (Q ≃* SemidihedralGroup k)) :
    ∃ R : Subgroup Q, IsCyclic R ∧ R.index = 2 := by
  rcases hQ with ⟨m, -, ⟨e⟩⟩ | ⟨k, hk, ⟨e⟩⟩
  · haveI : NeZero (2 ^ m) := ⟨pow_ne_zero m two_ne_zero⟩
    exact Grp.exists_cyclic_index_two_of_equiv e (DihedralGroup.r 1)
      (Grp.index_zpowers_r_one (2 ^ m))
  · exact Grp.exists_cyclic_index_two_of_equiv e (CFSG.Semidihedral.r k)
      (CFSG.Semidihedral.rotation_index k (by omega))

theorem conj_of_cyclic_index_two (hQ : IsPGroup 2 Q) {R S : Subgroup Q} (hR : IsCyclic R)
    (hR2 : R.index = 2) (hS2 : S.index = 2) (hne : S ≠ R) (hS4 : 4 ≤ Nat.card S) {t : Q}
    (htS : t ∉ S) (ht2 : t * t = 1) (hC : Nat.card ↥(S ⊓ centralizer ({t} : Set Q)) = 2)
    {x : Q} (hxS : x ∉ S) (hx2 : x * x = 1) : ∃ u ∈ S, u * t * u⁻¹ = x := by
  haveI hN : S.Normal := normal_of_index_eq_two hS2
  have hRS : Nat.card R = Nat.card S := by
    have h1 := Subgroup.card_mul_index R
    have h2 := Subgroup.card_mul_index S
    rw [hR2] at h1
    rw [hS2] at h2
    omega
  have h4 : 4 ∣ Nat.card R := by
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 (hQ.to_subgroup S)
    have ha2 : 2 ≤ a := by
      by_contra hlt
      push Not at hlt
      interval_cases a <;> omega
    rw [hRS, ha]
    exact (pow_dvd_pow 2 ha2 : 2 ^ 2 ∣ 2 ^ a)
  have hinv : ∀ y : Q, y * y = 1 → y ∉ S → y ∉ R := fun y hy2 hyS hyR =>
    hyS (Grp.mem_of_mem_cyclic_index_two hR hS2 h4 hyR hy2)
  have htR : t ∉ R := hinv t ht2 htS
  have hXcard : {y : Q | y ∉ S ∧ y ∉ R}.ncard ≤ Nat.card ↥(S ⊓ R) := by
    have h := Set.ncard_le_ncard_of_injOn (s := {y : Q | y ∉ S ∧ y ∉ R})
      (t := ((S ⊓ R : Subgroup Q) : Set Q)) (fun y => y * t⁻¹) ?_ ?_
    · exact h
    · rintro y ⟨hyS, hyR⟩
      show y * t⁻¹ ∈ S ⊓ R
      rw [mem_inf]
      refine ⟨?_, ?_⟩
      · rw [mul_mem_iff_of_index_two hS2]
        exact iff_of_false hyS (by simpa using htS)
      · rw [mul_mem_iff_of_index_two hR2]
        exact iff_of_false hyR (by simpa using htR)
    · intro a _ b _ hab
      exact mul_right_cancel hab
  have hAS : 2 * Nat.card ↥(S ⊓ R) ≤ Nat.card S := by
    have h1 := Subgroup.relIndex_mul_card (H := R) (K := S)
    rw [inf_comm] at h1
    have h2 : R.relIndex S ≠ 1 := fun h =>
      hne (Subgroup.eq_of_le_of_card_ge (relIndex_eq_one.1 h) hRS.le)
    have h3 : R.relIndex S ≠ 0 := by
      intro h
      rw [h] at h1
      have := Nat.card_pos (α := S)
      omega
    have h5 : 2 ≤ R.relIndex S := by omega
    calc 2 * Nat.card ↥(S ⊓ R) ≤ R.relIndex S * Nat.card ↥(S ⊓ R) := Nat.mul_le_mul_right _ h5
      _ = Nat.card S := h1
  have hsub : conjugatesOf t ⊆ {y : Q | y ∉ S ∧ y ∉ R} := by
    intro z hz
    obtain ⟨c, hc⟩ := isConj_iff.1 hz
    have hzS : z ∉ S := Grp.conjugatesOf_subset_compl htS hz
    have hz2 : z * z = 1 := by
      rw [← hc]
      calc c * t * c⁻¹ * (c * t * c⁻¹) = c * (t * t) * c⁻¹ := by group
        _ = 1 := by rw [ht2]; group
    exact ⟨hzS, hinv z hz2 hzS⟩
  have hcls := Grp.card_le_two_mul_ncard_conjugatesOf hS2 hC
  have hle : {y : Q | y ∉ S ∧ y ∉ R}.ncard ≤ (conjugatesOf t).ncard := by omega
  have heq := Set.eq_of_subset_of_ncard_le hsub hle
  have hxmem : x ∈ conjugatesOf t := by
    rw [heq]
    exact ⟨hxS, hinv x hx2 hxS⟩
  exact Grp.exists_mem_of_isConj hS2 htS hxmem

end CFSG.LocalAnalysis.EvenBN.Tits.N.S16A
