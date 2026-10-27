module

public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverRoots
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearFourCentralCover

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearCover

open Subgroup Matrix LinearFlag LinearFieldFour
open scoped commutatorElement

theorem conj_mem_zpowers_of_mem_closure {G : Type*} [Group G] {c : G} {X : Set G}
    (hX : ∀ g ∈ X, g * c * g⁻¹ = c ∨ g * c * g⁻¹ = c⁻¹) {g : G} (hg : g ∈ Subgroup.closure X) :
    ∀ t ∈ zpowers c, g * t * g⁻¹ ∈ zpowers c := by
  have key : g * c * g⁻¹ = c ∨ g * c * g⁻¹ = c⁻¹ := by
    induction hg using Subgroup.closure_induction with
    | mem t ht => exact hX t ht
    | one => left; group
    | mul g₁ g₂ _ _ ih₁ ih₂ =>
      have h : g₁ * g₂ * c * (g₁ * g₂)⁻¹ = g₁ * (g₂ * c * g₂⁻¹) * g₁⁻¹ := by group
      have h' : g₁ * c⁻¹ * g₁⁻¹ = (g₁ * c * g₁⁻¹)⁻¹ := by group
      rw [h]
      rcases ih₂ with h₂ | h₂ <;> rw [h₂]
      · exact ih₁
      · rw [h']
        rcases ih₁ with h₁ | h₁ <;> rw [h₁]
        · exact Or.inr rfl
        · exact Or.inl (inv_inv c)
    | inv g₁ _ ih =>
      rcases ih with h₁ | h₁
      · left
        calc g₁⁻¹ * c * g₁⁻¹⁻¹ = g₁⁻¹ * (g₁ * c * g₁⁻¹) * g₁ := by rw [h₁, inv_inv]
          _ = c := by group
      · right
        calc g₁⁻¹ * c * g₁⁻¹⁻¹ = (g₁⁻¹ * c⁻¹ * g₁)⁻¹ := by group
          _ = (g₁⁻¹ * (g₁ * c * g₁⁻¹) * g₁)⁻¹ := by rw [h₁]
          _ = c⁻¹ := by group
  intro t ht
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ht
  have hk : g * c ^ k * g⁻¹ = (g * c * g⁻¹) ^ k := by
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
  rw [hk]
  rcases key with h | h <;> rw [h]
  · exact zpow_mem (mem_zpowers c) k
  · exact zpow_mem (inv_mem (mem_zpowers c)) k

theorem isCyclic_of_natCard_le_two {G : Type*} [Group G] [Finite G] (h : Nat.card G ≤ 2) :
    IsCyclic G := by
  rcases Nat.lt_or_ge (Nat.card G) 2 with h1 | h1
  · have : Subsingleton G := Finite.card_le_one_iff_subsingleton.mp (by omega)
    exact isCyclic_of_subsingleton
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact isCyclic_of_prime_card (p := 2) (by omega)

theorem dihedral_sylow_kernel_bound {P Q : Type*} [Group P] [Group Q] [Finite P]
    [Group.IsPerfect P] (η : P →* Q) (hη : Function.Surjective η) (hK : η.ker ≤ center P)
    (h2 : IsPGroup 2 η.ker) {m : ℕ} (hm : 2 ≤ m) (S : Sylow 2 Q) {r s : Q}
    (hSrs : (S : Subgroup Q) = Subgroup.closure {r, s}) (hro : orderOf r = 2 ^ (m - 1))
    (hs2 : s ^ 2 = 1) (hconj : s⁻¹ * r * s = r⁻¹) :
    IsCyclic η.ker ∧ Nat.card η.ker ≤ 2 := by
  have hker : ∀ z, η z = 1 → z ∈ center P := fun z hz => hK hz
  obtain ⟨T, hTS, hKT⟩ := exists_sylow_map_eq_twoPart_le η hη hK S
  obtain ⟨x, hx⟩ := hη r
  obtain ⟨y, hy⟩ := hη s
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right (by rw [← sq, hs2])
  have hconj' : s * r * s⁻¹ = r⁻¹ := by
    rw [hsinv]
    rw [hsinv] at hconj
    exact hconj
  obtain ⟨b, hbdef⟩ : ∃ b, b = x * (y * x * y⁻¹) := ⟨_, rfl⟩
  have hbc : b ∈ center P := hker b (by
    rw [hbdef]
    simp only [map_mul, map_inv, hx, hy]
    rw [hconj', mul_inv_cancel])
  have hb : ∀ g, g * b = b * g := mem_center_iff.mp hbc
  have hyx : y * x * y⁻¹ = x⁻¹ * b := by rw [hbdef]; group
  obtain ⟨c, hcdef⟩ : ∃ c, c = ⁅x, y⁆ := ⟨_, rfl⟩
  have hxb : Commute x b⁻¹ := mem_center_iff.mp (inv_mem hbc) x
  have hc : c = x * x * b⁻¹ := by
    calc c = x * (y * x * y⁻¹)⁻¹ := by rw [hcdef, commutatorElement_def]; group
      _ = x * (x⁻¹ * b)⁻¹ := by rw [hyx]
      _ = x * (b⁻¹ * x) := by group
      _ = x * x * b⁻¹ := by rw [← hxb.eq, mul_assoc]
  have hxc : x * c * x⁻¹ = c := by
    have hcomm : Commute x c := by
      rw [hc]
      exact ((Commute.refl x).mul_right (Commute.refl x)).mul_right hxb
    rw [hcomm.eq, mul_inv_cancel_right]
  have hyc : y * c * y⁻¹ = c⁻¹ := by
    have hyb : y * b * y⁻¹ = b := by rw [hb y, mul_inv_cancel_right]
    rw [hc]
    calc y * (x * x * b⁻¹) * y⁻¹ = (y * x * y⁻¹) * (y * x * y⁻¹) * (y * b * y⁻¹)⁻¹ := by group
      _ = (x⁻¹ * b) * (x⁻¹ * b) * b⁻¹ := by rw [hyx, hyb]
      _ = (b * x⁻¹) * (x⁻¹ * b) * b⁻¹ := by rw [hb x⁻¹]
      _ = (x * x * b⁻¹)⁻¹ := by group
  have hηc : η c = r ^ 2 := by
    rw [hcdef, map_commutatorElement, hx, hy, commutatorElement_def]
    calc r * s * r⁻¹ * s⁻¹ = r * (s * r * s⁻¹)⁻¹ := by group
      _ = r ^ 2 := by rw [hconj', inv_inv, sq]
  obtain ⟨X, hXdef⟩ : ∃ X : Set P, X = {x, y} ∪ (η.ker : Set P) := ⟨_, rfl⟩
  have hTX : (T : Subgroup P) ≤ Subgroup.closure X := by
    have hmap : (Subgroup.closure ({x, y} : Set P)).map η = S := by
      rw [MonoidHom.map_closure, Set.image_pair, hx, hy, hSrs]
    have h1 : (T : Subgroup P) ≤ Subgroup.closure ({x, y} : Set P) ⊔ η.ker := by
      rw [← comap_map_eq, hmap]
      exact map_le_iff_le_comap.mp hTS.le
    rw [hXdef, Subgroup.closure_union, Subgroup.closure_eq]
    exact h1
  have hXc : ∀ g ∈ X, g * c * g⁻¹ = c ∨ g * c * g⁻¹ = c⁻¹ := by
    intro g hg
    rw [hXdef] at hg
    rcases hg with (rfl | rfl) | hg
    · exact Or.inl hxc
    · exact Or.inr hyc
    · left
      rw [← mem_center_iff.mp (hK hg) c, mul_inv_cancel_right]
  have hXcomm : ∀ g ∈ X, ∀ g' ∈ X, ⁅g, g'⁆ ∈ zpowers c := by
    intro g hg g' hg'
    rw [hXdef] at hg hg'
    rcases hg with (rfl | rfl) | hg
    · rcases hg' with (rfl | rfl) | hg'
      · rw [commutatorElement_self]
        exact one_mem _
      · rw [← hcdef]
        exact mem_zpowers c
      · rw [commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp (hK hg') _)]
        exact one_mem _
    · rcases hg' with (rfl | rfl) | hg'
      · rw [← commutatorElement_inv, ← hcdef]
        exact inv_mem (mem_zpowers c)
      · rw [commutatorElement_self]
        exact one_mem _
      · rw [commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp (hK hg') _)]
        exact one_mem _
    · rw [commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp (hK hg) _).symm]
      exact one_mem _
  have hTc : ⁅(T : Subgroup P), (T : Subgroup P)⁆ ≤ zpowers c :=
    commutator_le.mpr fun g₁ hg₁ g₂ hg₂ =>
      commutatorElement_mem_of_mem_closure (fun g hg => conj_mem_zpowers_of_mem_closure hXc hg)
        hXcomm (hTX hg₁) (hTX hg₂)
  have hKc : ∀ z ∈ η.ker, z ∈ zpowers c := fun z hz => by
    obtain ⟨n, hn⟩ := h2 ⟨z, hz⟩
    exact hTc (hKT z hz ⟨n, congrArg Subtype.val hn⟩)
  have hm1 : 2 ^ (m - 1) = 2 * 2 ^ (m - 2) := by
    rw [← pow_succ']
    congr 1
    omega
  obtain ⟨w, hwdef⟩ : ∃ w, w = c ^ 2 ^ (m - 2) := ⟨_, rfl⟩
  have hηw : η w = 1 := by
    rw [hwdef, map_pow, hηc, ← pow_mul, ← hm1, ← hro, pow_orderOf_eq_one]
  have hw2 : w ^ 2 = 1 := by
    have hyw : y * w * y⁻¹ = w⁻¹ := by rw [hwdef, ← conj_pow, hyc, inv_pow]
    have hyw' : y * w * y⁻¹ = w := by
      rw [mem_center_iff.mp (hker w hηw) y, mul_inv_cancel_right]
    rw [sq]
    calc w * w = w * w⁻¹ := by rw [← hyw, hyw']
      _ = 1 := mul_inv_cancel w
  have hcw : c ^ ((2 : ℤ) ^ (m - 2)) = w := by
    rw [hwdef]
    exact_mod_cast zpow_natCast c (2 ^ (m - 2))
  have hKw : η.ker ≤ zpowers w := by
    intro z hz
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp (hKc z hz)
    have hk : r ^ (2 * k) = 1 := by
      have h := hz
      rw [MonoidHom.mem_ker, map_zpow, hηc, ← zpow_natCast, ← _root_.zpow_mul] at h
      exact_mod_cast h
    have hdvd : (2 : ℤ) * 2 ^ (m - 2) ∣ 2 * k := by
      have h := orderOf_dvd_iff_zpow_eq_one.mpr hk
      rw [hro, hm1] at h
      exact_mod_cast h
    obtain ⟨j, hj⟩ := (mul_dvd_mul_iff_left two_ne_zero).mp hdvd
    rw [hj, _root_.zpow_mul, hcw]
    exact zpow_mem (mem_zpowers w) j
  refine ⟨Subgroup.isCyclic_of_le hKw, ?_⟩
  calc Nat.card η.ker ≤ Nat.card (zpowers w) := Subgroup.card_le_of_le hKw
    _ = orderOf w := Nat.card_zpowers w
    _ ≤ 2 := Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one hw2)

theorem dihedral_kernel_bound {P Q : Type*} [Group P] [Group Q] [Finite P] [Group.IsPerfect P]
    (η : P →* Q) (hη : Function.Surjective η) (hK : η.ker ≤ center P) (h2 : IsPGroup 2 η.ker)
    (hS : ∃ m : ℕ, 3 ≤ m ∧ ∃ S : Sylow 2 Q, ∃ r ∈ (S : Subgroup Q), ∃ s ∈ (S : Subgroup Q),
      (S : Subgroup Q) = Subgroup.closure {r, s} ∧ orderOf r = 2 ^ (m - 1) ∧
        orderOf s = 2 ∧ s ∉ zpowers r ∧ s⁻¹ * r * s = r⁻¹) :
    IsCyclic η.ker ∧ Nat.card η.ker ≤ 2 := by
  obtain ⟨m, hm, S, r, -, s, -, hSrs, hro, hso, -, hconj⟩ := hS
  exact dihedral_sylow_kernel_bound η hη hK h2 (by omega) S hSrs hro
    (by rw [← hso]; exact pow_orderOf_eq_one s) hconj

theorem eq_zero_or_eq_one_of_card_eq_two {K : Type*} [Field K] (hK : Nat.card K = 2) (a : K) :
    a = 0 ∨ a = 1 := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have := Fintype.ofFinite K
  by_contra h
  push Not at h
  have h3 : ({0, 1, a} : Finset K).card = 3 :=
    Finset.card_eq_three.mpr ⟨0, 1, a, zero_ne_one, h.1.symm, h.2.symm, rfl⟩
  have hle := Finset.card_le_univ ({0, 1, a} : Finset K)
  rw [h3, ← Nat.card_eq_fintype_card, hK] at hle
  omega

theorem heisenberg_dihedral_relations {K G : Type*} [Field K] [CharP K 2] [Group G]
    (R : HeisenbergRoots K G) :
    (R.x 1 * R.y 1) ^ 2 = R.w 1 ∧ R.y 1 ^ 2 = 1 ∧ R.w 1 ^ 2 = 1 ∧
      (R.y 1)⁻¹ * (R.x 1 * R.y 1) * R.y 1 = (R.x 1 * R.y 1)⁻¹ := by
  have hx2 : R.x 1 * R.x 1 = 1 := by rw [← R.x_add, CharTwo.add_self_eq_zero, R.x_zero]
  have hy2 : R.y 1 * R.y 1 = 1 := by rw [← R.y_add, CharTwo.add_self_eq_zero, R.y_zero]
  have hw2 : R.w 1 * R.w 1 = 1 := by rw [← R.w_add, CharTwo.add_self_eq_zero, R.w_zero]
  have hxy : R.x 1 * R.y 1 = R.w 1 * R.y 1 * R.x 1 := by rw [R.x_mul_y, mul_one]
  have hxinv : (R.x 1)⁻¹ = R.x 1 := inv_eq_of_mul_eq_one_right hx2
  have hyinv : (R.y 1)⁻¹ = R.y 1 := inv_eq_of_mul_eq_one_right hy2
  refine ⟨?_, by rw [sq, hy2], by rw [sq, hw2], ?_⟩
  · calc (R.x 1 * R.y 1) ^ 2 = R.w 1 * R.y 1 * R.x 1 * (R.x 1 * R.y 1) := by rw [sq, hxy]
      _ = R.w 1 * R.y 1 * (R.x 1 * R.x 1) * R.y 1 := by group
      _ = R.w 1 := by rw [hx2, mul_one, mul_assoc, hy2, mul_one]
  · rw [hyinv, _root_.mul_inv_rev, hxinv, hyinv, mul_assoc, mul_assoc, hy2, mul_one]

theorem closure_heisenberg_dihedral {K G : Type*} [Field K] [CharP K 2] [Group G]
    (R : HeisenbergRoots K G) (hK : ∀ a : K, a = 0 ∨ a = 1) :
    Subgroup.closure {R.x 1 * R.y 1, R.y 1} = R.S := by
  obtain ⟨hr2, -, -, -⟩ := heisenberg_dihedral_relations R
  have hrmem : R.x 1 * R.y 1 ∈ Subgroup.closure ({R.x 1 * R.y 1, R.y 1} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hsmem : R.y 1 ∈ Subgroup.closure ({R.x 1 * R.y 1, R.y 1} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro t (rfl | rfl)
    · exact mul_mem (R.x_mem 1) (R.y_mem 1)
    · exact R.y_mem 1
  · intro t ht
    obtain ⟨a, b, c, rfl⟩ := R.mem_S t ht
    have hx : R.x a ∈ Subgroup.closure ({R.x 1 * R.y 1, R.y 1} : Set G) := by
      rcases hK a with rfl | rfl
      · rw [R.x_zero]
        exact one_mem _
      · have h := mul_mem hrmem (inv_mem hsmem)
        rwa [mul_inv_cancel_right] at h
    have hy : R.y b ∈ Subgroup.closure ({R.x 1 * R.y 1, R.y 1} : Set G) := by
      rcases hK b with rfl | rfl
      · rw [R.y_zero]
        exact one_mem _
      · exact hsmem
    have hw : R.w c ∈ Subgroup.closure ({R.x 1 * R.y 1, R.y 1} : Set G) := by
      rcases hK c with rfl | rfl
      · rw [R.w_zero]
        exact one_mem _
      · rw [← hr2]
        exact pow_mem hrmem 2
    exact mul_mem (mul_mem hw hx) hy

theorem wP_one_ne_one {K : Type*} [Field K] : wP (1 : K) ≠ 1 := by
  intro h
  have h' : wMat (1 : K) = 1 := proj_injOn_unitriangular 3 (wMat_mem_unitriangular 1)
    (one_mem _) (by rw [map_one]; exact h)
  have h'' := congrArg (fun A : SpecialLinearGroup (Fin 3) K =>
    (A : Matrix (Fin 3) (Fin 3) K) 0 2) h'
  simp [wMat, wM] at h''

theorem yP_one_ne_one {K : Type*} [Field K] : yP (1 : K) ≠ 1 := by
  intro h
  have h' : yMat (1 : K) = 1 := proj_injOn_unitriangular 3 (yMat_mem_unitriangular 1)
    (one_mem _) (by rw [map_one]; exact h)
  have h'' := congrArg (fun A : SpecialLinearGroup (Fin 3) K =>
    (A : Matrix (Fin 3) (Fin 3) K) 1 2) h'
  simp [yMat, yM] at h''

theorem projectiveSL_three_dihedral_sylow {k : Type*} [Field k] [Finite k] [CharP k 2]
    (hk : Nat.card k = 2) :
    ∃ m : ℕ, 3 ≤ m ∧ ∃ S : Sylow 2 (projectiveSL 3 k), ∃ r ∈ (S : Subgroup (projectiveSL 3 k)),
      ∃ s ∈ (S : Subgroup (projectiveSL 3 k)), (S : Subgroup _) = Subgroup.closure {r, s} ∧
        orderOf r = 2 ^ (m - 1) ∧ orderOf s = 2 ∧ s ∉ zpowers r ∧ s⁻¹ * r * s = r⁻¹ := by
  obtain ⟨S, hS⟩ := exists_sylow_projUnitriangular (K := k) 2 (n := 3) (by norm_num)
  obtain ⟨hr2, hs2, hw2, hconj⟩ := heisenberg_dihedral_relations (projRoots (K := k))
  simp only [projRoots_x, projRoots_y, projRoots_w] at hr2 hs2 hw2 hconj
  have hcl := closure_heisenberg_dihedral (projRoots (K := k))
    (eq_zero_or_eq_one_of_card_eq_two hk)
  simp only [projRoots_x, projRoots_y, projRoots_S] at hcl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr1 : ¬ (xP (1 : k) * yP 1) ^ 2 = 1 := by
    rw [hr2]
    exact wP_one_ne_one
  refine ⟨3, le_rfl, S, xP 1 * yP 1, ?_, yP 1, ?_, ?_, ?_, orderOf_eq_prime hs2 yP_one_ne_one,
    ?_, hconj⟩
  · rw [hS, ← hcl]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  · rw [hS, ← hcl]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  · rw [hS, hcl]
  · have h := orderOf_eq_prime_pow (p := 2) (n := 1) (by rwa [pow_one])
      (by rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, hr2, hw2])
    simpa using h
  · intro hmem
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hmem
    have hcomm : Commute ((xP (1 : k) * yP 1) ^ j) (xP 1 * yP 1) := (Commute.refl _).zpow_left j
    rw [hj] at hcomm
    have h1 : (xP (1 : k) * yP 1)⁻¹ = xP 1 * yP 1 := by
      rw [← hconj, mul_assoc, ← hcomm.eq, ← mul_assoc, inv_mul_cancel, one_mul]
    apply hr1
    calc (xP (1 : k) * yP 1) ^ 2 = (xP 1 * yP 1) * (xP 1 * yP 1)⁻¹ := by rw [h1, sq]
      _ = 1 := mul_inv_cancel _

theorem linear_three_two_cover_kernel_bound {P : Type*} {Q : Type} [Group P] [Group Q]
    [Finite P] [Group.IsPerfect P] (η : P →* Q) (hη : Function.Surjective η)
    (hK : η.ker ≤ center P) (h2 : IsPGroup 2 η.ker) (hQ : CFSG.Blueprint.LieModel Q .PSL 3 2 1) :
    IsCyclic η.ker ∧ Nat.card η.ker ≤ 2 := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := exists_mulEquiv_projectiveSL_of_lieModel hQ
  have := finite_field_prime_power_characteristic (K := F) Nat.prime_two (by norm_num) hcard
  set η' : P →* projectiveSL 3 F := e.toMonoidHom.comp η
  have hker' : η'.ker = η.ker := by
    ext z
    exact e.map_eq_one_iff
  have h := dihedral_kernel_bound η' (e.surjective.comp hη) (hker' ▸ hK) (hker' ▸ h2)
    (projectiveSL_three_dihedral_sylow (by rw [hcard, pow_one]))
  rwa [hker'] at h

theorem linear_two_four_cover_kernel_bound {P : Type*} {Q : Type} [Group P] [Group Q]
    [Finite P] [Group.IsPerfect P] (η : P →* Q) (hη : Function.Surjective η)
    (hK : η.ker ≤ center P) (h2 : IsPGroup 2 η.ker) (hQ : CFSG.Blueprint.LieModel Q .PSL 2 2 2) :
    IsCyclic η.ker ∧ Nat.card η.ker ≤ 2 := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := exists_mulEquiv_projectiveSL_of_lieModel hQ
  have := finite_field_prime_power_characteristic (K := F) Nat.prime_two (by norm_num) hcard
  set η' : P →* SpecialLinearGroup (Fin 2) F :=
    (projectiveSLTwoEquivSL F).toMonoidHom.comp (e.toMonoidHom.comp η)
  have hker' : η'.ker = η.ker := by
    ext z
    change projectiveSLTwoEquivSL F (e (η z)) = 1 ↔ η z = 1
    rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff]
  have hbound := CFSG.ShultStronglyClosedTI.four_field_linear_cover_kernel_card_le_two
    (K := F) (by rw [hcard]; norm_num) η'
    ((projectiveSLTwoEquivSL F).surjective.comp (e.surjective.comp hη)) (hker' ▸ hK)
    (hker' ▸ h2)
  rw [hker'] at hbound
  exact ⟨isCyclic_of_natCard_le_two hbound, hbound⟩


theorem perfect_central_two_cover_dihedral_Sylow_and_small_linear_kernel_bound :
    (∀ {P Q : Type*} [Group P] [Group Q] [Finite P] [Finite Q] [Group.IsPerfect P]
      (η : P →* Q), Function.Surjective η → η.ker ≤ center P → IsPGroup 2 η.ker →
      (∃ m : ℕ, 3 ≤ m ∧ ∃ S : Sylow 2 Q, ∃ r ∈ (S : Subgroup Q), ∃ s ∈ (S : Subgroup Q),
        (S : Subgroup Q) = Subgroup.closure {r, s} ∧ orderOf r = 2 ^ (m - 1) ∧
          orderOf s = 2 ∧ s ∉ zpowers r ∧ s⁻¹ * r * s = r⁻¹) →
      IsCyclic η.ker ∧ Nat.card η.ker ≤ 2) ∧
    (∀ {P : Type*} {Q : Type} [Group P] [Group Q] [Finite P] [Finite Q] [Group.IsPerfect P]
      (η : P →* Q), Function.Surjective η → η.ker ≤ center P → IsPGroup 2 η.ker →
      CFSG.Blueprint.LieModel Q .PSL 2 2 2 → IsCyclic η.ker ∧ Nat.card η.ker ≤ 2) ∧
    (∀ {P : Type*} {Q : Type} [Group P] [Group Q] [Finite P] [Finite Q] [Group.IsPerfect P]
      (η : P →* Q), Function.Surjective η → η.ker ≤ center P → IsPGroup 2 η.ker →
      CFSG.Blueprint.LieModel Q .PSL 3 2 1 → IsCyclic η.ker ∧ Nat.card η.ker ≤ 2) :=
  ⟨fun η hη hK h2 hS => dihedral_kernel_bound η hη hK h2 hS,
    fun η hη hK h2 hQ => linear_two_four_cover_kernel_bound η hη hK h2 hQ,
    fun η hη hK h2 hQ => linear_three_two_cover_kernel_bound η hη hK h2 hQ⟩

end LinearCover

end CFSG.LocalAnalysis.ComponentInitial
