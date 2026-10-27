module

public import CFSG.GH74.GLS.SP.SpDefs
import CFSG.LieType.Universal.SymplecticExtras.Matrices
import CFSG.LieType.Universal.SymplecticExtras.Unipotent
import CFSG.LieType.Universal.SymplecticExtras.Torus
import CFSG.LieType.TitsSimplicity.Unipotent
import CFSG.LieType.Steinberg.Collection

public section

namespace CFSG.GH74.GLS.SP

open CFSG.GH74.BNPair CFSG.LieType.Universal.Symplectic CFSG.LieType.Steinberg
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank TauCeti.GLSymplecticFin
open scoped Pointwise commutatorElement

section Abstract

variable {G : Type*} [Group G]

theorem nodup_intList (i j : ℤ) : (intList i j).Nodup := by
  refine List.Nodup.map (fun a b h => ?_) List.nodup_range
  have : (a : ℤ) = b := by simpa using h
  exact_mod_cast this

theorem pairwise_le_intList (i j : ℤ) : (intList i j).Pairwise (· ≤ ·) := by
  unfold intList
  rw [List.pairwise_map]
  exact List.pairwise_lt_range.imp fun {a b} h => by
    have : (a : ℤ) < b := by exact_mod_cast h
    omega

theorem chainProd_subset_iSup (A : ℤ → Subgroup G) :
    ∀ l : List ℤ, chainProd A l ⊆ ((⨆ k ∈ l, A k : Subgroup G) : Set G)
  | [] => by
    intro g hg
    simp only [chainProd, List.map_nil, List.prod_nil, Set.mem_one] at hg
    rw [hg]
    exact one_mem _
  | k :: l => by
    intro g hg
    rw [chainProd_cons, Set.mem_mul] at hg
    obtain ⟨x, hx, y, hy, rfl⟩ := hg
    have hy' := chainProd_subset_iSup A l hy
    have hx' : x ∈ ⨆ k' ∈ k :: l, A k' :=
      le_iSup₂_of_le (f := fun k' (_ : k' ∈ k :: l) => A k') k List.mem_cons_self le_rfl hx
    have hle : (⨆ k' ∈ l, A k' : Subgroup G) ≤ ⨆ k' ∈ k :: l, A k' :=
      iSup₂_le fun k' hk' => le_iSup₂_of_le (f := fun k' (_ : k' ∈ k :: l) => A k') k'
        (List.mem_cons_of_mem k hk') le_rfl
    exact mul_mem hx' (hle hy')

theorem carrier_iSup_eq_chainProd (A : ℤ → Subgroup G) {l : List ℤ} (hnd : l.Nodup) (h : ℤ → ℤ)
    (hs : l.Pairwise fun a b => h a ≤ h b)
    (hc : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → ∀ x ∈ A a, ∀ y ∈ A b,
      ⁅x, y⁆ ∈ ⨆ c ∈ l, ⨆ (_ : min (h a) (h b) < h c), A c) :
    ((⨆ k ∈ l, A k : Subgroup G) : Set G) = chainProd A l := by
  refine Set.Subset.antisymm (fun g hg => ?_) (chainProd_subset_iSup A l)
  obtain ⟨f, hf, rfl⟩ := exists_prod_eq_of_commutator_mem A h hnd hs hc g hg
  exact list_prod_mem_chainProd A f l hf

@[expose] def OctComm (A : ℤ → Subgroup G) (n : ℤ) : Prop :=
  ∀ a b : ℤ, 1 ≤ a → a < b → b ≤ n → ∀ x ∈ A a, ∀ y ∈ A b, ⁅x, y⁆ ∈ ⨆ c ∈ Set.Ioo a b, A c

variable {A : ℤ → Subgroup G} {n : ℤ}

theorem OctComm.symm' (hC : OctComm A n) {a b : ℤ} (ha : 1 ≤ a) (hb : 1 ≤ b) (han : a ≤ n)
    (hbn : b ≤ n) (hab : a ≠ b) {x y : G} (hx : x ∈ A a) (hy : y ∈ A b) :
    ⁅x, y⁆ ∈ ⨆ c ∈ Set.Ioo (min a b) (max a b), A c := by
  rcases lt_or_gt_of_ne hab with h | h
  · rw [min_eq_left h.le, max_eq_right h.le]
    exact hC a b ha h hbn x hx y hy
  · rw [min_eq_right h.le, max_eq_left h.le, ← commutatorElement_inv]
    exact inv_mem (hC b a hb h han y hy x hx)

theorem OctComm.carrier_eq (hC : OctComm A n) {i j : ℤ} (hi : 1 ≤ i) (hj : j ≤ n) :
    ((⨆ k ∈ intList i j, A k : Subgroup G) : Set G) = chainProd A (intList i j) := by
  refine carrier_iSup_eq_chainProd A (nodup_intList i j) (fun v => v) (pairwise_le_intList i j) ?_
  intro a ha b hb hab x hx y hy
  rw [mem_intList_iff] at ha hb
  have h := hC.symm' (by omega) (by omega) (by omega) (by omega) hab hx hy
  refine (iSup₂_le fun c hc => ?_ : (⨆ c ∈ Set.Ioo (min a b) (max a b), A c) ≤ _) h
  rw [Set.mem_Ioo] at hc
  exact le_iSup₂_of_le (f := fun c (_ : c ∈ intList i j) => ⨆ (_ : min a b < c), A c) c
    (mem_intList_iff.2 ⟨by omega, by omega⟩) (le_iSup_of_le hc.1 le_rfl)

theorem OctComm.carrier_eq_reverse (hC : OctComm A n) {i j : ℤ} (hi : 1 ≤ i) (hj : j ≤ n) :
    ((⨆ k ∈ intList i j, A k : Subgroup G) : Set G) = chainProd A (intList i j).reverse := by
  have hjoin : (⨆ k ∈ intList i j, A k : Subgroup G) = ⨆ k ∈ (intList i j).reverse, A k := by
    simp only [List.mem_reverse]
  rw [hjoin]
  refine carrier_iSup_eq_chainProd A (List.nodup_reverse.2 (nodup_intList i j)) (fun v => -v) ?_ ?_
  · rw [List.pairwise_reverse]
    exact (pairwise_le_intList i j).imp fun {a b} hab => show -b ≤ -a by omega
  · intro a ha b hb hab x hx y hy
    rw [List.mem_reverse, mem_intList_iff] at ha hb
    have h := hC.symm' (by omega) (by omega) (by omega) (by omega) hab hx hy
    refine (iSup₂_le fun c hc => ?_ : (⨆ c ∈ Set.Ioo (min a b) (max a b), A c) ≤ _) h
    rw [Set.mem_Ioo] at hc
    exact le_iSup₂_of_le (f := fun c (_ : c ∈ (intList i j).reverse) =>
      ⨆ (_ : min (-a) (-b) < -c), A c) c
      (List.mem_reverse.2 (mem_intList_iff.2 ⟨by omega, by omega⟩))
      (le_iSup_of_le (show min (-a) (-b) < -c by omega) le_rfl)

theorem OctComm.reverse_eq (hC : OctComm A n) {i j : ℤ} (hi : 1 ≤ i) (hj : j ≤ n) :
    chainProd A (intList i j) = chainProd A (intList i j).reverse :=
  (hC.carrier_eq hi hj).symm.trans (hC.carrier_eq_reverse hi hj)

theorem OctComm.conj_mem_left (hC : OctComm A n) {i j : ℤ} (hi : 1 < i) (hj : j ≤ n) {x : G}
    (hx : x ∈ A (i - 1)) {v : G} (hv : v ∈ ⨆ k ∈ intList i j, A k) :
    x * v * x⁻¹ ∈ ⨆ k ∈ intList i j, A k := by
  refine conj_mem_of_forall_mem (P := {k | k ∈ intList i j}) (X := A) (fun k hk y hy => ?_) hv
  have hk0 : k ∈ intList i j := hk
  have hk' := mem_intList_iff.1 hk0
  have hcm := hC (i - 1) k (by omega) (by omega) (by omega) x hx y hy
  have hmem : ⁅x, y⁆ ∈ ⨆ k ∈ intList i j, A k :=
    (iSup₂_le fun c hc => le_iSup₂_of_le (f := fun c (_ : c ∈ intList i j) => A c) c
      (mem_intList_iff.2 ⟨by have := Set.mem_Ioo.1 hc; omega, by have := Set.mem_Ioo.1 hc; omega⟩)
      le_rfl : (⨆ c ∈ Set.Ioo (i - 1) k, A c) ≤ _) hcm
  have e : x * y * x⁻¹ = ⁅x, y⁆ * y := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact mul_mem hmem (le_iSup₂_of_le (f := fun c (_ : c ∈ intList i j) => A c) k hk0 le_rfl hy)

theorem OctComm.conj_mem_right (hC : OctComm A n) {i j : ℤ} (hi : 1 ≤ i) (hj : j < n) {x : G}
    (hx : x ∈ A (j + 1)) {v : G} (hv : v ∈ ⨆ k ∈ intList i j, A k) :
    x * v * x⁻¹ ∈ ⨆ k ∈ intList i j, A k := by
  refine conj_mem_of_forall_mem (P := {k | k ∈ intList i j}) (X := A) (fun k hk y hy => ?_) hv
  have hk0 : k ∈ intList i j := hk
  have hk' := mem_intList_iff.1 hk0
  have hcm := hC k (j + 1) (by omega) (by omega) (by omega) y hy x hx
  have hmem : ⁅y, x⁆ ∈ ⨆ k ∈ intList i j, A k :=
    (iSup₂_le fun c hc => le_iSup₂_of_le (f := fun c (_ : c ∈ intList i j) => A c) c
      (mem_intList_iff.2 ⟨by have := Set.mem_Ioo.1 hc; omega, by have := Set.mem_Ioo.1 hc; omega⟩)
      le_rfl : (⨆ c ∈ Set.Ioo k (j + 1), A c) ≤ _) hcm
  have e : x * y * x⁻¹ = ⁅y, x⁆⁻¹ * y := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact mul_mem (inv_mem hmem)
    (le_iSup₂_of_le (f := fun c (_ : c ∈ intList i j) => A c) k hk0 le_rfl hy)

theorem OctComm.exists_subgroup (hC : OctComm A n) {U : Subgroup G}
    (hU : ∀ k : ℤ, 1 ≤ k → k ≤ n → A k ≤ U) {i j : ℤ} (hi : 1 ≤ i) (hj : j ≤ n) :
    ∃ V : Subgroup G, (V : Set G) = chainProd A (intList i j) ∧ V ≤ U ∧
      (1 < i → ∀ x ∈ A (i - 1), ∀ v ∈ V, x * v * x⁻¹ ∈ V) ∧
      (j < n → ∀ x ∈ A (j + 1), ∀ v ∈ V, x * v * x⁻¹ ∈ V) :=
  ⟨⨆ k ∈ intList i j, A k, hC.carrier_eq hi hj,
    iSup₂_le fun k hk => hU k (by have := mem_intList_iff.1 hk; omega)
      (by have := mem_intList_iff.1 hk; omega),
    fun h1 x hx v hv => hC.conj_mem_left h1 hj hx hv,
    fun h1 x hx v hv => hC.conj_mem_right hi h1 hx hv⟩

end Abstract

section Coordinates

theorem toStd_two_zero (v : Fin 2 → ℤ) : toStd 2 v 0 = v 0 := by
  simp [toStd]

theorem toStd_two_one (v : Fin 2 → ℤ) : toStd 2 v 1 = 2 * v 1 - v 0 := by
  simp [toStd]

theorem mem_roots_coords_iff {γ : Fin 2 → ℤ} :
    γ ∈ roots (isFiniteType_cartanC 2) ∅ ↔
      (γ 0 = 1 ∧ γ 1 = 0) ∨ (γ 0 = -1 ∧ γ 1 = 0) ∨ (γ 0 = 2 ∧ γ 1 = 1) ∨ (γ 0 = -2 ∧ γ 1 = -1) ∨
      (γ 0 = 1 ∧ γ 1 = 1) ∨ (γ 0 = -1 ∧ γ 1 = -1) ∨ (γ 0 = 0 ∧ γ 1 = 1) ∨ (γ 0 = 0 ∧ γ 1 = -1) := by
  rw [roots_eq]
  constructor
  · rintro ⟨r, hr⟩
    have h0 := congrFun hr 0
    have h1 := congrFun hr 1
    clear hr
    rw [toStd_two_zero] at h0
    rw [toStd_two_one] at h1
    cases r with
    | positiveLong i => fin_cases i <;> simp [stdVec] at h0 h1 <;> omega
    | negativeLong i => fin_cases i <;> simp [stdVec] at h0 h1 <;> omega
    | difference i j hij =>
      fin_cases i <;> fin_cases j <;>
        first | exact absurd rfl hij | (simp [stdVec] at h0 h1; omega)
    | positiveSum i j hij =>
      fin_cases i <;> fin_cases j <;>
        first | exact absurd hij (by decide) | (simp [stdVec] at h0 h1; omega)
    | negativeSum i j hij =>
      fin_cases i <;> fin_cases j <;>
        first | exact absurd hij (by decide) | (simp [stdVec] at h0 h1; omega)
  · intro h
    have key : ∀ r : RootSubgroupIndex 2, stdVec r 0 = γ 0 → stdVec r 1 = 2 * γ 1 - γ 0 →
        ∃ r, stdVec r = toStd 2 γ := fun r h0 h1 => by
      refine ⟨r, funext fun k => ?_⟩
      fin_cases k
      · simpa [toStd_two_zero] using h0
      · simpa [toStd_two_one] using h1
    rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩ |
      ⟨h0, h1⟩
    · exact key (.difference 0 1 (by decide)) (by simp [stdVec]; omega) (by simp [stdVec]; omega)
    · exact key (.difference 1 0 (by decide)) (by simp [stdVec]; omega) (by simp [stdVec]; omega)
    · exact key (.positiveLong 0) (by simp [stdVec]; omega) (by simp [stdVec]; omega)
    · exact key (.negativeLong 0) (by simp [stdVec]; omega) (by simp [stdVec]; omega)
    · exact key (.positiveSum 0 1 (by decide)) (by simp [stdVec]; omega) (by simp [stdVec]; omega)
    · exact key (.negativeSum 0 1 (by decide)) (by simp [stdVec]; omega) (by simp [stdVec]; omega)
    · exact key (.positiveLong 1) (by simp [stdVec]; omega) (by simp [stdVec]; omega)
    · exact key (.negativeLong 1) (by simp [stdVec]; omega) (by simp [stdVec]; omega)

theorem octRoot_one : octRoot 1 = ![1, 0] := by simp [octRoot]
theorem octRoot_two : octRoot 2 = ![2, 1] := by simp [octRoot]
theorem octRoot_three : octRoot 3 = ![1, 1] := by simp [octRoot]
theorem octRoot_four : octRoot 4 = ![0, 1] := by simp [octRoot]
theorem octRoot_neg_one : octRoot (-1) = ![-1, 0] := by simp [octRoot]
theorem octRoot_neg_two : octRoot (-2) = ![-2, -1] := by simp [octRoot]
theorem octRoot_neg_three : octRoot (-3) = ![-1, -1] := by simp [octRoot]
theorem octRoot_neg_four : octRoot (-4) = ![0, -1] := by simp [octRoot]

theorem ext_fin_two {u v : Fin 2 → ℤ} (h0 : u 0 = v 0) (h1 : u 1 = v 1) : u = v := by
  funext k
  fin_cases k
  · exact h0
  · exact h1

theorem ht_fin_two (γ : Fin 2 → ℤ) : ht γ = γ 0 + γ 1 := by
  simp [ht, Fin.sum_univ_two]

theorem isRoot_four_iff {i : ℤ} :
    IsRoot 4 i ↔ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = -1 ∨ i = -2 ∨ i = -3 ∨ i = -4 := by
  unfold IsRoot
  omega

theorem octRoot_mem_roots' {i : ℤ} (hi : IsRoot 4 i) :
    octRoot i ∈ roots (isFiniteType_cartanC 2) ∅ := by
  rw [mem_roots_coords_iff]
  rcases isRoot_four_iff.1 hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [octRoot]

theorem octRoot_ht_pos {i : ℤ} (h1 : 1 ≤ i) (h4 : i ≤ 4) : 0 < ht (octRoot i) := by
  rw [ht_fin_two]
  rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl <;> simp [octRoot]

theorem octRoot_ht_neg {i : ℤ} (h1 : 1 ≤ i) (h4 : i ≤ 4) : ht (octRoot (-i)) < 0 := by
  rw [ht_fin_two]
  rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl <;> simp [octRoot]

theorem pos_root_cases {γ : Fin 2 → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanC 2) ∅)
    (hp : 0 < ht γ) : γ = octRoot 1 ∨ γ = octRoot 2 ∨ γ = octRoot 3 ∨ γ = octRoot 4 := by
  rw [mem_roots_coords_iff] at hγ
  rw [ht_fin_two] at hp
  have h : (γ 0 = 1 ∧ γ 1 = 0) ∨ (γ 0 = 2 ∧ γ 1 = 1) ∨ (γ 0 = 1 ∧ γ 1 = 1) ∨
      (γ 0 = 0 ∧ γ 1 = 1) := by omega
  rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact Or.inl (ext_fin_two (by simp [octRoot_one, h0]) (by simp [octRoot_one, h1]))
  · exact Or.inr (Or.inl (ext_fin_two (by simp [octRoot_two, h0]) (by simp [octRoot_two, h1])))
  · exact Or.inr (Or.inr (Or.inl (ext_fin_two (by simp [octRoot_three, h0])
      (by simp [octRoot_three, h1]))))
  · exact Or.inr (Or.inr (Or.inr (ext_fin_two (by simp [octRoot_four, h0])
      (by simp [octRoot_four, h1]))))

theorem octRoot_ne_two_smul {k : ℤ} (h1 : 1 ≤ k) (h4 : k ≤ 4) (δ : Fin 2 → ℤ) :
    octRoot k ≠ 2 • δ := by
  intro h
  have h0 := congrFun h 0
  have h1' := congrFun h 1
  rcases (by omega : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl <;>
    simp [octRoot] at h0 h1' <;> omega

end Coordinates

theorem octRoot_mem_roots (F : Type) [Field F] {i : ℤ} (hi : IsRoot 4 i) :
    octRoot i ∈ (rootDatum 2 F).roots :=
  octRoot_mem_roots' hi


section Commutators

variable (F : Type) [Field F]

theorem isRoot_four_of {k : ℤ} (h1 : 1 ≤ k) (h4 : k ≤ 4) : IsRoot 4 k := by
  unfold IsRoot
  omega

theorem isRoot_four_of_neg {k : ℤ} (h1 : 1 ≤ k) (h4 : k ≤ 4) : IsRoot 4 (-k) := by
  unfold IsRoot
  omega

theorem octRoot_mem_roots_of {k : ℤ} (h1 : 1 ≤ k) (h4 : k ≤ 4) :
    octRoot k ∈ (rootDatum 2 F).roots :=
  octRoot_mem_roots F (isRoot_four_of h1 h4)

theorem cone_coord {γ δ ε : Fin 2 → ℤ} {a b : ℕ} (h : ε = a • γ + b • δ) :
    ε 0 = a * γ 0 + b * δ 0 ∧ ε 1 = a * γ 1 + b * δ 1 := by
  subst h
  simp

theorem linIndep_of {γ δ : Fin 2 → ℤ}
    (h : ∀ a b : ℤ, a * γ 0 + b * δ 0 = 0 → a * γ 1 + b * δ 1 = 0 → a = 0 ∧ b = 0) :
    LinIndepPair γ δ := by
  intro a b hab
  refine h a b ?_ ?_
  · simpa using congrFun hab 0
  · simpa using congrFun hab 1

theorem octComm_aux {a b : ℤ} (ha : 1 ≤ a) (ha4 : a ≤ 4) (hb : 1 ≤ b) (hb4 : b ≤ 4)
    (hind : LinIndepPair (octRoot a) (octRoot b)) {S : Subgroup (StatedSp 2 F)}
    (hS : ∀ ε : Fin 2 → ℤ, ε ∈ openCone (rootDatum 2 F).roots (octRoot a) (octRoot b) →
      (rootDatum 2 F).rootGroup ε ≤ S) :
    ∀ x ∈ octGroup F a, ∀ y ∈ octGroup F b, ⁅x, y⁆ ∈ S := fun x hx y hy =>
  (iSup₂_le hS : (⨆ ε ∈ openCone (rootDatum 2 F).roots (octRoot a) (octRoot b),
      (rootDatum 2 F).rootGroup ε) ≤ S)
    ((steinbergExtras 2 F).commutator_mem (octRoot a) (octRoot_mem_roots_of F ha ha4)
      (octRoot b) (octRoot_mem_roots_of F hb hb4) hind x hx y hy)

theorem octComm_one_three :
    ∀ x ∈ octGroup F 1, ∀ y ∈ octGroup F 3, ⁅x, y⁆ ∈ octGroup F 2 :=
  octComm_aux F (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (linIndep_of fun a b h0 h1 => by simp [octRoot_one, octRoot_three] at h0 h1; omega)
    (fun ε hε => by
      obtain ⟨hr, a, b, ha, hb, he⟩ := hε
      have hr' := mem_roots_coords_iff.1 hr
      obtain ⟨h0, h1⟩ := cone_coord he
      simp [octRoot_one, octRoot_three] at h0 h1
      have hε : ε = octRoot 2 := by
        refine ext_fin_two ?_ ?_ <;> simp [octRoot_two] <;> omega
      subst hε
      exact le_rfl)

theorem octComm_one_four :
    ∀ x ∈ octGroup F 1, ∀ y ∈ octGroup F 4, ⁅x, y⁆ ∈ octGroup F 2 ⊔ octGroup F 3 :=
  octComm_aux F (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (linIndep_of fun a b h0 h1 => by simp [octRoot_one, octRoot_four] at h0 h1; omega)
    (fun ε hε => by
      obtain ⟨hr, a, b, ha, hb, he⟩ := hε
      have hr' := mem_roots_coords_iff.1 hr
      obtain ⟨h0, h1⟩ := cone_coord he
      simp [octRoot_one, octRoot_four] at h0 h1
      rcases (by omega : (ε 0 = 2 ∧ ε 1 = 1) ∨ (ε 0 = 1 ∧ ε 1 = 1)) with ⟨h2, h3⟩ | ⟨h2, h3⟩
      · have hε : ε = octRoot 2 := by
          refine ext_fin_two ?_ ?_ <;> simp [octRoot_two] <;> omega
        subst hε
        exact le_sup_left
      · have hε : ε = octRoot 3 := by
          refine ext_fin_two ?_ ?_ <;> simp [octRoot_three] <;> omega
        subst hε
        exact le_sup_right)

theorem octComm_one_two :
    ∀ x ∈ octGroup F 1, ∀ y ∈ octGroup F 2, ⁅x, y⁆ = 1 := fun x hx y hy =>
  Subgroup.mem_bot.1 (octComm_aux F (S := ⊥) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (linIndep_of fun a b h0 h1 => by simp [octRoot_one, octRoot_two] at h0 h1; omega)
    (fun ε hε => by
      obtain ⟨hr, a, b, ha, hb, he⟩ := hε
      have hr' := mem_roots_coords_iff.1 hr
      obtain ⟨h0, h1⟩ := cone_coord he
      simp [octRoot_one, octRoot_two] at h0 h1
      omega) x hx y hy)

theorem octComm_two_three :
    ∀ x ∈ octGroup F 2, ∀ y ∈ octGroup F 3, ⁅x, y⁆ = 1 := fun x hx y hy =>
  Subgroup.mem_bot.1 (octComm_aux F (S := ⊥) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (linIndep_of fun a b h0 h1 => by simp [octRoot_two, octRoot_three] at h0 h1; omega)
    (fun ε hε => by
      obtain ⟨hr, a, b, ha, hb, he⟩ := hε
      have hr' := mem_roots_coords_iff.1 hr
      obtain ⟨h0, h1⟩ := cone_coord he
      simp [octRoot_two, octRoot_three] at h0 h1
      omega) x hx y hy)

theorem octComm_two_four :
    ∀ x ∈ octGroup F 2, ∀ y ∈ octGroup F 4, ⁅x, y⁆ = 1 := fun x hx y hy =>
  Subgroup.mem_bot.1 (octComm_aux F (S := ⊥) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (linIndep_of fun a b h0 h1 => by simp [octRoot_two, octRoot_four] at h0 h1; omega)
    (fun ε hε => by
      obtain ⟨hr, a, b, ha, hb, he⟩ := hε
      have hr' := mem_roots_coords_iff.1 hr
      obtain ⟨h0, h1⟩ := cone_coord he
      simp [octRoot_two, octRoot_four] at h0 h1
      omega) x hx y hy)

theorem octComm_three_four :
    ∀ x ∈ octGroup F 3, ∀ y ∈ octGroup F 4, ⁅x, y⁆ = 1 := fun x hx y hy =>
  Subgroup.mem_bot.1 (octComm_aux F (S := ⊥) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (linIndep_of fun a b h0 h1 => by simp [octRoot_three, octRoot_four] at h0 h1; omega)
    (fun ε hε => by
      obtain ⟨hr, a, b, ha, hb, he⟩ := hε
      have hr' := mem_roots_coords_iff.1 hr
      obtain ⟨h0, h1⟩ := cone_coord he
      simp [octRoot_three, octRoot_four] at h0 h1
      omega) x hx y hy)

theorem octComm : OctComm (octGroup F) ((4 : ℕ) : ℤ) := by
  intro a b ha hab hb x hx y hy
  have hcases : (a = 1 ∧ b = 2) ∨ (a = 1 ∧ b = 3) ∨ (a = 1 ∧ b = 4) ∨ (a = 2 ∧ b = 3) ∨
      (a = 2 ∧ b = 4) ∨ (a = 3 ∧ b = 4) := by omega
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [octComm_one_two F x hx y hy]
    exact one_mem _
  · exact le_iSup₂_of_le (f := fun c (_ : c ∈ Set.Ioo (1 : ℤ) 3) => octGroup F c) 2
      (by simp [Set.mem_Ioo]) le_rfl (octComm_one_three F x hx y hy)
  · refine (sup_le (le_iSup₂_of_le (f := fun c (_ : c ∈ Set.Ioo (1 : ℤ) 4) => octGroup F c) 2
      (by simp [Set.mem_Ioo]) le_rfl) (le_iSup₂_of_le
        (f := fun c (_ : c ∈ Set.Ioo (1 : ℤ) 4) => octGroup F c) 3 (by simp [Set.mem_Ioo])
        le_rfl) : octGroup F 2 ⊔ octGroup F 3 ≤ _) (octComm_one_four F x hx y hy)
  · rw [octComm_two_three F x hx y hy]
    exact one_mem _
  · rw [octComm_two_four F x hx y hy]
    exact one_mem _
  · rw [octComm_three_four F x hx y hy]
    exact one_mem _

end Commutators


section Octagon

variable (F : Type) [Field F]

theorem octGroup_le_spU {k : ℤ} (h1 : 1 ≤ k) (h4 : k ≤ 4) : octGroup F k ≤ spU F :=
  rootGroup_le_posUnipotent (octRoot_mem_roots F (isRoot_four_of h1 h4)) (octRoot_ht_pos h1 h4)

theorem octGroup_neg_le_spUneg {k : ℤ} (h1 : 1 ≤ k) (h4 : k ≤ 4) : octGroup F (-k) ≤ spUneg F :=
  rootGroup_le_negUnipotent (octRoot_mem_roots F (isRoot_four_of_neg h1 h4))
    (octRoot_ht_neg h1 h4)

theorem spU_eq_iSup : spU F = ⨆ k ∈ intList 1 ((4 : ℕ) : ℤ), octGroup F k := by
  refine le_antisymm ?_ (iSup₂_le fun k hk => ?_)
  · show posUnipotent (rootDatum 2 F) ≤ _
    refine iSup₂_le fun γ hγ => ?_
    obtain ⟨hr, hp⟩ := hγ
    rcases pos_root_cases hr hp with rfl | rfl | rfl | rfl
    · exact le_iSup₂_of_le (f := fun k (_ : k ∈ intList 1 ((4 : ℕ) : ℤ)) => octGroup F k) 1
        (by simp [mem_intList_iff]) le_rfl
    · exact le_iSup₂_of_le (f := fun k (_ : k ∈ intList 1 ((4 : ℕ) : ℤ)) => octGroup F k) 2
        (by simp [mem_intList_iff]) le_rfl
    · exact le_iSup₂_of_le (f := fun k (_ : k ∈ intList 1 ((4 : ℕ) : ℤ)) => octGroup F k) 3
        (by simp [mem_intList_iff]) le_rfl
    · exact le_iSup₂_of_le (f := fun k (_ : k ∈ intList 1 ((4 : ℕ) : ℤ)) => octGroup F k) 4
        (by simp [mem_intList_iff]) le_rfl
  · obtain ⟨h1, h4⟩ := mem_intList_iff.1 hk
    exact octGroup_le_spU F h1 (by omega)

theorem spBruhatExtras : BruhatExtras (rootDatum 2 F) (torus 2 F) where
  borel_inf_negUnipotent := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxB, hxU⟩ := Subgroup.mem_inf.1 hx
    have hct := isCTGroupDatum 2 F
    rw [← SetLike.mem_coe, coe_borel (D := rootDatum 2 F) hct, Set.mem_mul] at hxB
    obtain ⟨t, htT, u, hu, rfl⟩ := hxB
    obtain ⟨d, rfl⟩ := SpExtras.exists_diagonal_of_mem_iSup_torus (n := 2) (F := F) htT
    have hpos : SpExtras.IdBelow (fun a => (1 : ℤ) * SpExtras.lvl a) 1 (SpExtras.mat 2 F u) :=
      SpExtras.idBelow_of_mem_iSup 1 {γ | γ ∈ roots (isFiniteType_cartanC 2) ∅ ∧ 0 < ht γ}
        (fun γ hγ => ⟨hγ.1, by have := hγ.2; omega⟩) hu
    have hneg : SpExtras.IdBelow (fun a => (-1 : ℤ) * SpExtras.lvl a) 1
        (SpExtras.mat 2 F (equivStatedSp 2 F (diagonal d) * u)) :=
      SpExtras.idBelow_of_mem_iSup (-1) {γ | γ ∈ roots (isFiniteType_cartanC 2) ∅ ∧ ht γ < 0}
        (fun γ hγ => ⟨hγ.1, by have := hγ.2; omega⟩) hxU
    have hd : ∀ a, Sum.elim (fun i => (d i : F)) (fun i => (((d i)⁻¹ : Fˣ) : F)) a = 1 := by
      intro a
      have h1 := hneg a a (by simp)
      rw [map_mul, SpExtras.mat_equiv_diagonal, Matrix.diagonal_mul, hpos a a (by simp)] at h1
      simpa using h1
    have hpos' : SpExtras.IdBelow (fun a => (1 : ℤ) * SpExtras.lvl a) 1
        (SpExtras.mat 2 F (equivStatedSp 2 F (diagonal d) * u)) := by
      intro a b hab
      rw [map_mul, SpExtras.mat_equiv_diagonal, Matrix.diagonal_mul, hpos a b hab, hd a, one_mul]
    rw [Subgroup.mem_bot]
    exact SpExtras.eq_one_of_idBelow hpos' hneg

private def octIdx (γ : Fin 2 → ℤ) : ℤ := 1 + γ 1 * (3 - γ 0)

private theorem octIdx_one : octIdx (octRoot 1) = 1 := by simp [octIdx, octRoot_one]
private theorem octIdx_two : octIdx (octRoot 2) = 2 := by simp [octIdx, octRoot_two]
private theorem octIdx_three : octIdx (octRoot 3) = 3 := by simp [octIdx, octRoot_three]
private theorem octIdx_four : octIdx (octRoot 4) = 4 := by simp [octIdx, octRoot_four]

theorem prodInjective_heights :
    ∀ f g : (Fin 2 → ℤ) → StatedSp 2 F,
      (∀ γ ∈ [octRoot 1, octRoot 4, octRoot 3, octRoot 2], f γ ∈ (rootDatum 2 F).rootGroup γ) →
      (∀ γ ∈ [octRoot 1, octRoot 4, octRoot 3, octRoot 2], g γ ∈ (rootDatum 2 F).rootGroup γ) →
      ([octRoot 1, octRoot 4, octRoot 3, octRoot 2].map f).prod =
        ([octRoot 1, octRoot 4, octRoot 3, octRoot 2].map g).prod →
      ∀ γ ∈ [octRoot 1, octRoot 4, octRoot 3, octRoot 2], f γ = g γ := by
  have hL : ∀ γ : Fin 2 → ℤ, γ ∈ [octRoot 1, octRoot 4, octRoot 3, octRoot 2] ↔
      γ ∈ (rootDatum 2 F).roots ∧ 0 < ht γ ∧ ∀ δ ∈ (rootDatum 2 F).roots, γ ≠ 2 • δ := by
    intro γ
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · intro h
      rcases h with rfl | rfl | rfl | rfl
      · exact ⟨octRoot_mem_roots_of F (by norm_num) (by norm_num),
          octRoot_ht_pos (by norm_num) (by norm_num),
          fun δ _ => octRoot_ne_two_smul (by norm_num) (by norm_num) δ⟩
      · exact ⟨octRoot_mem_roots_of F (by norm_num) (by norm_num),
          octRoot_ht_pos (by norm_num) (by norm_num),
          fun δ _ => octRoot_ne_two_smul (by norm_num) (by norm_num) δ⟩
      · exact ⟨octRoot_mem_roots_of F (by norm_num) (by norm_num),
          octRoot_ht_pos (by norm_num) (by norm_num),
          fun δ _ => octRoot_ne_two_smul (by norm_num) (by norm_num) δ⟩
      · exact ⟨octRoot_mem_roots_of F (by norm_num) (by norm_num),
          octRoot_ht_pos (by norm_num) (by norm_num),
          fun δ _ => octRoot_ne_two_smul (by norm_num) (by norm_num) δ⟩
    · rintro ⟨hr, hp, -⟩
      rcases pos_root_cases hr hp with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr h))
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inl h)
  have hnd : [octRoot 1, octRoot 4, octRoot 3, octRoot 2].Nodup := by decide
  have hsort : [octRoot 1, octRoot 4, octRoot 3, octRoot 2].Pairwise
      (fun γ δ => ht γ ≤ ht δ) := by
    simp [List.pairwise_cons, ht_fin_two, octRoot_one, octRoot_two, octRoot_three, octRoot_four]
  exact (steinbergExtras 2 F).prodInjective_pos _ hnd hL hsort

theorem octUnique :
    ∀ f g : ℤ → StatedSp 2 F,
      (∀ k ∈ intList 1 ((4 : ℕ) : ℤ), f k ∈ octGroup F k) →
      (∀ k ∈ intList 1 ((4 : ℕ) : ℤ), g k ∈ octGroup F k) →
      ((intList 1 ((4 : ℕ) : ℤ)).map f).prod = ((intList 1 ((4 : ℕ) : ℤ)).map g).prod →
        ∀ k ∈ intList 1 ((4 : ℕ) : ℤ), f k = g k := by
  have hl : intList 1 ((4 : ℕ) : ℤ) = [1, 2, 3, 4] := by decide
  have reorder : ∀ e : ℤ → StatedSp 2 F, (∀ k ∈ [1, 2, 3, 4], e k ∈ octGroup F k) →
      e 1 * (e 4 * (e 3 * e 2)) = e 1 * (e 2 * (e 3 * e 4)) := by
    intro e he
    have h23 : e 2 * e 3 = e 3 * e 2 :=
      commutatorElement_eq_one_iff_mul_comm.1 (octComm_two_three F _ (he 2 (by simp)) _
        (he 3 (by simp)))
    have h24 : e 2 * e 4 = e 4 * e 2 :=
      commutatorElement_eq_one_iff_mul_comm.1 (octComm_two_four F _ (he 2 (by simp)) _
        (he 4 (by simp)))
    have h34 : e 3 * e 4 = e 4 * e 3 :=
      commutatorElement_eq_one_iff_mul_comm.1 (octComm_three_four F _ (he 3 (by simp)) _
        (he 4 (by simp)))
    congr 1
    calc e 4 * (e 3 * e 2) = (e 4 * e 3) * e 2 := (mul_assoc _ _ _).symm
      _ = (e 3 * e 4) * e 2 := by rw [h34]
      _ = e 3 * (e 4 * e 2) := mul_assoc _ _ _
      _ = e 3 * (e 2 * e 4) := by rw [h24]
      _ = (e 3 * e 2) * e 4 := (mul_assoc _ _ _).symm
      _ = (e 2 * e 3) * e 4 := by rw [h23]
      _ = e 2 * (e 3 * e 4) := mul_assoc _ _ _
  intro f g hf hg hfg
  rw [hl] at hf hg hfg ⊢
  have key := prodInjective_heights F (fun γ => f (octIdx γ)) (fun γ => g (octIdx γ))
    (by
      intro γ hγ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
      rcases hγ with rfl | rfl | rfl | rfl
      · simp only [octIdx_one]; exact hf 1 (by simp)
      · simp only [octIdx_four]; exact hf 4 (by simp)
      · simp only [octIdx_three]; exact hf 3 (by simp)
      · simp only [octIdx_two]; exact hf 2 (by simp))
    (by
      intro γ hγ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
      rcases hγ with rfl | rfl | rfl | rfl
      · simp only [octIdx_one]; exact hg 1 (by simp)
      · simp only [octIdx_four]; exact hg 4 (by simp)
      · simp only [octIdx_three]; exact hg 3 (by simp)
      · simp only [octIdx_two]; exact hg 2 (by simp))
    (by
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, octIdx_one,
        octIdx_two, octIdx_three, octIdx_four]
      rw [reorder f hf, reorder g hg]
      simpa using hfg)
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · simpa [octIdx_one] using key (octRoot 1) (by simp)
  · simpa [octIdx_two] using key (octRoot 2) (by simp)
  · simpa [octIdx_three] using key (octRoot 3) (by simp)
  · simpa [octIdx_four] using key (octRoot 4) (by simp)

theorem spOctagon : SpOctagon F where
  ne_bot i hi := (steinbergExtras 2 F).ne_bot _ (octRoot_mem_roots F hi)
  invariant i hi h hh x hx := by
    have hct := isCTGroupDatum 2 F
    exact (Subgroup.mem_normalizer_iff.1
      (iSup_le_normalizer_rootGroup (D := rootDatum 2 F) hct (octRoot_mem_roots F hi) hh) x).1 hx
  carrier_eq := by
    have h := (octComm F).carrier_eq (i := 1) (j := ((4 : ℕ) : ℤ)) le_rfl le_rfl
    rw [← spU_eq_iSup F] at h
    exact h
  unique := octUnique F
  reverse_eq i j hi _ hj := (octComm F).reverse_eq hi hj
  subgroup i j hi _ hj := (octComm F).exists_subgroup (U := spU F)
    (fun k h1 h4 => octGroup_le_spU F h1 (by omega)) hi hj
  meet_one x hxB hx := by
    have hU : x ∈ spUneg F := by
      refine chainProd_subset (octGroup F) (spUneg F) _ (fun k hk => ?_) hx
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hk
      obtain ⟨h1, h4⟩ := mem_intList_iff.1 hj
      exact octGroup_neg_le_spUneg F h1 (by omega)
    have hmem : x ∈ borel (rootDatum 2 F) (torus 2 F) ⊓ negUnipotent (rootDatum 2 F) := ⟨hxB, hU⟩
    rw [(spBruhatExtras F).borel_inf_negUnipotent] at hmem
    exact Subgroup.mem_bot.1 hmem

theorem isNilpotent_spU : Group.IsNilpotent (spU F) := by
  refine CFSG.LieType.TitsSimplicity.isNilpotent_posUnipotent (steinbergExtras 2 F)
    (CFSG.LieType.TitsSimplicity.RootGroupCommutators.of_divisible_eq_empty rfl ?_)
  intro γ hγ x hx y hy
  obtain ⟨r, hr⟩ := SpExtras.exists_stdVec_of_mem_roots hγ
  obtain ⟨c, rfl⟩ := (SpExtras.mem_rootGroup_iff hr).1 hx
  obtain ⟨d, rfl⟩ := (SpExtras.mem_rootGroup_iff hr).1 hy
  rw [Commute, SemiconjBy, ← SpExtras.elt_add, ← SpExtras.elt_add, add_comm]

end Octagon


section Weyl

variable (F : Type) [Field F]

theorem reflection_zero_apply (v : Fin 2 → ℤ) :
    reflection (cartanC 2) 0 v = ![-v 0 + 2 * v 1, v 1] := by
  funext k
  fin_cases k
  · simp [reflection_apply, cartanC, Fin.sum_univ_two]
    ring
  · simp [reflection_apply, cartanC, Fin.sum_univ_two]

theorem reflection_one_apply (v : Fin 2 → ℤ) :
    reflection (cartanC 2) 1 v = ![v 0, v 0 - v 1] := by
  funext k
  fin_cases k
  · simp [reflection_apply, cartanC, Fin.sum_univ_two]
  · simp [reflection_apply, cartanC, Fin.sum_univ_two]
    ring

theorem map_conj_inv_simple {K : Type*} [Group K] (D : CFSG.LieType.Universal.UniversalRootDatum K)
    {m : K}
    {i : Fin D.rank} (hm : ActsAs D m ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i))
    {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) :
    (D.rootGroup γ).map (MulAut.conj m⁻¹).toMonoidHom =
      D.rootGroup (reflection D.cartan i γ) := by
  have h := hm.inv γ hγ
  rw [CoxeterSystem.inv_simple, weylAction_simple] at h
  exact h

theorem conjBy_octGroup_simple {m : StatedSp 2 F} {k : Fin 2}
    (hm : ActsAs (rootDatum 2 F) m
      ((coxeterMatrix (rootDatum 2 F).isFiniteType).toCoxeterSystem.simple k)) {i : ℤ}
    (hi : IsRoot 4 i) :
    conjBy m (octGroup F i) =
      (rootDatum 2 F).rootGroup (reflection (cartanC 2) k (octRoot i)) :=
  map_conj_inv_simple (rootDatum 2 F) hm (octRoot_mem_roots F hi)

theorem spAction₁ {m : StatedSp 2 F}
    (hm : ActsAs (rootDatum 2 F) m
      ((coxeterMatrix (rootDatum 2 F).isFiniteType).toCoxeterSystem.simple (0 : Fin 2))) :
    conjBy m (octGroup F 1) = octGroup F (-1) ∧ conjBy m (octGroup F (-1)) = octGroup F 1 ∧
      ∀ i : ℤ, 2 ≤ i → i ≤ 4 →
        conjBy m (octGroup F i) = octGroup F (((4 : ℕ) : ℤ) + 2 - i) ∧
          conjBy m (octGroup F (-i)) = octGroup F (-(((4 : ℕ) : ℤ) + 2 - i)) := by
  have key : ∀ {i j : ℤ}, IsRoot 4 i → reflection (cartanC 2) 0 (octRoot i) = octRoot j →
      conjBy m (octGroup F i) = octGroup F j := fun hi hj =>
    (conjBy_octGroup_simple F hm hi).trans (congrArg (rootDatum 2 F).rootGroup hj)
  refine ⟨key (isRoot_four_of (by norm_num) (by norm_num)) ?_,
    key (isRoot_four_of_neg (by norm_num) (by norm_num)) ?_, fun i h2 h4 => ?_⟩
  · rw [reflection_zero_apply, octRoot_one, octRoot_neg_one]
    simp
  · rw [reflection_zero_apply, octRoot_neg_one, octRoot_one]
    simp
  · rcases (by omega : i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl
    · rw [show ((4 : ℕ) : ℤ) + 2 - 2 = 4 by norm_num]
      refine ⟨key (isRoot_four_of (by norm_num) (by norm_num)) ?_,
        key (isRoot_four_of_neg (by norm_num) (by norm_num)) ?_⟩
      · rw [reflection_zero_apply, octRoot_two, octRoot_four]
        simp
      · rw [reflection_zero_apply, octRoot_neg_two, octRoot_neg_four]
        simp
    · rw [show ((4 : ℕ) : ℤ) + 2 - 3 = 3 by norm_num]
      refine ⟨key (isRoot_four_of (by norm_num) (by norm_num)) ?_,
        key (isRoot_four_of_neg (by norm_num) (by norm_num)) ?_⟩
      · rw [reflection_zero_apply, octRoot_three]
        simp
      · rw [reflection_zero_apply, octRoot_neg_three]
        simp
    · rw [show ((4 : ℕ) : ℤ) + 2 - 4 = 2 by norm_num]
      refine ⟨key (isRoot_four_of (by norm_num) (by norm_num)) ?_,
        key (isRoot_four_of_neg (by norm_num) (by norm_num)) ?_⟩
      · rw [reflection_zero_apply, octRoot_four, octRoot_two]
        simp
      · rw [reflection_zero_apply, octRoot_neg_four, octRoot_neg_two]
        simp

theorem spAction₂ {m : StatedSp 2 F}
    (hm : ActsAs (rootDatum 2 F) m
      ((coxeterMatrix (rootDatum 2 F).isFiniteType).toCoxeterSystem.simple (1 : Fin 2))) :
    conjBy m (octGroup F 4) = octGroup F (-4) ∧ conjBy m (octGroup F (-4)) = octGroup F 4 ∧
      ∀ i : ℤ, 1 ≤ i → i ≤ 3 → conjBy m (octGroup F i) = octGroup F (4 - i) ∧
        conjBy m (octGroup F (-i)) = octGroup F (-(4 - i)) := by
  have key : ∀ {i j : ℤ}, IsRoot 4 i → reflection (cartanC 2) 1 (octRoot i) = octRoot j →
      conjBy m (octGroup F i) = octGroup F j := fun hi hj =>
    (conjBy_octGroup_simple F hm hi).trans (congrArg (rootDatum 2 F).rootGroup hj)
  refine ⟨key (isRoot_four_of (by norm_num) (by norm_num)) ?_,
    key (isRoot_four_of_neg (by norm_num) (by norm_num)) ?_, fun i h1 h3 => ?_⟩
  · rw [reflection_one_apply, octRoot_four, octRoot_neg_four]
    simp
  · rw [reflection_one_apply, octRoot_neg_four, octRoot_four]
    simp
  · rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl
    · rw [show (4 : ℤ) - 1 = 3 by norm_num]
      refine ⟨key (isRoot_four_of (by norm_num) (by norm_num)) ?_,
        key (isRoot_four_of_neg (by norm_num) (by norm_num)) ?_⟩
      · rw [reflection_one_apply, octRoot_one, octRoot_three]
        simp
      · rw [reflection_one_apply, octRoot_neg_one, octRoot_neg_three]
        simp
    · rw [show (4 : ℤ) - 2 = 2 by norm_num]
      refine ⟨key (isRoot_four_of (by norm_num) (by norm_num)) ?_,
        key (isRoot_four_of_neg (by norm_num) (by norm_num)) ?_⟩
      · rw [reflection_one_apply, octRoot_two]
        simp
      · rw [reflection_one_apply, octRoot_neg_two]
        simp
    · rw [show (4 : ℤ) - 3 = 1 by norm_num]
      refine ⟨key (isRoot_four_of (by norm_num) (by norm_num)) ?_,
        key (isRoot_four_of_neg (by norm_num) (by norm_num)) ?_⟩
      · rw [reflection_one_apply, octRoot_three, octRoot_one]
        simp
      · rw [reflection_one_apply, octRoot_neg_three, octRoot_neg_one]
        simp

theorem spAction₂' {m : StatedSp 2 F}
    (hm : ActsAs (rootDatum 2 F) m
      ((coxeterMatrix (rootDatum 2 F).isFiniteType).toCoxeterSystem.simple (1 : Fin 2))) :
    conjBy m (octGroup F ((4 : ℕ) : ℤ)) = octGroup F (-((4 : ℕ) : ℤ)) ∧
      conjBy m (octGroup F (-((4 : ℕ) : ℤ))) = octGroup F ((4 : ℕ) : ℤ) ∧
      ∀ i : ℤ, 1 ≤ i → i ≤ ((4 : ℕ) : ℤ) - 1 →
        conjBy m (octGroup F i) = octGroup F (((4 : ℕ) : ℤ) - i) ∧
          conjBy m (octGroup F (-i)) = octGroup F (-(((4 : ℕ) : ℤ) - i)) := by
  obtain ⟨h1, h2, h3⟩ := spAction₂ F hm
  refine ⟨by simpa using h1, by simpa using h2, fun i hi1 hi3 => ?_⟩
  simpa using h3 i hi1 (by omega)

end Weyl


end CFSG.GH74.GLS.SP
