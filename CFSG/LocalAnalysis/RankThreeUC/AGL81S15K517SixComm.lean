module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K517SixLift
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KParU5Lift
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGenCentre

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K517Six

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.RootSystem
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

section Roots

variable {K : Type*} [Group K] (D : UniversalRootDatum K)

theorem reflection_mem_roots {i : Fin D.rank} {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) :
    reflection D.cartan i γ ∈ D.roots := by
  have := weylAction_mem_roots D.isFiniteType
    ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i) hγ
  rwa [weylAction_simple] at this

theorem false_of_root_mixed {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) {i j : Fin D.rank}
    (hi : 0 < γ i) (hj : γ j < 0) : False := by
  rcases nonneg_or_nonpos D.isFiniteType D.divisible hγ with h | h
  · exact absurd (h j) (not_le.2 hj)
  · exact absurd (h i) (not_le.2 hi)

theorem not_mem_roots_add_of_cartan_zero {i j : Fin D.rank} (hij : i ≠ j) (h0 : D.cartan i j = 0)
    {a b : ℤ} (ha : 0 < a) (hb : 0 < b) :
    (a • (Pi.single i 1 : Fin D.rank → ℤ) + b • (Pi.single j 1 : Fin D.rank → ℤ)) ∉ D.roots := by
  intro h
  have h' := reflection_mem_roots D (i := i) h
  rw [reflection_apply_coroot, map_add, map_zsmul, map_zsmul, coroot_single, coroot_single,
    D.isFiniteType.apply_self, h0] at h'
  refine false_of_root_mixed D h' (i := j) (j := i) ?_ ?_
  · simp [Pi.single_apply, hij.symm, hb]
  · simp [Pi.single_apply, hij, hij.symm]
    omega

end Roots

section Comm

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem single_mem_roots (i : Fin D.rank) : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
  (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i

theorem neg_single_mem_roots (i : Fin D.rank) : (-Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
  (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ (single_mem_roots i)

theorem neg_mem_roots {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) : -γ ∈ D.roots :=
  (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ hγ

theorem commute_of_open_cone_empty (hext : SteinbergExtras D n H) {γ δ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) (hδ : δ ∈ D.roots) (hind : LinIndepPair γ δ)
    (hcone : ∀ a b : ℕ, 0 < a → 0 < b → a • γ + b • δ ∉ D.roots) :
    ∀ x ∈ D.rootGroup γ, ∀ y ∈ D.rootGroup δ, x * y = y * x := by
  intro x hx y hy
  have h := hext.commutator_mem γ hγ δ hδ hind x hx y hy
  have hbot : (⨆ ε ∈ openCone D.roots γ δ, D.rootGroup ε) = ⊥ := by
    refine iSup₂_eq_bot.2 fun ε hε => ?_
    exfalso
    obtain ⟨hεr, a, b, ha, hb, rfl⟩ := hε
    exact hcone a b ha hb hεr
  rw [hbot, Subgroup.mem_bot] at h
  exact commutatorElement_eq_one_iff_mul_comm.1 h

theorem commute_sup {G : Type*} [Group G] {P₁ P₂ Q₁ Q₂ : Subgroup G}
    (h₁₁ : ∀ x ∈ P₁, ∀ y ∈ Q₁, x * y = y * x) (h₁₂ : ∀ x ∈ P₁, ∀ y ∈ Q₂, x * y = y * x)
    (h₂₁ : ∀ x ∈ P₂, ∀ y ∈ Q₁, x * y = y * x) (h₂₂ : ∀ x ∈ P₂, ∀ y ∈ Q₂, x * y = y * x) :
    ∀ x ∈ P₁ ⊔ P₂, ∀ y ∈ Q₁ ⊔ Q₂, x * y = y * x := by
  have key : ∀ (Q : Subgroup G), (∀ x ∈ P₁, ∀ y ∈ Q, x * y = y * x) →
      (∀ x ∈ P₂, ∀ y ∈ Q, x * y = y * x) → ∀ x ∈ P₁ ⊔ P₂, ∀ y ∈ Q, x * y = y * x := by
    intro Q hQ₁ hQ₂ x hx y hy
    have hle : P₁ ⊔ P₂ ≤ Subgroup.centralizer ({y} : Set G) := by
      refine sup_le (fun z hz => ?_) (fun z hz => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        simp only [Set.mem_singleton_iff, forall_eq]
        exact (hQ₁ z hz y hy).symm
      · rw [Subgroup.mem_centralizer_iff]
        simp only [Set.mem_singleton_iff, forall_eq]
        exact (hQ₂ z hz y hy).symm
    have := Subgroup.mem_centralizer_iff.1 (hle hx) y rfl
    exact this.symm
  have hQ₁ := key Q₁ h₁₁ h₂₁
  have hQ₂ := key Q₂ h₁₂ h₂₂
  intro x hx y hy
  have hle : Q₁ ⊔ Q₂ ≤ Subgroup.centralizer ((P₁ ⊔ P₂ : Subgroup G) : Set G) := by
    refine sup_le (fun z hz => ?_) (fun z hz => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact hQ₁ w hw z hz
    · rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact hQ₂ w hw z hz
  exact Subgroup.mem_centralizer_iff.1 (hle hy) x hx

theorem linIndepPair_single {i j : Fin D.rank} (hij : i ≠ j) {s t : ℤ} (hs : s ≠ 0) (ht : t ≠ 0) :
    LinIndepPair (s • (Pi.single i 1 : Fin D.rank → ℤ)) (t • (Pi.single j 1 : Fin D.rank → ℤ)) := by
  intro a b h
  have h1 := congrFun h i
  have h2 := congrFun h j
  simp [Pi.single_apply, hij, hij.symm] at h1 h2
  tauto

theorem not_mem_roots_nsmul_add_of_cartan_zero {i j : Fin D.rank} (hij : i ≠ j)
    (h0 : D.cartan i j = 0) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (a • (Pi.single i 1 : Fin D.rank → ℤ) + b • (Pi.single j 1 : Fin D.rank → ℤ)) ∉ D.roots := by
  have := not_mem_roots_add_of_cartan_zero D hij h0 (a := a) (b := b) (by exact_mod_cast ha)
    (by exact_mod_cast hb)
  simpa [natCast_zsmul] using this

theorem rootGroup_commute_of_cartan_zero (hext : SteinbergExtras D n H) {i j : Fin D.rank}
    (hij : i ≠ j) (h0 : D.cartan i j = 0) {s t : ℤ} (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) :
    ∀ x ∈ D.rootGroup (s • Pi.single i 1), ∀ y ∈ D.rootGroup (t • Pi.single j 1), x * y = y * x := by
  have hm : ∀ (e : ℤ) (k : Fin D.rank), (e = 1 ∨ e = -1) →
      (e • (Pi.single k 1 : Fin D.rank → ℤ)) ∈ D.roots := by
    intro e k he
    rcases he with rfl | rfl
    · simpa using single_mem_roots (D := D) k
    · simpa using neg_single_mem_roots (D := D) k
  refine commute_of_open_cone_empty hext (hm s i hs) (hm t j ht)
    (linIndepPair_single hij (by rcases hs with rfl | rfl <;> norm_num)
      (by rcases ht with rfl | rfl <;> norm_num)) ?_
  intro a b ha hb
  have haz : (0 : ℤ) < a := by exact_mod_cast ha
  have hbz : (0 : ℤ) < b := by exact_mod_cast hb
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  · simpa using not_mem_roots_nsmul_add_of_cartan_zero (D := D) hij h0 ha hb
  · intro h
    refine false_of_root_mixed D h (i := i) (j := j) ?_ ?_
    · simp [Pi.single_apply, hij.symm, ha]
    · simp [Pi.single_apply, hij, hb]
  · intro h
    refine false_of_root_mixed D h (i := j) (j := i) ?_ ?_
    · simp [Pi.single_apply, hij.symm, hb]
    · simp [Pi.single_apply, hij, ha]
  · intro h
    have h' := neg_mem_roots (D := D) h
    refine not_mem_roots_nsmul_add_of_cartan_zero (D := D) hij h0 ha hb ?_
    convert h' using 1
    simp only [neg_smul, one_smul, smul_neg, neg_add_rev, neg_neg]
    abel

theorem rankOne_commute_of_cartan_zero (hext : SteinbergExtras D n H) {i j : Fin D.rank}
    (hij : i ≠ j) (h0 : D.cartan i j = 0) :
    ∀ x ∈ rankOne D.rootGroup i, ∀ y ∈ rankOne D.rootGroup j, x * y = y * x := by
  have h := fun s t hs ht => rootGroup_commute_of_cartan_zero hext hij h0 (s := s) (t := t) hs ht
  refine commute_sup (h₁₁ := ?_) (h₁₂ := ?_) (h₂₁ := ?_) (h₂₂ := ?_)
  · simpa using h 1 1 (Or.inl rfl) (Or.inl rfl)
  · simpa using h 1 (-1) (Or.inl rfl) (Or.inr rfl)
  · simpa using h (-1) 1 (Or.inr rfl) (Or.inl rfl)
  · simpa using h (-1) (-1) (Or.inr rfl) (Or.inr rfl)

end Comm

section B2

variable {K : Type*} [Group K] (D : UniversalRootDatum K)

@[expose] def vec2 (i j : Fin D.rank) (c₁ c₂ : ℤ) : Fin D.rank → ℤ :=
  c₁ • Pi.single i 1 + c₂ • Pi.single j 1

variable {D} {i j : Fin D.rank}

theorem vec2_apply_left (hij : i ≠ j) (c₁ c₂ : ℤ) : vec2 D i j c₁ c₂ i = c₁ := by
  simp [vec2, Pi.single_apply, hij.symm]

theorem vec2_apply_right (hij : i ≠ j) (c₁ c₂ : ℤ) : vec2 D i j c₁ c₂ j = c₂ := by
  simp [vec2, Pi.single_apply, hij]

theorem reflection_vec2_left (hij : i ≠ j) (hAij : D.cartan i j = -1) (c₁ c₂ : ℤ) :
    reflection D.cartan i (vec2 D i j c₁ c₂) = vec2 D i j (c₂ - c₁) c₂ := by
  rw [reflection_apply_coroot]
  simp only [vec2, map_add, map_zsmul, coroot_single, D.isFiniteType.apply_self, hAij,
    smul_eq_mul]
  ext k
  by_cases hki : k = i
  · subst hki
    simp [Pi.single_apply, hij.symm]
    ring
  · by_cases hkj : k = j
    · subst hkj
      simp [Pi.single_apply, hij]
    · simp [Pi.single_apply, hki, hkj]

theorem reflection_vec2_right (hij : i ≠ j) (hAji : D.cartan j i = -2) (c₁ c₂ : ℤ) :
    reflection D.cartan j (vec2 D i j c₁ c₂) = vec2 D i j c₁ (2 * c₁ - c₂) := by
  rw [reflection_apply_coroot]
  simp only [vec2, map_add, map_zsmul, coroot_single, D.isFiniteType.apply_self, hAji,
    smul_eq_mul]
  ext k
  by_cases hki : k = i
  · subst hki
    simp [Pi.single_apply, hij]
  · by_cases hkj : k = j
    · subst hkj
      simp [Pi.single_apply, hij.symm]
      ring
    · simp [Pi.single_apply, hki, hkj]

theorem vec2_left_mem_roots (hij : i ≠ j) (hAij : D.cartan i j = -1) {c₁ c₂ : ℤ}
    (h : vec2 D i j c₁ c₂ ∈ D.roots) : vec2 D i j (c₂ - c₁) c₂ ∈ D.roots := by
  have := reflection_mem_roots D (i := i) h
  rwa [reflection_vec2_left hij hAij] at this

theorem vec2_right_mem_roots (hij : i ≠ j) (hAji : D.cartan j i = -2) {c₁ c₂ : ℤ}
    (h : vec2 D i j c₁ c₂ ∈ D.roots) : vec2 D i j c₁ (2 * c₁ - c₂) ∈ D.roots := by
  have := reflection_mem_roots D (i := j) h
  rwa [reflection_vec2_right hij hAji] at this

theorem vec2_sign (hij : i ≠ j) {c₁ c₂ : ℤ} (h : vec2 D i j c₁ c₂ ∈ D.roots) :
    (0 ≤ c₁ ∧ 0 ≤ c₂) ∨ (c₁ ≤ 0 ∧ c₂ ≤ 0) := by
  rcases nonneg_or_nonpos D.isFiniteType D.divisible h with hp | hn
  · left
    exact ⟨by simpa [vec2_apply_left hij] using hp i, by simpa [vec2_apply_right hij] using hp j⟩
  · right
    exact ⟨by simpa [vec2_apply_left hij] using hn i, by simpa [vec2_apply_right hij] using hn j⟩

theorem root_primitive (hdiv : D.divisible = ∅) {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) {d : ℤ}
    {u : Fin D.rank → ℤ} (h : γ = d • u) : d = 1 ∨ d = -1 := by
  rcases hγ with ⟨w, k, rfl⟩ | ⟨w, k, hk, rfl⟩
  · have h1 := congrArg (weylAction D.isFiniteType w⁻¹) h
    rw [weylAction_inv_apply_apply, map_zsmul] at h1
    have h2 := congrFun h1 k
    simp at h2
    exact Int.eq_one_or_neg_one_of_mul_eq_one' h2.symm |>.imp (fun h => h.1) (fun h => h.1)
  · exact absurd hk (by simp [hdiv])

variable (hdiv : D.divisible = ∅) (hij : i ≠ j) (hAij : D.cartan i j = -1)
  (hAji : D.cartan j i = -2)

include hdiv hij hAij hAji in
theorem roots_B2 {c₁ c₂ : ℤ} (h : vec2 D i j c₁ c₂ ∈ D.roots) :
    (c₂ = 0 ∨ c₁ = 0 ∨ c₁ = c₂ ∨ c₂ = 2 * c₁) ∧ ∀ d : ℤ, d ∣ c₁ → d ∣ c₂ → d = 1 ∨ d = -1 := by
  refine ⟨?_, ?_⟩
  · have h1 := vec2_left_mem_roots hij hAij h
    have h2 := vec2_right_mem_roots hij hAji h
    have h3 := vec2_right_mem_roots hij hAji h1
    have h4 := vec2_left_mem_roots hij hAij h2
    have h5 := vec2_left_mem_roots hij hAij h3
    have h6 := vec2_right_mem_roots hij hAji h4
    have s0 := vec2_sign hij h
    have s1 := vec2_sign hij h1
    have s2 := vec2_sign hij h2
    have s3 := vec2_sign hij h3
    have s4 := vec2_sign hij h4
    have s5 := vec2_sign hij h5
    have s6 := vec2_sign hij h6
    omega
  · intro d hd1 hd2
    obtain ⟨x, hx⟩ := hd1
    obtain ⟨y, hy⟩ := hd2
    refine root_primitive hdiv h (u := vec2 D i j x y) ?_
    rw [hx, hy]
    simp [vec2, smul_add, mul_smul]

include hdiv hij hAij hAji in
theorem not_mem_roots_B2_cone {a b : ℤ} (ha : 0 < a) (hb : 0 < b) {s t : ℤ}
    (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) :
    vec2 D i j (s * a + t * b) (2 * t * b) ∉ D.roots := by
  intro h
  obtain ⟨hdisj, hprim⟩ := roots_B2 hdiv hij hAij hAji h
  have hnp : ¬ ∃ w₁ w₂ : ℤ, s * a + t * b = 2 * b * w₁ ∧ 2 * t * b = 2 * b * w₂ := by
    rintro ⟨w₁, w₂, e₁, e₂⟩
    have := hprim (2 * b) ⟨w₁, e₁⟩ ⟨w₂, e₂⟩
    omega
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> rcases hdisj with h0 | h0 | h0 | h0 <;>
    first
    | omega
    | exact hnp ⟨1, 1, by omega, by omega⟩
    | exact hnp ⟨0, 1, by omega, by omega⟩
    | exact hnp ⟨0, -1, by omega, by omega⟩
    | exact hnp ⟨-1, -1, by omega, by omega⟩
    | exact hnp ⟨1, -1, by omega, by omega⟩

end B2

section B2Group

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {i j : Fin D.rank}

theorem vec2_one_zero : vec2 D i j 1 0 = Pi.single i 1 := by simp [vec2]

theorem vec2_neg_one_zero : vec2 D i j (-1) 0 = -Pi.single i 1 := by simp [vec2]

theorem vec2_nsmul (a : ℕ) (x y : ℤ) : a • vec2 D i j x y = vec2 D i j (a * x) (a * y) := by
  simp only [vec2, smul_add, ← natCast_zsmul, smul_smul]

theorem vec2_add (x y x' y' : ℤ) :
    vec2 D i j x y + vec2 D i j x' y' = vec2 D i j (x + x') (y + y') := by
  simp only [vec2, add_smul]
  abel

variable (hdiv : D.divisible = ∅) (hij : i ≠ j) (hAij : D.cartan i j = -1)
  (hAji : D.cartan j i = -2)

include hdiv hij hAij hAji in
theorem vec2_mem_roots_B2 {t : ℤ} (ht : t = 1 ∨ t = -1) : vec2 D i j t (2 * t) ∈ D.roots := by
  have h1 : vec2 D i j 1 (2 * 1 - 0) ∈ D.roots := by
    refine vec2_right_mem_roots hij hAji ?_
    rw [vec2_one_zero]
    exact single_mem_roots i
  rcases ht with rfl | rfl
  · simpa using h1
  · have := neg_mem_roots (D := D) h1
    have e : vec2 D i j (-1) (2 * -1) = -vec2 D i j 1 (2 * 1 - 0) := by
      funext k
      simp only [vec2, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
      ring
    rw [e]
    exact this

include hdiv hij hAij hAji in
theorem rootGroup_conj_commute_B2 (hext : SteinbergExtras D n H) {s t : ℤ}
    (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) :
    ∀ x ∈ D.rootGroup (vec2 D i j s 0), ∀ y ∈ D.rootGroup (vec2 D i j t (2 * t)),
      x * y = y * x := by
  have hγ : vec2 D i j s 0 ∈ D.roots := by
    rcases hs with rfl | rfl
    · rw [vec2_one_zero]; exact single_mem_roots i
    · rw [vec2_neg_one_zero]; exact neg_single_mem_roots i
  refine commute_of_open_cone_empty hext hγ (vec2_mem_roots_B2 hdiv hij hAij hAji ht) ?_ ?_
  · intro a b h
    have h1 := congrFun h i
    have h2 := congrFun h j
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, vec2_apply_left hij,
      vec2_apply_right hij, smul_eq_mul] at h1 h2
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> constructor <;> omega
  · intro a b ha hb
    rw [vec2_nsmul, vec2_nsmul, vec2_add]
    have haz : (0 : ℤ) < a := by exact_mod_cast ha
    have hbz : (0 : ℤ) < b := by exact_mod_cast hb
    have := not_mem_roots_B2_cone hdiv hij hAij hAji haz hbz hs ht
    have e1 : ((a : ℤ) * s + (b : ℤ) * t) = s * a + t * b := by ring
    have e2 : ((a : ℤ) * 0 + (b : ℤ) * (2 * t)) = 2 * t * b := by ring
    rw [e1, e2]
    exact this

end B2Group

section B2Rank

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {i j : Fin D.rank}
  (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
    (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)
  (hdiv : D.divisible = ∅) (hij : i ≠ j) (hAij : D.cartan i j = -1) (hAji : D.cartan j i = -2)

include hct hdiv hij hAij hAji in
theorem conj_rootGroup_B2 {s : ℤ} (hs : s = 1 ∨ s = -1) {y : K}
    (hy : y ∈ D.rootGroup (vec2 D i j s 0)) :
    n j * y * (n j)⁻¹ ∈ D.rootGroup (vec2 D i j s (2 * s)) := by
  have hγ : vec2 D i j s 0 ∈ D.roots := by
    rcases hs with rfl | rfl
    · rw [vec2_one_zero]; exact single_mem_roots i
    · rw [vec2_neg_one_zero]; exact neg_single_mem_roots i
  have := hct.conj_mem j (vec2 D i j s 0) hγ y hy
  rwa [weylAction_simple, reflection_vec2_right hij hAji, sub_zero] at this

include hct hext hdiv hij hAij hAji in
theorem rankOne_conj_commute_of_cartan_B2 :
    ∀ x ∈ rankOne D.rootGroup i, ∀ y ∈ rankOne D.rootGroup i,
      x * (n j * y * (n j)⁻¹) = (n j * y * (n j)⁻¹) * x := by
  have hP : rankOne D.rootGroup i =
      D.rootGroup (vec2 D i j 1 0) ⊔ D.rootGroup (vec2 D i j (-1) 0) := by
    rw [vec2_one_zero, vec2_neg_one_zero]
    rfl
  have hcomm := commute_sup (P₁ := D.rootGroup (vec2 D i j 1 0))
    (P₂ := D.rootGroup (vec2 D i j (-1) 0)) (Q₁ := D.rootGroup (vec2 D i j 1 (2 * 1)))
    (Q₂ := D.rootGroup (vec2 D i j (-1) (2 * -1)))
    (rootGroup_conj_commute_B2 hdiv hij hAij hAji hext (Or.inl rfl) (Or.inl rfl))
    (rootGroup_conj_commute_B2 hdiv hij hAij hAji hext (Or.inl rfl) (Or.inr rfl))
    (rootGroup_conj_commute_B2 hdiv hij hAij hAji hext (Or.inr rfl) (Or.inl rfl))
    (rootGroup_conj_commute_B2 hdiv hij hAij hAji hext (Or.inr rfl) (Or.inr rfl))
  have hle : rankOne D.rootGroup i ≤
      (D.rootGroup (vec2 D i j 1 (2 * 1)) ⊔ D.rootGroup (vec2 D i j (-1) (2 * -1))).comap
        (MulAut.conj (n j)).toMonoidHom := by
    rw [hP]
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · exact Subgroup.mem_sup_left (conj_rootGroup_B2 hct hdiv hij hAij hAji (Or.inl rfl) hy)
    · exact Subgroup.mem_sup_right (conj_rootGroup_B2 hct hdiv hij hAij hAji (Or.inr rfl) hy)
  intro x hx y hy
  rw [hP] at hx
  exact hcomm x hx _ (hle hy)

end B2Rank

section E9

variable {K : Type*} [Group K] {W : Type*} [Group W] [Finite W] {L : Subgroup W} {Y : Type*}
  [Group Y] {q : ↥L →* Y} {π : K →* Y}

theorem two_le_pRank_of_images (hq : q.ker ≤ Subgroup.center ↥L) (hπ : π.ker ≤ Subgroup.center K)
    {Hs : Subgroup ↥L} {a b m : K} (ha : π a ∈ Hs.map q) (hb : π b ∈ Hs.map q)
    (hm : π m ∈ Hs.map q) (ha3 : a ^ 3 = 1) (ha1 : a ∉ Subgroup.center K) (hb3 : b ^ 3 = 1)
    (hb1 : b ∉ Subgroup.center K) (hma : m * a * m⁻¹ = a⁻¹) (hab : a * b = b * a)
    (hmb : m * b = b * m) : 2 ≤ CFSG.Open.pRank 3 Hs := by
  refine two_le_pRank_three_of_commuting_images hq ha hb hm ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← map_pow, ha3, map_one]
  · intro h
    exact ha1 (hπ (MonoidHom.mem_ker.2 h))
  · rw [← map_pow, hb3, map_one]
  · intro h
    exact hb1 (hπ (MonoidHom.mem_ker.2 h))
  · have := congrArg π hma
    simpa [map_mul, map_inv] using this
  · rw [← map_mul, ← map_mul, hab]
  · rw [← map_mul, ← map_mul, hmb]

variable {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
  {i j : Fin D.rank}

theorem two_le_pRank_of_orthogonal_nodes (hq : q.ker ≤ Subgroup.center ↥L)
    (hπ : π.ker ≤ Subgroup.center K) {Hs : Subgroup ↥L}
    (hi : (rankOne D.rootGroup i).map π ≤ Hs.map q) (hj : (rankOne D.rootGroup j).map π ≤ Hs.map q)
    (hoi : OddNode (rankOne D.rootGroup i) 3) (hoj : OddNode (rankOne D.rootGroup j) 3)
    (hcomm : ∀ x ∈ rankOne D.rootGroup i, ∀ y ∈ rankOne D.rootGroup j, x * y = y * x) :
    2 ≤ CFSG.Open.pRank 3 Hs := by
  obtain ⟨w, hwR, m, hmR, hw3, hw1, hm⟩ := hoi
  obtain ⟨w', hw'R, m', hm'R, hw'3, hw'1, hm'⟩ := hoj
  refine two_le_pRank_of_images hq hπ (a := w) (b := w') (m := m) (hi ⟨w, hwR, rfl⟩)
    (hj ⟨w', hw'R, rfl⟩) (hi ⟨m, hmR, rfl⟩) hw3
    (not_mem_center_of_inverted (by decide) hw3 hw1 hm) hw'3
    (not_mem_center_of_inverted (by decide) hw'3 hw'1 hm') hm (hcomm w hwR w' hw'R)
    (hcomm m hmR w' hw'R)

theorem two_le_pRank_of_conj_nodes (hq : q.ker ≤ Subgroup.center ↥L)
    (hπ : π.ker ≤ Subgroup.center K) {Hs : Subgroup ↥L} {g : K}
    (hi : (rankOne D.rootGroup i).map π ≤ Hs.map q) (hg : π g ∈ Hs.map q)
    (hoi : OddNode (rankOne D.rootGroup i) 3)
    (hcomm : ∀ x ∈ rankOne D.rootGroup i, ∀ y ∈ rankOne D.rootGroup i,
      x * (g * y * g⁻¹) = (g * y * g⁻¹) * x) : 2 ≤ CFSG.Open.pRank 3 Hs := by
  obtain ⟨w, hwR, m, hmR, hw3, hw1, hm⟩ := hoi
  have hwc : w ∉ Subgroup.center K := not_mem_center_of_inverted (by decide) hw3 hw1 hm
  refine two_le_pRank_of_images hq hπ (a := w) (b := g * w * g⁻¹) (m := m) (hi ⟨w, hwR, rfl⟩)
    ?_ (hi ⟨m, hmR, rfl⟩) hw3 hwc ?_ ?_ hm (hcomm w hwR w hwR) (hcomm m hmR w hwR)
  · rw [map_mul, map_mul, map_inv]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg (hi ⟨w, hwR, rfl⟩)) (Subgroup.inv_mem _ hg)
  · rw [conj_pow, hw3]
    simp
  · intro hc
    apply hwc
    have h2 := Subgroup.Normal.conj_mem inferInstance _ hc g⁻¹
    have e : g⁻¹ * (g * w * g⁻¹) * g⁻¹⁻¹ = w := by group
    rwa [e] at h2


theorem two_le_pRank_of_images_q {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hπ : π.ker ≤ Subgroup.center K) {Hs : Subgroup ↥L} {a b m : K}
    (ha : π a ∈ Hs.map q) (hb : π b ∈ Hs.map q) (hm : π m ∈ Hs.map q) (har : a ^ r = 1)
    (ha1 : a ∉ Subgroup.center K) (hbr : b ^ r = 1) (hb1 : b ∉ Subgroup.center K)
    (hma : m * a * m⁻¹ = a⁻¹) (hab : a * b = b * a) (hmb : m * b = b * m) :
    2 ≤ CFSG.Open.pRank r Hs := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hx1 : π a ≠ 1 := fun h => ha1 (hπ (MonoidHom.mem_ker.2 h))
  have hy1 : π b ≠ 1 := fun h => hb1 (hπ (MonoidHom.mem_ker.2 h))
  have hxr : (π a) ^ r = 1 := by rw [← map_pow, har, map_one]
  have hyr : (π b) ^ r = 1 := by rw [← map_pow, hbr, map_one]
  have hxy : π a * π b = π b * π a := by rw [← map_mul, ← map_mul, hab]
  have hMx : π m * π a * (π m)⁻¹ = (π a)⁻¹ := by
    simpa [map_mul, map_inv] using congrArg π hma
  have hMy : π m * π b = π b * π m := by rw [← map_mul, ← map_mul, hmb]
  have hox : orderOf (π a) = r := orderOf_eq_prime hxr hx1
  have hoy : orderOf (π b) = r := orderOf_eq_prime hyr hy1
  refine KParU5Proof.two_le_pRank_of_lift hr hr2 q (𝒢 := Hs) (x := π a) (y := π b)
    ha hb hxr hyr hxy ?_
  intro i j hij
  have hxi : (π b) ^ j = ((π a) ^ i)⁻¹ := eq_inv_of_mul_eq_one_right hij
  have hMxi : π m * (π a) ^ i * (π m)⁻¹ = ((π a) ^ i)⁻¹ := by
    rw [← conj_pow, hMx, inv_pow]
  have hMyi : π m * (π b) ^ j * (π m)⁻¹ = (π b) ^ j := by
    rw [← conj_pow, hMy]
    group
  have h2 : ((π a) ^ i)⁻¹ * (π b) ^ j = 1 := by
    have hconj : π m * ((π a) ^ i * (π b) ^ j) * (π m)⁻¹ = 1 := by
      rw [hij]
      group
    have hconj' : (π m * (π a) ^ i * (π m)⁻¹) * (π m * (π b) ^ j * (π m)⁻¹) = 1 := by
      rw [← hconj]
      group
    rwa [hMxi, hMyi] at hconj'
  have h2x : ((π a) ^ i)⁻¹ * ((π a) ^ i)⁻¹ = 1 := by
    rw [hxi] at h2
    exact h2
  have hsq : ((π a) ^ i) ^ 2 = 1 := by
    have := congrArg (fun z => z⁻¹) h2x
    simpa [mul_inv_rev, inv_inv, pow_two] using this
  have hpow : (π a) ^ (2 * i) = 1 := by
    have := hsq
    rw [← pow_mul] at this
    simpa [mul_comm] using this
  have hdvd2 : r ∣ 2 * i := by
    rw [← hox]
    exact orderOf_dvd_iff_pow_eq_one.2 hpow
  have hri : r ∣ i := by
    rcases (hr.dvd_mul).1 hdvd2 with h | h
    · have hle : r ≤ 2 := Nat.le_of_dvd (by norm_num) h
      have := hr.two_le
      omega
    · exact h
  have hxi1 : (π a) ^ i = 1 := by
    refine orderOf_dvd_iff_pow_eq_one.1 ?_
    simpa [hox] using hri
  have hyj1 : (π b) ^ j = 1 := by
    have := hij
    rwa [hxi1, one_mul] at this
  have hdj : r ∣ j := by
    have := orderOf_dvd_iff_pow_eq_one.2 hyj1
    simpa [hoy] using this
  exact ⟨hri, hdj⟩

theorem two_le_pRank_of_orthogonal_nodes_q {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hπ : π.ker ≤ Subgroup.center K) {Hs : Subgroup ↥L}
    (hi : (rankOne D.rootGroup i).map π ≤ Hs.map q) (hj : (rankOne D.rootGroup j).map π ≤ Hs.map q)
    (hoi : OddNode (rankOne D.rootGroup i) r) (hoj : OddNode (rankOne D.rootGroup j) r)
    (hcomm : ∀ x ∈ rankOne D.rootGroup i, ∀ y ∈ rankOne D.rootGroup j, x * y = y * x) :
    2 ≤ CFSG.Open.pRank r Hs := by
  obtain ⟨w, hwR, m, hmR, hw3, hw1, hm⟩ := hoi
  obtain ⟨w', hw'R, m', hm'R, hw'3, hw'1, hm'⟩ := hoj
  refine two_le_pRank_of_images_q hr hr2 hπ (a := w) (b := w') (m := m) (hi ⟨w, hwR, rfl⟩)
    (hj ⟨w', hw'R, rfl⟩) (hi ⟨m, hmR, rfl⟩) hw3
    (not_mem_center_of_inverted (hr.odd_of_ne_two hr2) hw3 hw1 hm) hw'3
    (not_mem_center_of_inverted (hr.odd_of_ne_two hr2) hw'3 hw'1 hm') hm
    (hcomm w hwR w' hw'R) (hcomm m hmR w' hw'R)

theorem two_le_pRank_of_conj_nodes_q {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hπ : π.ker ≤ Subgroup.center K) {Hs : Subgroup ↥L} {g : K}
    (hi : (rankOne D.rootGroup i).map π ≤ Hs.map q) (hg : π g ∈ Hs.map q)
    (hoi : OddNode (rankOne D.rootGroup i) r)
    (hcomm : ∀ x ∈ rankOne D.rootGroup i, ∀ y ∈ rankOne D.rootGroup i,
      x * (g * y * g⁻¹) = (g * y * g⁻¹) * x) : 2 ≤ CFSG.Open.pRank r Hs := by
  obtain ⟨w, hwR, m, hmR, hw3, hw1, hm⟩ := hoi
  have hwc : w ∉ Subgroup.center K := not_mem_center_of_inverted (hr.odd_of_ne_two hr2) hw3 hw1 hm
  refine two_le_pRank_of_images_q hr hr2 hπ (a := w) (b := g * w * g⁻¹) (m := m)
    (hi ⟨w, hwR, rfl⟩) ?_ (hi ⟨m, hmR, rfl⟩) hw3 hwc ?_ ?_ hm (hcomm w hwR w hwR)
    (hcomm m hmR w hwR)
  · rw [map_mul, map_mul, map_inv]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg (hi ⟨w, hwR, rfl⟩)) (Subgroup.inv_mem _ hg)
  · rw [conj_pow, hw3]
    simp
  · intro hc
    apply hwc
    have h2 := Subgroup.Normal.conj_mem inferInstance _ hc g⁻¹
    have e : g⁻¹ * (g * w * g⁻¹) * g⁻¹⁻¹ = w := by group
    rwa [e] at h2

end E9

end CFSG.LocalAnalysis.RankThreeUC.S15.K517Six
