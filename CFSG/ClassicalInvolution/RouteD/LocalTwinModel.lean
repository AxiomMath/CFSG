module

public import CFSG.ClassicalInvolution.RouteD.LocalTwin

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg CFSG.ClassicalInvolution.ModelFacts
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups
open CFSG.ClassicalInvolution.Generic (Commutes conjSub Commutes.symm)

section Commutes

variable {X : Type} [Group X]

theorem commutes_sup_left {A B C : Subgroup X} : Commutes (A ⊔ B) C ↔ Commutes A C ∧ Commutes B C := by
  constructor
  · intro h
    exact ⟨fun x hx y hy => h x (Subgroup.mem_sup_left hx) y hy,
      fun x hx y hy => h x (Subgroup.mem_sup_right hx) y hy⟩
  · rintro ⟨hA, hB⟩
    have key : ∀ y ∈ C, A ⊔ B ≤ Subgroup.centralizer ({y} : Set X) := by
      intro y hy
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hA x hx y hy)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hB x hx y hy)
    intro x hx y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (key y hy hx)

theorem commutes_sup_right {A B C : Subgroup X} : Commutes C (A ⊔ B) ↔ Commutes C A ∧ Commutes C B := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := commutes_sup_left.mp h.symm
    exact ⟨h1.symm, h2.symm⟩
  · rintro ⟨h1, h2⟩
    exact (commutes_sup_left.mpr ⟨h1.symm, h2.symm⟩).symm

theorem commutes_iSup_left {ι : Type*} {A : ι → Subgroup X} {C : Subgroup X} :
    Commutes (⨆ i, A i) C ↔ ∀ i, Commutes (A i) C := by
  constructor
  · intro h i x hx y hy
    exact h x (Subgroup.mem_iSup_of_mem i hx) y hy
  · intro h
    have key : ∀ y ∈ C, ⨆ i, A i ≤ Subgroup.centralizer ({y} : Set X) := by
      intro y hy
      refine iSup_le fun i x hx => ?_
      exact Subgroup.mem_centralizer_singleton_iff.mpr (h i x hx y hy)
    intro x hx y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (key y hy hx)

end Commutes

section Orth

variable {K : Type} [Group K] (D : UniversalRootDatum K)

theorem lenSq_add_nsmul {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I ℤ}
    (hA : TauCeti.IsFiniteType A) {γ δ : I → ℤ} (horth : form hA (toRat γ) (toRat δ) = 0)
    (a b : ℕ) :
    lenSq hA (a • γ + b • δ) = (a : ℚ) ^ 2 * lenSq hA γ + (b : ℚ) ^ 2 * lenSq hA δ := by
  have h' : form hA (toRat δ) (toRat γ) = 0 := by rw [form_comm]; exact horth
  have e : toRat (a • γ + b • δ) = a • toRat γ + b • toRat δ := by
    rw [map_add, map_nsmul, map_nsmul]
  rw [lenSq, e]
  simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply]
  simp only [nsmul_eq_mul, horth, h', mul_zero, add_zero, zero_add]
  rw [lenSq, lenSq]
  ring

theorem commute_rootGroup_of_orthogonal {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hext : SteinbergExtras D n H) {ℓ : ℚ}
    (hℓ : ∀ γ ∈ D.roots, lenSq D.isFiniteType γ = ℓ) {γ δ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) (hδ : δ ∈ D.roots)
    (horth : form D.isFiniteType (toRat γ) (toRat δ) = 0) :
    ∀ x ∈ D.rootGroup γ, ∀ y ∈ D.rootGroup δ, x * y = y * x := by
  have hℓpos : 0 < ℓ := by
    rw [← hℓ γ hγ]
    exact lenSq_pos D.isFiniteType (ne_zero_of_mem_roots D.isFiniteType D.divisible hγ)
  have horth' : form D.isFiniteType (toRat δ) (toRat γ) = 0 := by rw [form_comm]; exact horth
  have hind : LinIndepPair γ δ := by
    intro a b hab
    have h1 := congrArg (fun v => form D.isFiniteType (toRat γ) (toRat v)) hab
    have h2 := congrArg (fun v => form D.isFiniteType (toRat δ) (toRat v)) hab
    simp only [map_add, map_zsmul, map_zero] at h1 h2
    simp only [zsmul_eq_mul, horth, horth', mul_zero, add_zero, zero_add] at h1 h2
    have e1 : form D.isFiniteType (toRat γ) (toRat γ) = ℓ := hℓ γ hγ
    have e2 : form D.isFiniteType (toRat δ) (toRat δ) = ℓ := hℓ δ hδ
    rw [e1] at h1
    rw [e2] at h2
    exact ⟨by exact_mod_cast (mul_eq_zero.mp h1).resolve_right hℓpos.ne',
      by exact_mod_cast (mul_eq_zero.mp h2).resolve_right hℓpos.ne'⟩
  have hempty : openCone D.roots γ δ = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun ε hε => ?_
    obtain ⟨hεr, a, b, ha, hb, rfl⟩ := hε
    have h1 := hℓ _ hεr
    have h2 := lenSq_add_nsmul D.isFiniteType horth a b
    rw [hℓ γ hγ, hℓ δ hδ] at h2
    rw [h2] at h1
    have ha' : (1 : ℚ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℚ) ≤ b := by exact_mod_cast hb
    have ha2 : (1 : ℚ) ≤ (a : ℚ) ^ 2 := by nlinarith
    have hb2 : (1 : ℚ) ≤ (b : ℚ) ^ 2 := by nlinarith
    have hpos : 0 < ℓ * ((a : ℚ) ^ 2 + (b : ℚ) ^ 2 - 1) := mul_pos hℓpos (by linarith)
    nlinarith
  intro x hx y hy
  have := hext.commutator_mem γ hγ δ hδ hind x hx y hy
  rw [hempty] at this
  simp only [Set.mem_empty_iff_false, iSup_false, iSup_bot, Subgroup.mem_bot] at this
  exact commutatorElement_eq_one_iff_mul_comm.mp this

end Orth

section Rank

variable {K : Type} [Group K] (D : UniversalRootDatum K)

theorem lenSq_eq_of_simplyLaced (hdiv : D.divisible = ∅)
    (hl : ∀ i, IsLongestRoot D (Pi.single i 1)) (i₀ : Fin D.rank) :
    ∀ γ ∈ D.roots, lenSq D.isFiniteType γ = lenSq D.isFiniteType (Pi.single i₀ 1) := by
  intro γ hγ
  have hγ' : γ ∈ roots D.isFiniteType ∅ := by
    have : γ ∈ roots D.isFiniteType D.divisible := hγ
    rwa [hdiv] at this
  rcases lenSq_of_mem_roots D.isFiniteType hγ' with ⟨j, hj⟩ | ⟨j, hj, -⟩
  · rw [hj, ← lenSq_single]
    exact (hl j).lenSq_eq (hl i₀) |>.trans rfl
  · exact absurd hj (Set.notMem_empty j)

theorem commutes_fund_of_orthogonal {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hext : SteinbergExtras D n H) {ℓ : ℚ}
    (hℓ : ∀ γ ∈ D.roots, lenSq D.isFiniteType γ = ℓ) {γ δ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) (hδ : δ ∈ D.roots)
    (horth : form D.isFiniteType (toRat γ) (toRat δ) = 0) :
    Commutes (D.rootGroup γ ⊔ D.rootGroup (-γ)) (D.rootGroup δ ⊔ D.rootGroup (-δ)) := by
  have hγ' : -γ ∈ D.roots := OfCartan.neg_mem_roots D.isFiniteType hγ
  have hδ' : -δ ∈ D.roots := OfCartan.neg_mem_roots D.isFiniteType hδ
  have o1 : form D.isFiniteType (toRat (-γ)) (toRat δ) = 0 := by simp [horth]
  have o2 : form D.isFiniteType (toRat γ) (toRat (-δ)) = 0 := by simp [horth]
  have o3 : form D.isFiniteType (toRat (-γ)) (toRat (-δ)) = 0 := by simp [horth]
  have c : ∀ {a b : Fin D.rank → ℤ}, a ∈ D.roots → b ∈ D.roots →
      form D.isFiniteType (toRat a) (toRat b) = 0 → Commutes (D.rootGroup a) (D.rootGroup b) :=
    fun ha hb ho x hx y hy => commute_rootGroup_of_orthogonal D hext hℓ ha hb ho x hx y hy
  rw [commutes_sup_left, commutes_sup_right, commutes_sup_right]
  exact ⟨⟨c hγ hδ horth, c hγ hδ' o2⟩, ⟨c hγ' hδ o1, c hγ' hδ' o3⟩⟩

theorem single_mem_roots (k : Fin D.rank) : (Pi.single k 1 : Fin D.rank → ℤ) ∈ D.roots :=
  Or.inl ⟨1, k, by simp⟩

theorem form_toRat_single_eq_zero (k : Fin D.rank) (θ : Fin D.rank → ℤ)
    (h : coroot D.cartan k θ = 0) :
    form D.isFiniteType (toRat θ) (toRat (Pi.single k 1)) = 0 := by
  rw [form_comm, toRat_single, form_single_left]
  have h2 : ∑ l, ((D.cartan k l : ℤ) : ℚ) * ((θ l : ℤ) : ℚ) = 0 := by
    have := h
    simp only [coroot_apply] at this
    exact_mod_cast this
  simp only [toRat_apply]
  rw [h2, mul_zero]

theorem commutes_rankOne_of_cartan_eq_zero {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hext : SteinbergExtras D n H) {ℓ : ℚ}
    (hℓ : ∀ γ ∈ D.roots, lenSq D.isFiniteType γ = ℓ) {i j : Fin D.rank}
    (hij : D.cartan i j = 0) :
    Commutes (rankOne D.rootGroup i) (rankOne D.rootGroup j) := by
  refine commutes_fund_of_orthogonal D hext hℓ (single_mem_roots D i) (single_mem_roots D j) ?_
  rw [toRat_single, toRat_single, form_single_left]
  simp [Pi.single_apply, hij]

end Rank

section LenSq

variable {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A)

theorem lenSq_eq_of_coroot (θ : I → ℤ) (k : I) (h1 : coroot A k θ = 1)
    (h0 : ∀ l, l ≠ k → coroot A l θ = 0) :
    lenSq hA θ = (θ k : ℚ) * symmetrizer hA k := by
  have key : ∀ l : I, form hA (toRat θ) (Pi.single l 1) =
      symmetrizer hA l * (coroot A l θ : ℚ) := by
    intro l
    rw [form_single_right]
    congr 1
    have := coroot_apply A l θ
    simp only [toRat_apply]
    exact_mod_cast this.symm
  rw [lenSq, form_eq_sum, Finset.sum_eq_single k]
  · rw [key, h1]
    simp [toRat_apply]
  · intro l _ hl
    rw [key, h0 l hl]
    simp
  · intro h
    exact absurd (Finset.mem_univ _) h

end LenSq

section LenSqDatum

variable {K : Type} [Group K] (D : UniversalRootDatum K)

theorem lenSq_eq_lenSq_single_of_coroot (θ : Fin D.rank → ℤ) (k : Fin D.rank) (hθk : θ k = 2)
    (h1 : coroot D.cartan k θ = 1) (h0 : ∀ l, l ≠ k → coroot D.cartan l θ = 0) :
    lenSq D.isFiniteType θ = lenSq D.isFiniteType (Pi.single k 1) := by
  rw [lenSq_eq_of_coroot D.isFiniteType θ k h1 h0, lenSq_single, hθk]
  norm_num

end LenSqDatum

section OrthLongest

variable {K : Type} [Group K] (D : UniversalRootDatum K)

theorem commute_rootGroup_of_orthogonal_of_longest {n : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K} (hext : SteinbergExtras D n H) {γ δ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) (hδ : δ ∈ D.roots)
    (hmax : ∀ ε ∈ D.roots, lenSq D.isFiniteType ε ≤ lenSq D.isFiniteType γ)
    (horth : form D.isFiniteType (toRat γ) (toRat δ) = 0) :
    ∀ x ∈ D.rootGroup γ, ∀ y ∈ D.rootGroup δ, x * y = y * x := by
  have hγpos : 0 < lenSq D.isFiniteType γ :=
    lenSq_pos D.isFiniteType (ne_zero_of_mem_roots D.isFiniteType D.divisible hγ)
  have hδpos : 0 < lenSq D.isFiniteType δ :=
    lenSq_pos D.isFiniteType (ne_zero_of_mem_roots D.isFiniteType D.divisible hδ)
  have horth' : form D.isFiniteType (toRat δ) (toRat γ) = 0 := by rw [form_comm]; exact horth
  have hind : LinIndepPair γ δ := by
    intro a b hab
    have h1 := congrArg (fun v => form D.isFiniteType (toRat γ) (toRat v)) hab
    have h2 := congrArg (fun v => form D.isFiniteType (toRat δ) (toRat v)) hab
    simp only [map_add, map_zsmul, map_zero] at h1 h2
    simp only [zsmul_eq_mul, horth, horth', mul_zero, add_zero, zero_add] at h1 h2
    have e1 : form D.isFiniteType (toRat γ) (toRat γ) = lenSq D.isFiniteType γ := rfl
    have e2 : form D.isFiniteType (toRat δ) (toRat δ) = lenSq D.isFiniteType δ := rfl
    rw [e1] at h1
    rw [e2] at h2
    exact ⟨by exact_mod_cast (mul_eq_zero.mp h1).resolve_right hγpos.ne',
      by exact_mod_cast (mul_eq_zero.mp h2).resolve_right hδpos.ne'⟩
  have hempty : openCone D.roots γ δ = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun ε hε => ?_
    obtain ⟨hεr, a, b, ha, hb, rfl⟩ := hε
    have h1 := hmax _ hεr
    have h2 := lenSq_add_nsmul D.isFiniteType horth a b
    rw [h2] at h1
    have ha' : (1 : ℚ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℚ) ≤ b := by exact_mod_cast hb
    have ha2 : (1 : ℚ) ≤ (a : ℚ) ^ 2 := by nlinarith
    have hb2 : (1 : ℚ) ≤ (b : ℚ) ^ 2 := by nlinarith
    nlinarith
  intro x hx y hy
  have := hext.commutator_mem γ hγ δ hδ hind x hx y hy
  rw [hempty] at this
  simp only [Set.mem_empty_iff_false, iSup_false, iSup_bot, Subgroup.mem_bot] at this
  exact commutatorElement_eq_one_iff_mul_comm.mp this

theorem commutes_fund_of_orthogonal_of_longest {n : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K} (hext : SteinbergExtras D n H) {γ δ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) (hδ : δ ∈ D.roots)
    (hmax : ∀ ε ∈ D.roots, lenSq D.isFiniteType ε ≤ lenSq D.isFiniteType γ)
    (horth : form D.isFiniteType (toRat γ) (toRat δ) = 0) :
    Commutes (D.rootGroup γ ⊔ D.rootGroup (-γ)) (D.rootGroup δ ⊔ D.rootGroup (-δ)) := by
  have hγ' : -γ ∈ D.roots := OfCartan.neg_mem_roots D.isFiniteType hγ
  have hδ' : -δ ∈ D.roots := OfCartan.neg_mem_roots D.isFiniteType hδ
  have hmax' : ∀ ε ∈ D.roots, lenSq D.isFiniteType ε ≤ lenSq D.isFiniteType (-γ) := by
    intro ε hε
    rw [lenSq_neg]
    exact hmax ε hε
  have o1 : form D.isFiniteType (toRat (-γ)) (toRat δ) = 0 := by simp [horth]
  have o2 : form D.isFiniteType (toRat γ) (toRat (-δ)) = 0 := by simp [horth]
  have o3 : form D.isFiniteType (toRat (-γ)) (toRat (-δ)) = 0 := by simp [horth]
  rw [commutes_sup_left, commutes_sup_right, commutes_sup_right]
  exact ⟨⟨fun x hx y hy => commute_rootGroup_of_orthogonal_of_longest D hext hγ hδ hmax horth x hx y hy,
      fun x hx y hy => commute_rootGroup_of_orthogonal_of_longest D hext hγ hδ' hmax o2 x hx y hy⟩,
    ⟨fun x hx y hy => commute_rootGroup_of_orthogonal_of_longest D hext hγ' hδ hmax' o1 x hx y hy,
      fun x hx y hy => commute_rootGroup_of_orthogonal_of_longest D hext hγ' hδ' hmax' o3 x hx y hy⟩⟩

theorem commutes_rankOne_of_cartan_eq_zero_of_longest {n : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K} (hext : SteinbergExtras D n H) {i j : Fin D.rank}
    (hmax : ∀ ε ∈ D.roots, lenSq D.isFiniteType ε ≤ lenSq D.isFiniteType (Pi.single i 1))
    (hij : D.cartan i j = 0) :
    Commutes (rankOne D.rootGroup i) (rankOne D.rootGroup j) := by
  refine commutes_fund_of_orthogonal_of_longest D hext (single_mem_roots D i)
    (single_mem_roots D j) hmax ?_
  rw [toRat_single, toRat_single, form_single_left]
  simp [Pi.single_apply, hij]

end OrthLongest

section Perfect

theorem range_le_commutator {A X : Type} [Group A] [Group X] (hA : Group.IsPerfect A)
    (f : A →* X) : f.range ≤ ⁅f.range, f.range⁆ := by
  have h : ⁅(⊤ : Subgroup A), ⊤⁆ = ⊤ := hA.commutator_eq_top
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, h]

theorem linearBlockStandardPair_perfect {F : Type} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F)
    {X : Type} [Group X] {W U V : Subgroup X} (h : LinearBlockStandardPair F W U V) :
    U ≤ ⁅U, U⁆ ∧ V ≤ ⁅V, V⁆ := by
  have hSL : Group.IsPerfect SL(2, F) := CFSG.ClassicalInvolution.sl2_isPerfect h4
  obtain ⟨θ, c, -, -, hUV⟩ := h
  have key : ∀ (i : ℕ) (hi : i + 2 ≤ 3),
      ((CFSG.ClassicalInvolution.WeakCT.blockSL F 3 2 i hi).range.map
          (MulAut.conj c⁻¹).toMonoidHom).map θ ≤
        ⁅((CFSG.ClassicalInvolution.WeakCT.blockSL F 3 2 i hi).range.map
          (MulAut.conj c⁻¹).toMonoidHom).map θ,
          ((CFSG.ClassicalInvolution.WeakCT.blockSL F 3 2 i hi).range.map
          (MulAut.conj c⁻¹).toMonoidHom).map θ⁆ := by
    intro i hi
    rw [Subgroup.map_map, ← MonoidHom.range_comp]
    exact range_le_commutator hSL _
  have h12 := key 0 (by omega)
  have h23 := key 1 (by omega)
  rcases hUV with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1 ▸ h12, h2 ▸ h23⟩
  · exact ⟨h2 ▸ h23, h1 ▸ h12⟩

end Perfect

section FundPerfect

variable {K : Type} [Group K]

theorem perfect_of_mem_fundamental {t : CFSG.Assembly.LowTwoRank.StatedLieTag}
    {D : UniversalRootDatum K} (hsc : CFSG.ClassicalInvolution.Generic.FundamentalSingleClass t D)
    {R₀ : Subgroup K} (hR₀ : R₀ ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups t D)
    (h₀ : R₀ ≤ ⁅R₀, R₀⁆) :
    ∀ R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups t D, R ≤ ⁅R, R⁆ := by
  intro R hR
  obtain ⟨g, rfl⟩ := hsc R₀ hR₀ R hR
  exact map_perfect (MulAut.conj g).toMonoidHom h₀

end FundPerfect

end CFSG.ClassicalInvolution.RouteD
