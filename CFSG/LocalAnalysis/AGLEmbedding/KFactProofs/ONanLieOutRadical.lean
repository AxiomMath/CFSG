module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabHub
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeCore

public section

namespace CFSG.AGLEmbedding.LieOut

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
open scoped commutatorElement

section Radical

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

@[expose] def coordHom (D : UniversalRootDatum K) (j : Fin D.rank) : (Fin D.rank → ℤ) →+ ℤ :=
  Pi.evalAddMonoidHom (fun _ => ℤ) j

@[simp] theorem coordHom_apply (j : Fin D.rank) (γ : Fin D.rank → ℤ) : coordHom D j γ = γ j :=
  rfl

@[expose] def radical (D : UniversalRootDatum K) (j : Fin D.rank) : Subgroup K :=
  ⨆ γ ∈ posSet D.roots (coordHom D j), D.rootGroup γ

theorem rootGroup_le_radical {j : Fin D.rank} {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots)
    (h : 0 < γ j) : D.rootGroup γ ≤ radical D j :=
  le_iSup₂_of_le (f := fun γ (_ : γ ∈ posSet D.roots (coordHom D j)) => D.rootGroup γ) γ
    ⟨hγ, by simpa using h⟩ le_rfl

theorem ht_pos_of_coord {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) {j : Fin D.rank}
    (hj : 0 < γ j) : 0 < ht γ := by
  rcases (RootSystem.ofCartan D.isFiniteType D.divisible).sign γ hγ with h | h
  · calc (0 : ℤ) < γ j := by omega
      _ ≤ ht γ := Finset.single_le_sum (f := γ) (fun i _ => h i) (Finset.mem_univ j)
  · have := h j
    omega

theorem coord_nonneg_of_ht_pos {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) (hpos : 0 < ht γ)
    (j : Fin D.rank) : 0 ≤ γ j := by
  rcases (RootSystem.ofCartan D.isFiniteType D.divisible).sign γ hγ with h | h
  · exact h j
  · have : ht γ ≤ 0 := Finset.sum_nonpos (fun i _ => h i)
    omega

theorem radical_le_posUnipotent (j : Fin D.rank) : radical D j ≤ posUnipotent D :=
  iSup₂_le fun _ hγ => rootGroup_le_posUnipotent hγ.1 (ht_pos_of_coord hγ.1 (by simpa using hγ.2))

theorem linIndepPair_of_coord {δ γ : Fin D.rank → ℤ} (hδ : δ ∈ D.roots) {j : Fin D.rank}
    (hδj : δ j = 0) (hγj : 0 < γ j) : LinIndepPair δ γ := by
  intro a b hab
  have h1 := congrFun hab j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hδj, mul_zero, zero_add,
    Pi.zero_apply] at h1
  have hb : b = 0 := by
    rcases mul_eq_zero.1 h1 with h | h
    · exact h
    · omega
  subst hb
  have hne : δ ≠ 0 := fun h =>
    (RootSystem.ofCartan D.isFiniteType D.divisible).zero_notMem (h ▸ hδ)
  obtain ⟨i, hi⟩ : ∃ i, δ i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne (funext hcon)
  have h2 := congrFun hab i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_smul, add_zero, Pi.zero_apply] at h2
  rcases mul_eq_zero.1 h2 with h | h
  · exact ⟨h, rfl⟩
  · exact absurd h hi

theorem rootGroup_conj_mem_radical (hext : SteinbergExtras D n H) {j : Fin D.rank}
    {δ γ : Fin D.rank → ℤ} (hδ : δ ∈ D.roots) (hδj : δ j = 0) (hγ : γ ∈ D.roots)
    (hγj : 0 < γ j) {x y : K} (hx : x ∈ D.rootGroup δ) (hy : y ∈ D.rootGroup γ) :
    x * y * x⁻¹ ∈ radical D j := by
  have hc := hext.commutator_mem δ hδ γ hγ (linIndepPair_of_coord hδ hδj hγj) x hx y hy
  have hle : (⨆ ε ∈ openCone D.roots δ γ, D.rootGroup ε) ≤ radical D j := by
    refine iSup₂_le fun ε hε => ?_
    obtain ⟨hεr, a, b, ha, hb, rfl⟩ := hε
    refine rootGroup_le_radical hεr ?_
    have hj : (a • δ + b • γ) j = (a : ℤ) * δ j + (b : ℤ) * γ j := by
      rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, nsmul_eq_mul, nsmul_eq_mul]
    rw [hj, hδj, mul_zero, zero_add]
    have : (0 : ℤ) < b := by exact_mod_cast hb
    positivity
  have e : x * y * x⁻¹ = ⁅x, y⁆ * y := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact mul_mem (hle hc) (rootGroup_le_radical hγ hγj hy)

theorem conj_mem_radical_of_forall {j : Fin D.rank} (g : K)
    (h : ∀ γ ∈ posSet D.roots (coordHom D j), ∀ y ∈ D.rootGroup γ, g * y * g⁻¹ ∈ radical D j)
    {r : K} (hr : r ∈ radical D j) : g * r * g⁻¹ ∈ radical D j := by
  refine Subgroup.iSup_induction
    (fun γ => ⨆ (_ : γ ∈ posSet D.roots (coordHom D j)), D.rootGroup γ)
    (C := fun r => g * r * g⁻¹ ∈ radical D j) hr (fun γ r hr => ?_) (by simp)
    (fun a b ha hb => ?_)
  · by_cases hγ : γ ∈ posSet D.roots (coordHom D j)
    · rw [iSup_pos hγ] at hr
      exact h γ hγ r hr
    · rw [iSup_neg hγ] at hr
      have : r = 1 := by simpa using hr
      subst this
      simp
  · rw [show g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) by group]
    exact mul_mem ha hb

theorem le_normalizer_of_conj_mem {G : Type*} [Group G] (C R : Subgroup G)
    (h : ∀ g ∈ C, ∀ r ∈ R, g * r * g⁻¹ ∈ R) : C ≤ Subgroup.normalizer (R : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h g hg y hy, fun hy => ?_⟩
  have := h g⁻¹ (C.inv_mem hg) _ hy
  simpa [mul_assoc] using this

theorem rootGroup_le_normalizer_radical (hext : SteinbergExtras D n H) {j : Fin D.rank}
    {δ : Fin D.rank → ℤ} (hδ : δ ∈ D.roots) (hδj : 0 ≤ δ j) :
    D.rootGroup δ ≤ Subgroup.normalizer (radical D j : Set K) := by
  refine le_normalizer_of_conj_mem _ _ fun x hx r hr => ?_
  by_cases h0 : δ j = 0
  · exact conj_mem_radical_of_forall x (fun γ hγ y hy =>
      rootGroup_conj_mem_radical hext hδ h0 hγ.1 (by simpa using hγ.2) hx hy) hr
  · have h1 : 0 < δ j := by omega
    have hxR : x ∈ radical D j := rootGroup_le_radical hδ h1 hx
    exact mul_mem (mul_mem hxR hr) (inv_mem hxR)

theorem borel_le_normalizer_radical
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (j : Fin D.rank) :
    borel D H ≤ Subgroup.normalizer (radical D j : Set K) := by
  refine sup_le (iSup_le fun k => ?_) (iSup₂_le fun δ hδ => ?_)
  · refine le_normalizer_of_conj_mem _ _ fun h hh r hr => ?_
    exact conj_mem_radical_of_forall h (fun γ hγ y hy =>
      rootGroup_le_radical hγ.1 (by simpa using hγ.2) (hct.H_conj_mem k γ hγ.1 h hh y hy)) hr
  · exact rootGroup_le_normalizer_radical hext hδ.1 (coord_nonneg_of_ht_pos hδ.1 hδ.2 j)

theorem rankOne_le_normalizer_radical (hext : SteinbergExtras D n H) {i j : Fin D.rank}
    (hij : i ≠ j) :
    rankOne D.rootGroup i ≤ Subgroup.normalizer (radical D j : Set K) := by
  have hα : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  have hα' : (-Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ hα
  refine sup_le (rootGroup_le_normalizer_radical hext hα ?_)
    (rootGroup_le_normalizer_radical hext hα' ?_)
  · simp [hij.symm]
  · simp [hij.symm]

end Radical

section Main

variable {K Y : Type*} [Group K] [Group Y] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

theorem exists_node_not_mem_negIndices (h : BorelQuotient D n H π M) {J : Subgroup Y}
    (hBJ : (borel D H).map π ≤ J) (hJ : J ≠ ⊤) : ∃ j, j ∉ negIndices D (J.comap π) := by
  by_contra hcon
  push Not at hcon
  apply hJ
  have hBA : borel D H ≤ J.comap π := fun b hb => hBJ ⟨b, hb, rfl⟩
  have htop := eq_borel_sup_rankOne h.ct h.extras (A := ⊤) le_top
  have hcomap : J.comap π = ⊤ := by
    refine eq_top_iff.2 ?_
    rw [htop]
    exact sup_le hBA (iSup₂_le fun i _ => rankOne_le_of_mem_negIndices hBA (hcon i))
  rw [← Subgroup.map_comap_eq_self_of_surjective h.surj J, hcomap, ← MonoidHom.range_eq_map]
  exact MonoidHom.range_eq_top.2 h.surj

theorem map_radical_ne_bot (h : BorelQuotient D n H π M) (j : Fin D.rank) :
    (radical D j).map π ≠ ⊥ := by
  intro hbot
  have hα : (Pi.single j 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem j
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 (h.extras.ne_bot _ hα)
  have haR : (a : K) ∈ radical D j := rootGroup_le_radical hα (by simp) a.2
  have hπ : π a = 1 := by
    have : π a ∈ (radical D j).map π := Subgroup.mem_map_of_mem π haR
    rw [hbot] at this
    exact Subgroup.mem_bot.1 this
  have hker : (a : K) ∈ π.ker := hπ
  obtain ⟨k, hk⟩ := h.pGroup _ hα a
  have hk' : (a : K) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hM := h.ker_pow _ hker
  have hcop : Nat.Coprime (2 ^ k) M := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 h.odd)
  have h1 : orderOf (a : K) = 1 := Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one hM)
  exact ha (Subtype.ext (orderOf_eq_one_iff.1 h1))

theorem exists_normal_twoGroup_of_borel_le (h : BorelQuotient D n H π M) {J : Subgroup Y}
    (hBJ : (borel D H).map π ≤ J) (hJ : J ≠ ⊤) :
    ∃ R : Subgroup Y, R ≠ ⊥ ∧ IsPGroup 2 R ∧ J ≤ Subgroup.normalizer (R : Set Y) := by
  obtain ⟨j, hj⟩ := exists_node_not_mem_negIndices h hBJ hJ
  refine ⟨(radical D j).map π, map_radical_ne_bot h j,
    (isPGroup_iSup_posSet h.extras h.pGroup (coordHom D j) : IsPGroup 2 (radical D j)).map π, ?_⟩
  calc J = (borel D H).map π ⊔ ⨆ i ∈ negIndices D (J.comap π), (rankOne D.rootGroup i).map π :=
        eq_map_borel_sup_of_le h.ct h.extras h.surj hBJ
    _ ≤ _ := by
        refine sup_le ?_ (iSup₂_le fun i hi => ?_)
        · exact (Subgroup.map_mono (borel_le_normalizer_radical h.ct h.extras j)).trans
            (Subgroup.le_normalizer_map π)
        · have hij : i ≠ j := fun e => hj (e ▸ hi)
          exact (Subgroup.map_mono (rankOne_le_normalizer_radical h.extras hij)).trans
            (Subgroup.le_normalizer_map π)

end Main

end CFSG.AGLEmbedding.LieOut
