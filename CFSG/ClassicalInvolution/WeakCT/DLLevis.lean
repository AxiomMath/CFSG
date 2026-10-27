module

public import CFSG.ClassicalInvolution.WeakCT.SignedLevis
public import CFSG.ClassicalInvolution.WeakCT.SignedLevisDL
public import CFSG.ClassicalInvolution.WeakCT.SpModel

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Timmesfeld
  CFSG.Timmesfeld.LevisExtras
open CFSG.Assembly.LowTwoRank (StatedSp)
open scoped commutatorElement MatrixGroups

section Levis

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : Steinberg.CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}

theorem rootGroup_le_range (hE : Steinberg.ChevalleyExtras D F x C O) {γ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) {M : Type*} [Group M] {emb : M →* K} (h : ∀ c, x γ c ∈ emb.range) :
    D.rootGroup γ ≤ emb.range := by
  intro g hg
  obtain ⟨c, rfl⟩ := ((hE.param γ hγ).1 g).1 hg
  exact h c

theorem pairRoots_self_subset (hdiv : D.divisible = ∅) (k : Fin D.rank) :
    pairRoots D k k ⊆ {sroot k, -sroot k} := by
  refine (pairRoots_subset hdiv (S := {sroot k, -sroot k}) (Set.mem_insert _ _)
    (Set.mem_insert _ _) ?_ ?_).trans
    (by intro γ hγ; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hγ ⊢; tauto) <;>
  · intro γ hγ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hγ ⊢
    rcases hγ with rfl | rfl
    · right
      exact reflection_single_self (D.isFiniteType.apply_self k)
    · left
      rw [map_neg, reflection_single_self (D.isFiniteType.apply_self k), neg_neg]

theorem exists_sl2Levi (hE : Steinberg.ChevalleyExtras D F x C O) (hdiv : D.divisible = ∅)
    (k : Fin D.rank) :
    ∃ emb : SL(2, F) →* K, Function.Injective emb ∧
      (∀ γ ∈ pairRoots D k k, D.rootGroup γ ≤ emb.range) ∧
      ∀ c, emb (tv 0 1 c) = x (sroot k) c ∧ emb (tv 1 0 c) = x (-sroot k) c := by
  obtain ⟨φ, hφ, hup, hlow⟩ := hE.rankOne k
  have h1 : ∀ c, φ (tv 0 1 c) = x (sroot k) c := fun c => by rw [tv01_eq_sl2Upper, hup]
  have h2 : ∀ c, φ (tv 1 0 c) = x (-sroot k) c := fun c => by rw [tv10_eq_sl2Lower, hlow]
  refine ⟨φ, hφ, fun γ hγ => ?_, fun c => ⟨h1 c, h2 c⟩⟩
  have hγ' := pairRoots_self_subset hdiv k hγ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hγ'
  rcases hγ' with rfl | rfl
  · exact rootGroup_le_range hE hγ.1 fun c => ⟨tv 0 1 c, h1 c⟩
  · exact rootGroup_le_range hE hγ.1 fun c => ⟨tv 1 0 c, h2 c⟩

theorem exists_sl3Levi [Finite F] (hE : Steinberg.ChevalleyExtras D F x C O)
    (hdiv : D.divisible = ∅) {i j k : Fin D.rank} (hij : i ≠ j) (hcij : D.cartan i j = -1)
    (hcji : D.cartan j i = -1) (hk : ¬ (3 : ℤ) ∣ D.cartan i k + 2 * D.cartan j k) :
    ∃ emb : SL(3, F) →* K, Function.Injective emb ∧
      (∀ γ ∈ pairRoots D i j, D.rootGroup γ ≤ emb.range) ∧
      ∀ c, emb (tv 0 1 c) = x (sroot i) c ∧ emb (tv 1 0 c) = x (-sroot i) c ∧
        emb (tv 1 2 c) = x (sroot j) c ∧ emb (tv 2 1 c) = x (-sroot j) c := by
  obtain ⟨ρ, hρ⟩ := exists_sl3_signed' hE hdiv hij hcij hcji
  refine ⟨ρ, injective_of_sl3_torus hE (fun c => ⟨(hρ c).1, (hρ c).2.1⟩)
    (fun c => ⟨(hρ c).2.2.1, (hρ c).2.2.2.1⟩) hk, fun γ hγ => ?_,
    fun c => ⟨(hρ c).1, (hρ c).2.1, (hρ c).2.2.1, (hρ c).2.2.2.1⟩⟩
  have hεp : epsPos F C i j * epsPos F C i j = 1 := Nz_pos_sq hE hdiv hij hcij hcji
  have hεm : epsNeg F C i j * epsNeg F C i j = 1 := by
    have h := Nz_neg_sq hE hdiv hij hcij hcji
    unfold epsNeg
    rw [neg_mul_neg]
    exact h
  have hsub : pairRoots D i j ⊆ pair i j '' zEdge :=
    pairRoots_subset_pair hdiv (by decide) (by decide) (by rw [hcij]; decide)
      (by rw [hcji]; decide)
  obtain ⟨z, hz, rfl⟩ := hsub hγ
  have hzr : pair i j z ∈ D.roots := pair_mem_roots_zEdge hcij hcji z hz
  rw [Finset.mem_coe] at hz
  simp only [zEdge, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [pair_one_zero]
    exact rootGroup_le_range hE (pair_one_zero i j ▸ hzr) fun c => ⟨tv 0 1 c, (hρ c).1⟩
  · rw [pair_neg_one_zero]
    exact rootGroup_le_range hE (pair_neg_one_zero i j ▸ hzr) fun c => ⟨tv 1 0 c, (hρ c).2.1⟩
  · rw [pair_zero_one]
    exact rootGroup_le_range hE (pair_zero_one i j ▸ hzr) fun c => ⟨tv 1 2 c, (hρ c).2.2.1⟩
  · rw [pair_zero_neg_one]
    exact rootGroup_le_range hE (pair_zero_neg_one i j ▸ hzr) fun c =>
      ⟨tv 2 1 c, (hρ c).2.2.2.1⟩
  · rw [pair_one_one]
    refine rootGroup_le_range hE (pair_one_one i j ▸ hzr) fun c => ⟨tv 0 2 (epsPos F C i j * c), ?_⟩
    rw [(hρ _).2.2.2.2.1]
    congr 1
    linear_combination c * hεp
  · rw [pair_neg_one_neg_one]
    refine rootGroup_le_range hE (pair_neg_one_neg_one i j ▸ hzr) fun c =>
      ⟨tv 2 0 (epsNeg F C i j * c), ?_⟩
    rw [(hρ _).2.2.2.2.2]
    congr 1
    linear_combination c * hεm

theorem exists_sl2sl2Levi (hE : Steinberg.ChevalleyExtras D F x C O) (hdiv : D.divisible = ∅)
    {i j : Fin D.rank} (hij : i ≠ j) (hcij : D.cartan i j = 0) (hcji : D.cartan j i = 0)
    {H : Fin D.rank → Subgroup K} (hind : iSupIndep H)
    (hsq : ∀ k, Steinberg.weylElement x k 1 ^ 2 ∈ H k) :
    ∃ l : SL(2, F) × SL(2, F) →* K, Function.Injective l ∧
      (∀ γ ∈ pairRoots D i j, D.rootGroup γ ≤ l.range) ∧
      ∀ c, l (tv 0 1 c, 1) = x (sroot i) c ∧ l (tv 1 0 c, 1) = x (-sroot i) c ∧
        l (1, tv 0 1 c) = x (sroot j) c ∧ l (1, tv 1 0 c) = x (-sroot j) c := by
  obtain ⟨l, hl, hl'⟩ := exists_sl2sl2 hE hdiv hij hcij hcji hind hsq
  refine ⟨l, hl, fun γ hγ => ?_, hl'⟩
  have hsub : pairRoots D i j ⊆ pair i j '' zNon :=
    pairRoots_subset_pair hdiv (by decide) (by decide) (by rw [hcij]; decide)
      (by rw [hcji]; decide)
  obtain ⟨z, hz, rfl⟩ := hsub hγ
  have hzr : pair i j z ∈ D.roots := pair_mem_roots_zNon z hz
  rw [Finset.mem_coe] at hz
  simp only [zNon, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · rw [pair_one_zero]
    exact rootGroup_le_range hE (pair_one_zero i j ▸ hzr) fun c => ⟨(tv 0 1 c, 1), (hl' c).1⟩
  · rw [pair_neg_one_zero]
    exact rootGroup_le_range hE (pair_neg_one_zero i j ▸ hzr) fun c =>
      ⟨(tv 1 0 c, 1), (hl' c).2.1⟩
  · rw [pair_zero_one]
    exact rootGroup_le_range hE (pair_zero_one i j ▸ hzr) fun c => ⟨(1, tv 0 1 c), (hl' c).2.2.1⟩
  · rw [pair_zero_neg_one]
    exact rootGroup_le_range hE (pair_zero_neg_one i j ▸ hzr) fun c =>
      ⟨(1, tv 1 0 c), (hl' c).2.2.2⟩

theorem exists_sp4Levi [Finite F] (hF : 4 ≤ Nat.card F) (h2 : (2 : F) ≠ 0)
    (hE : Steinberg.ChevalleyExtras D F x C O) (hdiv : D.divisible = ∅) {i j : Fin D.rank}
    (hcij : D.cartan i j = -2) (hcji : D.cartan j i = -1) :
    ∃ φ : StatedSp 2 F →* K, Function.Injective φ ∧
      (∀ γ ∈ pairRoots D i j, D.rootGroup γ ≤ φ.range) ∧
      ∀ c, φ (spBlock F 0 (tv 0 1 c)) = x (sroot i) c ∧
        φ (spBlock F 0 (tv 1 0 c)) = x (-sroot i) c ∧
        φ (spBlock F 1 (tv 0 1 c)) = x (sroot j) c ∧
        φ (spBlock F 1 (tv 1 0 c)) = x (-sroot j) c := by
  obtain ⟨φ, hφ, hle, hv⟩ := exists_b2Levi hF h2 hE hdiv hcij hcji
  exact ⟨φ, hφ, fun γ hγ g hg => hle γ hγ g hg, hv⟩

end Levis

end CFSG.ClassicalInvolution.WeakCT
