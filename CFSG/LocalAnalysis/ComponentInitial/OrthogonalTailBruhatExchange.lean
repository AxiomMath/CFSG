module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailParameterKernels
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailShortRootExchange
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryBruhat

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin Module Submodule
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped Pointwise

variable {K : Type*} [Field K] {A : Type*} [AddCommGroup A] [Module K A] {r : ℕ}
  {qA : QuadraticForm K A}

section Borel

theorem mem_tailBorel_of_diag {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)}
    (hgE : g ∈ orthElementaryGroup (quadTail r qA))
    (hg : ∀ j : Fin r, ∃ c : K, c ≠ 0 ∧ g (hypVec K A (.inl j)) = c • hypVec K A (.inl j)) :
    g ∈ tailBorel r qA := by
  refine mem_tailBorel.2 ⟨hgE, fun k _ _ => le_antisymm ?_ ?_⟩
  · rw [tailFlag, Submodule.map_span, span_le]
    rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    obtain ⟨c, -, hc⟩ := hg j
    rw [LinearEquiv.coe_coe, hc]
    exact Submodule.smul_mem _ _ (subset_span ⟨j, hj, rfl⟩)
  · rw [tailFlag, span_le]
    rintro _ ⟨j, hj, rfl⟩
    obtain ⟨c, hc0, hc⟩ := hg j
    refine ⟨c⁻¹ • hypVec K A (.inl j), Submodule.smul_mem _ _ (subset_span ⟨j, hj, rfl⟩), ?_⟩
    rw [LinearEquiv.coe_coe, map_smul, hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]

theorem prodHom_rootElt_mem (β : Fin r → ℤ) (t : K) :
    prodHom A (rootElt r K β t) ∈ orthElementaryGroup (quadTail r qA) := by
  rw [prodHom_apply, ← tailLongElt_eq_prodCongr]
  exact tailLongElt_mem β t

theorem prodHom_rootH_mem_tailBorel {α : Fin r → ℤ} (hα : α ∈ roots r) {c : K} (hc : c ≠ 0) :
    prodHom A (rootH r K α c) ∈ tailBorel r qA := by
  have hE : prodHom A (rootH r K α c) ∈ orthElementaryGroup (quadTail r qA) := by
    rw [rootH, rootN, rootN, map_mul, map_inv, map_mul, map_mul, map_mul, map_mul]
    exact mul_mem (mul_mem (mul_mem (prodHom_rootElt_mem _ _) (prodHom_rootElt_mem _ _))
      (prodHom_rootElt_mem _ _)) (inv_mem (mul_mem (mul_mem (prodHom_rootElt_mem _ _)
        (prodHom_rootElt_mem _ _)) (prodHom_rootElt_mem _ _)))
  obtain ⟨hH, -⟩ := orthogonal_geometry_split_root_rank_one_factorization (K := K) hα
  have hB := (mem_borel.1 (torus_le_borel (hH c hc))).2
  refine mem_tailBorel.2 ⟨hE, fun k hk1 hkr => ?_⟩
  rw [prodHom_apply]
  exact (map_tailFlag_prodCongr_eq_iff _ _ k).2 (hB k hk1 hkr)

end Borel

section Conj

variable (hani : qA.Anisotropic) {a₀ : A} (ha₀ : a₀ ≠ 0)
include hani ha₀

theorem inv_mul_tailTorus_mul_mem {n : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _}
    (hn : n ∈ tailTorusWeyl r qA a₀) {t : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _}
    (ht : t ∈ tailTorus r qA) : n⁻¹ * t * n ∈ tailTorus r qA := by
  have htN : t ∈ tailTorusWeyl r qA a₀ := tailTorus_le_tailTorusWeyl a₀ ht
  have hker : (⟨t, htN⟩ : tailTorusWeyl r qA a₀) ∈ (tailTorusWeylNu r qA hani ha₀).ker := by
    rw [tailTorusWeylNu_ker hani ha₀, Subgroup.mem_subgroupOf]
    exact ht
  have hker' : (⟨n, hn⟩ : tailTorusWeyl r qA a₀)⁻¹ * ⟨t, htN⟩ * ⟨n, hn⟩ ∈
      (tailTorusWeylNu r qA hani ha₀).ker := by
    rw [MonoidHom.mem_ker] at hker ⊢
    rw [map_mul, map_mul, hker, mul_one, map_inv, inv_mul_cancel]
  rw [tailTorusWeylNu_ker hani ha₀, Subgroup.mem_subgroupOf] at hker'
  exact hker'

theorem inv_mul_mul_mem_tailRootGroup {n : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _}
    (hn : n ∈ tailTorusWeyl r qA a₀) {β : Fin r → ℤ} (hβ : β ∈ rootsB r)
    {x : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _} (hx : x ∈ tailRootGroup r qA β) :
    n⁻¹ * x * n ∈ tailRootGroup r qA ((((tailTorusWeylNu r qA hani ha₀ ⟨n, hn⟩)⁻¹ :
      weylGroupB r) : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) β) := by
  have h := map_conj_tailRootGroup hani ha₀ (⟨n, hn⟩ : tailTorusWeyl r qA a₀)⁻¹ hβ
  rw [map_inv] at h
  rw [← h]
  refine ⟨x, hx, ?_⟩
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_inv, inv_inv]

theorem map_conj_tailWeylElt_tailUnipotentExcept_le (i : Fin r) :
    (tailUnipotentExcept r qA i).map (MulAut.conj (tailWeylElt r qA a₀ i)).toMonoidHom ≤
      tailUnipotent r qA := by
  rw [tailUnipotentExcept, Subgroup.map_iSup]
  refine iSup_le fun β => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hβ => ?_
  have h := map_conj_tailRootGroup hani ha₀
    ⟨tailWeylElt r qA a₀ i, tailWeylElt_mem_tailTorusWeyl a₀ i⟩ (posRootsB_subset_rootsB hβ.1)
  rw [tailTorusWeylNu_tailWeylElt hani ha₀ i] at h
  change (tailRootGroup r qA β).map (MulAut.conj (tailWeylElt r qA a₀ i)).toMonoidHom = _ at h
  rw [h]
  exact tailRootGroup_le_tailUnipotent ((bijOn_simpleReflB i).mapsTo hβ).1

end Conj

section Exchange

variable [FiniteDimensional K A] (hani : qA.Anisotropic) {a₀ : A} (ha₀ : a₀ ≠ 0)
include hani ha₀

theorem exists_tailBorel_tailWeylElt_root {n : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _}
    (hn : n ∈ tailTorusWeyl r qA a₀) (i : Fin r)
    {b₁ b₂ b₃ : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _} (h1 : b₁ ∈ tailBorel r qA)
    (h2 : b₂ ∈ tailBorel r qA) (h3 : b₃ ∈ tailBorel r qA) :
    ∃ c₁ ∈ tailBorel r qA, ∃ x ∈ tailRootGroup r qA (simpleRootB r i), ∃ c₂ ∈ tailBorel r qA,
      b₁ * tailWeylElt r qA a₀ i * b₂ * n * b₃ = c₁ * tailWeylElt r qA a₀ i * x * n * c₂ := by
  have hb2 : b₂ ∈ (tailUnipotent r qA :
      Set (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A))) *
      (tailTorus r qA : Set (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A))) := by
    rw [← (tailBorel_eq_mul hani).2]
    exact h2
  obtain ⟨υ, hυ, t, ht, rfl⟩ := hb2
  obtain ⟨-, -, hfac, -⟩ := (orthogonal_geometry_tail_simple_positive_parameter_kernels
    (r := r) hani).2.2 i
  have hυ' : υ ∈ (tailUnipotentExcept r qA i :
      Set (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A))) *
      (tailRootGroup r qA (simpleRootB r i) :
        Set (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A))) := by
    rw [← hfac]
    exact hυ
  obtain ⟨u, hu, x, hx, rfl⟩ := hυ'
  have hc₁ : b₁ * (tailWeylElt r qA a₀ i * u * (tailWeylElt r qA a₀ i)⁻¹) ∈ tailBorel r qA :=
    mul_mem h1 (tailUnipotent_le_tailBorel hani
      (map_conj_tailWeylElt_tailUnipotentExcept_le hani ha₀ i ⟨u, hu, rfl⟩))
  have hc₂ : (n⁻¹ * t * n) * b₃ ∈ tailBorel r qA :=
    mul_mem (tailTorus_le_tailBorel (inv_mul_tailTorus_mul_mem hani ha₀ hn ht)) h3
  exact ⟨_, hc₁, x, hx, _, hc₂, by group⟩

theorem exists_tailWeylElt_mul_eq (i : Fin r) {x : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _}
    (hx : x ∈ tailRootGroup r qA (simpleRootB r i)) (hx1 : x ≠ 1) :
    ∃ c ∈ tailBorel r qA, ∃ y ∈ tailRootGroup r qA (-simpleRootB r i),
      tailWeylElt r qA a₀ i * x = c * y := by
  by_cases hi : i.val + 1 < r
  ·
    have hα : simpleRoot r i ∈ roots r := by
      rw [← simpleRootB_eq_simpleRoot hi]
      exact posRoots_subset_roots (simpleRootB_mem_posRoots_of_lt hi)
    obtain ⟨s, rfl⟩ := (mem_tailRootGroup_long (by
      rw [simpleRootB_eq_simpleRoot hi]; exact hα)).1 hx
    have hs : s ≠ 0 := fun h => hx1 (by rw [h, tailLongElt_zero])
    obtain ⟨-, -, hfac, hnr⟩ := orthogonal_geometry_split_root_rank_one_factorization (K := K) hα
    have hneg : -simpleRootB r i ∈ roots r := by
      rw [simpleRootB_eq_simpleRoot hi]
      exact neg_mem_roots hα
    refine ⟨tailLongElt r qA (simpleRootB r i) (-s⁻¹) * prodHom A (rootH r K (simpleRoot r i)
      (-s⁻¹)), mul_mem (tailUnipotent_le_tailBorel hani (tailRootGroup_le_tailUnipotent
        (simpleRootB_mem_posRootsB i) ((mem_tailRootGroup_long (posRoots_subset_roots
          (simpleRootB_mem_posRoots_of_lt hi))).2 ⟨_, rfl⟩)))
      (prodHom_rootH_mem_tailBorel hα (neg_ne_zero.2 (inv_ne_zero hs))),
      tailLongElt r qA (-simpleRootB r i) s⁻¹, (mem_tailRootGroup_long hneg).2 ⟨_, rfl⟩, ?_⟩
    have e := congrArg (prodHom A) (hfac s hs)
    rw [map_mul, map_mul, map_mul] at e
    rw [tailWeylElt_eq_prodCongr a₀ hi, ← prodHom_apply, hnr i, simpleRootB_eq_simpleRoot hi,
      tailLongElt_eq_prodCongr, tailLongElt_eq_prodCongr, tailLongElt_eq_prodCongr,
      ← prodHom_apply, ← prodHom_apply, ← prodHom_apply]
    exact e
  ·
    rw [simpleRootB_of_not_lt hi] at hx ⊢
    obtain ⟨a, rfl⟩ := mem_tailRootGroup_eps.1 hx
    have ha : a ≠ 0 := fun h => hx1 (by
      rw [h, show ((0 : Fin r ⊕ Fin r → K), (0 : A)) = 0 from rfl]
      exact eichler_zero_right _ _)
    set P := hypPairT r qA i
    set A' : Submodule K ((Fin r ⊕ Fin r → K) × A) := LinearMap.range
      (LinearMap.inr K (Fin r ⊕ Fin r → K) A) with hA'
    have hA'P : A' ≤ P.perp := by
      rintro _ ⟨b, rfl⟩
      exact tail_mem_perp_hypPairT i b
    have hani' : ∀ v ∈ A', quadTail r qA v = 0 → v = 0 := by
      rintro _ ⟨b, rfl⟩ hb
      rw [LinearMap.inr_apply, quadTail_tail] at hb
      rw [LinearMap.inr_apply, hani b hb]
      rfl
    have hmem : ∀ b : A, ((0 : Fin r ⊕ Fin r → K), b) ∈ A' := fun b => ⟨b, rfl⟩
    have hne : ∀ {b : A}, b ≠ 0 → ((0 : Fin r ⊕ Fin r → K), b) ≠ 0 := fun hb h =>
      hb (congrArg Prod.snd h)
    obtain ⟨hT, heq, -⟩ := orthogonal_geometry_tail_short_root_exchange P hA'P hani'
      (hmem a₀) (hne ha₀) _ (hmem a) (hne ha)
    set t := shortWeyl P ((0 : Fin r ⊕ Fin r → K), a₀) *
      (shortWeyl P (-((0 : Fin r ⊕ Fin r → K), a)))⁻¹ with ht
    have hqa : qA a ≠ 0 := fun h => ha (hani a h)
    have hq₀ : qA a₀ ≠ 0 := fun h => ha₀ (hani a₀ h)
    have htB : t ∈ tailBorel r qA := by
      refine mem_tailBorel_of_diag (mem_exchTorus.1 hT).1 fun j => ?_
      by_cases hj : j = i
      · subst hj
        refine ⟨(quadTail r qA (0, a))⁻¹ * quadTail r qA (0, a₀), ?_, ?_⟩
        · rw [quadTail_tail, quadTail_tail]
          exact mul_ne_zero (inv_ne_zero hqa) hq₀
        · exact shortWeyl_mul_inv_e P (tail_mem_perp_hypPairT j a₀) (by rwa [quadTail_tail])
            (tail_mem_perp_hypPairT j a) (by rwa [quadTail_tail])
      · refine ⟨1, one_ne_zero, ?_⟩
        have hjP : hypVec K A (.inl j) ∈ P.perp := HypPair.mem_perp.2 ⟨by
          rw [hypPairT_e, polar_hypVec_hypVec]; simp, by
          rw [hypPairT_f, polar_hypVec_hypVec]; simp [hj]⟩
        have hfix : ∀ b : A, qA b ≠ 0 → shortWeyl P ((0 : Fin r ⊕ Fin r → K), b)
            (hypVec K A (.inl j)) = hypVec K A (.inl j) := fun b hb => by
          rw [shortWeyl_perp P (tail_mem_perp_hypPairT i b) (by rwa [quadTail_tail]) hjP,
            polar_hypVec_tail, zero_mul, zero_smul, sub_zero]
        have hneg : -((0 : Fin r ⊕ Fin r → K), a) = ((0 : Fin r ⊕ Fin r → K), -a) := by
          rw [Prod.neg_mk, neg_zero]
        rw [one_smul, ht, LinearEquiv.mul_apply, hneg, shortWeyl_inv P (tail_mem_perp_hypPairT i _)
          (by rwa [quadTail_tail, QuadraticMap.map_neg]), hfix (-a)
          (by rwa [QuadraticMap.map_neg]), hfix a₀ hq₀]
    have hneg : -((0 : Fin r ⊕ Fin r → K), a) = ((0 : Fin r ⊕ Fin r → K), -a) := by
      rw [Prod.neg_mk, neg_zero]
    have hl : -((quadTail r qA ((0 : Fin r ⊕ Fin r → K), a))⁻¹ •
        ((0 : Fin r ⊕ Fin r → K), a)) = ((0 : Fin r ⊕ Fin r → K), -((qA a)⁻¹ • a)) := by
      rw [quadTail_tail, Prod.smul_mk, smul_zero, Prod.neg_mk, neg_zero]
    refine ⟨t * eichler (quadTail r qA) P.e ((0 : Fin r ⊕ Fin r → K), -a),
      mul_mem htB (tailUnipotent_le_tailBorel hani (tailRootGroup_le_tailUnipotent
        (Or.inl ⟨i, rfl⟩) (mem_tailRootGroup_eps.2 ⟨_, rfl⟩))),
      eichler (quadTail r qA) P.f ((0 : Fin r ⊕ Fin r → K), -((qA a)⁻¹ • a)),
      mem_tailRootGroup_neg_eps.2 ⟨_, rfl⟩, ?_⟩
    rw [tailWeylElt_of_not_lt a₀ hi]
    rw [hneg, hl] at heq
    change shortWeyl P ((0 : Fin r ⊕ Fin r → K), a₀) *
      eichler (quadTail r qA) P.e ((0 : Fin r ⊕ Fin r → K), a) = _
    rw [heq, mul_assoc t]

theorem tailBorel_tailWeylElt_mul_mem {n : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _}
    (hn : n ∈ tailTorusWeyl r qA a₀) (i : Fin r)
    {b₁ b₂ b₃ : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _} (h1 : b₁ ∈ tailBorel r qA)
    (h2 : b₂ ∈ tailBorel r qA) (h3 : b₃ ∈ tailBorel r qA) :
    ((((tailTorusWeylNu r qA hani ha₀ ⟨n, hn⟩)⁻¹ : weylGroupB r) :
        (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) (simpleRootB r i) ∈ posRootsB r →
      ∃ c₁ ∈ tailBorel r qA, ∃ c₂ ∈ tailBorel r qA,
        b₁ * tailWeylElt r qA a₀ i * b₂ * n * b₃ = c₁ * (tailWeylElt r qA a₀ i * n) * c₂) ∧
    ((∃ c₁ ∈ tailBorel r qA, ∃ c₂ ∈ tailBorel r qA,
        b₁ * tailWeylElt r qA a₀ i * b₂ * n * b₃ = c₁ * (tailWeylElt r qA a₀ i * n) * c₂) ∨
      ∃ c₁ ∈ tailBorel r qA, ∃ c₂ ∈ tailBorel r qA,
        b₁ * tailWeylElt r qA a₀ i * b₂ * n * b₃ = c₁ * n * c₂) := by
  obtain ⟨c₁, hc₁, x, hx, c₂, hc₂, he⟩ := exists_tailBorel_tailWeylElt_root hani ha₀ hn i h1 h2 h3
  have hα : simpleRootB r i ∈ posRootsB r := simpleRootB_mem_posRootsB i
  set w := (((tailTorusWeylNu r qA hani ha₀ ⟨n, hn⟩)⁻¹ : weylGroupB r) :
    (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) with hw
  have hpos : w (simpleRootB r i) ∈ posRootsB r →
      ∃ c₁ ∈ tailBorel r qA, ∃ c₂ ∈ tailBorel r qA,
        b₁ * tailWeylElt r qA a₀ i * b₂ * n * b₃ = c₁ * (tailWeylElt r qA a₀ i * n) * c₂ := by
    intro hwα
    have hx' := inv_mul_mul_mem_tailRootGroup hani ha₀ hn (posRootsB_subset_rootsB hα) hx
    refine ⟨c₁, hc₁, _, mul_mem (tailUnipotent_le_tailBorel hani
      (tailRootGroup_le_tailUnipotent hwα hx')) hc₂, ?_⟩
    rw [he]
    group
  refine ⟨hpos, ?_⟩
  by_cases hwα : w (simpleRootB r i) ∈ posRootsB r
  · exact Or.inl (hpos hwα)
  by_cases hx1 : x = 1
  · refine Or.inl ⟨c₁, hc₁, c₂, hc₂, ?_⟩
    rw [he, hx1, mul_one, mul_assoc c₁]
  right
  have hroot : w (simpleRootB r i) ∈ rootsB r :=
    apply_mem_rootsB (tailTorusWeylNu r qA hani ha₀ ⟨n, hn⟩)⁻¹.2 (posRootsB_subset_rootsB hα)
  have hneg : -(w (simpleRootB r i)) ∈ posRootsB r :=
    ((mem_posRootsB_or_neg_mem_posRootsB hroot).1).resolve_left hwα
  obtain ⟨c, hc, y, hy, hxy⟩ := exists_tailWeylElt_mul_eq hani ha₀ i hx hx1
  have hy' := inv_mul_mul_mem_tailRootGroup hani ha₀ hn
    (neg_mem_rootsB (posRootsB_subset_rootsB hα)) hy
  rw [map_neg] at hy'
  refine ⟨c₁ * c, mul_mem hc₁ hc, _, mul_mem (tailUnipotent_le_tailBorel hani
    (tailRootGroup_le_tailUnipotent hneg hy')) hc₂, ?_⟩
  rw [he, mul_assoc c₁ (tailWeylElt r qA a₀ i), hxy]
  group

end Exchange

theorem orthogonal_geometry_tail_Bruhat_exchange {K : Type*} [Field K] {A : Type*}
    [AddCommGroup A] [Module K A] [FiniteDimensional K A] {r : ℕ} {qA : QuadraticForm K A}
    (hani : qA.Anisotropic) {a₀ : A} (ha₀ : a₀ ≠ 0)
    {n : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)}
    (hn : n ∈ tailTorusWeyl r qA a₀) (i : Fin r) :
    (tailBorel r qA : Set (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A))) *
        {tailWeylElt r qA a₀ i} * (tailBorel r qA : Set _) * {n} * (tailBorel r qA : Set _) ⊆
      (tailBorel r qA : Set _) * {tailWeylElt r qA a₀ i * n} * (tailBorel r qA : Set _) ∪
        (tailBorel r qA : Set _) * {n} * (tailBorel r qA : Set _) ∧
    ((((tailTorusWeylNu r qA hani ha₀ ⟨n, hn⟩)⁻¹ : weylGroupB r) :
        (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) (simpleRootB r i) ∈ posRootsB r →
      (tailBorel r qA : Set (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A))) *
          {tailWeylElt r qA a₀ i} * (tailBorel r qA : Set _) * {n} * (tailBorel r qA : Set _) =
        (tailBorel r qA : Set _) * {tailWeylElt r qA a₀ i * n} * (tailBorel r qA : Set _)) := by
  refine ⟨fun g hg => ?_, fun hw => Set.Subset.antisymm (fun g hg => ?_) fun g hg => ?_⟩
  · obtain ⟨b₁, h1, b₂, h2, b₃, h3, rfl⟩ := mem_mul_singleton_mul_singleton_mul.1 hg
    rcases (tailBorel_tailWeylElt_mul_mem hani ha₀ hn i h1 h2 h3).2 with
      ⟨c₁, hc₁, c₂, hc₂, he⟩ | ⟨c₁, hc₁, c₂, hc₂, he⟩
    · exact Or.inl (mem_mul_singleton_mul.2 ⟨c₁, hc₁, c₂, hc₂, he⟩)
    · exact Or.inr (mem_mul_singleton_mul.2 ⟨c₁, hc₁, c₂, hc₂, he⟩)
  · obtain ⟨b₁, h1, b₂, h2, b₃, h3, rfl⟩ := mem_mul_singleton_mul_singleton_mul.1 hg
    obtain ⟨c₁, hc₁, c₂, hc₂, he⟩ := (tailBorel_tailWeylElt_mul_mem hani ha₀ hn i h1 h2 h3).1 hw
    exact mem_mul_singleton_mul.2 ⟨c₁, hc₁, c₂, hc₂, he⟩
  · obtain ⟨b₁, h1, b₂, h2, rfl⟩ := mem_mul_singleton_mul.1 hg
    exact mem_mul_singleton_mul_singleton_mul.2 ⟨b₁, h1, 1, one_mem _, b₂, h2, by group⟩

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
