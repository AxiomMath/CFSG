module

public import CFSG.LocalAnalysis.ComponentInitial.FixedComponentCorrespondence

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped commutatorElement

variable {M : Type*} [Group M] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem commute_of_commutator_eq_bot {H K : Subgroup M} (h : ⁅H, K⁆ = ⊥) {x y : M} (hx : x ∈ H)
    (hy : y ∈ K) : x * y = y * x := by
  have := Subgroup.commutator_mem_commutator hx hy
  rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
  exact this

omit [Fintype ι] [DecidableEq ι] in
theorem coordMul_comm {A : ι → Subgroup M} (hc : ∀ i j, i ≠ j → ⁅A i, A j⁆ = ⊥) :
    Pairwise fun i j => ∀ (x : A i) (y : A j), Commute ((A i).subtype x) ((A j).subtype y) :=
  fun i j hij x y => commute_of_commutator_eq_bot (hc i j hij) x.2 y.2

@[expose] def coordMul (A : ι → Subgroup M) (hc : ∀ i j, i ≠ j → ⁅A i, A j⁆ = ⊥) :
    (∀ i, A i) →* M :=
  MonoidHom.noncommPiCoprod (fun i => (A i).subtype) (coordMul_comm hc)

@[expose] def restrictAut (a : MulAut M) (H : Subgroup M) (hH : H.map a.toMonoidHom = H) :
    MulAut H :=
  (MulEquiv.subgroupMap a H).trans (MulEquiv.subgroupCongr hH)

theorem coe_restrictAut (a : MulAut M) (H : Subgroup M) (hH : H.map a.toMonoidHom = H) (x : H) :
    ((restrictAut a H hH x : H) : M) = a x := rfl

@[expose] def coordAut (a : MulAut M) (A : ι → Subgroup M)
    (hA : ∀ i, (A i).map a.toMonoidHom = A i) : MulAut (∀ i, A i) :=
  MulEquiv.piCongrRight fun i => restrictAut a (A i) (hA i)

section

variable {A : ι → Subgroup M} {hc : ∀ i j, i ≠ j → ⁅A i, A j⁆ = ⊥}

theorem coordMul_mulSingle (i : ι) (y : A i) : coordMul A hc (Pi.mulSingle i y) = y := by
  rw [coordMul, MonoidHom.noncommPiCoprod_mulSingle]
  rfl

omit [DecidableEq ι] in
theorem range_coordMul : (coordMul A hc).range = ⨆ i, A i := by
  rw [coordMul, MonoidHom.noncommPiCoprod_range]
  simp only [Subgroup.range_subtype]

theorem mem_ker_coordMul_iff (x : ∀ i, A i) :
    x ∈ (coordMul A hc).ker ↔ (∀ i, x i ∈ center (A i)) ∧ coordMul A hc x = 1 := by
  refine ⟨fun hx => ⟨fun i => ?_, hx⟩, fun h => h.2⟩
  rw [Subgroup.mem_center_iff]
  intro y
  have hu : x * Pi.mulSingle i y * x⁻¹ * (Pi.mulSingle i y)⁻¹ =
      Pi.mulSingle i (x i * y * (x i)⁻¹ * y⁻¹) := by
    funext j
    rcases eq_or_ne j i with rfl | hj
    · simp
    · simp [hj]
  have h1 := congrArg (coordMul A hc) hu
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, MonoidHom.mem_ker.1 hx, coordMul_mulSingle,
    coordMul_mulSingle, one_mul, inv_one, mul_one, mul_inv_cancel] at h1
  have h2 : x i * y * (x i)⁻¹ * y⁻¹ = 1 := Subtype.ext h1.symm
  have h3 : x i * y = y * x i := by
    calc x i * y = x i * y * (x i)⁻¹ * y⁻¹ * (y * x i) := by group
      _ = y * x i := by rw [h2, one_mul]
  exact h3.symm

theorem ker_coordMul_le_center : (coordMul A hc).ker ≤ center (∀ i, A i) := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro z
  funext i
  exact Subgroup.mem_center_iff.1 (((mem_ker_coordMul_iff x).1 hx).1 i) (z i)

end

section Fixed

variable {A : ι → Subgroup M} {hc : ∀ i j, i ≠ j → ⁅A i, A j⁆ = ⊥} {a : MulAut M}
  {hA : ∀ i, (A i).map a.toMonoidHom = A i}

omit [Fintype ι] [DecidableEq ι] in
theorem coordAut_apply (x : ∀ i, A i) (i : ι) : ((coordAut a A hA x i : A i) : M) = a (x i) :=
  rfl

omit [DecidableEq ι] in
theorem coordMul_coordAut (x : ∀ i, A i) :
    coordMul A hc (coordAut a A hA x) = a (coordMul A hc x) := by
  rw [coordMul, MonoidHom.noncommPiCoprod_apply, MonoidHom.noncommPiCoprod_apply,
    Finset.map_noncommProd]
  rfl

omit [Fintype ι] [DecidableEq ι] in
theorem coordAut_coordAut (ha : ∀ x, a (a x) = x) (x : ∀ i, A i) :
    coordAut a A hA (coordAut a A hA x) = x := by
  funext i
  exact Subtype.ext (ha _)

omit [Fintype ι] [DecidableEq ι] in
theorem mem_fixed_coordAut {x : ∀ i, A i} :
    x ∈ fixedSubgroup (coordAut a A hA) ↔ ∀ i, ((x i : A i) : M) ∈ fixedSubgroup a := by
  rw [mem_fixedSubgroup_iff]
  constructor
  · intro hx i
    exact congrArg Subtype.val (congrFun hx i)
  · intro h
    funext i
    exact Subtype.ext (h i)

theorem map_fixed_coordAut :
    (fixedSubgroup (coordAut a A hA)).map (coordMul A hc) = ⨆ i, (A i ⊓ fixedSubgroup a) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [coordMul, MonoidHom.noncommPiCoprod_apply]
    refine Subgroup.noncommProd_mem _ _ fun i _ => ?_
    exact le_iSup (fun i => A i ⊓ fixedSubgroup a) i
      (Subgroup.mem_inf.2 ⟨(x i).2, (mem_fixed_coordAut.1 hx) i⟩)
  · refine iSup_le fun i => ?_
    intro y hy
    obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.1 hy
    refine Subgroup.mem_map.2 ⟨Pi.mulSingle i ⟨y, hy1⟩, ?_, coordMul_mulSingle i _⟩
    rw [mem_fixed_coordAut]
    intro j
    rcases eq_or_ne j i with rfl | hj
    · simpa using hy2
    · simp only [Pi.mulSingle_eq_of_ne hj, OneMemClass.coe_one]
      exact one_mem _

end Fixed

theorem factorwise_involution_central_product_fixed_layer [Finite M] (A : ι → Subgroup M)
    (hgen : ⨆ i, A i = ⊤) (hc : ∀ i j, i ≠ j → ⁅A i, A j⁆ = ⊥) (a : MulAut M)
    (ha : ∀ x, a (a x) = x) (hA : ∀ i, (A i).map a.toMonoidHom = A i) :
    let X := fixedSubgroup a
    let Bi : ι → Subgroup M := fun i => A i ⊓ fixedSubgroup a
    let B := ⨆ i, Bi i
    let π := coordMul A hc
    let F := π.ker ⊓ fixedSubgroup (coordAut a A hA)
    ((π.ker : Set (∀ i, A i)) = {x | (∀ i, x i ∈ center (A i)) ∧ π x = 1}) ∧
      π.ker ≤ center (∀ i, A i) ∧
      (∃ _ : (B.subgroupOf X).Normal, IsElementaryAbelian 2 (X ⧸ B.subgroupOf X) ∧
        ∃ n : ℕ, Nat.card (X ⧸ B.subgroupOf X) = 2 ^ n) ∧
      B.relIndex X ≤
        (squareImage (F := F) ((inf_le_left : F ≤ π.ker).trans ker_coordMul_le_center)).relIndex F ∧
      {Q : Subgroup M | CFSG.Assembly.IsComponentOf Q X} =
        ⋃ i, {Q | CFSG.Assembly.IsComponentOf Q (Bi i)} ∧
      (Pairwise fun i j => Disjoint {Q : Subgroup M | CFSG.Assembly.IsComponentOf Q (Bi i)}
        {Q | CFSG.Assembly.IsComponentOf Q (Bi j)}) ∧
      (layer X).map X.subtype = ⨆ i, (layer (Bi i)).map (Bi i).subtype ∧
      (layer X = ⊥ ↔ ∀ i, layer (Bi i) = ⊥) := by
  intro X Bi B π F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hπ : Function.Surjective π := MonoidHom.range_eq_top.1 (by rw [range_coordMul, hgen])
  have hK : π.ker ≤ center (∀ i, A i) := ker_coordMul_le_center
  have hcomm : ∀ x, π (coordAut a A hA x) = a (π x) := coordMul_coordAut
  have haD : ∀ x, coordAut a A hA (coordAut a A hA x) = x := coordAut_coordAut ha
  have hI : (fixedSubgroup (coordAut a A hA)).map π = B := map_fixed_coordAut
  obtain ⟨-, -, -, -, h5, h6, h7⟩ :=
    full_central_kernel_involution_fixed_image_quotient hπ hK haD (fun s => ha s) hcomm
  rw [hI] at h5 h6
  obtain ⟨hBn, -, hab⟩ := h5
  have hquot : ∃ _ : (B.subgroupOf X).Normal, IsElementaryAbelian 2 (X ⧸ B.subgroupOf X) ∧
      ∃ n : ℕ, Nat.card (X ⧸ B.subgroupOf X) = 2 ^ n := by
    refine ⟨hBn, hab, IsPGroup.iff_card.1 fun g => ⟨1, ?_⟩⟩
    obtain ⟨k, hk⟩ := hab.exponent_dvd_p
    rw [pow_one, show (2 : ℕ) = Monoid.exponent _ * k from hk, pow_mul,
      Monoid.pow_exponent_eq_one, one_pow]
  have hBiB : ∀ i, Bi i ≤ B := fun i => le_iSup Bi i
  have hBX : B ≤ X := iSup_le fun i => inf_le_right
  have hBicomm : ∀ i j, i ≠ j → Bi j ≤ centralizer (Bi i : Set M) := fun i j hij x hx => by
    rw [mem_centralizer_iff]
    intro y hy
    exact (commute_of_commutator_eq_bot (hc j i hij.symm) (Subgroup.mem_inf.1 hx).1
      (Subgroup.mem_inf.1 hy).1).symm
  have hBin : ∀ i, ((Bi i).subgroupOf B).Normal := fun i => by
    rw [normal_subgroupOf_iff_le_normalizer (hBiB i)]
    refine iSup_le fun j => ?_
    rcases eq_or_ne j i with rfl | hij
    · exact le_normalizer
    · exact (hBicomm i j hij.symm).trans (centralizer_le_normalizer _)
  have hXB : ⁅X, X⁆ ≤ B := hI ▸ commutator_fixed_le_image hπ hK haD hcomm
  have hcomps : {Q : Subgroup M | CFSG.Assembly.IsComponentOf Q X} =
      ⋃ i, {Q | CFSG.Assembly.IsComponentOf Q (Bi i)} := by
    ext R
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro hR
      have hRB : R ≤ B := by
        calc R = ⁅R, R⁆ := (commutator_self_of_isQuasisimple hR.2.2).symm
          _ ≤ ⁅X, X⁆ := commutator_mono hR.1 hR.1
          _ ≤ B := hXB
      have hRBc : CFSG.Assembly.IsComponentOf R B := isComponentOf_of_le hR hRB hBX
      have hRn := (isComponentOf_iff_isComponent_subgroupOf hRB).1 hRBc
      by_contra hnone
      push Not at hnone
      have hcent : ∀ i, ⁅R, Bi i⁆ = ⊥ := by
        intro i
        rcases component_normal_subgroup hRn (hBin i) with h | h
        · exfalso
          have hRi : R ≤ Bi i := by
            intro x hx
            have := h (show (⟨x, hRB hx⟩ : B) ∈ R.subgroupOf B from hx)
            exact this
          exact hnone i (isComponentOf_of_le hR hRi inf_le_right)
        · have h' := congrArg (Subgroup.map B.subtype) h
          rwa [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
            Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hRB, inf_eq_left.2 (hBiB i),
            Subgroup.map_bot] at h'
      apply not_le_centralizer_self_of_isQuasisimple hR.2.2
      intro x hx
      have hxB : B ≤ centralizer ({x} : Set M) := iSup_le fun i y hy => by
        rw [mem_centralizer_iff]
        rintro _ rfl
        exact commute_of_commutator_eq_bot (hcent i) hx hy
      rw [mem_centralizer_iff]
      intro y hy
      exact (mem_centralizer_iff.1 (hxB (hRB hy)) x rfl).symm
    · rintro ⟨i, hR⟩
      refine ⟨hR.1.trans ((hBiB i).trans hBX), ?_, hR.2.2⟩
      exact assembly_isSubnormal_trans hR.2.1 (CFSG.Assembly.IsSubnormal.step (hBiB i) (hBin i)
        (CFSG.Assembly.IsSubnormal.step hBX hBn (CFSG.Assembly.IsSubnormal.refl _)))
  have hdisj : Pairwise fun i j => Disjoint {Q : Subgroup M | CFSG.Assembly.IsComponentOf Q (Bi i)}
      {Q | CFSG.Assembly.IsComponentOf Q (Bi j)} := by
    intro i j hij
    refine Set.disjoint_left.2 fun R hRi hRj => ?_
    apply not_le_centralizer_self_of_isQuasisimple hRi.2.2
    exact hRj.1.trans ((hBicomm i j hij).trans (Subgroup.centralizer_le hRi.1))
  have hlayer : (layer X).map X.subtype = ⨆ i, (layer (Bi i)).map (Bi i).subtype := by
    rw [layer_map_subtype, hcomps, sSup_iUnion]
    exact iSup_congr fun i => (layer_map_subtype (Bi i)).symm
  have hiff : layer X = ⊥ ↔ ∀ i, layer (Bi i) = ⊥ := by
    rw [layer_eq_bot_iff, hcomps, Set.iUnion_eq_empty]
    exact forall_congr' fun i => (layer_eq_bot_iff (Bi i)).symm
  refine ⟨?_, hK, hquot, h6.trans h7, hcomps, hdisj, hlayer, hiff⟩
  ext x
  exact mem_ker_coordMul_iff x

end CFSG.LocalAnalysis.ComponentInitial
