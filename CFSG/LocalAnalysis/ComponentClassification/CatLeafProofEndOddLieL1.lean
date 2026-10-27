module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieLCore2
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCBasic
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4OutCard
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieLCore
public import CFSG.LocalAnalysis.ComponentClassification.Sol78F5EndB

public section

namespace CFSG.ComponentClassification.CatLeafProof.EndOddLin

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
open CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.CatLeafProof.EndOddCore
open CFSG.ComponentClassification.Burgoyne.C (commutator_eq_of_isPComponent not_le_of_isSolvable
  eq_of_le_of_isQuasisimple)
open scoped commutatorElement MatrixGroups

variable {X : Type} [Group X]

@[expose] def QuatBlock (N : Subgroup X) : Prop :=
  Group.IsSolvable N ∨ (IsQuasisimple N ∧ ∃ H : Subgroup N, Nonempty (H ≃* QuaternionGroup 2))

theorem quatBlock_of_isSolvable {N : Subgroup X} (h : Group.IsSolvable N) : QuatBlock N :=
  Or.inl h

theorem quatBlock_of_quat {N : Subgroup X} (hq : IsQuasisimple N) (H : Subgroup N)
    (e : H ≃* QuaternionGroup 2) : QuatBlock N :=
  Or.inr ⟨hq, H, ⟨e⟩⟩

omit [Group X] in
theorem quatBlock_map_of_sl2 {S : Type} [Group S] {Z : Subgroup S} [Z.Normal]
    {F : Subgroup S} (hq : IsQuasisimple F) {k : Type*} [Field k] [Finite k]
    (hk : ringChar k ≠ 2) (φ : SL(2, k) →* S) (hφF : ∀ g, φ g ∈ F) (hφ : φ (-1) ∉ Z) :
    QuatBlock (F.map (QuotientGroup.mk' Z)) := by
  let ψ : SL(2, k) →* F.map (QuotientGroup.mk' Z) :=
    ((QuotientGroup.mk' Z).comp φ).codRestrict (F.map (QuotientGroup.mk' Z))
      (fun g => mem_map_of_mem _ (hφF g))
  have hψ1 : ψ (-1) ≠ 1 := by
    intro h1
    apply hφ
    have h2 : QuotientGroup.mk' Z (φ (-1)) = 1 := congrArg Subtype.val h1
    exact (QuotientGroup.eq_one_iff _).1 h2
  obtain ⟨H, ⟨eH⟩⟩ := UnbalancedGS.SymplecticExclusion.exists_quaternion_of_sl2_hom hk ψ hψ1
  have hr : ((QuotientGroup.mk' Z).comp F.subtype).range = F.map (QuotientGroup.mk' Z) := by
    rw [MonoidHom.range_comp, range_subtype]
  rcases LocalAnalysis.ComponentInitial.quasisimple_homomorphic_images hq
      ((QuotientGroup.mk' Z).comp F.subtype) with h0 | h0
  · exfalso
    apply hφ
    have hm : QuotientGroup.mk' Z (φ (-1)) ∈ ((QuotientGroup.mk' Z).comp F.subtype).range :=
      ⟨⟨φ (-1), hφF _⟩, rfl⟩
    rw [h0, mem_bot] at hm
    exact (QuotientGroup.eq_one_iff _).1 hm
  · rw [hr] at h0
    exact quatBlock_of_quat h0 H eH

variable [Finite X]

theorem false_of_config_le_block {z : X} {K D : Subgroup X} (h : Config z K D) {N : Subgroup X}
    (hNC : N ≤ centralizer ({z} : Set X)) (hB : QuatBlock N) (hKN : K ≤ N) : False := by
  obtain ⟨-, hKC, hKc⟩ := h.twoComp
  rcases hB with hs | ⟨hq, H, ⟨e⟩⟩
  · exact not_le_of_isSolvable hKC hKc hs hKN
  · have := eq_of_le_of_isQuasisimple hKN hNC hKc hq
    subst this
    exact h.false_of_quat H e

theorem false_of_config_blocks {z : X} {K D : Subgroup X} (h : Config z K D)
    {N₁ N₂ : Subgroup X} (hN₁ : N₁ ≤ centralizer ({z} : Set X))
    (hN₂ : N₂ ≤ centralizer ({z} : Set X))
    (hs₁ : (N₁.subgroupOf (centralizer ({z} : Set X))).IsSubnormal)
    (hs₂ : (N₂.subgroupOf (centralizer ({z} : Set X))).IsSubnormal)
    (hperf : ∀ L : Subgroup X, L ≤ centralizer ({z} : Set X) → ⁅L, L⁆ = L → L ≤ N₁ ⊔ N₂)
    (hB₁ : QuatBlock N₁) (hB₂ : QuatBlock N₂) : False := by
  obtain ⟨-, hKC, hKc⟩ := h.twoComp
  rcases Burgoyne.C.le_or_le_of_le_sup hKC hKc hN₁ hN₂ hs₁ hs₂
      (hperf K hKC (commutator_eq_of_isPComponent hKC hKc)) with hK | hK
  · exact false_of_config_le_block h hN₁ hB₁ hK
  · exact false_of_config_le_block h hN₂ hB₂ hK

theorem false_of_config_layer {z : X} {K D : Subgroup X} (h : Config z K D) {N : Subgroup X}
    (hNC : N ≤ centralizer ({z} : Set X))
    (hperf : ∀ L : Subgroup X, L ≤ centralizer ({z} : Set X) → ⁅L, L⁆ = L → L ≤ N)
    (hB : QuatBlock N) : False := by
  obtain ⟨-, hKC, hKc⟩ := h.twoComp
  exact false_of_config_le_block h hNC hB (hperf K hKC (commutator_eq_of_isPComponent hKC hKc))

omit [Finite X] in
theorem mem_centralizer_of_comm_commutator {F : Subgroup X} (hF : ⁅F, F⁆ = F) {g : X}
    (hgN : g ∈ normalizer (F : Set X))
    (hc : ∀ j ∈ F, ∀ y ∈ F, (j⁻¹ * g⁻¹ * j * g) * y = y * (j⁻¹ * g⁻¹ * j * g)) :
    g ∈ centralizer (F : Set X) := by
  have hmem : ∀ j ∈ F, j⁻¹ * g⁻¹ * j * g ∈ F := by
    intro j hj
    have h1 : g⁻¹ * j * g ∈ F := by
      have := (mem_normalizer_iff.1 (inv_mem hgN) j).1 hj
      simpa using this
    have h2 := mul_mem (inv_mem hj) h1
    simpa [mul_assoc] using h2
  let φ : F →* F :=
    { toFun := fun j => ⟨(j : X)⁻¹ * g⁻¹ * j * g, hmem j j.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => by
        apply Subtype.ext
        change ((a : X) * b)⁻¹ * g⁻¹ * (a * b) * g =
          ((a : X)⁻¹ * g⁻¹ * a * g) * ((b : X)⁻¹ * g⁻¹ * b * g)
        have hcb := hc a a.2 (b : X)⁻¹ (inv_mem b.2)
        calc ((a : X) * b)⁻¹ * g⁻¹ * (a * b) * g =
            (b : X)⁻¹ * ((a : X)⁻¹ * g⁻¹ * a * g) * (g⁻¹ * b * g) := by group
          _ = ((a : X)⁻¹ * g⁻¹ * a * g) * (b : X)⁻¹ * (g⁻¹ * b * g) := by rw [← hcb]
          _ = ((a : X)⁻¹ * g⁻¹ * a * g) * ((b : X)⁻¹ * g⁻¹ * b * g) := by group }
  have hcomm : ⁅F, F⁆ ≤ φ.ker.map F.subtype := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨⁅(⟨a, ha⟩ : F), ⟨b, hb⟩⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    apply Subtype.ext
    exact hc a ha _ (φ ⟨b, hb⟩).2
  rw [mem_centralizer_iff]
  intro j hj
  rw [← hF] at hj
  obtain ⟨y, hy, rfl⟩ := hcomm hj
  have h1 : (y : X)⁻¹ * g⁻¹ * y * g = 1 := congrArg Subtype.val hy
  have h2 : g⁻¹ * y * g = y := by
    calc g⁻¹ * y * g = y * ((y : X)⁻¹ * g⁻¹ * y * g) := by group
      _ = y := by rw [h1, mul_one]
  calc (y : X) * g = g * (g⁻¹ * y * g) := by group
    _ = g * y := by rw [h2]

omit [Finite X] in
theorem coreActionKernel_le_centralizer_of_quasisimple {K : Subgroup X} (hq : IsQuasisimple K)
    (hs : IsSimpleGroup (K ⧸ pPrimeCore 2 K)) : coreActionKernel K ≤ centralizer (K : Set X) := by
  have hO : pPrimeCore 2 K ≤ center K := by
    rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hq
        (Normal.isSubnormal (pPrimeCore_normal (p := 2) (G := K))) with h0 | h0
    · exfalso
      obtain ⟨a, b, hab⟩ := exists_pair_ne (K ⧸ pPrimeCore 2 K)
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
      exact hab (QuotientGroup.eq.2 (h0 ▸ mem_top _))
    · exact h0
  intro g hg
  refine mem_centralizer_of_comm_commutator (Subgroup.isPerfect_iff.1 hq.1) hg.1 ?_
  intro j hj y hy
  obtain ⟨w, hw, hwj⟩ := mem_map.1 (hg.2 j hj)
  have h1 := congrArg Subtype.val (mem_center_iff.1 (hO hw) ⟨y, hy⟩)
  change y * (w : X) = (w : X) * y at h1
  have hwj' : (w : X) = j⁻¹ * g⁻¹ * j * g := hwj
  rw [hwj'] at h1
  exact h1.symm

theorem false_of_config_layer_comm {z : X} {K D : Subgroup X} (h : Config z K D)
    {N : Subgroup X} (hNC : N ≤ centralizer ({z} : Set X))
    (hperf : ∀ L : Subgroup X, L ≤ centralizer ({z} : Set X) → ⁅L, L⁆ = L → L ≤ N)
    (hq : IsQuasisimple N)
    (hab : ∀ x ∈ centralizer (N : Set X), ∀ y ∈ centralizer (N : Set X), x * y = y * x) :
    False := by
  obtain ⟨-, hKC, hKc⟩ := h.twoComp
  have hKN := eq_of_le_of_isQuasisimple (hperf K hKC (commutator_eq_of_isPComponent hKC hKc))
    hNC hKc hq
  subst hKN
  obtain ⟨x, hx, y, hy, hxy⟩ := h.exists_mul_ne
  have hD : ∀ d ∈ D, d ∈ centralizer (K : Set X) := fun d hd =>
    coreActionKernel_le_centralizer_of_quasisimple hq h.simple (mem_inf.mp (h.D_le hd)).2
  exact hxy (hab x (hD x hx) y (hD y hy))

end CFSG.ComponentClassification.CatLeafProof.EndOddLin
