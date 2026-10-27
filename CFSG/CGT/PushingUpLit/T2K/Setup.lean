module

public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.CGT.PushingUpLit.BlocksCommuteDefs
public import CFSG.CGT.PushingUpLit.SixThreeShort
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG CFSG.RankThree.PartOne
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

abbrev Fq (n : ℕ) : Type := GaloisField 2 n

structure NatBlock (L : Subgroup G) (n : ℕ) : Prop where
  short : IsShortGroup ↥L
  nat : IsNaturalSLTwoModule ↥L n
  two_le : 2 ≤ n

namespace NatBlock

variable {L : Subgroup G} {n : ℕ}

theorem exists_four (hn : 2 ≤ n) : ∃ s : Finset (GaloisField 2 n), s.card = 4 := by
  let _ : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 2 n (by omega)
  have h2 : 4 ≤ Fintype.card (GaloisField 2 n) := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (GaloisField 2 n))) (n := 4) (by simpa using h2)
  exact ⟨t, ht⟩

theorem perfect (h : NatBlock L n) : ⁅L, L⁆ = L := by
  classical
  obtain ⟨φ, -⟩ := h.nat
  refine le_antisymm (Subgroup.le_normalizer_iff_commutator_le_right.1
    (Subgroup.le_normalizer (H := L))) ?_
  refine noTwoQuot_of_short h.short ⁅L, L⁆ ?_ ?_
  · intro g hg m hm
    exact (Subgroup.mem_normalizer_iff.1 (Subgroup.normalizer_commutator_ge_left L L hg) m).1 hm
  · intro g hg
    set C : Subgroup ↥L := commutator ↥L with hC
    let φ' : ↥L →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
      (φ : (↥L ⧸ pCore 2 ↥L) →* _).comp (QuotientGroup.mk' (pCore 2 ↥L))
    have hφs : Function.Surjective φ' := φ.surjective.comp (QuotientGroup.mk'_surjective _)
    have hφk : φ'.ker = pCore 2 ↥L := by
      ext x
      rw [MonoidHom.mem_ker]
      show φ (QuotientGroup.mk x) = 1 ↔ x ∈ pCore 2 ↥L
      rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
    have hSL : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
      CFSG.LinearGroups.special_linear_isPerfect (K := GaloisField 2 n) (n := 2) le_rfl
        (Or.inr (exists_four h.two_le))
    have hCm : C.map φ' = ⊤ := by
      rw [hC, commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ hφs]
      exact Group.IsPerfect.commutator_eq_top
    have h1 : φ' ⟨g, hg⟩ ∈ C.map φ' := hCm ▸ Subgroup.mem_top _
    obtain ⟨c, hc, hce⟩ := h1
    have h2 : c⁻¹ * ⟨g, hg⟩ ∈ pCore 2 ↥L := by
      rw [← hφk, MonoidHom.mem_ker, map_mul, map_inv, hce, inv_mul_cancel]
    obtain ⟨j, hj⟩ := (pCore_isPGroup (p := 2) (G := ↥L)) ⟨c⁻¹ * ⟨g, hg⟩, h2⟩
    refine ⟨j, ?_⟩
    have hj' : (c⁻¹ * ⟨g, hg⟩ : ↥L) ^ 2 ^ j = 1 := congrArg Subtype.val hj
    have hmk : (QuotientGroup.mk (⟨g, hg⟩ : ↥L) : ↥L ⧸ C) = QuotientGroup.mk (c⁻¹ * ⟨g, hg⟩) := by
      rw [QuotientGroup.eq]
      have : (⟨g, hg⟩ : ↥L)⁻¹ * (c⁻¹ * ⟨g, hg⟩) ∈ C := by
        have := (inferInstance : C.Normal).conj_mem c⁻¹ (C.inv_mem hc) (⟨g, hg⟩ : ↥L)⁻¹
        simpa [mul_assoc] using this
      exact this
    have h3 : (QuotientGroup.mk ((⟨g, hg⟩ : ↥L) ^ 2 ^ j) : ↥L ⧸ C) = 1 := by
      rw [QuotientGroup.mk_pow, hmk, ← QuotientGroup.mk_pow, hj']
      rfl
    have h4 : ((⟨g, hg⟩ : ↥L) ^ 2 ^ j) ∈ C := (QuotientGroup.eq_one_iff _).1 h3
    have h5 : g ^ 2 ^ j ∈ C.map L.subtype := ⟨_, h4, rfl⟩
    rwa [hC, commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
      at h5

theorem blockU_eq (h : NatBlock L n) : ⁅blockU L, L⁆ = blockU L :=
  SixThree.commutator_commutator_eq (SubTwo.noTwoQuotient_of_oResidualTwo h.short.residual_eq)
    (SixThree.isPGroup_oTwoIn L) (SixThree.le_normalizer_oTwoIn L)

end NatBlock

structure NatData (L : Subgroup G) (n : ℕ) where
  φ : ↥L →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)
  ψ : ↥(blockU L) →* Multiplicative (Fin 2 → GaloisField 2 n)
  φ_surj : Function.Surjective φ
  φ_ker : ∀ l : ↥L, φ l = 1 ↔ (l : G) ∈ oTwoIn L
  ψ_surj : Function.Surjective ψ
  ψ_ker : ∀ v : ↥(blockU L), ψ v = 1 ↔ (v : G) ∈ blockZ L
  ψ_conj : ∀ (l : ↥L) (v : ↥(blockU L)) (hv : (l : G) * v * (l : G)⁻¹ ∈ blockU L),
    ψ ⟨(l : G) * v * (l : G)⁻¹, hv⟩ = Multiplicative.ofAdd
      (((φ l : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec (Multiplicative.toAdd (ψ v)))

namespace NatBlock

variable {L : Subgroup G} {n : ℕ}

theorem nonempty_natData (h : NatBlock L n) : Nonempty (NatData L n) := by
  obtain ⟨φ, ψ, hψs, hψk, hψe⟩ := h.nat
  let eU : ↥(shortU ↥L) ≃* ↥(blockU L) :=
    (Subgroup.equivMapOfInjective (shortU ↥L) L.subtype L.subtype_injective).trans
      (MulEquiv.subgroupCongr (map_shortU_subtype L))
  have heU : ∀ u : ↥(shortU ↥L), ((eU u : ↥(blockU L)) : G) = ((u : ↥L) : G) := fun u => rfl
  let φ' : ↥L →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
    (φ : (↥L ⧸ pCore 2 ↥L) →* _).comp (QuotientGroup.mk' (pCore 2 ↥L))
  refine ⟨⟨φ', ψ.comp eU.symm.toMonoidHom, φ.surjective.comp (QuotientGroup.mk'_surjective _), ?_,
    hψs.comp eU.symm.surjective, ?_, ?_⟩⟩
  · intro l
    show φ (QuotientGroup.mk l) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, oTwoIn_eq_map]
    exact (Subgroup.mem_map_iff_mem L.subtype_injective).symm
  · intro v
    have hv : (((eU.symm v : ↥(shortU ↥L)) : ↥L) : G) = (v : G) := by
      have := heU (eU.symm v)
      rw [MulEquiv.apply_symm_apply] at this
      exact this.symm
    show ψ (eU.symm v) = 1 ↔ _
    rw [← MonoidHom.mem_ker, hψk, Subgroup.mem_subgroupOf, ← hv]
    constructor
    · intro hc
      rw [← map_shortC_subtype]
      exact Subgroup.mem_map_of_mem _ hc
    · intro hc
      rw [← map_shortC_subtype] at hc
      obtain ⟨c, hc', hcv⟩ := hc
      have : c = ((eU.symm v : ↥(shortU ↥L)) : ↥L) := Subtype.ext hcv
      rwa [← this]
  · intro l v hv
    set u : ↥(shortU ↥L) := eU.symm v with hu
    have hu1 : ((u : ↥L) : G) = (v : G) := by
      have := heU u
      rw [hu, MulEquiv.apply_symm_apply] at this
      exact this.symm
    have hu' : l * (u : ↥L) * l⁻¹ ∈ shortU ↥L := by
      rw [← Subgroup.mem_map_iff_mem L.subtype_injective, map_shortU_subtype]
      show ((l * (u : ↥L) * l⁻¹ : ↥L) : G) ∈ blockU L
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hu1]
      exact hv
    have hsub : eU.symm ⟨(l : G) * v * (l : G)⁻¹, hv⟩ = ⟨l * (u : ↥L) * l⁻¹, hu'⟩ := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      show ((l : G) * v * (l : G)⁻¹) = ((l * (u : ↥L) * l⁻¹ : ↥L) : G)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hu1]
    have key := hψe l u u.2 hu'
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [hsub, key]
    rfl

noncomputable def natData (h : NatBlock L n) : NatData L n := h.nonempty_natData.some

end NatBlock

namespace NatData

variable {L : Subgroup G} {n : ℕ}

theorem eq_one_of_forall_mulVec {F : Type} [Field F]
    {g : Matrix.SpecialLinearGroup (Fin 2) F}
    (h : ∀ v : Fin 2 → F, (g : Matrix (Fin 2) (Fin 2) F).mulVec v = v) : g = 1 := by
  apply Subtype.ext
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using this

omit [Finite G] in
theorem mem_oTwoIn_of_centralizes (D : NatData L n) {l : G} (hl : l ∈ L)
    (h : ∀ v ∈ blockU L, l * v * l⁻¹ = v) :
    l ∈ oTwoIn L := by
  have h1 : D.φ ⟨l, hl⟩ = 1 := by
    apply eq_one_of_forall_mulVec
    intro w
    obtain ⟨v, hv⟩ := D.ψ_surj (Multiplicative.ofAdd w)
    have hlv : l * (v : G) * l⁻¹ ∈ blockU L := conj_mem_blockU (Subgroup.le_normalizer hl) v.2
    have key := D.ψ_conj ⟨l, hl⟩ v hlv
    have e : (⟨l * (v : G) * l⁻¹, hlv⟩ : ↥(blockU L)) = v := Subtype.ext (h v v.2)
    rw [e, hv] at key
    have := congrArg Multiplicative.toAdd key
    simpa using this.symm
  exact (D.φ_ker ⟨l, hl⟩).1 h1

end NatData

namespace NatBlock

variable {L : Subgroup G} {n : ℕ}

theorem inf_centralizer_blockU (h : NatBlock L n) :
    L ⊓ Subgroup.centralizer (blockU L : Set G) = oTwoIn L := by
  apply le_antisymm
  · intro l hl
    refine NatData.mem_oTwoIn_of_centralizes h.natData hl.1 fun v hv => ?_
    have := Subgroup.mem_centralizer_iff.1 hl.2 v hv
    rw [← this, mul_inv_cancel_right]
  · intro r hr
    refine Subgroup.mem_inf.2 ⟨oTwoIn_le L hr, Subgroup.mem_centralizer_iff.2 fun v hv => ?_⟩
    exact blockU_comm_of_short h.short v hv r hr

theorem blockU_comm (h : NatBlock L n) : ∀ a ∈ blockU L, ∀ b ∈ blockU L, a * b = b * a :=
  fun a ha b hb => blockU_comm_of_short h.short a ha b (blockU_le_oTwoIn L hb)

omit [Finite G] in
theorem blockZ_le_centralizer (L : Subgroup G) :
    blockZ L ≤ Subgroup.centralizer (L : Set G) := inf_le_right

theorem sq_mem_blockZ (h : NatBlock L n) {u : G} (hu : u ∈ blockU L) : u ^ 2 ∈ blockZ L := by
  have hu2 : u ^ 2 ∈ blockU L := (blockU L).pow_mem hu 2
  refine Subgroup.mem_inf.2 ⟨hu2, ?_⟩
  have hker := (h.natData.ψ_ker ⟨u ^ 2, hu2⟩).1
  have e : (⟨u ^ 2, hu2⟩ : ↥(blockU L)) = (⟨u, hu⟩ : ↥(blockU L)) ^ 2 := rfl
  have h1 : h.natData.ψ ⟨u ^ 2, hu2⟩ = 1 := by
    have hadd : ∀ w : Fin 2 → Fq n, w + w = 0 := fun w => by
      funext j
      exact CharTwo.add_self_eq_zero (w j)
    rw [e, map_pow]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, two_nsmul]
    exact hadd _
  exact (hker h1).2

theorem sq_eq_one_of_mem_blockU (h : NatBlock L n) {v : G} (hv : v ∈ blockU L) : v ^ 2 = 1 := by
  have hcomm := h.blockU_comm
  let E : Subgroup G :=
    { carrier := {u | u ∈ blockU L ∧ u ^ 2 = 1}
      one_mem' := ⟨one_mem _, one_pow 2⟩
      mul_mem' := by
        rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
        refine ⟨mul_mem ha hb, ?_⟩
        rw [(Commute.mul_pow (hcomm a ha b hb) 2), ha2, hb2, one_mul]
      inv_mem' := by
        rintro a ⟨ha, ha2⟩
        refine ⟨inv_mem ha, ?_⟩
        rw [inv_pow, ha2, inv_one] }
  have hle : ⁅blockU L, L⁆ ≤ E := by
    refine Subgroup.commutator_le.2 fun u hu l hl => ?_
    have hlN : l ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hl
    have hb : l * u⁻¹ * l⁻¹ ∈ blockU L := conj_mem_blockU hlN (inv_mem hu)
    have hcom : Commute u (l * u⁻¹ * l⁻¹) := hcomm u hu _ hb
    have hz : l * u ^ 2 * l⁻¹ = u ^ 2 := by
      have := Subgroup.mem_centralizer_iff.1 (blockZ_le_centralizer L (h.sq_mem_blockZ hu)) l hl
      rw [this, mul_inv_cancel_right]
    have hmem : ⁅u, l⁆ = u * (l * u⁻¹ * l⁻¹) := by simp [commutatorElement_def, mul_assoc]
    refine ⟨?_, ?_⟩
    · rw [hmem]
      exact mul_mem hu hb
    · show ⁅u, l⁆ ^ 2 = 1
      rw [hmem, hcom.mul_pow, conj_pow, inv_pow]
      have : l * (u ^ 2)⁻¹ * l⁻¹ = (u ^ 2)⁻¹ := by
        have h1 : l * (u ^ 2)⁻¹ * l⁻¹ = (l * u ^ 2 * l⁻¹)⁻¹ := by group
        rw [h1, hz]
      rw [this]
      simp
  rw [← h.blockU_eq] at hv
  exact (hle hv).2

theorem isElemAbelian_blockU (h : NatBlock L n) : CFSG.Open.IsElemAbelian 2 (blockU L) :=
  ⟨⟨⟨fun a b => Subtype.ext (h.blockU_comm a a.2 b b.2)⟩⟩, fun _ hv => h.sq_eq_one_of_mem_blockU hv⟩

end NatBlock

end CFSG.CGT.PushingUpLit.T2K
