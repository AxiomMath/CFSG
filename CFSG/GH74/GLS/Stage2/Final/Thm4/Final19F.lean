module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.Final19E
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Core
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Final19D

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section GLevel

variable {G : Type} [Group G] [Finite G]

theorem isCyclic_of_not_two_le_pRank {Γ : Type} [Group Γ] [Finite Γ] (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hΓ : IsPGroup p Γ) (h : ¬ 2 ≤ pRank p Γ) : IsCyclic Γ := by
  by_contra hnc
  have : Fact (IsPGroup p Γ) := ⟨hΓ⟩
  obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a hp2 hnc
  apply h
  have hE : CFSG.Open.IsElemAbelian p S := (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p S).mp hSel
  have h2 := CFSG.SectionRank.le_pRank hp.out.one_lt (le_top : S ≤ ⊤) hE hScard
  rwa [← CFSG.SectionRank.pRank_eq_open_pRank_top] at h2

omit [Finite G] in
theorem Op_normalized (r : ℕ) (M : Subgroup G) {m : G} (hm : m ∈ M) {x : G} (hx : x ∈ Op r M) :
    m * x * m⁻¹ ∈ Op r M := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨(⟨m, hm⟩ : ↥M) * y * (⟨m, hm⟩ : ↥M)⁻¹, (inferInstance : (pCore r ↥M).Normal).conj_mem y hy _, rfl⟩

omit [Finite G] in
theorem pCore_map_subtype_map (p : ℕ) (M : Subgroup G) (R : Subgroup ↥M) :
    (pCore p ↥(R.map M.subtype)).map (R.map M.subtype).subtype =
      ((pCore p ↥R).map R.subtype).map M.subtype := by
  let e : ↥R ≃* ↥(R.map M.subtype) := R.equivMapOfInjective M.subtype M.subtype_injective
  have h1 := CFSG.pCore_map_iso p e
  rw [← h1, Subgroup.map_map, Subgroup.map_map]
  congr 1

omit [Finite G] in
theorem Op_Fm_le_Op (r : ℕ) [Fact r.Prime] (M : Subgroup G) : Op r (Fm M) ≤ Op r M := by
  have h := pCore_map_subtype_map r M (fittingSubgroup ↥M)
  change (pCore r ↥((fittingSubgroup ↥M).map M.subtype)).map
    ((fittingSubgroup ↥M).map M.subtype).subtype ≤ _
  rw [h]
  refine Subgroup.map_mono ?_
  exact le_sSup ⟨inferInstance, (pCore_isPGroup (G := ↥(fittingSubgroup ↥M)) (p := r)).map _⟩

omit [Finite G] in
theorem Qof_normalized {p : ℕ} (M U : Subgroup G) (hQ : ((Qof p M U).subgroupOf (Op p M)).Characteristic)
    {m : G} (hm : m ∈ M) {x : G} (hx : x ∈ Qof p M U) : m * x * m⁻¹ ∈ Qof p M U := by
  have hxP : x ∈ Op p M := hx.1
  let φ : MulAut ↥(Op p M) :=
    { toFun := fun y => ⟨m * y * m⁻¹, Op_normalized p M hm y.2⟩
      invFun := fun y => ⟨m⁻¹ * y * m, by simpa using Op_normalized p M (M.inv_mem hm) y.2⟩
      left_inv := fun y => Subtype.ext (by simp [mul_assoc])
      right_inv := fun y => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have h1 := Subgroup.characteristic_iff_comap_eq.mp hQ φ
  have hx' : (⟨x, hxP⟩ : ↥(Op p M)) ∈ (Qof p M U).subgroupOf (Op p M) := hx
  have hx'' : (⟨x, hxP⟩ : ↥(Op p M)) ∈ ((Qof p M U).subgroupOf (Op p M)).comap φ.toMonoidHom := by
    rw [h1]
    exact hx'
  exact Subgroup.mem_comap.mp hx''

theorem lemma19_5_of_19_3_19_4 (h193 : Lemma19_3) (h194 : Lemma19_4) : Lemma19_5 := by
  intro G _ _ z k S M p U t hctx
  have hp : p.Prime := hctx.base.prime
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := hctx.base.odd
  have hctx17 : Ctx17 G z k S M := hctx.base.base.ctx
  have htM : t ∈ M := hctx17.S_le hctx.t_mem
  have ht2 : t ^ 2 = 1 := by
    have hz2 : z ^ 2 = 1 := by
      have := hctx17.ctx.central.1
      rw [← this]
      exact pow_orderOf_eq_one z
    obtain ⟨c, hc⟩ := isConj_iff.mp hctx.t_conj
    rw [← hc, conj_pow, hz2]
    group
  obtain ⟨hQinv, hRinv⟩ := h193 G z k S M p U t hctx
  have hQchar := h194 G z k S M p U t hctx
  have hpg : IsPGroup p ↥(Op p M) := (pCore_isPGroup (G := ↥M) (p := p)).map M.subtype
  have hUcomm : IsMulCommutative ↥U := hctx.U_elem.toIsMulCommutative
  have hstab := stab_chain_centralizes (p := p) (M := M) (P := Op p M) (Q := Qof p M U) (U := U) htM ht2
    (fun m hm x hx => Op_normalized p M hm hx)
    (fun x hx => by
      obtain ⟨e, he⟩ := hpg ⟨x, hx⟩
      exact ⟨e, by simpa using congrArg Subtype.val he⟩)
    (fun m hm x hx => Qof_normalized M U hQchar hm hx)
    inf_le_left hctx.U_le
    (fun x hx u hu => hctx.U_normal.conj_mem ⟨u, hctx.U_le hu⟩ hu ⟨x, hx⟩)
    (fun u hu v hv => congrArg Subtype.val (mul_comm' (⟨u, hu⟩ : ↥U) ⟨v, hv⟩))
    (fun x hx h => ⟨hx, Subgroup.mem_centralizer_iff.mpr fun u hu => (h u hu).symm⟩) hQinv
  show (oResidual p ↥⁅M, Subgroup.zpowers t⁆).map ⁅M, Subgroup.zpowers t⁆.subtype ≤ _
  rw [Subgroup.map_le_iff_le_comap, oResidual, Subgroup.closure_le]
  intro a ha
  have hacop : Nat.Coprime (orderOf (a : G)) p := by
    rw [Subgroup.orderOf_coe]
    exact ha
  have haA : (a : G) ∈ ⁅M, Subgroup.zpowers t⁆ := a.2
  have hAM : ⁅M, Subgroup.zpowers t⁆ ≤ ⁅M, M⁆ := Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr htM)
  have hFle : Fpi {r | r.Prime ∧ r ≠ 2} M ≤ Subgroup.centralizer ({(a : G)} : Set G) := by
    refine iSup₂_le fun r hr => ?_
    have : Fact r.Prime := ⟨hr.1⟩
    intro x hx
    have hxO : x ∈ Op r M := Op_Fm_le_Op r M hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    by_cases hrp : r = p
    · subst hrp
      exact (hstab a haA hacop x hxO).symm
    · by_cases hrk : 2 ≤ pRank r ↥(Op r M)
      · have hinv := hRinv r hr.1 hr.2 hrp hrk
        have hc := commutator_zpowers_le_centralizer_of_inv htM ht2
          (fun m hm y hy => Op_normalized r M hm hy) hinv haA
        exact Subgroup.mem_centralizer_iff.mp hc x hxO
      · have hrpg : IsPGroup r ↥(Op r M) := (pCore_isPGroup (G := ↥M) (p := r)).map M.subtype
        have hcyc := isCyclic_of_not_two_le_pRank r hr.2 hrpg hrk
        have hc := commutator_le_centralizer_of_cyclic (fun m hm y hy => Op_normalized r M hm hy) hcyc
          (hAM haA)
        exact Subgroup.mem_centralizer_iff.mp hc x hxO
  show (a : G) ∈ Subgroup.centralizer ((Fpi {r | r.Prime ∧ r ≠ 2} M : Subgroup G) : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  exact Subgroup.mem_centralizer_singleton_iff.mp (hFle hf)

theorem prop19_1_of_19_2_to_19_4 (h26 : Leaf_Lemma26) (h192 : Lemma19_2) (h193 : Lemma19_3)
    (h194 : Lemma19_4) : Prop19_1 :=
  prop19_1_of_lemmas h26 h192 (lemma19_5_of_19_3_19_4 h193 h194)

theorem thm4_of_19_2_to_19_4 (h34 : Leaf_Prop34) (h26 : Leaf_Lemma26) (h192 : Lemma19_2) (h193 : Lemma19_3)
    (h194 : Lemma19_4) (hP : PSp4_oddCover) : Ch4Thm4 :=
  thm4 h34 (prop19_1_of_19_2_to_19_4 h26 h192 h193 h194) hP

end GLevel

end CFSG.GH74.GLS.Stage2.Final.Thm4
