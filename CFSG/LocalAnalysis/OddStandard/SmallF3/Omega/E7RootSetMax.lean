module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.E7RootSetDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IOrd
public import CFSG.Certificates.SuborbitCoatom
public import Certificates.Certificate709545
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.E7RootSetFacts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega.E7RootSet

open Certificates.OmegaSevenMax

section Orbit

variable (hQ : qForm.Nondegenerate)

theorem q_e0 : qV (decV 1) = 1 := by decide

theorem q_ej : ∀ j : Fin 6, qV (decV (3 ^ (j.val + 1))) = 1 := by decide

noncomputable def hEl (j : Fin 6) : omegaGroup hQ :=
  omegaEl hQ (decV 1) (decV (3 ^ (j.val + 1))) q_e0 (q_ej j)

noncomputable def hGrp : Subgroup (omegaGroup hQ) := Subgroup.closure (Set.range (hEl hQ))

theorem hEl_smul (j : Fin 6) (S : Finset V) : hEl hQ j • S = S.image (hV j) := by
  unfold hEl
  rw [omegaEl_smul]
  rfl

theorem hWord_smul : ∀ w : List (Fin 6), ∃ h ∈ hGrp hQ, ∀ S : Finset V, h • S = S.image (hWord w)
  | [] => ⟨1, (hGrp hQ).one_mem, fun S => by rw [one_smul]; exact Finset.image_id.symm⟩
  | j :: w => by
    obtain ⟨h, hh, e⟩ := hWord_smul w
    refine ⟨hEl hQ j * h, (hGrp hQ).mul_mem (Subgroup.subset_closure ⟨j, rfl⟩) hh, fun S => ?_⟩
    rw [mul_smul, e, hEl_smul, Finset.image_image]
    rfl

theorem pairWord_smul : ∀ L : List (V × V), (∀ x ∈ L, qV x.1 = 1 ∧ qV x.2 = 1) →
    ∃ g : omegaGroup hQ, ∀ S : Finset V, g • S = S.image (pairWord L)
  | [], _ => ⟨1, fun S => by rw [one_smul]; exact Finset.image_id.symm⟩
  | x :: L, hL => by
    obtain ⟨g, e⟩ := pairWord_smul L fun y hy => hL y (List.mem_cons_of_mem _ hy)
    have hx := hL x List.mem_cons_self
    refine ⟨omegaEl hQ x.1 x.2 hx.1 hx.2 * g, fun S => ?_⟩
    rw [mul_smul, e, omegaEl_smul, Finset.image_image]
    rfl

theorem hGrp_le (hfix : ∀ j, rootSetV.image (hV j) = rootSetV) :
    hGrp hQ ≤ MulAction.stabilizer (omegaGroup hQ) rootSetV := by
  rw [hGrp, Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  exact MulAction.mem_stabilizer_iff.2 ((hEl_smul hQ j _).trans (hfix j))

theorem isCoatom_of_cert
    (hStab : Nat.card (MulAction.stabilizer (omegaGroup hQ) rootSetV) = 1451520) :
    IsCoatom (MulAction.stabilizer (omegaGroup hQ) rootSetV) := by
  obtain ⟨p, c, r, hinj, hp0, hL, hW, hc0, hsz, hfix⟩ := Certificates.certificate709545
  have hΩ : Nat.card (omegaGroup hQ) = 4585351680 :=
    natCard_omegaGroup_seven hQ (Module.finrank_fin_fun (ZMod 3))
  haveI : Finite (omegaGroup hQ) := Nat.finite_of_card_ne_zero (by rw [hΩ]; norm_num)
  have horb : (MulAction.orbit (omegaGroup hQ) rootSetV).ncard = 3159 := by
    have h1 := MulAction.index_stabilizer (omegaGroup hQ) rootSetV
    have h2 := Subgroup.card_mul_index (MulAction.stabilizer (omegaGroup hQ) rootSetV)
    rw [hStab, hΩ] at h2
    rw [← h1]
    omega
  have hpo : ∀ i, p i ∈ MulAction.orbit (omegaGroup hQ) rootSetV := by
    intro i
    obtain ⟨L, hq, e⟩ := hL i
    obtain ⟨g, hg⟩ := pairWord_smul hQ L hq
    exact ⟨g, (hg _).trans e.symm⟩
  have hS : Set.range p = MulAction.orbit (omegaGroup hQ) rootSetV := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
    · rintro _ ⟨i, rfl⟩
      exact hpo i
    · rw [horb, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]
  let blk : Fin 4 → Set (Finset V) := fun d => p '' {i | c i = d}
  have hsz' : ∀ d, (blk d).ncard = ![1, 288, 630, 2240] d := by
    intro d
    have e : {i | c i = d} = ↑(Finset.univ.filter (c · = d)) := by
      ext i
      simp
    change (p '' {i | c i = d}).ncard = _
    rw [Set.ncard_image_of_injective _ hinj, e, Set.ncard_coe_finset, hsz]
  have hB0 : blk 0 = {rootSetV} := by
    ext X
    simp only [blk, Set.mem_image, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      rw [(hc0 i).1 hi, hp0]
    · rintro rfl
      exact ⟨0, (hc0 0).2 rfl, hp0⟩
  have hBorb : ∀ d, blk d ⊆ MulAction.orbit (omegaGroup hQ) rootSetV := by
    rintro d _ ⟨i, -, rfl⟩
    exact hpo i
  have hcover : ∀ y ∈ MulAction.orbit (omegaGroup hQ) rootSetV, ∃ d, y ∈ blk d := by
    intro y hy
    rw [← hS] at hy
    obtain ⟨i, rfl⟩ := hy
    exact ⟨c i, i, rfl, rfl⟩
  have hdisj : ∀ d e, d ≠ e → Disjoint (blk d) (blk e) := by
    intro d e hde
    rw [Set.disjoint_left]
    rintro X ⟨i, hi, rfl⟩ ⟨k, hk, hik⟩
    have := hinj hik
    subst this
    exact hde (hi.symm.trans hk)
  have htrans : ∀ d, ∀ y ∈ blk d, ∀ z ∈ blk d, ∃ h ∈ hGrp hQ, h • y = z := by
    rintro d y ⟨i, hi, rfl⟩ z ⟨k, hk, rfl⟩
    obtain ⟨wi, ei⟩ := hW i
    obtain ⟨wk, ek⟩ := hW k
    obtain ⟨hI, hhI, eI⟩ := hWord_smul hQ wi
    obtain ⟨hK, hhK, eK⟩ := hWord_smul hQ wk
    have hcc : c i = c k := hi.trans hk.symm
    refine ⟨hK * hI⁻¹, (hGrp hQ).mul_mem hhK ((hGrp hQ).inv_mem hhI), ?_⟩
    rw [ei, ek, ← eI, ← eK, hcc, mul_smul, inv_smul_smul]
  have hprim : ∀ T : Finset (Fin 4), (0 : Fin 4) ∈ T →
      (∑ d ∈ T, (blk d).ncard) ∣ ∑ d : Fin 4, (blk d).ncard → T = {0} ∨ T = Finset.univ := by
    intro T h0 hdvd
    simp only [hsz'] at hdvd
    revert T
    decide
  have hnt : ∃ d : Fin 4, d ≠ 0 ∧ (blk d).Nonempty := by
    refine ⟨1, by decide, ?_⟩
    rw [← Set.ncard_pos (Set.toFinite _), hsz']
    decide
  exact CFSG.Certificates.isCoatom_stabilizer_of_suborbits rootSetV (hGrp hQ) (hGrp_le hQ hfix)
    (k := 3) blk hB0 hBorb hcover hdisj htrans hprim hnt

end Orbit

@[expose] def rootSet : Finset V := rootSetOf (tables ())

theorem rootSet_eq : rootSet = rootSetV := rfl

theorem isCoatom_stabilizer_rootSet (hQ : qForm.Nondegenerate)
    (hStab : Nat.card (MulAction.stabilizer (omegaGroup hQ) rootSet) = 1451520) :
    IsCoatom (MulAction.stabilizer (omegaGroup hQ) rootSet) := by
  rw [rootSet_eq] at hStab ⊢
  exact isCoatom_of_cert hQ hStab

end CFSG.OddStandard.SmallF3.Omega.E7RootSet

end
