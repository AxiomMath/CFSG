module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalViso
public import Certificates.Certificate9540
import CFSG.Alternating.Multipliers.Carmichael

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp62Local

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two

theorem sp62_escape_check :
    chkAlt = true ∧ relAlt = true ∧ commAlt = true ∧ outW = true :=
  Certificates.certificate9540

@[expose] def Alt0 : Subgroup H6 := Hgen gensAlt

theorem tabCheck_Alt :
    tabCheck gensAlt 360 (fun _ => true) = true :=
  sp62_escape_check.1

theorem card_Alt0 : Nat.card Alt0 = 360 :=
  (tabCheck_spec tabCheck_Alt).2.2.1

theorem genB_gensAlt : ∀ c ∈ gensAlt, genB c = true :=
  (tabCheck_spec tabCheck_Alt).2.2.2.2

theorem elt_cAlt0_mem_Alt0 : elt cAlt0 ∈ Alt0 :=
  elt_mem_Hgen (gens := gensAlt) (c := cAlt0) (by simp [gensAlt])

theorem w0_mem_B0 : elt cW0 ∈ B0 := elt_mem_Hgen (c := cW0) (by simp [gensB])

theorem orderOf_w0 : orderOf (elt cW0) = 3 :=
  orderOf_eq_prime (pow_three_elt (g := cW0) (by simp)) fun h =>
    absurd ((rep_elt (genB_isoB genB_cW0)).eq_one_iff.1 h) (by decide)

theorem Alt0_le_centralizer :
    Alt0 ≤ Subgroup.centralizer ({elt cW0} : Set H6) := by
  intro h hh
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hcomm : ∀ c ∈ gensAlt, commB cW0 c = true := by
    have := sp62_escape_check.2.2.1
    simpa [commAlt] using this
  exact (comm_Hgen_of_gens (rep_elt (genB_isoB genB_cW0)) genB_gensAlt hcomm h hh).symm

theorem elt_cAlt0_not_mem_W0 :
    elt cAlt0 ∉ W0 := by
  intro h
  obtain ⟨t, ht, hrep⟩ := Hgen_rep tabCheck_WD h
  have hgen : genB cAlt0 = true := genB_gensAlt _ (by simp [gensAlt])
  have htc : t = cAlt0 := (hrep.eq_iff (rep_elt (genB_isoB hgen))).1 rfl
  have hout := sp62_escape_check.2.2.2
  simp only [outW, Bool.not_eq_true'] at hout
  rw [htc] at ht
  have := inTab_iff.2 ht
  rw [hout] at this
  exact Bool.false_ne_true this

theorem card_alternatingGroup_fin_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  have h2 := two_mul_nat_card_alternatingGroup (α := Fin 6)
  simp only [Nat.card_perm, Nat.card_fin] at h2
  have h6 : Nat.factorial 6 = 720 := by decide
  omega

theorem nonempty_Alt0_mulEquiv :
    Nonempty (Alt0 ≃* alternatingGroup (Fin 6)) := by
  have hrel := sp62_escape_check.2.1
  simp only [relAlt, List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at hrel
  let code : Fin 4 → List ℕ := fun i => gensAlt.getD i []
  have hmem : ∀ i, code i ∈ gensAlt := fun i => by fin_cases i <;> simp [code, gensAlt]
  have hgen : ∀ i, genB (code i) = true := fun i => genB_gensAlt _ (hmem i)
  let e : Fin 4 → Alt0 := fun i => ⟨elt (code i), elt_mem_Hgen (hmem i)⟩
  have h3 : ∀ i, e i ^ 3 = 1 := by
    intro i
    refine Subtype.ext ?_
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    exact (rep_elt (genB_isoB (hgen i))).pow_three.2 (beq_iff_eq.1 (hrel i i.2).1)
  have h2 : ∀ i j, i ≠ j → (e i * e j) ^ 2 = 1 := by
    intro i j hij
    refine Subtype.ext ?_
    have hsq := ((hrel i i.2).2 j j.2).resolve_left fun h => hij (Fin.ext h)
    have hr := (rep_elt (genB_isoB (hgen i))).mul (rep_elt (genB_isoB (hgen j)))
    simp only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_one]
    rw [sq]
    exact (hr.mul hr).eq_one_iff.2 (beq_iff_eq.1 hsq)
  have hrange : Set.range e = ((↑) : Alt0 → H6) ⁻¹' genSet gensAlt := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨code i, hmem i, rfl⟩
    · rintro ⟨c, hc, hvc⟩
      obtain ⟨i, hi⟩ : ∃ i : Fin 4, code i = c := by
        simp only [gensAlt, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl
        exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]
      exact ⟨i, Subtype.ext (by rw [hvc, ← hi])⟩
  have hcl : Subgroup.closure (Set.range e) = ⊤ := by
    rw [hrange]
    exact Subgroup.closure_closure_coe_preimage
  obtain ⟨φ⟩ := nonempty_mulEquiv_of_isPresentation
    (CFSG.Alternating.Multipliers.isPresentation_carmichael 4)
    (CFSG.Alternating.Multipliers.lift_carmichaelWords_eq_one h3 h2) hcl
    (by rw [card_Alt0, card_alternatingGroup_fin_six])
  exact ⟨φ.symm⟩

end CFSG.AGLEmbedding.KFactProofs.Sp62Local
