module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step211NatSq
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step211NatMod

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard Hexa
open CFSG.CharacterTheory.SteinbergBY.AlternatingSix (totalPerm)
open scoped IsMulCommutative commutatorElement

theorem step211Natural_of
    (h11 : Step11) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h22iv : Step22iv) :
    Step211Natural := by
  intro G _ _ A R g E F hS
  have hF := hS.frame
  have hL := hS.type
  have hodd := hS.odd
  have hSc := sec2S_comm h11 hE16 hF hL hodd
  have h4 : 4 ^ 4 ≤ Nat.card (conjClosure (E ⊓ A) (sec2P F)) :=
    h22iv G A R g F E ⟨hF.symm, hL, hodd, hS.below⟩
  obtain ⟨x, hx, hxC⟩ := exists_mem_sec2P_not_mem_centralizerMod h11 hE16 hF.symm hL hodd
  have hxS : x ∉ sec2S A R E F := fun hS' => hxC (by
    rw [← sec2S_inf_sec2P h11 hE16 hF.symm hL hodd, hSc]
    exact ⟨hS', hx⟩)
  obtain ⟨rep, e, ψ, hc⟩ := exists_sec2HexaCoord h11 hE16 hF hL hodd hx hxS h4
  have : IsMulCommutative ↥(E ⊓ A) := isMulCommutative_inf hF
  have hsqm := sq_rep_mem h11 hE16 hF hL hodd hx hxS h4 e hc
  have hcmm := commutator_rep_mem h11 hE16 hF hL hodd hx hxS h4 e hc
  have hQ : IsQuadMap (sqE rep hsqm) (cmE rep hcmm) :=
    isQuadMap_sqE h11 hE16 hF hL hodd hx hxS h4 e hc
  set q := sqE rep hsqm with hq
  have hov : ∀ o : Fin 64, (∃ i : Fin 6, o.val ∈ hexaOval[(i : ℕ)]!) → q o = 1 := fun o ho =>
    sqE_eq_one_of_mem_oval h11 hE16 hF hL hodd hx hxS h4 e hc ho
  have hqω : ∀ v : Fin 64, q (omegaF v) = q v :=
    sqE_omegaF h11 hE16 hF hL hodd hx hxS h4 e hc
  have hsq : ∀ m : ↥(E ⊓ A), m * m = 1 := hQ.sq
  set t : Fin 6 → Fin 6 → ↥(E ⊓ A) := fun a b => q (rep2 a b) with ht
  have hsymm : ∀ a b, t a b = t b a := fun a b => by
    simp only [ht]
    rw [rep2_comm]
  have htri : ∀ j j' : Fin 6, j ≠ 0 → j' ≠ 0 → j ≠ j' → t 0 j * t 0 j' * t j j' = 1 :=
    fun j j' hj hj' hjj' => quad_rel hQ hov hj hj' hjj'
  have hone : ∏ s : Fin 5, t 0 s.succ = 1 := by
    rw [Fin.prod_univ_five]
    exact quad_rel_one hQ hov
  have hqmem : ∀ u : Fin 64, ∃ v : Fin 6 → ZMod 2, natTheta t v = q u := fun u => by
    rcases mem_or_exists_rep2 u with ⟨i, hi, hu⟩ | ⟨j, j', hjj', hu⟩
    · exact ⟨0, by rw [natTheta_zero, hov u ⟨⟨i, hi⟩, hu⟩]⟩
    · refine ⟨pairVec j j', ?_⟩
      rw [natTheta_pairVec hsq hsymm htri hjj']
      rcases hu with rfl | rfl | rfl
      · rfl
      · exact (hqω _).symm
      · rw [hqω, hqω]
  have hsurj : ∀ m : ↥(E ⊓ A), ∃ v, natTheta t v = m := by
    set H := (natThetaHom hsq t).range with hH
    have hqH : ∀ u : Fin 64, q u ∈ H := fun u => by
      obtain ⟨v, hv⟩ := hqmem u
      exact ⟨Multiplicative.ofAdd v, hv⟩
    have hPC := sec2P_le_centralizer_inf h11 hE16 hF hL hodd
    have hle : ⁅sec2P E, sec2P E⁆ ≤ H.map (E ⊓ A).subtype := by
      rw [Subgroup.commutator_le]
      intro p hp p' hp'
      obtain ⟨v, hv⟩ := hc.surj p hp
      obtain ⟨v', hv'⟩ := hc.surj p' hp'
      have hpe : p = rep v * (p⁻¹ * rep v)⁻¹ := by group
      have hpe' : p' = rep v' * (p'⁻¹ * rep v')⁻¹ := by group
      have hcomm : ⁅p, p'⁆ = ⁅rep v, rep v'⁆ := by
        rw [hpe, hpe', commutatorElement_def, commutatorElement_def]
        exact commutator_mul_mul_eq
          (mem_centralizer_iff.mp (hPC (hc.mem v')) _ (inv_mem hv))
          (mem_centralizer_iff.mp (hPC (hc.mem v)) _ (inv_mem hv'))
          (mem_centralizer_iff.mp (hPC ((inf_le_left.trans (le_sec2P_of_frame hF))
            (inv_mem hv'))) _ (inv_mem hv))
      have hcm : cmE rep hcmm v' v = (q v' * q v)⁻¹ * q (xorF v' v) :=
        eq_inv_mul_of_mul_eq (hQ.q_xor v' v).symm
      refine ⟨cmE rep hcmm v' v, ?_, ?_⟩
      · rw [hcm]
        exact mul_mem (inv_mem (mul_mem (hqH _) (hqH _))) (hqH _)
      · rw [hcomm]
        rfl
    rw [commutator_sec2P_eq h11 hE16 hF hL hodd hx hxS h4] at hle
    intro m
    obtain ⟨m', hm', hmm'⟩ := hle m.2
    obtain ⟨v, hv⟩ := hm'
    refine ⟨Multiplicative.toAdd v, ?_⟩
    have : m' = m := Subtype.ext hmm'
    rw [← this, ← hv]
    rfl
  have h16 : Nat.card ↥(E ⊓ A) = 16 := card_inf_left hF hodd
  set φ := totalPermAlt.comp (sec2KAction E F e) with hφ
  refine ⟨φ, fun v => ((natTheta t v : ↥(E ⊓ A)) : G),
    (totalPermAlt_bijective.2).comp (sec2KAction_surjective h11 hE16 hF hL hodd hx hxS h4 e),
    ?_, fun v w _ _ => by
      show ((natTheta t (v + w) : ↥(E ⊓ A)) : G) =
        ((natTheta t v : ↥(E ⊓ A)) : G) * ((natTheta t w : ↥(E ⊓ A)) : G)
      rw [natTheta_add hsq]
      rfl, fun v _ => (natTheta t v).2,
    fun a ha => ?_, fun v hv => ?_, fun k v hv => ?_⟩
  · ext k
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply,
      map_eq_one_iff _ totalPermAlt_bijective.1, ← MonoidHom.mem_ker,
      ker_sec2KAction h11 hE16 hF hL hodd hx hxS h4 e hc]
  · obtain ⟨v, hv⟩ := hsurj ⟨a, ha⟩
    refine ⟨evenize v, sum_evenize v, ?_⟩
    show ((natTheta t (evenize v) : ↥(E ⊓ A)) : G) = a
    rw [natTheta_evenize, hv]
  · rw [OneMemClass.coe_eq_one]
    exact natTheta_eq_one_iff hsq hone hsurj h16 hv
  ·
    have hkP := sec2K_le_normalizer_sec2P E k.2
    set σ := sec2PlanesActionFin E F e ⟨k, hkP⟩ with hσ
    have hφk : ((φ k : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) = totalPerm σ := by
      rw [hφ, MonoidHom.comp_apply, coe_totalPermAlt, coe_sec2KAction_apply]
    let f : ↥(E ⊓ A) →* ↥(E ⊓ A) :=
      { toFun := fun m => ⟨(k : G) * m * (k : G)⁻¹,
          conj_mem_inf_of_mem_normalizer h11 hE16 hF hL hodd hx hxS h4 hkP m.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
    have hf : ∀ a b, a ≠ b → f (t a b) = t (totalPerm σ a) (totalPerm σ b) := fun a b hab => by
      apply Subtype.ext
      show (k : G) * (q (rep2 a b) : G) * (k : G)⁻¹ = q (rep2 (totalPerm σ a) (totalPerm σ b))
      rw [conj_sqE h11 hE16 hF hL hodd hx hxS h4 e hc ⟨k, hkP⟩]
      change (q (ψ ⟨k, hkP⟩ (rep2 a b)) : G) = _
      rcases psi_rep2 h11 hE16 hF hL hodd e hc ⟨k, hkP⟩ hab with h | h | h
      · rw [h]
      · rw [h, hqω]
      · rw [h, hqω, hqω]
    have h1 := natTheta_comp hsq hsymm htri f (totalPerm σ) hf hv
    rw [hφk]
    exact congrArg Subtype.val h1

end CFSG.ComponentClassification.AS81
