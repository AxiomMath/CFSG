module

public import CFSG.GF2Type.Smith1979.W4C2TestComm

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4C2

namespace LocalTest

open Module QuadraticMap CFSG.LargeExtraspecial CFSG.RankThree.OrthogonalInvolutions
  CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix

theorem valid_E1 : Valid E1 := by
  unfold Valid E1
  decide

theorem matG1 : rowsMatrix 4 E1.G = !![1,0,0,0; 1,1,0,0; 0,0,1,0; 0,0,0,1] := by
  decide

theorem matH1 : rowsMatrix 4 E1.H = !![1,1,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,1] := by
  decide

theorem rel_sq_E1 : Rel (mulE E1 E1) idE := by
  unfold Rel mulE E1 idE
  simp only [Bool.false_eq_true, ↓reduceIte, rowsMatrix_mulRows, rowsMatrix_idRows, and_true]
  refine ⟨?_, ?_⟩ <;> decide

theorem dec_E1_sq : dec E1 * dec E1 = 1 := by
  rw [← dec_mul valid_E1 valid_E1, dec_congr rel_sq_E1, dec_idE]

theorem dec_E1_sub (v : Vm) :
    dec E1 v - v = ((v.1 1) • (Pi.single 0 1 : V4), (v.2 0) • (Pi.single 1 1 : V4)) := by
  rw [dec_apply valid_E1]
  have hs : E1.s = false := rfl
  unfold semE act
  rw [hs, matG1, matH1]
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;> fin_cases j <;>
    simp [Matrix.vecHead, Matrix.vecTail]

@[expose] def u1 : Vm := (Pi.single 0 1, 0)

@[expose] def u2 : Vm := (0, Pi.single 1 1)

theorem commSpace_E1 : commSpace (dec E1) = Submodule.span (ZMod 2) (Set.range ![u1, u2]) := by
  ext x
  rw [mem_commSpace, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨![v.1 1, v.2 0], ?_⟩
    rw [dec_E1_sub, Fin.sum_univ_two]
    simp [u1, u2]
  · rintro ⟨c, rfl⟩
    refine ⟨(c 0 • (Pi.single 1 1 : V4), c 1 • (Pi.single 0 1 : V4)), ?_⟩
    rw [dec_E1_sub, Fin.sum_univ_two]
    simp [u1, u2]

theorem linearIndependent_u : LinearIndependent (ZMod 2) ![u1, u2] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have h1 := congrArg (fun w : Vm => w.1 0) h
  have h2 := congrArg (fun w : Vm => w.2 1) h
  simp [u1, u2] at h1 h2
  exact ⟨h1, h2⟩

theorem finrank_commSpace_E1 : finrank (ZMod 2) (commSpace (dec E1)) = 2 := by
  rw [commSpace_E1, finrank_span_eq_card linearIndependent_u]
  simp

theorem q0_commSpace_E1 : ∀ x ∈ commSpace (dec E1), q0 x = 0 := by
  intro x hx
  obtain ⟨v, rfl⟩ := mem_commSpace.mp hx
  rw [dec_E1_sub, q0_apply]
  simp [dotProduct, Pi.single_apply]

theorem dec_E1_ne_one : dec E1 ≠ 1 := by
  intro h
  have := dec_E1_sub (Pi.single 1 1, 0)
  rw [h] at this
  have h0 := congrArg (fun w : Vm => w.1 0) this
  simp at h0

theorem isTypeA_E1 : IsTypeA q0 (dec E1) 2 :=
  ⟨dec_q0 valid_E1, dec_E1_ne_one, dec_E1_sq, finrank_commSpace_E1, q0_commSpace_E1⟩

theorem typeA_of_comm_N (hchk : chk = true) {L : Subgroup (Vm ≃ₗ[ZMod 2] Vm)} (hLH : L ≤ Hm)
    (hLc : ∀ a ∈ L, ∀ a' ∈ L, a * a' = a' * a) (hLs : ∀ a ∈ L, a * a = 1)
    (hLb : ∀ ℓ ∈ L, ℓ (vecE bN) = vecE bN)
    (hLn : ∀ m ∈ Hm, m (vecE bN) = vecE bN → ∀ ℓ ∈ L, m * ℓ * m⁻¹ ∈ L) :
    ∀ ℓ ∈ L, ℓ ≠ 1 → IsTypeA q0 ℓ 2 := by
  obtain ⟨hv, ho, hN, hM⟩ := chk_parts hchk
  simp only [chkN, Bool.and_eq_true] at hN
  obtain ⟨hcand, hU⟩ := hN
  intro ℓ hℓ hℓ1
  obtain ⟨C, hC, hCv, rfl⟩ := comm_mem_Cl hv hcand hLH hLc hLs hLb hLn ℓ hℓ
  have hU' := List.all_eq_true.mp hU C hC
  rcases Bool.or_eq_true_iff.mp hU' with h1 | h2
  · exact absurd (by rw [dec_eq_of_eqE h1, dec_idE]) hℓ1
  · obtain ⟨F, hF, hFeq⟩ := List.any_eq_true.mp h2
    obtain ⟨hFv, hFm, hFb⟩ := stabL_spec hv hF
    have e1 : dec (conj F C) = dec E1 := dec_eq_of_eqE hFeq
    rw [dec_conj hFv hCv] at e1
    have hT : IsTypeA q0 (dec F * dec C * (dec F)⁻¹) 2 := by
      rw [e1]
      exact isTypeA_E1
    exact isTypeA_of_conj (dec_q0 hFv) hT

end LocalTest

end CFSG.GF2Type.Smith1979.W4C2
