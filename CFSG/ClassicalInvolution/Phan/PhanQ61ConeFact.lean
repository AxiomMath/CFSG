module

public import CFSG.ClassicalInvolution.Phan.PhanQ60Cone
public import CFSG.ClassicalInvolution.Phan.PhanQ50SolidInput
public import CFSG.ClassicalInvolution.Phan.PhanQ36Wire

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.PhanP
  CFSG.ClassicalInvolution.PhanD4 CFSG.ClassicalInvolution.PhanG CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Unitary

section ConeStd

variable {p e : ℕ} [Fact p.Prime]


set_option linter.unusedSectionVars false

theorem coneFact_std (M : StdModel p e) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) :
    ConeFact M.S (M.ptStep0 hp2 hq) := by
  have he0 : e ≠ 0 := by
    rintro rfl
    simp at hq
  have hodd := (CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq).1
  have hF : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e he0
  have hK := StdModel.card_K hq
  let _ : Algebra (GaloisField p e) (GaloisField p (2 * e)) := (Aniso.nonempty_algebra hF hK).some
  obtain ⟨D⟩ := exists_kdata (F := GaloisField p e) (K := GaloisField p (2 * e)) p e hF hK hp2
    M.hε M.nonsq
  classical
  have h2K := two_ne_zero_gf hp2 (2 * e)
  have hσ := unitaryInvolution_eq_tau M D hq
  have hσu := isUnitaryInvolution_unitaryInvolution (K := GaloisField p (2 * e)) (p := p) (f := e)
    hK
  have h0 : PtStep0 M.S := M.ptStep0 hp2 hq
  have hE : PtEdge M.S := M.ptEdge hp2 hq
  have hle : ∀ (x : spinGroup (quadPlus 4 (GaloisField p e)) ⧸ parab M.S {1, 2, 3})
      (u : V8 (GaloisField p (2 * e))), lineOfPt M D hp2 hq x = Submodule.span _ {u} →
      ∀ (W : Submodule (GaloisField p (2 * e)) (V8 (GaloisField p (2 * e)))), u ∈ W →
      lineOfPt M D hp2 hq x ≤ W := fun x u hx W hu => by
    rw [hx, Submodule.span_singleton_le_iff_mem]
    exact hu
  intro a b c hab hbc hca
  obtain ⟨ua, -, hffa, hla⟩ := lineOfPt_ff hp2 hq h2K (D := D) a
  obtain ⟨ub, -, hffb, hlb⟩ := lineOfPt_ff hp2 hq h2K (D := D) b
  obtain ⟨uc, -, hffc, hlc⟩ := lineOfPt_ff hp2 hq h2K (D := D) c
  have colK : ∀ {x y : spinGroup (quadPlus 4 (GaloisField p e)) ⧸ parab M.S {1, 2, 3}}
      {ux uy : V8 (GaloisField p (2 * e))}, lineOfPt M D hp2 hq x = Submodule.span _ {ux} →
      lineOfPt M D hp2 hq y = Submodule.span _ {uy} → (ptGraph M.S).Adj x y → ColK D ux uy :=
    fun hx hy hxy => by
      have := (adj_iff_adjL hp2 hq _ _ (D := D)).1 hxy
      rw [hx, hy] at this
      exact (adjL_span_iff D).1 this
  have hab' := colK hla hlb hab
  have hbc' := colK hlb hlc hbc
  have hac' := (colK hlc hla hca).symm
  obtain ⟨ue, hffe, hae, hbe, hce, ⟨W₁, hW₁, ha₁, hb₁, he₁⟩, ⟨W₂, hW₂, hb₂, hc₂, he₂⟩,
      ⟨W₃, hW₃, hc₃, ha₃, he₃⟩⟩ :=
    exists_cone D hodd h2K M.hε hσ hσu (StdModel.card_K hq) hF hq hffa hffb hffc hab' hbc' hac'
  obtain ⟨x, hlx⟩ := exists_pt_of_ffK hp2 hq hffe
  have adjx : ∀ {y : spinGroup (quadPlus 4 (GaloisField p e)) ⧸ parab M.S {1, 2, 3}}
      {uy : V8 (GaloisField p (2 * e))}, lineOfPt M D hp2 hq y = Submodule.span _ {uy} →
      ColK D uy ue → (ptGraph M.S).Adj y x := fun hy hc => by
    refine (adj_iff_adjL hp2 hq _ _ (D := D)).2 ?_
    rw [hy, hlx]
    exact (adjL_span_iff D).2 hc
  have hax := adjx hla hae
  have hbx := adjx hlb hbe
  have hcx := adjx hlc hce
  refine ⟨x, hax, hbx, hcx, ?_, ?_, ?_⟩
  · refine solidNull_of_phanSolid M D hp2 hq h0 hE hW₁ _ ?_
    intro v hv
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact hle _ _ hla _ ha₁
    · exact hle _ _ hlb _ hb₁
    · exact hle _ _ hlx _ he₁
    · exact hle _ _ hla _ ha₁
  · refine solidNull_of_phanSolid M D hp2 hq h0 hE hW₂ _ ?_
    intro v hv
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact hle _ _ hlb _ hb₂
    · exact hle _ _ hlc _ hc₂
    · exact hle _ _ hlx _ he₂
    · exact hle _ _ hlb _ hb₂
  · refine solidNull_of_phanSolid M D hp2 hq h0 hE hW₃ _ ?_
    intro v hv
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact hle _ _ hlc _ hc₃
    · exact hle _ _ hla _ ha₃
    · exact hle _ _ hlx _ he₃
    · exact hle _ _ hlc _ hc₃

end ConeStd

section Wire3

set_option linter.unusedSectionVars false

variable (p f : ℕ) [Fact p.Prime]


theorem phanD4Cone : PhanD4Cone p f := by
  intro hp2 hq
  exact coneFact_std (stdModel hp2 hq) hp2 hq

theorem phanD4Geometry_std : PhanD4Geometry p f := phanD4Geometry_of_cone (phanD4Cone p f)

end Wire3

end CFSG.ClassicalInvolution.PhanQ
