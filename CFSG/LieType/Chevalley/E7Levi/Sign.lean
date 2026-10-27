module

public import CFSG.LieType.Chevalley.E7Levi.Emb
public import CFSG.LieType.Chevalley.AllRootWeylConjugation
public import CFSG.RankThree.PartOne.KD4T.Certs

public noncomputable section

namespace CFSG.LieType.Chevalley.E7Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KD4T

variable {τ : Tag} [hτ : E7Sub τ]

theorem weylElt_comp_e7Emb {K : Type} [Field K] (k : Fin Tag.E7.rank) (t : Kˣ) :
    (weylElt τ K (e7Idx k) t : Module.End K (RootModule τ K)) ∘ₗ e7Emb τ K =
      e7Emb τ K ∘ₗ (weylElt Tag.E7 K k t : Module.End K (RootModule Tag.E7 K)) := by
  rw [LieType.Chevalley.weylElt_eq_xUnit_mul, LieType.Chevalley.weylElt_eq_xUnit_mul]
  exact mul_comp_e7Emb (mul_comp_e7Emb (xOp_comp_e7Emb k _) (yOp_comp_e7Emb k _))
    (xOp_comp_e7Emb k _)

theorem exists_sign_pinnedX_comp_e7Emb {α : Fin Tag.E7.rank → ℤ} (hα : IsRoot Tag.E7 α) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ (L : Type) [Field L] (c : L),
      (pinnedX τ L (e7Lat τ α) c : Module.End L (RootModule τ L)) ∘ₗ e7Emb τ L =
        e7Emb τ L ∘ₗ (pinnedX Tag.E7 L α ((ε : L) * c) : Module.End L (RootModule Tag.E7 L)) := by
  induction hα with
  | basis j =>
    refine ⟨1, Or.inl rfl, fun L _ c => ?_⟩
    rw [e7Lat_single, pinnedX_single, pinnedX_single, Int.cast_one, one_mul]
    exact xOp_comp_e7Emb j c
  | @reflect i v hv ih =>
    obtain ⟨ε, hε, h⟩ := ih
    have hv6 : IsRoot τ (e7Lat τ v) := isRoot_e7Lat_iff.2 hv
    have h6 := (all_root_weyl_infinitesimal.{0} τ).2.2.2.1 (e7Idx i) _ hv6
    have h4 := (all_root_weyl_infinitesimal.{0} Tag.E7).2.2.2.1 i _ hv
    refine ⟨allRootWeylSign Tag.E7 i v * ε * allRootWeylSign τ (e7Idx i) (e7Lat τ v), ?_,
      fun L _ c => ?_⟩
    · rcases h4 with h4 | h4 <;> rcases hε with hε | hε <;> rcases h6 with h6 | h6 <;>
        simp [h4, hε, h6]
    have hσ6 : ((allRootWeylSign τ (e7Idx i) (e7Lat τ v) : L) *
        allRootWeylSign τ (e7Idx i) (e7Lat τ v)) = 1 := by
      rcases h6 with h6 | h6 <;> simp [h6]
    have e6 := weylElt_one_mul_pinnedX_mul_inv L (e7Idx i) hv6
      ((allRootWeylSign τ (e7Idx i) (e7Lat τ v) : L) * c)
    rw [← mul_assoc, hσ6, one_mul, ← e7Lat_reflect] at e6
    have e4 := weylElt_one_mul_pinnedX_mul_inv L i hv
      ((ε : L) * ((allRootWeylSign τ (e7Idx i) (e7Lat τ v) : L) * c))
    have hc : ((allRootWeylSign Tag.E7 i v * ε * allRootWeylSign τ (e7Idx i) (e7Lat τ v) :
        ℤ) : L) * c = (allRootWeylSign Tag.E7 i v : L) *
          ((ε : L) * ((allRootWeylSign τ (e7Idx i) (e7Lat τ v) : L) * c)) := by
      push_cast
      ring
    rw [← e6, hc, ← e4]
    exact mul_comp_e7Emb (mul_comp_e7Emb (weylElt_comp_e7Emb i 1) (h L _))
      (inv_comp_e7Emb (weylElt_comp_e7Emb i 1))

end CFSG.LieType.Chevalley.E7Levi
