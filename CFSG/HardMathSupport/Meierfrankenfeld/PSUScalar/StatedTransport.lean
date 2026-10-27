module

public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.WittTransport
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

open CFSG.Open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem exists_stated_transport (hF : Nat.card F = (p ^ f) ^ 2) {m e : ℕ}
    {P : Subgroup (SU (unitaryInvolution F p f) m)} (hPel : IsElemAbelian e P) :
    ∃ A : Subgroup (GL (Fin m) F), A ≤ StatedSU m (p ^ f) F ∧ IsElemAbelian e A ∧
      Nat.card A = Nat.card P ∧
      ∀ a ∈ A, ∃ x ∈ P, a = wittMat hF m * (x : GL (Fin m) F) * (wittMat hF m)⁻¹ := by
  let eS := suToStated hF m
  refine ⟨(P.map eS.toMonoidHom).map (StatedSU m (p ^ f) F).subtype, Subgroup.map_subtype_le _,
    (hPel.map _).map _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      Subgroup.card_map_of_injective eS.injective]
  · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, coe_suToStated hF m x⟩

end CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
