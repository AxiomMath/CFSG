module

public import CFSG.Quasithin.EmptyFaithful.S152UOff
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152QB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def Input15209Offender_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → Concl319 T M (V154 T Mc M) H True →
      Nonempty (OTwoQuot H ≃* S152N.W3) → ∀ A ∈ deltaSet H (V154 T Mc M),
        ∃ B₁ : Subgroup G, B₁ ≤ A ∧ (B₁ ⊓ pCoreOf 2 H).relIndex B₁ = 2 ∧
          Nat.card B₁ *
              Nat.card ↥(conjClosure (V154 T Mc M) H ⊓ Subgroup.centralizer (B₁ : Set G)) =
            Nat.card A * Nat.card ↥(B₁ ⊓ conjClosure (V154 T Mc M) H)

theorem input15209Lift_of_offender_F4 (h1511one : StageLemma15111One) (hO : Input15209Offender_F4) :
    Input15209Lift_F4 := by
  intro G _ _ T Mc M hs H hH hc hW hne
  obtain ⟨A, hA⟩ := hne
  obtain ⟨B₁, hB₁A, hrel, hcard⟩ := hO G T Mc M hs H hH hc hW A hA
  have hVQ : V154 T Mc M ≤ pCoreOf 2 H := h1511one G T Mc M hs.qtfe hs.mf hs.ce H hH
  have hUQ : conjClosure (V154 T Mc M) H ≤ pCoreOf 2 H :=
    conjClosure_le fun h hh z hz =>
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 H hh) z).1 (hVQ hz)
  obtain ⟨hDmax, hDQ⟩ := S152U.lift_offender hA.1 hc.elemAbelian hUQ hB₁A hcard
  refine ⟨_, hDmax, ?_, ?_⟩
  · intro hDle
    have hB₁Q : B₁ ≤ pCoreOf 2 H := le_sup_left.trans hDle
    have h1 : (B₁ ⊓ pCoreOf 2 H).relIndex B₁ = 1 :=
      Subgroup.relIndex_eq_one.2 (le_inf le_rfl hB₁Q)
    omega
  · have hDH := hDmax.1
    rw [← Gap6.relIndex_sup_pCoreOf_eq hDH, hDQ, Gap6.relIndex_sup_pCoreOf_eq (hB₁A.trans hA.1.1)]
    exact hrel

end CFSG.Quasithin
