module

public import CFSG.ClassicalInvolution.AschTight.S1911P3d
public import CFSG.ClassicalInvolution.AschTight.S19MSylow

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19M

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77

@[expose] def FactM0' : Prop :=
  ∀ (p e : ℕ) [Fact p.Prime], p ≠ 2 → 5 ≤ p ^ e →
    ∀ (E : Type) [Group E] [Finite E] [IsSimpleGroup E] (Ω : Set (Subgroup E))
      (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (k e' : ℕ), S1911.IsT6Tag t k →
        Nonempty (Ih8Model p e Ω t k e') → Ω.Nonempty → Disconnected.DEdgeless Ω →
        ∀ φ : MulAut E, φ * φ = 1 → (∀ L ∈ Ω, L.map φ.toMonoidHom ∈ Ω) →
          ∃ L ∈ Ω, L.map φ.toMonoidHom = L

theorem ih8Model_map_conj_mem {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]
    {Ω : Set (Subgroup G)} {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {k e : ℕ}
    (M : Ih8Model p f Ω t k e) {L : Subgroup G} (hL : L ∈ Ω) (g : G) :
    L.map (MulAut.conj g).toMonoidHom ∈ Ω := by
  obtain ⟨R, hR, rfl⟩ := (M.mem_iff L).mp hL
  obtain ⟨x, rfl⟩ := M.surj g
  change conjSub (M.ψ x) (R.map M.ψ) ∈ Ω
  rw [conjSub_map]
  exact M.map_mem (M.cls_conj R hR x)

theorem factM0' : FactM0' := by
  intro p e _ _ _ E _ _ _ Ω t k e' _ hM hne hDE φ hφ hφΩ
  obtain ⟨M⟩ := hM
  exact exists_map_eq_of_dEdgeless (fun L hL g => ih8Model_map_conj_mem M hL g) hne hDE φ hφ hφΩ

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19M
