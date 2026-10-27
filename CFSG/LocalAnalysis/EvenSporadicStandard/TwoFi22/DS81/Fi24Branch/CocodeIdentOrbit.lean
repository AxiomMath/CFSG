module

public import CFSG.Quasithin.Background.HTransport

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open MulAction CFSG.Quasithin.H

variable {V W : Type*} [CommGroup V] [CommGroup W]

theorem image_orbit_map_congrHom (e : V ≃* W) (L : Subgroup (MulAut V)) (x : V) :
    e '' orbit ↥L x = orbit ↥(L.map (congrHom e)) (e x) := by
  ext w
  constructor
  · rintro ⟨v, ⟨⟨g, hg⟩, rfl⟩, rfl⟩
    refine ⟨⟨congrHom e g, Subgroup.mem_map_of_mem _ hg⟩, ?_⟩
    show congrHom e g (e x) = e (g x)
    simp [congrHom_apply]
  · rintro ⟨⟨_, ⟨g, hg, rfl⟩⟩, rfl⟩
    refine ⟨g x, ⟨⟨g, hg⟩, rfl⟩, ?_⟩
    show e (g x) = congrHom e g (e x)
    simp [congrHom_apply]

theorem mem_orbit_map_congrHom_iff (e : V ≃* W) (L : Subgroup (MulAut V)) (x : V) (w : W) :
    w ∈ orbit ↥(L.map (congrHom e)) (e x) ↔ e.symm w ∈ orbit ↥L x := by
  rw [← image_orbit_map_congrHom]
  constructor
  · rintro ⟨v, hv, rfl⟩
    simpa using hv
  · intro h
    exact ⟨e.symm w, h, by simp⟩

theorem ncard_orbit_map_congrHom (e : V ≃* W) (L : Subgroup (MulAut V)) (x : V) :
    (orbit ↥(L.map (congrHom e)) (e x)).ncard = (orbit ↥L x).ncard := by
  rw [← image_orbit_map_congrHom, Set.ncard_image_of_injective _ e.injective]

theorem card_orbit_map_congrHom (e : V ≃* W) (L : Subgroup (MulAut V)) (x : V) :
    Nat.card ↥(orbit ↥(L.map (congrHom e)) (e x)) = Nat.card ↥(orbit ↥L x) := by
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, ncard_orbit_map_congrHom]

theorem card_orbit_map_congrHom_symm (e : V ≃* W) (L : Subgroup (MulAut V)) (w : W) :
    Nat.card ↥(orbit ↥(L.map (congrHom e)) w) = Nat.card ↥(orbit ↥L (e.symm w)) := by
  have h := card_orbit_map_congrHom e L (e.symm w)
  rwa [e.apply_symm_apply] at h

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
