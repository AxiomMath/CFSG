module

public import CFSG.LocalAnalysis.GL83PartI.I_27_9.Orbits
public import CFSG.LocalAnalysis.GL83PartI.I_27_9_3.Fix
public import CFSG.LocalAnalysis.GL83PartI.I_27_9_3.Alt

public section

namespace GL83.PiGen

open Equiv Equiv.Perm GL83.CompFam CFSG.Open

section Rep

variable {X : Type*} [Group X] {K : Subgroup X} {n : ℕ}

@[expose] noncomputable def quotEquiv (hZ : Subgroup.center K = ⊥)
    (e : ↥K ≃* ↥(alternatingGroup (Fin n))) :
    K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n) :=
  ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e

theorem quotEquiv_mk (hZ : Subgroup.center K = ⊥) (e : ↥K ≃* ↥(alternatingGroup (Fin n)))
    (x : ↥K) : quotEquiv hZ e (QuotientGroup.mk x) = e x := rfl

@[expose] noncomputable def piRep (hZ : Subgroup.center K = ⊥) (hn5 : 5 ≤ n) (hn6 : n ≠ 6)
    (e : ↥K ≃* ↥(alternatingGroup (Fin n))) :
    ↥(Subgroup.normalizer (K : Set X)) →* Perm (Fin n) :=
  permHom (le_refl _) hn5 hn6 (quotEquiv hZ e)

theorem implements_piRep (hZ : Subgroup.center K = ⊥) (hn5 : 5 ≤ n) (hn6 : n ≠ 6)
    (e : ↥K ≃* ↥(alternatingGroup (Fin n))) {g : X} (hg : g ∈ Subgroup.normalizer (K : Set X)) :
    Implements e g (piRep hZ hn5 hn6 e ⟨g, hg⟩) := by
  intro x
  obtain ⟨y, hy, h⟩ := permHom_spec (le_refl _) hn5 hn6 (quotEquiv hZ e) ⟨g, hg⟩ x
  exact ⟨y, hy, h⟩

theorem Implements.unique (hn5 : 5 ≤ n) (hn6 : n ≠ 6) {e : ↥K ≃* ↥(alternatingGroup (Fin n))}
    {g : X} {σ σ' : Perm (Fin n)} (h : Implements e g σ) (h' : Implements e g σ') : σ = σ' := by
  refine (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn5 hn6).1 ?_
  ext u
  obtain ⟨x, rfl⟩ := e.surjective u
  obtain ⟨y, hy, hσ⟩ := h x
  obtain ⟨y', hy', hσ'⟩ := h' x
  have hyy : y = y' := Subtype.ext (hy.trans hy'.symm)
  subst hyy
  simp only [MulAut.conjNormal_apply]
  rw [hσ, hσ']

theorem piRep_eq_of_implements (hZ : Subgroup.center K = ⊥) (hn5 : 5 ≤ n) (hn6 : n ≠ 6)
    (e : ↥K ≃* ↥(alternatingGroup (Fin n))) {g : X} (hg : g ∈ Subgroup.normalizer (K : Set X))
    {σ : Perm (Fin n)} (h : Implements e g σ) : piRep hZ hn5 hn6 e ⟨g, hg⟩ = σ :=
  Implements.unique hn5 hn6 (implements_piRep hZ hn5 hn6 e hg) h

end Rep

section Plane

variable {X : Type*} [Group X] [Finite X] {K : Subgroup X} {n : ℕ} {p : ℕ} [Fact p.Prime]

theorem exists_fixing_of_plane (hp3 : 3 ≤ p) {k : ℕ} (hk : 1 ≤ k) (hnk : n = k * p + 2)
    (hn5 : 5 ≤ n) (hn6 : n ≠ 6) (hZ : Subgroup.center K = ⊥) (hK : IsComponentOf K ⊤)
    (e : ↥K ≃* ↥(alternatingGroup (Fin n))) {B D : Subgroup X} (hB : IsElemAbelian p B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hrank : GLATwoLocalRank p X ≤ pRank p B)
    (hDB : D ≤ B) (hD : Nat.card D = p ^ 2) (ω : Fin n) :
    ∃ d : X, ∃ hd : d ∈ D, d ≠ 1 ∧ piRep hZ hn5 hn6 e ⟨d, hBN (hDB hd)⟩ ω = ω := by
  have hp := (Fact.out : p.Prime)
  let R : Subgroup (Perm (Fin n)) :=
    (permHom (stab_le_normalizer B K) hn5 hn6 (quotEquiv hZ e)).range
  let f : ↥D →* Perm (Fin n) :=
    (piRep hZ hn5 hn6 e).comp (Subgroup.inclusion (hDB.trans hBN))
  have hR : ∀ d : ↥D, f d ∈ R := fun d =>
    ⟨⟨d, Subgroup.mem_inf.2 ⟨hDB d.2, hBN (hDB d.2)⟩⟩, rfl⟩
  have horb : Nat.card (MulAction.orbit R ω) ≤ p :=
    orbit_card_le hp3 hk hnk hn5 hn6 hB hK hZ (quotEquiv hZ e) hrank ω
  have hlt : Nat.card (MulAction.orbit R ω) < Nat.card D := by
    rw [hD]
    calc Nat.card (MulAction.orbit R ω) ≤ p := horb
      _ < p ^ 2 := by nlinarith [hp.one_lt]
  obtain ⟨d, hd1, hdω⟩ := exists_ne_one_fixing f R hR ω hlt
  exact ⟨d, d.2, fun h => hd1 (Subtype.ext h), hdω⟩

end Plane

end GL83.PiGen
