module

public import CFSG.LocalAnalysis.GLTheoremB.PCompLift

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

theorem glaPPrimeCore_eq_ker {A H : Type*} [Group A] [Finite A] [Group H] {p : ℕ} (hp : p.Prime)
    (f : A →* H) (hf : Function.Surjective f) (hker : Nat.Coprime p (Nat.card f.ker))
    (hO : GLAPPrimeCore p H = ⊥) : GLAPPrimeCore p A = f.ker := by
  refine le_antisymm ?_ (le_sSup ⟨f.normal_ker, hker⟩)
  have h := glaPPrimeCore_map_of_surjective hp f hf hker
  rw [hO] at h
  exact (Subgroup.map_eq_bot_iff _).1 h

theorem exists_barX_top_equiv {X H : Type*} [Group X] [Finite X] [Group H] {p : ℕ} (hp : p.Prime)
    (ψ : X →* H) (hs : Function.Surjective ψ) (hker : Nat.Coprime p (Nat.card ψ.ker))
    (hO : GLAPPrimeCore p H = ⊥) :
    ∃ Φ : (↥(⊤ : Subgroup X) ⧸ GLAPPrimeCore p ↥(⊤ : Subgroup X)) ≃* H,
      ∀ L : Subgroup X, (barX p (⊤ : Subgroup X) L).map Φ.toMonoidHom = L.map ψ := by
  set f₀ : ↥(⊤ : Subgroup X) →* H := ψ.comp (⊤ : Subgroup X).subtype with hf₀
  have hf₀s : Function.Surjective f₀ := fun h => by
    obtain ⟨x, rfl⟩ := hs h
    exact ⟨⟨x, trivial⟩, rfl⟩
  have hk₀ : Nat.Coprime p (Nat.card f₀.ker) := by
    have : Nat.card f₀.ker = Nat.card ψ.ker :=
      Nat.card_congr (Equiv.subtypeEquiv Subgroup.topEquiv.toEquiv (fun x => Iff.rfl))
    rwa [this]
  have hcore := glaPPrimeCore_eq_ker hp f₀ hf₀s hk₀ hO
  let Φ : (↥(⊤ : Subgroup X) ⧸ GLAPPrimeCore p ↥(⊤ : Subgroup X)) ≃* H :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans
      (QuotientGroup.quotientKerEquivOfSurjective f₀ hf₀s)
  have hΦ : ∀ a : ↥(⊤ : Subgroup X), Φ (QuotientGroup.mk a) = ψ a.1 := fun a => rfl
  refine ⟨Φ, fun L => ?_⟩
  ext z
  simp only [barX, Subgroup.mem_map]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a.1, (Subgroup.mem_subgroupOf).1 ha, hΦ a⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨⟨x, trivial⟩, (Subgroup.mem_subgroupOf).2 hx, rfl⟩, hΦ ⟨x, trivial⟩⟩

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710
