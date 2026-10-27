module

public import CFSG.Timmesfeld.ARS.ExclNSFrames
public import CFSG.LargeExtraspecial.A2ModFrFShort

public section

namespace CFSG.LargeExtraspecial.A2Mod.FrF

open Module CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.ExclNS CFSG.Blueprint.Chevalley
  CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] {R : Set (Subgroup G)}

theorem exists_f4Frame_of_nslFrame (F : NSLFrameData G R)
    (hF4 : F.D.rank = Tag.rank .F4 ∧ HEq F.D.cartan (Tag.cartan .F4)) :
    ∃ F' : F4Frame G R, ∀ m : ℕ, (∀ γ ∈ F.D.roots, Nat.card (F.D.rootGroup γ) ≤ m) →
      Nat.card (F'.X a2v) ≤ m := by
  revert hF4
  obtain ⟨K, ⟨r, A, hA, div, X⟩, nW, H, hct, hext, hdiv, i₀, type, pg, Ψ, surj, ker, mem, opp,
    -, -⟩ := F
  intro hF4
  obtain ⟨hr, hC⟩ := hF4
  dsimp only at hr hC hdiv
  subst hr
  obtain rfl := eq_of_heq hC
  change div = ∅ at hdiv
  subst hdiv
  have hi₀ : i₀.val < 2 := by
    rcases NSLType.elim type with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨h, -, -⟩ | ⟨-, h, -⟩
    · exact absurd h cartan_F4_ne_cartanC
    · exact absurd (show Tag.cartan .F4 = Spin.cartanB (Tag.rank .F4) from h) (by decide)
    · exact absurd (show Tag.rank .F4 = 2 from h) (by decide)
    · exact h
  exact ⟨⟨K, hA, X, nW, H, hct, hext, i₀, hi₀, pg, Ψ, surj, ker, mem, opp⟩,
    fun m hm => hm a2v (a2v_mem_roots hA)⟩

variable {D : Set G} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {ρ : G →* (V ≃ₗ[ZMod 2] V)}

end CFSG.LargeExtraspecial.A2Mod.FrF
