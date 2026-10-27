module

public import CFSG.LargeExtraspecial.A2ModFrC
public import CFSG.LargeExtraspecial.A2ModOrdFrame

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.A2Mod.FrC

open Module CFSG.Timmesfeld.ARS CFSG.LieType CFSG.LieType.Universal CFSG.Blueprint
open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Chevalley

variable {X : Type} [Group X] {D : Set X} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {ρ : X →* (V ≃ₗ[ZMod 2] V)}

theorem conj_mem_of_rootClass (hD : RootClass X D) : ∀ g, ∀ d ∈ D, g * d * g⁻¹ ∈ D := by
  obtain ⟨d₀, -, hd₀⟩ := hD.1.2.1
  intro g d hd
  exact (hd₀ _).mpr (((hd₀ d).mp hd).trans (isConj_iff.mpr ⟨g, rfl⟩))

theorem of_nslType_cartanC {n : ℕ} {i₀ : Fin n} (h : NSLType n (Symplectic.cartanC n) i₀) :
    3 ≤ n ∧ i₀.val + 1 < n := by
  generalize hA : Symplectic.cartanC n = A at h
  cases h with
  | symplectic hn i₀ hi₀ => exact ⟨hn, hi₀⟩
  | orthogonal hm i₀ hi₀ => exact absurd hA.symm (cartanB_ne_cartanC (by omega))
  | g2 i₀ hi₀ => exact absurd hA.symm cartan_G2_ne_cartanC
  | f4 i₀ hi₀ => exact absurd hA.symm cartan_F4_ne_cartanC

theorem frame_false_of_cartan_eq {R : Set (Subgroup X)} (F : NSLFrameData X R)
    (hC : F.D.cartan = Symplectic.cartanC F.D.rank)
    (hR : ∀ A ∈ R, ∃ d ∈ D, A = Subgroup.zpowers d) (hD : RootClass X D) (hA : A2Action D Q ρ)
    (hirr : ∀ W : Submodule (ZMod 2) V, (∀ x, ∀ w ∈ W, ρ x w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hV : 10 ≤ finrank (ZMod 2) V) : False := by
  obtain ⟨d, hd, hdA⟩ := hR _ F.mem
  have h2 : Nat.card ((F.D.rootGroup (Pi.single F.i₀ 1)).map F.Ψ) = 2 := by
    rw [hdA, Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hA.mul_self hd) (hA.ne_one hd)
  have hX := (Frame.card_map_rootGroup_single F F.i₀).symm.trans h2
  obtain ⟨K, D', nW, H, hct, hext, hdiv, i₀, type, pg, Ψ, surj, ker, mem, opp, comm, conc⟩ := F
  dsimp only at hC hdA hX
  cases conc with
  | symplectic n F' =>
    obtain ⟨hn, hi₀⟩ := of_nslType_cartanC type
    have hF : Nat.card F' = 2 := (Frame.card_rootGroup_symplectic n F' i₀).symm.trans hX
    exact false_of_symplectic (conj_mem_of_rootClass hD) hA hirr hV hn hF Ψ surj ker hi₀ hd hdA
  | @minus n K' _ b c hirr' =>
    obtain ⟨hm, -⟩ := Frame.of_nslType_cartanB (m := n - 1) type
    exact cartanB_ne_cartanC (by omega) hC
  | g2 K' => exact cartan_G2_ne_cartanC hC
  | twistedD4 f => exact cartan_G2_ne_cartanC hC
  | f4 K' => exact cartan_F4_ne_cartanC hC
  | twistedE6 f => exact cartan_F4_ne_cartanC hC

end CFSG.LargeExtraspecial.A2Mod.FrC
