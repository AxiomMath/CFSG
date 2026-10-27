module

public import CFSG.LargeExtraspecial.S11Eight

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u_G

variable {G : Type u_G} [Group G] [Finite G]

@[expose] def Timmesfeld11_8M2 (S : Setting G) : Prop :=
  CentralExtInput.{u_G} → ∀ {g : G} {t : S.O} {τ : S.M} {u : G}, Hyp S g →
    Conf S g t τ u → 6 ≤ S.width → finrank (ZMod 2) (Vt S g t) ≠ 2

variable {S : Setting G} {g : G}

theorem Conf.timmesfeld_11_8 (hy : Hyp S g) {t : S.O} {τ : S.M} {u : G} (K : Conf S g t τ u)
    (hCE : CentralExtInput.{u_G}) (hn : 6 ≤ S.width) (hm2 : Timmesfeld11_8M2 S) :
    finrank (ZMod 2) (Vt S g t) = 3 ∧ S.width = 6 := by
  have h2 := K.lin.two_le_finrank
  by_cases hm : 3 ≤ finrank (ZMod 2) (Vt S g t)
  · exact K.timmesfeld_11_8_of_three_le hy hCE hn hm
  · exact absurd (by omega) (hm2 hCE hy K hn)

theorem timmesfeld_11_9 (hy : Hyp S g) (h11 : Timmesfeld11_1Stmt S)
    (hCE : CentralExtInput.{u_G}) (hn : 6 ≤ S.width) (hm2 : Timmesfeld11_8M2 S) :
    S.width = 6 ∧ ∃ (k u : G) (τ : S.M), Hyp S k ∧ Conf S k (S.ρ τ) τ u ∧
      finrank (ZMod 2) (Vt S k (S.ρ τ)) = 3 := by
  obtain ⟨k, u, hτ, hkQ, hkz, hτQ, hτk, hR⟩ := h11
  have hyk := hy.of_conj hkQ hkz
  have K := hyk.conf (τ := ⟨u * S.z * u⁻¹, hτ⟩) rfl hτQ hτk hR
  obtain ⟨hm, hw⟩ := K.timmesfeld_11_8 hyk hCE hn hm2
  exact ⟨hw, k, u, _, hyk, K, hm⟩

end CFSG.LargeExtraspecial.S11
