module

public import CFSG.GF2Type.Smith1979.CaseIIITheta

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

open Subgroup Module CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S14
  CFSG.GF2Type.Smith1980Orth

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem exists_hyp10 [IsSimpleGroup G] (I : TimInputs) (hw : S.width = 6)
    (hirr : ¬ S.IsReducible) (hnoAll : S11.NoA2All S) {g : G} (H : Hyp4 S g) (C : Cons311 S g)
    (hI : ∀ (t : S.O) (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g),
      ¬ (OmegaCase H C ht ht1 hVQ ∧ finrank (ZMod 2) (Vt S g t) = 6 ∧ Nbar S g t = zpowers t))
    (hII : ∀ (t : S.O) (ht : t ∈ S.Lbar g), t ≠ 1 →
      ¬ (LinCase S g ht ∧ finrank (ZMod 2) (Vt S g t) = 3)) :
    ∃ t, S10.Hyp10 S g t := by
  by_contra hno
  push Not at hno
  have hlin : ∀ (t : S.O) (ht : t ∈ S.Lbar g), t ≠ 1 →
      Rbar S g t = S.Lbar g ∨ LinCase S g ht := by
    intro t ht ht1
    rcases classify_six I hw hirr hnoAll H C ht ht1 with hR | ⟨hL, -⟩ | hX | ⟨hVQ, hΩ, h6, hN⟩
    · exact Or.inl hR
    · exact Or.inr hL
    · exact absurd hX (hno t)
    · exact absurd ⟨hΩ, h6, hN⟩ (hI t ht ht1 hVQ)
  have hy : S11.Hyp S g := ⟨H, C, hnoAll, fun {t} ht ht1 => hlin t ht ht1⟩
  have hex := claim_14_3 I.hF2 I.hBen I.hTI H C hy.noA2' hirr (by omega)
  obtain ⟨-, k, u, τ, hyk, K, h3⟩ :=
    S11.timmesfeld_11_9 hy (I.h111 G S g hy hirr (by omega) hex) I.hCE (by omega) (I.h118 G S)
  obtain ⟨m, hm, hmk⟩ := hy.fusion k hyk.hyp4.conj_mem hyk.hyp4.conj_ne
  set m' : S.M := ⟨m, hm⟩ with hm'
  have hc : (m' : G) * g * S.z * ((m' : G) * g)⁻¹ = k * S.z * k⁻¹ := by
    rw [mul_conj_z]
    exact hmk
  have htk : S.ρ τ ∈ S.Lbar ((m' : G) * g) := by
    rw [S.Lbar_eq_of_conj_eq hc]
    exact K.mem_Lbar
  set t := (S.ρ m')⁻¹ * S.ρ τ * S.ρ m' with htdef
  have ht : t ∈ S.Lbar g := (mem_Lbar_mul_iff S m' g).1 htk
  have hτt : S.ρ τ = S.ρ m' * t * (S.ρ m')⁻¹ := by
    rw [htdef]
    group
  have ht1 : t ≠ 1 := by
    intro h1
    apply K.ne_one
    rw [hτt, h1, mul_one, mul_inv_cancel]
  have hV : finrank (ZMod 2) (Vt S g t) = 3 := by
    have e1 : Vt S k (S.ρ τ) = Vt S g (S.ρ τ) := by
      rw [← S11.Vt_eq_of_conj_eq hc, Vt_mul]
    rw [e1, hτt, S10.Vt_conj H.conj_mem m' t] at h3
    rwa [LinearEquiv.finrank_map_eq] at h3
  rcases hlin t ht ht1 with hR | hL
  · have := finrank_Vt_le_one_of_Rbar_eq H hR
    omega
  · exact hII t ht ht1 ⟨hL, hV⟩

end CFSG.GF2Type.Smith1979
