module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93ResG2G
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93ResLin
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93ResUni

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Local.P34 CFSG.ComponentClassification CFSG.Blueprint
  CFSG.Assembly.LowTwoRank

theorem ivk93res_mod4 {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {ε : Bool} {q : ℕ}
    {L₁ L₂ : Subgroup (CentralizerBar z)} (hctx : Stage2Ctx G z (Kind.l4 ε) S)
    (hp : Stage1L4 G z S ε q L₁ L₂)
    (hone : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) :
    q % 4 = (if ε then 1 else 3) := by
  rcases hp.fusion with ⟨h, -⟩ | ⟨-, x, hx, -, -⟩
  · exact h
  · exfalso
    apply hx.x_nonCentral
    obtain ⟨c, hc⟩ := isConj_iff.1 (hone z x hctx.orderOf_z hx.x_inv)
    have := isCentralInvolution_of_equiv (MulAut.conj c) hctx.central
    have hx' : (MulAut.conj c) z = x := by
      show c * z * c⁻¹ = x
      exact hc
    rwa [hx'] at this

theorem ivk93res_mismatch : ∀ (G : Type) [Group G] [Finite G] (z : G) (ε : Bool) (S : Subgroup G)
    (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)), Stage2Ctx G z (Kind.l4 ε) S →
    Stage1L4 G z S ε q L₁ L₂ → (∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) →
    ∀ H : Subgroup G, H ≠ ⊤ → Cen z ≤ H → pCore 2 (HBar H) = ⊥ →
      IsSimpleGroup ↥(generalizedFitting (HBar H)) →
      (∃ a b : ↥(generalizedFitting (HBar H)), a * b ≠ b * a) → PerfInJ H →
      HasTwoInvolutionClasses (HBar H) →
      ∀ p f : ℕ, p ^ f = q →
        ¬ (if ε then LieModel ↥(generalizedFitting (HBar H)) .PSU 4 p f
            else LieModel ↥(generalizedFitting (HBar H)) .PSL 4 p f) := by
  intro G _ _ z ε S q L₁ L₂ hctx hp hone H _ _ _ _ _ _ _ p f hpf hm
  have hz2 := hctx.orderOf_z
  have hq4 := ivk93res_mod4 hctx hp hone
  cases ε
  ·
    simp only [Bool.false_eq_true, ite_false] at hm hq4
    obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.stated_of_lieModel_PSL hm
    have hFq : Nat.card F = q := hF.trans hpf
    have hres := (ivk93res_sl2_lin (F := F) (by rw [hFq]; exact hq4)).of_equiv e.symm
    rw [hFq] at hres
    exact false_of_ResSL2 hp.pair hz2 hone hres
  ·
    simp only [ite_true] at hm hq4
    obtain ⟨⟨hpp, hf1, -⟩, K, _, _, hK, ⟨φ⟩⟩ := CFSG.GH74.Generic.stated_of_lieModel_PSU hm
    have hodd : Odd q := hp.pair.odd
    have hp2 : p ≠ 2 := by
      rintro rfl
      have h2 : Even (2 ^ f) := (Nat.even_pow' (by omega)).2 even_two
      rw [hpf] at h2
      exact (Nat.not_even_iff_odd.2 hodd) h2
    have hs := ivk93res_sl2_uni hpp hp2 hf1 hK (by rw [hpf]; exact hq4)
    have hres := hs.of_equiv φ.symm
    rw [hpf] at hres
    exact false_of_ResSL2 hp.pair hz2 hone hres

theorem ivk93OneClassRes_proved :
    Ivk93OneClassRes := by
  exact ⟨ivk93res_g2, ivk93res_mismatch⟩

end CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt
