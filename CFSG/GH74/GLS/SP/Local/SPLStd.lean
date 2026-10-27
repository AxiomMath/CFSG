module

public import CFSG.GH74.GLS.SP.Local.SPLR2
public import CFSG.GH74.GLS.SP.Local.SPLL33
public import CFSG.GH74.GLS.SP.Local.SPLOrd
public import CFSG.GH74.GLS.SP.Local.Setup
public import CFSG.GH74.GLS.SP.Generic
public import CFSG.GH74.GLS.SP.Local.SPLFB
public import CFSG.GH74.GLS.SP.Local.SPLIso
public import CFSG.GH74.GLS.SP.Local.SPLM1d
public import CFSG.GH74.GLS.SP.Local.SPLSetFinal

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS
open CFSG.GH74.GLS.LU.Local

@[expose] def SPLLeafCtStd : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Stage12.Std G → ∀ D₁ : SPLNot1 G,
    SPLSetup D₁.toSPLNot0 → SPL2Set D₁ → ∃ D : SPLNot2 G, D.toSPLNot1 = D₁ ∧ SPL2Ct D

@[expose] def SPLocalLeafStd : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Stage12.Std G → ∀ (F : Type) [Field F] [Finite F]
    (hF : 4 ≤ Nat.card F), Odd (Nat.card F) →
    ∀ (z : G) (S : Sylow 2 G) (K₁ K₂ : Subgroup G) (t : G), LUComps G (Nat.card F) z K₁ K₂ →
      SPSyl G z S K₁ K₂ t → pPrimeCoreOf 2 (Cz z) = ⊥ →
      (∀ c ∈ Cz z, ∃ k ∈ K₁ ⊔ K₂, ∃ s ∈ (S : Subgroup G),
        ∃ y ∈ pPrimeCoreOf 2 (centralizer (((S : Subgroup G) ⊓ (K₁ ⊔ K₂) : Subgroup G) : Set G)),
          c = k * s * y) → SPGlueData G F hF

theorem spLocalLeafStd_of_leaves (h1 : SPLLeafSet) (h2 : SPLLeafCtStd) (h3 : SPLLeafOrd)
    (h4 : SPLLeafM2) (h7 : SPLLeafIso) : SPLocalLeafStd := by
  have h5 := splLeafM1
  have h6 := splLeafL42
  intro G _ _ hS F _ _ hF hodd z S K₁ K₂ t hc hs hA hgen
  have hG : IsKProperSimple G := hS.kps
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨p, hpc⟩ := CharP.exists F
  have hp : p.Prime := CharP.char_is_prime F p
  obtain ⟨n, -, hcard⟩ := FiniteField.card F p
  have hcard' : Nat.card F = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hcard
  have hp2 : p ≠ 2 := by
    rintro rfl
    rw [hcard'] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, n.ne_zero⟩)
  have hq5 : 5 ≤ Nat.card F := by
    obtain ⟨m, hm⟩ := hodd
    omega
  obtain ⟨D₀, hsetup, hq⟩ : ∃ D₀ : SPLNot0 G, SPLSetup D₀ ∧ D₀.q = Nat.card F :=
    ⟨⟨p, Nat.card F, z, S, K₁, K₂, t⟩,
      ⟨hp, hp2, ⟨n, n.pos, hcard'⟩, hq5, hc, hs, hA, hgen⟩, rfl⟩
  obtain ⟨D1, rfl, hset⟩ := h1 G hG D₀ hsetup
  obtain ⟨D2, rfl, hct⟩ := h2 G hS D1 hsetup hset
  have hord := h3 G hG D2 hsetup hset hct
  obtain ⟨D3, rfl, hm2⟩ := h4 G hG D2 hsetup hset hct hord
  obtain ⟨D4, rfl, hm1⟩ := h5 G hG D3 hsetup hset hct hord hm2
  have hstage : SPLStage4 D4 := ⟨hsetup, hset, hct, hord, hm2, hm1⟩
  obtain ⟨hL42, hCH⟩ := h6 G hG D4 hstage
  exact spGlueData_of_stage hG hF D4 hq hstage hL42 hCH (h7 G hG D4 hstage hL42 hCH F hF hq)
    (F_inf_B D4.toSPLNot3 hsetup hset hm2 hL42)

theorem spLocalLeafStd_of_L2_11 (h11 : IVK.Proofs2.IVK_11_1b_nat) (h2 : SPLLeafCtStd) :
    SPLocalLeafStd :=
  spLocalLeafStd_of_leaves splLeafSet h2 splLeafOrd
    (splLeafM2_of_AR2 splLeafA
      (splLeafR2_of_inputs (natModStmt_of_11_1b h11) splInL33 splInL34 splInC2))
    (splLeafIso_of_nat (natModStmt_of_11_1b h11))

@[expose] def SPLocalGlueStdFor (T : TwoCentralPred) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Stage12.Std G →
    ∀ (Gs : Type) [Group Gs] (F : Type) [Field F] [Finite F] (hF : 4 ≤ Nat.card F),
      Odd (Nat.card F) → Nonempty (Gs ≃* StatedProj (StatedSp 2 F)) →
        T G Gs → SPGlueData G F hF

theorem spLocalGlueStd_of_leaves (hT0 : SPSetupLeaf) (hT1 : SPLocalLeafStd) :
    SPLocalGlueStdFor (fun G _ Gs _ => LU.IsTwoCentralClassicalTypeCompat G Gs) := by
  intro G _ _ hS Gs _ F _ _ hF hodd e hT
  obtain ⟨z, S, K₁, K₂, t, hc, hs, hA⟩ := hT0 G hS.kps Gs F hF hodd e hT
  exact hT1 G hS F hF hodd z S K₁ K₂ t hc hs hA (sp_gen hF hodd hc hs hA)

theorem spLocalGlueStd_of_model (hM : SPModelLeaf) (hT1 : SPLocalLeafStd) :
    SPLocalGlueStdFor (fun G _ Gs _ => LU.IsTwoCentralClassicalTypeCompat G Gs) :=
  spLocalGlueStd_of_leaves (spSetupLeaf_of_model hM) hT1

@[expose] def S_stage5_SP_compat_Std : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Stage12.Std G →
    ∀ (Gs : Type) [Group Gs], (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 3 < p ^ f ∧ LieModel Gs .PSp 2 p f) →
      LU.IsTwoCentralClassicalTypeCompat G Gs → Nonempty (G ≃* Gs)

theorem sp_compat_Std_of_localGlueStd
    (h : SPLocalGlueStdFor fun G _ Gs _ => LU.IsTwoCentralClassicalTypeCompat G Gs) :
    S_stage5_SP_compat_Std := by
  intro G _ _ hS Gs _ ⟨p, f, hp, hp2, hq, hLie⟩ hT
  obtain ⟨K, _, _, hcard, ⟨e⟩⟩ := exists_model_of_lieModel_psp hLie
  have hodd : Odd (Nat.card K) := by
    rw [hcard]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hK4 : 4 ≤ Nat.card K := by rw [hcard]; omega
  have := hS.kps.1
  obtain ⟨e2⟩ := sp_of_glueData (h G hS Gs K hK4 hodd ⟨e⟩ hT)
  exact ⟨e2.trans e.symm⟩

end CFSG.GH74.GLS.SP.Local
