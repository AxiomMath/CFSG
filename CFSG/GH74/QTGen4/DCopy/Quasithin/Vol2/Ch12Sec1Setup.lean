module

public import CFSG.Quasithin.Vol2.Ch12Sec1Setup
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsCh7
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL4S331

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.Assembly.LowTwoRank (StatedSp)
open scoped IsMulCommutative

open Sec121

theorem stmt12_1_setup_of_F4
    (h323 : Stmt3_2_3) (h325 : Stmt3_2_5_F4) (h701 : Stmt7_0_1_F4) :
    ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V₀ : Subgroup G), FSU G T L V₀ →
      L = conjClosure L T → V₀ ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
      ∀ t ∈ T, t ∉ Subgroup.normalizer (V₀ : Set G) →
        conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)) = conjClosure V₀ T →
        conjClosure V₀ T = V₀ ⊔ CFSG.conjugate V₀ t → V₀ ⊓ CFSG.conjugate V₀ t = ⊥ →
        ¬ IsXSectionIso₂ L V₀ ⊥ (CFSG.conjugate V₀ t) ⊥ →
          Nonempty (G ≃* NativeSporadic.J4) ∨
          ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
            Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) ∧
            IsPrimeReduced 2 ((conjClosure V₀ T).subgroupOf (Subgroup.normalizer (L : Set G))) ∧
            Nonempty (↥(autOn (Subgroup.normalizer (L : Set G)) (conjClosure V₀ T)) ≃*
              MulAut (↥L ⧸ CFSG.pCore 2 ↥L)) ∧
            L ≤ Subgroup.normalizer (CFSG.conjugate V₀ t : Set G) ∧
            (∃ _ : IsMulCommutative ↥V₀, BinaryNaturalSL (V := ↥V₀) (autOn L V₀) ⊤ ⊥ n 1) ∧
            ∃ _ : IsMulCommutative ↥(CFSG.conjugate V₀ t),
              BinaryNaturalSL (V := ↥(CFSG.conjugate V₀ t)) (autOn L (CFSG.conjugate V₀ t)) ⊤ ⊥ n 1 := by
  intro G _ _ T L V₀ hfsu hL hC t ht htN hVM hVsum hVinf hniso
  have hL0 : fsuL0 T L = L := hL.symm
  have htV₀ : ¬ T ≤ Subgroup.normalizer (V₀ : Set G) := fun h => htN (h ht)

  obtain ⟨-, -, hcases⟩ := h325 G T L V₀ hfsu hL
  have hnot : ¬ V₀ = conjClosure V₀ T := fun h1 => htV₀ (by
    have h := le_normalizer_conjClosure V₀ T
    rwa [← h1] at h)
  have h3 := (hcases.resolve_left fun h => hnot h.1).resolve_left fun h => hnot h.1

  obtain ⟨hab, hVel, hN, h7⟩ := h701 G T L V₀ hfsu
  rcases h7 with hFF | hJ4 | ⟨a, ha, hO⟩ | hFour
  ·
    have hNM : Subgroup.normalizer (fsuV T V₀ : Set G) ≤ fsuM T L := by
      obtain ⟨⟨-, -⟩, ⟨-, huniq⟩, -⟩ := h323 G T L hfsu.simple hfsu.nonabelian hfsu.qtke
        hfsu.sylow hfsu.maximal hfsu.faithful hfsu.quasisimple
      have hVne : fsuV T V₀ ≠ ⊥ := fun h => hfsu.irrPlus.2.1 (le_bot_iff.mp
        (h ▸ le_conjClosure V₀ T))
      have hV2 : IsPGroup 2 ↥(fsuV T V₀) := fun x => ⟨1, Subtype.ext (by
        simpa using hVel.2 x x.2)⟩
      obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge
        (⟨fsuV T V₀, hVne, hV2, rfl⟩ : IsTwoLocal (Subgroup.normalizer (fsuV T V₀ : Set G)))
      have hM'eq := huniq M' hM' (hN.trans hle)
      rw [hM'eq] at hle
      exact hle
    rcases not_concl701FF_or_325 hfsu hL hVel hN hNM h3 with hnot | ⟨-, hlin⟩
    · exact absurd hFF hnot
    · right
      rcases hlin with ⟨⟨e⟩, hab₀, hnat₀⟩ | ⟨⟨e⟩, hab₀, hnat₀⟩
      · exact ⟨4, Or.inl rfl, setup_of_linear hfsu hL hC ht htN hVM hVsum hVinf hniso hVel hN
          (Or.inl rfl) e hnat₀ CFSG.Quasithin.H.L4.card_mulAut_SL_four⟩
      · exact ⟨5, Or.inr rfl, setup_of_linear hfsu hL hC ht htN hVM hVsum hVinf hniso hVel hN
          (Or.inr rfl) e hnat₀ VolI.autSLFiveTwo_holds⟩
  ·
    exact Or.inl hJ4.2.2.2.2.2
  ·
    exfalso
    rw [hL0] at hO
    refine not_binaryOrthogonalFour ha hO ?_
    rcases h3.2.1 with ⟨n, K, hK, hf, hc, he, -⟩ | ⟨n, K, hK, hf, hc, he, -⟩ | ⟨he, -⟩ |
      ⟨he, -⟩ | ⟨he, -⟩ | ⟨he, -⟩
    · exact Or.inl ⟨n, K, hK, hf, hc, he⟩
    · exact Or.inr (Or.inl ⟨n, K, hK, hf, hc, he⟩)
    · exact Or.inr (Or.inr (Or.inl he))
    · exact Or.inr (Or.inr (Or.inr (Or.inl he)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr he))))
  ·
    have h1 := hFour.1
    rw [hL0] at h1
    exact (lt_irrefl L h1).elim

end CFSG.Quasithin.H13
