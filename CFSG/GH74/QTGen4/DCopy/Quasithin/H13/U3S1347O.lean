module

public import CFSG.Quasithin.H13.U3S1347O
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S1347B

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem s1347_concl_ii_F4 (hedge : GoldschmidtEdgeBoundS3) (h1332 : Stmt13_3_2_F4)
    (h1228 : Stmt12_2_8_F4) (hC58 : TheoremC58) (h317 : AS317Sylow) (h56 : AsB56)
    (h135 : A6.Stmt13_3_5_F4) (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (h : Hyp1347 T H₁ H₂) {K₀ : Subgroup G} (hK₀ : K₀ ∈ cComp (H₁ ⊔ H₂))
    (hN : H₁ ⊔ H₂ ≤ normalizer (K₀ : Set G))
    (hloc : quasithinIsMaximalLocal T K₀ ∧ quasithinIsFaithfulLocal T K₀)
    (hLie : LieModel (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) .PSL 3 2 1) (hsup : H₁ ⊔ H₂ = K₀ ⊔ T) :
    Concl1347ii T H₁ H₂ := by
  obtain ⟨hH₀, -, -, hZsup, hZinf, hc₁, hc₂⟩ :=
    s1347_one_first_F4 hedge h1332 h1228 hC58 h317 h56 h135 S h
  have hKH := le_of_mem_cComp hK₀
  have hK := quotIso_of_lieModel hLie
  have hiso₀ := s1347_quotIso_H0 S h hN hK hsup
  have hsyl₀ : IsSylowTwoOf T (H₁ ⊔ H₂) := A5.isSylowTwoOf_of_le S.h13.sylow hH₀.1
  obtain ⟨ψ, hψ, hker, hTψ⟩ := I51.exists_model_hom hiso₀ hsyl₀ SL3.P0_sylow.1 SL3.P0_sylow.2
  have hcent := s1347_centralizer_eq S h hH₀ hiso₀
  have hKψ := s1347_map_K0 hψ hker hKH hN hK
  obtain ⟨σ, hσ⟩ := s1347_exists_action S h hH₀ hψ hker
  have h3₁ := s1347_relIndex_three S h.inH₁.1 h.s3₁
  have h3₂ := s1347_relIndex_three S h.inH₂.1 h.s3₂
  have hP₁ := s1347_map_parabolic hsyl₀ hker hTψ le_sup_left h.inH₁.1 h3₁
  have hP₂ := s1347_map_parabolic hsyl₀ hker hTψ le_sup_right h.inH₂.1 h3₂
  have hne := s1347_map_ne hsyl₀ hker le_sup_left le_sup_right h.inH₁.1 h.inH₂.1 h.ne

  obtain ⟨u, hu, hu1⟩ := exists_ne_one_of_card_two hc₁
  obtain ⟨v, hv, hv1⟩ := exists_ne_one_of_card_two hc₂
  have hZ := s1347_Z_eq hZsup hc₁ hc₂ hu hu1 hv hv1
  have huZ : u ∈ quasithinOmegaOneCenter T := (mem_inf.1 hu).1
  have hvZ : v ∈ quasithinOmegaOneCenter T := (mem_inf.1 hv).1
  have hu₂ : u ∉ centralizer (H₂ : Set G) := fun h' => hu1 (by
    have : u ∈ cZ T H₁ ⊓ cZ T H₂ := mem_inf.2 ⟨hu, mem_inf.2 ⟨huZ, h'⟩⟩
    rwa [hZinf, mem_bot] at this)
  have hv₁ : v ∉ centralizer (H₁ : Set G) := fun h' => hv1 (by
    have : v ∈ cZ T H₁ ⊓ cZ T H₂ := mem_inf.2 ⟨mem_inf.2 ⟨hvZ, h'⟩, hv⟩
    rwa [hZinf, mem_bot] at this)
  set uV : ↥(v0Of T H₁ H₂) := ⟨u, s1347_Z_le_V0 huZ⟩
  set vV : ↥(v0Of T H₁ H₂) := ⟨v, s1347_Z_le_V0 hvZ⟩

  have hmod : (IsSumNatDual3 K₀ (v0Of T H₁ H₂) ∨ IsFanoCore K₀ (v0Of T H₁ H₂)) ∧
      ∀ A : Subgroup G, IsMaxElemAbelian T A → A ≤ centralizer (v0Of T H₁ H₂ : Set G) := by
    rcases hP₂ with h2X | h2X
    · have h1X : (H₁.subgroupOf (H₁ ⊔ H₂)).map ψ = SL3.X2 :=
        hP₁.resolve_left fun h1X => hne (h1X.trans h2X.symm)
      refine s1347_module_core S hH₀ hKH hker hTψ hKψ hcent hσ le_sup_right le_sup_left h2X h1X
        (x := vV) (y := uV) (mem_inf.1 hv).2 (mem_inf.1 hu).2 hv₁ hu₂ fun z hz => ?_
      rcases hZ z hz with h' | h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr (Or.inl h'))
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr (Or.inr (h'.trans (s1347_Z_comm huZ hvZ))))
    · have h1X : (H₁.subgroupOf (H₁ ⊔ H₂)).map ψ = SL3.X1 :=
        hP₁.resolve_right fun h1X => hne (h1X.trans h2X.symm)
      exact s1347_module_core S hH₀ hKH hker hTψ hKψ hcent hσ le_sup_left le_sup_right h1X h2X
        (x := uV) (y := vV) (mem_inf.1 hu).2 (mem_inf.1 hv).2 hu₂ hv₁ hZ

  have hJ : thompsonJ T ≤ pCoreOf 2 (H₁ ⊔ H₂) := by
    rw [← s1347_T_inf_centralizer S h hH₀]
    exact iSup₂_le fun A hA => le_inf hA.1 (hmod.2 A hA)
  have hJeq := B6.thompsonJ_eq_of_le hJ (pCoreOf_two_le_of_isSylowTwoOf hsyl₀)
  have hJN : H₁ ⊔ H₂ ≤ normalizer (thompsonJ T : Set G) := by
    rw [← hJeq]
    exact (le_normalizer_pCoreOf 2 (H₁ ⊔ H₂)).trans (normalizer_le_normalizer_thompsonJ _)
  exact ⟨K₀, hsup, hK₀, hloc.1, hloc.2, hK, hJN, hmod.1⟩

end CFSG.Quasithin.H13.U3
