module

public import CFSG.ClassicalInvolution.Q3.Q3AMLY4P02

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Asc77.AscP1Nine3
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T8W
  CFSG.ClassicalInvolution.Q3.Q3NL
open scoped commutatorElement

section Sylow

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J : Subgroup G}
  {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem conjSub_eq_of_mem_centralizer_std8 (hs : Std8 Ω K J S R T W z t) {g : G}
    (hg : g ∈ Subgroup.centralizer ({z} : Set G)) : conjSub g K = K :=
  layerCentralizer_conjSub_eq hs hs.stand.mem hs.hz g hg

theorem mem_centralizer_of_mem_K_std8 (hs : Std8 Ω K J S R T W z t) {k : G} (hk : k ∈ K) :
    k ∈ Subgroup.centralizer ({z} : Set G) :=
  mem_centralizer_of_conjSub_eq hs.hz (conjSub_eq_self_of_mem hk)

theorem layer_exists_sylow_RT (hs : Std8 Ω K J S R T W z t) :
    ∃ S₂ : Sylow 2 G, R ≤ (S₂ : Subgroup G) ∧ T ≤ (S₂ : Subgroup G) ∧
      IsSylow2In ((S₂ : Subgroup G) ⊓ nbrLayer Ω K z) (nbrLayer Ω K z) := by
  set Y : Subgroup G := nbrLayer Ω K z with hYdef
  have hRN : ∀ r ∈ R, conjSub r Y = Y := fun r hr =>
    mem_normalizer_iff_conjSub_eq.mp (centralizer_le_normalizer_nbrLayer_of_std8 hs hs.stand.mem
      hs.hz (mem_centralizer_of_mem_K_std8 hs (hs.hR.2.1 hr)))
  have hYN : Y ⊔ R ≤ Subgroup.normalizer (Y : Set G) :=
    sup_le Subgroup.le_normalizer
      (fun r hr => mem_normalizer_iff_conjSub_eq.mpr (hRN r hr))
  have hTY : T ≤ Y := (layerT_le_exactCore hs).trans (exactCore3_le_nbrLayer hs.hJ)
  have hRT : IsPGroup 2 ↥(R ⊔ T) :=
    S.isPGroup'.to_le (sup_le hs.hR.2.2 hs.hT.2.2)
  have hRTle : R ⊔ T ≤ Y ⊔ R := sup_le le_sup_right (hTY.trans le_sup_left)
  obtain ⟨V, hV, hRTV⟩ := IsSylow2In.exists_ge hRT hRTle
  have hVY : IsSylow2In (V ⊓ Y) Y :=
    AscP1Nine3.isSylow2In_inf_of_le_normalizer' hV le_sup_left hYN
  obtain ⟨S₂, hS₂⟩ := hV.2.1.exists_le_sylow
  have heq : (S₂ : Subgroup G) ⊓ Y = V ⊓ Y :=
    hVY.2.2 _ inf_le_right S₂.isPGroup'.to_inf_left (inf_le_inf_right Y hS₂)
  exact ⟨S₂, le_sup_left.trans (hRTV.trans hS₂), le_sup_right.trans (hRTV.trans hS₂),
    heq ▸ hVY⟩

theorem eq_J_of_mem_omegaNbr (hs : Std8 Ω K J S R T W z t) (hE : MuIsoE4 Ω W)
    {S₂ : Sylow 2 G} (hRS₂ : R ≤ (S₂ : Subgroup G)) (hTS₂ : T ≤ (S₂ : Subgroup G))
    {L : Subgroup G} (hL : L ∈ omegaNbr Ω K) (hcard : 2 < Nat.card ↥(L ⊓ (S₂ : Subgroup G))) :
    L = J := by
  classical
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hLΩ : L ∈ Ω := hL.1
  have hP : PartIHyp Ω := T8.partIHyp_of_std8 hs
  obtain ⟨η₂, hη₂, hinv₂⟩ := Disconnected.AschTight.Sec6Gen.exists_invariant_mem_etaSet hΩ S₂
  have hη₂G : η₂ ∈ etaG Ω := ⟨S₂, hη₂, hinv₂⟩
  set W₂ : Subgroup G := ⨆ U ∈ η₂, U with hW₂def
  have hW₂ : W₂ ∈ Asc77.WSet Ω := ⟨η₂, hη₂G, rfl⟩
  have hSN : ∀ s ∈ (S₂ : Subgroup G), s ∈ Subgroup.normalizer (W₂ : Set G) := fun s hs' =>
    mem_normalizer_iff_conjSub_eq.mpr (T7A.conjSub_eta_eq hinv₂ hs')
  have hηS : ∀ V ∈ η₂, V ≤ (S₂ : Subgroup G) := fun V hV => (hη₂.1 hV).2
  have c₂ : Q3CL.Thompson.Ctx Ω W₂ := MuTab.muTabCtx hP hW₂
  have hE₂ : MuIsoE4 Ω W₂ := by
    obtain ⟨φ⟩ := hE
    obtain ⟨e⟩ := l7_5_2_proved G Ω hs.stand.modU W₂ hW₂ W hs.hW.1
    exact ⟨e.trans φ⟩
  have hRsyl : IsSylow2In R K := Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK
      hs.hR.1 hs.hR.2.1
  have hTsyl : IsSylow2In T J := Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hJΩ
      hs.hT.1 hs.hT.2.1
  have hRD : R ∈ DSet Ω W₂ := ⟨hs.hR.1, fun x hx => hSN x (hRS₂ hx)⟩
  have hTD : T ∈ DSet Ω W₂ := ⟨hs.hT.1, fun x hx => hSN x (hTS₂ hx)⟩
  obtain ⟨r₀, hr₀R, hr₀W⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW₂ hRD
  obtain ⟨t₀, ht₀T, ht₀W⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW₂ hTD
  let ρK : Rep Ω W₂ := ⟨K, R, r₀, hK, hRD, hRsyl, hr₀R, hr₀W⟩
  let ρJ : Rep Ω W₂ := ⟨J, T, t₀, hJΩ, hTD, hTsyl, ht₀T, ht₀W⟩
  have h611 : L ⊓ W₂ ∈ η₂ := l6_11_proved G Ω hΩ S₂ η₂ hη₂G hηS L hLΩ hcard
  have hV₀U : L ⊓ W₂ ∈ USet Ω := (hη₂.1 h611).1
  obtain ⟨zL, hzL⟩ := hΩ.exists_uniqueInvolution hLΩ
  have hV₀2 : IsPGroup 2 ↥(L ⊓ W₂) := hΩ.isPGroup_of_mem_USet hV₀U
  have hV₀4 : 4 ≤ Nat.card ↥(L ⊓ W₂) := by
    obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := hΩ.exists_data_of_mem_USet hV₀U
    exact h4
  have hzLV : zL ∈ L ⊓ W₂ := T3.mem_of_isPGroup hzL inf_le_left hV₀2 (by omega)
  obtain ⟨ρL, hρL⟩ := c₂.exists_rep_of_involution_mem hs.stand.cls hLΩ hzL hzLV.2
  have hρLL : ρL.K = L := hρL
  by_contra hLJ
  exact no_three_reps_E4 hP hW₂ hE₂ ρK ρJ ρL (Ne.symm hs.hJ.2.1)
    (by show K ≠ ρL.K; rw [hρLL]; exact Ne.symm hL.2.1)
    (by show J ≠ ρL.K; rw [hρLL]; exact Ne.symm hLJ)

theorem layer_sY_normalizes_J (hs : Std8 Ω K J S R T W z t) (hE : MuIsoE4 Ω W)
    {S₂ : Sylow 2 G} (hRS₂ : R ≤ (S₂ : Subgroup G)) (hTS₂ : T ≤ (S₂ : Subgroup G)) {s : G}
    (hsS : s ∈ (S₂ : Subgroup G)) (hsY : s ∈ nbrLayer Ω K z) : conjSub s J = J := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hsC : s ∈ Subgroup.centralizer ({z} : Set G) := nbrLayer_le_centralizer Ω K z hsY
  have hJs : conjSub s J ∈ omegaNbr Ω K :=
    conjSub_mem_omegaNbr_of_conjSub_eq hΩ (conjSub_eq_of_mem_centralizer_std8 hs hsC) hs.hJ
  have h8 : 8 ≤ Nat.card T := hΩ.eight_le_of_mem_RSet hs.hT.1
  have hle : conjSub s (J ⊓ (S₂ : Subgroup G)) ≤ conjSub s J ⊓ (S₂ : Subgroup G) := by
    intro y hy
    have h1 := mem_conjSub_iff.mp hy
    refine ⟨mem_conjSub_iff.mpr h1.1, ?_⟩
    have h2 := h1.2
    have : y = s * (s⁻¹ * y * s) * s⁻¹ := by group
    rw [this]
    exact (S₂ : Subgroup G).mul_mem ((S₂ : Subgroup G).mul_mem hsS h2)
      ((S₂ : Subgroup G).inv_mem hsS)
  have hcardT : Nat.card T ≤ Nat.card ↥(J ⊓ (S₂ : Subgroup G)) :=
    Subgroup.card_le_of_le (le_inf hs.hT.2.1 hTS₂)
  have hcard : 2 < Nat.card ↥(conjSub s J ⊓ (S₂ : Subgroup G)) := by
    have h1 := Subgroup.card_le_of_le hle
    have h2 : Nat.card ↥(conjSub s (J ⊓ (S₂ : Subgroup G))) =
        Nat.card ↥(J ⊓ (S₂ : Subgroup G)) := T8S2.natCard_conjSub_eq s _
    omega
  exact eq_J_of_mem_omegaNbr hs hE hRS₂ hTS₂ hJs hcard

theorem layer_sY_centralizes_t (hs : Std8 Ω K J S R T W z t) (hE : MuIsoE4 Ω W)
    {S₂ : Sylow 2 G} (hRS₂ : R ≤ (S₂ : Subgroup G)) (hTS₂ : T ≤ (S₂ : Subgroup G)) {s : G}
    (hsS : s ∈ (S₂ : Subgroup G)) (hsY : s ∈ nbrLayer Ω K z) : s * t * s⁻¹ = t :=
  hs.ht.conj_eq (layer_sY_normalizes_J hs hE hRS₂ hTS₂ hsS hsY)

end Sylow

end CFSG.ClassicalInvolution.Q3.Q3AM
