module

public import CFSG.ClassicalInvolution.Q3.Q3T8E4A
import CFSG.ClassicalInvolution.Asc77.AscT8X2Eng

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3CL.Wyl

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Asc77.MuTab (muTabElt muTabElt_mem)
open CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.Q3CL.T8R.Loc (Std8Core partIHyp_of_std8 stdRepK)

section Cent

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}
  (hP : Q3CL.PartIHypG Ω) (hW : W ∈ WSet Ω)
include hP hW

theorem exists_not_conn_at (hnc : ¬ DbarConnected Ω W) (d : ↥(muGroup Ω W)) :
    ∃ a ∈ muDelta Ω W, ¬ Star3T.Conn (muDelta Ω W) d a := by
  obtain ⟨d₁, hd₁, a₁, ha₁, hc⟩ := Q3T8.Asc77.Thompson.exists_not_conn_of_not_connected hP.hyp hW hnc
  by_cases h : Star3T.Conn (muDelta Ω W) d d₁
  · exact ⟨a₁, ha₁, fun h' => hc (h.symm.trans h')⟩
  · exact ⟨d₁, hd₁, h⟩

theorem muIso_of_cent (hnc : ¬ DbarConnected Ω W) (ρ : Rep Ω W) :
    ((Star3T.cent (muDelta Ω W) (muTabElt ρ)).ncard = 1 → MuIsoS3 Ω W) ∧
    ((Star3T.cent (muDelta Ω W) (muTabElt ρ)).ncard = 2 → MuIsoS4 Ω W) ∧
    ((Star3T.cent (muDelta Ω W) (muTabElt ρ)).ncard = 4 → MuIsoWylD4 Ω W) := by
  have hTT := Q3T8.Asc77.Thompson.isTT_muDelta hP.hyp hW (Q3CL.thompsonCube hP W hW)
  have hS := Q3T8.Asc77.Thompson.isStar_muDelta hP.hyp hW (Q3T8.Asc77.thompsonStar G Ω hP W hW)
  obtain ⟨a, ha, hconn⟩ := exists_not_conn_at hP hW hnc (muTabElt ρ)
  have hd := muTabElt_mem ρ
  refine ⟨fun hk => ?_, fun hk => ?_, fun hk => ?_⟩
  · obtain ⟨e, -⟩ := Star3T.exists_mulEquiv_perm_three hTT hS hd ha hconn hk
    exact ⟨e⟩
  · obtain ⟨e, -⟩ := Star3T.exists_mulEquiv_perm_four hTT hS hd ha hconn hk
    exact ⟨e⟩
  · rcases Q3T8.Asc77.thompsonClique G Ω hP W hW hnc (muTabElt ρ) hd with h | h | ⟨-, hcard⟩
    · omega
    · omega
    · exact Star3T.nonempty_mulEquiv_of_card_four hTT hS hd ha hconn hk hcard
        (M := coxeterD4) (fun i j => by fin_cases i <;> fin_cases j <;> rfl)
        coxeterD4.toCoxeterSystem

end Cent

theorem exists_four {α : Type*} {C : Set α} (hC : C.ncard = 4) {a b : α}
    (ha : a ∈ C) (hb : b ∈ C) (hab : a ≠ b) :
    ∃ c d : α, C = {a, b, c, d} ∧ c ≠ d ∧ c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b :=
  CFSG.ClassicalInvolution.Asc77.T8X.exists_four_gen hC ha hb hab

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

omit [Finite G] in
theorem not_muIsoS3_or_S4 (h : MuIsoWylD4 Ω W) : ¬ MuIsoS3 Ω W ∧ ¬ MuIsoS4 Ω W := by
  obtain ⟨e⟩ := h
  constructor
  · rintro ⟨e3⟩
    exact MuTab.not_wyl_equiv_perm3 ⟨e.symm.trans e3⟩
  · rintro ⟨e4⟩
    exact MuTab.not_wyl_equiv_perm4 ⟨e.symm.trans e4⟩

theorem not_dbarConnected_of_ne (hs : Std8Core Ω K J S R T W z t)
    (hne : dComp Ω K ≠ dstarComp Ω K) : ¬ DbarConnected Ω W :=
  Q3T8.Asc77.thompsonGraphAll G Ω (partIHyp_of_std8 hs) hs.stand.mem hne hs.hW.1

theorem ncard_cent_eq_four (hs : Std8Core Ω K J S R T W z t) (hμ : MuIsoWylD4 Ω W)
    (hnc : ¬ DbarConnected Ω W) (ρ : Rep Ω W) :
    (Star3T.cent (muDelta Ω W) (muTabElt ρ)).ncard = 4 := by
  have hP := partIHyp_of_std8 hs
  have hW : W ∈ WSet Ω := hs.hW.1
  have hnot := not_muIsoS3_or_S4 hμ
  have key := muIso_of_cent hP hW hnc ρ
  rcases Q3T8.Asc77.thompsonClique G Ω hP W hW hnc (muTabElt ρ) (muTabElt_mem ρ) with
    h | h | ⟨h, -⟩
  · exact absurd (key.1 h) hnot.1
  · exact absurd (key.2.1 h) hnot.2
  · exact h

theorem exists_frame (hs : Std8Core Ω K J S R T W z t) (hμ : MuIsoWylD4 Ω W)
    (hnc : ¬ DbarConnected Ω W) :
    ∃ ρ : Fin 4 → Rep Ω W, (ρ 0).K = K ∧ (ρ 1).K = J ∧ (∀ i j, i ≠ j → (ρ i).K ≠ (ρ j).K) ∧
      (∀ i j, i ≠ j → (ρ j).K ∈ omegaNbr Ω (ρ i).K) ∧
      ∀ σ : Rep Ω W, (σ.K = K ∨ σ.K ∈ omegaNbr Ω K) → ∃ i, σ.K = (ρ i).K := by
  classical
  have hΩ : HypOmegaGen Ω := hs.stand.hyp
  have hP := partIHyp_of_std8 hs
  have hW : W ∈ WSet Ω := hs.hW.1
  have hTT := Q3T8.Asc77.Thompson.isTT_muDelta hΩ hW (Q3CL.thompsonCube hP W hW)
  have hSt := Q3T8.Asc77.Thompson.isStar_muDelta hΩ hW (Q3T8.Asc77.thompsonStar G Ω hP W hW)
  set ρ0 := stdRepK hs
  set ρ1 := Q3CL.T8R.Loc.stdRepJ hs
  have hK0 : ρ0.K = K := rfl
  have hK1 : ρ1.K = J := rfl
  have hne01 : ρ0.K ≠ ρ1.K := by rw [hK0, hK1]; exact hs.hJ.2.1.symm
  have hd01 : muTabElt ρ0 ≠ muTabElt ρ1 := fun h =>
    hne01 ((Q3T8.Asc77.MuTab.muTabElt_eq_iff hP hW ρ0 ρ1).mp h)
  set C := Star3T.cent (muDelta Ω W) (muTabElt ρ0) with hCdef
  have hC4 : C.ncard = 4 := ncard_cent_eq_four hs hμ hnc ρ0
  have h0C : muTabElt ρ0 ∈ C := Star3T.self_mem_cent (muTabElt_mem ρ0)
  have h1C : muTabElt ρ1 ∈ C := ⟨muTabElt_mem ρ1,
    ((Q3T8.Asc77.MuTab.muTab_commute_iff hP hW ρ0 ρ1 hne01).mpr
      (by rw [hK0, hK1]; exact hs.hJ)).symm⟩
  obtain ⟨c, d, hCe, hcd, hca, hcb, hda, hdb⟩ := exists_four hC4 h0C h1C hd01
  have hcC : c ∈ C := by rw [hCe]; simp
  have hdC : d ∈ C := by rw [hCe]; simp
  obtain ⟨ρ2, hρ2⟩ := MuTab.exists_rep_of_mem_muDelta hcC.1
  obtain ⟨ρ3, hρ3⟩ := MuTab.exists_rep_of_mem_muDelta hdC.1
  let ρ : Fin 4 → Rep Ω W := ![ρ0, ρ1, ρ2, ρ3]
  let dd : Fin 4 → ↥(muGroup Ω W) := ![muTabElt ρ0, muTabElt ρ1, c, d]
  have hdd : ∀ i, muTabElt (ρ i) = dd i := by
    intro i; fin_cases i
    · rfl
    · rfl
    · exact hρ2.symm
    · exact hρ3.symm
  have hddC : ∀ i, dd i ∈ C := by
    intro i; fin_cases i
    · exact h0C
    · exact h1C
    · exact hcC
    · exact hdC
  have hddinj : ∀ i j, i ≠ j → dd i ≠ dd j := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | skip
    all_goals first
      | exact hd01 | exact fun h => hd01 h.symm
      | exact fun h => hca h.symm | exact hca | exact fun h => hcb h.symm | exact hcb
      | exact fun h => hda h.symm | exact hda | exact fun h => hdb h.symm | exact hdb
      | exact hcd | exact fun h => hcd h.symm
  have hKne : ∀ i j, i ≠ j → (ρ i).K ≠ (ρ j).K := by
    intro i j hij h
    exact hddinj i j hij (by
      rw [← hdd i, ← hdd j]
      exact (Q3T8.Asc77.MuTab.muTabElt_eq_iff hP hW _ _).mpr h)
  obtain ⟨a₁, ha₁, hn₁⟩ := exists_not_conn_at hP hW hnc (muTabElt ρ0)
  have hcommdd : ∀ i j, dd i * dd j = dd j * dd i := fun i j =>
    hTT.isClique_cent hSt (muTabElt_mem ρ0) ha₁ hn₁ (hddC i) (hddC j)
  refine ⟨ρ, hK0, hK1, hKne, ?_, ?_⟩
  · intro i j hij
    exact (Q3T8.Asc77.MuTab.muTab_commute_iff hP hW (ρ i) (ρ j) (hKne i j hij)).mp
      (by rw [hdd i, hdd j]; exact hcommdd i j)
  · intro σ hσ
    have hσC : muTabElt σ ∈ C := by
      refine ⟨muTabElt_mem σ, ?_⟩
      rcases hσ with h | h
      · have : muTabElt σ = muTabElt ρ0 :=
          (Q3T8.Asc77.MuTab.muTabElt_eq_iff hP hW σ ρ0).mpr (by rw [h, hK0])
        rw [this]
      · by_cases hσK : ρ0.K = σ.K
        · have : muTabElt σ = muTabElt ρ0 :=
            (Q3T8.Asc77.MuTab.muTabElt_eq_iff hP hW σ ρ0).mpr hσK.symm
          rw [this]
        · exact ((Q3T8.Asc77.MuTab.muTab_commute_iff hP hW ρ0 σ hσK).mpr
            (by rw [hK0]; exact h)).symm
    rw [hCe] at hσC
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hσC
    rcases hσC with h | h | h | h
    · exact ⟨0, (Q3T8.Asc77.MuTab.muTabElt_eq_iff hP hW σ ρ0).mp h⟩
    · exact ⟨1, (Q3T8.Asc77.MuTab.muTabElt_eq_iff hP hW σ ρ1).mp h⟩
    · exact ⟨2, (Q3T8.Asc77.MuTab.muTabElt_eq_iff hP hW σ ρ2).mp (h.trans hρ2)⟩
    · exact ⟨3, (Q3T8.Asc77.MuTab.muTabElt_eq_iff hP hW σ ρ3).mp (h.trans hρ3)⟩

theorem exists_frame_closed (hs : Std8Core Ω K J S R T W z t) (hμ : MuIsoWylD4 Ω W)
    (hnc : ¬ DbarConnected Ω W) :
    ∃ ρ : Fin 4 → Rep Ω W, (ρ 0).K = K ∧ (ρ 1).K = J ∧ (∀ i j, i ≠ j → (ρ i).K ≠ (ρ j).K) ∧
      (∀ i j, i ≠ j → (ρ j).K ∈ omegaNbr Ω (ρ i).K) ∧
      ∀ (σ : Rep Ω W) (i : Fin 4), (σ.K = (ρ i).K ∨ σ.K ∈ omegaNbr Ω (ρ i).K) →
        ∃ j, σ.K = (ρ j).K := by
  classical
  obtain ⟨ρ, h0, h1, hne, hadj, -⟩ := exists_frame hs hμ hnc
  refine ⟨ρ, h0, h1, hne, hadj, ?_⟩
  intro σ i hσ
  have hP := partIHyp_of_std8 hs
  have hW : W ∈ WSet Ω := hs.hW.1
  have hcard := ncard_cent_eq_four hs hμ hnc (ρ i)
  have hinj : Function.Injective (fun j : Fin 4 => muTabElt (ρ j)) := by
    intro j j' hjj'
    by_contra hne'
    exact hne j j' hne' ((Q3T8.Asc77.MuTab.muTabElt_eq_iff hP hW (ρ j) (ρ j')).mp hjj')
  have hcomm : ∀ j : Fin 4, muTabElt (ρ j) ∈ Star3T.cent (muDelta Ω W) (muTabElt (ρ i)) := by
    intro j
    refine ⟨muTabElt_mem (ρ j), ?_⟩
    by_cases hji : j = i
    · rw [hji]
    · exact ((Q3T8.Asc77.MuTab.muTab_commute_iff hP hW (ρ i) (ρ j)
        (hne i j (Ne.symm hji))).mpr (hadj i j (Ne.symm hji))).symm
  have himg : (Set.range fun j : Fin 4 => muTabElt (ρ j)).ncard = 4 := by
    rw [← Set.image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ]
    simp
  have hsub : (Set.range fun j : Fin 4 => muTabElt (ρ j)) ⊆
      Star3T.cent (muDelta Ω W) (muTabElt (ρ i)) := by
    rintro _ ⟨j, rfl⟩
    exact hcomm j
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [himg, hcard]) (Set.toFinite _)
  have hσC : muTabElt σ ∈ Star3T.cent (muDelta Ω W) (muTabElt (ρ i)) := by
    refine ⟨muTabElt_mem σ, ?_⟩
    by_cases hσi : σ.K = (ρ i).K
    · have : muTabElt σ = muTabElt (ρ i) :=
        (Q3T8.Asc77.MuTab.muTabElt_eq_iff hP hW σ (ρ i)).mpr hσi
      rw [this]
    · exact ((Q3T8.Asc77.MuTab.muTab_commute_iff hP hW (ρ i) σ (Ne.symm hσi)).mpr
        (hσ.resolve_left hσi)).symm
  rw [← heq] at hσC
  obtain ⟨j, hj⟩ := hσC
  exact ⟨j, (Q3T8.Asc77.MuTab.muTabElt_eq_iff hP hW σ (ρ j)).mp hj.symm⟩


theorem mem_W_of_uniqueInvolution (c : Q3CL.Thompson.Ctx Ω W) (σ : Rep Ω W) {v : G}
    (hv : IsUniqueInvolution σ.K v) : v ∈ W :=
  (Q3CL.Thompson.uniqueInvolution_mem_W c.hΩ c.hW σ.hK σ.hR σ.hRK hv).2

theorem rep_le_centralizer (c : Q3CL.Thompson.Ctx Ω W) (ρ σ : Rep Ω W)
    (hσ : σ.K = ρ.K ∨ σ.K ∈ omegaNbr Ω ρ.K) {v : G} (hv : IsUniqueInvolution σ.K v) :
    ρ.R ≤ Subgroup.centralizer ({v} : Set G) := by
  intro y hy
  rw [Subgroup.mem_centralizer_singleton_iff]
  rcases hσ with h | h
  · rw [h] at hv
    have := hv.conj_eq (n := y) (conjSub_eq_self_of_mem (ρ.hRK.1 hy))
    calc y * v = (y * v * y⁻¹) * y := by group
      _ = v * y := by rw [this]
  · have hvW : v ∈ σ.K ⊓ W :=
      Q3CL.Thompson.uniqueInvolution_mem_W c.hΩ c.hW σ.hK σ.hR σ.hRK hv
    have hrv : ρ.r * v = v * ρ.r := c.centralizes ρ σ h hvW
    by_cases hyW : y ∈ W
    · exact c.comm_W y hyW v hvW.2
    · have hw : ρ.r⁻¹ * y ∈ W :=
        Q3CL.Thompson.D_inv_mul_mem c.hΩ c.hW ρ.hR ρ.hr hy ρ.hrW hyW
      have hwv : (ρ.r⁻¹ * y) * v = v * (ρ.r⁻¹ * y) := c.comm_W _ hw v hvW.2
      have hy' : y = ρ.r * (ρ.r⁻¹ * y) := by group
      calc y * v = ρ.r * ((ρ.r⁻¹ * y) * v) := by rw [hy']; group
        _ = ρ.r * (v * (ρ.r⁻¹ * y)) := by rw [hwv]
        _ = (ρ.r * v) * (ρ.r⁻¹ * y) := by group
        _ = (v * ρ.r) * (ρ.r⁻¹ * y) := by rw [hrv]
        _ = v * y := by group

theorem rep_comm_frame_prod (c : Q3CL.Thompson.Ctx Ω W) (ρ : Fin 4 → Rep Ω W)
    (hadj : ∀ i j, i ≠ j → (ρ j).K ∈ omegaNbr Ω (ρ i).K)
    (hclos : ∀ (σ : Rep Ω W) (i : Fin 4), (σ.K = (ρ i).K ∨ σ.K ∈ omegaNbr Ω (ρ i).K) →
      ∃ j, σ.K = (ρ j).K)
    {zz : Fin 4 → G} (hz : ∀ i, IsUniqueInvolution (ρ i).K (zz i)) (σ : Rep Ω W)
    (i j : Fin 4) : σ.r * (zz i * zz j) = (zz i * zz j) * σ.r := by
  by_cases hin : ∃ s, σ.K = (ρ s).K
  · obtain ⟨s, hs⟩ := hin
    have key : ∀ k, σ.r * zz k = zz k * σ.r := by
      intro k
      have hσ : (ρ k).K = σ.K ∨ (ρ k).K ∈ omegaNbr Ω σ.K := by
        by_cases hks : k = s
        · exact Or.inl (by rw [hks, hs])
        · exact Or.inr (by rw [hs]; exact hadj s k (Ne.symm hks))
      have hR := rep_le_centralizer c σ (ρ k) hσ (hz k)
      exact Subgroup.mem_centralizer_singleton_iff.mp (hR σ.hr)
    calc σ.r * (zz i * zz j) = (σ.r * zz i) * zz j := by group
      _ = (zz i * σ.r) * zz j := by rw [key i]
      _ = zz i * (σ.r * zz j) := by group
      _ = zz i * (zz j * σ.r) := by rw [key j]
      _ = (zz i * zz j) * σ.r := by group
  · push Not at hin
    have hnot : ∀ s, σ.K ∉ omegaNbr Ω (ρ s).K := by
      intro s hmem
      obtain ⟨j, hj⟩ := hclos σ s (Or.inr hmem)
      exact hin j hj
    have hnot' : ∀ s, (ρ s).K ∉ omegaNbr Ω σ.K := by
      intro s hmem
      apply hnot s
      have h1 : σ.img * (ρ s).img = (ρ s).img * σ.img := c.comm_of_omega σ (ρ s) hmem
      exact c.omega_of_comm (ρ s) σ (Ne.symm (hin s)) h1.symm
    obtain ⟨zσ, hzσ⟩ := Sec6Gen.exists_uniqueInvolution c.hΩ σ.hK
    have hzσW : zσ ∈ W := mem_W_of_uniqueInvolution c σ hzσ
    have hzW : ∀ k, zz k ∈ W := fun k => mem_W_of_uniqueInvolution c (ρ k) (hz k)
    have hconj : ∀ k, σ.r * zz k * σ.r⁻¹ = zσ * zz k := fun k =>
      c.conj_involution σ (ρ k) (hin k) (hnot' k) hzσ (hz k)
    have hcσ : ∀ k, zσ * zz k = zz k * zσ := fun k => c.comm_W _ hzσW _ (hzW k)
    have h2 : σ.r * (zz i * zz j) * σ.r⁻¹ = zz i * zz j := by
      calc σ.r * (zz i * zz j) * σ.r⁻¹ = (σ.r * zz i * σ.r⁻¹) * (σ.r * zz j * σ.r⁻¹) := by
            group
        _ = (zσ * zz i) * (zσ * zz j) := by rw [hconj i, hconj j]
        _ = zσ * (zz i * zσ) * zz j := by group
        _ = zσ * (zσ * zz i) * zz j := by rw [hcσ i]
        _ = (zσ * zσ) * zz i * zz j := by group
        _ = zz i * zz j := by rw [hzσ.sq, one_mul]
    calc σ.r * (zz i * zz j) = (σ.r * (zz i * zz j) * σ.r⁻¹) * σ.r := by group
      _ = (zz i * zz j) * σ.r := by rw [h2]

theorem commute_frame_prod_of_mem_DSet (c : Q3CL.Thompson.Ctx Ω W) (ρ : Fin 4 → Rep Ω W)
    (hadj : ∀ i j, i ≠ j → (ρ j).K ∈ omegaNbr Ω (ρ i).K)
    (hclos : ∀ (σ : Rep Ω W) (i : Fin 4), (σ.K = (ρ i).K ∨ σ.K ∈ omegaNbr Ω (ρ i).K) →
      ∃ j, σ.K = (ρ j).K)
    {zz : Fin 4 → G} (hz : ∀ i, IsUniqueInvolution (ρ i).K (zz i)) {R'' : Subgroup G}
    (hR : R'' ∈ DSet Ω W) {x : G} (hx : x ∈ R'') (i j : Fin 4) :
    x * (zz i * zz j) = (zz i * zz j) * x := by
  by_cases hxW : x ∈ W
  · exact c.comm_W x hxW _ (W.mul_mem (mem_W_of_uniqueInvolution c (ρ i) (hz i))
      (mem_W_of_uniqueInvolution c (ρ j) (hz j)))
  · obtain ⟨K'', hK'', hRK⟩ := exists_isSylow2In_of_mem_RSet hR.1
    exact rep_comm_frame_prod c ρ hadj hclos hz ⟨K'', R'', x, hK'', hR, hRK, hx, hxW⟩ i j

end CFSG.ClassicalInvolution.Q3.Q3CL.Wyl
