module

public import CFSG.ClassicalInvolution.Asc77.AscT8X2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.MuTab

namespace T8YY


variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem exists_frame_closed (hs : Std8 p f Ω K J S R T W z t) (hμ : MuIsoWylD4 Ω W)
    (hnc : ¬ DbarConnected Ω W) :
    ∃ ρ : Fin 4 → Rep Ω W, (ρ 0).K = K ∧ (ρ 1).K = J ∧ (∀ i j, i ≠ j → (ρ i).K ≠ (ρ j).K) ∧
      (∀ i j, i ≠ j → (ρ j).K ∈ omegaNbr Ω (ρ i).K) ∧
      ∀ (σ : Rep Ω W) (i : Fin 4), (σ.K = (ρ i).K ∨ σ.K ∈ omegaNbr Ω (ρ i).K) →
        ∃ j, σ.K = (ρ j).K := by
  classical
  obtain ⟨ρ, h0, h1, hne, hadj, -⟩ := T8X.exists_frame hs hμ hnc
  refine ⟨ρ, h0, h1, hne, hadj, ?_⟩
  intro σ i hσ
  have hP := T8.partIHyp_of_std8 hs
  have hW : W ∈ WSet Ω := hs.hW.1
  have hcard := T8X.ncard_cent_eq_four hs hμ hnc (ρ i)
  have hinj : Function.Injective (fun j : Fin 4 => muTabElt (ρ j)) := by
    intro j j' hjj'
    by_contra hne'
    exact hne j j' hne' ((muTabElt_eq_iff hP hW (ρ j) (ρ j')).mp hjj')
  have hcomm : ∀ j : Fin 4, muTabElt (ρ j) ∈ Star3T.cent (muDelta Ω W) (muTabElt (ρ i)) := by
    intro j
    refine ⟨muTabElt_mem (ρ j), ?_⟩
    by_cases hji : j = i
    · rw [hji]
    · exact ((muTab_commute_iff hP hW (ρ i) (ρ j) (hne i j (Ne.symm hji))).mpr
        (hadj i j (Ne.symm hji))).symm
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
    · have : muTabElt σ = muTabElt (ρ i) := (muTabElt_eq_iff hP hW σ (ρ i)).mpr hσi
      rw [this]
    · exact ((muTab_commute_iff hP hW (ρ i) σ (Ne.symm hσi)).mpr (hσ.resolve_left hσi)).symm
  rw [← heq] at hσC
  obtain ⟨j, hj⟩ := hσC
  exact ⟨j, (muTabElt_eq_iff hP hW σ (ρ j)).mp hj.symm⟩


theorem mem_W_of_uniqueInvolution (c : Ctx p f Ω W) (σ : Rep Ω W) {v : G}
    (hv : IsUniqueInvolution σ.K v) : v ∈ W :=
  (uniqueInvolution_mem_W c.hp c.hq c.hΩ c.hW σ.hK σ.hR σ.hRK hv).2

theorem rep_comm_frame_prod (c : Ctx p f Ω W) (ρ : Fin 4 → Rep Ω W)
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
      have hR := T8.rep_le_centralizer c σ (ρ k) hσ (hz k)
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
    obtain ⟨zσ, hzσ⟩ := c.hΩ.exists_uniqueInvolution c.hp c.hq σ.hK
    have hzσW : zσ ∈ W := mem_W_of_uniqueInvolution c σ hzσ
    have hzW : ∀ k, zz k ∈ W := fun k => mem_W_of_uniqueInvolution c (ρ k) (hz k)
    have hconj : ∀ k, σ.r * zz k * σ.r⁻¹ = zσ * zz k := fun k =>
      c.conj_involution σ (ρ k) (hin k) (hnot' k) hzσ (hz k)
    have hcσ : ∀ k, zσ * zz k = zz k * zσ := fun k => c.comm_W _ hzσW _ (hzW k)
    have h2 : σ.r * (zz i * zz j) * σ.r⁻¹ = zz i * zz j := by
      calc σ.r * (zz i * zz j) * σ.r⁻¹ = (σ.r * zz i * σ.r⁻¹) * (σ.r * zz j * σ.r⁻¹) := by group
        _ = (zσ * zz i) * (zσ * zz j) := by rw [hconj i, hconj j]
        _ = zσ * (zz i * zσ) * zz j := by group
        _ = zσ * (zσ * zz i) * zz j := by rw [hcσ i]
        _ = (zσ * zσ) * zz i * zz j := by group
        _ = zz i * zz j := by rw [hzσ.sq, one_mul]
    calc σ.r * (zz i * zz j) = (σ.r * (zz i * zz j) * σ.r⁻¹) * σ.r := by group
      _ = (zz i * zz j) * σ.r := by rw [h2]

theorem commute_frame_prod_of_mem_DSet (c : Ctx p f Ω W) (ρ : Fin 4 → Rep Ω W)
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

end T8YY

end CFSG.ClassicalInvolution.Asc77
