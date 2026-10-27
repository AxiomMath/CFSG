module

public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalU62Plane
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

variable {K : Type} [Field K] (h : UnitaryFieldData 2 1 K)

theorem TorusInv.mem_normalizer {N : Subgroup (primeFormP h (idGram K 6))} (hN : TorusInv h N)
    (μ : Fin 6 → Kˣ) (hμ : ∏ i, μ i = 1) :
    diagP h μ hμ ∈ Subgroup.normalizer (N : Set (primeFormP h (idGram K 6))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hN μ hμ x hx, fun hx => ?_⟩
  have h1 := hN μ⁻¹ (prod_inv_eq_one hμ) _ hx
  have e : diagP h μ⁻¹ (prod_inv_eq_one hμ) = (diagP h μ hμ)⁻¹ := (diagP_inv h μ hμ).symm
  rw [e] at h1
  have e2 : (diagP h μ hμ)⁻¹ * (diagP h μ hμ * x * (diagP h μ hμ)⁻¹) *
      ((diagP h μ hμ)⁻¹)⁻¹ = x := by group
  rwa [e2] at h1

theorem TorusInv.inf_centralizer {N : Subgroup (primeFormP h (idGram K 6))} (hN : TorusInv h N)
    {m : primeFormP h (idGram K 6)} {i j n : Fin 6} (hm : m ∈ plane h i j n) :
    TorusInv h (N ⊓ Subgroup.centralizer ({m} : Set (primeFormP h (idGram K 6)))) := by
  obtain ⟨α, β, rfl⟩ := (mem_plane_iff h i j n m).1 hm
  intro μ hμ x hx
  rw [Subgroup.mem_inf] at hx ⊢
  refine ⟨hN μ hμ x hx.1, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  set m := diagP h (planeVec i j n α β) (prod_planeVec i j n α β) with hmdef
  set d := diagP h μ hμ with hddef
  have hmd : m * d = d * m := diagP_comm h _ μ _ hμ
  have hinv : m * d⁻¹ = d⁻¹ * m := (Commute.inv_right (show Commute m d from hmd)).eq
  have hx' : m * x = x * m := hx.2.symm
  refine Eq.symm ?_
  calc m * (d * x * d⁻¹) = (m * d) * x * d⁻¹ := by group
    _ = (d * m) * x * d⁻¹ := by rw [hmd]
    _ = d * (m * x) * d⁻¹ := by group
    _ = d * (x * m) * d⁻¹ := by rw [hx']
    _ = d * x * (m * d⁻¹) := by group
    _ = d * x * (d⁻¹ * m) := by rw [hinv]
    _ = d * x * d⁻¹ * m := by group

theorem u62lb_noNormal_of_phi
    (hΦ : ∀ N : Subgroup (primeFormP h (idGram K 6)), TorusInv h N → N ≠ ⊥ →
      Nat.Coprime 3 (Nat.card N) → NoCommutingPlane h N) :
    ∀ N : Subgroup (primeFormP h (idGram K 6)), TorusInv h N → Nat.Coprime 3 (Nat.card N) →
      N = ⊥ := by
  haveI := u62lb_finite h
  suffices H : ∀ k : ℕ, ∀ N : Subgroup (primeFormP h (idGram K 6)), Nat.card N = k →
      TorusInv h N → Nat.Coprime 3 (Nat.card N) → N = ⊥ from fun N => H _ N rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro N hk hInv hcop
    by_contra hne
    obtain ⟨i, j, n, hij, hin, hjn, hφ⟩ := hΦ N hInv hne hcop
    have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
      3 Nat.prime_three (plane h i j n) N (fun m => plane_pow_three h i j n m)
      (card_plane h hij hin hjn) ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop)
      (by
        intro m hm
        obtain ⟨α, β, rfl⟩ := (mem_plane_iff h i j n m).1 hm
        exact hInv.mem_normalizer h _ _)
    apply hne
    rw [hgen]
    refine iSup_eq_bot.2 fun m => iSup_eq_bot.2 fun hm1 => ?_
    have hmP : (m : primeFormP h (idGram K 6)) ≠ 1 := fun hh => hm1 (Subtype.ext hh)
    have hlt : N ⊓ Subgroup.centralizer ({(m : primeFormP h (idGram K 6))} :
        Set (primeFormP h (idGram K 6))) < N := by
      refine lt_of_le_of_ne inf_le_left fun heq => hφ m m.2 hmP ?_
      rw [← heq]
      exact inf_le_right
    exact ih _ (hk ▸ Subgroup.card_lt_of_lt hlt) _ rfl (hInv.inf_centralizer h m.2)
      (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hcop)

end CFSG.HardMathSupport.Dickson.Bal207

end
