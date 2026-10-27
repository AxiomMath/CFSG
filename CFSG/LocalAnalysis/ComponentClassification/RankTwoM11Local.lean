module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoM11LocalCheck
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM11Check
public import Certificates.Certificate110

public section

namespace CFSG.ComponentClassification.RankTwoM11

open Equiv CFSG.QuasithinUnique.Unc25G2 CFSG.QuasithinUnique.Vol2Native.L239.M11Insp

local notation "𝓜" => CFSG.Blueprint.NativeSporadic.M11

theorem mem_m11_of_mem_wordPermsT {W : List (Fin 11 × List (ℕ × Bool))} {t : Perm (Fin 11)}
    (ht : t ∈ wordPermsT W) : t ∈ 𝓜 := by
  rw [wordPermsT_eq] at ht
  obtain ⟨w, -, rfl⟩ := mem_wordPerms.mp ht
  exact CFSG.Sporadic.Bridge.M11.nativeWord_mem _

theorem mem_centralizerList {x : Perm (Fin 11)} (hx : x ∈ 𝓜) (hc : x * pA = pA * x) :
    x ∈ centralizerList := by
  obtain ⟨t₀, ht₀, t₁, ht₁, t₂, ht₂, t₃, ht₃, rfl⟩ := level0 hx
  rw [← wordPermsT_eq] at ht₀ ht₁ ht₂ ht₃
  unfold centralizerList m11Products
  rw [List.mem_filter]
  refine ⟨?_, decide_eq_true hc⟩
  simp only [List.mem_flatMap, List.mem_map]
  exact ⟨t₀, ht₀, t₁, ht₁, t₂, ht₂, t₃, ht₃, rfl⟩

theorem of_mem_centralizerList {x : Perm (Fin 11)} (hx : x ∈ centralizerList) :
    x ∈ 𝓜 ∧ x * pA = pA * x := by
  unfold centralizerList m11Products at hx
  obtain ⟨hx, hc⟩ := List.mem_filter.mp hx
  simp only [List.mem_flatMap, List.mem_map] at hx
  obtain ⟨t₀, ht₀, t₁, ht₁, t₂, ht₂, t₃, ht₃, rfl⟩ := hx
  exact ⟨Subgroup.mul_mem _ (mem_m11_of_mem_wordPermsT ht₀) (Subgroup.mul_mem _
    (mem_m11_of_mem_wordPermsT ht₁) (Subgroup.mul_mem _ (mem_m11_of_mem_wordPermsT ht₂)
      (mem_m11_of_mem_wordPermsT ht₃))), of_decide_eq_true hc⟩

theorem exists_conj_gA {t : ↥𝓜} (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    ∃ g : ↥𝓜, g * gA * g⁻¹ = t := by
  by_cases h : t = gA
  · exact ⟨1, by simp [h]⟩
  obtain ⟨t₀, ht₀, t₁, ht₁, t₂, ht₂, t₃, ht₃, hgeq⟩ := level0 t.2
  rw [← wordPermsT_eq] at ht₀ ht₁ ht₂ ht₃
  have hcov := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp
    (List.all_eq_true.mp covered_check t₀ ht₀) t₁ ht₁) t₂ ht₂) t₃ ht₃
  rw [← hgeq] at hcov
  simp only [covered, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, List.any_eq_true] at hcov
  rcases hcov with ((hcov | hcov) | hcov) | ⟨e, he, hkey⟩
  · exact absurd (congrArg Subtype.val ht2) hcov
  · exact absurd (Subtype.ext hcov) ht1
  · exact absurd (Subtype.ext (code_injective hcov)) h
  · have hcert := List.all_eq_true.mp cert_check e he
    simp only [certOK, CFSG.Sporadic.Schreier.tab_eq, Bool.and_eq_true, beq_iff_eq] at hcert
    have hy : ev genT e.2.1 ∈ 𝓜 := by
      unfold ev
      rw [genT_eq]
      exact CFSG.Sporadic.Bridge.M11.nativeWord_mem _
    exact ⟨⟨ev genT e.2.1, hy⟩, Subtype.ext (code_injective (hcert.1.trans hkey))⟩

theorem exists_orderFour_gA {s : ↥𝓜} (hs2 : s * s = 1) (hs1 : s ≠ 1) (hsa : s ≠ gA)
    (hsc : s * gA = gA * s) :
    ∃ c : ↥𝓜, c * gA = gA * c ∧ (s * (c * s * c⁻¹)) ^ 2 ≠ 1 ∧
      (s * (c * s * c⁻¹)) ^ 4 = 1 := by
  have hmem := mem_centralizerList s.2 (congrArg Subtype.val hsc)
  have h := List.all_eq_true.mp orderFourOK_true _ hmem
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, Bool.and_eq_true] at h
  rcases h with ((h | h) | h) | ⟨c, hc, h2, h4⟩
  · exact absurd (congrArg Subtype.val hs2) h
  · exact absurd (Subtype.ext h) hs1
  · exact absurd (Subtype.ext h) hsa
  · obtain ⟨hcM, hcc⟩ := of_mem_centralizerList hc
    refine ⟨⟨c, hcM⟩, Subtype.ext hcc, fun h => h2 ?_, Subtype.ext ?_⟩
    · have h' := congrArg Subtype.val h
      simpa [pow_two] using h'
    · rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
      simpa using h4

theorem exists_orderFour_of_equiv {B : Type*} [Group B] (e : B ≃* ↥𝓜) {t s : B}
    (ht2 : t * t = 1) (ht1 : t ≠ 1) (hs2 : s * s = 1) (hs1 : s ≠ 1) (hts : t ≠ s)
    (hcomm : t * s = s * t) :
    ∃ c : B, c * t = t * c ∧ (s * (c * s * c⁻¹)) ^ 2 ≠ 1 ∧ (s * (c * s * c⁻¹)) ^ 4 = 1 := by
  obtain ⟨g, hg⟩ := exists_conj_gA (t := e t) (by rw [← map_mul, ht2, map_one])
    (fun h => ht1 (e.injective (h.trans (map_one e).symm)))
  let φ : B ≃* ↥𝓜 := e.trans (MulAut.conj g⁻¹)
  have hφ : ∀ x, φ x = g⁻¹ * e x * g := fun x => by
    simp [φ]
  have hφt : φ t = gA := by
    rw [hφ, ← hg]
    group
  have hs2' : φ s * φ s = 1 := by rw [← map_mul, hs2, map_one]
  have hs1' : φ s ≠ 1 := fun h => hs1 (φ.injective (h.trans (map_one φ).symm))
  have hsa : φ s ≠ gA := fun h => hts (φ.injective (hφt.trans h.symm))
  have hsc : φ s * gA = gA * φ s := by
    rw [← hφt, ← map_mul, ← map_mul, hcomm]
  obtain ⟨c, hc, h2, h4⟩ := exists_orderFour_gA hs2' hs1' hsa hsc
  refine ⟨φ.symm c, φ.injective ?_, fun h => h2 ?_, φ.injective ?_⟩
  · rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hφt, hc]
  · have h' := congrArg φ h
    simpa [map_pow, map_mul, map_inv] using h'
  · simpa [map_pow, map_mul, map_inv] using h4

theorem eq_one_of_forall_commute_of_equiv {B : Type*} [Group B] (e : B ≃* ↥𝓜) {z : B}
    (hz : ∀ x : B, z * x = x * z) : z = 1 := by
  have hcomm : ∀ y : ↥𝓜, e z * y = y * e z := fun y => by
    have h := congrArg e (hz (e.symm y))
    simpa [map_mul] using h
  have hmem := mem_centralizerList (e z).2 (congrArg Subtype.val (hcomm gA))
  have h := List.all_eq_true.mp centerOK_true _ hmem
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · exact absurd (congrArg Subtype.val (hcomm gB)) h
  · exact e.injective ((Subtype.ext h : e z = 1).trans (map_one e).symm)

end CFSG.ComponentClassification.RankTwoM11
