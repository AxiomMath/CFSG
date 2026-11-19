module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109Cc
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109Ca
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Comb5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10TwoCore

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec10C_B_le_of_weight4 {B H : Subgroup G} {Alt : Subgroup (Equiv.Perm (Fin 5))}
    {φ : (Fin 5 → ZMod 2) → G} (hφ : IsPermModuleVia IsEvenVec φ B H Alt) {X : Subgroup G}
    (hX : ∀ v, IsEvenVec v → vecWeight v = 4 → φ v ∈ X) : B ≤ X := by
  obtain ⟨hadd, -, himg, -, -⟩ := hφ
  have hφ1 : φ 0 = 1 := by
    have h0 : IsEvenVec (0 : Fin 5 → ZMod 2) := by simp [IsEvenVec]
    have := hadd 0 0 h0 h0
    simpa using this
  intro b hb
  obtain ⟨w, hw, rfl⟩ := (himg b).1 hb
  rcases even_weight_cases_five w hw with h0 | h02 | h04
  · rw [h0, hφ1]
    exact X.one_mem
  · obtain ⟨x, y, hx, hy, rfl⟩ := weight_two_sum_five w h02
    rw [hadd x y (isEvenVec_of_weight_four x hx) (isEvenVec_of_weight_four y hy)]
    exact X.mul_mem (hX x (isEvenVec_of_weight_four x hx) hx)
      (hX y (isEvenVec_of_weight_four y hy) hy)
  · exact hX w hw h04

theorem sec10C_exists_weight4_outer [Finite G] (hf : Asc82Facts10) (hb : Asc82Basic10)
    (h107c : Asc82Lemma107c) {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} {g : G}
    (hctx : Sec109Ctx G t L S z K1 K2 g) {φ : (Fin 5 → ZMod 2) → G}
    (hφ : IsPermModuleVia IsEvenVec φ (secB S L) (L ⊓ normalizer (secB S L : Set G))
      (alternatingGroup (Fin 5))) :
    ∃ v, IsEvenVec v ∧ vecWeight v = 4 ∧ g⁻¹ * φ v * g ∉ L ⊔ centralizer (L : Set G) := by
  obtain ⟨hpsp, htC, -, htS, hSN, -⟩ := hb G t L S z hctx.toSec10Z
  obtain ⟨r, hrS, hr2, hrty, hne, hX, hconj⟩ := sec10C_exists_A2 h107c hctx
  have hzL : z ∈ L := (hctx.pocket1.2.1 hctx.pocket1.1).1
  by_contra hcon
  push Not at hcon
  have hB : secB S L ≤ CFSG.conjugate (L ⊔ centralizer (L : Set G)) g⁻¹ :=
    sec10C_B_le_of_weight4 hφ fun v hv hw => by
      rw [mem_conjugate_iff']
      simpa using hcon v hv hw
  have ht : t ∈ CFSG.conjugate (L ⊔ centralizer (L : Set G)) g⁻¹ := by
    rw [mem_conjugate_iff']
    have : g⁻¹ * t * g⁻¹⁻¹ = t * z := by rw [inv_inv]; exact hctx.swap
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right htC) (Subgroup.mem_sup_left hzL)
  have hA : secA t S L ≤ CFSG.conjugate (L ⊔ centralizer (L : Set G)) g⁻¹ :=
    sup_le hB (Subgroup.zpowers_le.mpr ht)
  have hrA2 : r ∈ secA2 t r K1 K2 :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers r))
  rw [← hconj] at hrA2
  have h1 : g * r * g⁻¹ ∈ secA t S L := mem_conjugate_iff'.mp hrA2
  have h2 := mem_conjugate_iff'.mp (hA h1)
  have hrr : r * r = 1 := by
    have h := pow_orderOf_eq_one r
    rw [hr2] at h
    simpa [pow_two] using h
  have hrr' : r * r ∈ centralizer (L : Set G) := by rw [hrr]; exact Subgroup.one_mem _
  have hr : r ∉ L ⊔ centralizer (L : Set G) :=
    (hf.factsC.ty G L hpsp r (hSN hrS) hrr').mpr (Or.inr hrty)
  apply hr
  have e : g⁻¹ * (g * r * g⁻¹) * g⁻¹⁻¹ = r := by group
  rwa [e] at h2

theorem sec10C_A2_swap [Finite G] (hP5 : Asc82FactPockets5) (hb : Asc82Basic10) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) {r : G}
    (hr2 : r * r = 1) (hrS : r ∈ S) (hrsw : CFSG.conjugate K1 r = K2) {a : G}
    (ha : a ∈ secA2 t r K1 K2) (hout : a ∉ L ⊔ centralizer (L : Set G)) :
    CFSG.conjugate K1 a = K2 := by
  obtain ⟨hpsp, htC, -, htS, -, -⟩ := hb G t L S z hctx.toSec10Z
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [hctx.involution] at h
    simpa [pow_two] using h
  have hQK : secQ K1 K2 ≤ K1 ⊔ K2 := twoCoreIn_le_self (K1 ⊔ K2)
  have hQS : secQ K1 K2 ≤ S := (sec10J_Q_le hP5 hb hctx).trans inf_le_left
  have hQL : secQ K1 K2 ≤ L := (sec10J_Q_le hP5 hb hctx).trans inf_le_right
  have hK2L : K2 ≤ L := hctx.pocket2.2.1.trans inf_le_left
  have hsup := sec10C_sup_normalizes hP5 hpsp hctx
  have htN2 : t ∈ normalizer (K2 : Set G) :=
    sec10C_mem_normalizer_of_comm fun x hx =>
      Subgroup.mem_centralizer_iff.mp htC x (hK2L hx)
  have hSt : ∀ y ∈ S, y * t = t * y := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mp (hctx.sylow.1 hy)
  have hcomm1 : ∀ y ∈ (secQ K1 K2 ⊓ centralizer ({r} : Set G)) ⊔ zpowers r, ∀ k ∈ zpowers t,
      y * k = k * y := by
    have hle : (secQ K1 K2 ⊓ centralizer ({r} : Set G)) ⊔ zpowers r ≤ S :=
      sup_le (inf_le_left.trans hQS) (Subgroup.zpowers_le.mpr hrS)
    intro y hy k hk
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    exact (Commute.zpow_right (show Commute y t from hSt y (hle hy)) n).eq
  have hcomm2 : ∀ c ∈ secQ K1 K2 ⊓ centralizer ({r} : Set G), ∀ k ∈ zpowers r,
      c * k = k * c := by
    intro c hc k hk
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    exact (Commute.zpow_right
      (show Commute c r from Subgroup.mem_centralizer_singleton_iff.mp hc.2) n).eq
  obtain ⟨y, hy, k, hk, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm1 ha
  obtain ⟨c, hc, r', hr', rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm2 hy
  have hcN1 : c ∈ normalizer (K1 : Set G) := (hsup (hQK hc.1)).1
  have hcL : c ∈ L := hQL hc.1
  have hc1 : CFSG.conjugate K1 c = K1 := sec10C_conjugate_eq_of_normalizer hcN1
  have hcLC : c ∈ L ⊔ centralizer (L : Set G) := Subgroup.mem_sup_left hcL
  have htLC : t ∈ L ⊔ centralizer (L : Set G) := Subgroup.mem_sup_right htC
  rcases sec10D_eq_one_or_of_mem_zpowers hr2 hr' with h1 | h1 <;>
    rcases sec10D_eq_one_or_of_mem_zpowers ht2 hk with h2 | h2 <;> rw [h1, h2] at hout ⊢
  · exact (hout (by simpa using hcLC)).elim
  · exact (hout (by simpa using Subgroup.mul_mem _ hcLC htLC)).elim
  · rw [mul_one, ← sec10C_conjugate_mul, hc1, hrsw]
  · rw [← sec10C_conjugate_mul, ← sec10C_conjugate_mul, hc1, hrsw,
      sec10C_conjugate_eq_of_normalizer htN2]

end CFSG.OddStandard.SmallF3.Omega
