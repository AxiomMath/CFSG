module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18Cj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbTSyl

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem smul_conj_eq_cj (g : G) (P : Subgroup G) :
    MulAut.conj g • P = cj g P := rfl

theorem exists_cj_of_isSylowIn {P P' H : Subgroup G} (hP : IsSylowIn 2 P H)
    (hP' : IsSylowIn 2 P' H) : ∃ c ∈ H, cj c P = P' := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : IsPGroup 2 (P.subgroupOf H) :=
    hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP.1).symm
  have hP'2 : IsPGroup 2 (P'.subgroupOf H) :=
    hP'.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP'.1).symm
  have hPidx : ¬ 2 ∣ (P.subgroupOf H).index := by
    simpa only [Subgroup.relIndex] using hP.2.2
  have hP'idx : ¬ 2 ∣ (P'.subgroupOf H).index := by
    simpa only [Subgroup.relIndex] using hP'.2.2
  haveI : Finite (Sylow 2 ↥H) := Sylow.finite_of_finiteIndex (hP2.toSylow hPidx)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥H) (hP2.toSylow hPidx) (hP'2.toSylow hP'idx)
  have hg' : MulAut.conj g • (P.subgroupOf H) = P'.subgroupOf H := by
    have h := congrArg (fun S : Sylow 2 ↥H => (S : Subgroup ↥H)) hg
    rw [Sylow.smul_def, Sylow.pointwise_smul_def] at h
    simpa only [IsPGroup.toSylow_coe] using h
  refine ⟨(g : G), g.2, ?_⟩
  have hsub : (cj (g : G) P).subgroupOf H = P'.subgroupOf H := by
    rw [← smul_conj_eq_cj, ← Subgroup.conj_smul_subgroupOf hP.1 g]
    exact hg'
  have hle : cj (g : G) P ≤ H := by
    rw [← smul_conj_eq_cj]
    exact Subgroup.conj_smul_le_of_le hP.1 g
  have hinf : cj (g : G) P ⊓ H = P' ⊓ H := Subgroup.subgroupOf_inj.mp hsub
  rw [inf_eq_left.mpr hle, inf_eq_left.mpr hP'.1] at hinf
  exact hinf

theorem isSylowIn_cj {S H : Subgroup G} (hS : IsSylowIn 2 S H) (g : G) :
    IsSylowIn 2 (cj g S) (cj g H) := by
  refine ⟨cj_mono hS.1, isPGroup_cj hS.2.1, ?_⟩
  have h : (cj g S).relIndex (cj g H) = S.relIndex H := by
    change (S.map (MulAut.conj g).toMonoidHom).relIndex
      (H.map (MulAut.conj g).toMonoidHom) = S.relIndex H
    exact Subgroup.relIndex_map_map_of_injective S H (MulAut.conj g).injective
  rw [h]
  exact hS.2.2

theorem exists_cj_of_card_le {S D H : Subgroup G} (hS : IsSylowIn 2 S H) (hD : D ≤ H)
    (hD2 : IsPGroup 2 D) (hc : Nat.card S ≤ Nat.card D) : ∃ c ∈ H, cj c S = D := by
  obtain ⟨S', hS'sylow, hDS'⟩ := exists_isSylowIn_of_le hD hD2
  obtain ⟨c, hcH, hcj⟩ := exists_cj_of_isSylowIn hS hS'sylow
  have hcard : Nat.card S' = Nat.card S := by rw [← hcj, card_cj]
  have hle : S' = D := by
    refine (Subgroup.eq_of_le_of_card_ge hDS' ?_).symm
    rw [hcard]
    exact hc
  rw [← hle]
  exact ⟨c, hcH, hcj⟩

theorem isSylowIn_inf_centralizer {P A : Subgroup G} (hP : IsSylowIn 2 P ⊤)
    (hA : ∀ n ∈ P, ∀ a ∈ A, n * a * n⁻¹ ∈ A) :
    IsSylowIn 2 (P ⊓ centralizer (A : Set G)) (centralizer (A : Set G)) := by
  set N : Subgroup G := normalizer (A : Set G) with hN
  set C : Subgroup G := centralizer (A : Set G) with hC
  have hPN : P ≤ N := by
    intro n hn
    rw [hN, Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      exact hA n hn a ha
    · intro ha
      have h := hA n⁻¹ (P.inv_mem hn) (n * a * n⁻¹) ha
      simpa [mul_assoc] using h
  have hPNsylow : IsSylowIn 2 P N := by
    refine ⟨hPN, hP.2.1, ?_⟩
    intro hdvd
    apply hP.2.2
    rw [← Subgroup.relIndex_mul_relIndex (H := P) (K := N) (L := ⊤) hPN le_top]
    exact hdvd.mul_right _
  have hCN : ∀ n ∈ N, ∀ c ∈ C, n * c * n⁻¹ ∈ C := by
    intro n hn c hc
    rw [hC, Subgroup.mem_centralizer_iff] at hc ⊢
    intro a ha
    have hna : n⁻¹ * a * n ∈ A :=
      (Subgroup.mem_normalizer_iff''.mp (by rwa [hN] at hn) a).mp ha
    have hcomm := hc (n⁻¹ * a * n) hna
    calc a * (n * c * n⁻¹) = n * ((n⁻¹ * a * n) * c) * n⁻¹ := by group
      _ = n * (c * (n⁻¹ * a * n)) * n⁻¹ := by rw [hcomm]
      _ = (n * c * n⁻¹) * a := by group
  have hC2 : IsPGroup 2 ↥(P ⊓ C) := hP.2.1.to_inf_left
  have hPCC : P ⊓ C ≤ C := inf_le_right
  obtain ⟨T, hTsylow, hPT⟩ := exists_isSylowIn_of_le hPCC hC2
  have hTCN : C ≤ N := by
    rw [hC, hN]
    exact Subgroup.centralizer_le_normalizer (A : Set G)
  have hTN : T ≤ N := hTsylow.1.trans hTCN
  obtain ⟨T₂, hT₂sylow, hTT₂⟩ := exists_isSylowIn_of_le hTN hTsylow.2.1
  obtain ⟨n, hnN, hncj⟩ := exists_cj_of_isSylowIn hPNsylow hT₂sylow
  have hCn : cj n C = C := cj_eq_self_of_normalizes (hCN n hnN)
  have hle : T ≤ cj n (P ⊓ C) := by
    rw [cj_inf, hncj, hCn]
    exact le_inf hTT₂ hTsylow.1
  have hcardT : Nat.card T ≤ Nat.card ↥(P ⊓ C) := by
    have h1 : Nat.card T ≤ Nat.card (cj n (P ⊓ C)) := Subgroup.card_le_of_le hle
    rwa [card_cj] at h1
  have hEq : P ⊓ C = T := Subgroup.eq_of_le_of_card_ge hPT hcardT
  rw [hEq]
  exact hTsylow

theorem exists_mul_mem_normalizer {A B E : Subgroup G} (hAB : A ≤ B)
    (hA : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A) (hE : IsSylowIn 2 E A) :
    ∀ g ∈ B, ∃ a ∈ A, ∃ h ∈ B, cj h E = E ∧ g = a * h := by
  intro g hg
  have hgEA : cj g E ≤ A := by
    intro x hx
    rw [mem_cj] at hx
    have hxa : g * (g⁻¹ * x * g) * g⁻¹ ∈ A := hA g hg (g⁻¹ * x * g) (hE.1 hx)
    simpa [mul_assoc] using hxa
  have hgE2 : IsPGroup 2 (cj g E) := isPGroup_cj hE.2.1
  have hcard : Nat.card E ≤ Nat.card (cj g E) := le_of_eq (card_cj g E).symm
  obtain ⟨a, haA, haj⟩ := exists_cj_of_card_le hE hgEA hgE2 hcard
  refine ⟨a, haA, a⁻¹ * g, B.mul_mem (B.inv_mem (hAB haA)) hg, ?_, ?_⟩
  · rw [← cj_cj a⁻¹ g E, ← haj, cj_cj a⁻¹ a E, inv_mul_cancel, cj_one]
  · group

theorem covBy_of_card_eq_two_mul {B N : Subgroup G} (hBN : B ≤ N)
    (hc : Nat.card N = 2 * Nat.card B) : B ⋖ N := by
  have hcardB : 0 < Nat.card B :=
    Nat.card_pos_iff.mpr ⟨⟨1, B.one_mem⟩, inferInstance⟩
  have hne : B ≠ N := by
    intro heq
    have h : Nat.card B = 2 * Nat.card B := by rw [← heq] at hc; exact hc
    omega
  refine ⟨lt_of_le_of_ne hBN hne, ?_⟩
  intro c hBc hcN
  have hBc' : B ≤ c := le_of_lt hBc
  have h1 : Nat.card B < Nat.card c := Subgroup.card_lt_of_lt hBc
  have h2 : Nat.card c < Nat.card N := Subgroup.card_lt_of_lt hcN
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hBc'
  have h1' : Nat.card B * 1 < Nat.card B * m := by rw [hm] at h1; simpa using h1
  have h2' : Nat.card B * m < Nat.card B * 2 := by
    rw [hm, hc] at h2
    rwa [mul_comm 2 (Nat.card B)] at h2
  have hm_gt : 1 < m := (Nat.mul_lt_mul_left hcardB).mp h1'
  have hm_lt : m < 2 := (Nat.mul_lt_mul_left hcardB).mp h2'
  omega

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
