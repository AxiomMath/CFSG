module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888GY2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888E2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {X : Type} [Group X] {V : Subgroup X} {W : Fin 4 → Subgroup X}

@[expose] def IsMember (T V Xm : Subgroup X) : Prop :=
  Xm ≤ T ∧ ¬ Xm ≤ V ∧ ∃ g : X, Xm ≤ CFSG.conjugate V g

private lemma s888_pow_sub_le_of_mul_le {n k t : ℕ} (hk : k ≤ n)
    (h : 2 ^ n ≤ 2 ^ k * t) : 2 ^ (n - k) ≤ t := by
  have h1 : 2 ^ k * 2 ^ (n - k) = 2 ^ n := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hk]
  have h2 : 2 ^ k * 2 ^ (n - k) ≤ 2 ^ k * t := by rw [h1]; exact h
  exact Nat.le_of_mul_le_mul_left h2 (Nat.pow_pos (by norm_num))

private lemma s888_pow_sub_two_le_of_mul_le {n k t : ℕ} (ht : 0 < t)
    (h : 2 ^ n ≤ 2 ^ (2 * k) * t) : 2 ^ (n - 2 * k) ≤ t := by
  by_cases hk : 2 * k ≤ n
  · have h1 : 2 ^ (2 * k) * 2 ^ (n - 2 * k) = 2 ^ n := by
      rw [← Nat.pow_add, Nat.add_sub_of_le hk]
    have h2 : 2 ^ (2 * k) * 2 ^ (n - 2 * k) ≤ 2 ^ (2 * k) * t := by rw [h1]; exact h
    exact Nat.le_of_mul_le_mul_left h2 (Nat.pow_pos (by norm_num))
  · rw [Nat.sub_eq_zero_of_le (by omega : n ≤ 2 * k), pow_zero]
    exact ht

private lemma s888_relIndex_pos {Y : Type*} [Group Y] [Finite Y] (H K : Subgroup Y) :
    0 < H.relIndex K := by
  have h := Subgroup.relIndex_mul_card (H := H) (K := K)
  have hK : Nat.card K ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨⟨1, K.one_mem⟩⟩, inferInstance⟩
  by_contra hle
  have hz : H.relIndex K = 0 := Nat.eq_zero_of_not_pos hle
  rw [hz, zero_mul] at h
  exact hK h.symm

private lemma s888_card_pos {Y : Type*} [Group Y] [Finite Y] (H : Subgroup Y) :
    0 < Nat.card H :=
  Nat.pos_of_ne_zero (Nat.card_ne_zero.mpr ⟨⟨⟨1, H.one_mem⟩⟩, inferInstance⟩)

private lemma s888_conjugate_injective {Y : Type*} [Group Y] (g : Y) :
    Function.Injective fun H : Subgroup Y => CFSG.conjugate H g := by
  intro A B h
  exact Subgroup.map_injective (MulAut.conj g⁻¹).injective h

private lemma s888_relIndex_conjugate {Y : Type*} [Group Y] (A B : Subgroup Y) (g : Y) :
    (CFSG.conjugate A g).relIndex (CFSG.conjugate B g) = A.relIndex B :=
  Subgroup.relIndex_map_map_of_injective A B (MulAut.conj g⁻¹).injective

private lemma s888_card_conjugate {Y : Type*} [Group Y] (A : Subgroup Y) (g : Y) :
    Nat.card (CFSG.conjugate A g) = Nat.card A :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

private lemma s888_card_inf_centralizer {Y : Type*} [Group Y] (u : Y) (V : Subgroup Y) :
    Nat.card ↥(V ⊓ centralizer ({u} : Set Y)) =
      Nat.card {v : V // u * (v : Y) * u⁻¹ = v} := by
  refine Nat.card_congr ?_
  refine
    { toFun := ?_
      invFun := ?_
      left_inv := ?_
      right_inv := ?_ }
  · rintro ⟨x, hxV, hxC⟩
    refine ⟨⟨x, hxV⟩, ?_⟩
    have h : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
    calc u * x * u⁻¹ = (x * u) * u⁻¹ := by rw [← h]
      _ = x := by group
  · rintro ⟨⟨x, hxV⟩, hx⟩
    refine ⟨x, hxV, ?_⟩
    have h : x * u = u * x := by
      calc x * u = (u * x * u⁻¹) * u := by rw [hx]
        _ = u * x := by group
    exact Subgroup.mem_centralizer_singleton_iff.mpr h
  · rintro ⟨x, hxV, hxC⟩
    exact Subtype.ext rfl
  · rintro ⟨⟨x, hxV⟩, hx⟩
    exact Subtype.ext rfl

theorem exists_member_of_conj [Finite X] (hS : PlaneSys V W) {T : Subgroup X}
    (hT : IsSylow2Of T (⊤ : Subgroup X)) (hVT : V ≤ T)
    (hweak : ∀ k : X, CFSG.conjugate V k ≤ T → CFSG.conjugate V k = V)
    {u : X} (hu : u ∈ T) (huV : u ∉ V) (hconj : ∃ k : X, u ∈ CFSG.conjugate V k) :
    ∃ (Xm : Subgroup X) (k : ℕ), IsMember T V Xm ∧ 1 ≤ k ∧
      (Xm ⊓ V).relIndex Xm = 2 ^ k ∧
      2 ^ (8 - k) ≤ Nat.card {v : V // u * (v : X) * u⁻¹ = v} ∧
      2 ^ (8 - 2 * k) ≤ Nat.card ↥(Xm ⊓ V) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hTp, hTnd⟩ := hT
  have hTindex : ¬ 2 ∣ T.index := by rwa [Subgroup.relIndex_top_right] at hTnd
  let P : Sylow 2 X := hTp.toSylow hTindex
  have hPT : (P : Subgroup X) = T := IsPGroup.toSylow_coe hTp hTindex
  have hVe : CFSG.Open.IsElemAbelian 2 V :=
    ⟨IsMulCommutative.of_comm (fun a b => Subtype.ext (hS.comm a a.2 b b.2)),
      fun x hx => by rw [pow_two]; exact hS.sq x hx⟩
  have hVP : V ≤ (P : Subgroup X) := hPT ▸ hVT
  have hweak' : ∀ k : X, CFSG.conjugate V k ≤ (P : Subgroup X) →
      CFSG.conjugate V k = V := fun k hk => hweak k (hPT ▸ hk)
  have huP : u ∈ (P : Subgroup X) := hPT ▸ hu
  obtain ⟨V₀, V₂, g, hV₀lt, hV₂V, hCV₂, hV₀C, hV₂g, hinter, hidx⟩ :=
    goldschmidtYoshidaCount_holds X P V hVP hVe hweak' u huP huV hconj
  obtain ⟨k, hk8, hV0V2⟩ :
      ∃ k ≤ 8, V₀.relIndex V₂ = 2 ^ k := by
    have hdiv : V₀.relIndex V₂ ∣ 2 ^ 8 := by
      refine dvd_trans (Subgroup.relIndex_dvd_card (H := V₀) (K := V₂)) ?_
      rw [← hS.card_D]
      exact Subgroup.card_dvd_of_le hV₂V
    exact (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  have hk1 : 1 ≤ k := by
    rw [Nat.one_le_iff_ne_zero]
    rintro rfl
    have h1 : V₀.relIndex V₂ = 1 := by rw [hV0V2]; simp
    exact (not_le_of_gt hV₀lt) (Subgroup.relIndex_eq_one.mp h1)
  set Xm : Subgroup X := CFSG.conjugate V₂ g with hXmdef
  have hXmT : Xm ≤ T := by rw [hXmdef]; exact hPT ▸ hV₂g
  have hXmV : ¬ Xm ≤ V := by
    intro hle
    have h1 : V ⊓ Xm = Xm := inf_of_le_right hle
    have h2 : CFSG.conjugate V₀ g = CFSG.conjugate V₂ g := by
      rw [← hinter, h1, hXmdef]
    exact (not_le_of_gt hV₀lt) ((s888_conjugate_injective g h2).symm.le)
  have hXmg : Xm ≤ CFSG.conjugate V g := by
    rw [hXmdef]
    exact Subgroup.map_mono hV₂V
  have hrk : (Xm ⊓ V).relIndex Xm = 2 ^ k := by
    have h1 : Xm ⊓ V = CFSG.conjugate V₀ g := by
      rw [inf_comm]; exact hinter
    rw [h1, hXmdef]
    exact (s888_relIndex_conjugate V₀ V₂ g).trans hV0V2
  set CV : Subgroup X := V ⊓ centralizer ({u} : Set X) with hCVdef
  have hV₀C' : V₀ ≤ CV := by rw [hCVdef]; exact hV₀C
  have hCV₂' : CV ≤ V₂ := by rw [hCVdef]; exact hCV₂
  have hCVleV : CV ≤ V := hCV₂'.trans hV₂V
  have hidx' : V₂.relIndex V * V₀.relIndex CV ≤ V₀.relIndex CV * V₀.relIndex CV := by
    rw [hCVdef]; exact hidx
  have hcpos : 0 < V₀.relIndex CV := s888_relIndex_pos V₀ CV
  have ha_le_c : V₂.relIndex V ≤ V₀.relIndex CV :=
    Nat.le_of_mul_le_mul_right hidx' hcpos
  have hrelC : V₀.relIndex CV * CV.relIndex V₂ = 2 ^ k := by
    rw [Subgroup.relIndex_mul_relIndex (H := V₀) (K := CV) (L := V₂) hV₀C' hCV₂', hV0V2]
  have hCVle : CV.relIndex V ≤ 2 ^ k := by
    rw [← Subgroup.relIndex_mul_relIndex (H := CV) (K := V₂) (L := V) hCV₂' hV₂V]
    calc CV.relIndex V₂ * V₂.relIndex V ≤ CV.relIndex V₂ * V₀.relIndex CV :=
          Nat.mul_le_mul_left _ ha_le_c
      _ = V₀.relIndex CV * CV.relIndex V₂ := mul_comm _ _
      _ = 2 ^ k := hrelC
  have hcardCV : 2 ^ (8 - k) ≤ Nat.card CV := by
    have hcvcard : CV.relIndex V * Nat.card CV = 2 ^ 8 := by
      have h := Subgroup.relIndex_mul_card (H := CV) (K := V)
      rw [inf_of_le_left hCVleV, hS.card_D] at h
      exact h
    have h2 : 2 ^ 8 ≤ 2 ^ k * Nat.card CV := by
      rw [← hcvcard]
      exact Nat.mul_le_mul_right _ hCVle
    exact s888_pow_sub_le_of_mul_le hk8 h2
  have hV0pos : 0 < Nat.card V₀ := s888_card_pos V₀
  have hc2one : 1 ≤ CV.relIndex V₂ :=
    Nat.one_le_iff_ne_zero.mpr (ne_of_gt (s888_relIndex_pos CV V₂))
  have hb_le : V₀.relIndex CV ≤ 2 ^ k := by
    calc V₀.relIndex CV = V₀.relIndex CV * 1 := (mul_one _).symm
      _ ≤ V₀.relIndex CV * CV.relIndex V₂ := Nat.mul_le_mul_left _ hc2one
      _ = 2 ^ k := hrelC
  have hac : V₂.relIndex V * 2 ^ k ≤ 2 ^ (2 * k) := by
    calc V₂.relIndex V * 2 ^ k ≤ V₀.relIndex CV * 2 ^ k := Nat.mul_le_mul_right _ ha_le_c
      _ ≤ 2 ^ k * 2 ^ k := Nat.mul_le_mul_right _ hb_le
      _ = 2 ^ (2 * k) := by rw [← Nat.pow_add, two_mul]
  have hV2card : 2 ^ k * Nat.card V₀ = Nat.card V₂ := by
    have h := Subgroup.relIndex_mul_card (H := V₀) (K := V₂)
    rw [inf_of_le_left hV₀lt.le, hV0V2] at h
    exact h
  have haV2 : V₂.relIndex V * Nat.card V₂ = 2 ^ 8 := by
    have h := Subgroup.relIndex_mul_card (H := V₂) (K := V)
    rw [inf_of_le_left hV₂V, hS.card_D] at h
    exact h
  have hV0bound : 2 ^ (8 - 2 * k) ≤ Nat.card V₀ := by
    refine s888_pow_sub_two_le_of_mul_le hV0pos ?_
    rw [← haV2, ← hV2card]
    calc V₂.relIndex V * (2 ^ k * Nat.card V₀)
        = (V₂.relIndex V * 2 ^ k) * Nat.card V₀ := (mul_assoc _ _ _).symm
      _ ≤ 2 ^ (2 * k) * Nat.card V₀ := Nat.mul_le_mul_right _ hac
  refine ⟨Xm, k, ⟨hXmT, hXmV, ⟨g, hXmg⟩⟩, hk1, hrk, ?_, ?_⟩
  · rw [← s888_card_inf_centralizer u V]
    exact hcardCV
  · have h1 : Xm ⊓ V = CFSG.conjugate V₀ g := by
      rw [inf_comm]; exact hinter
    rw [h1, s888_card_conjugate]
    exact hV0bound

end CFSG.OddStandard.SmallF3.Omega
