module

public import CFSG.GH74.GLS.C3.Layer1.P34L311
public import CFSG.GH74.GLS.C3.Layer1.P34L313

public section

namespace CFSG.GH74.GLS.C3.Layer1.P34

open Subgroup CFSG.GH74.GLS.Bg.Thompson CFSG.Quasithin

variable {X : Type} [Group X] [Finite X]

theorem normalizer_le_normalizer_T0 {T : Subgroup X} :
    normalizer (T : Set X) ≤ normalizer (T0 T : Set X) := by
  intro n hn
  have hn' := (normalizer (T : Set X)).inv_mem hn
  refine mem_normalizer_of_conj_le (fun a ha => ?_)
  induction ha using Subgroup.closure_induction with
  | mem t ht =>
    refine subset_closure ⟨?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1 hn' t).1 ht.1
      simpa using this
    · calc n⁻¹ * t * n * (n⁻¹ * t * n) = n⁻¹ * (t * t) * n := by group
        _ = 1 := by rw [ht.2]; group
  | one => simp
  | mul a b _ _ ha hb =>
    have : n⁻¹ * (a * b) * n = (n⁻¹ * a * n) * (n⁻¹ * b * n) := by group
    rw [this]; exact (T0 T).mul_mem ha hb
  | inv a _ ha =>
    have : n⁻¹ * a⁻¹ * n = (n⁻¹ * a * n)⁻¹ := by group
    rw [this]; exact (T0 T).inv_mem ha

theorem isWeaklyClosedIn_self' (T : Subgroup X) : IsWeaklyClosedIn T T := by
  intro g hg
  refine Subgroup.eq_of_le_of_card_ge hg ?_
  unfold conjSubgroup
  rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]

omit [Finite X] in
theorem exists_odd_pow_mem {T : Subgroup X} (hT : ¬ 2 ∣ T.index) {n : X}
    (hn : n ∈ normalizer (T : Set X)) : ∃ o : ℕ, Odd o ∧ n ^ o ∈ T := by
  set N : Subgroup X := normalizer (T : Set X) with hN
  have hTN : T ≤ N := Subgroup.le_normalizer
  have hcard : Nat.card (↥N ⧸ T.subgroupOf N) = T.relIndex N := by
    rw [← Subgroup.index_eq_card]; rfl
  have hodd : Odd (T.relIndex N) := by
    have hdvd : T.relIndex N ∣ T.index := Subgroup.relIndex_dvd_index_of_le hTN
    rw [Nat.odd_iff]
    by_contra hne
    exact hT ((Nat.dvd_of_mod_eq_zero (by omega)).trans hdvd)
  refine ⟨T.relIndex N, hodd, ?_⟩
  have h1 : ((⟨n, hn⟩ : ↥N) : ↥N ⧸ T.subgroupOf N) ^ Nat.card (↥N ⧸ T.subgroupOf N) = 1 :=
    pow_card_eq_one'
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hcard] at h1
  exact Subgroup.mem_subgroupOf.1 h1

theorem prop34_core {T P Q : Subgroup X} {x z f h : X} (c : Cfg34 X T P Q x z f h)
    (h35 : Lemma35 T P Q f) (h37 : Lemma37 T z) (h310 : Lemma310 T P) (hQ : QShapeFacts)
    (h38 : Lemma38 T P z) : False := by
  have h311 := lemma311 c h310
  have h312 := lemma312 c h35 h38 h310 h311
  obtain ⟨g₀, hg₀⟩ := lemma313 c hQ h37 h312
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Tsyl : Sylow 2 X := c.T_pgroup.toSylow c.T_index
  have hxC : x ∈ centralizer (T : Set X) :=
    Subgroup.mem_centralizer_iff.2 (fun t ht => c.x_central t ht)
  have hxzC : x * z ∈ centralizer (T : Set X) := by
    refine Subgroup.mem_centralizer_iff.2 (fun t ht => ?_)
    calc t * (x * z) = (t * x) * z := by group
      _ = (x * t) * z := by rw [c.x_central t ht]
      _ = x * (t * z) := by group
      _ = x * (z * t) := by rw [c.z_cent_T t ht]
      _ = x * z * t := by group
  obtain ⟨n, hn, hnx⟩ := burnside_fusion_lemma_centralizer Tsyl (W := T) le_rfl
    (isWeaklyClosedIn_self' T) hxC hxzC (g := g₀) hg₀
  have hzZ : z ∈ Z0 T := mem_Z0 c.z_mem_T c.z_sq c.z_cent_T
  have hzn : n⁻¹ * z * n = z := h37 n (Z0_conj (normalizer_le_normalizer_T0 hn) hzZ)
  have hx2 : (n * n)⁻¹ * x * (n * n) = x := by
    calc (n * n)⁻¹ * x * (n * n) = n⁻¹ * (n⁻¹ * x * n) * n := by group
      _ = n⁻¹ * (x * z) * n := by rw [hnx]
      _ = (n⁻¹ * x * n) * (n⁻¹ * z * n) := by group
      _ = (x * z) * z := by rw [hnx, hzn]
      _ = x := by rw [mul_assoc, c.z_sq, mul_one]
  obtain ⟨o, ⟨j, hj⟩, hoT⟩ := exists_odd_pow_mem c.T_index hn
  have h1 : n ^ o * x = x * n ^ o := c.x_central _ hoT
  have hcomm : Commute x (n * n) := by
    show x * (n * n) = (n * n) * x
    calc x * (n * n) = (n * n) * ((n * n)⁻¹ * x * (n * n)) := by group
      _ = (n * n) * x := by rw [hx2]
  have hv : (n * n) ^ j * x = x * (n * n) ^ j := (hcomm.pow_right j).eq.symm
  have hno : n ^ o = (n * n) ^ j * n := by
    rw [hj, pow_succ, ← sq, ← pow_mul]
  have h2 : (n ^ o)⁻¹ * x * n ^ o = x * z := by
    rw [hno]
    calc ((n * n) ^ j * n)⁻¹ * x * ((n * n) ^ j * n)
        = n⁻¹ * (((n * n) ^ j)⁻¹ * x * (n * n) ^ j) * n := by group
      _ = n⁻¹ * x * n := by
          have : ((n * n) ^ j)⁻¹ * x * (n * n) ^ j = x := by
            calc ((n * n) ^ j)⁻¹ * x * (n * n) ^ j = ((n * n) ^ j)⁻¹ * (x * (n * n) ^ j) := by group
              _ = ((n * n) ^ j)⁻¹ * ((n * n) ^ j * x) := by rw [hv]
              _ = x := by group
          rw [this]
      _ = x * z := hnx
  have h3 : (n ^ o)⁻¹ * x * n ^ o = x := by
    calc (n ^ o)⁻¹ * x * n ^ o = (n ^ o)⁻¹ * (x * n ^ o) := by group
      _ = (n ^ o)⁻¹ * (n ^ o * x) := by rw [h1]
      _ = x := by group
  have h4 : x * z = x := h2.symm.trans h3
  exact c.z_ne_one (mul_left_cancel (h4.trans (mul_one x).symm))

end CFSG.GH74.GLS.C3.Layer1.P34
