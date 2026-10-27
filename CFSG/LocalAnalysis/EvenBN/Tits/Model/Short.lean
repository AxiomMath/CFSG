module

public import CFSG.LocalAnalysis.EvenBN.Tits.Sec4Basic
public import Certificates.Certificate27015
public import Certificates.Certificate27016

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits
open scoped commutatorElement

section FourGroup

variable {M : Type*} [Group M]

theorem mem_closure_pair_iff {a b x : M} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) :
    x ∈ closure ({a, b} : Set M) ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  constructor
  · intro hx
    have e1 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
    have e2 : b * a = a * b := hab.symm
    have e3 : b * (a * b) = a := by rw [← mul_assoc, e2, mul_assoc, hb, mul_one]
    have e4 : a * b * a = b := by rw [mul_assoc, e2, ← mul_assoc, ha, one_mul]
    have e5 : a * b * b = a := by rw [mul_assoc, hb, mul_one]
    have e6 : a * b * (a * b) = 1 := by rw [mul_assoc, e3, ha]
    have ia : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
    have ib : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
    have iab : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right e6
    let K : Subgroup M :=
      { carrier := {x | x = 1 ∨ x = a ∨ x = b ∨ x = a * b}
        mul_mem' := by
          rintro x y (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;>
            simp [ha, hb, e1, e2, e3, e4, e5, e6]
        one_mem' := Or.inl rfl
        inv_mem' := by
          rintro x (rfl | rfl | rfl | rfl) <;> simp [ia, ib, iab] }
    have hle : closure ({a, b} : Set M) ≤ K := by
      rw [closure_le]
      rintro y (rfl | rfl)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    exact hle hx
  · rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))

theorem false_of_conj_cycle {u₁ u₂ x : M} (h2 : u₂ * u₂ = 1) (h12 : u₁ * u₂ = u₂ * u₁)
    (hne : u₁ ≠ u₂) {n : ℕ} (hx : x ^ 2 ^ n = 1) (hx1 : x * u₁ * x⁻¹ = u₂)
    (hx2 : x * u₂ * x⁻¹ = u₁ * u₂) : False := by
  have hx3 : x * (u₁ * u₂) * x⁻¹ = u₁ := by
    calc x * (u₁ * u₂) * x⁻¹ = (x * u₁ * x⁻¹) * (x * u₂ * x⁻¹) := by group
      _ = u₂ * (u₁ * u₂) := by rw [hx1, hx2]
      _ = u₁ := by rw [← mul_assoc, ← h12, mul_assoc, h2, mul_one]
  have e : x ^ 3 * u₁ * (x ^ 3)⁻¹ = u₁ := by
    rw [pow_three']
    calc x * x * x * u₁ * (x * x * x)⁻¹ = x * (x * (x * u₁ * x⁻¹) * x⁻¹) * x⁻¹ := by group
      _ = u₁ := by rw [hx1, hx2, hx3]
  have hc3 : Commute (x ^ 3) u₁ := by
    change x ^ 3 * u₁ = u₁ * x ^ 3
    calc x ^ 3 * u₁ = x ^ 3 * u₁ * (x ^ 3)⁻¹ * x ^ 3 := by group
      _ = u₁ * x ^ 3 := by rw [e]
  have hcop : Nat.Coprime 3 (orderOf x) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hx)
      (Nat.Coprime.pow_right n (by norm_num))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have hc : x * u₁ = u₁ * x := by
    have h := (hc3.pow_left m).eq
    rwa [hm] at h
  exact hne (by rw [← hx1, hc, mul_inv_cancel_right])

theorem commute_of_isPGroup_of_conj {u₁ u₂ y : M} (h1 : u₁ * u₁ = 1) (h2 : u₂ * u₂ = 1)
    (h12 : u₁ * u₂ = u₂ * u₁) (hne1 : u₁ ≠ 1) (hne2 : u₂ ≠ 1) (hne : u₁ ≠ u₂)
    (hy1 : y * u₁ * y⁻¹ = u₂) (hy2 : y * u₂ * y⁻¹ = u₁ * u₂) {P : Subgroup M}
    (hP : IsPGroup 2 P) (hyP : ∀ p ∈ P, y * p * y⁻¹ ∈ P)
    (hN : ∀ p ∈ P, p * u₁ * p⁻¹ ∈ closure ({u₁, u₂} : Set M) ∧
      p * u₂ * p⁻¹ ∈ closure ({u₁, u₂} : Set M))
    {p : M} (hp : p ∈ P) : p * u₁ = u₁ * p ∧ p * u₂ = u₂ * p := by
  have e13 : u₁ * (u₁ * u₂) = u₂ := by rw [← mul_assoc, h1, one_mul]
  have e32 : u₁ * u₂ * u₂ = u₁ := by rw [mul_assoc, h2, mul_one]
  have e21 : u₂ * u₁ = u₁ * u₂ := h12.symm
  have e23 : u₂ * (u₁ * u₂) = u₁ := by rw [← mul_assoc, e21, e32]
  have e31 : u₁ * u₂ * u₁ = u₂ := by rw [mul_assoc, e21, ← mul_assoc, h1, one_mul]
  have hne31 : u₁ * u₂ ≠ u₁ := fun h => hne2 (mul_left_cancel (h.trans (mul_one u₁).symm))
  have hne32 : u₁ * u₂ ≠ u₂ := fun h => hne1 (mul_right_cancel (h.trans (one_mul u₂).symm))
  have vals : ∀ q a : M, a ≠ 1 → q * a * q⁻¹ ∈ closure ({u₁, u₂} : Set M) →
      q * a * q⁻¹ = u₁ ∨ q * a * q⁻¹ = u₂ ∨ q * a * q⁻¹ = u₁ * u₂ := by
    intro q a ha hmem
    rcases (mem_closure_pair_iff h1 h2 h12).1 hmem with h | h | h | h
    · exact absurd (by
        calc a = q⁻¹ * (q * a * q⁻¹) * q := by group
          _ = 1 := by rw [h]; group) ha
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have inj : ∀ q a b : M, q * a * q⁻¹ = q * b * q⁻¹ → a = b :=
    fun q a b h => mul_left_cancel (mul_right_cancel h)
  have pconj : ∀ q : M, q * (u₁ * u₂) * q⁻¹ = (q * u₁ * q⁻¹) * (q * u₂ * q⁻¹) :=
    fun q => by group
  have noCyc : ∀ q ∈ P, q * u₁ * q⁻¹ = u₂ → q * u₂ * q⁻¹ = u₁ * u₂ → False := by
    intro q hq hq1 hq2
    obtain ⟨n, hn⟩ := hP ⟨q, hq⟩
    exact false_of_conj_cycle h2 h12 hne (n := n) (by simpa using congrArg Subtype.val hn)
      hq1 hq2
  have hy3 : y * (u₁ * u₂) * y⁻¹ = u₁ := by rw [pconj, hy1, hy2, e23]
  have hyi1 : y⁻¹ * u₁ * y = u₁ * u₂ := by
    calc y⁻¹ * u₁ * y = y⁻¹ * (y * (u₁ * u₂) * y⁻¹) * y := by rw [hy3]
      _ = u₁ * u₂ := by group
  have hyi2 : y⁻¹ * u₂ * y = u₁ := by
    calc y⁻¹ * u₂ * y = y⁻¹ * (y * u₁ * y⁻¹) * y := by rw [hy1]
      _ = u₁ := by group
  have hr : p * (y * p * y⁻¹) ∈ P := mul_mem hp (hyP p hp)
  have c1 : p * (y * p * y⁻¹) * u₁ * (p * (y * p * y⁻¹))⁻¹ =
      p * (y * (p * (u₁ * u₂) * p⁻¹) * y⁻¹) * p⁻¹ := by
    rw [← hyi1]; group
  have c2 : p * (y * p * y⁻¹) * u₂ * (p * (y * p * y⁻¹))⁻¹ =
      p * (y * (p * u₁ * p⁻¹) * y⁻¹) * p⁻¹ := by
    rw [← hyi2]; group
  have fix : ∀ a : M, p * a * p⁻¹ = a → p * a = a * p := fun a h => by
    calc p * a = p * a * p⁻¹ * p := by group
      _ = a * p := by rw [h]
  rcases vals p u₁ hne1 (hN p hp).1 with e1 | e1 | e1 <;>
    rcases vals p u₂ hne2 (hN p hp).2 with e2 | e2 | e2
  · exact absurd (inj p _ _ (e1.trans e2.symm)) hne
  · exact ⟨fix u₁ e1, fix u₂ e2⟩
  · have hp3 : p * (u₁ * u₂) * p⁻¹ = u₂ := by rw [pconj, e1, e2, e13]
    exact (noCyc _ hr (by rw [c1, hp3, hy2, hp3]) (by rw [c2, e1, hy1, e2])).elim
  · have hp3 : p * (u₁ * u₂) * p⁻¹ = u₁ * u₂ := by rw [pconj, e1, e2, e21]
    exact (noCyc _ hr (by rw [c1, hp3, hy3, e1]) (by rw [c2, e1, hy2, hp3])).elim
  · exact absurd (inj p _ _ (e1.trans e2.symm)) hne
  · exact (noCyc p hp e1 e2).elim
  · have hp3 : p * (u₁ * u₂) * p⁻¹ = u₂ := by rw [pconj, e1, e2, e31]
    refine (noCyc p⁻¹ (inv_mem hp) ?_ ?_).elim
    · calc p⁻¹ * u₁ * p⁻¹⁻¹ = p⁻¹ * (p * u₂ * p⁻¹) * p := by rw [e2, inv_inv]
        _ = u₂ := by group
    · calc p⁻¹ * u₂ * p⁻¹⁻¹ = p⁻¹ * (p * (u₁ * u₂) * p⁻¹) * p := by rw [hp3, inv_inv]
        _ = u₁ * u₂ := by group
  · have hp3 : p * (u₁ * u₂) * p⁻¹ = u₁ := by rw [pconj, e1, e2, e32]
    exact (noCyc _ hr (by rw [c1, hp3, hy1, e2]) (by rw [c2, e1, hy3, e1])).elim
  · exact absurd (inj p _ _ (e1.trans e2.symm)) hne

end FourGroup

section Recognition

variable {M : Type*} [Group M]

@[expose] def zOTwoComm (Q : Subgroup M) : Subgroup M :=
  ⁅CFSG.Open.pCoreOf 2 Q ⊓ centralizer (CFSG.Open.pCoreOf 2 Q : Set M), Q⁆

theorem map_conj_eq_of_mem_normalizer {X : Subgroup M} {k : M}
    (hk : k ∈ normalizer (X : Set M)) : X.map (MulAut.conj k).toMonoidHom = X := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff.1 hk y).1 hy
  · intro hx
    refine ⟨k⁻¹ * x * k, (mem_normalizer_iff.1 hk _).2 ?_, ?_⟩
    · have e : k * (k⁻¹ * x * k) * k⁻¹ = x := by group
      rwa [e]
    · change k * (k⁻¹ * x * k) * k⁻¹ = x
      group

theorem mem_normalizer_centralizer {X : Subgroup M} {k : M}
    (hk : k ∈ normalizer (X : Set M)) : k ∈ normalizer (centralizer (X : Set M)) := by
  have key : ∀ k ∈ normalizer (X : Set M), ∀ c ∈ centralizer (X : Set M),
      k * c * k⁻¹ ∈ centralizer (X : Set M) := by
    intro k hk c hc
    rw [mem_centralizer_iff] at hc ⊢
    intro x hx
    have hx' : k⁻¹ * x * k ∈ X := (mem_normalizer_iff.1 hk _).2 (by
      have e : k * (k⁻¹ * x * k) * k⁻¹ = x := by group
      rwa [e])
    have h := hc _ hx'
    calc x * (k * c * k⁻¹) = k * ((k⁻¹ * x * k) * c) * k⁻¹ := by group
      _ = k * (c * (k⁻¹ * x * k)) * k⁻¹ := by rw [h]
      _ = k * c * k⁻¹ * x := by group
  rw [mem_normalizer_iff]
  intro c
  refine ⟨key k hk c, fun hc => ?_⟩
  have h := key k⁻¹ (inv_mem hk) _ hc
  have e : k⁻¹ * (k * c * k⁻¹) * k⁻¹⁻¹ = c := by group
  rwa [e] at h

theorem conj_mem_zOTwoComm {Q : Subgroup M} {k : M} (hk : k ∈ normalizer (Q : Set M)) {w : M}
    (hw : w ∈ zOTwoComm Q) : k * w * k⁻¹ ∈ zOTwoComm Q := by
  have hO : k ∈ normalizer (CFSG.Open.pCoreOf 2 Q : Set M) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Q hk
  have e : (zOTwoComm Q).map (MulAut.conj k).toMonoidHom = zOTwoComm Q := by
    rw [zOTwoComm, map_commutator, map_inf_eq _ _ _ (MulAut.conj k).injective,
      map_conj_eq_of_mem_normalizer hO,
      map_conj_eq_of_mem_normalizer (mem_normalizer_centralizer hO),
      map_conj_eq_of_mem_normalizer hk]
  rw [← e]
  exact ⟨w, hw, rfl⟩

variable [Finite M]

theorem zOTwoComm_eq_closure {Q : Subgroup M} {u₁ u₂ y : M} (h1 : u₁ * u₁ = 1)
    (h2 : u₂ * u₂ = 1) (h12 : u₁ * u₂ = u₂ * u₁) (hne1 : u₁ ≠ 1) (hne2 : u₂ ≠ 1)
    (hne : u₁ ≠ u₂) (hu₁ : u₁ ∈ Q) (hu₂ : u₂ ∈ Q) (hy : y ∈ Q) (hy1 : y * u₁ * y⁻¹ = u₂)
    (hy2 : y * u₂ * y⁻¹ = u₁ * u₂)
    (hN : ∀ x ∈ Q, x * u₁ * x⁻¹ ∈ closure ({u₁, u₂} : Set M) ∧
      x * u₂ * x⁻¹ ∈ closure ({u₁, u₂} : Set M))
    (h2grp : ∀ x ∈ Q, x * u₁ = u₁ * x → x * u₂ = u₂ * x → ∃ n : ℕ, x ^ 2 ^ n = 1)
    {R : Set M} (hRQ : R ⊆ Q) (hRU : ∀ r ∈ R, r * u₁ = u₁ * r ∧ r * u₂ = u₂ * r)
    (hC : ∀ x ∈ Q, (∀ r ∈ R, x * r = r * x) → ∃ c u : M, (∀ q ∈ Q, c * q = q * c) ∧
      u ∈ closure ({u₁, u₂} : Set M) ∧ x = c * u) :
    zOTwoComm Q = closure ({u₁, u₂} : Set M) := by
  set U := closure ({u₁, u₂} : Set M) with hU
  set P := Q ⊓ centralizer ({u₁} : Set M) ⊓ centralizer ({u₂} : Set M) with hPdef
  have hUQ : U ≤ Q := by
    rw [hU, closure_le]
    rintro _ (rfl | rfl)
    exacts [hu₁, hu₂]
  have hconjU : ∀ x ∈ Q, ∀ u ∈ U, x * u * x⁻¹ ∈ U := by
    intro x hx u hu
    have hle : U ≤ U.comap (MulAut.conj x).toMonoidHom := by
      rw [hU, closure_le]
      intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      simp only [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rcases ha with rfl | rfl
      exacts [(hN x hx).1, (hN x hx).2]
    simpa using hle hu
  have hPU : ∀ p ∈ P, ∀ u ∈ U, p * u = u * p := by
    intro p hp u hu
    have hle : U ≤ centralizer ({p} : Set M) := by
      rw [hU, closure_le]
      rintro _ (rfl | rfl)
      · exact mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 hp.1.2).symm
      · exact mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 hp.2).symm
    exact (mem_centralizer_singleton_iff.1 (hle hu)).symm
  have hQP : ∀ x ∈ Q, ∀ p ∈ P, x * p * x⁻¹ ∈ P := by
    intro x hx p hp
    have hxi : x⁻¹ ∈ Q := inv_mem hx
    have hcomm : ∀ a ∈ U, x * p * x⁻¹ * a = a * (x * p * x⁻¹) := by
      intro a ha
      have h := hPU p hp _ (hconjU x⁻¹ hxi a ha)
      calc x * p * x⁻¹ * a = x * (p * (x⁻¹ * a * x⁻¹⁻¹)) * x⁻¹ := by group
        _ = x * ((x⁻¹ * a * x⁻¹⁻¹) * p) * x⁻¹ := by rw [h]
        _ = a * (x * p * x⁻¹) := by group
    exact ⟨⟨mul_mem (mul_mem hx hp.1.1) hxi,
      mem_centralizer_singleton_iff.2 (hcomm u₁ (subset_closure (by simp)))⟩,
      mem_centralizer_singleton_iff.2 (hcomm u₂ (subset_closure (by simp)))⟩
  have hPQ : Q ≤ normalizer (P : Set M) := by
    intro x hx
    rw [mem_normalizer_iff]
    intro p
    refine ⟨hQP x hx p, fun hp => ?_⟩
    have h := hQP x⁻¹ (inv_mem hx) _ hp
    have e : x⁻¹ * (x * p * x⁻¹) * x⁻¹⁻¹ = p := by group
    rwa [e] at h
  have hP2 : IsPGroup 2 P := by
    intro g
    obtain ⟨n, hn⟩ := h2grp g g.2.1.1 (mem_centralizer_singleton_iff.1 g.2.1.2)
      (mem_centralizer_singleton_iff.1 g.2.2)
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  have hPO : P ≤ CFSG.Open.pCoreOf 2 Q :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans inf_le_left) hPQ hP2
  have hOP : CFSG.Open.pCoreOf 2 Q ≤ P := by
    intro p hp
    have hpQ : p ∈ Q := CFSG.LieType.BorelTits.pCoreOf_le 2 Q hp
    have hc := commute_of_isPGroup_of_conj h1 h2 h12 hne1 hne2 hne hy1 hy2
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Q)
      (fun q hq => (mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Q hy)
        q).1 hq)
      (fun q hq => hN q (CFSG.LieType.BorelTits.pCoreOf_le 2 Q hq)) hp
    exact ⟨⟨hpQ, mem_centralizer_singleton_iff.2 hc.1⟩, mem_centralizer_singleton_iff.2 hc.2⟩
  have hOeq : CFSG.Open.pCoreOf 2 Q = P := le_antisymm hOP hPO
  have hZ : ∀ a ∈ U, a ∈ P → a ∈ CFSG.Open.pCoreOf 2 Q ⊓
      centralizer (CFSG.Open.pCoreOf 2 Q : Set M) := by
    intro a ha haP
    rw [hOeq]
    exact ⟨haP, mem_centralizer_iff.2 fun p hp => hPU p hp a ha⟩
  have hu₁Z := hZ u₁ (subset_closure (by simp))
    ⟨⟨hu₁, mem_centralizer_singleton_iff.2 rfl⟩, mem_centralizer_singleton_iff.2 h12⟩
  have hu₂Z := hZ u₂ (subset_closure (by simp))
    ⟨⟨hu₂, mem_centralizer_singleton_iff.2 h12.symm⟩, mem_centralizer_singleton_iff.2 rfl⟩
  apply le_antisymm
  ·
    rw [zOTwoComm, hOeq, Subgroup.commutator_le]
    intro a ha x hx
    have hrP : ∀ r ∈ R, r ∈ P := fun r hr =>
      ⟨⟨hRQ hr, mem_centralizer_singleton_iff.2 (hRU r hr).1⟩,
        mem_centralizer_singleton_iff.2 (hRU r hr).2⟩
    obtain ⟨c, u, hc, hu, rfl⟩ :=
      hC a ha.1.1.1 fun r hr => (mem_centralizer_iff.1 ha.2 r (hrP r hr)).symm
    have hcu : c * u = u * c := hc u (hUQ hu)
    have hcx : c * x * c⁻¹ = x := by rw [hc x hx, mul_inv_cancel_right]
    have e : ⁅c * u, x⁆ = u * (x * u⁻¹ * x⁻¹) := by
      rw [commutatorElement_def, hcu]
      calc u * c * x * (u * c)⁻¹ * x⁻¹ = u * (c * x * c⁻¹) * u⁻¹ * x⁻¹ := by group
        _ = u * (x * u⁻¹ * x⁻¹) := by rw [hcx]; group
    rw [e]
    exact mul_mem hu (hconjU x hx _ (inv_mem hu))
  ·
    have iab : (u₁ * u₂)⁻¹ = u₁ * u₂ := inv_eq_of_mul_eq_one_right (by
      rw [mul_assoc, ← mul_assoc u₂, ← h12, mul_assoc, h2, mul_one, h1])
    have hm3 : u₁ * u₂ ∈ zOTwoComm Q := by
      have e : ⁅u₁, y⁆ = u₁ * u₂ := by
        rw [commutatorElement_def]
        calc u₁ * y * u₁⁻¹ * y⁻¹ = u₁ * (y * u₁ * y⁻¹)⁻¹ := by group
          _ = u₁ * u₂ := by rw [hy1, inv_eq_of_mul_eq_one_right h2]
      rw [← e]
      exact commutator_mem_commutator hu₁Z hy
    have hm1 : u₁ ∈ zOTwoComm Q := by
      have e : ⁅u₂, y⁆ = u₁ := by
        rw [commutatorElement_def]
        calc u₂ * y * u₂⁻¹ * y⁻¹ = u₂ * (y * u₂ * y⁻¹)⁻¹ := by group
          _ = u₁ := by rw [hy2, iab, ← mul_assoc, ← h12, mul_assoc, h2, mul_one]
      rw [← e]
      exact commutator_mem_commutator hu₂Z hy
    have hm2 : u₂ ∈ zOTwoComm Q := by
      have e : u₁ * (u₁ * u₂) = u₂ := by rw [← mul_assoc, h1, one_mul]
      rw [← e]
      exact mul_mem hm1 hm3
    rw [hU, closure_le]
    rintro _ (rfl | rfl)
    exacts [hm1, hm2]

end Recognition

namespace Model

open Certificates.TitsAschbacherSecFour CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open Certificates.TitsAschbacherParrott (powA)

@[expose] noncomputable def nElt (w : List ℕ) : Equiv.Perm (Fin 1755) :=
  (w.map (chainGen titsNArrs)).prod

@[expose] noncomputable def hatU₁ : Equiv.Perm (Fin 1755) := nElt u1Word

@[expose] noncomputable def hatU₂ : Equiv.Perm (Fin 1755) := nElt u2Word

@[expose] noncomputable def hatY : Equiv.Perm (Fin 1755) := nElt yWord

@[expose] noncomputable def hatEz : Equiv.Perm (Fin 1755) := nElt eWord

theorem nLetters_words : nLetters u1Word = true ∧ nLetters u2Word = true ∧
    nLetters yWord = true ∧ nLetters eWord = true ∧ (∀ w ∈ fWords, nLetters w = true) ∧
      ∀ w ∈ qWords, nLetters w = true := by
  decide

theorem rep_nElt
    {w : List ℕ} (hw : nLetters w = true) :
    Rep 1755 (nArr w) (nElt w) ∧ nElt w ∈ titsD :=
  ⟨rep_nArr hw, titsN_le_titsD (nArr_mem hw)⟩

theorem structCheck_eq_true : structCheck = true :=
  Certificates.certificate27015

theorem enumCheck_eq_true : enumCheck = true :=
  Certificates.certificate27016

theorem struct_facts
    : hatU₁ * hatU₁ = 1 ∧ hatU₂ * hatU₂ = 1 ∧ hatU₁ * hatU₂ = hatU₂ * hatU₁ ∧ hatU₁ ≠ 1 ∧
      hatU₂ ≠ 1 ∧ hatU₁ ≠ hatU₂ ∧ hatU₁ * titsTInv = titsTInv * hatU₁ ∧
      hatU₂ * titsTInv = titsTInv * hatU₂ ∧ hatY * titsTInv = titsTInv * hatY ∧
      hatY * hatU₁ * hatY⁻¹ = hatU₂ ∧ hatY * hatU₂ * hatY⁻¹ = hatU₁ * hatU₂ ∧ hatY ^ 3 = 1 ∧
      hatY ≠ 1 ∧ hatEz * titsZ * hatEz⁻¹ = hatU₁ ∧
      (∀ u, u = hatU₁ ∨ u = hatU₂ ∨ u = hatU₁ * hatU₂ →
        ∃ f ∈ titsD, f * titsTInv * f⁻¹ = u * titsTInv) ∧
      ∀ w ∈ qWords, nElt w * titsTInv = titsTInv * nElt w ∧ nElt w * hatU₁ = hatU₁ * nElt w ∧
        nElt w * hatU₂ = hatU₂ * nElt w := by
  have h := structCheck_eq_true
  simp only [structCheck, Bool.and_eq_true, Bool.not_eq_true', and_assoc] at h
  obtain ⟨-, -, -, -, -, -, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20,
    a21, a22⟩ := h
  obtain ⟨l1, l2, ly, le, lf, lq⟩ := nLetters_words
  have r1 : Rep 1755 u1A hatU₁ := (rep_nElt l1).1
  have r2 : Rep 1755 u2A hatU₂ := (rep_nElt l2).1
  have r3 : Rep 1755 u3A (hatU₁ * hatU₂) := rep_compA r1 r2
  have ry : Rep 1755 yA hatY := (rep_nElt ly).1
  have re : Rep 1755 eA hatEz := (rep_nElt le).1
  have rt := titsTInv_rep
  have rz := titsZ_rep
  have conj : ∀ {a b c : Equiv.Perm (Fin 1755)}, a * b = c * a → a * b * a⁻¹ = c :=
    fun h => by rw [h, mul_inv_cancel_right]
  refine ⟨eq_of_eqA (rep_compA r1 r1) rep_idA a7, eq_of_eqA (rep_compA r2 r2) rep_idA a8,
    (commA_iff r1 r2).1 a9, fun e => ?_, fun e => ?_, fun e => ?_, (commA_iff r1 rt).1 a13,
    (commA_iff r2 rt).1 a14, (commA_iff ry rt).1 a15,
    conj (eq_of_eqA (rep_compA ry r1) (rep_compA r2 ry) a16),
    conj (eq_of_eqA (rep_compA ry r2) (rep_compA r3 ry) a17),
    eq_of_eqA (rep_powA ry 3) rep_idA a18, fun e => ?_,
    conj (eq_of_eqA (rep_compA re rz) (rep_compA r1 re) a20), ?_, fun w hw => ?_⟩
  · rw [(eqA_iff r1 rep_idA).2 e] at a10
    exact Bool.true_eq_false.mp a10
  · rw [(eqA_iff r2 rep_idA).2 e] at a11
    exact Bool.true_eq_false.mp a11
  · rw [(eqA_iff r1 r2).2 e] at a12
    exact Bool.true_eq_false.mp a12
  · rw [(eqA_iff ry rep_idA).2 e] at a19
    exact Bool.true_eq_false.mp a19
  · simp only [fWords, uSharp, List.zip_cons_cons, List.zip_nil_right, List.all_cons,
      List.all_nil, Bool.and_true, Bool.and_eq_true] at a21
    obtain ⟨f1, f2, f3⟩ := a21
    have lf1 : nLetters [0] = true := by decide
    have lf2 : nLetters [0, 1] = true := by decide
    have lf3 : nLetters [1] = true := by decide
    rintro u (rfl | rfl | rfl)
    · exact ⟨_, (rep_nElt lf1).2, conj (eq_of_eqA (rep_compA (rep_nElt lf1).1 rt)
        (rep_compA (rep_compA r1 rt) (rep_nElt lf1).1) f1)⟩
    · exact ⟨_, (rep_nElt lf2).2, conj (eq_of_eqA (rep_compA (rep_nElt lf2).1 rt)
        (rep_compA (rep_compA r2 rt) (rep_nElt lf2).1) f2)⟩
    · exact ⟨_, (rep_nElt lf3).2, conj (eq_of_eqA (rep_compA (rep_nElt lf3).1 rt)
        (rep_compA (rep_compA r3 rt) (rep_nElt lf3).1) f3)⟩
  · have rq := (rep_nElt (lq w hw)).1
    have h := List.all_eq_true.1 a22 (nArr w) (List.mem_map.2 ⟨w, hw, rfl⟩)
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨q1, q2⟩, q3⟩ := h
    exact ⟨(commA_iff rq rt).1 q1, (commA_iff rq r1).1 q2, (commA_iff rq r2).1 q3⟩

theorem rep_sqIter {a : Array ℕ} {c : Equiv.Perm (Fin 1755)} (ha : Rep 1755 a c) :
    ∀ k, Rep 1755 (sqIter k a) (c ^ 2 ^ k) := by
  intro k
  induction k generalizing a c with
  | zero => simpa [sqIter] using ha
  | succ k ih =>
    have h := ih (rep_compA ha ha)
    rw [sqIter]
    rwa [← sq, ← pow_mul, ← pow_succ'] at h

theorem cOK_sound
    {r : Array ℕ} {c : Equiv.Perm (Fin 1755)}
    (hr : Rep 1755 r c) (hok : cOK r = true) :
    (c * hatU₁ * c⁻¹ = hatU₁ ∨ c * hatU₁ * c⁻¹ = hatU₂ ∨ c * hatU₁ * c⁻¹ = hatU₁ * hatU₂) ∧
      (c * hatU₂ * c⁻¹ = hatU₁ ∨ c * hatU₂ * c⁻¹ = hatU₂ ∨ c * hatU₂ * c⁻¹ = hatU₁ * hatU₂) ∧
      ((∀ w ∈ qWords, c * nElt w = nElt w * c) → ∃ e u : Equiv.Perm (Fin 1755),
        (e = 1 ∨ e = titsTInv) ∧ (u = 1 ∨ u = hatU₁ ∨ u = hatU₂ ∨ u = hatU₁ * hatU₂) ∧
        c = e * u) ∧
      (c * hatU₁ = hatU₁ * c → c * hatU₂ = hatU₂ * c → c ^ 2 ^ 10 = 1) := by
  obtain ⟨l1, l2, -, -, -, lq⟩ := nLetters_words
  have r1 : Rep 1755 u1A hatU₁ := (rep_nElt l1).1
  have r2 : Rep 1755 u2A hatU₂ := (rep_nElt l2).1
  have r3 : Rep 1755 u3A (hatU₁ * hatU₂) := rep_compA r1 r2
  have rt := titsTInv_rep
  have conj : ∀ {a b c : Equiv.Perm (Fin 1755)}, a * b = c * a → a * b * a⁻¹ = c :=
    fun h => by rw [h, mul_inv_cancel_right]
  simp only [cOK, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨k1, k2⟩, k3⟩, k4⟩ := hok
  simp only [uSharp, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] at k1 k2
  refine ⟨?_, ?_, fun hq => ?_, fun hc1 hc2 => ?_⟩
  · rcases k1 with h | h | h
    · exact Or.inl (conj (eq_of_eqA (rep_compA hr r1) (rep_compA r1 hr) h))
    · exact Or.inr (Or.inl (conj (eq_of_eqA (rep_compA hr r1) (rep_compA r2 hr) h)))
    · exact Or.inr (Or.inr (conj (eq_of_eqA (rep_compA hr r1) (rep_compA r3 hr) h)))
  · rcases k2 with h | h | h
    · exact Or.inl (conj (eq_of_eqA (rep_compA hr r2) (rep_compA r1 hr) h))
    · exact Or.inr (Or.inl (conj (eq_of_eqA (rep_compA hr r2) (rep_compA r2 hr) h)))
    · exact Or.inr (Or.inr (conj (eq_of_eqA (rep_compA hr r2) (rep_compA r3 hr) h)))
  · have hall : (qArrs.all fun q => commA r q) = true := by
      rw [List.all_eq_true]
      intro q hqm
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hqm
      exact (commA_iff hr (rep_nElt (lq w hw)).1).2 (hq w hw)
    rcases k3 with h | h
    · rw [hall] at h
      exact absurd h (by decide)
    · simp only [u10List, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] at h
      have rt1 := rep_compA rt r1
      have rt2 := rep_compA rt r2
      have rt3 := rep_compA rt r3
      rcases h with h | h | h | h | h | h | h | h
      · exact ⟨1, 1, Or.inl rfl, Or.inl rfl, by rw [one_mul]; exact eq_of_eqA hr rep_idA h⟩
      · exact ⟨1, _, Or.inl rfl, Or.inr (Or.inl rfl), by rw [one_mul]; exact eq_of_eqA hr r1 h⟩
      · exact ⟨1, _, Or.inl rfl, Or.inr (Or.inr (Or.inl rfl)), by
          rw [one_mul]; exact eq_of_eqA hr r2 h⟩
      · exact ⟨1, _, Or.inl rfl, Or.inr (Or.inr (Or.inr rfl)), by
          rw [one_mul]; exact eq_of_eqA hr r3 h⟩
      · exact ⟨_, 1, Or.inr rfl, Or.inl rfl, by rw [mul_one]; exact eq_of_eqA hr rt h⟩
      · exact ⟨_, _, Or.inr rfl, Or.inr (Or.inl rfl), eq_of_eqA hr rt1 h⟩
      · exact ⟨_, _, Or.inr rfl, Or.inr (Or.inr (Or.inl rfl)), eq_of_eqA hr rt2 h⟩
      · exact ⟨_, _, Or.inr rfl, Or.inr (Or.inr (Or.inr rfl)), eq_of_eqA hr rt3 h⟩
  · rcases k4 with h | h
    · rw [(commA_iff hr r1).2 hc1, (commA_iff hr r2).2 hc2] at h
      exact absurd h (by decide)
    · exact eq_of_eqA (rep_sqIter hr 10) rep_idA h

theorem exists_cOK
    {c : Equiv.Perm (Fin 1755)} (hc : c ∈ titsA) (hct : c * titsTInv = titsTInv * c) :
    ∃ r, Rep 1755 r c ∧ cOK r = true := by
  obtain ⟨r, hr, hrep⟩ := exists_rep_of_comm_titsTInv hc hct
  have h := enumCheck_eq_true
  rw [enumCheck, List.all_eq_true] at h
  obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ ▸ h r hr
  rcases hrep with h' | h'
  · exact ⟨r, h', h1⟩
  · exact ⟨_, h', h2⟩

theorem hat_mem :
    hatU₁ ∈ titsD ∧ hatU₂ ∈ titsD ∧ hatY ∈ titsD ∧ hatEz ∈ titsD ∧
      ∀ w ∈ qWords, nElt w ∈ titsD := by
  obtain ⟨l1, l2, ly, le, -, lq⟩ := nLetters_words
  exact ⟨(rep_nElt l1).2, (rep_nElt l2).2, (rep_nElt ly).2, (rep_nElt le).2,
    fun w hw => (rep_nElt (lq w hw)).2⟩

theorem long_of_mem_hatU
    {u : Equiv.Perm (Fin 1755)}
    (hu : u = hatU₁ ∨ u = hatU₂ ∨ u = hatU₁ * hatU₂) :
    ∃ e ∈ titsD, e * titsZ * e⁻¹ = u := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hy1, hy2, -, -, he, -, -⟩ := struct_facts
  obtain ⟨-, -, hyD, heD, -⟩ := hat_mem
  rcases hu with rfl | rfl | rfl
  · exact ⟨_, heD, he⟩
  · refine ⟨hatY * hatEz, mul_mem hyD heD, ?_⟩
    rw [← hy1, ← he]
    group
  · refine ⟨hatY * (hatY * hatEz), mul_mem hyD (mul_mem hyD heD), ?_⟩
    rw [← hy2, ← hy1, ← he]
    group

theorem short_of_mem_hatU
    {u : Equiv.Perm (Fin 1755)}
    (hu : u = hatU₁ ∨ u = hatU₂ ∨ u = hatU₁ * hatU₂) :
    ∃ f ∈ titsD, f * titsTInv * f⁻¹ = u * titsTInv :=
  struct_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 u hu

end Model

end CFSG.LocalAnalysis.EvenBN.Tits
