module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.WreathSplit

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G}
  {S A B Aa D : Subgroup G} {z b : G}

private def wreathK (hD : DHyp A Aa t D) (w : AddMonoid.End (VSub hD)) (Q : Subgroup G)
    (hHn : L ⊓ normalizer (A : Set G) ≤ wComm hD w) : Subgroup G where
  carrier := {n | n ∈ L ⊓ normalizer (A : Set G) ∧
    ∃ m ∈ normalizer (Q : Set G) ⊓ wComm hD w,
      (∀ v ∈ wFix hD w, m * v * m⁻¹ = v) ∧
        ∀ v ∈ wKer hD w, m * v * m⁻¹ = n * v * n⁻¹}
  one_mem' := by
    refine ⟨(L ⊓ normalizer (A : Set G)).one_mem, 1, ?_, ?_, ?_⟩
    · exact (normalizer (Q : Set G) ⊓ wComm hD w).one_mem
    · intro v _
      group
    · intro v _
      group
  mul_mem' := by
    intro n₁ n₂ hn₁ hn₂
    rcases hn₁ with ⟨hn₁, m₁, hm₁, hm₁Fix, hm₁Ker⟩
    rcases hn₂ with ⟨hn₂, m₂, hm₂, hm₂Fix, hm₂Ker⟩
    refine ⟨(L ⊓ normalizer (A : Set G)).mul_mem hn₁ hn₂, m₁ * m₂, ?_, ?_, ?_⟩
    · exact (normalizer (Q : Set G) ⊓ wComm hD w).mul_mem hm₁ hm₂
    · intro v hv
      calc (m₁ * m₂) * v * (m₁ * m₂)⁻¹
          = m₁ * (m₂ * v * m₂⁻¹) * m₁⁻¹ := by group
        _ = m₁ * v * m₁⁻¹ := by rw [hm₂Fix v hv]
        _ = v := hm₁Fix v hv
    · intro v hv
      have hv' : m₂ * v * m₂⁻¹ ∈ wKer hD w := conj_mem_wKer_of_mem_wComm hD hm₂.2 hv
      calc (m₁ * m₂) * v * (m₁ * m₂)⁻¹
          = m₁ * (m₂ * v * m₂⁻¹) * m₁⁻¹ := by group
        _ = m₁ * (n₂ * v * n₂⁻¹) * m₁⁻¹ := by rw [hm₂Ker v hv]
        _ = n₁ * (n₂ * v * n₂⁻¹) * n₁⁻¹ := by
              rw [hm₁Ker _ (conj_mem_wKer_of_mem_wComm hD (hHn hn₂) hv)]
        _ = (n₁ * n₂) * v * (n₁ * n₂)⁻¹ := by group
  inv_mem' := by
    intro n hn
    rcases hn with ⟨hn, m, hm, hmFix, hmKer⟩
    refine ⟨(L ⊓ normalizer (A : Set G)).inv_mem hn, m⁻¹, ?_, ?_, ?_⟩
    · exact (normalizer (Q : Set G) ⊓ wComm hD w).inv_mem hm
    · intro v hv
      have hv' : m⁻¹ * v * m ∈ wFix hD w := by
        simpa only [inv_inv] using
          conj_mem_wFix_of_mem_wComm hD
            ((normalizer (Q : Set G) ⊓ wComm hD w).inv_mem hm).2 hv
      have h1 : m * (m⁻¹ * v * m) * m⁻¹ = m⁻¹ * v * m := hmFix _ hv'
      have h2 : m * (m⁻¹ * v * m) * m⁻¹ = v := by group
      simpa only [inv_inv] using h1.symm.trans h2
    · intro v hv
      have hnv : n⁻¹ * v * n ∈ wKer hD w := by
        simpa only [inv_inv] using
          conj_mem_wKer_of_mem_wComm hD ((wComm hD w).inv_mem (hHn hn)) hv
      have h1 : m * (n⁻¹ * v * n) * m⁻¹ = n * (n⁻¹ * v * n) * n⁻¹ := hmKer _ hnv
      have h2 : n * (n⁻¹ * v * n) * n⁻¹ = v := by group
      have h3 : m * (m⁻¹ * v * m) * m⁻¹ = v := by group
      have hXY : n⁻¹ * v * n = m⁻¹ * v * m := by
        have hthis : m * (n⁻¹ * v * n) * m⁻¹ = m * (m⁻¹ * v * m) * m⁻¹ := by
          rw [h1, h2]
          exact h3.symm
        have hthis' : m * ((n⁻¹ * v * n) * m⁻¹) = m * ((m⁻¹ * v * m) * m⁻¹) := by
          simpa only [mul_assoc] using hthis
        exact mul_right_cancel (mul_left_cancel hthis')
      simpa only [inv_inv] using hXY.symm

private theorem wreathK_le_Hn (hD : DHyp A Aa t D) (w : AddMonoid.End (VSub hD))
    (Q : Subgroup G) (hHn : L ⊓ normalizer (A : Set G) ≤ wComm hD w) :
    wreathK hD w Q hHn ≤ L ⊓ normalizer (A : Set G) :=
  fun _ hn => hn.1

private theorem Hn_le_wreathN0 (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    (hwH : ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * w = w * vConj hD n)
    {Q : Subgroup G} (hQ : QHyp L A D t Q) :
    L ⊓ normalizer (A : Set G) ≤ normalizer (Q : Set G) ⊓ wComm hD w := by
  intro n hn
  refine ⟨?_, Hn_le_wComm H W W2 hD hwH hn⟩
  refine mem_normalizer_iff.2 (mem_iff_conj_of_conj_le Q (g := n) ?_)
  intro q hq
  simpa using hQ.conj_mem n⁻¹ ((L ⊓ normalizer (A : Set G)).inv_mem hn) q hq

private theorem B_le_wreathK (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {Q : Subgroup G} (hQ : QHyp L A D t Q)
    (hHn : L ⊓ normalizer (A : Set G) ≤ wComm hD w) :
    B ≤ wreathK hD w Q hHn := by
  intro β hβ
  have hβL : β ∈ L := W.B_le hβ
  have hβN : β ∈ normalizer (A : Set G) := by
    refine mem_normalizer_iff.2 (mem_iff_conj_of_conj_le A (g := β) ?_)
    intro a ha
    have hc : β * a = a * β := (W.mem_B_iff β hβL).1 hβ a ha
    have hconj : β⁻¹ * a * β = a := by
      calc β⁻¹ * a * β = β⁻¹ * (a * β) := by group
        _ = β⁻¹ * (β * a) := by rw [hc]
        _ = a := by group
    rw [hconj]
    exact ha
  have hβHn : β ∈ L ⊓ normalizer (A : Set G) := ⟨hβL, hβN⟩
  have hβQ : β ∈ normalizer (Q : Set G) := by
    refine mem_normalizer_iff.2 (mem_iff_conj_of_conj_le Q (g := β) ?_)
    intro q hq
    simpa using hQ.conj_mem β⁻¹ ((L ⊓ normalizer (A : Set G)).inv_mem hβHn) q hq
  refine ⟨hβHn, β, ⟨hβQ, hHn hβHn⟩, ?_, ?_⟩
  · intro v hv
    exact H.comm_omega1_of_mem_B W W2 hD hb hβ (wFix_le_omega1 hD w hv)
  · intro v hv
    rw [H.comm_omega1_of_mem_B W W2 hD hb hβ (wKer_le_omega1 hD w hv)]

private theorem wreathK_normal (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    (hwH : ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * w = w * vConj hD n)
    {Q : Subgroup G} (hQ : QHyp L A D t Q)
    (hHn : L ⊓ normalizer (A : Set G) ≤ wComm hD w) :
    ∀ h ∈ L ⊓ normalizer (A : Set G), ∀ x ∈ wreathK hD w Q hHn,
      h * x * h⁻¹ ∈ wreathK hD w Q hHn := by
  intro h hh x ⟨hxHn, m, hm, hmFix, hmKer⟩
  have hhQ : h ∈ normalizer (Q : Set G) := by
    refine mem_normalizer_iff.2 (mem_iff_conj_of_conj_le Q (g := h) ?_)
    intro q hq
    simpa using hQ.conj_mem h⁻¹ ((L ⊓ normalizer (A : Set G)).inv_mem hh) q hq
  have hhN0 : h ∈ normalizer (Q : Set G) ⊓ wComm hD w := ⟨hhQ, hHn hh⟩
  have hxHn' : h * x * h⁻¹ ∈ L ⊓ normalizer (A : Set G) :=
    (L ⊓ normalizer (A : Set G)).mul_mem
      ((L ⊓ normalizer (A : Set G)).mul_mem hh hxHn)
      ((L ⊓ normalizer (A : Set G)).inv_mem hh)
  have hm' : h * m * h⁻¹ ∈ normalizer (Q : Set G) ⊓ wComm hD w :=
    (normalizer (Q : Set G) ⊓ wComm hD w).mul_mem
      ((normalizer (Q : Set G) ⊓ wComm hD w).mul_mem hhN0 hm)
      ((normalizer (Q : Set G) ⊓ wComm hD w).inv_mem hhN0)
  refine ⟨hxHn', h * m * h⁻¹, hm', ?_, ?_⟩
  · intro v hv
    have hv' : h⁻¹ * v * h ∈ wFix hD w := by
      simpa only [inv_inv] using
        conj_mem_wFix_of_mem_wComm hD ((wComm hD w).inv_mem (hHn hh)) hv
    calc (h * m * h⁻¹) * v * (h * m * h⁻¹)⁻¹
        = h * (m * (h⁻¹ * v * h) * m⁻¹) * h⁻¹ := by group
      _ = h * (h⁻¹ * v * h) * h⁻¹ := by rw [hmFix _ hv']
      _ = v := by group
  · intro v hv
    have hv' : h⁻¹ * v * h ∈ wKer hD w := by
      simpa only [inv_inv] using
        conj_mem_wKer_of_mem_wComm hD ((wComm hD w).inv_mem (hHn hh)) hv
    calc (h * m * h⁻¹) * v * (h * m * h⁻¹)⁻¹
        = h * (m * (h⁻¹ * v * h) * m⁻¹) * h⁻¹ := by group
      _ = h * (x * (h⁻¹ * v * h) * x⁻¹) * h⁻¹ := by rw [hmKer _ hv']
      _ = (h * x * h⁻¹) * v * (h * x * h⁻¹)⁻¹ := by group

theorem ThCyc.exists_trivial_wFix_of_wreath (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {w : AddMonoid.End (VSub hD)}
    (hwH : ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * w = w * vConj hD n)
    (hww : w * w = w) (hτw : vConj hD t * w * vConj hD t = w + 1)
    {Q : Subgroup G} (hQ : QHyp L A D t Q) {g : G}
    (hgQ : g ∈ normalizer (Q : Set G)) (hgw : g ∈ wComm hD w)
    (hgM : g ∉ normalizer (D : Set G)) {h : G}
    (hh : h ∈ L ⊓ normalizer (A : Set G)) :
    ∃ m ∈ normalizer (Q : Set G) ⊓ wComm hD w,
      (∀ v ∈ wFix hD w, m * v * m⁻¹ = v) ∧
        ∀ v ∈ wKer hD w, m * v * m⁻¹ = h * v * h⁻¹ := by
  let K := wreathK hD w Q (Hn_le_wComm H W W2 hD hwH)
  have hKle : K ≤ L ⊓ normalizer (A : Set G) := wreathK_le_Hn hD w Q _
  have hBK : B ≤ K := B_le_wreathK H W W2 hD hb hQ (Hn_le_wComm H W W2 hD hwH)
  have hKnormal : ∀ h ∈ L ⊓ normalizer (A : Set G), ∀ x ∈ K, h * x * h⁻¹ ∈ K :=
    wreathK_normal H W W2 hD hwH hQ (Hn_le_wComm H W W2 hD hwH)
  rcases W.eq_B_or_eq_of_normal (N₀ := K) hKle hBK hKnormal with hKB | hKH
  · exfalso
    obtain ⟨h₁, hh₁, hact₁⟩ :=
      exists_mem_Hn_conj_eq_of_mem_wComm H W W2 hD hww hτw hwH hgw
    let m : G := h₁⁻¹ * g
    have hmN0 : m ∈ normalizer (Q : Set G) ⊓ wComm hD w := by
      refine (normalizer (Q : Set G) ⊓ wComm hD w).mul_mem ?_ ⟨hgQ, hgw⟩
      exact (normalizer (Q : Set G) ⊓ wComm hD w).inv_mem
        (Hn_le_wreathN0 H W W2 hD hwH hQ hh₁)
    have hmFix : ∀ v ∈ wFix hD w, m * v * m⁻¹ = v := by
      intro v hv
      calc m * v * m⁻¹ = h₁⁻¹ * (g * v * g⁻¹) * h₁ := by
            dsimp only [m]
            group
        _ = h₁⁻¹ * (h₁ * v * h₁⁻¹) * h₁ := by rw [hact₁ v hv]
        _ = v := by group
    obtain ⟨n, hn, hact₂⟩ :=
      exists_mem_Hn_conj_eq_of_mem_wComm_wKer H W W2 hD hww hτw hwH hmN0.2
    have hnK : n ∈ K := ⟨hn, m, hmN0, hmFix, fun v hv => (hact₂ v hv).symm⟩
    rw [hKB] at hnK
    have hnTriv : ∀ v ∈ omega1 D hD.comm, n * v * n⁻¹ = v :=
      fun v hv => H.comm_omega1_of_mem_B W W2 hD hb hnK hv
    have hmTrivKer : ∀ v ∈ wKer hD w, m * v * m⁻¹ = v := by
      intro v hv
      rw [(hact₂ v hv).symm, hnTriv v (wKer_le_omega1 hD w hv)]
    have hmTrivV : ∀ v ∈ omega1 D hD.comm, m * v * m⁻¹ = v := by
      intro v hv
      obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := exists_mem_wFix_mul_mem_wKer hD w hww hv
      calc m * (v₁ * v₂) * m⁻¹ = (m * v₁ * m⁻¹) * (m * v₂ * m⁻¹) := by group
        _ = v₁ * v₂ := by rw [hmFix v₁ hv₁, hmTrivKer v₂ hv₂]
    have hgA : ∀ a ∈ A, g * a * g⁻¹ ∈ A := by
      intro a ha
      have haV : a ∈ omega1 D hD.comm := H.A_le_omega1 W W2 hD ha
      have hg : g * a * g⁻¹ = h₁ * (m * a * m⁻¹) * h₁⁻¹ := by
        dsimp only [m]
        group
      rw [hg, hmTrivV a haV]
      exact (mem_normalizer_iff.1 hh₁.2 a).1 ha
    have hgQ' : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q :=
      fun q hq => (mem_normalizer_iff.1 hgQ q).1 hq
    exact hgM (QHyp.mem_normalizer_D_of_conj_mem_A H W W2 hD h4 hQ hgQ' hgA)
  · have hhK : h ∈ K := by rw [hKH]; exact hh
    obtain ⟨-, m, hm, hmFix, hmKer⟩ := hhK
    exact ⟨m, hm, hmFix, hmKer⟩

theorem ThCyc.exists_trivial_wKer_of_wreath (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {w : AddMonoid.End (VSub hD)}
    (hwH : ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * w = w * vConj hD n)
    (hww : w * w = w) (hτw : vConj hD t * w * vConj hD t = w + 1)
    {Q : Subgroup G} (hQ : QHyp L A D t Q) {g : G}
    (hgQ : g ∈ normalizer (Q : Set G)) (hgw : g ∈ wComm hD w)
    (hgM : g ∉ normalizer (D : Set G)) {h : G}
    (hh : h ∈ L ⊓ normalizer (A : Set G)) :
    ∃ m ∈ normalizer (Q : Set G) ⊓ wComm hD w,
      (∀ v ∈ wKer hD w, m * v * m⁻¹ = v) ∧
        ∀ v ∈ wFix hD w, m * v * m⁻¹ = h * v * h⁻¹ := by
  obtain ⟨m', hm', hm'Fix, hm'Ker⟩ :=
    H.exists_trivial_wFix_of_wreath W W2 hD h4 hb hwH hww hτw hQ hgQ hgw hgM hh
  have hhN0 : h ∈ normalizer (Q : Set G) ⊓ wComm hD w :=
    Hn_le_wreathN0 H W W2 hD hwH hQ hh
  have hmN0 : h * m'⁻¹ ∈ normalizer (Q : Set G) ⊓ wComm hD w :=
    (normalizer (Q : Set G) ⊓ wComm hD w).mul_mem hhN0
      ((normalizer (Q : Set G) ⊓ wComm hD w).inv_mem hm')
  refine ⟨h * m'⁻¹, hmN0, ?_, ?_⟩
  · intro v hv
    have hv' : h⁻¹ * v * h ∈ wKer hD w := by
      simpa only [inv_inv] using
        conj_mem_wKer_of_mem_wComm hD ((wComm hD w).inv_mem hhN0.2) hv
    have h1 : m' * (h⁻¹ * v * h) * m'⁻¹ = v := by
      rw [hm'Ker _ hv']
      group
    calc (h * m'⁻¹) * v * (h * m'⁻¹)⁻¹
        = h * (m'⁻¹ * v * m') * h⁻¹ := by group
      _ = h * (h⁻¹ * v * h) * h⁻¹ := by
            have hinner : m'⁻¹ * v * m' = h⁻¹ * v * h := by
              calc m'⁻¹ * v * m'
                  = m'⁻¹ * (m' * (h⁻¹ * v * h) * m'⁻¹) * m' := by rw [h1]
                _ = h⁻¹ * v * h := by group
            rw [hinner]
      _ = v := by group
  · intro v hv
    have hv' : m'⁻¹ * v * m' ∈ wFix hD w := by
      simpa only [inv_inv] using
        conj_mem_wFix_of_mem_wComm hD ((wComm hD w).inv_mem hm'.2) hv
    have h1 : m' * (m'⁻¹ * v * m') * m'⁻¹ = m'⁻¹ * v * m' := hm'Fix _ hv'
    have h2 : m' * (m'⁻¹ * v * m') * m'⁻¹ = v := by group
    calc (h * m'⁻¹) * v * (h * m'⁻¹)⁻¹
        = h * (m'⁻¹ * v * m') * h⁻¹ := by group
      _ = h * v * h⁻¹ := by rw [h1.symm.trans h2]

theorem ThCyc.exists_mul_of_wreath (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {w : AddMonoid.End (VSub hD)}
    (hwH : ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * w = w * vConj hD n)
    (hww : w * w = w) (hτw : vConj hD t * w * vConj hD t = w + 1)
    {Q : Subgroup G} (hQ : QHyp L A D t Q) {g : G}
    (hgQ : g ∈ normalizer (Q : Set G)) (hgw : g ∈ wComm hD w)
    (hgM : g ∉ normalizer (D : Set G)) {n : G}
    (hn : n ∈ normalizer (Q : Set G) ⊓ wComm hD w) :
    ∃ m₁ ∈ normalizer (Q : Set G) ⊓ wComm hD w,
      ∃ m₂ ∈ normalizer (Q : Set G) ⊓ wComm hD w,
        (∀ v ∈ wKer hD w, m₁ * v * m₁⁻¹ = v) ∧
          (∀ v ∈ wFix hD w, m₂ * v * m₂⁻¹ = v) ∧
            ∀ v ∈ omega1 D hD.comm,
              (m₁ * m₂) * v * (m₁ * m₂)⁻¹ = n * v * n⁻¹ := by
  obtain ⟨h₁, hh₁, hact₁⟩ :=
    exists_mem_Hn_conj_eq_of_mem_wComm H W W2 hD hww hτw hwH hn.2
  obtain ⟨h₂, hh₂, hact₂⟩ :=
    exists_mem_Hn_conj_eq_of_mem_wComm_wKer H W W2 hD hww hτw hwH hn.2
  obtain ⟨m₁, hm₁, hm₁Ker, hm₁Fix⟩ :=
    H.exists_trivial_wKer_of_wreath W W2 hD h4 hb hwH hww hτw hQ hgQ hgw hgM hh₁
  obtain ⟨m₂, hm₂, hm₂Fix, hm₂Ker⟩ :=
    H.exists_trivial_wFix_of_wreath W W2 hD h4 hb hwH hww hτw hQ hgQ hgw hgM hh₂
  refine ⟨m₁, hm₁, m₂, hm₂, hm₁Ker, hm₂Fix, ?_⟩
  intro v hv
  obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := exists_mem_wFix_mul_mem_wKer hD w hww hv
  have hh₂Ker : h₂ * v₂ * h₂⁻¹ ∈ wKer hD w :=
    conj_mem_wKer_of_mem_wComm hD (Hn_le_wComm H W W2 hD hwH hh₂) hv₂
  calc (m₁ * m₂) * (v₁ * v₂) * (m₁ * m₂)⁻¹
      = (m₁ * (m₂ * v₁ * m₂⁻¹) * m₁⁻¹) * (m₁ * (m₂ * v₂ * m₂⁻¹) * m₁⁻¹) := by
          group
    _ = (m₁ * v₁ * m₁⁻¹) * (m₁ * (m₂ * v₂ * m₂⁻¹) * m₁⁻¹) := by rw [hm₂Fix v₁ hv₁]
    _ = (m₁ * v₁ * m₁⁻¹) * (m₁ * (h₂ * v₂ * h₂⁻¹) * m₁⁻¹) := by rw [hm₂Ker v₂ hv₂]
    _ = (h₁ * v₁ * h₁⁻¹) * (m₁ * (h₂ * v₂ * h₂⁻¹) * m₁⁻¹) := by rw [hm₁Fix v₁ hv₁]
    _ = (h₁ * v₁ * h₁⁻¹) * (h₂ * v₂ * h₂⁻¹) := by rw [hm₁Ker _ hh₂Ker]
    _ = (n * v₁ * n⁻¹) * (n * v₂ * n⁻¹) := by rw [hact₁ v₁ hv₁, hact₂ v₂ hv₂]
    _ = n * (v₁ * v₂) * n⁻¹ := by group

end CFSG.EvenSporadicStandard.ThStd
