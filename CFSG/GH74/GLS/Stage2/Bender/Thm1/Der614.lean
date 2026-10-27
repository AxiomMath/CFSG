module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der613
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.ExtraCard

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section L614

variable {G : Type} [Group G] [Finite G]

theorem lemma6_14_of (h61 : Prop6_1) (h610 : Lemma6_10) (h611 : Lemma6_11) (h612 : Lemma6_12)
    (h613 : Lemma6_13) : Lemma6_14 := by
  intro G _ _ z k S M p hC Q X hmin
  have hp := hC.prime
  have hp2 := hC.p_ne_two
  have : Fact p.Prime := ⟨hp⟩
  have hz2 : z * z = 1 := mul_self_eq_one_of_orderOf_two hC.orderOf_z
  have hPp : IsPGroup p ↥(Op p M) := isPGroup_Op p hp M
  have hQP : Q ≤ Op p M := hmin.Q_mem.1
  have hQp : IsPGroup p ↥Q := hPp.to_le hQP
  have hQn : M ≤ normalizer (Q : Set G) := le_normalizer_QP (le_normalizer_Op p M) hmin.Q_mem
  have hzQ : z ∈ normalizer (Q : Set G) := hQn hC.z_mem
  have hexp : ∀ x ∈ Q, x ^ p = 1 := hmin.Q_mem.2.2.1
  have hcl : ⁅⁅Q, Q⁆, Q⁆ = ⊥ := hmin.Q_mem.2.2.2.1
  have hE : ExtraG p Q := extraG_of_isExtraspecial (h612 G z k S M p hC Q X hmin)
  have hR : ⁅Q, zpowers z⁆ = Q := h613 G z k S M p hC Q X hmin
  obtain ⟨⟨hXcard, hXinv⟩, hR₁N, -, -, he, -⟩ := h611 G z k S M p hC Q X hmin
  have hRN : NF z M Q := hR ▸ nf_commutator_QP h61 hC hmin.Q_mem
  have hQ'Z : ⁅Q, Q⁆ ≤ zOf Q := hE.comm_eq.le
  have hZQ : zOf Q ≤ Q := inf_le_left
  have hZ0 : zOf Q ≠ ⊥ := by
    intro h
    have := hE.card_Z
    rw [h, Subgroup.card_bot] at this
    exact hp.one_lt.ne this
  have hQ0 : Q ≠ ⊥ := fun h => hZ0 (le_bot_iff.mp (h ▸ hZQ))
  have hpart2 : ∀ Y : Subgroup G, zOf Q ≤ Y → Y ≤ Q → z ∈ normalizer (Y : Set G) → NF z M Y := by
    intro Y hZY hYQ hzY
    by_contra hnot
    have hY0 : Y ≠ ⊥ := fun h => hZ0 (le_bot_iff.mp (h ▸ hZY))
    have hQN : Q ≤ normalizer (Y : Set G) := by
      intro q hq
      refine mem_normalizer_of_forall fun y hy => ?_
      have h1 : q * y * q⁻¹ = ⁅q, y⁆ * y := by rw [commutatorElement_def]; group
      rw [h1]
      exact Y.mul_mem (hZY (hQ'Z (Subgroup.commutator_mem_commutator hq (hYQ hy)))) hy
    exact h610 G z k S M p hC Y Q (hYQ.trans hQP) hY0 hzY hnot (le_inf hQP hQN) hQ0 hR hRN
  refine ⟨?_, hpart2⟩
  have hzK : z ∈ normalizer ((Q ⊓ normalizer (X : Set G) : Subgroup G) : Set G) :=
    mem_normalizer_inf hzQ (Subgroup.le_normalizer hmin.X_inv)
  have hR₁K : ⁅Q ⊓ normalizer (X : Set G), zpowers z⁆ ≤ Q ⊓ normalizer (X : Set G) :=
    commutator_le_left_of_normalizes (Subgroup.zpowers_le.mpr hzK)
  have hR₁z : z ∈ normalizer ((⁅Q ⊓ normalizer (X : Set G), zpowers z⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator_zpowers hzK (mem_Cen_self z)
  have hR₁Q : ⁅Q ⊓ normalizer (X : Set G), zpowers z⁆ ≤ Q := hR₁K.trans inf_le_left
  have hZR₁ : ¬ zOf Q ≤ ⁅Q ⊓ normalizer (X : Set G), zpowers z⁆ := fun h =>
    hR₁N (hpart2 _ h hR₁Q hR₁z)
  have hR₁Z : ⁅Q ⊓ normalizer (X : Set G), zpowers z⁆ ⊓ zOf Q = ⊥ := by
    by_contra hne
    apply hZR₁
    have hcardle : Nat.card ↥(⁅Q ⊓ normalizer (X : Set G), zpowers z⁆ ⊓ zOf Q) ∣ p :=
      hE.card_Z ▸ Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime hp).mp hcardle with h | h
    · exact absurd (Subgroup.eq_bot_of_card_eq _ h) hne
    · have : ⁅Q ⊓ normalizer (X : Set G), zpowers z⁆ ⊓ zOf Q = zOf Q :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hE.card_Z, h])
      exact this ▸ inf_le_left
  have hR₁ab : ∀ a ∈ ⁅Q ⊓ normalizer (X : Set G), zpowers z⁆,
      ∀ b ∈ ⁅Q ⊓ normalizer (X : Set G), zpowers z⁆, a * b = b * a := by
    intro a ha b hb
    have hcZ : ⁅a, b⁆ ∈ zOf Q := hQ'Z (Subgroup.commutator_mem_commutator (hR₁Q ha) (hR₁Q hb))
    have hcR : ⁅a, b⁆ ∈ ⁅Q ⊓ normalizer (X : Set G), zpowers z⁆ := by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb) (Subgroup.inv_mem _ ha))
        (Subgroup.inv_mem _ hb)
    have hmem : ⁅a, b⁆ ∈ ⁅Q ⊓ normalizer (X : Set G), zpowers z⁆ ⊓ zOf Q := ⟨hcR, hcZ⟩
    rw [hR₁Z, Subgroup.mem_bot] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp hmem
  have hfix : ∀ y ∈ Q, z * y * z⁻¹ = y → y ∈ zOf Q := by
    intro y hyQ hyz
    by_contra hyZ
    have hRy := commutator_le_centralizer_of_fixed hp hp2 hz2 hzQ hexp hcl he hyQ hyz
    rw [hR] at hRy
    exact hyZ ⟨hyQ, Subgroup.mem_centralizer_iff.mpr fun q hq =>
      Subgroup.mem_centralizer_singleton_iff.mp (hRy hq)⟩
  have hcent : ∀ b ∈ zOf Q, ∀ x ∈ Q, Commute b x := fun b hb x hx =>
    (Subgroup.mem_centralizer_iff.mp hb.2 x hx).symm
  have hKab : ∀ a ∈ Q ⊓ normalizer (X : Set G), ∀ b ∈ Q ⊓ normalizer (X : Set G), a * b = b * a := by
    have hKexp : ∀ x ∈ Q ⊓ normalizer (X : Set G), x ^ p = 1 := fun x hx => hexp x hx.1
    have hdec : ∀ q ∈ Q ⊓ normalizer (X : Set G), ∃ b ∈ zOf Q,
        ∃ s ∈ ⁅Q ⊓ normalizer (X : Set G), zpowers z⁆, q = b * s := by
      intro q hq
      obtain ⟨b, hbK, s, hs, hbz, hqbs⟩ := exists_fixed_mul hp hp2 hz2 hzK hKexp hq
      exact ⟨b, hfix b hbK.1 hbz, s, hs, hqbs⟩
    intro a ha b hb
    obtain ⟨b₁, hb₁, s₁, hs₁, rfl⟩ := hdec a ha
    obtain ⟨b₂, hb₂, s₂, hs₂, rfl⟩ := hdec b hb
    have hs₁Q := hR₁Q hs₁
    have hs₂Q := hR₁Q hs₂
    have h1 : ⁅b₁ * s₁, b₂ * s₂⁆ = 1 := by
      rw [commutator_mul_central (hcent b₁ hb₁ s₁ hs₁Q) (hcent b₁ hb₁ s₂ hs₂Q)
        (hcent b₁ hb₁ b₂ (hZQ hb₂)) (hcent b₂ hb₂ s₁ hs₁Q) (hcent b₂ hb₂ s₂ hs₂Q)]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hR₁ab s₁ hs₁ s₂ hs₂)
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  obtain ⟨x, hxX, hx1⟩ : ∃ x ∈ X, x ≠ 1 := by
    by_contra hno
    push Not at hno
    exact hmin.X_ne (eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (hno x hx))
  have hxQ : x ∈ Q := hmin.X_le hxX
  have hxp : x ^ p = 1 := hexp x hxQ
  have hXeq : zpowers x = X :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxX)
      (by rw [Nat.card_zpowers, orderOf_eq_prime hxp hx1, hXcard])
  have hxZ : x ∉ zOf Q := by
    intro hxZ
    have h1 : z * x * z⁻¹ = x := by
      have := Subgroup.mem_centralizer_singleton_iff.mp (he hxZ)
      rw [← this]; group
    exact ne_inv_of_prime hp hp2 hx1 hxp (h1.symm.trans (hXinv x hxX))
  have hK'K : Q ⊓ centralizer ({x} : Set G) ≤ Q ⊓ normalizer (X : Set G) := fun c hc =>
    ⟨hc.1, by
      have := mem_normalizer_zpowers_of_comm (z := c) (v := x)
        (Subgroup.mem_centralizer_singleton_iff.mp hc.2)
      rwa [hXeq] at this⟩
  exact card_eq_prime_cube hp hQ'Z hE.card_Z hxQ hxZ
    (fun a ha b hb => hKab a (hK'K ha) b (hK'K hb))

end L614

end CFSG.GH74.GLS.Stage2.Bender.Thm1
