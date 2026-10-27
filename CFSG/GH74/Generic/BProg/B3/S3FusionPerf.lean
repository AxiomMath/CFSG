module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.NoncommCoprod

public section

open Subgroup
open scoped commutatorElement

namespace CFSG.GH74.Generic.BProg.B3

namespace S3Fusion
theorem exists_perfect_lift {A B : Type*} [Group A] [Group B] [Finite A] (f : A →* B)
    {P : Subgroup B} (hP : ⁅P, P⁆ = P) (hf : P ≤ f.range) :
    ∃ Q : Subgroup A, ⁅Q, Q⁆ = Q ∧ Q.map f = P := by
  classical
  obtain ⟨Q, hQ, hmin⟩ := WellFounded.has_min (wellFounded_lt (α := Subgroup A))
    {Q : Subgroup A | Q.map f = P} ⟨P.comap f, Subgroup.map_comap_eq_self hf⟩
  refine ⟨Q, ?_, hQ⟩
  have hle : ⁅Q, Q⁆ ≤ Q := Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact Q.mul_mem (Q.mul_mem (Q.mul_mem ha hb) (Q.inv_mem ha)) (Q.inv_mem hb)
  by_contra hne
  have hlt : ⁅Q, Q⁆ < Q := lt_of_le_of_ne hle hne
  refine hmin ⁅Q, Q⁆ ?_ hlt
  show (⁅Q, Q⁆).map f = P
  rw [Subgroup.map_commutator]
  show ⁅Q.map f, Q.map f⁆ = P
  rw [hQ, hP]



theorem commutatorElement_central_mul_left {H : Type*} [Group H] {a c z : H}
    (hz : ∀ h : H, z * h = h * z) : ⁅z * a, c⁆ = ⁅a, c⁆ := by
  simp only [commutatorElement_def]
  have : z * (a * c * a⁻¹) * z⁻¹ = a * c * a⁻¹ := by rw [hz (a * c * a⁻¹)]; group
  calc z * a * c * (z * a)⁻¹ * c⁻¹ = (z * (a * c * a⁻¹) * z⁻¹) * c⁻¹ := by group
    _ = a * c * a⁻¹ * c⁻¹ := by rw [this]

theorem commutatorElement_central_mul_right {H : Type*} [Group H] {a b w : H}
    (hw : ∀ h : H, w * h = h * w) : ⁅a, w * b⁆ = ⁅a, b⁆ := by
  simp only [commutatorElement_def]
  have : w * (a * b * a⁻¹ * b⁻¹) * w⁻¹ = a * b * a⁻¹ * b⁻¹ := by
    rw [hw (a * b * a⁻¹ * b⁻¹)]; group
  calc a * (w * b) * a⁻¹ * (w * b)⁻¹ = w * (a * b * a⁻¹ * b⁻¹) * w⁻¹ := by
        have haw : a * w = w * a := (hw a).symm
        calc a * (w * b) * a⁻¹ * (w * b)⁻¹ = (a * w) * b * a⁻¹ * b⁻¹ * w⁻¹ := by group
          _ = (w * a) * b * a⁻¹ * b⁻¹ * w⁻¹ := by rw [haw]
          _ = w * (a * b * a⁻¹ * b⁻¹) * w⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := this

theorem eq_one_of_mem_commutator_of_cyclic_sylow {C : Type*} [Group C] [Finite C] (P : Sylow 2 C)
    (hP : IsCyclic ↥P) {z : C} (hz : z ∈ _root_.commutator C) (hz2 : z * z = 1) : z = 1 := by
  classical
  by_contra hz1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzord : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hz2) hz1
  have hdvd : 2 ∣ Nat.card C := by rw [← hzord]; exact orderOf_dvd_natCard z
  have hmin : (Nat.card C).minFac = 2 := Nat.minFac_eq_two_iff _ |>.mpr hdvd
  let φ := MonoidHom.transferSylow P (hP.normalizer_le_centralizer hmin)
  have : IsCyclic ↥P := hP
  have hker : _root_.commutator C ≤ φ.ker := by
    rw [commutator_def]
    refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm' _ _)
  have hzk : z ∈ φ.ker := hker hz
  have h1 : 2 ∣ Nat.card φ.ker := by
    have := Subgroup.orderOf_dvd_natCard φ.ker hzk
    rwa [hzord] at this
  exact MonoidHom.not_dvd_card_ker_transferSylow P (hP.normalizer_le_centralizer hmin) h1


section Perfect

variable {G : Type*} [Group G]

def maxPerfect (M : Subgroup G) : Subgroup G := sSup {P : Subgroup G | P ≤ M ∧ ⁅P, P⁆ = P}

theorem le_maxPerfect {M P : Subgroup G} (hPM : P ≤ M) (hP : ⁅P, P⁆ = P) : P ≤ maxPerfect M :=
  le_sSup ⟨hPM, hP⟩

theorem maxPerfect_le (M : Subgroup G) : maxPerfect M ≤ M :=
  sSup_le fun _ hP => hP.1

theorem commutator_le_self' (P : Subgroup G) : ⁅P, P⁆ ≤ P := Subgroup.commutator_le.mpr fun a ha b hb => by
  rw [commutatorElement_def]
  exact P.mul_mem (P.mul_mem (P.mul_mem ha hb) (P.inv_mem ha)) (P.inv_mem hb)

theorem maxPerfect_perfect (M : Subgroup G) : ⁅maxPerfect M, maxPerfect M⁆ = maxPerfect M := by
  refine le_antisymm (commutator_le_self' _) ?_
  refine sSup_le fun P hP => ?_
  calc P = ⁅P, P⁆ := hP.2.symm
    _ ≤ ⁅maxPerfect M, maxPerfect M⁆ :=
      Subgroup.commutator_mono (le_maxPerfect hP.1 hP.2) (le_maxPerfect hP.1 hP.2)

theorem conj_mem_maxPerfect {M : Subgroup G} {n : G} (hn : ∀ g ∈ M, n * g * n⁻¹ ∈ M) {θ : G}
    (hθ : θ ∈ maxPerfect M) : n * θ * n⁻¹ ∈ maxPerfect M := by
  have hP : ⁅(maxPerfect M).map (MulAut.conj n).toMonoidHom, (maxPerfect M).map (MulAut.conj n).toMonoidHom⁆ =
      (maxPerfect M).map (MulAut.conj n).toMonoidHom := by
    rw [← Subgroup.map_commutator, maxPerfect_perfect]
  have hle : (maxPerfect M).map (MulAut.conj n).toMonoidHom ≤ M := by
    rintro _ ⟨g, hg, rfl⟩
    exact hn g (maxPerfect_le M hg)
  exact le_maxPerfect hle hP ⟨θ, hθ, by simp [MulAut.conj_apply]⟩

end Perfect

theorem swap_le {H : Type*} [Group H] (α : H ≃* H) {J N : Subgroup H}
    (hJN : ∀ h : H, ∃ j ∈ J, ∃ n ∈ N, h = j * n) (hcomm : ∀ j ∈ J, ∀ n ∈ N, j * n = n * j)
    (hJperf : ⁅J, J⁆ = J)
    (hJq : ∀ A : Subgroup H, A ≤ J → (∀ a ∈ A, ∀ j ∈ J, j * a * j⁻¹ ∈ A) →
      (∀ a ∈ A, ∀ j ∈ J, a * j = j * a) ∨ J ≤ A)
    {jy : H} (hjyJ : jy ∈ J) (hjy2 : jy * jy = 1) (hjyun : ∀ i ∈ J, i * i = 1 → i = 1 ∨ i = jy)
    (hα : α jy ∉ J) : ∀ a ∈ J, α a ∈ N := by
  classical
  set D : Subgroup H := J.map α.toMonoidHom with hD
  have hJnorm : ∀ h : H, ∀ a ∈ J, h * a * h⁻¹ ∈ J := by
    intro h a ha
    obtain ⟨j, hj, n, hn, rfl⟩ := hJN h
    have hna : n * a = a * n := (hcomm a ha n hn).symm
    have : j * n * a * (j * n)⁻¹ = j * a * j⁻¹ := by
      calc j * n * a * (j * n)⁻¹ = j * (n * a) * n⁻¹ * j⁻¹ := by group
        _ = j * (a * n) * n⁻¹ * j⁻¹ := by rw [hna]
        _ = j * a * j⁻¹ := by group
    rw [this]
    exact J.mul_mem (J.mul_mem hj ha) (J.inv_mem hj)
  have hDnorm : ∀ h : H, ∀ d ∈ D, h * d * h⁻¹ ∈ D := by
    rintro h _ ⟨a, ha, rfl⟩
    refine ⟨(α.symm h) * a * (α.symm h)⁻¹, hJnorm _ a ha, ?_⟩
    simp
  have hDperf : ⁅D, D⁆ = D := by
    rw [hD, ← Subgroup.map_commutator, hJperf]
  rcases hJq (D ⊓ J) inf_le_right (fun a ha j hj => ⟨hDnorm j a ha.1, hJnorm j a ha.2⟩) with hcen | hJA
  ·
    have hcommDJ : ∀ d ∈ D, ∀ j ∈ J, ⁅d, j⁆ ∈ D ⊓ J := by
      intro d hd j hj
      refine ⟨?_, ?_⟩
      · have e : ⁅d, j⁆ = d * (j * d⁻¹ * j⁻¹) := by simp only [commutatorElement_def]; group
        rw [e]
        exact D.mul_mem hd (hDnorm j d⁻¹ (D.inv_mem hd))
      · have e : ⁅d, j⁆ = (d * j * d⁻¹) * j⁻¹ := by simp only [commutatorElement_def]
        rw [e]
        exact J.mul_mem (hJnorm d j hj) (J.inv_mem hj)
    have hcentral : ∀ c ∈ D ⊓ J, ∀ h : H, c * h = h * c := by
      intro c hc h
      obtain ⟨j', hj', n', hn', rfl⟩ := hJN h
      calc c * (j' * n') = (c * j') * n' := (mul_assoc _ _ _).symm
        _ = (j' * c) * n' := by rw [hcen c hc j' hj']
        _ = j' * (c * n') := mul_assoc _ _ _
        _ = j' * (n' * c) := by rw [hcomm c hc.2 n' hn']
        _ = (j' * n') * c := (mul_assoc _ _ _).symm
    have hDJle : ⁅D, J⁆ ≤ D ⊓ J := Subgroup.commutator_le.mpr hcommDJ
    have h1 : ⁅⁅D, J⁆, D⁆ = ⊥ := by
      rw [eq_bot_iff]
      refine Subgroup.commutator_le.mpr fun c hc d _ => ?_
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hcentral c (hDJle hc) d
    have h2 : ⁅⁅J, D⁆, D⁆ = ⊥ := by rw [Subgroup.commutator_comm J D]; exact h1
    have h3 : ⁅⁅D, D⁆, J⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
    rw [hDperf] at h3
    have hDJ : ∀ d ∈ D, ∀ j ∈ J, d * j = j * d := by
      intro d hd j hj
      have : ⁅d, j⁆ ∈ (⊥ : Subgroup H) := h3 ▸ Subgroup.commutator_mem_commutator hd hj
      rwa [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    have hDN : D ≤ N := by
      calc D = ⁅D, D⁆ := hDperf.symm
        _ ≤ N := by
          refine Subgroup.commutator_le.mpr fun d₁ hd₁ d₂ hd₂ => ?_
          have hdec : ∀ d ∈ D, ∃ z : H, (∀ h : H, z * h = h * z) ∧ ∃ n ∈ N, d = z * n := by
            intro d hd
            obtain ⟨j₀, hj₀, n₀, hn₀, rfl⟩ := hJN d
            refine ⟨j₀, ?_, n₀, hn₀, rfl⟩
            intro h
            obtain ⟨j', hj', n', hn', rfl⟩ := hJN h
            have hj₀c : j₀ * j' = j' * j₀ := by
              have := hDJ (j₀ * n₀) hd j' hj'
              have hn₀j : n₀ * j' = j' * n₀ := (hcomm j' hj' n₀ hn₀).symm
              calc j₀ * j' = j₀ * j' * n₀ * n₀⁻¹ := by group
                _ = j₀ * (j' * n₀) * n₀⁻¹ := by rw [mul_assoc j₀ j' n₀]
                _ = j₀ * (n₀ * j') * n₀⁻¹ := by rw [hn₀j]
                _ = (j₀ * n₀) * j' * n₀⁻¹ := by group
                _ = j' * (j₀ * n₀) * n₀⁻¹ := by rw [this]
                _ = j' * j₀ := by
                  calc j' * (j₀ * n₀) * n₀⁻¹ = j' * j₀ * (n₀ * n₀⁻¹) := by group
                    _ = j' * j₀ := by rw [mul_inv_cancel, mul_one]
            have hj₀n : j₀ * n' = n' * j₀ := hcomm j₀ hj₀ n' hn'
            calc j₀ * (j' * n') = (j₀ * j') * n' := (mul_assoc _ _ _).symm
              _ = (j' * j₀) * n' := by rw [hj₀c]
              _ = j' * (j₀ * n') := mul_assoc _ _ _
              _ = j' * (n' * j₀) := by rw [hj₀n]
              _ = (j' * n') * j₀ := (mul_assoc _ _ _).symm
          obtain ⟨z₁, hz₁, n₁, hn₁, rfl⟩ := hdec d₁ hd₁
          obtain ⟨z₂, hz₂, n₂, hn₂, rfl⟩ := hdec d₂ hd₂
          rw [commutatorElement_central_mul_left hz₁, commutatorElement_central_mul_right hz₂,
            commutatorElement_def]
          exact N.mul_mem (N.mul_mem (N.mul_mem hn₁ hn₂) (N.inv_mem hn₁)) (N.inv_mem hn₂)
    intro a ha
    exact hDN ⟨a, ha, rfl⟩
  · exfalso
    have hjyD : jy ∈ D := (hJA hjyJ).1
    obtain ⟨a, ha, haj⟩ := hjyD
    have haj' : α a = jy := haj
    have ha2 : a * a = 1 := by
      apply α.injective
      rw [map_mul, haj', hjy2, map_one]
    rcases hjyun a ha ha2 with h1 | h1
    · apply hα
      have : jy = 1 := by rw [← haj', h1, map_one]
      rw [this, map_one]
      exact J.one_mem
    · apply hα
      rw [h1] at haj'
      rw [haj']
      exact hjyJ


theorem commutatorElement_mul_mul_of_commute {H : Type*} [Group H] {A B : Subgroup H}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {a₁ a₂ : H} (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) {b₁ b₂ : H}
    (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B) : ⁅a₁ * b₁, a₂ * b₂⁆ = ⁅a₁, a₂⁆ * ⁅b₁, b₂⁆ := by
  let Ψ : ↥A × ↥B →* H := MonoidHom.noncommCoprod A.subtype B.subtype
    (fun a b => (hAB a a.2 b b.2 : (a : H) * b = b * a))
  have hΨ : ∀ (p : ↥A × ↥B), Ψ p = (p.1 : H) * p.2 := fun p =>
    MonoidHom.noncommCoprod_apply _ _ _ p
  have key := map_commutatorElement Ψ (⟨a₁, ha₁⟩, ⟨b₁, hb₁⟩) (⟨a₂, ha₂⟩, ⟨b₂, hb₂⟩)
  rw [hΨ, hΨ, hΨ] at key
  simpa [commutatorElement_def] using key.symm

end S3Fusion

end CFSG.GH74.Generic.BProg.B3
