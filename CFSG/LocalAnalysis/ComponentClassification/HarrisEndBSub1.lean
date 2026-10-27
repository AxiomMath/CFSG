module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBLayer

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42 CFSG.ComponentClassification.J2Cover
open scoped commutatorElement

namespace EndB

section SupZpowers

variable {G : Type*} [Group G] {K : Subgroup G} {u : G}

theorem mem_sup_zpowers_iff (hn : ∀ k ∈ K, u * k * u⁻¹ ∈ K) (hu2 : u ^ 2 ∈ K) {x : G} :
    x ∈ K ⊔ zpowers u ↔ x ∈ K ∨ x * u⁻¹ ∈ K := by
  have hn' : ∀ k ∈ K, u⁻¹ * k * u ∈ K := fun k hk => by
    have h1 := hn k hk
    have h2 : u⁻¹ * k * u = (u ^ 2)⁻¹ * (u * k * u⁻¹) * u ^ 2 := by group
    rw [h2]
    exact mul_mem (mul_mem (inv_mem hu2) h1) hu2
  let S : Subgroup G :=
    { carrier := {x | x ∈ K ∨ x * u⁻¹ ∈ K}
      mul_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · exact Or.inl (mul_mem ha hb)
        · exact Or.inr (by rw [mul_assoc]; exact mul_mem ha hb)
        · right
          rw [show a * b * u⁻¹ = (a * u⁻¹) * (u * b * u⁻¹) by group]
          exact mul_mem ha (hn b hb)
        · left
          rw [show a * b = (a * u⁻¹) * (u * (b * u⁻¹) * u⁻¹) * u ^ 2 by group]
          exact mul_mem (mul_mem ha (hn _ hb)) hu2
      one_mem' := Or.inl (one_mem K)
      inv_mem' := by
        rintro a (ha | ha)
        · exact Or.inl (inv_mem ha)
        · right
          rw [show a⁻¹ * u⁻¹ = (u⁻¹ * (a * u⁻¹)⁻¹ * u) * (u ^ 2)⁻¹ by group]
          exact mul_mem (hn' _ (inv_mem ha)) (inv_mem hu2) }
  constructor
  · intro hx
    have hle : K ⊔ zpowers u ≤ S := sup_le (fun k hk => Or.inl hk) (zpowers_le.mpr (Or.inr (by
      rw [mul_inv_cancel]; exact one_mem K)))
    exact hle hx
  · rintro (hx | hx)
    · exact mem_sup_left hx
    · rw [show x = (x * u⁻¹) * u by group]
      exact mul_mem (mem_sup_left hx) (mem_sup_right (mem_zpowers u))

theorem card_sup_zpowers [Finite G] (hn : ∀ k ∈ K, u * k * u⁻¹ ∈ K) (hu2 : u ^ 2 ∈ K)
    (hu : u ∉ K) : Nat.card ↥(K ⊔ zpowers u) = 2 * Nat.card K := by
  have hidx : (K.subgroupOf (K ⊔ zpowers u)).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨u, mem_sup_right (mem_zpowers u)⟩, fun b => ?_⟩
    simp only [mem_subgroupOf, Subgroup.coe_mul]
    rcases (mem_sup_zpowers_iff hn hu2).mp b.2 with hb | hb
    · refine Or.inr ⟨hb, fun h => hu ?_⟩
      have := mul_mem (inv_mem hb) h
      rwa [show (b : G)⁻¹ * (b * u) = u by group] at this
    · refine Or.inl ⟨?_, fun h => hu ?_⟩
      · rw [show (b : G) * u = (b * u⁻¹) * u ^ 2 by group]
        exact mul_mem hb hu2
      · have := mul_mem (inv_mem hb) h
        rwa [show ((b : G) * u⁻¹)⁻¹ * b = u by group] at this
  have h := Subgroup.card_mul_index (K.subgroupOf (K ⊔ zpowers u))
  rw [hidx, Nat.card_congr (subgroupOfEquivOfLe le_sup_left).toEquiv] at h
  rw [← h, mul_comm]

end SupZpowers

end EndB

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

theorem Setting46e.betaBar_mem_pCore (hs : Setting46e t L p f S w z V i j) :
    betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) ∈
      pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
  have : betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) ∈
      pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓ centralizer {hs.setup.tBar i j} := by
    rw [hs.pCore_inf_centralizer_tBar]
    exact mem_zpowers _
  exact (mem_inf.mp this).1

namespace EndB.JLayer

variable {hs : Setting46e t L p f S w z V i j}
  {π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* P}

theorem betaBar_not_mem_layer
    (hJ : JLayer hs π) (hπi : Function.Injective π) :
    betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) ∉
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
  intro h
  have h1 : hJ.theta (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = 1 :=
    (hJ.theta_eq_one_iff _).mpr hs.betaBar_mem_pCore
  rw [show betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) =
    ((⟨_, h⟩ : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) :
      MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) from rfl, hJ.theta_conj] at h1
  have h2 : π ⟨_, h⟩ = 1 := conj_injective_P (by rw [h1, map_one])
  have h3 : (⟨_, h⟩ : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) = 1 :=
    hπi (by rw [h2, map_one])
  exact hs.betaBar_ne_one (congrArg Subtype.val h3)

theorem exists_mem_A
    (hJ : JLayer hs π)
    (hQ : pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) =
      zpowers (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
    (g : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :
    ∃ a ∈ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔ zpowers (hs.setup.tBar i j),
      g = a ∨ g = betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) * a := by
  have hβ2 := orderOf_eq_prime hs.betaBar_sq hs.betaBar_ne_one
  have hcomm : ∀ k ∈ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
      ∀ n ∈ zpowers (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)), k * n = n * k :=
    fun k _ n hn => (mem_center_iff.mp (zpowers_le.mpr (betaBar_mem_center _) hn) k)
  have hdec : ∀ x ∈ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
      pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
      ∃ e ∈ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
        x = e ∨ x = betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) * e := by
    intro x hx
    rw [hQ] at hx
    obtain ⟨e, he, q, hq, rfl⟩ := M12Cover.CyclicKernel.exists_mul_of_mem_sup_of_commute hcomm hx
    rcases eq_one_or_eq_of_mem_zpowers hβ2 hq with rfl | rfl
    · exact ⟨e, he, Or.inl (mul_one e)⟩
    · exact ⟨e, he, Or.inr (hcomm e he _ (mem_zpowers _))⟩
  have hct : ∀ e, betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) * e =
      e * betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) :=
    fun e => (mem_center_iff.mp (betaBar_mem_center _) e).symm
  rcases hJ.mem_sup_or g with hg | hg
  · obtain ⟨e, he, h | h⟩ := hdec g hg
    · exact ⟨e, mem_sup_left he, Or.inl h⟩
    · exact ⟨e, mem_sup_left he, Or.inr h⟩
  · obtain ⟨e, he, h | h⟩ := hdec _ hg
    · refine ⟨e * hs.setup.tBar i j, mul_mem (mem_sup_left he) (mem_sup_right (mem_zpowers _)),
        Or.inl ?_⟩
      rw [← h]
      group
    · refine ⟨e * hs.setup.tBar i j, mul_mem (mem_sup_left he) (mem_sup_right (mem_zpowers _)),
        Or.inr ?_⟩
      rw [← mul_assoc, ← h]
      group

theorem betaBar_not_mem_A
    (hJ : JLayer hs π) (hπi : Function.Injective π) :
    betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) ∉
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔ zpowers (hs.setup.tBar i j) := by
  have hn : ∀ k ∈ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
      hs.setup.tBar i j * k * (hs.setup.tBar i j)⁻¹ ∈
        layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := fun k hk =>
    (inferInstance : (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).Normal).conj_mem k hk _
  have hsq : hs.setup.tBar i j ^ 2 ∈ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
    rw [hs.tBar_sq]
    exact one_mem _
  intro h
  rcases (mem_sup_zpowers_iff hn hsq).mp h with h1 | h1
  · exact hJ.betaBar_not_mem_layer hπi h1
  · apply hJ.alpha_not_mem
    rw [hJ.theta_mem_inner_iff]
    rw [show hs.setup.tBar i j = (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) *
      (hs.setup.tBar i j)⁻¹)⁻¹ * betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) by group]
    exact mul_mem (mem_sup_left (inv_mem h1)) (mem_sup_right hs.betaBar_mem_pCore)

theorem commutator_mem_A
    (hJ : JLayer hs π)
    (hQ : pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) =
      zpowers (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
    (g₁ g₂ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :
    ⁅g₁, g₂⁆ ∈
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔ zpowers (hs.setup.tBar i j) := by
  have hct : ∀ e, betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) * e =
      e * betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) :=
    fun e => (mem_center_iff.mp (betaBar_mem_center _) e).symm
  have hl : ∀ a b : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j),
      ⁅betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) * a, b⁆ = ⁅a, b⁆ := by
    intro a b
    rw [commutatorElement_def, commutatorElement_def, hct a,
      show a * betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) * b *
        (a * betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))⁻¹ * b⁻¹ =
        a * (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) * b) *
          (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))⁻¹ * a⁻¹ * b⁻¹ by group, hct b]
    group
  have hr : ∀ a b : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j),
      ⁅a, betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) * b⁆ = ⁅a, b⁆ := by
    intro a b
    rw [← commutatorElement_inv, hl, commutatorElement_inv]
  obtain ⟨a₁, ha₁, h₁⟩ := hJ.exists_mem_A hQ g₁
  obtain ⟨a₂, ha₂, h₂⟩ := hJ.exists_mem_A hQ g₂
  have : ⁅g₁, g₂⁆ = ⁅a₁, a₂⁆ := by
    rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;> simp only [hl, hr]
  rw [this, commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha₁ ha₂) (inv_mem ha₁)) (inv_mem ha₂)

end EndB.JLayer

end CFSG.ComponentClassification.HarrisLit
