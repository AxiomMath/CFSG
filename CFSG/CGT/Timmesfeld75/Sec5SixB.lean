module

public import CFSG.CGT.Timmesfeld75.Sec5SixA
public import CFSG.CGT.Timmesfeld75.Sec5FiveFinal

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G}

section Six

variable [Finite G]

theorem card_le_normIn_mul_card_secA (hP : MaxPair T T₁) (hS : Sec3Global T)
    (hI : Sec3IsoGlobal T) {g : G} (hne : conjSubgroup g T ≠ T)
    (hL : normIn T (conjSubgroup g T) ≠ ⊥) (hA1 : secA T T₁ ≠ ⊥) :
    Nat.card T ≤ Nat.card (normIn T (conjSubgroup g T)) * Nat.card (secA T T₁) := by
  have hsec := hS g hne hL
  obtain ⟨hN, f, hf, hiso⟩ := hI g hne hL
  have := hN
  have hmul := hsec.card_eq_mul hf hiso
  have h2 : 2 ^ f ≤ Nat.card (secA T T₁) :=
    hsec.two_pow_le_card_of_normal_normalizer hf hiso hA1
      ((secA_le_normIn_conj hP hS hne hL).trans (Cfg.normIn_le_cfgM_left _ _))
      fun n hn => conjSubgroup_secA hn
  rw [hmul]
  exact Nat.mul_le_mul_left _ h2

omit [Finite G] in
theorem secR₁_eq_bot_of_secA_eq_bot (h : secA T T₁ = ⊥) : secR₁ T T₁ = ⊥ := by
  unfold secR₁
  rw [h]
  simp [conjSubgroup_bot]

theorem card_lt_of_not_isUIdx (hP : MaxPair T T₁) (hS : Sec3Global T) (hI : Sec3IsoGlobal T)
    (hA1 : secA T T₁ ≠ ⊥) {g : G}
    (hg : conjSubgroup g (secA T T₁) ≤ Subgroup.normalizer (T : Set G))
    (hgT : conjSubgroup g T ≠ T) (hnu : ¬ IsUIdx T T₁ g) :
    Nat.card T < Nat.card (secA T T₁) * Nat.card (normIn T T₁) := by
  have hL₂ : normIn (conjSubgroup g T) T ≠ ⊥ := by
    intro hbot
    apply hA1
    have : conjSubgroup g (secA T T₁) ≤ ⊥ := by
      rw [← hbot]
      exact fun x hx => mem_normIn.2 ⟨conjSubgroup_mono secA_le_left hx, hg hx⟩
    exact conjSubgroup_eq_bot_iff.1 (le_bot_iff.1 this)
  have hL : normIn T (conjSubgroup g T) ≠ ⊥ := normIn_ne_bot_of_conj hP.wc hgT hL₂
  have hsec := hS g hgT hL
  have hle := hP.maximal g hgT
  have hne' : Nat.card (normIn T (conjSubgroup g T)) ≠ Nat.card (normIn T T₁) := fun h' =>
    hnu ⟨hgT, by rw [hsec.card_normIn_swap]; exact h'⟩
  have hlt : Nat.card (normIn T (conjSubgroup g T)) < Nat.card (normIn T T₁) :=
    lt_of_le_of_ne hle hne'
  have h2 := card_le_normIn_mul_card_secA hP hS hI hgT hL hA1
  have hApos : 0 < Nat.card (secA T T₁) := Nat.card_pos
  calc Nat.card T ≤ Nat.card (normIn T (conjSubgroup g T)) * Nat.card (secA T T₁) := h2
    _ < Nat.card (normIn T T₁) * Nat.card (secA T T₁) := Nat.mul_lt_mul_of_pos_right hlt hApos
    _ = Nat.card (secA T T₁) * Nat.card (normIn T T₁) := mul_comm _ _

theorem isUIdx_of_secR₁_nonabelian (h1 : Sec4NoA) (h3 : Sec4Nine) (hy : StepHyp T T₁)
    (hS : Sec3Global T) (hI : Sec3IsoGlobal T)
    (hTO : CFSG.Timmesfeld.Bridge.Asc72.TheoremOne) (hBW : BenderWCInput)
    (hnab : ¬ ∀ x ∈ secR₁ T T₁, ∀ y ∈ secR₁ T T₁, x * y = y * x) {g : G}
    (hg : conjSubgroup g (secA T T₁) ≤ Subgroup.normalizer (T : Set G))
    (hgT : conjSubgroup g T ≠ T) : IsUIdx T T₁ g := by
  have hA1 : secA T T₁ ≠ ⊥ := fun h => hnab (by
    rw [secR₁_eq_bot_of_secA_eq_bot h]
    intro x hx y hy'
    rw [Subgroup.mem_bot] at hx hy'
    rw [hx, hy'])
  by_contra hnu
  exact hnab (secR₁_comm_of_card_lt h1 h3 hy hS hI hTO hBW
    (card_lt_of_not_isUIdx hy.pair hS hI hA1 hg hgT hnu))

end Six

@[expose] def Sec56StepOne : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G), StepHyp T T₁ → Sec3Global T → Sec3IsoGlobal T →
    (¬ ∀ x ∈ secR₁ T T₁, ∀ y ∈ secR₁ T T₁, x * y = y * x) →
    IsPGroup 2 ↥(secR₁ T T₁) →
    (∀ x ∈ secR₁ T T₁, ∀ y ∈ secR₁ T T₁, ⁅x, y⁆ ∈ secA T T₁) →
    Nat.card (secA T T₁) * Nat.card (normIn T T₁) ≤ Nat.card T →
    (∀ g : G, conjSubgroup g (secA T T₁) ≤ Subgroup.normalizer (T : Set G) →
      conjSubgroup g T ≠ T → IsUIdx T T₁ g) →
    ∀ g h : G, IsUIdx T T₁ g → IsUIdx T T₁ h →
      (∀ a ∈ conjSubgroup g (secA T T₁), ∀ x ∈ secR₁ T T₁, a * x = x * a) →
      ∃ n ∈ Subgroup.normalizer (T : Set G),
        conjSubgroup n (conjSubgroup g (secA T T₁)) = conjSubgroup h (secA T T₁)

@[expose] def Sec56CorB : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G), StepHyp T T₁ → Sec3Global T → Sec3IsoGlobal T →
    (¬ ∀ x ∈ secR₁ T T₁, ∀ y ∈ secR₁ T T₁, x * y = y * x) →
    IsPGroup 2 ↥(secR₁ T T₁) →
    (∀ x ∈ secR₁ T T₁, ∀ y ∈ secR₁ T T₁, ⁅x, y⁆ ∈ secA T T₁) →
    Nat.card (secA T T₁) * Nat.card (normIn T T₁) ≤ Nat.card T →
    (∀ g : G, conjSubgroup g (secA T T₁) ≤ Subgroup.normalizer (T : Set G) →
      conjSubgroup g T ≠ T → IsUIdx T T₁ g) →
    (∀ g : G, IsUIdx T T₁ g →
      ¬ ∀ a ∈ conjSubgroup g (secA T T₁), ∀ x ∈ secR₁ T T₁, a * x = x * a) → False

@[expose] def Sec56Residue : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G), StepHyp T T₁ → Sec3Global T → Sec3IsoGlobal T →
    (¬ ∀ x ∈ secR₁ T T₁, ∀ y ∈ secR₁ T T₁, x * y = y * x) →
    IsPGroup 2 ↥(secR₁ T T₁) →
    (∀ x ∈ secR₁ T T₁, ∀ y ∈ secR₁ T T₁, ⁅x, y⁆ ∈ secA T T₁) →
    Nat.card (secA T T₁) * Nat.card (normIn T T₁) ≤ Nat.card T →
    (∀ g : G, conjSubgroup g (secA T T₁) ≤ Subgroup.normalizer (T : Set G) →
      conjSubgroup g T ≠ T → IsUIdx T T₁ g) → False

theorem sec56Residue_of (hs1 : Sec56StepOne) (hs2 : Sec56CorB) : Sec56Residue := by
  intro G _ T T₁ hy hS hI hnab h2grp hR' hcard hplus
  have : Finite G := hy.finite
  refine hs2 G T T₁ hy hS hI hnab h2grp hR' hcard hplus fun g hg hcent => hnab ?_
  have hall : ∀ h : G, IsUIdx T T₁ h → ∀ b ∈ conjSubgroup h (secA T T₁),
      ∀ x ∈ secR₁ T T₁, b * x = x * b := by
    intro h hh b hb x hx
    obtain ⟨n, hn, hconj⟩ := hs1 G T T₁ hy hS hI hnab h2grp hR' hcard hplus g h hg hh hcent
    rw [← hconj] at hb
    have hb' : n⁻¹ * b * n ∈ conjSubgroup g (secA T T₁) := mem_conjSubgroup.1 hb
    have hx' : n⁻¹ * x * n ∈ secR₁ T T₁ := by
      have h5 := conjSubgroup_secR₁ (T₁ := T₁) ((Subgroup.normalizer (T : Set G)).inv_mem hn)
      have h6 := conj_mem_conjSubgroup n⁻¹ hx
      rw [h5] at h6
      simpa using h6
    have h7 := hcent _ hb' _ hx'
    calc b * x = n * ((n⁻¹ * b * n) * (n⁻¹ * x * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * x * n) * (n⁻¹ * b * n)) * n⁻¹ := by rw [h7]
      _ = x * b := by group
  exact secR₁_comm_of_gen_comm fun i j hi hj a ha x hx => by
    refine hall i hi a ha x ?_
    unfold secR₁
    exact (le_iSup₂ (f := fun (k : G) (_ : IsUIdx T T₁ k) => conjSubgroup k (secA T T₁)) j hj) hx

theorem sec56 (hres : Sec56Residue) (h1 : Sec4NoA) (h3 : Sec4Nine) (hy : StepHyp T T₁)
    (hS : Sec3Global T) (hI : Sec3IsoGlobal T)
    (hTO : CFSG.Timmesfeld.Bridge.Asc72.TheoremOne) (hBW : BenderWCInput) :
    ∀ x ∈ secR₁ T T₁, ∀ y ∈ secR₁ T T₁, x * y = y * x := by
  have : Finite G := hy.finite
  by_contra hnab
  have h55 := sec55 h1 h3 hy hS hI hTO hBW
  refine hres G T T₁ hy hS hI hnab h55.2.2.1 h55.2.2.2 ?_ fun g hg hgT =>
    isUIdx_of_secR₁_nonabelian h1 h3 hy hS hI hTO hBW hnab hg hgT
  by_contra hcard
  push Not at hcard
  exact hnab (secR₁_comm_of_card_lt h1 h3 hy hS hI hTO hBW hcard)

end CFSG.CGT.Timmesfeld75
