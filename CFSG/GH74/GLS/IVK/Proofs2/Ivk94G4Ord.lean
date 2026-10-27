module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4Assembly

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk94

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
open scoped MatrixGroups

theorem exists_prod_subgroup {K : Type} [Group K] [Finite K] {I₁ I₂ : Subgroup K}
    (hcomm : ∀ x ∈ I₁, ∀ y ∈ I₂, x * y = y * x) (hcard : Nat.card ↥(I₁ ⊓ I₂) = 2) :
    ∃ A : Subgroup K, (∀ x ∈ I₁, x ∈ A) ∧ (∀ y ∈ I₂, y ∈ A) ∧
      (∀ g : K, (∀ x ∈ I₁, g * x = x * g) → (∀ y ∈ I₂, g * y = y * g) → ∀ a ∈ A, g * a = a * g) ∧
      Nat.card ↥A * 2 = Nat.card ↥I₁ * Nat.card ↥I₂ := by
  have hc : ∀ (a : I₁) (b : I₂), Commute (I₁.subtype a) (I₂.subtype b) :=
    fun a b => hcomm a a.2 b b.2
  set f : I₁ × I₂ →* K := I₁.subtype.noncommCoprod I₂.subtype hc with hf
  have hfapp : ∀ x : I₁ × I₂, f x = (x.1 : K) * (x.2 : K) := fun x => rfl
  refine ⟨f.range, fun x hx => ⟨(⟨x, hx⟩, 1), by simp [hfapp]⟩,
    fun y hy => ⟨(1, ⟨y, hy⟩), by simp [hfapp]⟩, ?_, ?_⟩
  · rintro g h₁ h₂ _ ⟨x, rfl⟩
    rw [hfapp, ← mul_assoc, h₁ x.1 x.1.2, mul_assoc, h₂ x.2 x.2.2, ← mul_assoc]
  · have hker : Nat.card f.ker = 2 := by
      rw [← hcard]
      refine Nat.card_congr
        { toFun := fun x => ⟨(x.1.1 : K), x.1.1.2, by
            have h := (MonoidHom.mem_ker.mp x.2)
            rw [hfapp] at h
            have h' : (x.1.2 : K) = (x.1.1 : K)⁻¹ := eq_inv_of_mul_eq_one_right h
            have h'' : (x.1.1 : K) = ((x.1.2 : K))⁻¹ := by rw [h', inv_inv]
            rw [h'']
            exact I₂.inv_mem (x.1.2).2⟩
          invFun := fun x => ⟨(⟨x.1, x.2.1⟩, ⟨x.1⁻¹, I₂.inv_mem x.2.2⟩), by
            rw [MonoidHom.mem_ker, hfapp]
            exact mul_inv_cancel _⟩
          left_inv := fun x => by
            apply Subtype.ext
            have h := (MonoidHom.mem_ker.mp x.2)
            rw [hfapp] at h
            have h' : (x.1.2 : K) = (x.1.1 : K)⁻¹ := eq_inv_of_mul_eq_one_right h
            refine Prod.ext rfl (Subtype.ext ?_)
            exact h'.symm
          right_inv := fun x => rfl }
    have := Subgroup.card_ker_mul_card_range f
    rw [hker, Nat.card_prod] at this
    rw [mul_comm]
    exact this

theorem K94Cfg.exists_order_data {K : Type} [Group K] [Finite K] (hs : IsSimpleGroup K)
    (hnab : ∃ a b : K, a * b ≠ b * a) {z : K} {I₁ I₂ : Subgroup K} {F₁ F₂ : Type} [Field F₁]
    [Field F₂] [Finite F₁] [Finite F₂] (cfg : K94Cfg K z I₁ I₂ F₁ F₂) :
    ∃ m : ℕ, m ∣ Nat.card ↥(centralizer ({z} : Set K)) ∧ m ∣ Nat.card K ∧ 2 * m ≤ Nat.card K ∧
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 5 ≤ p ^ f ∧
      (2 * m = (p ^ f * ((p ^ f) ^ 2 - 1)) ^ 2 ∨
        2 * m = ((p ^ f) ^ 3 * (((p ^ f) ^ 3) ^ 2 - 1)) * (p ^ f * ((p ^ f) ^ 2 - 1))) := by
  obtain ⟨e₁⟩ := cfg.e₁
  obtain ⟨e₂⟩ := cfg.e₂
  obtain ⟨p, f, hp, hp2, h5, hcards⟩ := cfg.cards
  have hzz : z ∈ I₁ ⊓ I₂ := by rw [cfg.inter]; exact mem_zpowers z
  have hcard2 : Nat.card ↥(I₁ ⊓ I₂) = 2 := by rw [cfg.inter, Nat.card_zpowers, cfg.z_ord]
  obtain ⟨A, hA₁, hA₂, hAc, hAcard⟩ := exists_prod_subgroup cfg.comm hcard2
  have hAC : A ≤ centralizer ({z} : Set K) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hAc z (fun x hx => (cfg.comm x hx z hzz.2).symm) (fun y hy => by
      have := cfg.comm z hzz.1 y hy
      exact this) a ha
    exact this.symm
  have hCtop : centralizer ({z} : Set K) ≠ ⊤ := by
    intro htop
    have hzc : z ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro g
      have : g ∈ centralizer ({z} : Set K) := by rw [htop]; exact Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.1 this
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h0 | h0
    · rw [h0, Subgroup.mem_bot] at hzc
      have hz := cfg.z_ord
      rw [hzc, orderOf_one] at hz
      exact absurd hz (by norm_num)
    · obtain ⟨b, c, hbc⟩ := hnab
      apply hbc
      exact (Subgroup.mem_center_iff.1 (h0 ▸ Subgroup.mem_top c : c ∈ Subgroup.center K) b)
  have hdvd : Nat.card ↥A ∣ Nat.card K :=
    (Subgroup.card_dvd_of_le hAC).trans (Subgroup.card_subgroup_dvd_card _)
  have hidx : 2 ≤ (centralizer ({z} : Set K)).index := by
    have h1 : (centralizer ({z} : Set K)).index ≠ 1 := fun h => hCtop (Subgroup.index_eq_one.1 h)
    have h2 : (centralizer ({z} : Set K)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hle : 2 * Nat.card ↥A ≤ Nat.card K := by
    have h1 := Subgroup.index_mul_card (centralizer ({z} : Set K))
    have h2 : Nat.card ↥A ≤ Nat.card ↥(centralizer ({z} : Set K)) := Subgroup.card_le_of_le hAC
    calc 2 * Nat.card ↥A ≤ (centralizer ({z} : Set K)).index * Nat.card ↥(centralizer ({z} : Set K)) :=
          Nat.mul_le_mul hidx h2
      _ = Nat.card K := h1
  refine ⟨Nat.card ↥A, Subgroup.card_dvd_of_le hAC, hdvd, hle, p, f, hp, hp2, h5, ?_⟩
  have hI₁ : Nat.card ↥I₁ = Nat.card F₁ * (Nat.card F₁ ^ 2 - 1) := by
    rw [Nat.card_congr e₁.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  have hI₂ : Nat.card ↥I₂ = Nat.card F₂ * (Nat.card F₂ ^ 2 - 1) := by
    rw [Nat.card_congr e₂.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  rw [hI₁, hI₂] at hAcard
  rcases hcards with ⟨c1, c2⟩ | ⟨c1, c2⟩
  · left
    rw [c1, c2] at hAcard
    rw [mul_comm]
    rw [← pow_two] at hAcard
    exact hAcard
  · right
    rw [c1, c2] at hAcard
    rw [mul_comm]
    exact hAcard

theorem k94Excl_of_card {P : (K : Type) → [Group K] → Prop} {N : ℕ}
    (hP : ∀ (K : Type) [Group K] [Finite K], P K → Nat.card K = N)
    (hN : ∀ q : ℕ, 5 ≤ q → ∀ m : ℕ, m ∣ N → 2 * m ≤ N →
      2 * m ≠ (q * (q ^ 2 - 1)) ^ 2 ∧ 2 * m ≠ (q ^ 3 * ((q ^ 3) ^ 2 - 1)) * (q * (q ^ 2 - 1))) :
    K94Excl P := by
  intro K _ _ hs hnab _ _ hPK z I₁ I₂ F₁ F₂ _ _ _ _ cfg
  obtain ⟨m, -, hm, hm2, p, f, hp, hp2, h5, hmq⟩ := cfg.exists_order_data hs hnab
  rw [hP K hPK] at hm hm2
  have := hN (p ^ f) h5 m hm hm2
  rcases hmq with h | h
  · exact this.1 h
  · exact this.2 h

theorem k94Excl_or {P Q : (K : Type) → [Group K] → Prop} (hP : K94Excl P) (hQ : K94Excl Q) :
    K94Excl fun K _ => P K ∨ Q K := by
  intro K _ _ hs hnab hgen htwo hPQ z I₁ I₂ F₁ F₂ _ _ _ _ cfg
  rcases hPQ with h | h
  · exact hP K hs hnab hgen htwo h z I₁ I₂ F₁ F₂ cfg
  · exact hQ K hs hnab hgen htwo h z I₁ I₂ F₁ F₂ cfg

end CFSG.GH74.GLS.IVK.Proofs2.Ivk94
