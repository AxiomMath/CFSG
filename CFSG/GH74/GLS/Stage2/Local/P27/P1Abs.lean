module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinConvention
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.GroupTheory.PrimeCorefreeQuasisimple

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27

open Subgroup CFSG CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBPrimeJoin

theorem odd_card_of_forall_odd' {Y : Type*} [Group Y] [Finite Y] (N : Subgroup Y)
    (h : ∀ y ∈ N, Odd (orderOf y)) : Odd (Nat.card ↥N) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have h2 : 2 ∣ Nat.card ↥N := by
    rcases Nat.even_or_odd (Nat.card ↥N) with he | ho
    · exact even_iff_two_dvd.1 he
    · exact absurd ho hne
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 2 h2
  have hg' : orderOf (g : Y) = 2 := by rw [Subgroup.orderOf_coe]; exact hg
  have := h (g : Y) g.2
  rw [hg'] at this
  exact absurd this (by decide)

theorem pPrimeCore_eq_ker' {Y' Y : Type*} [Group Y'] [Finite Y'] [Group Y] [Finite Y]
    (ρ : Y' →* Y) (hρ : Function.Surjective ρ) (hodd : ∀ y ∈ ρ.ker, Odd (orderOf y))
    (hY : pPrimeCore 2 Y = ⊥) : pPrimeCore 2 Y' = ρ.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker_le : ρ.ker ≤ pPrimeCore 2 Y' :=
    GroupTheory.le_pPrimeCore_of_normal (MonoidHom.normal_ker ρ)
      (Nat.coprime_two_left.2 (odd_card_of_forall_odd' ρ.ker hodd))
  have hO_le : pPrimeCore 2 Y' ≤ ρ.ker := by
    have hN : ((pPrimeCore 2 Y').map ρ).Normal :=
      (inferInstance : (pPrimeCore 2 Y').Normal).map ρ hρ
    have hcop : Nat.Coprime 2 (Nat.card ↥((pPrimeCore 2 Y').map ρ)) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd (pPrimeCore 2 Y') ρ)
        pPrimeCore_coprime_card
    have h1 := GroupTheory.le_pPrimeCore_of_normal hN hcop
    rw [hY] at h1
    intro x hx
    have := h1 (Subgroup.mem_map_of_mem ρ hx)
    rw [Subgroup.mem_bot] at this
    exact this
  exact le_antisymm hO_le hker_le


@[expose] noncomputable def quotEquivOfHom' {Y' Y : Type*} [Group Y'] [Finite Y'] [Group Y] [Finite Y]
    (ρ : Y' →* Y) (hρ : Function.Surjective ρ) (hodd : ∀ y ∈ ρ.ker, Odd (orderOf y))
    (hY : pPrimeCore 2 Y = ⊥) : (Y' ⧸ pPrimeCore 2 Y') ≃* Y :=
  (QuotientGroup.quotientMulEquivOfEq (pPrimeCore_eq_ker' ρ hρ hodd hY)).trans
    (QuotientGroup.quotientKerEquivOfSurjective ρ hρ)

theorem unique_pComponent_of_simple_image {X W : Type} [Group X] [Finite X] [Group W] [Finite W]
    (ρ : X →* W) (hodd : ∀ x ∈ ρ.ker, Odd (orderOf x))
    (A : Subgroup W) (hAs : IsSimpleGroup ↥A) (hAn : ∃ a b : ↥A, a * b ≠ b * a)
    (hA2 : 2 ∣ Nat.card ↥A) (hAle : A ≤ ρ.range) (hsub : (A.comap ρ).IsSubnormal)
    (hperf : ∀ B : Subgroup X, ⁅B, B⁆ = B → B.map ρ ≤ A) :
    ∃ P : Subgroup X, (∀ B : Subgroup X, IsPComponent 2 B ↔ B = P) ∧ P.map ρ = A ∧
      Nonempty ((↥P ⧸ pPrimeCore 2 ↥P) ≃* ↥A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite ↥A := Finite.of_injective A.subtype A.subtype_injective
  set X₁ : Subgroup X := A.comap ρ with hX₁
  let ρ₁ : ↥X₁ →* ↥A := (ρ.comp X₁.subtype).codRestrict A (fun x => x.2)
  have hρ₁ : Function.Surjective ρ₁ := by
    intro a
    obtain ⟨x, hx⟩ := hAle a.2
    exact ⟨⟨x, by simp [hX₁, hx]⟩, Subtype.ext hx⟩
  have hAcore : pPrimeCore 2 ↥A = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pPrimeCore 2 ↥A) with h | h
    · exact h
    · exfalso
      have hc : Nat.Coprime 2 (Nat.card ↥(pPrimeCore 2 ↥A)) := pPrimeCore_coprime_card
      rw [h, Subgroup.card_top] at hc
      exact absurd (Nat.Coprime.eq_one_of_dvd hc hA2) (by norm_num)
  have hAres : primeResidual 2 ↥A = ⊤ := by
    have : (primeResidual 2 ↥A).Characteristic := primeResidual_characteristic 2 ↥A
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (primeResidual 2 ↥A) with h | h
    · exfalso
      obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥A) 2 hA2
      have hP : IsPGroup 2 (Subgroup.zpowers a) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha]; norm_num)
      have := pSubgroup_le_residual 2 _ hP (Subgroup.mem_zpowers a)
      rw [h, Subgroup.mem_bot] at this
      rw [this, orderOf_one] at ha
      exact absurd ha (by norm_num)
    · exact h
  set R : Subgroup ↥X₁ := primeResidual 2 ↥X₁ with hR
  set P : Subgroup X := R.map X₁.subtype with hP
  have hPle : P ≤ X₁ := Subgroup.map_subtype_le _
  have hPmap : P.map ρ = A := by
    have h1 : P.map ρ = (R.map ρ₁).map A.subtype := by
      rw [hP, Subgroup.map_map, Subgroup.map_map]
      rfl
    rw [h1, hR, primeResidual_map_surjective 2 ρ₁ hρ₁, hAres, Subgroup.map_top, Subgroup.range_subtype]
  have : R.Characteristic := primeResidual_characteristic 2 ↥X₁
  have hPnormal : (P.subgroupOf X₁).Normal := by
    have h1 : P.subgroupOf X₁ = R := Subgroup.comap_map_eq_self_of_injective X₁.subtype_injective R
    rw [h1]
    infer_instance
  have hPsub : P.IsSubnormal := Subgroup.IsSubnormal.step P X₁ hPle hsub hPnormal
  have hPres : primeResidual 2 ↥P = ⊤ := by
    let e : ↥R ≃* ↥P := Subgroup.equivMapOfInjective R X₁.subtype X₁.subtype_injective
    have h1 : primeResidual 2 ↥R = ⊤ := by
      have := primeResidual_idempotent 2 ↥X₁
      rw [← hR] at this
      apply Subgroup.map_injective R.subtype_injective
      rw [this, Subgroup.map_top, Subgroup.range_subtype]
    rw [← primeResidual_map_equiv 2 e, h1]
    exact Subgroup.map_top_of_surjective _ e.surjective
  have hmem2 : ∀ x : X, x ∈ X₁ → (∃ k : ℕ, orderOf x = 2 ^ k) → x ∈ P := by
    intro x hx hk
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    rw [hR, primeResidual_eq_closure]
    obtain ⟨k, hk⟩ := hk
    exact Subgroup.subset_closure ⟨k, by rw [Subgroup.orderOf_mk]; exact hk⟩
  let ρP : ↥P →* ↥A := (ρ.comp P.subtype).codRestrict A (fun x => hPle x.2)
  have hρP : Function.Surjective ρP := by
    intro a
    have : (a : W) ∈ P.map ρ := by rw [hPmap]; exact a.2
    obtain ⟨p, hp, hpa⟩ := this
    exact ⟨⟨p, hp⟩, Subtype.ext hpa⟩
  have hkerP : ∀ y ∈ ρP.ker, Odd (orderOf y) := by
    intro y hy
    have h0 : ρP y = 1 := hy
    have h1 : ρ (y : X) = 1 := congrArg Subtype.val h0
    have := hodd (y : X) (MonoidHom.mem_ker.2 h1)
    rwa [Subgroup.orderOf_coe] at this
  have e₂ : (↥P ⧸ pPrimeCore 2 ↥P) ≃* ↥A := quotEquivOfHom' ρP hρP hkerP hAcore
  have hPqs : IsQuasisimple (↥P ⧸ pPrimeCore 2 ↥P) :=
    LocalCores.isQuasisimple_of_mulEquiv e₂.symm (LocalCores.isQuasisimple_of_isSimpleGroup hAn).1
  have hPcomp : IsPComponent 2 P :=
    (pComponent_iff_subnormal_generated_quasisimple 2 P).2 ⟨hPsub, hPres, hPqs⟩
  have hkerle : ρ.ker ≤ pPrimeCore 2 X :=
    GroupTheory.le_pPrimeCore_of_normal (MonoidHom.normal_ker ρ)
      (Nat.coprime_two_left.2 (odd_card_of_forall_odd' ρ.ker hodd))
  refine ⟨P, fun B => ⟨fun hB => ?_, fun h => h ▸ hPcomp⟩, hPmap, ⟨e₂⟩⟩
  obtain ⟨hBsub, hBres, hBqs⟩ := (pComponent_iff_subnormal_generated_quasisimple 2 B).1 hB
  have hBperf : ⁅B, B⁆ = B :=
    (Subgroup.isPerfect_iff).mp (CatalogueBHeldSmallCore.pComponent_perfect 2 B hB)
  have hBA : B.map ρ ≤ A := hperf B hBperf
  have hBX₁ : B ≤ X₁ := fun b hb => hBA ⟨b, hb, rfl⟩
  have hBP : B ≤ P := by
    intro b hb
    have h1 : (⟨b, hb⟩ : ↥B) ∈ primeResidual 2 ↥B := by rw [hBres]; exact Subgroup.mem_top _
    rw [primeResidual_eq_closure] at h1
    have h2 : Subgroup.closure {x : ↥B | ∃ k : ℕ, orderOf x = 2 ^ k} ≤ P.comap B.subtype := by
      rw [Subgroup.closure_le]
      rintro x ⟨k, hk⟩
      exact hmem2 (x : X) (hBX₁ x.2) ⟨k, by rw [Subgroup.orderOf_coe]; exact hk⟩
    exact h2 h1
  have hBρ : B.map ρ = A := by
    have hBsubX₁ : (B.subgroupOf X₁).IsSubnormal := Subgroup.IsSubnormal.subgroupOf hBsub
    have hmap : (B.subgroupOf X₁).map ρ₁ = ⊥ ∨ (B.subgroupOf X₁).map ρ₁ = ⊤ :=
      Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hAs (hBsubX₁.map hρ₁)
    have hcomm : ((B.subgroupOf X₁).map ρ₁).map A.subtype = B.map ρ := by
      rw [Subgroup.map_map]
      have h1 : A.subtype.comp ρ₁ = ρ.comp X₁.subtype := by ext x; rfl
      rw [h1, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hBX₁]
    rcases hmap with h | h
    · exfalso
      rw [h, Subgroup.map_bot] at hcomm
      have hker : B ≤ ρ.ker := fun b hb => by
        have : ρ b ∈ B.map ρ := ⟨b, hb, rfl⟩
        rw [← hcomm, Subgroup.mem_bot] at this
        exact this
      have hnt : Nontrivial ↥B := by
        by_contra hnt
        rw [not_nontrivial_iff_subsingleton] at hnt
        obtain ⟨-, -, a, b, hab⟩ := hBqs
        have h1 : Subsingleton (↥B ⧸ pPrimeCore 2 ↥B) :=
          Function.Surjective.subsingleton (QuotientGroup.mk'_surjective _)
        have h2 : Subsingleton ((↥B ⧸ pPrimeCore 2 ↥B) ⧸ center (↥B ⧸ pPrimeCore 2 ↥B)) :=
          Function.Surjective.subsingleton (QuotientGroup.mk'_surjective _)
        exact hab (Subsingleton.elim _ _)
      obtain ⟨b₀, hb₀⟩ := exists_ne (1 : ↥B)
      have hb₀' : b₀ ∈ primeResidual 2 ↥B := by rw [hBres]; exact Subgroup.mem_top _
      rw [primeResidual_eq_closure] at hb₀'
      by_contra hcon
      have h2 : Subgroup.closure {x : ↥B | ∃ k : ℕ, orderOf x = 2 ^ k} ≤ ⊥ := by
        rw [Subgroup.closure_le]
        rintro x ⟨k, hk⟩
        by_contra hx1
        have hx1' : x ≠ 1 := fun h => hx1 (by rw [h]; exact Subgroup.one_mem _)
        have hk1 : 1 ≤ k := by
          rcases Nat.eq_zero_or_pos k with h0 | h0
          · subst h0
            exact absurd (orderOf_eq_one_iff.1 (by simpa using hk)) hx1'
          · exact h0
        have hodd' := hodd (x : X) (hker x.2)
        rw [Subgroup.orderOf_coe, hk] at hodd'
        exact absurd hodd' (by
          rw [Nat.not_odd_iff_even]
          exact (Nat.even_pow.2 ⟨by norm_num, by omega⟩))
      exact hb₀ (Subgroup.mem_bot.1 (h2 hb₀'))
    · rw [h, Subgroup.map_top, Subgroup.range_subtype] at hcomm
      exact hcomm.symm
  by_contra hne
  obtain ⟨K, hK, hPs, hPmapK, hmin⟩ := hPcomp
  have hBmk : B.map (QuotientGroup.mk' (pPrimeCore 2 X)) = K := by
    rw [← hPmapK]
    apply le_antisymm (Subgroup.map_mono hBP)
    rintro _ ⟨p, hp, rfl⟩
    have hpA : ρ p ∈ B.map ρ := by rw [hBρ]; exact hPle hp
    obtain ⟨b, hb, hbp⟩ := hpA
    refine ⟨b, hb, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    apply hkerle
    rw [MonoidHom.mem_ker, map_mul, map_inv, hbp, inv_mul_cancel]
  exact hmin B (lt_of_le_of_ne hBP hne) hBsub hBmk

end CFSG.GH74.GLS.Stage2.Local.P27
