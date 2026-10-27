module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Fpf.AFive

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Swap

open CFSG.EvenSporadicStandard.HNRecog.Fpf
open Equiv Equiv.Perm

@[expose] def PreservesFactorsAut (φ : A5 × A5 ≃* A5 × A5) : Prop :=
  (∀ x : A5, ∃ x' : A5, φ (x, 1) = (x', 1)) ∧ (∀ y : A5, ∃ y' : A5, φ (1, y) = (1, y'))

@[expose] def SwapsFactorsAut (φ : A5 × A5 ≃* A5 × A5) : Prop :=
  (∀ x : A5, ∃ y' : A5, φ (x, 1) = (1, y')) ∧ (∀ y : A5, ∃ x' : A5, φ (1, y) = (x', 1))

private theorem centerless (x : A5) (hx : ∀ g : A5, x * g = g * x) : x = 1 := by
  have key : ∀ x : A5, (∀ g : A5, x * g = g * x) → x = 1 := by decide +kernel
  exact key x hx

private theorem card_A5 : Nat.card A5 = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card]
  decide

private def c₃ : A5 := ⟨swap 0 1 * swap 1 2, mem_alternatingGroup.2 (by decide)⟩

private theorem orderOf_c₃ : orderOf c₃ = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [orderOf_eq_prime_iff]
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem c₃_ne_one : c₃ ≠ 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact (orderOf_eq_prime_iff.mp orderOf_c₃).2

private theorem three_not_dvd_two_pow (k : ℕ) : ¬ (3 ∣ 2 ^ k) := by
  intro h
  have h2 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 3) h
  omega

private theorem c₃_pow_two_pow_ne_one (k : ℕ) : c₃ ^ (2 ^ k) ≠ 1 := by
  intro h
  have hdvd : orderOf c₃ ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr h
  rw [orderOf_c₃] at hdvd
  exact three_not_dvd_two_pow k hdvd

private abbrev N1 (N : Subgroup (A5 × A5)) : Subgroup A5 := N.comap (MonoidHom.inl A5 A5)

private abbrev N2 (N : Subgroup (A5 × A5)) : Subgroup A5 := N.comap (MonoidHom.inr A5 A5)

private theorem mem_N1_iff (N : Subgroup (A5 × A5)) (x : A5) :
    x ∈ N1 N ↔ (x, (1 : A5)) ∈ N := by
  rw [N1, Subgroup.mem_comap, MonoidHom.inl_apply]

private theorem mem_N2_iff (N : Subgroup (A5 × A5)) (y : A5) :
    y ∈ N2 N ↔ ((1 : A5), y) ∈ N := by
  rw [N2, Subgroup.mem_comap, MonoidHom.inr_apply]

private theorem fst_eq_one_of_N1_eq_bot {N : Subgroup (A5 × A5)} [N.Normal]
    (h : N1 N = ⊥) {p : A5 × A5} (hp : p ∈ N) : p.1 = 1 := by
  refine centerless p.1 fun g => ?_
  have hconj : (g, (1 : A5)) * p⁻¹ * (g, 1)⁻¹ ∈ N :=
    (inferInstance : N.Normal).conj_mem p⁻¹ (inv_mem hp) (g, 1)
  have hprod : p * ((g, 1) * p⁻¹ * (g, 1)⁻¹) ∈ N := mul_mem hp hconj
  have heq : p * ((g, 1) * p⁻¹ * (g, 1)⁻¹) =
      (p.1 * g * p.1⁻¹ * g⁻¹, (1 : A5)) := by
    refine Prod.ext ?_ ?_ <;> simp [mul_assoc]
  have hmem : p.1 * g * p.1⁻¹ * g⁻¹ ∈ N1 N := by
    rw [mem_N1_iff, ← heq]
    exact hprod
  rw [h] at hmem
  have h1 : p.1 * g * p.1⁻¹ * g⁻¹ = 1 := by simpa using hmem
  have h2 : p.1 * g * p.1⁻¹ = g := by
    have := congrArg (· * g) h1
    simpa [mul_assoc] using this
  have h3 : p.1 * g = g * p.1 := by
    have := congrArg (· * p.1) h2
    simpa [mul_assoc] using this
  exact h3

private theorem snd_eq_one_of_N2_eq_bot {N : Subgroup (A5 × A5)} [N.Normal]
    (h : N2 N = ⊥) {p : A5 × A5} (hp : p ∈ N) : p.2 = 1 := by
  refine centerless p.2 fun g => ?_
  have hconj : ((1 : A5), g) * p⁻¹ * ((1 : A5), g)⁻¹ ∈ N :=
    (inferInstance : N.Normal).conj_mem p⁻¹ (inv_mem hp) ((1 : A5), g)
  have hprod : p * (((1 : A5), g) * p⁻¹ * ((1 : A5), g)⁻¹) ∈ N := mul_mem hp hconj
  have heq : p * (((1 : A5), g) * p⁻¹ * ((1 : A5), g)⁻¹) =
      ((1 : A5), p.2 * g * p.2⁻¹ * g⁻¹) := by
    refine Prod.ext ?_ ?_ <;> simp [mul_assoc]
  have hmem : p.2 * g * p.2⁻¹ * g⁻¹ ∈ N2 N := by
    rw [mem_N2_iff, ← heq]
    exact hprod
  rw [h] at hmem
  have h1 : p.2 * g * p.2⁻¹ * g⁻¹ = 1 := by simpa using hmem
  have h2 : p.2 * g * p.2⁻¹ = g := by
    have := congrArg (· * g) h1
    simpa [mul_assoc] using this
  have h3 : p.2 * g = g * p.2 := by
    have := congrArg (· * p.2) h2
    simpa [mul_assoc] using this
  exact h3

theorem eq_bot_of_normal_of_two_power (K : Subgroup (A5 × A5)) [K.Normal]
    (hK : ∀ p ∈ K, ∃ k : ℕ, p ^ (2 ^ k) = 1) : K = ⊥ := by
  haveI hK1n : (N1 K).Normal := (inferInstance : K.Normal).comap (MonoidHom.inl A5 A5)
  haveI hK2n : (N2 K).Normal := (inferInstance : K.Normal).comap (MonoidHom.inr A5 A5)
  have hK1 : N1 K ≠ ⊤ := by
    intro htop
    have hc : c₃ ∈ N1 K := by rw [htop]; trivial
    have hmem : (c₃, (1 : A5)) ∈ K := (mem_N1_iff K c₃).mp hc
    obtain ⟨k, hk⟩ := hK (c₃, (1 : A5)) hmem
    have hck : c₃ ^ (2 ^ k) = 1 := by
      have hfst := congrArg Prod.fst hk
      simpa [Prod.pow_def] using hfst
    exact c₃_pow_two_pow_ne_one k hck
  have hK2 : N2 K ≠ ⊤ := by
    intro htop
    have hc : c₃ ∈ N2 K := by rw [htop]; trivial
    have hmem : ((1 : A5), c₃) ∈ K := (mem_N2_iff K c₃).mp hc
    obtain ⟨k, hk⟩ := hK ((1 : A5), c₃) hmem
    have hck : c₃ ^ (2 ^ k) = 1 := by
      have hsnd := congrArg Prod.snd hk
      simpa [Prod.pow_def] using hsnd
    exact c₃_pow_two_pow_ne_one k hck
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N1 K) with h1 | h1
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N2 K) with h2 | h2
    · rw [Subgroup.eq_bot_iff_forall]
      intro p hp
      exact Prod.ext (fst_eq_one_of_N1_eq_bot h1 hp) (snd_eq_one_of_N2_eq_bot h2 hp)
    · exact absurd h2 hK2
  · exact absurd h1 hK1

theorem normal_card_sixty (N : Subgroup (A5 × A5)) [N.Normal] (hN : Nat.card N = 60) :
    (∀ p : A5 × A5, p ∈ N ↔ p.2 = 1) ∨ (∀ p : A5 × A5, p ∈ N ↔ p.1 = 1) := by
  haveI hN1n : (N1 N).Normal := (inferInstance : N.Normal).comap (MonoidHom.inl A5 A5)
  haveI hN2n : (N2 N).Normal := (inferInstance : N.Normal).comap (MonoidHom.inr A5 A5)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N1 N) with h1 | h1
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N2 N) with h2 | h2
    · exfalso
      have hbot : N = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro p hp
        exact Prod.ext (fst_eq_one_of_N1_eq_bot h1 hp) (snd_eq_one_of_N2_eq_bot h2 hp)
      rw [hbot, Subgroup.card_bot] at hN
      omega
    · right
      intro p
      constructor
      · intro hp
        exact fst_eq_one_of_N1_eq_bot h1 hp
      · intro hp1
        have hp_eq : p = ((1 : A5), p.2) := Prod.ext hp1 rfl
        rw [hp_eq]
        exact (mem_N2_iff N p.2).mp (by rw [h2]; trivial)
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N2 N) with h2 | h2
    · left
      intro p
      constructor
      · intro hp
        exact snd_eq_one_of_N2_eq_bot h2 hp
      · intro hp2
        have hp_eq : p = (p.1, (1 : A5)) := Prod.ext rfl hp2
        rw [hp_eq]
        exact (mem_N1_iff N p.1).mp (by rw [h1]; trivial)
    · exfalso
      have htop : N = ⊤ := by
        rw [eq_top_iff]
        intro p _
        have hp1 : (p.1, (1 : A5)) ∈ N :=
          (mem_N1_iff N p.1).mp (by rw [h1]; trivial)
        have hp2 : ((1 : A5), p.2) ∈ N :=
          (mem_N2_iff N p.2).mp (by rw [h2]; trivial)
        have hprod := mul_mem hp1 hp2
        rwa [Prod.fst_mul_snd] at hprod
      rw [htop, Subgroup.card_top, Nat.card_prod, card_A5] at hN
      omega

private abbrev F1 : Subgroup (A5 × A5) := (MonoidHom.snd A5 A5).ker

private abbrev F2 : Subgroup (A5 × A5) := (MonoidHom.fst A5 A5).ker

private theorem mem_F1_iff (p : A5 × A5) : p ∈ F1 ↔ p.2 = 1 := by
  rw [F1, MonoidHom.mem_ker]
  rfl

private theorem mem_F2_iff (p : A5 × A5) : p ∈ F2 ↔ p.1 = 1 := by
  rw [F2, MonoidHom.mem_ker]
  rfl

private theorem inl_injective : Function.Injective (MonoidHom.inl A5 A5) :=
  fun a b h => by simpa [MonoidHom.inl_apply] using congrArg Prod.fst h

private theorem card_F1 : Nat.card F1 = 60 := by
  have hmap : F1 = Subgroup.map (MonoidHom.inl A5 A5) ⊤ := by
    rw [← MonoidHom.range_eq_map]
    ext p
    rw [mem_F1_iff, MonoidHom.mem_range]
    constructor
    · intro hp
      exact ⟨p.1, by rw [MonoidHom.inl_apply]; exact Prod.ext rfl hp.symm⟩
    · rintro ⟨x, hx⟩
      simpa [MonoidHom.inl_apply] using (congrArg Prod.snd hx).symm
  rw [hmap, Subgroup.card_map_of_injective (K := (⊤ : Subgroup A5))
        (f := MonoidHom.inl A5 A5) inl_injective, Subgroup.card_top, card_A5]

private theorem card_F2 : Nat.card F2 = 60 := by
  have hmap : F2 = Subgroup.map (MonoidHom.inr A5 A5) ⊤ := by
    rw [← MonoidHom.range_eq_map]
    ext p
    rw [mem_F2_iff, MonoidHom.mem_range]
    constructor
    · intro hp
      exact ⟨p.2, by rw [MonoidHom.inr_apply]; exact Prod.ext hp.symm rfl⟩
    · rintro ⟨y, hy⟩
      simpa [MonoidHom.inr_apply] using (congrArg Prod.fst hy).symm
  rw [hmap, Subgroup.card_map_of_injective (K := (⊤ : Subgroup A5))
        (f := MonoidHom.inr A5 A5) (by
          intro a b h; simpa [MonoidHom.inr_apply] using congrArg Prod.snd h),
      Subgroup.card_top, card_A5]

private theorem phi_map_F1_ne_map_F2 (φ : A5 × A5 ≃* A5 × A5) :
    φ.mapSubgroup F1 ≠ φ.mapSubgroup F2 := by
  intro heq
  have hF : F1 = F2 := (MulEquiv.mapSubgroup φ).injective heq
  have hmem : (c₃, (1 : A5)) ∈ F2 :=
    hF ▸ ((mem_F1_iff _).mpr (by simp))
  exact c₃_ne_one ((mem_F2_iff _).mp hmem)

private theorem card_map_F1 (φ : A5 × A5 ≃* A5 × A5) :
    Nat.card (φ.mapSubgroup F1) = 60 := by
  rw [Subgroup.card_mapSubgroup (H := F1) φ, card_F1]

private theorem card_map_F2 (φ : A5 × A5 ≃* A5 × A5) :
    Nat.card (φ.mapSubgroup F2) = 60 := by
  rw [Subgroup.card_mapSubgroup (H := F2) φ, card_F2]

private theorem preserves_of_map_eq (φ : A5 × A5 ≃* A5 × A5)
    (hF1 : φ.mapSubgroup F1 = F1) (hF2 : φ.mapSubgroup F2 = F2) :
    PreservesFactorsAut φ := by
  refine ⟨?_, ?_⟩
  · intro x
    have hmem : φ (x, 1) ∈ φ.mapSubgroup F1 :=
      ⟨(x, 1), (mem_F1_iff _).mpr (by simp), rfl⟩
    have h : (φ (x, 1)).2 = 1 := (mem_F1_iff _).mp (hF1 ▸ hmem)
    exact ⟨(φ (x, 1)).1, Prod.ext rfl h⟩
  · intro y
    have hmem : φ (1, y) ∈ φ.mapSubgroup F2 :=
      ⟨(1, y), (mem_F2_iff _).mpr (by simp), rfl⟩
    have h : (φ (1, y)).1 = 1 := (mem_F2_iff _).mp (hF2 ▸ hmem)
    exact ⟨(φ (1, y)).2, Prod.ext h rfl⟩

private theorem swaps_of_map_eq (φ : A5 × A5 ≃* A5 × A5)
    (hF1 : φ.mapSubgroup F1 = F2) (hF2 : φ.mapSubgroup F2 = F1) :
    SwapsFactorsAut φ := by
  refine ⟨?_, ?_⟩
  · intro x
    have hmem : φ (x, 1) ∈ φ.mapSubgroup F1 :=
      ⟨(x, 1), (mem_F1_iff _).mpr (by simp), rfl⟩
    have h : (φ (x, 1)).1 = 1 := (mem_F2_iff _).mp (hF1 ▸ hmem)
    exact ⟨(φ (x, 1)).2, Prod.ext h rfl⟩
  · intro y
    have hmem : φ (1, y) ∈ φ.mapSubgroup F2 :=
      ⟨(1, y), (mem_F2_iff _).mpr (by simp), rfl⟩
    have h : (φ (1, y)).2 = 1 := (mem_F1_iff _).mp (hF2 ▸ hmem)
    exact ⟨(φ (1, y)).1, Prod.ext rfl h⟩

theorem exists_preserves_or_swaps (φ : A5 × A5 ≃* A5 × A5) :
    (PreservesFactorsAut φ ∧ PreservesFactorsAut φ.symm) ∨
      (SwapsFactorsAut φ ∧ SwapsFactorsAut φ.symm) := by
  haveI hnorm1 : (φ.mapSubgroup F1).Normal := by
    rw [MulEquiv.coe_mapSubgroup]
    exact MulEquiv.normal_map_iff.mpr (inferInstance : F1.Normal)
  haveI hnorm2 : (φ.mapSubgroup F2).Normal := by
    rw [MulEquiv.coe_mapSubgroup]
    exact MulEquiv.normal_map_iff.mpr (inferInstance : F2.Normal)
  have hc1 : Nat.card (φ.mapSubgroup F1) = 60 := card_map_F1 φ
  have hc2 : Nat.card (φ.mapSubgroup F2) = 60 := card_map_F2 φ
  have hne : φ.mapSubgroup F1 ≠ φ.mapSubgroup F2 := phi_map_F1_ne_map_F2 φ
  rcases normal_card_sixty (φ.mapSubgroup F1) hc1 with h1 | h1
  · rcases normal_card_sixty (φ.mapSubgroup F2) hc2 with h2 | h2
    · exact absurd (Subgroup.ext fun p => (h1 p).trans (h2 p).symm) hne
    · left
      have hF1 : φ.mapSubgroup F1 = F1 :=
        Subgroup.ext fun p => (h1 p).trans (mem_F1_iff p).symm
      have hF2 : φ.mapSubgroup F2 = F2 :=
        Subgroup.ext fun p => (h2 p).trans (mem_F2_iff p).symm
      have hF1s : φ.symm.mapSubgroup F1 = F1 :=
        (MulEquiv.mapSubgroup φ).injective (by
          rw [← MulEquiv.symm_mapSubgroup, OrderIso.apply_symm_apply, hF1])
      have hF2s : φ.symm.mapSubgroup F2 = F2 :=
        (MulEquiv.mapSubgroup φ).injective (by
          rw [← MulEquiv.symm_mapSubgroup, OrderIso.apply_symm_apply, hF2])
      exact ⟨preserves_of_map_eq φ hF1 hF2, preserves_of_map_eq φ.symm hF1s hF2s⟩
  · rcases normal_card_sixty (φ.mapSubgroup F2) hc2 with h2 | h2
    · right
      have hF1 : φ.mapSubgroup F1 = F2 :=
        Subgroup.ext fun p => (h1 p).trans (mem_F2_iff p).symm
      have hF2 : φ.mapSubgroup F2 = F1 :=
        Subgroup.ext fun p => (h2 p).trans (mem_F1_iff p).symm
      have hF1s : φ.symm.mapSubgroup F1 = F2 :=
        (MulEquiv.mapSubgroup φ).injective (by
          rw [← MulEquiv.symm_mapSubgroup, OrderIso.apply_symm_apply, hF2])
      have hF2s : φ.symm.mapSubgroup F2 = F1 :=
        (MulEquiv.mapSubgroup φ).injective (by
          rw [← MulEquiv.symm_mapSubgroup, OrderIso.apply_symm_apply, hF1])
      exact ⟨swaps_of_map_eq φ hF1 hF2, swaps_of_map_eq φ.symm hF1s hF2s⟩
    · exact absurd (Subgroup.ext fun p => (h1 p).trans (h2 p).symm) hne

theorem SwapsFactorsAut.conj {s : A5 × A5 ≃* A5 × A5} (hs : SwapsFactorsAut s)
    (ψ : A5 × A5 ≃* A5 × A5) : SwapsFactorsAut (ψ.symm.trans (s.trans ψ)) := by
  rcases exists_preserves_or_swaps ψ with ⟨hψ1, hψ2⟩ | ⟨hψ1, hψ2⟩
  · refine ⟨?_, ?_⟩
    · intro x
      obtain ⟨x₁, hx₁⟩ := hψ2.1 x
      obtain ⟨y₂, hy₂⟩ := hs.1 x₁
      obtain ⟨y₃, hy₃⟩ := hψ1.2 y₂
      exact ⟨y₃, by
        simp only [MulEquiv.trans_apply]
        rw [hx₁, hy₂, hy₃]⟩
    · intro y
      obtain ⟨y₁, hy₁⟩ := hψ2.2 y
      obtain ⟨x₂, hx₂⟩ := hs.2 y₁
      obtain ⟨x₃, hx₃⟩ := hψ1.1 x₂
      exact ⟨x₃, by
        simp only [MulEquiv.trans_apply]
        rw [hy₁, hx₂, hx₃]⟩
  · refine ⟨?_, ?_⟩
    · intro x
      obtain ⟨y₁, hy₁⟩ := hψ2.1 x
      obtain ⟨x₂, hx₂⟩ := hs.2 y₁
      obtain ⟨y₃, hy₃⟩ := hψ1.1 x₂
      exact ⟨y₃, by
        simp only [MulEquiv.trans_apply]
        rw [hy₁, hx₂, hy₃]⟩
    · intro y
      obtain ⟨x₁, hx₁⟩ := hψ2.2 y
      obtain ⟨y₂, hy₂⟩ := hs.1 x₁
      obtain ⟨x₃, hx₃⟩ := hψ1.2 y₂
      exact ⟨x₃, by
        simp only [MulEquiv.trans_apply]
        rw [hx₁, hy₂, hx₃]⟩

end CFSG.EvenSporadicStandard.HNRecog.Swap
