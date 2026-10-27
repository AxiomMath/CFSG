module

public import CFSG.GH74.BNPair.Semidirect
public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ComplementConjugacy

public noncomputable section

namespace CFSG.GH74.BNPair

universe u

open scoped commutatorElement

section SchurZassenhaus

variable {p : ℕ} [Fact p.Prime]

theorem exists_conj_of_complements_top {G : Type*} [Group G] [Finite G]
    {N Z Y : Subgroup G} [N.Normal] (hN : IsPGroup p N) (hZp : ¬ p ∣ Nat.card Z)
    (hNZ : Disjoint N Z) (hNY : Disjoint N Y) (hZ : N ⊔ Z = ⊤) (hY : N ⊔ Y = ⊤) :
    ∃ n ∈ N, Y.map (MulAut.conj n).toMonoidHom = Z := by
  have hZc : N.IsComplement' Z := Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hNZ (by
    rw [← Subgroup.normal_mul, hZ]
    simp)
  have hYc : N.IsComplement' Y := Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hNY (by
    rw [← Subgroup.normal_mul, hY]
    simp)
  have hcop : Nat.Coprime (Nat.card N) N.index := by
    rw [hZc.symm.index_eq_card]
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hN
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hZp)
  obtain ⟨n, hn⟩ := CFSG.GorensteinWalter.SchurZassenhaus.exists_mem_normal_conjugator_of_coprime
    N Z Y inferInstance hZc hYc hcop
  refine ⟨((n⁻¹ : N) : G), (n⁻¹).2, ?_⟩
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [hn] at hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hy
    simpa [MulAut.conj_apply, mul_assoc] using hz
  · intro hx
    refine ⟨((n : N) : G) * x * ((n : N) : G)⁻¹, ?_, ?_⟩
    · rw [hn]
      exact Subgroup.mem_map.2 ⟨x, hx, by simp [MulAut.conj_apply]⟩
    · simp [mul_assoc]

theorem exists_conj_of_complements {G : Type*} [Group G] [Finite G]
    {E Z Y : Subgroup G} [E.Normal] (hE : IsPGroup p E) (hZp : ¬ p ∣ Nat.card Z)
    (hEZ : Disjoint E Z) (hEY : Disjoint E Y) (hYZ : E ⊔ Y = E ⊔ Z) :
    ∃ e ∈ E, Y.map (MulAut.conj e).toMonoidHom = Z := by
  set H₀ : Subgroup G := E ⊔ Z with hH₀
  have hEH : E ≤ H₀ := le_sup_left
  have hZH : Z ≤ H₀ := le_sup_right
  have hYH : Y ≤ H₀ := hYZ ▸ le_sup_right
  have : (E.subgroupOf H₀).Normal := Subgroup.Normal.subgroupOf inferInstance H₀
  have hmul : ∀ g ∈ H₀, ∃ e ∈ E, ∃ z ∈ Z, e * z = g := by
    intro g hg
    have : g ∈ (↑(E ⊔ Z) : Set G) := hg
    rw [Subgroup.normal_mul] at this
    obtain ⟨e, he, z, hz, rfl⟩ := Set.mem_mul.1 this
    exact ⟨e, he, z, hz, rfl⟩
  have hmulY : ∀ g ∈ H₀, ∃ e ∈ E, ∃ y ∈ Y, e * y = g := by
    intro g hg
    have : g ∈ (↑(E ⊔ Y) : Set G) := hYZ ▸ hg
    rw [Subgroup.normal_mul] at this
    obtain ⟨e, he, y, hy, rfl⟩ := Set.mem_mul.1 this
    exact ⟨e, he, y, hy, rfl⟩
  have hN : IsPGroup p (E.subgroupOf H₀) := hE.of_equiv (Subgroup.subgroupOfEquivOfLe hEH).symm
  have hZg : ¬ p ∣ Nat.card (Z.subgroupOf H₀) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZH).toEquiv]
    exact hZp
  have hdisj : ∀ {W : Subgroup G}, Disjoint E W → Disjoint (E.subgroupOf H₀) (W.subgroupOf H₀) := by
    intro W hW
    rw [Subgroup.disjoint_def] at hW ⊢
    intro x hx1 hx2
    have := hW hx1 hx2
    exact Subtype.ext this
  have htop : ∀ {W : Subgroup G}, W ≤ H₀ → (∀ g ∈ H₀, ∃ e ∈ E, ∃ w ∈ W, e * w = g) →
      E.subgroupOf H₀ ⊔ W.subgroupOf H₀ = ⊤ := by
    intro W hW hmulW
    rw [eq_top_iff]
    intro g _
    obtain ⟨e, he, w, hw, hew⟩ := hmulW g.1 g.2
    have h1 : (⟨e, hEH he⟩ : H₀) ∈ E.subgroupOf H₀ := he
    have h2 : (⟨w, hW hw⟩ : H₀) ∈ W.subgroupOf H₀ := hw
    have : g = ⟨e, hEH he⟩ * ⟨w, hW hw⟩ := Subtype.ext hew.symm
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2)
  obtain ⟨n, hn, hnY⟩ := exists_conj_of_complements_top hN hZg (hdisj hEZ) (hdisj hEY)
    (htop hZH hmul) (htop hYH hmulY)
  refine ⟨(n : G), hn, ?_⟩
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h1 : (⟨y, hYH hy⟩ : H₀) ∈ Y.subgroupOf H₀ := hy
    have h2 : n * ⟨y, hYH hy⟩ * n⁻¹ ∈ Z.subgroupOf H₀ := by
      rw [← hnY]
      exact Subgroup.mem_map.2 ⟨_, h1, by simp [MulAut.conj_apply]⟩
    have h3 := Subgroup.mem_subgroupOf.1 h2
    simpa [MulAut.conj_apply] using h3
  · intro hx
    have h1 : (⟨x, hZH hx⟩ : H₀) ∈ Z.subgroupOf H₀ := hx
    rw [← hnY] at h1
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 h1
    refine ⟨(y : G), hy, ?_⟩
    have := congrArg Subtype.val hyx
    simpa [MulAut.conj_apply] using this

end SchurZassenhaus

section Main

variable {p : ℕ} [Fact p.Prime] {Q : Type u} [Group Q] [Finite Q]

theorem not_dvd_card_center {G : Type*} [Group G] [Finite G] (hG : CFSG.pCore p G = ⊥) :
    ¬ p ∣ Nat.card (Subgroup.center G) := by
  intro hdvd
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hcz : (c : G) ∈ Subgroup.center G := c.2
  have hN : (Subgroup.zpowers (c : G)).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.2 hcz)
  have hp : IsPGroup p (Subgroup.zpowers (c : G)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    have : orderOf (c : G) = orderOf c := Subgroup.orderOf_coe c
    rw [this, hc]
  have hle : Subgroup.zpowers (c : G) ≤ CFSG.pCore p G := le_sSup ⟨hN, hp⟩
  rw [hG] at hle
  have h1 : (c : G) = 1 := by
    have : (c : G) ∈ (⊥ : Subgroup G) := hle (Subgroup.mem_zpowers _)
    simpa using this
  have h2 : c = 1 := Subtype.ext h1
  rw [h2, orderOf_one] at hc
  exact (Fact.out : p.Prime).one_lt.ne hc

theorem frattiniAutHom_ker_isPGroup (hQ : IsPGroup p Q) : IsPGroup p (frattiniAutHom Q).ker :=
  (CFSG.GroupTheory.frattini_automorphism_kernel hQ).2

end Main

end CFSG.GH74.BNPair
