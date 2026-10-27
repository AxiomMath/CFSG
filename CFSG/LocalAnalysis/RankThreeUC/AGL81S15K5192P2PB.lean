module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsPair
public import CFSG.LieType.BorelTits.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.QuasithinUnique KFactsPair

private theorem exists_odd_map_eq {G H : Type*} [Group G] [Finite G] [Group H] (f : G →* H)
    (x : G) (hx : Odd (orderOf (f x))) : ∃ y : G, Odd (orderOf y) ∧ f y = f x := by
  obtain ⟨a, m, hm, hxm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime
    (Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hx) : Nat.Coprime (2 ^ a) (orderOf (f x)))
  have h0 : Odd (orderOf (x ^ 2 ^ a)) := by
    refine Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one ?_)
    rw [← pow_mul, ← hxm, pow_orderOf_eq_one]
  exact ⟨(x ^ 2 ^ a) ^ j, Odd.of_dvd_nat h0 (orderOf_pow_dvd j), by rw [map_pow, map_pow, hj]⟩

private theorem mem_alternatingGroup_of_odd {α : Type*} [Fintype α] [DecidableEq α]
    {σ : Equiv.Perm α} (h : Odd (orderOf σ)) : σ ∈ alternatingGroup α := by
  rw [Equiv.Perm.mem_alternatingGroup]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
  · exact h1
  · exfalso
    have h2 := congrArg Equiv.Perm.sign (pow_orderOf_eq_one σ)
    rw [map_pow, h1, Odd.neg_one_pow h, map_one] at h2
    exact absurd h2 (by decide)

private theorem alt_five_index_ne_three (H : Subgroup (alternatingGroup (Fin 5))) :
    H.index ≠ 3 := by
  intro h3
  haveI := alternatingGroup.isSimpleGroup_five
  have hdvd := Subgroup.index_normalCore_dvd_factorial_index H
  rw [h3] at hdvd
  rcases H.normalCore_normal.eq_bot_or_eq_top with hb | ht
  · rw [hb, Subgroup.index_bot, nat_card_alternatingGroup, Nat.card_fin] at hdvd
    exact absurd hdvd (by decide)
  · have hH : H = ⊤ := top_le_iff.1 (ht ▸ H.normalCore_le)
    rw [hH, Subgroup.index_top] at h3
    omega

private theorem index_eq_relIndex_of_mul {G : Type*} [Group G] {H K : Subgroup G}
    (h : ∀ a : G, ∃ b ∈ H, ∃ c ∈ K, a = b * c) : K.index = K.relIndex H := by
  have horb : MulAction.orbit H ((1 : G) : G ⧸ K) = Set.univ := by
    refine Set.eq_univ_of_forall fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H a =>
      obtain ⟨b, hb, c, hc, rfl⟩ := h a
      refine ⟨⟨b, hb⟩, ?_⟩
      change ((b * 1 : G) : G ⧸ K) = ((b * c : G) : G ⧸ K)
      rw [QuotientGroup.eq]
      simpa using hc
  have hstab : MulAction.stabilizer H ((1 : G) : G ⧸ K) = K.subgroupOf H := by
    ext b
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    change ((b * 1 : G) : G ⧸ K) = ((1 : G) : G ⧸ K) ↔ (b : G) ∈ K
    rw [QuotientGroup.eq]
    simp
  rw [Subgroup.relIndex, ← hstab, MulAction.index_stabilizer, horb, Set.ncard_univ]
  rfl

theorem alt_five_eq_top_or_eq_top_of_mul (H₁ H₂ : Subgroup (alternatingGroup (Fin 5)))
    (h₁ : ¬ 2 ∣ H₁.index) (h₂ : ¬ 2 ∣ H₂.index)
    (hmul : ∀ a : alternatingGroup (Fin 5), ∃ b ∈ H₁, ∃ c ∈ H₂, a = b * c) :
    H₁ = ⊤ ∨ H₂ = ⊤ := by
  have hA : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hrel : H₂.index = H₂.relIndex H₁ := index_eq_relIndex_of_mul hmul
  have hcard : H₁.index * H₂.index ∣ 60 := by
    rw [← hA, ← H₁.index_mul_card, hrel]
    exact mul_dvd_mul_left _ (Subgroup.index_dvd_card _)
  have hval : ∀ c : ℕ, c ∣ 60 → ¬ 2 ∣ c → c ≠ 1 → c ≠ 3 → c = 5 ∨ c = 15 := by
    intro c hc h2 h1 h3
    have : c ≤ 60 := Nat.le_of_dvd (by norm_num) hc
    interval_cases c <;> omega
  by_contra hne
  push Not at hne
  rcases hval _ (Dvd.dvd.trans (Dvd.intro _ rfl) hcard) h₁
      (fun h => hne.1 (Subgroup.index_eq_one.1 h)) (alt_five_index_ne_three H₁) with ha | ha <;>
    rcases hval _ (Dvd.dvd.trans (Dvd.intro_left _ rfl) hcard) h₂
      (fun h => hne.2 (Subgroup.index_eq_one.1 h)) (alt_five_index_ne_three H₂) with hb | hb <;>
    · rw [ha, hb] at hcard
      omega

private theorem le_of_isPGroup_of_odd_index {G : Type*} [Group G] [Finite G] {N H : Subgroup G}
    [N.Normal] (hN : IsPGroup 2 N) (hH : ¬ 2 ∣ H.index) : N ≤ H := by
  obtain ⟨Q⟩ : Nonempty (Sylow 2 H) := inferInstance
  have hQ2 : IsPGroup 2 ((Q : Subgroup H).map H.subtype) := Q.isPGroup'.map H.subtype
  have hidx : ¬ 2 ∣ ((Q : Subgroup H).map H.subtype).index := by
    rw [Subgroup.index_map_subtype]
    intro hd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 hd with h | h
    · exact Q.not_dvd_index h
    · exact hH h
  exact (hN.le_sylow_of_normal (hQ2.toSylow hidx)).trans (Subgroup.map_subtype_le _)

theorem eq_top_or_eq_top_of_mul_of_alt_five {K : Type*} [Group K] [Finite K]
    (ψ : K →* alternatingGroup (Fin 5)) (hψ : Function.Surjective ψ) (hker : IsPGroup 2 ψ.ker)
    (H₁ H₂ : Subgroup K) (h₁ : ¬ 2 ∣ H₁.index) (h₂ : ¬ 2 ∣ H₂.index)
    (hmul : ∀ k : K, ∃ a ∈ H₁, ∃ b ∈ H₂, k = a * b) : H₁ = ⊤ ∨ H₂ = ⊤ := by
  have hodd : ∀ H : Subgroup K, ¬ 2 ∣ H.index → ¬ 2 ∣ (H.map ψ).index := fun H hH hd =>
    hH (hd.trans (Subgroup.index_map_dvd H hψ))
  have key : ∀ H : Subgroup K, ¬ 2 ∣ H.index → H.map ψ = ⊤ → H = ⊤ := by
    intro H hH htop
    rw [← Subgroup.comap_map_eq_self (le_of_isPGroup_of_odd_index hker hH), htop,
      Subgroup.comap_top]
  have hmul' : ∀ a, ∃ b ∈ H₁.map ψ, ∃ c ∈ H₂.map ψ, a = b * c := by
    intro a
    obtain ⟨k, rfl⟩ := hψ a
    obtain ⟨x, hx, y, hy, rfl⟩ := hmul k
    exact ⟨ψ x, ⟨x, hx, rfl⟩, ψ y, ⟨y, hy, rfl⟩, map_mul ψ x y⟩
  rcases alt_five_eq_top_or_eq_top_of_mul _ _ (hodd H₁ h₁) (hodd H₂ h₂) hmul' with h | h
  · exact Or.inl (key H₁ h₁ h)
  · exact Or.inr (key H₂ h₂ h)

theorem exists_alt_five_of_isTwoFourSFive {Y : Type} [Group Y] [Finite Y] {P : Subgroup Y}
    (hP : IsTwoFourSFive P) :
    ∃ ψ : ↥(oddHull P) →* alternatingGroup (Fin 5), Function.Surjective ψ ∧
      ∀ k : ↥(oddHull P), ψ k = 1 ↔ (k : Y) ∈ CFSG.Open.pCoreOf 2 P := by
  classical
  obtain ⟨-, -, ⟨e₀⟩⟩ := hP
  have hKP : oddHull P ≤ P := (Subgroup.closure_le P).2 fun x hx => hx.1
  let θ : ↥P →* Equiv.Perm (Fin 5) :=
    e₀.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥P))
  have hθ : Function.Surjective θ := e₀.surjective.comp (QuotientGroup.mk'_surjective _)
  let ψ₀ : ↥(oddHull P) →* Equiv.Perm (Fin 5) := θ.comp (Subgroup.inclusion hKP)
  have hmem : ∀ k, ψ₀ k ∈ alternatingGroup (Fin 5) := by
    have hle : oddHull P ≤ ((alternatingGroup (Fin 5)).comap ψ₀).map (oddHull P).subtype := by
      refine (Subgroup.closure_le _).2 fun x hx => ⟨⟨x, Subgroup.subset_closure hx⟩, ?_, rfl⟩
      refine mem_alternatingGroup_of_odd (Odd.of_dvd_nat hx.2 ?_)
      have := orderOf_map_dvd θ ⟨x, hx.1⟩
      rwa [Subgroup.orderOf_mk] at this
    intro k
    obtain ⟨k', hk', hkk'⟩ := hle k.2
    rwa [show k' = k from Subtype.ext hkk'] at hk'
  refine ⟨ψ₀.codRestrict _ hmem, fun a => ?_, fun k => ?_⟩
  · have h3 : alternatingGroup (Fin 5) ≤ ψ₀.range := by
      rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
      intro c hc
      obtain ⟨p, rfl⟩ := hθ c
      obtain ⟨q, hq, hqp⟩ := exists_odd_map_eq θ p
        (by rw [Equiv.Perm.IsThreeCycle.orderOf hc]; exact ⟨1, rfl⟩)
      have hqK : (q : Y) ∈ oddHull P :=
        Subgroup.subset_closure ⟨q.2, by rwa [Subgroup.orderOf_coe]⟩
      exact ⟨⟨q, hqK⟩, hqp⟩
    obtain ⟨k, hk⟩ := h3 a.2
    exact ⟨k, Subtype.ext hk⟩
  · have h1 : ψ₀.codRestrict _ hmem k = 1 ↔ ψ₀ k = 1 := by
      rw [← Subtype.coe_inj]
      exact Iff.rfl
    rw [h1]
    change e₀ (QuotientGroup.mk (Subgroup.inclusion hKP k)) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
    constructor
    · exact fun h => ⟨_, h, rfl⟩
    · rintro ⟨q, hq, hqk⟩
      rwa [show q = Subgroup.inclusion hKP k from Subtype.ext hqk] at hq

theorem oddHull_eq_or_eq_of_mul_of_isTwoFourSFive {Y : Type} [Group Y] [Finite Y]
    {P : Subgroup Y} (hP : IsTwoFourSFive P) {H₁ H₂ S₁ S₂ : Subgroup Y}
    (hH₁ : H₁ ≤ oddHull P) (hH₂ : H₂ ≤ oddHull P)
    (hS₁ : IsSylowTwoOf S₁ (oddHull P)) (hS₂ : IsSylowTwoOf S₂ (oddHull P))
    (hSH₁ : S₁ ≤ H₁) (hSH₂ : S₂ ≤ H₂)
    (hmul : ∀ k ∈ oddHull P, ∃ a ∈ H₁, ∃ b ∈ H₂, k = a * b) :
    H₁ = oddHull P ∨ H₂ = oddHull P := by
  obtain ⟨ψ, hψ, hker⟩ := exists_alt_five_of_isTwoFourSFive hP
  have hk2 : IsPGroup 2 ψ.ker :=
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P).comap_of_injective (oddHull P).subtype
      (oddHull P).subtype_injective).to_le fun k hk => (hker k).1 (MonoidHom.mem_ker.1 hk)
  have hodd : ∀ {H S : Subgroup Y}, H ≤ oddHull P → IsSylowTwoOf S (oddHull P) → S ≤ H →
      ¬ 2 ∣ (H.subgroupOf (oddHull P)).index := by
    intro H S hHK hS hSH hd
    refine hS.2.2 ?_
    change 2 ∣ S.relIndex (oddHull P)
    rw [← Subgroup.relIndex_mul_relIndex S H (oddHull P) hSH hHK]
    exact Dvd.dvd.mul_left hd _
  have hmul' : ∀ k : ↥(oddHull P), ∃ a ∈ H₁.subgroupOf (oddHull P),
      ∃ b ∈ H₂.subgroupOf (oddHull P), k = a * b := by
    intro k
    obtain ⟨a, ha, b, hb, hab⟩ := hmul k k.2
    exact ⟨⟨a, hH₁ ha⟩, ha, ⟨b, hH₂ hb⟩, hb, Subtype.ext hab⟩
  rcases eq_top_or_eq_top_of_mul_of_alt_five ψ hψ hk2 _ _ (hodd hH₁ hS₁ hSH₁)
      (hodd hH₂ hS₂ hSH₂) hmul' with h | h
  · exact Or.inl (le_antisymm hH₁ (Subgroup.subgroupOf_eq_top.1 h))
  · exact Or.inr (le_antisymm hH₂ (Subgroup.subgroupOf_eq_top.1 h))

end CFSG.LocalAnalysis.RankThreeUC.S15
