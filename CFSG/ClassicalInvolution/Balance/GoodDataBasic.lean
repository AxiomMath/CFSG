module

public import CFSG.ClassicalInvolution.Balance.BootNoTripleBasic

public section

namespace CFSG.ClassicalInvolution.Balance.GoodData

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Balance.BootRank3

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem oddQuotMk_self_central (b : G) (y : OddQuot b) :
    oddQuotMk b ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ * y =
      y * oddQuotMk b ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ := by
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective _ y
  show oddQuotMk b _ * oddQuotMk b c = oddQuotMk b c * oddQuotMk b _
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  have := Subgroup.mem_centralizer_singleton_iff.mp c.2
  exact this.symm


omit [Fact p.Prime] in
theorem four_le_card_closure_pair [Finite G] {x y : G} (hx2 : orderOf x = 2) (hx1 : y ≠ 1)
    (hxy : y ≠ x) : 4 ≤ Nat.card (Subgroup.closure ({x, y} : Set G)) := by
  set D : Subgroup G := Subgroup.closure ({x, y} : Set G) with hD
  have hxD : Subgroup.zpowers x ≤ D := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.subset_closure (by simp)
  have hyD : y ∈ D := Subgroup.subset_closure (by simp)
  have hcardx : Nat.card (Subgroup.zpowers x) = 2 := by rw [Nat.card_zpowers, hx2]
  have hdvd : 2 ∣ Nat.card D := hcardx ▸ Subgroup.card_dvd_of_le hxD
  have hne : Nat.card D ≠ 2 := by
    intro h2
    have hEq : Subgroup.zpowers x = D := Subgroup.eq_of_le_of_card_ge hxD (by omega)
    have hy' : y ∈ Subgroup.zpowers x := hEq ▸ hyD
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy'
    have hmod := zpow_mod_orderOf x k
    rw [hx2, hk] at hmod
    push_cast at hmod
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · rw [h, zpow_zero] at hmod
      exact hx1 hmod.symm
    · rw [h, zpow_one] at hmod
      exact hxy hmod.symm
  have hpos : 0 < Nat.card D := Nat.card_pos
  omega

theorem largeCentralizerOn_of_ne_z₀ [Finite G] {A : Subgroup G} {L₀ : Subgroup G} {z₀ : G}
    (hL₀Ω : L₀ ∈ Ω) (hz₀ : IsClassicalMember p f L₀ z₀) (hz₀A : z₀ ∈ A)
    (hL₀A : L₀ ≤ Subgroup.centralizer (A : Set G)) {b : G} (hbA : b ∈ A) (hb1 : b ≠ 1)
    (hbz : b ≠ z₀) (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {L : Subgroup (OddQuot b)}
    (hL : OmegaFreeAt Ω b L ∨ RankOneAt Ω b L) : LargeCentralizerOn A b L := by
  classical
  set D : Subgroup G := Subgroup.closure ({z₀, b} : Set G) with hD
  have hDA : D ≤ A := by
    rw [hD, Subgroup.closure_le]
    intro x hx
    rcases hx with hx | hx
    · rw [hx]; exact hz₀A
    · rw [Set.mem_singleton_iff.mp hx]; exact hbA
  have h4 : 4 ≤ Nat.card D := four_le_card_closure_pair hz₀.orderOf_eq_two hb1 hbz
  have hzC : z₀ ∈ Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hAc z₀ hz₀A b hbA
  have hbC : b ∈ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hKC : L₀ ≤ Subgroup.centralizer ({b} : Set G) :=
    hL₀A.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbA))
  set Q : Subgroup ↥(Subgroup.centralizer ({b} : Set G)) :=
    (Subgroup.centralizer ((L : Subgroup (OddQuot b)) : Set (OddQuot b))).comap (oddQuotMk b)
    with hQ
  have hDQ : D ≤ Q.map (Subgroup.centralizer ({b} : Set G)).subtype := by
    rw [hD, Subgroup.closure_le]
    intro x hx
    rcases hx with hx | hx
    · rw [hx]
      refine ⟨⟨z₀, hzC⟩, ?_, rfl⟩
      show oddQuotMk b ⟨z₀, hzC⟩ ∈ Subgroup.centralizer ((L : Subgroup (OddQuot b)) : Set _)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (oddQuotMk_centralizes_of_isCentralInvolution hL₀Ω hKC hz₀.isCentralInvolution hzC hL
        y hy).symm
    · rw [Set.mem_singleton_iff.mp hx]
      refine ⟨⟨b, hbC⟩, ?_, rfl⟩
      show oddQuotMk b ⟨b, hbC⟩ ∈ Subgroup.centralizer ((L : Subgroup (OddQuot b)) : Set _)
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      exact (oddQuotMk_self_central b y).symm
  refine ⟨D, hDA, h4, fun g hg => ?_⟩
  obtain ⟨q, hq, hqg⟩ := hDQ hg
  subst hqg
  exact ⟨q.2, fun y hy => (Subgroup.mem_centralizer_iff.mp hq y hy).symm⟩

theorem free_of_freeAt_z₀ [Finite G] {A : Subgroup G} {L₀ : Subgroup G} {z₀ : G}
    (hL₀Ω : L₀ ∈ Ω) (hz₀ : IsClassicalMember p f L₀ z₀) (hz₀A : z₀ ∈ A)
    (hL₀A : L₀ ≤ Subgroup.centralizer (A : Set G)) (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hfree : ∀ L : Subgroup (OddQuot z₀), CFSG.IsComponent L →
      (OmegaFreeAt Ω z₀ L ∨ RankOneAt Ω z₀ L) → LargeCentralizerOn A z₀ L) :
    ∀ b ∈ A, b ≠ 1 → ∀ L : Subgroup (OddQuot b), CFSG.IsComponent L →
      (OmegaFreeAt Ω b L ∨ RankOneAt Ω b L) → LargeCentralizerOn A b L := by
  intro b hbA hb1 L hL hOR
  by_cases hbz : b = z₀
  · subst hbz
    exact hfree L hL hOR
  · exact largeCentralizerOn_of_ne_z₀ hL₀Ω hz₀ hz₀A hL₀A hbA hb1 hbz hAc hOR

section Lift

variable {Y : Type*} [Group Y]

theorem exists_isElemAbelian_lift_map [Finite Y] (N : Subgroup Y) [N.Normal] (hN : Odd (Nat.card N))
    (E : Subgroup (Y ⧸ N)) (hE : IsElemAbelian 2 E) :
    ∃ H : Subgroup Y, IsElemAbelian 2 H ∧ H.map (QuotientGroup.mk' N) = E ∧
      Nat.card H = Nat.card E := by
  classical
  set φ : Y →* Y ⧸ N := QuotientGroup.mk' N with hφ
  set P : Subgroup Y := E.comap φ with hP
  have hNP : N ≤ P := fun n hn => by
    rw [hP, Subgroup.mem_comap, hφ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff n).mpr hn]
    exact E.one_mem
  have hmapP : P.map φ = E :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) E
  have : (N.subgroupOf P).Normal := Subgroup.Normal.subgroupOf inferInstance P
  have hidx : (N.subgroupOf P).index = Nat.card E := by
    have h2 := Subgroup.relIndex_comap (H := (⊥ : Subgroup (Y ⧸ N))) φ P
    rw [MonoidHom.comap_bot, hφ, QuotientGroup.ker_mk', ← hφ, hmapP,
      Subgroup.relIndex_bot_left] at h2
    exact h2
  have hcardN : Nat.card (N.subgroupOf P) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNP).toEquiv
  have hEp : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by
    simpa using hE.2 x x.2)⟩
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  have hcop : Nat.Coprime (Nat.card (N.subgroupOf P)) (N.subgroupOf P).index := by
    rw [hcardN, hidx, hk]
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hN)
  obtain ⟨H', hH'⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  set H : Subgroup Y := H'.map P.subtype with hH
  have hHP : H ≤ P := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hcardH : Nat.card H = Nat.card E := by
    rw [← hidx, hH'.symm.index_eq_card, hH]
    exact Subgroup.card_map_of_injective (Subgroup.subtype_injective P)
  have hinj : ∀ x ∈ H, φ x = 1 → x = 1 := by
    intro x hx hx1
    obtain ⟨x', hx'H, rfl⟩ := hx
    have hxN : (x' : Y) ∈ N := (QuotientGroup.eq_one_iff _).mp hx1
    have : x' ∈ N.subgroupOf P ⊓ H' := ⟨hxN, hx'H⟩
    rw [hH'.disjoint.eq_bot] at this
    simpa using congrArg Subtype.val ((Subgroup.mem_bot).mp this)
  have hHE : H.map φ ≤ E := by
    rintro _ ⟨x, hx, rfl⟩
    exact hHP hx
  have hmemE : ∀ x ∈ H, φ x ∈ E := fun x hx => hHE ⟨x, hx, rfl⟩
  have hrinj : Function.Injective (φ.comp H.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hinj x x.2 hx)
  have hcardmap : Nat.card (H.map φ) = Nat.card H := by
    have h1 : (φ.comp H.subtype).range = H.map φ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← h1]
    exact (Nat.card_congr (MonoidHom.ofInjective hrinj).toEquiv).symm
  have hEq : H.map φ = E := Subgroup.eq_of_le_of_card_ge hHE (by omega)
  refine ⟨H, ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩, hEq, hcardH⟩
  · apply Subtype.ext
    have hxy := hE.1.is_comm.comm ⟨φ x, hmemE x x.2⟩ ⟨φ y, hmemE y y.2⟩
    have hxy' : φ (x : Y) * φ y = φ y * φ x := congrArg Subtype.val hxy
    have h1 : (x : Y) * y * ((y : Y) * x)⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem x.2 y.2) (H.inv_mem (H.mul_mem y.2 x.2))
    have h2 := hinj _ h1 (by rw [map_mul, map_mul, map_inv, map_mul, hxy']; group)
    exact mul_inv_eq_one.mp h2
  · have h1 : x ^ 2 ∈ H := H.pow_mem hx 2
    exact hinj _ h1 (by rw [map_pow]; exact hE.2 _ (hmemE x hx))

end Lift

end CFSG.ClassicalInvolution.Balance.GoodData
