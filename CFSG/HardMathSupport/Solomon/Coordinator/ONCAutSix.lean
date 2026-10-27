module

public import CFSG.HardMathSupport.Solomon.Coordinator.ONAut
public import CFSG.LieType.SteinbergBRSmallAltSylow

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

theorem center_alt_six : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ := by
  have hs : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hcard : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    norm_num [Nat.factorial]
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center (alternatingGroup (Fin 6))) with h | h
  · exact h
  · exfalso
    have hcomm : ∀ a b : alternatingGroup (Fin 6), a * b = b * a := fun a b =>
      (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)
    have hprime := @IsSimpleGroup.prime_card _ ⟨fun a b => hcomm a b⟩ hs
    rw [hcard] at hprime
    exact absurd hprime (by norm_num)

theorem center_eq_ker_of_alt {K : Type} [Group K] (f : K →* alternatingGroup (Fin 6))
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center K) :
    Subgroup.center K = f.ker := by
  refine le_antisymm (fun z hz => ?_) hker
  rw [MonoidHom.mem_ker]
  have : f z ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
    rw [Subgroup.mem_center_iff]
    intro b
    obtain ⟨c, rfl⟩ := hf b
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz c]
  rwa [center_alt_six, Subgroup.mem_bot] at this

theorem card_le_nine_of_pGroup_mulAut {K : Type} [Group K] [Finite K] (hK : commutator K = ⊤)
    (f : K →* alternatingGroup (Fin 6)) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center K) (B : Subgroup (MulAut K)) (hB : IsPGroup 3 B) :
    Nat.card B ≤ 9 := by
  have hc := center_eq_ker_of_alt f hf hker
  let e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans (QuotientGroup.quotientKerEquivOfSurjective f hf)
  let g : MulAut K →* MulAut (alternatingGroup (Fin 6)) :=
    (MulAut.congr e).toMonoidHom.comp (mulAutQuotCenter K)
  have hg : Function.Injective g := (MulAut.congr e).injective.comp (mulAutQuotCenter_injective hK)
  have hcardB : Nat.card (B.map g) = Nat.card B := Subgroup.card_map_of_injective hg
  have hpB : IsPGroup 3 (B.map g) := hB.map g
  have hout : IsPGroup 2 (Outer (alternatingGroup (Fin 6))) :=
    CFSG.LieType.SteinbergBR.SmallAlt.isPGroup_outer_six
  have hle : B.map g ≤ inner (alternatingGroup (Fin 6)) := by
    intro β hβ
    obtain ⟨n, hn⟩ := hpB ⟨β, hβ⟩
    obtain ⟨m, hm⟩ := hout (QuotientGroup.mk β : Outer (alternatingGroup (Fin 6)))
    have h3 : (QuotientGroup.mk β : Outer (alternatingGroup (Fin 6))) ^ 3 ^ n = 1 := by
      rw [← QuotientGroup.mk_pow]
      have := congrArg Subtype.val hn
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
      rw [this]
      rfl
    have hd3 := orderOf_dvd_of_pow_eq_one h3
    have hd2 := orderOf_dvd_of_pow_eq_one hm
    have hcop : Nat.Coprime (3 ^ n) (2 ^ m) :=
      Nat.Coprime.pow _ _ (by norm_num)
    have h1 : orderOf (QuotientGroup.mk β : Outer (alternatingGroup (Fin 6))) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop hd3 hd2
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h1
    exact h1
  have hd1 : Nat.card (B.map g) ∣ Nat.card (inner (alternatingGroup (Fin 6))) :=
    Subgroup.card_dvd_of_le hle
  have hd2 : Nat.card (inner (alternatingGroup (Fin 6))) ∣ Nat.card (alternatingGroup (Fin 6)) :=
    Subgroup.card_range_dvd _
  have hcard : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    norm_num [Nat.factorial]
  rw [hcard] at hd2
  have hdvd : Nat.card B ∣ 360 := hcardB ▸ hd1.trans hd2
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 3)).1 hB
  rw [hk] at hdvd ⊢
  by_contra hlt
  push Not at hlt
  have hk3 : 3 ≤ k := by
    by_contra h3
    push Not at h3
    have : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h27 : 3 ^ 3 ∣ 360 := (Nat.pow_dvd_pow 3 hk3).trans hdvd
  norm_num at h27

theorem commutator_mul_central {K : Type*} [Group K] {c₁ c₂ n₁ n₂ : K}
    (h₁ : n₁ ∈ Subgroup.center K) (h₂ : n₂ ∈ Subgroup.center K) :
    ⁅c₁ * n₁, c₂ * n₂⁆ = ⁅c₁, c₂⁆ := by
  have e₁ : ⁅n₁, c₂ * n₂⁆ = 1 :=
    commutatorElement_eq_one_iff_commute.2 (Subgroup.mem_center_iff.1 h₁ _).symm
  have e₂ : ⁅c₁, n₂⁆ = 1 :=
    commutatorElement_eq_one_iff_commute.2 (Subgroup.mem_center_iff.1 h₂ _)
  rw [commutatorElement_mul_left_eq_conj_mul, e₁, mul_one, mul_inv_cancel, one_mul,
    commutatorElement_mul_right_eq_mul_conj, e₂, mul_one, mul_inv_cancel_right]

theorem isPerfect_of_ext_alt {K : Type} [Group K] (f : K →* alternatingGroup (Fin 6))
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center K)
    (hN : Nat.card f.ker = 3) {a b : K} (hab : ⁅a, b⁆ ∈ f.ker) (hne : ⁅a, b⁆ ≠ 1) :
    commutator K = ⊤ := by
  have hs : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hperf6 : commutator (alternatingGroup (Fin 6)) = ⊤ := by
    have hnab : ¬ ∀ x y : alternatingGroup (Fin 6), x * y = y * x := by
      intro hcomm
      have hcard : Nat.card (alternatingGroup (Fin 6)) = 360 := by
        rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
        norm_num [Nat.factorial]
      have hprime := @IsSimpleGroup.prime_card _ ⟨fun a b => hcomm a b⟩ hs
      rw [hcard] at hprime
      exact absurd hprime (by norm_num)
    rcases Subgroup.Normal.eq_bot_or_eq_top (commutator (alternatingGroup (Fin 6))) with h | h
    · exfalso
      apply hnab
      intro x y
      have : ⁅x, y⁆ ∈ commutator (alternatingGroup (Fin 6)) :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    · exact h
  have hsup : commutator K ⊔ f.ker = ⊤ := by
    rw [← Subgroup.comap_map_eq]
    have : (commutator K).map f = ⊤ := by
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        MonoidHom.range_eq_top_of_surjective f hf, ← commutator_def, hperf6]
    rw [this, Subgroup.comap_top]
  have : Fact (Nat.card f.ker).Prime := ⟨by rw [hN]; exact Nat.prime_three⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card ((commutator K ⊓ f.ker).subgroupOf f.ker) with
    h | h
  ·
    exfalso
    have hbot : ∀ x ∈ commutator K ⊓ f.ker, x = 1 := by
      intro x hx
      have : (⟨x, hx.2⟩ : f.ker) ∈ (commutator K ⊓ f.ker).subgroupOf f.ker := hx
      rw [h, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    have hmem : ∀ k : K, ∃ c ∈ commutator K, ∃ n ∈ f.ker, c * n = k := by
      intro k
      have hk : k ∈ commutator K ⊔ f.ker := hsup ▸ Subgroup.mem_top k
      exact Subgroup.mem_sup_of_normal_right.1 hk
    obtain ⟨c₁, hc₁, n₁, hn₁, rfl⟩ := hmem a
    obtain ⟨c₂, hc₂, n₂, hn₂, rfl⟩ := hmem b
    rw [commutator_mul_central (hker hn₁) (hker hn₂)] at hab hne
    exact hne (hbot _ ⟨Subgroup.commutator_mem_commutator (Subgroup.mem_top _)
      (Subgroup.mem_top _), hab⟩)
  ·
    have hle : f.ker ≤ commutator K := by
      intro n hn
      have : (⟨n, hn⟩ : f.ker) ∈ (commutator K ⊓ f.ker).subgroupOf f.ker := by
        rw [h]; exact Subgroup.mem_top _
      exact this.1
    rw [← sup_eq_left.2 hle, hsup]

end CFSG.HardMathSupport.Solomon.Coordinator
