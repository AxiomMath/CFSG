module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviSmallLat
public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviTransfer
public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviCover
public import CFSG.LocalAnalysis.AGLEmbedding.BlockOutNine
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIIASix
public import CFSG.Alternating.Multipliers.Main
import CFSG.RankThree.PartOne.N143.Inspect613Even

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.AGLEmbedding.ParabHub CFSG.RankThree.PerfectCover

section Elem

variable {G : Type*} [Group G]

theorem isElemAbelian_of_card_dvd_three {U : Subgroup G} (h : Nat.card U ∣ 3) :
    IsElemAbelian 3 U := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨?_, fun x hx => ?_⟩
  · rcases (Nat.dvd_prime Nat.prime_three).1 h with h1 | h1
    · have : Subsingleton U := (Nat.card_eq_one_iff_unique.1 h1).1
      exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
    · have := isCyclic_of_prime_card h1
      exact ⟨⟨fun a b => (IsCyclic.commGroup (α := U)).mul_comm a b⟩⟩
  · have := (Subgroup.orderOf_dvd_natCard U hx).trans h
    exact orderOf_dvd_iff_pow_eq_one.1 this

theorem card_dvd_three_of_not_nine_dvd [Finite G] {J U : Subgroup G} (h9 : ¬ 9 ∣ Nat.card J)
    (hUJ : U ≤ J) (hU : IsPGroup 3 U) : Nat.card U ∣ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hU.exists_card_eq
  rw [hk]
  rcases k with _ | _ | k
  · norm_num
  · norm_num
  · exact absurd ((pow_dvd_pow 3 (show 2 ≤ k + 2 by omega)).trans
      (hk ▸ Subgroup.card_dvd_of_le hUJ)) (by norm_num [h9])

theorem isElemAbelian_of_not_nine_dvd [Finite G] {J : Subgroup G} (h9 : ¬ 9 ∣ Nat.card J) :
    ∀ U : Subgroup G, U ≤ J → IsPGroup 3 U → IsElemAbelian 3 U := fun _ hUJ hU =>
  isElemAbelian_of_card_dvd_three (card_dvd_three_of_not_nine_dvd h9 hUJ hU)

theorem isElemAbelian_three_of_map_injective {H : Type*} [Group H] {f : G →* H}
    (hf : Function.Injective f) {U : Subgroup G} (h : IsElemAbelian 3 (U.map f)) :
    IsElemAbelian 3 U := by
  refine ⟨⟨⟨fun a b => Subtype.ext (hf ?_)⟩⟩, fun x hx => hf ?_⟩
  · have := h.1.is_comm.comm ⟨f a, a, a.2, rfl⟩ ⟨f b, b, b.2, rfl⟩
    simpa using congrArg Subtype.val this
  · rw [map_pow, map_one]
    exact h.2 _ ⟨x, hx, rfl⟩

theorem perm_pow_three_eq_one_of_lt_nine {m : ℕ} (hm : m < 9) {g : Equiv.Perm (Fin m)} {k : ℕ}
    (hg : g ^ 3 ^ k = 1) : g ^ 3 = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one, ← Equiv.Perm.lcm_cycleType, Multiset.lcm_dvd]
  intro n hn
  have h1 : n ∣ 3 ^ k := (Equiv.Perm.dvd_of_mem_cycleType hn).trans (orderOf_dvd_of_pow_eq_one hg)
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h1
  have h8 : 3 ^ j ≤ m := (Equiv.Perm.le_card_support_of_mem_cycleType hn).trans
    ((Finset.card_le_univ _).trans (by simp))
  rcases j with _ | _ | j
  · norm_num
  · norm_num
  · have : 9 ≤ 3 ^ (j + 2) := by
      rw [pow_add]
      exact le_mul_of_one_le_left (by norm_num) (Nat.one_le_pow _ _ (by norm_num))
    omega

theorem isElemAbelian_alt_eight (U : Subgroup (alternatingGroup (Fin 8))) (hU : IsPGroup 3 U) :
    IsElemAbelian 3 U := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hU.exists_card_eq
  have hA : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hk2 : k ≤ 2 := by
    by_contra hk2
    have := (pow_dvd_pow 3 (show 3 ≤ k by omega)).trans (hk ▸ Subgroup.card_subgroup_dvd_card U)
    rw [hA] at this
    norm_num at this
  refine ⟨?_, fun x hx => ?_⟩
  · rcases (show k ≤ 1 ∨ k = 2 by omega) with hk1 | rfl
    · refine (isElemAbelian_of_card_dvd_three ?_).1
      rw [hk]
      exact pow_dvd_pow 3 hk1 |>.trans (by norm_num)
    · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hk
  · obtain ⟨e, he⟩ := hU ⟨x, hx⟩
    have he' : (x : Equiv.Perm (Fin 8)) ^ 3 ^ e = 1 := by
      simpa using congrArg (fun z : U => ((z : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8))) he
    exact Subtype.ext (by simpa using perm_pow_three_eq_one_of_lt_nine (by norm_num) he')

end Elem

section Small

variable {Y₁ X : Type} [Group Y₁] [Finite Y₁] [Group X]

theorem card_ker_dvd_of_alt (hY₁ : Group.IsPerfect Y₁)
    {ρ₁ : Y₁ →* X} (hρ₁ : Function.Surjective ρ₁) (hk : ρ₁.ker ≤ Subgroup.center Y₁) {m : ℕ}
    (hm : 5 ≤ m) (e : X ≃* alternatingGroup (Fin m)) :
    Nat.card ρ₁.ker ∣ if m = 6 ∨ m = 7 then 6 else 2 := by
  have hker : (e.toMonoidHom.comp ρ₁).ker = ρ₁.ker := by
    ext x
    simp [MonoidHom.mem_ker]
  have h := CFSG.GH74.Generic.card_ker_dvd_hopfMultiplier hY₁ (e.toMonoidHom.comp ρ₁)
    (e.surjective.comp hρ₁) (hker ▸ hk)
  rwa [hker, (CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput m hm).2] at h

theorem eq_bot_of_isPGroup_three_of_dvd_two {G : Type*} [Group G] {K : Subgroup G}
    [Finite K] (h3 : IsPGroup 3 K) (h2 : Nat.card K ∣ 2) : K = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := h3.exists_card_eq
  apply Subgroup.eq_bot_of_card_eq
  rw [hk] at h2 ⊢
  rcases k with _ | k
  · rfl
  · exact absurd ((dvd_pow_self 3 (Nat.succ_ne_zero k)).trans h2) (by norm_num)

open CFSG.Blueprint.Multiplier CFSG.Assembly.LowTwoRank in
theorem threeDichotomy_of_small
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hY₁ : Group.IsPerfect Y₁) (ρ₁ : Y₁ →* X) (hρ₁ : Function.Surjective ρ₁)
    (hk : ρ₁.ker ≤ Subgroup.center Y₁) (h3 : IsPGroup 3 ρ₁.ker) (hX : Subgroup.center X = ⊥)
    (hsmall : (∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 8) ∧ Nonempty (X ≃* alternatingGroup (Fin n))) ∨
      ∃ d : TauCeti.ValidLieTypeIndex, ((∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q) ∨
        (∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .twistedA 2 q)) ∧
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group))
    (T₁ : Sylow 2 Y₁) (J₁ : Subgroup Y₁)
    (hNJ : Subgroup.normalizer ((T₁ : Subgroup Y₁) : Set Y₁) ≤ J₁)
    (hJ : J₁ ≠ Subgroup.normalizer ((T₁ : Subgroup Y₁) : Set Y₁))
    (hperf : ∀ U : Subgroup Y₁, U ≤ J₁ → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U)) :
    ThreeDichotomy J₁ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite X := Finite.of_surjective ρ₁ hρ₁
  obtain ⟨hTb, hNb, -, hperfb⟩ := map_overgroup_of_central hρ₁ hk T₁ hNJ hJ hperf
  have hXp : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤ := by
    have : Group.IsPerfect X := Group.IsPerfect.ofSurjective hρ₁
    exact this.commutator_eq_top
  have hnine : NineFreeOver X → ¬ 9 ∣ Nat.card (J₁.map ρ₁) := fun hNF h9 => by
    have htop := hNF _ _ hTb (Subgroup.le_normalizer.trans hNb) h9
    have hc := hperfb ⊤ htop.ge hXp
    rw [← htop] at hc
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hc ((dvd_mul_right 3 3).trans h9)
  have hbot : ρ₁.ker = ⊥ → (∀ U : Subgroup X, U ≤ J₁.map ρ₁ → IsPGroup 3 U →
      IsElemAbelian 3 U) → ThreeDichotomy J₁ := fun hb hE =>
    ThreeDichotomy.of_map hρ₁ (hb ▸ bot_le) (by rw [hb, Subgroup.card_bot]; norm_num) (Or.inl hE)
  rcases hsmall with ⟨m, hm, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
  · rcases hm with rfl | rfl | rfl
    ·
      have hb := eq_bot_of_isPGroup_three_of_dvd_two h3
        (by simpa using card_ker_dvd_of_alt hY₁ hρ₁ hk (by norm_num) e)
      refine hbot hb (isElemAbelian_of_not_nine_dvd fun h9 => ?_)
      have h60 : Nat.card X = 60 := by
        rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
          Fintype.card_fin]
        decide
      have := h9.trans (Subgroup.card_subgroup_dvd_card _)
      rw [h60] at this
      norm_num at this
    ·
      have hk6 : Nat.card ρ₁.ker ∣ 6 := by
        simpa using card_ker_dvd_of_alt hY₁ hρ₁ hk (by norm_num) e
      have h9 : ¬ 9 ∣ Nat.card (J₁.map ρ₁) :=
        hnine (NineFreeOver.of_mulEquiv e.symm nineFreeOver_alt_six)
      have hZ : Subgroup.center Y₁ = ρ₁.ker := by
        refine le_antisymm (fun z hz => ?_) hk
        have : ρ₁ z ∈ Subgroup.center X := by
          rw [Subgroup.mem_center_iff]
          intro w
          obtain ⟨w, rfl⟩ := hρ₁ w
          rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz w]
        rw [hX, Subgroup.mem_bot] at this
        exact this
      have hexp : ∀ l : Y₁, (∃ k : ℕ, l ^ 3 ^ k = 1) → l ^ 3 = 1 := by
        obtain ⟨j, hj⟩ := h3.exists_card_eq
        have hj1 : j ≤ 1 := by
          by_contra hj1
          have := (pow_dvd_pow 3 (show 2 ≤ j by omega)).trans (hj ▸ hk6)
          norm_num at this
        rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
        · intro l ⟨k, hlk⟩
          have hb : ρ₁.ker = ⊥ := Subgroup.eq_bot_of_card_eq _ (by simpa using hj)
          have hperm :
              ((e (ρ₁ l) : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) ^ 3 ^ k = 1 := by
            rw [← Subgroup.coe_pow, ← map_pow, ← map_pow, hlk, map_one, map_one, Subgroup.coe_one]
          have h3' := perm_fin_six_pow_three_eq_one hperm
          have : ρ₁ (l ^ 3) = 1 := by
            apply e.injective
            rw [map_pow, map_pow, map_one]
            exact Subtype.ext (by simpa using h3')
          have hmem : l ^ 3 ∈ ρ₁.ker := this
          rw [hb, Subgroup.mem_bot] at hmem
          exact hmem
        · exact kFactThreeASixExpThree_holds Y₁ (by rw [hZ, hj, pow_one])
            ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans
              ((QuotientGroup.quotientKerEquivOfSurjective ρ₁ hρ₁).trans e)⟩
      left
      intro U hUJ hU
      refine ⟨?_, fun x hx => hexp x ?_⟩
      · let f : U →* U.map ρ₁ := (ρ₁.comp U.subtype).codRestrict _ fun x => ⟨x, x.2, rfl⟩
        have hcard := card_dvd_three_of_not_nine_dvd h9 (Subgroup.map_mono hUJ) (hU.map ρ₁)
        have : IsCyclic (U.map ρ₁) := by
          rcases (Nat.dvd_prime Nat.prime_three).1 hcard with h1 | h1
          · have : Subsingleton (U.map ρ₁) := (Nat.card_eq_one_iff_unique.1 h1).1
            exact isCyclic_of_subsingleton
          · exact isCyclic_of_prime_card h1
        refine f.isMulCommutative_of_isCyclic_of_ker_le_center fun u hu => ?_
        have hu1 : ρ₁ (u : Y₁) = 1 := congrArg Subtype.val hu
        rw [Subgroup.mem_center_iff]
        intro w
        exact Subtype.ext (Subgroup.mem_center_iff.1 (hk hu1) w)
      · obtain ⟨k, hk'⟩ := hU ⟨x, hx⟩
        exact ⟨k, by simpa using congrArg Subtype.val hk'⟩
    ·
      have hb := eq_bot_of_isPGroup_three_of_dvd_two h3
        (by simpa using card_ker_dvd_of_alt hY₁ hρ₁ hk (by norm_num) e)
      refine hbot hb fun U _ hU => isElemAbelian_three_of_map_injective (f := e.toMonoidHom)
        e.injective (isElemAbelian_alt_eight _ (hU.map _))
  · rcases hd with ⟨q, hq, hd'⟩ | ⟨q, hq, hd'⟩
    ·
      obtain ⟨dd, hv⟩ := d
      simp only at hd'
      subst hd'
      obtain ⟨hp, hf⟩ := primePower_eq_of_card_eq Nat.prime_seven hq
      have hc := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
      rw [hp, hf] at hc
      have hM : Nat.Coprime 3 (Nat.card (hopfMultiplier X)) := by
        rw [card_hopfMultiplier_of_statedClassicalModel hGA hc]
        decide
      exact hbot (ker_eq_bot_of_coprime_hopfMultiplier hY₁ ρ₁ hρ₁ hk h3 hM)
        (isElemAbelian_of_not_nine_dvd (hnine (nineFreeOver_catalog_seven hq rfl e)))
    ·
      obtain ⟨dd, hv⟩ := d
      simp only at hd'
      subst hd'
      obtain ⟨hp, hf⟩ := primePower_eq_of_card_eq Nat.prime_three hq
      have hc := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
      rw [hp, hf] at hc
      have hM : Nat.Coprime 3 (Nat.card (hopfMultiplier X)) := by
        rw [card_hopfMultiplier_of_statedClassicalModel hGA hc]
        decide
      exact hbot (ker_eq_bot_of_coprime_hopfMultiplier hY₁ ρ₁ hρ₁ hk h3 hM)
        (isElemAbelian_of_not_nine_dvd (hnine (nineFreeOver_catalog_psu_three_three hq rfl e)))

end Small

end CFSG.AGLEmbedding
