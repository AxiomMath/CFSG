module

public import CFSG.Quasithin.H13.GoldschmidtC137SQA6
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub.Pieces

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.U3.GC137.SQ (isKGroupCat_of_pGroup isKGroupCat_of_ker
  isKGroupCat_of_mulEquiv_alternatingGroup_six)
open CFSG.SectionRank (IsKGroupCat)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem card_quot_eq_360 {L₁ : Subgroup G}
    (e : ↥L₁ ⧸ CFSG.pCore 2 ↥L₁ ≃* alternatingGroup (Fin 6)) :
    Nat.card (↥L₁ ⧸ CFSG.pCore 2 ↥L₁) = 360 := by
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  decide

theorem le_two_of_pow_dvd_360 {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ^ k ∣ 360) :
    k ≤ 2 := by
  by_contra hk
  push Not at hk
  have h3 : p ^ 3 ∣ 360 := (Nat.pow_dvd_pow p hk).trans h
  have hcop : Nat.Coprime (p ^ 3) (2 ^ 3) :=
    Nat.Coprime.pow 3 3 ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have h45 : p ^ 3 ∣ 45 := by
    have : (360 : ℕ) = 2 ^ 3 * 45 := by norm_num
    rw [this] at h3
    exact hcop.dvd_of_dvd_mul_left h3
  have hle : p ^ 3 ≤ 45 := Nat.le_of_dvd (by norm_num) h45
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hp' : p ≤ 3 := by
    by_contra hlt
    push Not at hlt
    have : 4 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hlt 3
    omega
  have : p = 3 := le_antisymm hp' hp3
  subst this
  exact absurd h45 (by decide)

theorem isPGroup_of_isElemAbelian {p : ℕ} [Fact p.Prime] {H : Type*} [Group H] {E : Subgroup H}
    (hE : IsElemAbelian p E) : IsPGroup p E := by
  intro x
  refine ⟨1, ?_⟩
  apply Subtype.ext
  rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  exact hE.2 x x.2

theorem sQTKSubLStmt_holds : SQTKSubLStmt := by
  intro G _ _ X S L N θ Δ₀ P ω hE a ha L₁ hL₁ hN ⟨e⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 S := hE.asc.twoRadical.isPGroup
  set G₁ : Subgroup G := L₁ ⊔ S with hG₁
  set N₁ : Subgroup ↥G₁ := L₁.subgroupOf G₁ with hN₁
  have hN₁n : N₁.Normal := by
    rw [hN₁, Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    exact sup_le (Subgroup.le_normalizer) hN
  have hprod : ((G₁ : Subgroup G) : Set G) = (L₁ : Set G) * (S : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left L₁ S hN
  have hquot2 : IsPGroup 2 (↥G₁ ⧸ N₁) := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    have hg : (g : G) ∈ (L₁ : Set G) * (S : Set G) := hprod ▸ g.2
    obtain ⟨l, hl, s, hs, hls⟩ := hg
    obtain ⟨k, hk⟩ := hS2 ⟨s, hs⟩
    refine ⟨k, ?_⟩
    have hsG : s ∈ G₁ := (le_sup_right : S ≤ L₁ ⊔ S) hs
    have hlG : l ∈ G₁ := (le_sup_left : L₁ ≤ L₁ ⊔ S) hl
    have hg' : g = ⟨l, hlG⟩ * ⟨s, hsG⟩ := Subtype.ext hls.symm
    have hlN : (⟨l, hlG⟩ : ↥G₁) ∈ N₁ := by rw [hN₁, Subgroup.mem_subgroupOf]; exact hl
    rw [hg', QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 hlN, one_mul,
      ← QuotientGroup.mk_pow]
    have hs1 : (⟨s, hsG⟩ : ↥G₁) ^ 2 ^ k = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val hk
      simpa using this
    rw [hs1, QuotientGroup.mk_one]
  have hKL₁ : IsKGroupCat ↥L₁ := by
    refine isKGroupCat_of_ker (QuotientGroup.mk' (CFSG.pCore 2 ↥L₁)) ?_
      (isKGroupCat_of_mulEquiv_alternatingGroup_six e)
    rw [QuotientGroup.ker_mk']
    exact isKGroupCat_of_pGroup CFSG.pCore_isPGroup
  refine ⟨?_, ?_⟩
  ·
    intro p hp hp2
    have : Fact p.Prime := ⟨hp⟩
    unfold CFSG.Open.pRank
    refine csSup_le' fun k hk => ?_
    obtain ⟨E, -, hEab, hEc⟩ := hk
    have hEp : IsPGroup p E := isPGroup_of_isElemAbelian hEab
    have hEN : E ≤ N₁ := by
      have h1 : IsPGroup p (E.map (QuotientGroup.mk' N₁)) := hEp.map _
      have h2 : IsPGroup 2 (E.map (QuotientGroup.mk' N₁)) := hquot2.to_subgroup _
      have hdis := IsPGroup.disjoint_of_ne p 2 hp2 _ _ h1 h2
      have hbot : E.map (QuotientGroup.mk' N₁) = ⊥ := disjoint_self.1 hdis
      rw [← QuotientGroup.ker_mk' N₁, ← Subgroup.map_eq_bot_iff]
      exact hbot
    set φ : ↥N₁ ≃* ↥L₁ := Subgroup.subgroupOfEquivOfLe (le_sup_left : L₁ ≤ G₁) with hφ
    set g : ↥E →* ↥L₁ ⧸ CFSG.pCore 2 ↥L₁ :=
      (QuotientGroup.mk' _).comp (φ.toMonoidHom.comp (Subgroup.inclusion hEN)) with hg
    have hinj : Function.Injective g := by
      rw [injective_iff_map_eq_one]
      intro x hx
      set y : ↥L₁ := φ (Subgroup.inclusion hEN x) with hydef
      have hy : y ∈ CFSG.pCore 2 ↥L₁ := (QuotientGroup.eq_one_iff y).1 hx
      have hxp : x ^ p = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hEab.2 x x.2)
      have hyp : y ^ p = 1 := by
        rw [hydef, ← map_pow, ← map_pow, hxp, map_one, map_one]
      obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L₁)) ⟨y, hy⟩
      have hy2 : y ^ 2 ^ m = 1 := by
        have := congrArg Subtype.val hm
        simpa using this
      have hcop : Nat.Coprime p (2 ^ m) :=
        Nat.Coprime.pow_right m ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
      have hord : orderOf y ∣ 1 := by
        rw [← hcop.gcd_eq_one]
        exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hyp) (orderOf_dvd_of_pow_eq_one hy2)
      have hy1 : y = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 hord)
      have hinc : Function.Injective (φ.toMonoidHom.comp (Subgroup.inclusion hEN)) :=
        φ.injective.comp (Subgroup.inclusion_injective hEN)
      apply hinc
      rw [map_one]
      exact hy1
    have hdvd : Nat.card ↥E ∣ 360 := card_quot_eq_360 e ▸ Subgroup.card_dvd_of_injective g hinj
    rw [hEc] at hdvd
    exact le_two_of_pow_dvd_360 hp hp2 hdvd
  ·
    refine isKGroupCat_of_ker (QuotientGroup.mk' N₁) ?_ (isKGroupCat_of_pGroup hquot2)
    rw [QuotientGroup.ker_mk']
    exact IsKGroupCat.of_mulEquiv hKL₁ (Subgroup.subgroupOfEquivOfLe le_sup_left)

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub
