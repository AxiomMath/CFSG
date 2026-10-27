module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrTwoLocalNested

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_bot_of_commutator_eq_of_isSolvable {K : Subgroup G} (hK : ⁅K, K⁆ = K)
    (hs : Group.IsSolvable ↥K) : K = ⊥ := by
  by_contra hne
  have : Nontrivial ↥K := (nontrivial_iff_ne_bot K).mpr hne
  have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hK
  exact Group.IsPerfect.not_isSolvable ↥K hs

omit [Finite G] in
theorem normalClosure_eq_top_of_quasisimple {Q : Type*} [Group Q] {A T : Subgroup Q}
    (hA : IsQuasisimple A) [A.Normal] (σ : Q ≃* Q) (htop : A ⊔ A.map σ.toMonoidHom = ⊤)
    (hσT : ∀ x ∈ T, σ x = x) (hT : ⁅T, T⁆ = T) (hT1 : T ≠ ⊥) :
    normalClosure (T : Set Q) = ⊤ := by
  set Y := normalClosure (T : Set Q) with hYdef
  have hYn : Y.Normal := normalClosure_normal
  have hTY : T ≤ Y := fun x hx => subset_normalClosure hx
  have hσT' : T.map σ.toMonoidHom = T := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, hσT y hy]
      exact hy
    · intro hx
      exact ⟨x, hx, hσT x hx⟩
  have hσY : Y.map σ.toMonoidHom = Y := by
    rw [hYdef, map_normalClosure _ _ σ.surjective, ← coe_map, hσT']
  have hD : ⁅A, Y⁆ ≤ A := commutator_le_left A Y
  have hDn : ((⁅A, Y⁆ : Subgroup Q).subgroupOf A).Normal := inferInstance
  rcases LocalCores.quasisimple_normal_subgroups hA hDn with htop' | hcen
  ·
    have hAY : A ≤ Y := (subgroupOf_eq_top.mp htop').trans (commutator_le_right A Y)
    have hσAY : A.map σ.toMonoidHom ≤ Y := by
      rw [← hσY]
      exact map_mono hAY
    rw [eq_top_iff, ← htop]
    exact sup_le hAY hσAY
  · exfalso
    have hD1 : ⁅A, Y⁆ = ⊥ := by
      apply LocalCores.perfect_double_commutator hA.1
      rw [commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [mem_centralizer_iff]
      intro y hy
      have hxc := hcen (show (⟨x, hD hx⟩ : A) ∈ (⁅A, Y⁆ : Subgroup Q).subgroupOf A from hx)
      exact congrArg Subtype.val (mem_center_iff.mp hxc ⟨y, hy⟩)
    have hYA : ∀ y ∈ Y, ∀ x ∈ A, x * y = y * x := by
      intro y hy x hx
      have h1 := commutator_mem_commutator hx hy
      rw [hD1, mem_bot] at h1
      exact commutatorElement_eq_one_iff_mul_comm.mp h1
    have hYσA : ∀ y ∈ Y, ∀ x ∈ A.map σ.toMonoidHom, x * y = y * x := by
      intro y hy x hx
      obtain ⟨x', hx', rfl⟩ := hx
      have hy' : σ.symm y ∈ Y := by
        rw [← hσY] at hy
        obtain ⟨y', hy', rfl⟩ := hy
        rwa [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
      have h1 := hYA _ hy' x' hx'
      have h2 := congrArg σ h1
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
      exact h2
    have hYc : ∀ y ∈ Y, ∀ q : Q, q * y = y * q := by
      intro y hy q
      have hle : A ⊔ A.map σ.toMonoidHom ≤ centralizer ({y} : Set Q) :=
        sup_le (fun x hx => mem_centralizer_singleton_iff.mpr (hYA y hy x hx))
          (fun x hx => mem_centralizer_singleton_iff.mpr (hYσA y hy x hx))
      rw [htop] at hle
      exact mem_centralizer_singleton_iff.mp (hle (mem_top q))
    have hTc : ⁅T, T⁆ = ⊥ := by
      rw [commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [mem_centralizer_iff]
      intro y _
      exact hYc x (hTY hx) y
    rw [hT] at hTc
    exact hT1 hTc

theorem isPGroup_two_of_abelian_normal {X : Type*} [Group X] [Finite X]
    (hX : pPrimeCore 2 X = ⊥) {Z : Subgroup X} (hZn : Z.Normal)
    (hZc : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x) : IsPGroup 2 Z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOZ : pPrimeCore 2 ↥Z = ⊥ := by
    have hmapn : ((pPrimeCore 2 ↥Z).map Z.subtype).Normal := by
      rw [← normalizer_eq_top_iff, eq_top_iff]
      have h1 := UnbalancedGS.normalizer_le_normalizer_map_of_characteristic Z (pPrimeCore 2 ↥Z)
      rw [normalizer_eq_top_iff.mpr hZn] at h1
      exact h1
    have hcop : Nat.Coprime 2 (Nat.card ((pPrimeCore 2 ↥Z).map Z.subtype)) := by
      rw [card_map_of_injective Z.subtype_injective]
      exact pPrimeCore_coprime_card
    have hle : (pPrimeCore 2 ↥Z).map Z.subtype ≤ pPrimeCore 2 X := le_sSup ⟨hmapn, hcop⟩
    rw [hX, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ Z.subtype_injective] at hle
    exact hle
  rw [IsPGroup.iff_orderOf]
  intro z
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos z).ne'
  refine ⟨k, ?_⟩
  set y := z ^ (2 ^ k) with hydef
  have hy : orderOf y = m := by
    rw [hydef, orderOf_pow' z (pow_ne_zero k two_ne_zero), hkm]
    rw [Nat.gcd_mul_right_left]
    exact Nat.mul_div_cancel_left m (pow_pos two_pos k)
  have hyn : (zpowers y).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hc : g * n = n * g := Subtype.ext (hZc _ g.2 _ n.2)
    rw [hc, mul_inv_cancel_right]
    exact hn
  have hcop : Nat.Coprime 2 (Nat.card (zpowers y)) := by
    rw [Nat.card_zpowers, hy]
    exact (Nat.coprime_two_left).mpr hm
  have hyO : zpowers y ≤ pPrimeCore 2 ↥Z := le_sSup ⟨hyn, hcop⟩
  rw [hOZ, le_bot_iff, zpowers_eq_bot] at hyO
  have h1 : orderOf y = 1 := by rw [hyO, orderOf_one]
  rw [hy] at h1
  rw [hkm, h1, mul_one]

theorem exists_sylow_of_card_eq {L Q : Subgroup G} (hQL : Q ≤ L)
    (hcard : Nat.card Q = 2 ^ (Nat.card L).factorization 2) :
    ∃ P₀ : Sylow 2 ↥L, (P₀ : Subgroup ↥L) = Q.subgroupOf L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Nat.card ↥(Q.subgroupOf L) = 2 ^ (Nat.card L).factorization 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hQL).toEquiv, hcard]
  exact ⟨Sylow.ofCard (Q.subgroupOf L) h1, Sylow.coe_ofCard _ _⟩

theorem core_trivial_fixed_layer_facts {V T F : Subgroup G} (hT2 : IsPGroup 2 T)
    (hTV : T ≤ normalizer (V : Set G)) (hTK : T ≤ UnbalancedLayer.coreActionKernel V)
    (hEQ : pLayer (↥V ⧸ pPrimeCore 2 ↥V) 2 = ⊤)
    (hF : F = (pLayer ↥(V ⊓ centralizer (T : Set G)) 2).map
      (V ⊓ centralizer (T : Set G)).subtype) :
    F ≤ V ⊓ centralizer (T : Set G) ∧
      Nat.card ((↥F ⧸ pPrimeCore 2 ↥F) ⧸ center (↥F ⧸ pPrimeCore 2 ↥F)) =
        Nat.card ((↥V ⧸ pPrimeCore 2 ↥V) ⧸ center (↥V ⧸ pPrimeCore 2 ↥V)) ∧
      ∀ W : Subgroup G, W ≤ V ⊓ centralizer (T : Set G) →
        CatalogueBPrimeJoin.primeResidual 2 ↥W = ⊤ →
        normalClosure (((W.subgroupOf V).map (QuotientGroup.mk' (pPrimeCore 2 ↥V)) :
          Subgroup (↥V ⧸ pPrimeCore 2 ↥V)) : Set (↥V ⧸ pPrimeCore 2 ↥V)) = ⊤ →
        W ≤ F ∧ normalClosure ((W.subgroupOf F : Subgroup ↥F) : Set ↥F) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := pPrimeCore 2 ↥V with hNdef
  let α : T →* MulAut ↥V := V.normalizerMonoidHom.comp (inclusion hTV)
  have hα : ∀ (c : T) (v : V), ((α c v : V) : G) = (c : G) * v * (c : G)⁻¹ :=
    fun c v => Subgroup.normalizerMonoidHom_apply_apply_coe V _ v
  have hαQ : ∀ (c : T) (v : V), ((α c v : V) : ↥V ⧸ N) = (v : ↥V ⧸ N) := by
    intro c v
    rw [eq_comm, QuotientGroup.eq]
    apply (mem_map_iff_mem V.subtype_injective).mp
    have h1 := (UnbalancedLayer.mem_coreActionKernel.mp (inv_mem (hTK c.2))).2 v v.2
    rw [inv_inv] at h1
    show (v : G)⁻¹ * ((α c v : V) : G) ∈ N.map V.subtype
    rw [hα]
    rwa [show (v : G)⁻¹ * ((c : G) * v * (c : G)⁻¹) = (v : G)⁻¹ * c * v * (c : G)⁻¹ by group]
  have hfix : UnbalancedGS.actionFixedSubgroup α = (centralizer (T : Set G)).subgroupOf V := by
    ext v
    rw [UnbalancedGS.mem_actionFixedSubgroup, mem_subgroupOf, mem_centralizer_iff]
    constructor
    · intro h t ht
      have h2 := congrArg Subtype.val (h ⟨t, ht⟩)
      rw [hα] at h2
      exact mul_inv_eq_iff_eq_mul.mp h2
    · intro h c
      apply Subtype.ext
      rw [hα, h (c : G) c.2, mul_inv_cancel_right]
  have hN : ¬ 2 ∣ Nat.card N := by
    have h1 : Nat.Coprime 2 (Nat.card N) := pPrimeCore_coprime_card
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp h1
  obtain ⟨-, -, -, hgen, ⟨e, -⟩⟩ :=
    UnbalancedGS.core_trivial_fixed_layer_normal_generation Nat.prime_two N hN hT2 α hαQ hEQ _ rfl
  set V' := (pLayer ↥(UnbalancedGS.actionFixedSubgroup α) 2).map
    (UnbalancedGS.actionFixedSubgroup α).subtype with hV'def
  have hV'F : V'.map V.subtype = F := by
    rw [hV'def, hF]
    rw [hfix]
    exact map_pLayer_subgroupOf_eq V _
  have hFC : F ≤ V ⊓ centralizer (T : Set G) := hF ▸ map_subtype_le _
  refine ⟨hFC, ?_, ?_⟩
  ·
    have h1 : Nat.card ((↥F ⧸ pPrimeCore 2 ↥F) ⧸ center (↥F ⧸ pPrimeCore 2 ↥F)) =
        Nat.card ((↥V' ⧸ pPrimeCore 2 ↥V') ⧸ center (↥V' ⧸ pPrimeCore 2 ↥V')) := by
      have e₁ : ↥V' ≃* ↥F :=
        (V'.equivMapOfInjective V.subtype V.subtype_injective).trans (MulEquiv.subgroupCongr hV'F)
      exact (card_centerQuotient_pPrimeCore_congr e₁).symm
    obtain ⟨f₁, -⟩ := exists_centerQuotient_congr e
    have hbot : pPrimeCore 2 (↥V ⧸ N) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
    have e₂ : (↥V ⧸ N) ⧸ pPrimeCore 2 (↥V ⧸ N) ≃* ↥V ⧸ N :=
      (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
    obtain ⟨f₂, -⟩ := exists_centerQuotient_congr e₂
    rw [h1, Nat.card_congr f₁.toEquiv, Nat.card_congr f₂.toEquiv]
  · intro W hWC hW2 hNC
    have hWV : W ≤ V := hWC.trans inf_le_left
    set W' := W.subgroupOf V with hW'def
    have hW'C : W' ≤ UnbalancedGS.actionFixedSubgroup α := by
      rw [hfix]
      intro x hx
      exact (hWC hx).2
    have hW'2 : W' = closure {x : ↥V | x ∈ W' ∧ ∃ k : ℕ, orderOf x = 2 ^ k} := by
      have h1 : CatalogueBPrimeJoin.primeResidual 2 ↥W' = ⊤ :=
        CatalogueBPrimeJoin.primeResidual_eq_top_of_equiv 2 (subgroupOfEquivOfLe hWV).symm hW2
      have h2 := map_primeResidual_eq_closure W'
      rw [h1, ← MonoidHom.range_eq_map, range_subtype] at h2
      exact h2
    obtain ⟨hW'V', hncl⟩ := hgen W' hW'C hW'2 hNC
    refine ⟨?_, ?_⟩
    · rw [← hV'F]
      intro w hw
      exact ⟨⟨w, hWV hw⟩, hW'V' hw, rfl⟩
    · have h1 := normalClosure_subgroupOf_map (K := V) (W := W) V' hncl
      rw [hV'F] at h1
      exact h1

end CFSG.ComponentClassification.UnbalancedCorr
