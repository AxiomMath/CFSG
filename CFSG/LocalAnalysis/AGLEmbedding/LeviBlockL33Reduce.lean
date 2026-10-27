module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockL33Defs
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsPL
import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDispatch
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockL33Orders
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockReduce
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockQuotient
import CFSG.LocalAnalysis.AGLEmbedding.A15ComponentsAux
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexFiveTypes
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem kFactCompParabNoL33U35L37He_of_families
    (hA : KFactCompParabNoL33U35L37HeOn (IsLieOf IdxA))
    (h2A : KFactCompParabNoL33U35L37HeOn (IsLieOf IdxTwistedA))
    (hB : KFactCompParabNoL33U35L37HeOn (IsLieOf IdxB))
    (hD : KFactCompParabNoL33U35L37HeOn (IsLieOf IdxD))
    (h2D : KFactCompParabNoL33U35L37HeOn (IsLieOf IdxTwistedD))
    (hG : KFactCompParabNoL33U35L37HeOn (IsLieOf IdxG2))
    (hS : KFactCompParabNoL33U35L37HeOn IsSmallTwoOrG2) : KFactCompParabNoL33U35L37He := by
  intro Y _ _ L P hCP
  rcases isClassicalTwoOrG2_family_cases hCP.type with h | h | h | h | h | h | h
  exacts [hA Y L P hCP h, h2A Y L P hCP h, hB Y L P hCP h, hD Y L P hCP h, h2D Y L P hCP h,
    hG Y L P hCP h, hS Y L P hCP h]

namespace LeviBlock

theorem card_dvd_ker_of_perm_normal {X U : Type*} [Group X] [Finite X] [Group U] [Finite U]
    [IsSimpleGroup U] (h3U : 3 ∣ Nat.card U) {n : ℕ}
    (hnU : Nat.card (alternatingGroup (Fin n)) ≠ Nat.card U) (ρ : X →* Equiv.Perm (Fin n))
    (hρ : Function.Surjective ρ) {O W : Subgroup X} [O.Normal] (hO3 : Nat.Coprime 3 (Nat.card O))
    [(W ⊔ O).Normal] (hW : ⁅W, W⁆ = W) (ψ : ↥W →* U) (hψ : Function.Surjective ψ) :
    Nat.card U ∣ Nat.card ρ.ker := by
  classical
  set A := alternatingGroup (Fin n) with hA
  have hWA : W.map ρ ≤ A := by
    have hc : ⁅W.map ρ, W.map ρ⁆ = W.map ρ := by rw [← Subgroup.map_commutator, hW]
    rw [← hc, hA, alternatingGroup_eq_sign_ker]
    exact (Subgroup.commutator_mono le_top le_top).trans
      (Abelianization.commutator_subset_ker Equiv.Perm.sign)
  by_cases hn : 5 ≤ n
  · have h5 : 5 ≤ Nat.card (Fin n) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hn
    haveI : IsSimpleGroup A := alternatingGroup.isSimpleGroup h5
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    have h3A : 3 ∣ Nat.card A := by
      have hAc := two_mul_nat_card_alternatingGroup (α := Fin n)
      rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at hAc
      have h3 : 3 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
      rw [← hAc] at h3
      exact Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h3
    set N := O.map ρ with hNdef
    have hN : N.Normal := ‹O.Normal›.map ρ hρ
    have hM : (W.map ρ ⊔ N).Normal := by
      rw [← Subgroup.map_sup]
      exact ‹(W ⊔ O).Normal›.map ρ hρ
    by_cases hMbot : W.map ρ ⊔ N = ⊥
    · have hWk : W ≤ ρ.ker := by
        refine (Subgroup.map_eq_bot_iff W).mp (le_bot_iff.mp ?_)
        exact hMbot ▸ le_sup_left
      exact (Subgroup.card_dvd_of_surjective hψ).trans (Subgroup.card_dvd_of_le hWk)
    · have hntM : Nontrivial ↥(W.map ρ ⊔ N) :=
        (Subgroup.nontrivial_iff_ne_bot _).mpr hMbot
      have hAM : A ≤ W.map ρ ⊔ N :=
        Equiv.Perm.alternatingGroup_le_of_normal (α := Fin n) h5 hntM
      have hNA : ∀ x ∈ N, x ∈ A → x = 1 := by
        have hNs : (N.subgroupOf A).Normal := Subgroup.Normal.subgroupOf hN A
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf A) with h | h
        · intro x hxN hxA
          have hx : (⟨x, hxA⟩ : A) ∈ N.subgroupOf A := Subgroup.mem_subgroupOf.mpr hxN
          rw [h, Subgroup.mem_bot] at hx
          exact congrArg Subtype.val hx
        · exfalso
          have hAN : A ≤ N := fun a ha => by
            have ha' : (⟨a, ha⟩ : A) ∈ N.subgroupOf A := h ▸ Subgroup.mem_top _
            exact Subgroup.mem_subgroupOf.mp ha'
          have hd : Nat.card A ∣ Nat.card O :=
            (Subgroup.card_dvd_of_le hAN).trans (Subgroup.card_map_dvd O ρ)
          exact absurd (Nat.Coprime.coprime_dvd_right (h3A.trans hd) hO3) (by norm_num)
      have hAW : A ≤ W.map ρ := by
        intro a ha
        obtain ⟨w, hw, m, hm, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hAM ha)
        have hmA : m ∈ A := by
          have := A.mul_mem (A.inv_mem (hWA hw)) ha
          rwa [inv_mul_cancel_left] at this
        rw [hNA m hm hmA, mul_one]
        exact hw
      have hWeq : W.map ρ = A := le_antisymm hWA hAW
      set σ : ↥W →* A := (ρ.comp W.subtype).codRestrict A
        (fun w => hWA ⟨w, w.2, rfl⟩) with hσd
      have hσ : Function.Surjective σ := by
        rintro ⟨a, ha⟩
        obtain ⟨w, hw, rfl⟩ := (hWeq ▸ ha : a ∈ W.map ρ)
        exact ⟨⟨w, hw⟩, rfl⟩
      have hker : Nat.card σ.ker ∣ Nat.card ρ.ker := by
        rw [hσd, MonoidHom.ker_codRestrict, ← MonoidHom.comap_ker]
        exact Subgroup.card_comap_dvd_of_injective _ _ W.subtype_injective
      rcases card_dvd_ker_or_card_eq σ hσ ψ hψ with h | h
      · exact h.trans hker
      · exact absurd h hnU
  · have hsolA : Group.IsSolvable A :=
      alternatingGroup.isSolvable (α := Fin n)
        (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
    have hbot : W.map ρ = ⊥ := by
      by_contra hne
      have hnt : Nontrivial ↥(W.map ρ) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
      haveI : Group.IsPerfect ↥W := Subgroup.isPerfect_iff.mpr hW
      let σ₀ : ↥W →* ↥(W.map ρ) := (ρ.comp W.subtype).codRestrict (W.map ρ)
        (fun w => ⟨w, w.2, rfl⟩)
      have hσ₀ : Function.Surjective σ₀ := by
        rintro ⟨a, ha⟩
        obtain ⟨w, hw, rfl⟩ := ha
        exact ⟨⟨w, hw⟩, rfl⟩
      have hperf : Group.IsPerfect ↥(W.map ρ) :=
        Group.IsPerfect.ofSurjective (f := σ₀) hσ₀
      let f : ↥(W.map ρ) →* A :=
        { toFun := fun x => ⟨x.1, hWA x.2⟩
          map_one' := by ext; rfl
          map_mul' := fun a b => by ext; rfl }
      have hf : Function.Injective f := fun a b h =>
        Subtype.ext (congrArg (fun y : ↥A => (y : Equiv.Perm (Fin n))) h)
      haveI : Group.IsSolvable ↥A := hsolA
      have hsol : Group.IsSolvable ↥(W.map ρ) :=
        Group.isSolvable_of_isSolvable_injective (f := f) hf
      exact (Group.IsPerfect.not_isSolvable (G := ↥(W.map ρ))) hsol
    have hWk : W ≤ ρ.ker := (Subgroup.map_eq_bot_iff W).mp hbot
    exact (Subgroup.card_dvd_of_surjective hψ).trans (Subgroup.card_dvd_of_le hWk)

theorem not_dvd_two_pow_mul_factorial_of_isL33U35L37HeOrder {a n m : ℕ} (hn : n ≤ 11)
    (hm : IsL33U35L37HeOrder m) : ¬ m ∣ 2 ^ a * n.factorial := by
  intro h
  have hf : n.factorial ∣ Nat.factorial 11 := Nat.factorial_dvd_factorial hn
  rcases hm with rfl | rfl | rfl | rfl
  · exact absurd ((dvd_of_dvd_two_pow_mul (by norm_num) (by norm_num)
      ((by norm_num : 13 ∣ 5616).trans h)).trans hf) (by norm_num)
  · have hcop : Nat.Coprime 125 (2 ^ a) := by
      have h0 : Nat.Coprime 5 2 :=
        (Nat.coprime_primes Nat.prime_five Nat.prime_two).mpr (by norm_num)
      simpa using (h0.pow_left 3).pow_right a
    exact absurd ((hcop.dvd_of_dvd_mul_left ((by norm_num : 125 ∣ 126000).trans h)).trans hf)
      (by norm_num)
  · exact absurd ((dvd_of_dvd_two_pow_mul (by norm_num) (by norm_num)
      ((by norm_num : 19 ∣ 1876896).trans h)).trans hf) (by norm_num)
  · exact absurd ((dvd_of_dvd_two_pow_mul (by norm_num) (by norm_num)
      ((by norm_num : 17 ∣ 4030387200).trans h)).trans hf) (by norm_num)

theorem false_of_perm_quotient_of_normal_section {Y : Type} [Group Y] [Finite Y]
    {P W O : Subgroup Y} {U : Type} [Group U] [Finite U] [IsSimpleGroup U] {n : ℕ}
    (hOP : O ≤ P) (hWP : W ≤ P) (hPO : P ≤ Subgroup.normalizer (O : Set Y))
    (hPWO : P ≤ Subgroup.normalizer ((W ⊔ O : Subgroup Y) : Set Y))
    (hOc : Nat.Coprime 3 (Nat.card O)) (hW : ⁅W, W⁆ = W)
    (e : (↥P ⧸ CFSG.pCore 2 ↥P) ≃* Equiv.Perm (Fin n))
    (h3U : 3 ∣ Nat.card U) (hnU : Nat.card (alternatingGroup (Fin n)) ≠ Nat.card U)
    (ψ : ↥(W.subgroupOf P) →* U) (hψ : Function.Surjective ψ) : False := by
  classical
  let ρ : ↥P →* Equiv.Perm (Fin n) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥P))
  have hρ : Function.Surjective ρ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hO3 : Nat.Coprime 3 (Nat.card (O.subgroupOf P)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOP).toEquiv]
    exact hOc
  have hW' : ⁅W.subgroupOf P, W.subgroupOf P⁆ = W.subgroupOf P := by
    haveI : Group.IsPerfect ↥W := Subgroup.isPerfect_iff.mpr hW
    exact Subgroup.isPerfect_iff.mp (Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hWP).symm.toMonoidHom) (MulEquiv.surjective _))
  haveI : (O.subgroupOf P).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hPO
  haveI : (W.subgroupOf P ⊔ O.subgroupOf P).Normal := by
    rw [← Subgroup.subgroupOf_sup hWP hOP]
    exact Subgroup.normal_subgroupOf_of_le_normalizer hPWO
  have h := card_dvd_ker_of_perm_normal (X := ↥P) h3U hnU ρ hρ (O := O.subgroupOf P)
    (W := W.subgroupOf P) hO3 hW' ψ hψ
  have hle : ρ.ker ≤ CFSG.pCore 2 ↥P := by
    intro x hx
    rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥P)]
    exact e.injective (hx.trans (e.map_one).symm)
  have hUk : Nat.card U ∣ Nat.card (CFSG.pCore 2 ↥P) :=
    h.trans (Subgroup.card_dvd_of_le hle)
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥P))
  rw [hm] at hUk
  exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) (h3U.trans hUk)) (by norm_num)

end LeviBlock

section Reduce

variable {G : Type} [Group G] [Finite G] {M S L : Subgroup G}
variable {O : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
variable {V : Subgroup G}
variable {U : Type} [Group U] [Finite U] [IsSimpleGroup U]

theorem kFactBlockNoL33_nineThreeTwo (hC : KFactCompParabNoL33U35L37He)
    (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L) (hS : ¬ IsSylowTwoOf (S ⊓ L) L)
    (h2 : NineThreeTwo M S L) (hO : O ≤ blockParabolic M S L)
    (hPO : blockParabolic M S L ≤ Subgroup.normalizer (O : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hOc : Nat.Coprime 3 (Nat.card O)) (hV : barM M V ≤ blockParabolic M S L)
    (hPVO : blockParabolic M S L ≤
      Subgroup.normalizer ((barM M V ⊔ O : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set _))
    (hVM : V ≤ M) (hVV : ⁅V, V⁆ = V) {ψ' : ↥(barM M V) →* U}
    (hψ' : Function.Surjective ψ') (hd : IsL33U35L37HeOrder (Nat.card U)) : False :=
  hC _ _ _ (LeviBlock.compParab_of_nineThreeTwo hA hL hS h2) O (barM M V) hO hPO hOc hV hPVO
    (commutator_barM_eq_self hVM hVV) U ψ' hψ' hd

theorem kFactBlockNoL33_nineThreeThree_sp {k : ℕ} {d' : TauCeti.ValidLieTypeIndex}
    (hk : 3 ≤ k) {q' : TauCeti.PrimePower} (hq' : q'.card = 2) (hdq' : d'.1 = .B k q')
    (e : (↥(blockParabolic M S L) ⧸ CFSG.pCore 2 ↥(blockParabolic M S L)) ≃* CatGroup d')
    (hO : O ≤ blockParabolic M S L)
    (hPO : blockParabolic M S L ≤ Subgroup.normalizer (O : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hOc : Nat.Coprime 3 (Nat.card O)) (hV : barM M V ≤ blockParabolic M S L)
    (hPVO : blockParabolic M S L ≤
      Subgroup.normalizer ((barM M V ⊔ O : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set _))
    (h3U : 3 ∣ Nat.card U) {ψ' : ↥(barM M V) →* U} (hψ' : Function.Surjective ψ')
    (hU : Nat.card U ∣ Nat.card (blockParabolic M S L))
    (hd : IsL33U35L37HeOrder (Nat.card U)) : False := by
  obtain ⟨a, ha⟩ := LeviBlock.card_eq_of_quotient_pCore (X := ↥(blockParabolic M S L)) e
  have hq2 : q'.p = 2 ∧ q'.exponent = 1 := by
    rw [TauCeti.PrimePower.card_def] at hq'
    exact Nat.prime_two.pow_eq_iff.mp hq'
  have h3Q : 3 ∣ Nat.card (↥(blockParabolic M S L) ⧸
      CFSG.pCore 2 ↥(blockParabolic M S L)) := by
    have h1 : 3 ∣ 2 ^ a * Nat.card (CatGroup d') := by
      rw [← ha]
      exact h3U.trans hU
    have h2 : 3 ∣ Nat.card (CatGroup d') :=
      LeviBlock.dvd_of_dvd_two_pow_mul (by norm_num) (by norm_num) h1
    rwa [Nat.card_congr e.toEquiv]
  haveI : IsSimpleGroup (↥(blockParabolic M S L) ⧸
      CFSG.pCore 2 ↥(blockParabolic M S L)) := by
    haveI : IsSimpleGroup (CatGroup d') :=
      (kFactSpTwoSimple_holds k d' hk ⟨q', hq', hdq'⟩).1
    exact e.isSimpleGroup
  have hO3 : Nat.Coprime 3 (Nat.card (O.subgroupOf (blockParabolic M S L))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hO).toEquiv]
    exact hOc
  haveI : (O.subgroupOf (blockParabolic M S L)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hPO
  haveI : ((barM M V).subgroupOf (blockParabolic M S L) ⊔
      O.subgroupOf (blockParabolic M S L)).Normal := by
    rw [← Subgroup.subgroupOf_sup hV hO]
    exact Subgroup.normal_subgroupOf_of_le_normalizer hPVO
  have hres := LeviBlock.card_dvd_ker_of_simple (X := ↥(blockParabolic M S L)) (U := U) h3Q
    (QuotientGroup.mk' (CFSG.pCore 2 ↥(blockParabolic M S L)))
    (QuotientGroup.mk'_surjective _) (O := O.subgroupOf (blockParabolic M S L))
    (W := (barM M V).subgroupOf (blockParabolic M S L)) hO3
    (ψ'.comp (Subgroup.subgroupOfEquivOfLe hV).toMonoidHom)
    (hψ'.comp (MulEquiv.surjective _))
  rcases hres with h | h
  · have hUk : Nat.card U ∣ Nat.card (CFSG.pCore 2 ↥(blockParabolic M S L)) := by
      rwa [QuotientGroup.ker_mk'] at h
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp
      (CFSG.pCore_isPGroup (p := 2) (G := ↥(blockParabolic M S L)))
    rw [hm] at hUk
    exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) (h3U.trans hUk)) (by norm_num)
  · have hcardQ : Nat.card (↥(blockParabolic M S L) ⧸
        CFSG.pCore 2 ↥(blockParabolic M S L)) = ordBC k 2 := by
      rw [Nat.card_congr e.toEquiv, card_catGroup_B_even hk hq2.1 hdq', hq2.2, pow_one]
    have : IsL33U35L37HeOrder (ordBC k 2) := by
      rw [← hcardQ, h]
      exact hd
    exact LeviBlock.ordBC_not_isL33U35L37HeOrder (n := k) (q := 2) (f := 1)
      (by norm_num) this

theorem kFactBlockNoL33_nineThreeThree_perm {n : ℕ} (hn : n = 3 ∨ n = 4 ∨ n = 6)
    (e : (↥(blockParabolic M S L) ⧸ CFSG.pCore 2 ↥(blockParabolic M S L)) ≃*
      Equiv.Perm (Fin n))
    (hU : Nat.card U ∣ Nat.card (blockParabolic M S L))
    (hd : IsL33U35L37HeOrder (Nat.card U)) : False := by
  obtain ⟨a, ha⟩ := LeviBlock.card_eq_of_quotient_pCore (X := ↥(blockParabolic M S L)) e
  have h1 : Nat.card U ∣ 2 ^ a * Nat.card (Equiv.Perm (Fin n)) := by
    rw [← ha]
    exact hU
  rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at h1
  have hn11 : n ≤ 11 := by rcases hn with rfl | rfl | rfl <;> norm_num
  exact LeviBlock.not_dvd_two_pow_mul_factorial_of_isL33U35L37HeOrder hn11 hd h1

theorem kFactBlockNoL33_nineThreeFour (h4 : NineThreeFour M S L)
    (hU : Nat.card U ∣ Nat.card (blockParabolic M S L))
    (hd : IsL33U35L37HeOrder (Nat.card U)) : False := by
  have h72 : Nat.card U ∣ 72 := hU.trans (card_blockPL_dvd_of_nineThreeFour h4)
  rcases hd with h | h | h | h <;> rw [h] at h72 <;> exact absurd h72 (by norm_num)

theorem kFactBlockNoL33_nineThreeFive (hA7 : CitedBlockAltSevenPL)
    (hK : Open.IsKGroup ↥M) (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (hX : ¬ InClassXBlock L) (hS : ¬ IsSylowTwoOf (S ⊓ L) L) (h5 : NineThreeFive M L)
    (hU : Nat.card U ∣ Nat.card (blockParabolic M S L))
    (hd : IsL33U35L37HeOrder (Nat.card U)) : False := by
  have h72 : Nat.card U ∣ 72 := hU.trans (hA7 G M S L hK hA hL hX hS h5)
  rcases hd with h | h | h | h <;> rw [h] at h72 <;> exact absurd h72 (by norm_num)

theorem kFactBlockNoL33_permQuotient {n : ℕ}
    (e : (↥(blockParabolic M S L) ⧸ CFSG.pCore 2 ↥(blockParabolic M S L)) ≃*
      Equiv.Perm (Fin n))
    (hO : O ≤ blockParabolic M S L)
    (hPO : blockParabolic M S L ≤ Subgroup.normalizer (O : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hOc : Nat.Coprime 3 (Nat.card O)) (hV : barM M V ≤ blockParabolic M S L)
    (hPVO : blockParabolic M S L ≤
      Subgroup.normalizer ((barM M V ⊔ O : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set _))
    (hVM : V ≤ M) (hVV : ⁅V, V⁆ = V) (h3U : 3 ∣ Nat.card U)
    {ψ' : ↥(barM M V) →* U} (hψ' : Function.Surjective ψ')
    (hd : IsL33U35L37HeOrder (Nat.card U)) : False :=
  LeviBlock.false_of_perm_quotient_of_normal_section (P := blockParabolic M S L)
    (W := barM M V) (O := O) hO hV hPO hPVO hOc (commutator_barM_eq_self hVM hVV) e h3U
    (fun hc => LeviBlock.card_alternatingGroup_not_isL33U35L37HeOrder n (hc ▸ hd))
    (ψ'.comp (Subgroup.subgroupOfEquivOfLe hV).toMonoidHom)
    (hψ'.comp (MulEquiv.surjective _))

theorem kFactBlockNoL33_nineThreeEight {N r : ℕ} (h2r : 2 * r ≤ N)
    (eL : ↥(barM M L) ≃* alternatingGroup (Fin N))
    (e : (↥(blockParabolic M S L) ⧸ CFSG.pCore 2 ↥(blockParabolic M S L)) ≃*
      (Equiv.Perm (Fin r) × Equiv.Perm (Fin (N - 2 * r))))
    (hpr : ∀ q : ℕ, q.Prime → q ≠ 2 → Open.pRank q (barM M L) ≤ 3)
    (hU : Nat.card U ∣ Nat.card (blockParabolic M S L))
    (hd : IsL33U35L37HeOrder (Nat.card U)) : False := by
  have hNle : N ≤ 11 := by
    have h1 : N / 3 ≤ Open.pRank 3 (barM M L) :=
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndexP.div_three_le_pRank_of_alt
        eL
    have h2 : Open.pRank 3 (barM M L) ≤ 3 := hpr 3 (by norm_num) (by norm_num)
    have h3 : N / 3 ≤ 3 := le_trans h1 h2
    have h4 : N / 3 < 4 := by omega
    have h5 : N < 4 * 3 := (Nat.div_lt_iff_lt_mul (by norm_num)).mp h4
    omega
  obtain ⟨a, ha⟩ := LeviBlock.card_eq_of_quotient_pCore
    (X := ↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L))) e
  have h1 : Nat.card U ∣ 2 ^ a * Nat.card (Equiv.Perm (Fin r) ×
      Equiv.Perm (Fin (N - 2 * r))) := by
    rw [← ha]
    exact hU
  rw [Nat.card_prod, Nat.card_perm, Nat.card_perm, Nat.card_eq_fintype_card (α := Fin r),
    Nat.card_eq_fintype_card (α := Fin (N - 2 * r)), Fintype.card_fin,
    Fintype.card_fin] at h1
  have hfac : Nat.factorial r * Nat.factorial (N - 2 * r) ∣ Nat.factorial N := by
    have h' : Nat.factorial r * Nat.factorial (N - r - r) ∣ Nat.factorial (N - r) :=
      Nat.factorial_mul_factorial_dvd_factorial (by omega)
    have h'' : Nat.factorial (N - r) ∣ Nat.factorial N :=
      Nat.factorial_dvd_factorial (by omega)
    have h3 : N - r - r = N - 2 * r := by omega
    rw [h3] at h'
    exact h'.trans h''
  exact LeviBlock.not_dvd_two_pow_mul_factorial_of_isL33U35L37HeOrder hNle hd
    (h1.trans (Nat.mul_dvd_mul_left (2 ^ a) hfac))

end Reduce

theorem kFactBlockNoL33U35L37He_of (hTPL : CitedBlockTransvectionPL)
    (hA7 : CitedBlockAltSevenPL) (hC : KFactCompParabNoL33U35L37He) :
    KFactBlockNoL33U35L37He := by
  intro G _ _ M S L hK hA hL h93 hX hS hpr O V hVM hO hV hPO hOc hPVO hVV U _ _ _ ψ hψ hd
  have h3U : 3 ∣ Nat.card U := LeviBlock.three_dvd_of_isL33U35L37HeOrder hd
  obtain ⟨ψ', hψ', -⟩ := LeviBlock.exists_surj_barM h3U hVM ψ hψ
  have hU : Nat.card U ∣ Nat.card (blockParabolic M S L) :=
    (Subgroup.card_dvd_of_surjective hψ').trans (Subgroup.card_dvd_of_le hV)
  rcases h93 with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hX
  · exact kFactBlockNoL33_nineThreeTwo hC hA hL hS h2 hO hPO hOc hV hPVO hVM hVV hψ' hd
  · rcases hTPL G M S L hK hA hL hX hS h3 with
      ⟨k, d', hk, ⟨q', hq', hdq'⟩, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · exact kFactBlockNoL33_nineThreeThree_sp hk hq' hdq' e hO hPO hOc hV hPVO h3U hψ' hU hd
    · exact kFactBlockNoL33_nineThreeThree_perm hn e hU hd
  · exact kFactBlockNoL33_nineThreeFour h4 hU hd
  · exact kFactBlockNoL33_nineThreeFive hA7 hK hA hL hX hS h5 hU hd
  · obtain ⟨-, n, -, ⟨e⟩⟩ := h6
    exact kFactBlockNoL33_permQuotient e hO hPO hOc hV hPVO hVM hVV h3U hψ' hd
  · obtain ⟨-, n, -, ⟨e⟩⟩ := h7
    exact kFactBlockNoL33_permQuotient e hO hPO hOc hV hPVO hVM hVV h3U hψ' hd
  · obtain ⟨-, N, r, -, h2r, -, -, -, ⟨eL⟩, e, -, -⟩ := h8
    exact kFactBlockNoL33_nineThreeEight h2r eL e hpr hU hd

end CFSG.AGLEmbedding
