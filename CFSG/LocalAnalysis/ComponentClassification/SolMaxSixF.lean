module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSixE
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxTwoH
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxTwoIB0K

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv
open scoped commutatorElement

@[expose] def SignalizerNineTwoPointCentralizerLocalInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 9)) (E : Subgroup X) (D : Finset (Fin 9)),
    Sig36 X t J 9 e E D → Sol78.signalizerCompletion E E ≠ ⊥ →
    ∀ M : Subgroup X, M ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
      IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))) →
      J ≤ M → normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X) →
      J ⊔ FooteLit.oddCoreIn M = M →
    ∀ (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9))
      (ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)), IsPermAction θ ρ →
      (∀ (x : X) (hx : x ∈ M), x * x = 1 → (ρ ⟨x, le_normalizer hx⟩).support.card = 4 →
        ∀ K : Subgroup X, K ≤ centralizer ({x} : Set X) →
          IsPComponent 2 (K.subgroupOf (centralizer ({x} : Set X))) →
          IsEmpty (↥K ⧸ pPrimeCore 2 ↥K ≃* alternatingGroup (Fin 9))) →
    ∀ Q S : Subgroup X,
      Q ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M → IsPGroup 2 Q →
      Nat.card Q = 2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M)).factorization 2 → t ∈ Q → Q ≤ S →
      S ≤ normalizer (Sol78.signalizerCompletion E E : Set X) → IsPGroup 2 S →
      Nat.card S =
        2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X))).factorization 2 →
      (∀ y ∈ S, y * t = t * y) →
      (∀ y ∈ Q, orderOf y = 2 →
        centralizer ({y} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) →
      (∀ x y : X, y ∈ S → y ∉ Q → y ∈ Q.map (MulAut.conj x).toMonoidHom →
        Q ⊓ Q.map (MulAut.conj x).toMonoidHom = ⊥) →
      KernelBalanceAt t J e (normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M) →
    ∀ f ∈ normalizer (Sol78.signalizerCompletion E E : Set X), f * f = 1 → f * t = t * f →
      ∀ hfN : f ∈ normalizer (M : Set X), (ρ ⟨f, hfN⟩).support.card = 2 →
        centralizer ({f} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X)

theorem signalizerNineTwoPointCentralizerLocalInput_holds
    (hbal : Sol78.BalanceTwoComponentInput) (h33 : Sol78.BalanceLemmaInput)
    (h35 : SignalizerLemma35) (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion) :
    SignalizerNineTwoPointCentralizerLocalInput := by
  intro X _ _ _ t J e E D S₀ hW M hMH hMpc hJM hHN hsup θ ρ hρ hNoA9 Q Sc hQK hQ2 hQcard htQ hQS
    hSH hS2 hScard htZ hCQ hd3 hKloc f hfH hf2 hft hfN hf2pt
  classical
  have hδ : ∀ F : Subgroup X, F ≤ J →
      Nonempty (F ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) →
      ∀ DF : Finset (Fin 9), DF.card = 4 → (∀ x : J, (x : X) ∈ F → ∀ ω ∉ DF,
        ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin 9)) : Perm (Fin 9)) ω = ω) →
      ∀ a ∈ F, a ≠ 1 →
        (pPrimeCore 2 ↥(centralizer ({a * t} : Set X))).map
            (centralizer ({a * t} : Set X)).subtype ⊓ centralizer (F : Set X) ≤
          (pPrimeCore 2 ↥(centralizer (F : Set X))).map (centralizer (F : Set X)).subtype := by
    intro F hFJ hFk DF hDF hFs a ha ha1
    classical
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
    obtain ⟨-, hFsq⟩ := card_sq_of_klein hFk
    have hFel : IsElementaryAbelian 2 F := isElementaryAbelian_of_klein hFk
    have hFne : F ≠ ⊥ := fun h => ha1 (by rw [h] at ha; exact mem_bot.mp ha)
    have hcF : ∀ y ∈ F, ∀ z ∈ F, y * z = z * y := fun y hy z hz =>
      congrArg Subtype.val (hFel.toIsMulCommutative.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
    have hJt : ∀ y ∈ J, y * t = t * y := fun y hy =>
      mem_centralizer_singleton_iff.mp (S₀.pair.1.2.1 hy)
    have ht2 : orderOf t = 2 := S₀.pair.1.1
    have htt : t * t = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
    have haa : a * a = 1 := by rw [← sq]; exact hFsq a ha
    have hat : a * t = t * a := hJt a (hFJ ha)
    have hatat : a * t * (a * t) = 1 := mul_mul_self_eq_one_of_commute haa htt hat
    have hat1 : a * t ≠ 1 := fun h =>
      S₀.t_not_mem (by rw [eq_inv_of_mul_eq_one_right h]; exact J.inv_mem (hFJ ha))
    have hS : zpowers (a * t) ≠ ⊥ := fun h => hat1 (zpowers_eq_bot.mp h)
    have hSel : IsElementaryAbelian 2 (zpowers (a * t)) :=
      IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [sq]; exact hatat)
    have hST : zpowers (a * t) ≤ centralizer (F : Set X) := by
      rw [zpowers_le, mem_centralizer_iff]
      intro y hy
      calc y * (a * t) = y * a * t := (mul_assoc _ _ _).symm
        _ = a * y * t := by rw [hcF y hy a ha]
        _ = a * (y * t) := mul_assoc _ _ _
        _ = a * (t * y) := by rw [hJt y (hFJ hy)]
        _ = a * t * y := (mul_assoc _ _ _).symm
    obtain ⟨-, hbc, hd⟩ := hbal X (zpowers (a * t)) F hS hFne hSel hFel hST
    rw [centralizer_zpowers_eq' (a * t)] at hbc hd
    by_contra hX₀
    obtain ⟨L, ⟨hLC, hLpc⟩, hLX⟩ := hd hX₀
    obtain ⟨-, hc⟩ := hbc L ⟨hLC, hLpc⟩
    obtain ⟨hSN, -, hOL⟩ := hc hLX
    have hatN : a * t ∈ normalizer (L : Set X) := by
      obtain ⟨⟨g, hg⟩, hg1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hSN
      obtain ⟨hgS, hgN⟩ := mem_inf.mp hg
      rcases eq_one_or_eq_of_mem_zpowers hatat hgS with h | h
      · exact absurd (Subtype.ext h) hg1
      · exact h ▸ hgN
    have haN : a ∈ normalizer (L : Set X) :=
      Subgroup.centralizer_le_normalizer _ (le_centralizer_iff.mp hLC ha)
    have htN : t ∈ normalizer (L : Set X) := by
      have h1 : t = a * (a * t) := by rw [← mul_assoc, haa, one_mul]
      rw [h1]
      exact mul_mem haN hatN
    set OF := (pPrimeCore 2 ↥(centralizer (F : Set X))).map (centralizer (F : Set X)).subtype
      with hOFdef
    have hLa : ∀ l ∈ L, l * a = a * l := fun l hl => (mem_centralizer_iff.mp (hLC hl) a ha).symm
    have hc1 : ⁅L, zpowers (a * t) ⊓ normalizer (L : Set X)⁆ ≤ ⁅L, zpowers t⁆ := by
      rw [commutator_le]
      intro l hl g hg
      rcases eq_one_or_eq_of_mem_zpowers hatat (mem_inf.mp hg).1 with h | h
      · rw [h, commutatorElement_one_right]
        exact one_mem _
      · rw [h, commutatorElement_mul_eq_of_commute_left (hLa l hl) hat]
        exact commutator_mem_commutator hl (mem_zpowers t)
    have hc2 : ⁅L, zpowers t⁆ ≤ L := by
      rw [commutator_le]
      intro l hl g hg
      have h1 : g * l⁻¹ * g⁻¹ ∈ L :=
        (mem_normalizer_iff.mp (zpowers_le.mpr htN hg) _).mp (inv_mem hl)
      have h2 : ⁅l, g⁆ = l * (g * l⁻¹ * g⁻¹) := by rw [commutatorElement_def]; group
      rw [h2]
      exact mul_mem hl h1
    have hLt : OF ⊔ L = OF ⊔ ⁅L, zpowers t⁆ :=
      le_antisymm (hOL.le.trans (sup_le_sup_left hc1 _)) (sup_le_sup_left hc2 _)
    have hFH : normalizer (F : Set X) ≤ H := by
      have h1 := normalizer_le_normalizer_signalizerCompletion_self F
      rwa [S₀.completion_eq_of_four h33 h35 hFJ hFk hDF hFs] at h1
    have hCFH : centralizer (F : Set X) ≤ H := (Subgroup.centralizer_le_normalizer _).trans hFH
    have hLH : L ≤ H := hLC.trans hCFH
    have hCt := S₀.centralizer_le_normalizer_completion h33 h35 hT13 hML hSch
    have htH : t ∈ H := hCt (mem_centralizer_singleton_iff.mpr rfl)
    have htK : t ∈ UnbalancedLayer.coreActionKernel M :=
      S₀.t_mem_coreActionKernel_of_sup h33 h35 hT13 hML hSch hHN hsup
    set Kst := H ⊓ UnbalancedLayer.coreActionKernel M with hKstdef
    have hKN : H ≤ normalizer (Kst : Set X) := fun g hg =>
      inf_mem_normalizer' (le_normalizer hg) (mem_normalizer_coreActionKernel (hHN hg))
    have hc3 : ⁅L, zpowers t⁆ ≤ Kst := by
      rw [commutator_le]
      intro l hl g hg
      have hgK : g ∈ Kst := zpowers_le.mpr (show t ∈ Kst from ⟨htH, htK⟩) hg
      have h1 : l * g * l⁻¹ ∈ Kst := (mem_normalizer_iff.mp (hKN (hLH hl)) g).mp hgK
      rw [commutatorElement_def]
      exact mul_mem h1 (inv_mem hgK)
    have hLOK : L ≤ OF ⊔ Kst := le_sup_right.trans (hLt.le.trans (sup_le_sup_left hc3 _))
    have hOFodd : Odd (Nat.card OF) := by
      rw [hOFdef, Subgroup.card_map_of_injective (centralizer (F : Set X)).subtype_injective]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    have hOFK : OF ≤ normalizer (Kst : Set X) := (map_subtype_le _).trans (hCFH.trans hKN)
    have hLperf : ⁅L, L⁆ = L := UnbalancedCorr.commutator_eq_of_isPComponent hLC hLpc
    have hLK : L ≤ Kst := le_of_perfect_of_le_odd_sup hLperf hOFodd hOFK hLOK
    exact hLX (hKloc F hFJ hFk DF hDF hFs a ha ha1 L hLC hLpc hLK htN hLt)
  have hB0 : ∀ F : Subgroup X, F ≤ J → F ≤ centralizer ({f} : Set X) →
      Nonempty (F ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) →
      ∀ DF : Finset (Fin 9), DF.card = 4 → (∀ x : J, (x : X) ∈ F → ∀ ω ∉ DF,
        ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin 9)) : Perm (Fin 9)) ω = ω) →
      ∀ x ∈ F, x ≠ 1 → ∀ x' ∈ F, x' ≠ 1 → x ≠ x' →
        (pPrimeCore 2 ↥(centralizer ({f} : Set X))).map (centralizer ({f} : Set X)).subtype ⊓
            centralizer ({x} : Set X) ⊓ centralizer ({x' * t} : Set X) ≤
          normalizer (Sol78.signalizerCompletion E E : Set X) := by
    intro F hFJ _ hFk DF hDF hFs x hx hx1 x' hx' hx'1 hxx'
    have hN := S₀.normalizer_closure_le_of_diag hbal h33 h35 hFJ hFk hDF hFs
      (hδ F hFJ hFk DF hDF hFs) hx hx1 hx' hx'1 hxx'
    intro y hy
    have hyx : y ∈ centralizer ({x} : Set X) := hy.1.2
    have hyx' : y ∈ centralizer ({x' * t} : Set X) := hy.2
    have h1 : closure ({x, x' * t} : Set X) ≤ centralizer ((zpowers y : Subgroup X) : Set X) := by
      rw [centralizer_zpowers_eq', closure_le]
      rintro g (rfl | rfl)
      · exact mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hyx).symm
      · exact mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hyx').symm
    exact hN (Subgroup.centralizer_le_normalizer _ (le_centralizer_iff.mp h1 (mem_zpowers y)))
  have hOf : (pPrimeCore 2 ↥(centralizer ({f} : Set X))).map (centralizer ({f} : Set X)).subtype ≤
      normalizer (Sol78.signalizerCompletion E E : Set X) := by
    classical
    set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
    have hfJ : f ∈ normalizer (J : Set X) :=
      S₀.centralizer_le_normalizer hT13 hML hSch (mem_centralizer_singleton_iff.mpr hft)
    obtain ⟨ρJ, hρJ⟩ := exists_isPermAction (M := J) (by norm_num) (by norm_num) e
    have hf2J : (ρJ ⟨f, hfJ⟩).support.card = 2 := by
      rw [← card_support_rho_eq_rhoJ (by norm_num) hJM hsup hρ hρJ hfJ hfN]
      exact hf2pt
    obtain ⟨L₀, F, -, -, -, hL₀C, -, hFL₀, hFJ, hF4, hFsq, ⟨DF, hDF, hFs⟩, -, -⟩ :=
      S₀.exists_fixed_layer_seven_of_two hρJ hfJ hf2 hf2J
    have hFk := klein_of_card_sq hF4 hFsq
    have hFC : F ≤ centralizer ({f} : Set X) := hFL₀.trans (hL₀C.trans inf_le_right)
    have : IsKleinFour ↥F := isKleinFour_of_card hF4 fun g => Subtype.ext (hFsq g g.2)
    have hFH : normalizer (F : Set X) ≤ H := by
      have h1 := normalizer_le_normalizer_signalizerCompletion_self F
      rwa [S₀.completion_eq_of_four h33 h35 hFJ hFk hDF hFs] at h1
    have hCt := S₀.centralizer_le_normalizer_completion h33 h35 hT13 hML hSch
    have ht2 : orderOf t = 2 := S₀.pair.1.1
    have ht1 : t ≠ 1 := by
      intro h
      rw [h, orderOf_one] at ht2
      exact absurd ht2 (by norm_num)
    have hJt : ∀ y ∈ J, y * t = t * y := fun y hy =>
      mem_centralizer_singleton_iff.mp (S₀.pair.1.2.1 hy)
    set Of := (pPrimeCore 2 ↥(centralizer ({f} : Set X))).map (centralizer ({f} : Set X)).subtype
      with hOfdef
    have hCO : centralizer ({f} : Set X) ≤ normalizer (Of : Set X) :=
      Sol78.le_normalizer_map_subtype (pPrimeCore 2 (centralizer ({f} : Set X)))
    have hFO : F ≤ normalizer (Of : Set X) := hFC.trans hCO
    have htO : t ∈ normalizer (Of : Set X) := hCO (mem_centralizer_singleton_iff.mpr hft.symm)
    have hodd : Odd (Nat.card Of) := by
      rw [hOfdef, Subgroup.card_map_of_injective (centralizer ({f} : Set X)).subtype_injective]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    have hC : ∀ x ∈ F, x ≠ 1 → ∀ x' ∈ F, x' ≠ 1 → x ≠ x' →
        Of ⊓ centralizer ({x} : Set X) ≤ H := by
      intro x hx hx1 x' hx' hx'1 hxx'
      set Y := Of ⊓ centralizer ({x} : Set X) with hYdef
      have hYodd : Odd (Nat.card Y) := Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le inf_le_left)
      have hx'2 : orderOf x' = 2 := orderOf_eq_prime (by rw [sq]; exact hFsq x' hx') hx'1
      have hx't : x' ≠ t := fun h => S₀.t_not_mem (h ▸ hFJ hx')
      have : IsKleinFour ↥(closure ({x', t} : Set X)) :=
        UnbalancedGS.ReciprocalFusion.isKleinFour_closure_pair hx'2 ht2 (hJt x' (hFJ hx')) hx't
      have hx'x : x' ∈ centralizer ({x} : Set X) :=
        mem_centralizer_singleton_iff.mpr (ABGLocalTools.kleinFour_comm (T := F) hx' hx)
      have htx : t ∈ centralizer ({x} : Set X) :=
        mem_centralizer_singleton_iff.mpr (hJt x (hFJ hx)).symm
      have hVY : closure ({x', t} : Set X) ≤ normalizer (Y : Set X) := by
        rw [closure_le]
        rintro g (rfl | rfl)
        · exact ABGLocalTools.mem_normalizer_inf (hFO hx') (le_normalizer hx'x)
        · exact ABGLocalTools.mem_normalizer_inf htO (le_normalizer htx)
      have hx'V : x' ∈ closure ({x', t} : Set X) := subset_closure (Set.mem_insert _ _)
      have htV : t ∈ closure ({x', t} : Set X) :=
        subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton t))
      have hx't1 : x' * t ≠ 1 := fun h =>
        S₀.t_not_mem (by rw [eq_inv_of_mul_eq_one_right h]; exact J.inv_mem (hFJ hx'))
      have hne₁ : x' ≠ x' * t := fun h => ht1 (by simpa using h)
      have hne₂ : t ≠ x' * t := fun h => hx'1 (by simpa using h)
      have hprod := ABGLocalTools.four_group_odd_eq_mul_centralizers hYodd hVY hx'V htV
        (mul_mem hx'V htV) hx'1 ht1 hx't1 hx't hne₁ hne₂
      have h₁ : Y ⊓ centralizer ({x'} : Set X) ≤ H := by
        intro y hy
        have hyF : y ∈ centralizer (F : Set X) := by
          rw [ABGLocalTools.centralizer_kleinFour_eq (T := F) hx hx' hx1 hx'1 hxx']
          exact ⟨hy.1.2, hy.2⟩
        exact hFH (Subgroup.centralizer_le_normalizer _ hyF)
      have h₂ : Y ⊓ centralizer ({t} : Set X) ≤ H := inf_le_right.trans hCt
      have h₃ : Y ⊓ centralizer ({x' * t} : Set X) ≤ H :=
        hB0 F hFJ hFC hFk DF hDF hFs x hx hx1 x' hx' hx'1 hxx'
      intro y hy
      have hy' : y ∈ (Y : Set X) := hy
      rw [hprod] at hy'
      obtain ⟨_, ⟨c₁, hc₁, c₂, hc₂, rfl⟩, c₃, hc₃, rfl⟩ := hy'
      exact mul_mem (mul_mem (h₁ hc₁) (h₂ hc₂)) (h₃ hc₃)
    obtain ⟨a₁, a₂, a₃, h₁, h₂, h₃, h₁₁, h₂₁, h₃₁, h₁₂, h₁₃, h₂₃⟩ := exists_three_of_klein hFk
    have hprod := ABGLocalTools.four_group_odd_eq_mul_centralizers hodd hFO h₁ h₂ h₃ h₁₁ h₂₁ h₃₁
      h₁₂ h₁₃ h₂₃
    intro y hy
    have hy' : y ∈ (Of : Set X) := hy
    rw [hprod] at hy'
    obtain ⟨_, ⟨c₁, hc₁, c₂, hc₂, rfl⟩, c₃, hc₃, rfl⟩ := hy'
    exact mul_mem (mul_mem (hC a₁ h₁ h₁₁ a₂ h₂ h₂₁ h₁₂ hc₁) (hC a₂ h₂ h₂₁ a₃ h₃ h₃₁ h₂₃ hc₂))
      (hC a₃ h₃ h₃₁ a₁ h₁ h₁₁ h₁₃.symm hc₃)
  exact S₀.centralizer_le_of_two_of_oddCore h33 h35 hT13 hML hSch hPump hN1 hMH hMpc hJM hHN
    hsup hρ hfH hf2 hft hf2pt hOf

end CFSG.ComponentClassification.SolMax
