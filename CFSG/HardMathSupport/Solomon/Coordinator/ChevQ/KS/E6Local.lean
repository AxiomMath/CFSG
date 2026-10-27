module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6LocalFix
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.U6Model

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Dickson.I271 Bal209F4Aux
  OuterFourInAux

@[expose] def InnerOneBalanceAt (Q : Type) [Group Q] (s : Q) : Prop :=
  CFSG.Open.GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set Q)) = ⊥ ∧
    ∀ σ : MulAut Q, σ ^ 2 = 1 → σ ∉ innerAut Q → ∃ t : Q, s * t = t * s ∧ σ t ≠ t

@[expose] def E6ThreeCentralCore : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], (∃ d : TauCeti.ValidLieTypeIndex, IsTwE6EightIndex d.1 ∧
    Nonempty (Q ≃* (TauCeti.CFSGIndex.lie d).Group)) → ∀ z : Q, IsThreeCentral Q z →
      CFSG.Open.GLAPPrimeCoreOf 3 (Subgroup.centralizer ({z} : Set Q)) = ⊥

namespace E6LocalAux

theorem innerOneBalanceAt_of_threeCentral {Q : Type} [Group Q] [Finite Q]
    (hQ : ∃ d : TauCeti.ValidLieTypeIndex, IsTwE6EightIndex d.1 ∧
      Nonempty (Q ≃* (TauCeti.CFSGIndex.lie d).Group))
    {z : Q} (hz : IsThreeCentral Q z)
    (hcore : CFSG.Open.GLAPPrimeCoreOf 3 (Subgroup.centralizer ({z} : Set Q)) = ⊥) {s : Q}
    (hs : s ∈ Subgroup.zpowers z) (hs1 : s ≠ 1) : InnerOneBalanceAt Q s := by
  refine ⟨by rw [centralizer_eq_of_mem_zpowers hz.1 hs hs1]; exact hcore, ?_⟩
  intro σ hσ2 hσi
  obtain ⟨t, hzt, hσt⟩ := noOuterFixes_of_threeCentral hQ hz σ hσ2 hσi
  refine ⟨t, ?_, hσt⟩
  have hzC : z ∈ Subgroup.centralizer ({t} : Set Q) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hzt
  have := Subgroup.zpowers_le.2 hzC hs
  rw [Subgroup.mem_centralizer_singleton_iff] at this
  exact this

end E6LocalAux

section Main

open E6LocalAux

theorem e6Local_of_innerBalance {X : Type} [Group X] [Finite X] {K A : Subgroup X}
    (hK : CFSG.Open.IsComponentOf K ⊤) (hLie : IsLieQuot ↥K IsTwE6EightIndex)
    (hAN : A ≤ Subgroup.normalizer (K : Set X))
    (hout : ∀ (a : X) (ha : a ∈ A), ¬ InnerAt K a →
      FieldAutTwE6 (↥K ⧸ Subgroup.center ↥K) (actHom K ⟨a, hAN ha⟩))
    (hin : ∀ (a : X) (ha : a ∈ A), InnerAt K a → ∀ s : ↥K ⧸ Subgroup.center ↥K,
      actHom K ⟨a, hAN ha⟩ = MulAut.conj s → s ≠ 1 →
        InnerOneBalanceAt (↥K ⧸ Subgroup.center ↥K) s) :
    IsCompLocallyBalanced 3 1 A K := by
  classical
  have hq : CFSG.Open.IsQuasisimple ↥K := hK.2.2
  have hperf : commutator ↥K = ⊤ := hq.1
  have hS : ∃ d : TauCeti.ValidLieTypeIndex, IsTwE6EightIndex d.1 ∧
      Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* (TauCeti.CFSGIndex.lie d).Group) := hLie
  have h3 : 3 ∣ Nat.card ↥K := by
    have h3S : 3 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) := by
      rw [card_eq_ordTwistedE6 hS]
      norm_num [ordTwistedE6]
    exact h3S.trans (Subgroup.card_quotient_dvd_card _)
  have hNZ : GLAPPrimeCore 3 ↥K ≤ Subgroup.center ↥K :=
    Bal209TwoInAux.pPrimeCore_le_center_of_quasisimple hq Nat.prime_three h3
  have hψ := barToS_injective hperf hNZ
  have hinn := innerAut_le_map_barToS hperf hNZ
  have hcenS : Subgroup.center (↥K ⧸ Subgroup.center ↥K) = ⊥ := center_quot_eq_bot hq
  have hinj : Function.Injective (MulAut.conj : (↥K ⧸ Subgroup.center ↥K) →*
      MulAut (↥K ⧸ Subgroup.center ↥K)) := conj_inj_of_center_bot hcenS
  intro D hD H hH hDH
  obtain ⟨hDA, hDel, hDcard⟩ := hD
  obtain ⟨d, hdD, hd1⟩ : ∃ d ∈ D, d ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : D = ⊥ := (Subgroup.eq_bot_iff_forall D).2 hcon
    rw [hbot, Subgroup.card_bot] at hDcard
    norm_num at hDcard
  obtain ⟨γ, hγ, rfl⟩ := hDA hdD
  have hγA : (γ : X) ∈ A := (Subgroup.mem_subgroupOf.1 hγ).1
  have hψγ := barToS_barAut hperf hNZ γ
  have hd3 : barAut 3 K γ ^ 3 = 1 := hDel.2 _ hdD
  by_cases hinner : InnerAt K (γ : X)
  ·
    obtain ⟨k, hk, c, hc, hγkc⟩ := innerAt_iff.1 hinner
    have hb : k * c ∈ Subgroup.normalizer (K : Set X) := hγkc ▸ γ.2
    obtain ⟨s, hs⟩ : ∃ s : ↥K ⧸ Subgroup.center ↥K, s = QuotientGroup.mk (⟨k, hk⟩ : ↥K) :=
      ⟨_, rfl⟩
    have hact : actHom K γ = MulAut.conj s := by
      have hγeq : γ = ⟨k * c, hb⟩ := Subtype.ext hγkc
      rw [hs, hγeq]
      exact actHom_eq_conj_of_mul hk hc hb
    have hs1 : s ≠ 1 := by
      intro h1
      apply hd1
      apply hψ
      rw [hψγ, hact, h1, map_one, map_one]
    obtain ⟨hcore, hnofix⟩ := hin (γ : X) hγA hinner s hact hs1
    have hbalS : ∀ H' : Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K)), innerAut _ ≤ H' →
        GLAPPrimeCoreOf 3 (H' ⊓ Subgroup.centralizer
          ({MulAut.conj s} : Set (MulAut (↥K ⧸ Subgroup.center ↥K)))) = ⊥ := fun H' hH' =>
      F4LocalOneAux.oneBalanced_at_of_good Nat.prime_three hcenS
        (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner _))
        (fun α => QuotientGroup.eq_one_iff α) (outer_sq_eq_one_of_coprime hS) hcore hnofix H' hH'
    have hcore' := coreBot_of_map _ hψ hinn (d := barAut 3 K γ) (H := H)
      (by rw [hψγ, hact]; exact hbalS) hH
    exact localDeltaIn_eq_bot_of_core_eq_bot hdD hd1 hcore'
  ·
    have hfa := hout (γ : X) hγA hinner
    have hφ3 : actHom K γ ^ 3 = 1 := by rw [← hψγ, ← map_pow, hd3, map_one]
    have hfc := fieldCoreAt_of_fieldAutTwE6 hφ3 hfa
    exact U6LocalAux.localDeltaIn_eq_bot_of_map Nat.prime_three _ hψ hinn hinj hH hdD hd1
      (by rwa [hψγ])

theorem e6_localBalance_at_threeCentral_of_core (h1 : E6ThreeCentralCore) {X : Type} [Group X]
    [Finite X] {K : Subgroup X} {x y : X} (hK : CFSG.Open.IsComponentOf K ⊤)
    (hLie : IsLieQuot ↥K IsTwE6EightIndex) (hxN : x ∈ Subgroup.normalizer (K : Set X))
    (hyN : y ∈ Subgroup.normalizer (K : Set X)) (hxy : Commute x y) (hx3 : x ^ 3 = 1)
    (hy3 : y ^ 3 = 1) {z : ↥K ⧸ Subgroup.center ↥K}
    (hyz : actHom K ⟨y, hyN⟩ = MulAut.conj z) (hz : IsThreeCentral (↥K ⧸ Subgroup.center ↥K) z)
    (hxI : InnerAt K x → x ∈ Subgroup.zpowers y)
    (hout : ∀ a ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y,
      (haN : a ∈ Subgroup.normalizer (K : Set X)) → ¬ InnerAt K a →
        FieldAutTwE6 (↥K ⧸ Subgroup.center ↥K) (actHom K ⟨a, haN⟩)) :
    IsCompLocallyBalanced 3 1 (Subgroup.zpowers x ⊔ Subgroup.zpowers y) K := by
  classical
  have hq : CFSG.Open.IsQuasisimple ↥K := hK.2.2
  have hperf : commutator ↥K = ⊤ := hq.1
  have hS : ∃ d : TauCeti.ValidLieTypeIndex, IsTwE6EightIndex d.1 ∧
      Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* (TauCeti.CFSGIndex.lie d).Group) := hLie
  have hcenS : Subgroup.center (↥K ⧸ Subgroup.center ↥K) = ⊥ := center_quot_eq_bot hq
  have hinj : Function.Injective (MulAut.conj : (↥K ⧸ Subgroup.center ↥K) →*
      MulAut (↥K ⧸ Subgroup.center ↥K)) := conj_inj_of_center_bot hcenS
  have hApair := sup_zpowers_eq_pairSub hxy
  have hAN : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ Subgroup.normalizer (K : Set X) :=
    sup_le (Subgroup.zpowers_le.2 hxN) (Subgroup.zpowers_le.2 hyN)
  have hyI : y ∈ innerSub K := by
    refine (innerAt_iff_congr_mem_innSub hperf (MulEquiv.refl _) hyN).2 ?_
    rw [hyz]
    exact ⟨z, rfl⟩
  refine e6Local_of_innerBalance hK hLie hAN (fun a ha hna => hout a ha (hAN ha) hna) ?_
  intro a ha hain s hs hs1
  have hay : a ∈ Subgroup.zpowers y := by
    by_cases hxin : InnerAt K x
    · have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ Subgroup.zpowers y :=
        sup_le (Subgroup.zpowers_le.2 (hxI hxin)) le_rfl
      exact hle ha
    · exact mem_zpowers_of_inner_mem_pairSub hxy hx3 (fun h => hxin h) hyI (hApair ▸ ha) hain
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hay
  have hsz : s ∈ Subgroup.zpowers z := by
    have hact : actHom K ⟨y ^ j, hAN ha⟩ = MulAut.conj (z ^ j) := by
      have hpow : (⟨y ^ j, hAN ha⟩ : ↥(Subgroup.normalizer (K : Set X))) =
          (⟨y, hyN⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ j := Subtype.ext (by simp)
      rw [hpow, map_zpow, hyz, map_zpow]
    have hsj : s = z ^ j := hinj (hs.symm.trans hact)
    rw [hsj]
    exact Subgroup.zpow_mem_zpowers z j
  exact innerOneBalanceAt_of_threeCentral hS hz (h1 _ hS z hz) hsz hs1

end Main

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
