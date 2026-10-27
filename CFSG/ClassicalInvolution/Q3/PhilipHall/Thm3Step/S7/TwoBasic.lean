module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.Orbit
import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.Sub
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf19Sec6Lift

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Ident

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Thm3A
  CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups

section TypeR

variable {G : Type} [Group G] [Finite G] {Ψ : Set (Subgroup G)}

theorem mul_self_eq_one_of_central_q8 (a : QuaternionGroup 2) (ha : ∀ b, a * b = b * a) :
    a * a = 1 := by
  revert a
  decide

theorem not_isPGroup_two_sl23 : ¬ IsPGroup 2 SL(2, ZMod 3) := by
  intro h
  obtain ⟨g, hg3, hg1⟩ : ∃ g : SL(2, ZMod 3), g ^ 3 = 1 ∧ g ≠ 1 := by decide
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ho : orderOf g = 3 := orderOf_eq_prime hg3 hg1
  obtain ⟨k, hk⟩ := h g
  have h3 : 3 ∣ 2 ^ k := ho ▸ orderOf_dvd_of_pow_eq_one hk
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

theorem closure_twoElements_eq (hΨ : TypeRHyp Ψ) {J : Subgroup G} (hJ : J ∈ Ψ) :
    Subgroup.closure {x : G | x ∈ J ∧ IsPGroup 2 (Subgroup.zpowers x)} = J := by
  rcases hΨ.hyp.omega2 J hJ with h | h
  · exact h
  · obtain ⟨e⟩ := h
    exact absurd ((hΨ.twoGroup J hJ).of_equiv e) not_isPGroup_two_sl23

theorem eq_one_or_eq_of_central (hΨ : TypeRHyp Ψ) {J : Subgroup G} (hJ : J ∈ Ψ) {z : G}
    (hz : IsUniqueInvolution J z) {v : G} (hvJ : v ∈ J) (hv2 : IsPGroup 2 (Subgroup.zpowers v))
    (hvc : ∀ w ∈ J, v * w = w * v) : v = 1 ∨ v = z := by
  have hvle : Subgroup.zpowers v ≤ J := (Subgroup.zpowers_le).mpr hvJ
  obtain ⟨P, hP, hvP⟩ := IsSylow2In.exists_ge hv2 hvle
  obtain ⟨e⟩ := hΨ.sylow J hJ P hP
  have hvP' : v ∈ P := hvP (Subgroup.mem_zpowers v)
  have hc : ∀ b, e ⟨v, hvP'⟩ * b = b * e ⟨v, hvP'⟩ := by
    intro b
    obtain ⟨b', rfl⟩ := e.surjective b
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hvc b' (hP.1 b'.2))
  have h1 := mul_self_eq_one_of_central_q8 _ hc
  rw [← map_mul, ← map_one e] at h1
  have h2 : v * v = 1 := congrArg Subtype.val (e.injective h1)
  exact hz.unique v hvJ h2

theorem conjSub_le_normalizer (hΨ : TypeRHyp Ψ) {K : Subgroup G} (hK : K ∈ Ψ) {z : G}
    (hz : IsUniqueInvolution K z) {c : G} (hc : c ∈ Subgroup.centralizer ({z} : Set G)) :
    conjSub c K ≤ Subgroup.normalizer (K : Set G) := by
  by_cases hJK : conjSub c K = K
  · rw [hJK]
    exact Subgroup.le_normalizer
  have hJ : conjSub c K ∈ Ψ := hΨ.hyp.conjInvariant c K hK
  have hcz : c * z * c⁻¹ = z := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hc]
    group
  have hzJ : IsUniqueInvolution (conjSub c K) z := by
    have := hz.conj c
    rwa [hcz] at this
  have hJC : conjSub c K ≤ Subgroup.centralizer ({z} : Set G) :=
    le_centralizer_of_isUniqueInvolution hzJ
  rw [← closure_twoElements_eq hΨ hJ, Subgroup.closure_le]
  rintro v ⟨hvJ, hv2⟩
  by_cases hvc : ∀ w ∈ conjSub c K, v * w = w * v
  · rcases eq_one_or_eq_of_central hΨ hJ hzJ hvJ hv2 hvc with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.le_normalizer hz.mem
  · exact hΨ.hyp.omega5 K hK _ hJ (Ne.symm hJK) z hz v hvJ hvc hv2
      (Subgroup.mem_centralizer_singleton_iff.mp (hJC hvJ))

theorem oddCoreOf_le_oddCoreOf_centralizer (hΨ : TypeRHyp Ψ) {K : Subgroup G} (hK : K ∈ Ψ)
    {z : G} (hz : IsUniqueInvolution K z) :
    oddCoreOf K ≤ oddCoreOf (Subgroup.centralizer ({z} : Set G)) := by
  set C := Subgroup.centralizer ({z} : Set G) with hC
  set N := omegaGen (lOrbit C K) with hN
  have hKC : K ≤ C := le_centralizer_of_isUniqueInvolution hz
  have hNK : N ≤ Subgroup.normalizer (K : Set G) := by
    refine iSup₂_le fun J hJ => ?_
    obtain ⟨c, hc, rfl⟩ := hJ
    exact conjSub_le_normalizer hΨ hK hz hc
  have hNC : N ≤ C := by
    refine iSup₂_le fun J hJ => ?_
    obtain ⟨c, hc, rfl⟩ := hJ
    have := conjSub_mono (n := c) hKC
    rwa [conjSub_eq_self_of_mem hc] at this
  have h1 : oddCoreOf K ≤ oddCoreOf N :=
    T8.oddCoreOf_le_oddCoreOf_of_normalized (le_omegaGen mem_lOrbit_self)
      fun n hn => mem_normalizer_iff_conjSub_eq.mp (hNK hn)
  have h2 : oddCoreOf N ≤ oddCoreOf C :=
    T8.oddCoreOf_le_oddCoreOf_of_normalized hNC fun c hc =>
      mem_normalizer_iff_conjSub_eq.mp
        (T3Core.conjStab_le_normalizer_omegaGen _ (le_conjStab_lOrbit hc))
  exact h1.trans h2

theorem nonempty_q8_of_oddCore_eq_bot (hΨ : TypeRHyp Ψ) {K : Subgroup G} (hK : K ∈ Ψ)
    (hO : classicalInvolutionOddCore ↥K = ⊥) : Nonempty (↥K ≃* QuaternionGroup 2) := by
  have h2 : IsPGroup 2 ↥K := (hΨ.twoGroup K hK).of_equiv
    ((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot)
  exact hΨ.sylow K hK K ⟨le_rfl, h2, fun V' hV' _ hKV' => le_antisymm hV' hKV'⟩

theorem nonempty_q8_of_oddCore_centralizer_eq_bot (hΨ : TypeRHyp Ψ) {K : Subgroup G} (hK : K ∈ Ψ)
    {z : G} (hz : IsUniqueInvolution K z)
    (hC : classicalInvolutionOddCore ↥(Subgroup.centralizer ({z} : Set G)) = ⊥) :
    Nonempty (↥K ≃* QuaternionGroup 2) := by
  refine nonempty_q8_of_oddCore_eq_bot hΨ hK ?_
  have h1 := oddCoreOf_le_oddCoreOf_centralizer hΨ hK hz
  have h2 : oddCoreOf (Subgroup.centralizer ({z} : Set G)) = ⊥ := by
    unfold oddCoreOf
    rw [hC, Subgroup.map_bot]
  have h3 : oddCoreOf K = ⊥ := le_bot_iff.mp (h2 ▸ h1)
  unfold oddCoreOf at h3
  exact (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).mp h3

theorem card_eq_eight_of_q8 {T : Type} [Group T] (e : T ≃* QuaternionGroup 2) : Nat.card T = 8 := by
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem typeRHyp_conjClass_subgroupOf (hΨ : TypeRHyp Ψ) {M X : Subgroup G} (hM : M ∈ Ψ)
    (hMX : M ≤ X) : TypeRHyp (CoreAssembly.conjClass (M.subgroupOf X)) := by
  refine typeRHyp_of_subset (hΨ.restrict X) ?_ (TL4.conjInvariant_conjClass _)
  rintro _ ⟨x, rfl⟩
  refine ⟨conjSub (x : G) M, hΨ.hyp.conjInvariant _ M hM, ?_, (conjSub_subgroupOf X x M)⟩
  have := conjSub_mono (n := (x : G)) hMX
  rwa [conjSub_eq_self_of_mem x.2] at this

end TypeR

section SL23

variable {G : Type} [Group G] [Finite G] {Ψ : Set (Subgroup G)}

theorem nonempty_sl23_of_classical {Λ : Subgroup G} {z : G} (hΛ : IsClassicalMember3 Λ z)
    (h24 : Nat.card Λ = 24) : Nonempty (↥Λ ≃* SL(2, ZMod 3)) := by
  refine hΛ.nonempty_equiv_sl2 ?_
  obtain ⟨e⟩ := hΛ.nonempty_equiv
  have hq : Nat.card (↥Λ ⧸ classicalInvolutionOddCore ↥Λ) = 24 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    rfl
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (classicalInvolutionOddCore ↥Λ)
  rw [hq, h24] at h
  have h1 : Nat.card (classicalInvolutionOddCore ↥Λ) = 1 := by omega
  exact Subgroup.eq_bot_of_card_eq _ h1

theorem card_eq_eight_of_le (hΨ : TypeRHyp Ψ) {K Λ : Subgroup G} (hK : K ∈ Ψ) (hKΛ : K ≤ Λ)
    (e : ↥Λ ≃* SL(2, ZMod 3)) : Nat.card K = 8 := by
  have hΛ : Nat.card Λ = 24 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    rfl
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥K) := inferInstance
  obtain ⟨eS⟩ := hΨ.sylow K hK _ (isSylow2In_map_subtype K S)
  have h8 : 8 ∣ Nat.card K := by
    have := Subgroup.card_dvd_of_le (Subgroup.map_subtype_le (S : Subgroup K))
    rwa [card_eq_eight_of_q8 eS] at this
  have h24 : Nat.card K ∣ 24 := hΛ ▸ Subgroup.card_dvd_of_le hKΛ
  have hcases : Nat.card K = 8 ∨ Nat.card K = 24 := by
    have hle : Nat.card K ≤ 24 := Nat.le_of_dvd (by norm_num) h24
    obtain ⟨k, hk⟩ := h8
    rw [hk] at h24 hle ⊢
    have hk3 : k ≤ 3 := by omega
    interval_cases k
    · norm_num at h24
    · left; rfl
    · norm_num at h24
    · right; rfl
  rcases hcases with h | h
  · exact h
  · exfalso
    have hKΛ' : K = Λ := Subgroup.eq_of_le_of_card_ge hKΛ (by rw [h, hΛ])
    subst hKΛ'
    have hO : classicalInvolutionOddCore ↥K = ⊥ :=
      Q3.TC.Thin.classicalInvolutionOddCore_eq_bot_of_mulEquiv e.symm
        Q3T6.classicalInvolutionOddCore_sl2Three
    have h2 : IsPGroup 2 ↥K := (hΨ.twoGroup K hK).of_equiv
      ((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot)
    exact not_isPGroup_two_sl23 (h2.of_equiv e)

theorem eq_of_card_eight {Λ A B : Subgroup G} (e : ↥Λ ≃* SL(2, ZMod 3)) (hA : A ≤ Λ) (hB : B ≤ Λ)
    (hA8 : Nat.card A = 8) (hB8 : Nat.card B = 8) : A = B := by
  have hcard : ∀ {C : Subgroup G}, C ≤ Λ → Nat.card C = 8 →
      Nat.card ↥((C.subgroupOf Λ).map e.toMonoidHom) = 8 := by
    intro C hC h8
    rw [Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC).toEquiv, h8]
  have hAB : (A.subgroupOf Λ).map e.toMonoidHom = (B.subgroupOf Λ).map e.toMonoidHom := by
    ext g
    rw [Frame.TwinThin.mem_iff_pow_four_of_card_eight _ (hcard hA hA8),
      Frame.TwinThin.mem_iff_pow_four_of_card_eight _ (hcard hB hB8)]
  have h := Subgroup.map_injective e.injective hAB
  rwa [Subgroup.subgroupOf_inj, inf_eq_left.mpr hA, inf_eq_left.mpr hB] at h

end SL23

section Over

variable {Y : Type} [Group Y] {L : Subgroup Y}

theorem center_eq_bot_of_le (hC : Subgroup.centralizer (L : Set Y) = ⊥) {X : Subgroup Y}
    (hLX : L ≤ X) : Subgroup.center ↥X = ⊥ := by
  refine eq_bot_iff.mpr fun x hx => ?_
  have hx' : (x : Y) ∈ Subgroup.centralizer (L : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hx ⟨l, hLX hl⟩))
  rw [hC, Subgroup.mem_bot] at hx'
  exact Subgroup.mem_bot.mpr (Subtype.ext hx')

theorem eq_of_le_of_isSimpleGroup (hLn : L.Normal) (hL : L ≠ ⊥) {X : Subgroup Y} (hLX : L ≤ X)
    [IsSimpleGroup ↥X] : X = L := by
  haveI : (L.subgroupOf X).Normal := hLn.subgroupOf X
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (L.subgroupOf X) with h | h
  · exfalso
    apply hL
    rw [Subgroup.subgroupOf_eq_bot] at h
    exact le_bot_iff.mp (fun x hx => h.le_bot ⟨hx, hLX hx⟩)
  · exact le_antisymm (Subgroup.subgroupOf_eq_top.mp h) hLX

theorem nonempty_fStarQuot_equiv [Finite Y] (hLn : L.Normal) [IsSimpleGroup ↥L]
    (hnab : ∃ a b : L, a * b ≠ b * a) (hC : Subgroup.centralizer (L : Set Y) = ⊥)
    {X : Subgroup Y} (hLX : L ≤ X) : Nonempty (TL4.FStarQuot ↥X ≃* ↥L) := by
  have hF := genFittingFStar_eq_of_le hLn hnab hC hLX
  have hZ : Subgroup.center ↥(genFittingFStar ↥X) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : ((x : X) : Y) ∈ Subgroup.centralizer (L : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hlF : (⟨l, hLX hl⟩ : X) ∈ genFittingFStar ↥X := by
        rw [hF]
        exact hl
      exact congrArg (fun y : genFittingFStar ↥X => ((y : X) : Y))
        (Subgroup.mem_center_iff.mp hx ⟨_, hlF⟩)
    rw [hC, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subtype.ext hx'))
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans
    ((MulEquiv.subgroupCongr hF).trans (Subgroup.subgroupOfEquivOfLe hLX))⟩

end Over

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Ident
