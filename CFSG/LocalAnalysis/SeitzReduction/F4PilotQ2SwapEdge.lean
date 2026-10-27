module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2SwapCT
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.SeitzReduction.SeitzQ2 (SwapParam)
open CFSG.LieType.Ree (ReeTag)

section Sylow

variable {M : Type*} [Group M] [Finite M]

theorem odd_card_of_isPGroup_card_le_two {W : Subgroup M} [hWn : W.Normal]
    (h2 : ∀ U : Subgroup M, IsPGroup 2 U → Nat.card U ≤ 2) {t : M} (ht : orderOf t = 2)
    (htW : t ∉ W) : Odd (Nat.card W) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  have h2W : 2 ∣ Nat.card W := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hodd)
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := W) 2 h2W
  have hs' : orderOf (s : M) = 2 := by rw [Subgroup.orderOf_coe, hs]
  have hsyl : ∀ g : M, orderOf g = 2 → ∃ Q : Sylow 2 M, (Q : Subgroup M) = zpowers g := by
    intro g hg
    have hcard : Nat.card (zpowers g) = 2 := by rw [Nat.card_zpowers, hg]
    have hP : IsPGroup 2 (zpowers g) := IsPGroup.of_card (n := 1) (by rw [hcard, pow_one])
    obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
    refine ⟨Q, (Subgroup.eq_of_le_of_card_ge hQ ?_).symm⟩
    rw [hcard]
    exact h2 Q Q.isPGroup'
  obtain ⟨Q, hQ⟩ := hsyl _ hs'
  obtain ⟨Q', hQ'⟩ := hsyl t ht
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq M Q Q'
  have htQ' : t ∈ (Q' : Subgroup M) := hQ' ▸ mem_zpowers t
  rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at htQ'
  obtain ⟨b, hb, hbt⟩ := htQ'
  rw [hQ] at hb
  have hbW : b ∈ W := (zpowers_le.2 s.2) hb
  apply htW
  rw [← hbt, MulAut.smul_def, MulAut.conj_apply]
  exact hWn.conj_mem b hbW c

end Sylow

section Swap

variable {G : Type*} [Group G] [Finite G]

theorem inf_eq_bot_of_isPGroup_two_of_odd {H : Type*} [Group H] [Finite H] {A T : Subgroup H}
    (hA : IsPGroup 2 A) (hT : Odd (Nat.card T)) : A ⊓ T = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  rw [mem_bot]
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hA) ⟨y, hy.1⟩
  rw [Subgroup.orderOf_mk] at hk
  have hdvd : orderOf y ∣ Nat.card T := Subgroup.orderOf_dvd_natCard T hy.2
  rw [hk] at hdvd
  have hodd : Odd (2 ^ k) := Odd.of_dvd_nat hT hdvd
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact orderOf_eq_one_iff.1 hk
  · exact absurd hodd (Nat.not_odd_iff_even.2 (Nat.even_pow.2 ⟨even_two, Nat.succ_ne_zero k⟩))

theorem odd_card_centralizer_inf_centralizer_of_swapParam {t : G} {D X : Subgroup G}
    (P : SwapParam t D) (hrange : P.Ψ.range = centralizerPerfectCore X)
    (htX : t ∈ centralizer (X : Set G))
    (ht : orderOf t = 2) {x : G} (hx : x ∈ D) (hxZ : (⟨x, hx⟩ : D) ∉ center D)
    (hsyl : ∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsPGroup 2 U →
      U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
      Nat.card U ≤ 2) :
    Odd (Nat.card (centralizer (X : Set G) ⊓
      centralizer (centralizerPerfectCore X : Set G) : Subgroup G)) := by
  set H : Subgroup G := centralizer (X : Set G) with hHdef
  set E : Subgroup G := centralizerPerfectCore X with hEdef
  set W : Subgroup G := H ⊓ centralizer (E : Set G) with hWdef
  set M : Subgroup G := H ⊓ centralizer (D : Set G) with hMdef
  set π := QuotientGroup.mk' (oddCore H) with hπ
  have hDE : D ≤ E := fun d hd => hrange ▸ ⟨(⟨d, hd⟩, ⟨d, hd⟩), P.diag ⟨d, hd⟩⟩
  have hWM : W ≤ M := inf_le_inf le_rfl (centralizer_le hDE)
  have htD : t ∈ centralizer (D : Set G) := by
    rw [mem_centralizer_iff]
    intro d hd
    have h1 := P.swap ⟨d, hd⟩ ⟨d, hd⟩
    rw [P.diag] at h1
    calc d * t = t * d * t⁻¹ * t := by rw [h1]
      _ = t * d := by group
  have htM : t ∈ M := ⟨htX, htD⟩
  have htW : t ∉ W := by
    rintro ⟨-, htE⟩
    have hmem : P.lft x ∈ E := hrange ▸ swapParam_lft_mem_range P
    have h1 := mem_centralizer_iff.1 htE (P.lft x) hmem
    apply P.lft_ne_conj_lft hx hxZ
    rw [← h1, mul_inv_cancel_right]
  have hWn : (W.subgroupOf M).Normal := by
    refine ⟨fun w hw m => ?_⟩
    rw [mem_subgroupOf] at hw ⊢
    obtain ⟨hwH, hwE⟩ := Subgroup.mem_inf.1 hw
    have hmH : (m : G) ∈ H := (Subgroup.mem_inf.1 m.2).1
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · simp only [coe_mul, coe_inv]
      exact mul_mem (mul_mem hmH hwH) (inv_mem hmH)
    · rw [mem_centralizer_iff]
      intro y hy
      have hy' : (m : G)⁻¹ * y * ((m : G)⁻¹)⁻¹ ∈ E :=
        conj_mem_centralizerPerfectCore_of_mem_centralizer (inv_mem hmH) hy
      have h1 := mem_centralizer_iff.1 hwE _ hy'
      simp only [coe_mul, coe_inv, inv_inv] at h1 ⊢
      calc y * ((m : G) * w * (m : G)⁻¹) =
          (m : G) * (((m : G)⁻¹ * y * (m : G)) * w) * (m : G)⁻¹ := by group
        _ = (m : G) * (w * ((m : G)⁻¹ * y * (m : G))) * (m : G)⁻¹ := by rw [h1]
        _ = (m : G) * w * (m : G)⁻¹ * y := by group
  have h2 : ∀ U : Subgroup M, IsPGroup 2 U → Nat.card U ≤ 2 := by
    intro U hU
    have hMH : M ≤ H := inf_le_left
    set f : M →* H := Subgroup.inclusion hMH with hf
    have hfinj : Function.Injective f := Subgroup.inclusion_injective hMH
    set U' : Subgroup H := U.map f with hU'
    have hU'p : IsPGroup 2 U' := hU.map f
    have hcard' : Nat.card U' = Nat.card U := Subgroup.card_map_of_injective hfinj
    have hdisj : U' ⊓ oddCore H = ⊥ :=
      inf_eq_bot_of_isPGroup_two_of_odd hU'p CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
    have hV : IsPGroup 2 (U'.map π) := hU'p.map π
    have hVC : U'.map π ≤ centralizer ((D.subgroupOf H).map π : Set (H ⧸ oddCore H)) := by
      rintro _ ⟨u, hu, rfl⟩
      rw [mem_centralizer_iff]
      rintro _ ⟨d, hd, rfl⟩
      obtain ⟨m, -, rfl⟩ := hu
      have hmD : (m : G) ∈ centralizer (D : Set G) := m.2.2
      have hc : d * f m = f m * d := Subtype.ext (mem_centralizer_iff.1 hmD d (mem_subgroupOf.1 hd))
      rw [← map_mul, ← map_mul, hc]
    have h1 := hsyl _ hV hVC
    rw [card_map_mk'_of_inf_eq_bot _ hdisj, hcard'] at h1
    exact h1
  have ht' : orderOf (⟨t, htM⟩ : M) = 2 := by rw [Subgroup.orderOf_mk, ht]
  have htW' : (⟨t, htM⟩ : M) ∉ W.subgroupOf M := fun h => htW (mem_subgroupOf.1 h)
  have hodd := odd_card_of_isPGroup_card_le_two (W := W.subgroupOf M) h2 ht' htW'
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWM).toEquiv] at hodd

end Swap

section Edge

open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.SeitzReduction.SeitzQ2 (TwistOn)

variable {G : Type*} [Group G] [Finite G] {t : G}

theorem exists_twistOn_of_edge_of_odd (ht2 : t * t = 1) {DX DY : Subgroup G}
    (PX : SwapParam t DX) (PY : SwapParam t DY)
    (hinjX : Function.Injective PX.Ψ) (hinjY : Function.Injective PY.Ψ)
    {X Y X'' Y'' : Subgroup G} (hrX : PX.Ψ.range = centralizerPerfectCore X)
    (hrY : PY.Ψ.range = centralizerPerfectCore Y) (hX'' : X'' ≤ DX) (hY'' : Y'' ≤ DY)
    (hT : X ⊔ X'' = Y ⊔ Y'') [IsSimpleGroup DX]
    (hZDX : ∀ a : DX, (∀ b : DX, a * b = b * a) → a = 1)
    (hAut : ∀ φ : MulAut DX, ∃ g : DX, φ = MulAut.conj g)
    [IsSimpleGroup (perfectCore (DX ⊓ centralizer (X'' : Set G)))]
    (hZ : center (perfectCore (DX ⊓ centralizer (X'' : Set G))) = ⊥)
    (hZodd : Odd (Nat.card (DX ⊓ centralizer
      (perfectCore (DX ⊓ centralizer (X'' : Set G)) : Set G) ⊓ centralizer (X'' : Set G) :
        Subgroup G)))
    (hWodd : Odd (Nat.card (centralizer (X : Set G) ⊓
      centralizer (centralizerPerfectCore X : Set G) : Subgroup G)))
    (S : Set G)
    (hS : ∀ u ∈ S, u ∈ DX ∧ u ∈ DY ∧ (∀ x ∈ X'', u * x = x * u) ∧ (∀ y ∈ Y'', u * y = y * u) ∧
      (∀ o ∈ perfectCore (DX ⊓ centralizer (X'' : Set G)),
        u * o * u⁻¹ ∈ perfectCore (DX ⊓ centralizer (X'' : Set G))) ∧
      (∀ z ∈ DX ⊓ centralizer (perfectCore (DX ⊓ centralizer (X'' : Set G)) : Set G) ⊓
        centralizer (X'' : Set G), u * z = z * u) ∧ ∃ k : ℕ, u ^ 2 ^ k = 1) :
    ∃ s : ℤˣ, TwistOn s PX PY (closure S) := by
  set O := perfectCore (DX ⊓ centralizer (X'' : Set G)) with hOdef
  have hOX : O ≤ DX := (perfectCore_le _).trans inf_le_left
  obtain ⟨⟨o₀, ho₀⟩, ho₀1⟩ := exists_ne (1 : O)
  have ho₀1' : o₀ ≠ 1 := fun h => ho₀1 (Subtype.ext h)
  refine exists_twistOn_of_edge ht2 PX PY hinjX hinjY hrX hrY hX'' hY'' hT hZ S
    (fun u hu => ?_) (fun u hu c hcX hcX'' hcO hcO' => ?_)
  · obtain ⟨h1, h2, h3, h4, h5, -, h7⟩ := hS u hu
    exact ⟨h1, h2, h3, h4, h5, h7⟩
  · obtain ⟨huX, -, -, -, -, huZ, -⟩ := hS u hu
    exact odd_and_commute_of_mem_overlapCentralizer PX hinjX hrX hZDX hAut hX'' hOX ho₀ ho₀1'
      hZodd hWodd huX huZ hcX hcX'' hcO hcO'

end Edge

section Chains

open CFSG.SeitzReduction.SeitzQ2 (TwistOn signConj)

variable {G : Type*} [Group G] {t : G} {D D' DR : Subgroup G}

theorem twistOn_twist (ht2 : t * t = 1) {s s' : ℤˣ} {P : SwapParam t D} {P' : SwapParam t D'}
    {A : Subgroup G} (h : TwistOn s P P' A) : TwistOn (s' * s) P (P'.twist s') A := fun x hx => by
  rw [SeitzQ2.SwapParam.lft_twist, h x hx, SeitzQ2.signConj_mul ht2]

theorem agreeOn_twist_sup_of_not_commute (ht2 : t * t = 1) {s s' : ℤˣ} {P : SwapParam t D}
    {P' : SwapParam t D'} (hinj' : Function.Injective P'.Ψ) {A B : Subgroup G}
    (hA : TwistOn s P P' A) (hB : TwistOn s' P P' B) (hAD : A ≤ D) (hBD : B ≤ D)
    (hAD' : A ≤ D') (hBD' : B ≤ D') {a b : G} (ha : a ∈ A) (hb : b ∈ B) (hab : a * b ≠ b * a) :
    SeitzQ2.AgreeOn P (P'.twist s) (A ⊔ B) := by
  have hss := eq_of_twistOn_of_not_commute hinj' hA hB ha hb (hAD' ha) (hBD' hb) hab
  subst hss
  have hagr : ∀ {C : Subgroup G}, TwistOn s P P' C → SeitzQ2.AgreeOn P (P'.twist s) C :=
    fun {C} hC x hx => by
      have h := twistOn_twist (s' := s) ht2 hC x hx
      rwa [Int.units_mul_self, SeitzQ2.signConj_one] at h
  have hsup : A ⊔ B = closure ((A : Set G) ∪ B) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  rw [hsup]
  refine agreeOn_closure (fun x hx => ?_) (fun x hx => ?_)
  · rcases hx with hx | hx
    exacts [⟨hAD hx, hAD' hx⟩, ⟨hBD hx, hBD' hx⟩]
  · rcases hx with hx | hx
    exacts [hagr hA x hx, hagr hB x hx]

theorem commute_twist_lft_of_twistOn (ht2 : t * t = 1) {σ σ' : ℤˣ} (s : ℤˣ)
    (R : SwapParam t DR) {P : SwapParam t D} {P' : SwapParam t D'} {A B : Subgroup G}
    (hA : TwistOn σ R P' A) (hB : TwistOn σ' R P B) (hADR : A ≤ DR) (hBDR : B ≤ DR)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    ∀ a ∈ A, ∀ b ∈ B, Commute ((P'.twist s).lft a) (P.lft b) ∧
      Commute ((P'.twist s).lft a) (t * P.lft b * t⁻¹) := fun a ha b hb =>
  commute_lft_of_twistOn ht2 R (twistOn_twist ht2 hA) hB ha hb (hADR ha) (hBDR hb) (hAB a ha b hb)

end Chains

section F4


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem center_subgroupToG_C3Levi_eq_bot [Finite K] [CharP K 2] (e : L ≃* adjointGroup .F4 K) :
    center (subgroupToG e (C3Levi K)) = ⊥ := by
  let eD : C3Levi K ≃* subgroupToG e (C3Levi K) :=
    ((C3Levi K).equivMapOfInjective e.symm.toMonoidHom e.symm.injective).trans
      (((C3Levi K).map e.symm.toMonoidHom).equivMapOfInjective L.subtype L.subtype_injective)
  exact center_eq_bot_congr eD center_C3Levi_eq_bot

theorem odd_card_centralizer_inf_centralizer_nonsplit_F4_two {t : G} (hw : F4Work L K t 1)
    (e : L ≃* adjointGroup .F4 K) {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) (P : SwapParam t (subgroupToG e (C3Levi K)))
    (hrange : P.Ψ.range = centralizerPerfectCore (subgroupToG e X₀)) :
    Odd (Nat.card (centralizer (subgroupToG e X₀ : Set G) ⊓
      centralizer (centralizerPerfectCore (subgroupToG e X₀) : Set G) : Subgroup G)) := by
  have hK2 : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  have := finite_of_natCard_eq_two_pow hw.card_eq
  have := charP_two_of_natCard_eq_two_pow hw.card_eq
  have htC := hw.mem_centralizer
  have hX₀' : Nat.card X₀ = Nat.card K + 1 := by rw [hX₀, hK2]
  have htX : t ∈ centralizer (subgroupToG e X₀ : Set G) :=
    centralizer_le (subgroupToG_le e X₀) htC
  obtain ⟨-, hsyl, -⟩ := neighbour_standard_nonsplit hw.standard.standard htC hw.orderOf_eq
    hw.inf_eq hw.card_eq e hXJ hcyc hX₀' rfl htX rfl
  have hDq : CFSG.IsQuasisimple (subgroupToG e (C3Levi K)) := isQuasisimple_map_C3Levi e
  have : Nontrivial (subgroupToG e (C3Levi K)) := CFSG.LocalCores.isQuasisimple_nontrivial hDq
  obtain ⟨x, hx⟩ := exists_ne (1 : subgroupToG e (C3Levi K))
  refine odd_card_centralizer_inf_centralizer_of_swapParam P hrange htX hw.orderOf_eq x.2 ?_ hsyl
  rw [center_subgroupToG_C3Levi_eq_bot, mem_bot]
  exact hx

end F4

end CFSG.SeitzReduction.F4Pilot
