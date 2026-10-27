module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcE6OneHeads
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcFldConc
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourSc
import CFSG.LieType.SemisimpleCentralizers.HeldLangCover
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SchurFactsCore
import CFSG.CGT.T75P.SylowSplit

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.E6One

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction CFSG.SeitzReduction.EPilot
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.StandardType.NoOffE6Three CFSG.StandardType.TableBExc.E6Three
open CFSG.LieType.Steinberg.CentralExt.MinusculeClosed CFSG.LieType.Steinberg.Isogeny
open CFSG.LieType.Steinberg.Minuscule
open CFSG.HardMathSupport.Timmesfeld.CrossChar (minBC e6RootParams e6Isogeny_minTorus e6Isogeny_minBC)
open scoped commutatorElement

section Cover

theorem exists_mulEquiv_comp_eq_of_central_cover {U L X : Type} [Group U] [Group L] [Group X]
    [Finite U] [Finite L] (πU : U →* X) (πL : L →* X) (hU : Function.Surjective πU)
    (hL : Function.Surjective πL) (hcL : πL.ker ≤ Subgroup.center L) (hperf : Group.IsPerfect L)
    (hsec : ∀ (E : Type) [Group E] [Finite E] (π : E →* U), Function.Surjective π →
      π.ker ≤ Subgroup.center E → ∃ s : U →* E, ∀ g, π (s g) = g)
    (hker : Nat.card πU.ker ≤ Nat.card πL.ker) : ∃ f : U ≃* L, ∀ g, πL (f g) = πU g := by
  classical
  let E : Subgroup (L × U) := CFSG.LieType.SemisimpleCentralizers.HeldLang.fibreProduct πL πU
  let π : E →* U := (MonoidHom.snd L U).comp E.subtype
  have hπ : Function.Surjective π := by
    intro g
    obtain ⟨l, hl⟩ := hL (πU g)
    exact ⟨⟨(l, g), hl⟩, rfl⟩
  have hπc : π.ker ≤ Subgroup.center E := by
    intro x hx
    obtain ⟨⟨l, s⟩, hxm⟩ := x
    have hs : s = 1 := hx
    subst hs
    have hl : l ∈ Subgroup.center L :=
      hcL (by rw [MonoidHom.mem_ker]; exact (show πL l = πU 1 from hxm).trans (map_one πU))
    rw [Subgroup.mem_center_iff]
    rintro ⟨⟨l', s'⟩, hy⟩
    refine Subtype.ext (Prod.ext ?_ ?_)
    · exact Subgroup.mem_center_iff.1 hl l'
    · exact (mul_one s').trans (one_mul s').symm
  obtain ⟨s, hs⟩ := hsec E π hπ hπc
  let φ : U →* L := (MonoidHom.fst L U).comp (E.subtype.comp s)
  have hφ : ∀ g, πL (φ g) = πU g := by
    intro g
    calc πL (φ g) = πU (π (s g)) := (s g).2
      _ = πU g := by rw [hs g]
  have hdec : ∀ x : L, ∃ g : U, ∃ z ∈ Subgroup.center L, x = φ g * z := by
    intro x
    obtain ⟨g, hg⟩ := hU (πL x)
    refine ⟨g, (φ g)⁻¹ * x, ?_, by group⟩
    apply hcL
    rw [MonoidHom.mem_ker, map_mul, map_inv, hφ, hg, inv_mul_cancel]
  have hcomm : ∀ x y : L, ⁅x, y⁆ ∈ φ.range := by
    intro x y
    obtain ⟨g, z, hz, rfl⟩ := hdec x
    obtain ⟨g', z', hz', rfl⟩ := hdec y
    rw [CFSG.LieType.SemisimpleCentralizers.HeldLang.commutatorElement_mul_central_mul_central hz
      hz']
    exact ⟨⁅g, g'⁆, by simp [commutatorElement_def]⟩
  have hsurj : Function.Surjective φ := by
    have h1 : commutator L ≤ φ.range := by
      rw [commutator_def, Subgroup.commutator_le]
      exact fun x _ y _ => hcomm x y
    rw [hperf.commutator_eq_top] at h1
    intro x
    exact h1 (Subgroup.mem_top x)
  have hcardU : Nat.card U = Nat.card X * Nat.card πU.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup πU.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective πU hU).toEquiv]
  have hcardL : Nat.card L = Nat.card X * Nat.card πL.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup πL.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective πL hL).toEquiv]
  have hle : Nat.card U ≤ Nat.card L := by
    rw [hcardU, hcardL]
    exact Nat.mul_le_mul_left _ hker
  exact ⟨MulEquiv.ofBijective φ (hsurj.bijective_of_nat_card_le hle), hφ⟩

theorem eq_of_comp_eq_of_isPerfect {G X : Type*} [Group G] [Group X] (hG : Group.IsPerfect G)
    (p : G →* X) (hp : p.ker ≤ Subgroup.center G) {β₁ β₂ : G →* G}
    (h : p.comp β₁ = p.comp β₂) : β₁ = β₂ := by
  have hz : ∀ x, (β₂ x)⁻¹ * β₁ x ∈ Subgroup.center G := fun x => hp (by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    have := DFunLike.congr_fun h x
    simp only [MonoidHom.comp_apply] at this
    rw [this, inv_mul_cancel])
  have hle : commutator G ≤ MonoidHom.eqLocus β₁ β₂ := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    change β₁ ⁅x, y⁆ = β₂ ⁅x, y⁆
    have e1 : β₁ x = β₂ x * ((β₂ x)⁻¹ * β₁ x) := by group
    have e2 : β₁ y = β₂ y * ((β₂ y)⁻¹ * β₁ y) := by group
    rw [map_commutatorElement, map_commutatorElement, e1, e2,
      CFSG.LieType.SemisimpleCentralizers.HeldLang.commutatorElement_mul_central_mul_central
        (hz x) (hz y)]
  rw [hG.commutator_eq_top] at hle
  exact MonoidHom.ext fun x => hle (Subgroup.mem_top x)

end Cover

section Torus


variable {K : Type} [Field K]

@[expose] noncomputable def zetaTorus (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    Multiplicative (Fin Tag.E6.rank → ZMod 3) →* ↥(e6Data_valid.minGroup K) :=
  (minTorus e6Data_valid K).comp (zetaHom ζ hζ)

theorem zetaTorus_injective {ζ : Kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) :
    Function.Injective (zetaTorus (K := K) ζ hζ) :=
  (minTorus_injective e6Data_valid K).comp (zetaHom_injective hζo hζ)

@[expose] def cartanMulE6 (x : Fin Tag.E6.rank → ZMod 3) : Fin Tag.E6.rank → ZMod 3 :=
  fun j => ∑ l, ((Tag.E6.cartan l j : ℤ) : ZMod 3) * x l

theorem cartanMulE6_mem_hypE6 (x : Fin Tag.E6.rank → ZMod 3) :
    cartanMulE6 x ∈ CFSG.StandardType.NoOffRest.hypE6 := by
  rw [CFSG.StandardType.NoOffRest.mem_hypE6]
  revert x
  decide +kernel

theorem e6RootParams_zetaVec (ζ : Kˣ) (hζ : ζ ^ 3 = 1) (x : Fin Tag.E6.rank → ZMod 3) :
    e6RootParams (zetaVec ζ hζ x) =
      zetaVec ζ hζ (cartanMulE6 x) := by
  funext j
  simp only [e6RootParams, zetaVec, cartanMulE6]
  rw [ofAdd_sum, map_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [zmodPowHom_zpow]

theorem e6Isogeny_zetaTorus [Finite K] (ζ : Kˣ) (hζ : ζ ^ 3 = 1)
    (z : Multiplicative (Fin Tag.E6.rank → ZMod 3)) :
    e6Isogeny K (zetaTorus ζ hζ z) =
      hypTorusHom ζ hζ (Multiplicative.ofAdd ⟨_, cartanMulE6_mem_hypE6 (Multiplicative.toAdd z)⟩) := by
  apply Subtype.ext
  change ((e6Isogeny K (minTorus e6Data_valid K (zetaHom ζ hζ z)) : adjointGroup .E6 K) :
    ModGL .E6 K) = _
  rw [e6Isogeny_minTorus]
  change rootDiagUnit .E6 _ = rootDiagUnit .E6 (zetaVec ζ hζ (cartanMulE6 (Multiplicative.toAdd z)))
  rw [← e6RootParams_zetaVec]
  rfl

theorem e6Isogeny_minBC_eq [Finite K] (σ : K ≃+* K) (g : ↥(e6Data_valid.minGroup K)) :
    e6Isogeny K (minBC e6Data_valid σ.toRingHom g) =
      entrywiseAdjointAut .E6 σ (e6Isogeny K g) := by
  apply Subtype.ext
  rw [e6Isogeny_minBC, coe_entrywiseAdjointAut,
    units_map_entrywiseHom_eq_baseChangeGL]

theorem minBC_minTorus_of_fix {σ : K ≃+* K} {u : Fin Tag.E6.rank → Kˣ}
    (hu : ∀ i, σ ((u i : Kˣ) : K) = u i) :
    minBC e6Data_valid σ.toRingHom
      (minTorus e6Data_valid K u) = minTorus e6Data_valid K u := by
  rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.minBC_minTorus_E6]
  congr 1
  funext i
  exact Units.ext (hu i)

@[expose] def thetaSignE6 (K : Type) [Field K] : Fin Tag.E6.rank → Kˣ :=
  fun j => (-1 : Kˣ) ^ highRoot .E6 j

theorem e6RootParams_thetaSign :
    e6RootParams (thetaSignE6 K) =
      Pi.mulSingle (highNode .E6) (-1 : Kˣ) := by
  funext l
  simp only [e6RootParams, thetaSignE6, ← zpow_mul,
    Finset.prod_zpow_eq_zpow_sum, sum_highRoot_mul_cartan (Or.inl rfl)]
  by_cases hl : l = highNode .E6
  · rw [if_pos hl, zpow_one, hl, Pi.mulSingle_eq_same]
  · rw [if_neg hl, zpow_zero, Pi.mulSingle_eq_of_ne hl]

theorem e6Isogeny_thetaSign [Finite K] :
    e6Isogeny K (minTorus e6Data_valid K (thetaSignE6 K)) = thetaInv K := by
  apply Subtype.ext
  rw [e6Isogeny_minTorus, e6RootParams_thetaSign]
  rfl

theorem thetaSignE6_sq : thetaSignE6 K ^ 2 = 1 := by
  funext j
  simp only [thetaSignE6, Pi.pow_apply, Pi.one_apply, ← zpow_natCast, ← zpow_mul]
  rw [mul_comm, zpow_mul, show ((-1 : Kˣ) ^ ((2 : ℕ) : ℤ)) = 1 by norm_num, one_zpow]

end Torus

section Lift


variable {K : Type} [Field K]

@[expose] def HypLift {Ω : Type} [Group Ω] (Γ : Ω →* MulAut ↥(adjointGroup .E6 K)) (ζ : Kˣ)
    (hζ : ζ ^ 3 = 1) (b : Ω) : Prop :=
  ∃ (M : Subgroup Ω) (t : Ω), IsElemAbelian 3 M ∧ Nat.card M = 3 ^ 6 ∧ M.map Γ = vHyp ζ hζ ∧
    (∀ m ∈ M, b * m = m * b) ∧ t ≠ 1 ∧ t ^ 2 = 1 ∧ (∀ m ∈ M, m * t = t * m) ∧ b * t = t * b

theorem actHom_coe_eq_conj {Ω : Type} [Group Ω] {S : Subgroup Ω} (hS : S.Normal) {X : Type}
    [Group X] {π : ↥S →* X} (hπ : Function.Surjective π) {Γ : Ω →* MulAut X}
    (hΓ : ∀ (b : Ω) (g : ↥S), Γ b (π g) = π ⟨b * g * b⁻¹, hS.conj_mem _ g.2 b⟩) (s : ↥S) :
    Γ s = MulAut.conj (π s) := by
  refine MulEquiv.ext fun y => ?_
  obtain ⟨g, rfl⟩ := hπ y
  rw [hΓ, MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul]
  rfl

theorem exists_cartanMulE6_eq {w : Fin Tag.E6.rank → ZMod 3}
    (hw : w ∈ CFSG.StandardType.NoOffRest.hypE6) : ∃ z, cartanMulE6 z = w := by
  refine ⟨fun j => ∑ m, cartanSection j m * w m, ?_⟩
  funext l
  exact cartan_mul_cartanSection w hw l

theorem hypLift_of_injective {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω} [Finite K]
    (hK2 : ringChar K ≠ 2) (hS : S.Normal) (hcore : GLAPPrimeCore 3 ↥S = ⊥) (hB : IsElemAbelian 3 B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup 3 S) = 3) {π : ↥S →* ↥(adjointGroup .E6 K)}
    (hπ : Function.Surjective π) (hπi : Function.Injective π)
    {Γ : Ω →* MulAut ↥(adjointGroup .E6 K)}
    (hΓ : ∀ (b : Ω) (g : ↥S), Γ b (π g) = π ⟨b * g * b⁻¹, hS.conj_mem _ g.2 b⟩)
    (hΓker : Γ.ker = centModSubgroup 3 S) {ζ : Kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {σ : K ≃+* K} (hσζ : σ (ζ : K) = ζ) {b : Ω} (hbB : b ∈ B)
    (hb : Γ b = entrywiseAdjointAut .E6 σ) : HypLift Γ ζ hζ b := by
  classical
  haveI : Finite ↥(adjointGroup .E6 K) := generated_group_finite .E6 K
  set B₀ := B ⊓ centModSubgroup 3 S with hB₀
  set H := (hypTorusHom (K := K) ζ hζ).range with hH
  set L := H.comap π with hL
  set Lφ := L.map S.subtype with hLφ
  have hB₀S : ∀ c ∈ B₀, ∀ x ∈ S, c * x = x * c := fun c hc x hx =>
    CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen.comm_of_mem_centMod hS hcore hc.2 hx
  have hZ : Subgroup.center ↥S = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    apply hπi
    rw [map_one]
    have h1 : π z ∈ Subgroup.center ↥(adjointGroup .E6 K) := Subgroup.mem_center_iff.2 fun a => by
      obtain ⟨g, rfl⟩ := hπ a
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz g]
    rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at h1
    exact h1
  have hLmap : L.map π = H := Subgroup.map_comap_eq_self_of_surjective hπ H
  have hLc : Nat.card L = 3 ^ 5 := by
    rw [← Subgroup.card_map_of_injective hπi, hLmap, hH, card_range_hypTorusHom hζo hζ]
  have hLel : IsElemAbelian 3 Lφ := by
    refine CFSG.SectionRank.isElemAbelian_map ?_ S.subtype
    refine ⟨⟨⟨fun x y => Subtype.ext (hπi ?_)⟩⟩, fun x hx => hπi ?_⟩
    · change π ((x : ↥S) * y) = π (y * x)
      rw [map_mul, map_mul]
      exact (isElemAbelian_range_hypTorusHom ζ hζ).comm x.2 y.2
    · rw [map_pow, map_one]
      exact (isElemAbelian_range_hypTorusHom ζ hζ).2 _ hx
  have hcomm : ∀ c ∈ B₀, ∀ x ∈ Lφ, c * x = x * c := by
    rintro c hc _ ⟨s, -, rfl⟩
    exact hB₀S c hc s s.2
  have hinf : B₀ ⊓ Lφ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx₀, ⟨s, -, rfl⟩⟩
    rw [Subgroup.mem_bot]
    exact CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen.eq_one_of_mem_centMod hS hcore hZ s.2 hx₀.2
  have hΓS := actHom_coe_eq_conj hS hπ hΓ
  have hB₀ker : B₀ ≤ Γ.ker := fun c hc => by rw [hΓker]; exact hc.2
  obtain ⟨s₀, hs₀⟩ := hπ (thetaInv K)
  have hs₀2 : s₀ ^ 2 = 1 := hπi (by rw [map_pow, hs₀, thetaInv_sq, map_one])
  have hconj : ∀ s : ↥S, π s = π (s₀) → s = s₀ := fun s h => hπi h
  refine ⟨B₀ ⊔ Lφ, (s₀ : Ω), (hB.mono inf_le_left).sup_of_commute hLel hcomm, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [CFSG.CGT.T75P.card_sup_of_commute hcomm hinf, hBC, hLφ,
      Subgroup.card_map_of_injective S.subtype_injective, hLc]
    norm_num
  · rw [Subgroup.map_sup]
    have h1 : B₀.map Γ = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨c, hc, rfl⟩
      exact (MonoidHom.mem_ker.1 (hB₀ker hc)).symm ▸ one_mem _
    rw [h1, bot_sup_eq]
    apply le_antisymm
    · rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      obtain ⟨x, hx⟩ := hs
      refine ⟨x, ?_⟩
      rw [Subgroup.coe_subtype, hΓS, ← hx, conj_hypTorusHom]
      rfl
    · rintro _ ⟨x, rfl⟩
      obtain ⟨s, hs⟩ := hπ (hypTorusHom ζ hζ x)
      refine ⟨s, ⟨s, ⟨x, hs.symm⟩, rfl⟩, ?_⟩
      rw [hΓS, hs, conj_hypTorusHom]
      rfl
  · intro m hm
    have hle : B₀ ⊔ Lφ ≤ Subgroup.centralizer ({b} : Set Ω) := by
      refine sup_le (fun c hc => Subgroup.mem_centralizer_singleton_iff.2 (hB.comm hc.1 hbB)) ?_
      rintro _ ⟨s, ⟨x, hx⟩, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := hΓ b s
      rw [hb, ← hx, entrywiseAdjointAut_hypTorusHom hζ hσζ, hx] at h1
      have h2 : (⟨b * s * b⁻¹, hS.conj_mem _ s.2 b⟩ : ↥S) = s := hπi h1.symm
      have h3 : b * (s : Ω) * b⁻¹ = s := congrArg Subtype.val h2
      calc (s : Ω) * b = b * (s : Ω) * b⁻¹ * b := by rw [h3]
        _ = b * s := by group
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hm)).symm
  · intro h
    apply thetaInv_ne_one (K := K) hK2
    rw [← hs₀, show s₀ = 1 from Subtype.ext h, map_one]
  · rw [← Subgroup.coe_pow, hs₀2, Subgroup.coe_one]
  · intro m hm
    have hle : B₀ ⊔ Lφ ≤ Subgroup.centralizer ({(s₀ : Ω)} : Set Ω) := by
      refine sup_le (fun c hc => Subgroup.mem_centralizer_singleton_iff.2 (hB₀S c hc _ s₀.2)) ?_
      rintro _ ⟨s, ⟨x, hx⟩, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : π (s * s₀) = π (s₀ * s) := by
        rw [map_mul, map_mul, ← hx, hs₀, hypTorusHom_mul_thetaInv]
      exact congrArg Subtype.val (hπi h1)
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hm)
  · have h1 := hΓ b s₀
    rw [hb, hs₀, entrywiseAdjointAut_thetaInv, ← hs₀] at h1
    have h2 : (⟨b * s₀ * b⁻¹, hS.conj_mem _ s₀.2 b⟩ : ↥S) = s₀ := hπi h1.symm
    have h3 : b * (s₀ : Ω) * b⁻¹ = s₀ := congrArg Subtype.val h2
    calc b * (s₀ : Ω) = b * (s₀ : Ω) * b⁻¹ * b := by group
      _ = s₀ * b := by rw [h3]

theorem hypLift_of_not_injective {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω} [Finite K]
    (hK2 : ringChar K ≠ 2) (h3 : 3 ∣ Nat.card K - 1) (hS : S.Normal) (hperf : ⁅S, S⁆ = S)
    (hcore : GLAPPrimeCore 3 ↥S = ⊥) {π : ↥S →* ↥(adjointGroup .E6 K)}
    (hπ : Function.Surjective π) (hπZ : π.ker ≤ Subgroup.center ↥S)
    (hπi : ¬ Function.Injective π) {Γ : Ω →* MulAut ↥(adjointGroup .E6 K)}
    (hΓ : ∀ (b : Ω) (g : ↥S), Γ b (π g) = π ⟨b * g * b⁻¹, hS.conj_mem _ g.2 b⟩)
    {ζ : Kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) {σ : K ≃+* K} (hσζ : σ (ζ : K) = ζ) {b : Ω}
    (hb : Γ b = entrywiseAdjointAut .E6 σ) : HypLift Γ ζ hζ b := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite ↥(adjointGroup .E6 K) := generated_group_finite .E6 K
  haveI : Finite ↥(e6Data_valid.minGroup K) := by
    have : Finite (Module.End K (Fin e6Data.d →₀ K)) := Module.finite_of_finite K
    infer_instance
  haveI : S.Normal := hS
  have hK5 : 5 ≤ Nat.card K := five_le_card_of_dvd_sq_sub_one hK2 Nat.prime_three (by norm_num)
    (h3.trans (Nat.sub_one_dvd_pow_sub_one _ 2))
  have hperf' : Group.IsPerfect ↥S :=
    ⟨CFSG.LocalAnalysis.GLTheoremA.S267.perfect_of_commutator_self_eq hperf⟩
  have hkerE : (e6Isogeny K).ker = Subgroup.center ↥(e6Data_valid.minGroup K) :=
    le_antisymm (CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
      (CFSG.LieType.CurtisTits.isQuasisimple_e6 K) (e6Isogeny_ne_one K))
      (center_le_ker_of_surjective (e6Isogeny_surjective K) center_adjointGroup_eq_bot)
  have hkerEc : Nat.card (e6Isogeny K).ker = 3 := by
    rw [hkerE, (card_center_e6 K).1]
    exact Nat.gcd_eq_left h3
  have hker3 : 3 ≤ Nat.card π.ker := by
    have hne : π.ker ≠ ⊥ := fun h => hπi ((MonoidHom.ker_eq_bot_iff π).1 h)
    have hp3 : IsPGroup 3 π.ker :=
      (CFSG.LocalAnalysis.GLTheoremB.MovingAround.SchurFacts.isPGroup_center_of_glaPPrimeCore_eq_bot
        Nat.prime_three hcore).to_le hπZ
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hp3
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact hne (Subgroup.eq_bot_of_card_eq _ hk)
    rw [hk]
    calc 3 = 3 ^ 1 := (pow_one 3).symm
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.2 hk0)
  obtain ⟨f, hf⟩ := exists_mulEquiv_comp_eq_of_central_cover (e6Isogeny K) π
    (e6Isogeny_surjective K) hπ hπZ hperf'
    (fun E _ _ π' hπ' hc => e6_exists_section_of_central hK5 hπ' hc) (by rw [hkerEc]; exact hker3)
  set β : ↥S →* ↥S := (MulAut.conjNormal b).toMonoidHom with hβ
  have hβapp : ∀ g : ↥S, (β g : Ω) = b * g * b⁻¹ := fun g => by
    rw [hβ, MulEquiv.coe_toMonoidHom, MulAut.conjNormal_apply]
  set β' : ↥(e6Data_valid.minGroup K) →* ↥(e6Data_valid.minGroup K) :=
    f.symm.toMonoidHom.comp (β.comp f.toMonoidHom) with hβ'
  have hβ'eq : β' = minBC e6Data_valid σ.toRingHom := by
    refine eq_of_comp_eq_of_isPerfect (CFSG.LieType.CurtisTits.isPerfect_e6 K) (e6Isogeny K)
      hkerE.le
      (MonoidHom.ext fun g => ?_)
    simp only [MonoidHom.comp_apply]
    rw [e6Isogeny_minBC_eq, ← hf (β' g), hβ']
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    have e1 : β (f g) = ⟨b * (f g) * b⁻¹, hS.conj_mem _ (f g).2 b⟩ := Subtype.ext (hβapp (f g))
    rw [e1, ← hΓ, hb, hf]
  have hfix : ∀ u : Fin Tag.E6.rank → Kˣ, (∀ i, σ ((u i : Kˣ) : K) = u i) →
      b * (f (minTorus e6Data_valid K u) : Ω) = (f (minTorus e6Data_valid K u) : Ω) * b := by
    intro u hu
    have h1 : β' (minTorus e6Data_valid K u) = minTorus e6Data_valid K u := by
      rw [hβ'eq]
      exact minBC_minTorus_of_fix hu
    have h2 : β (f (minTorus e6Data_valid K u)) = f (minTorus e6Data_valid K u) := by
      have := congrArg f h1
      simpa [hβ'] using this
    have h3 := congrArg Subtype.val h2
    rw [hβapp] at h3
    calc b * (f (minTorus e6Data_valid K u) : Ω)
        = b * (f (minTorus e6Data_valid K u) : Ω) * b⁻¹ * b := by group
      _ = (f (minTorus e6Data_valid K u) : Ω) * b := by rw [h3]
  have hσζpow : ∀ (z : Multiplicative (Fin Tag.E6.rank → ZMod 3)) i,
      σ (((zetaHom ζ hζ z) i : Kˣ) : K) = (zetaHom ζ hζ z) i := by
    intro z i
    change σ (((ζ ^ (Multiplicative.toAdd z i).val : Kˣ) : K)) = ((ζ ^ (Multiplicative.toAdd z i).val : Kˣ) : K)
    rw [Units.val_pow_eq_pow_val, map_pow, hσζ]
  have hσθ : ∀ i, σ ((thetaSignE6 K i : Kˣ) : K) = thetaSignE6 K i := by
    intro i
    simp only [thetaSignE6, Units.val_zpow_eq_zpow_val, map_zpow₀, Units.val_neg, Units.val_one,
      map_neg, map_one]
  set T3 := (zetaTorus (K := K) ζ hζ).range with hT3
  set M : Subgroup Ω := (T3.map f.toMonoidHom).map S.subtype with hM
  set t : Ω := (f (minTorus e6Data_valid K (thetaSignE6 K)) : Ω) with ht
  have hT3el : IsElemAbelian 3 T3 := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨u, hu⟩ := x.2
      obtain ⟨v, hv⟩ := y.2
      change (x : ↥(e6Data_valid.minGroup K)) * y = y * x
      rw [← hu, ← hv, ← map_mul, ← map_mul, mul_comm]
    · rintro _ ⟨x, rfl⟩
      rw [← map_pow, pow_three_eq_one, map_one]
  refine ⟨M, t, CFSG.SectionRank.isElemAbelian_map (CFSG.SectionRank.isElemAbelian_map hT3el _) _,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hM, Subgroup.card_map_of_injective S.subtype_injective,
      Subgroup.card_map_of_injective f.injective, hT3, card_range_of_injective' (zetaTorus_injective hζo hζ),
      card_multiplicative_fun]
    rfl
  · have hΓS := actHom_coe_eq_conj hS hπ hΓ
    apply le_antisymm
    · rintro _ ⟨_, ⟨_, ⟨_, ⟨z, rfl⟩, rfl⟩, rfl⟩, rfl⟩
      refine ⟨Multiplicative.ofAdd ⟨_, cartanMulE6_mem_hypE6 (Multiplicative.toAdd z)⟩, ?_⟩
      change diag3 ζ hζ (hypIncl _) = Γ (f (zetaTorus ζ hζ z))
      rw [hΓS, hf, e6Isogeny_zetaTorus, conj_hypTorusHom]
    · rintro _ ⟨x, rfl⟩
      obtain ⟨z, hz⟩ := exists_cartanMulE6_eq (Multiplicative.toAdd x).2
      refine ⟨(f (zetaTorus ζ hζ (Multiplicative.ofAdd z)) : Ω),
        ⟨_, ⟨_, ⟨_, rfl⟩, rfl⟩, rfl⟩, ?_⟩
      rw [hΓS, hf, e6Isogeny_zetaTorus, conj_hypTorusHom]
      have hx : (Multiplicative.ofAdd ⟨cartanMulE6 (Multiplicative.toAdd (Multiplicative.ofAdd z)),
          cartanMulE6_mem_hypE6 _⟩ : Multiplicative CFSG.StandardType.NoOffRest.hypE6) = x := by
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        exact hz
      rw [hx]
      rfl
  · rintro _ ⟨_, ⟨_, ⟨z, rfl⟩, rfl⟩, rfl⟩
    exact hfix _ (hσζpow z)
  · intro h
    apply thetaInv_ne_one (K := K) hK2
    rw [← e6Isogeny_thetaSign, ← hf, show f (minTorus e6Data_valid K (thetaSignE6 K)) = 1 from
      Subtype.ext h, map_one]
  · rw [ht, ← Subgroup.coe_pow, ← map_pow, ← map_pow, thetaSignE6_sq, map_one, map_one,
      Subgroup.coe_one]
  · rintro _ ⟨_, ⟨_, ⟨z, rfl⟩, rfl⟩, rfl⟩
    have hc : f (minTorus e6Data_valid K (zetaHom ζ hζ z)) *
        f (minTorus e6Data_valid K (thetaSignE6 K)) =
          f (minTorus e6Data_valid K (thetaSignE6 K)) * f (minTorus e6Data_valid K (zetaHom ζ hζ z)) := by
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm]
    exact congrArg Subtype.val hc
  · exact hfix _ hσθ

end Lift

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.E6One

end
