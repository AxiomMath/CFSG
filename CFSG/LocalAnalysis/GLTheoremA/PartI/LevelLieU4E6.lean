module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU4E5
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU4E4
import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma49i

public section

namespace CFSG.LocalAnalysis.GLTheoremA.LevelLieU4E

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

theorem coprime_core3 {G : Type} [Group G] [Finite G] (X : Subgroup G) :
    Nat.Coprime 3 (Nat.card ↥(GLAPPrimeCore 3 ↥X)) := by
  have h := CFSG.HardMathSupport.Solomon.Coordinator.i183_coprime_card_glaPPrimeCoreOf
    Nat.prime_three X
  have hc : Nat.card ↥(GLAPPrimeCoreOf 3 X) = Nat.card ↥(GLAPPrimeCore 3 ↥X) := by
    unfold GLAPPrimeCoreOf
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ X.subtype_injective).toEquiv.symm
  rw [hc] at h
  exact h

theorem eq_of_contains_normal {G : Type} [Group G] [Finite G] {X I N : Subgroup G}
    (hI : GLAPComponent 3 X I) (hNX : N ≤ X) (hNn : ∀ g ∈ X, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (hNI : N ≤ I) (hsimp : IsSimpleGroup N) (hnc : ¬ IsMulCommutative N) (h3 : 3 ∣ Nat.card N) :
    I = N := by
  classical
  by_contra hne
  have hlt : N < I := lt_of_le_of_ne hNI (Ne.symm hne)
  obtain ⟨hIX, hIsub, hcomp, hmin⟩ := hI
  have hN'simple : IsSimpleGroup ↥(N.subgroupOf X) := (Subgroup.subgroupOfEquivOfLe hNX).isSimpleGroup
  have hN'card : Nat.card ↥(N.subgroupOf X) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv
  have hNPC : ∀ x : ↥X, x ∈ N.subgroupOf X → x ∈ GLAPPrimeCore 3 ↥X → x = 1 := by
    intro x hxN hxP
    have hsub : CFSG.Open.IsSubnormal ((N.subgroupOf X) ⊓ GLAPPrimeCore 3 ↥X) (N.subgroupOf X) := by
      apply CFSG.Open.IsSubnormal.step inf_le_left _ (CFSG.Open.IsSubnormal.refl _)
      rw [Subgroup.normal_subgroupOf_iff inf_le_left]
      intro h k hh hk
      exact ⟨(N.subgroupOf X).mul_mem ((N.subgroupOf X).mul_mem hk hh.1) ((N.subgroupOf X).inv_mem hk),
        Subgroup.Normal.conj_mem (GLAPPrimeCore.normal 3 ↥X) h hh.2 k⟩
    rcases CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hsub hN'simple with h | h
    · have hm : x ∈ (N.subgroupOf X) ⊓ GLAPPrimeCore 3 ↥X := ⟨hxN, hxP⟩
      rw [h] at hm
      exact Subgroup.mem_bot.1 hm
    · exfalso
      have hle : N.subgroupOf X ≤ GLAPPrimeCore 3 ↥X := by
        intro y hy
        have hm : y ∈ (N.subgroupOf X) ⊓ GLAPPrimeCore 3 ↥X := by
          rw [h]
          exact hy
        exact hm.2
      have h3' : 3 ∣ Nat.card ↥(GLAPPrimeCore 3 ↥X) :=
        (hN'card ▸ h3).trans (Subgroup.card_dvd_of_le hle)
      have := (coprime_core3 X).eq_one_of_dvd h3'
      norm_num at this
  set mk := QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) with hmk
  set A := (N.subgroupOf X).map mk with hA
  set Im := (I.subgroupOf X).map mk with hIm
  have hAIm : A ≤ Im :=
    Subgroup.map_mono (fun y hy => Subgroup.mem_subgroupOf.2 (hNI (Subgroup.mem_subgroupOf.1 hy)))
  have hImq : CFSG.Open.IsQuasisimple Im := hcomp.2.2
  have hAnorm : (A.subgroupOf Im).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hAIm]
    intro h k hh hk
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hk
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hh
    rw [← map_mul, ← map_inv, ← map_mul]
    refine Subgroup.mem_map_of_mem _ ?_
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := hNn x.1 x.2 n.1 hn
    simpa using this
  have hAsub : CFSG.Open.IsSubnormal A Im :=
    CFSG.Open.IsSubnormal.step hAIm hAnorm (CFSG.Open.IsSubnormal.refl Im)
  have hsubN : CFSG.Open.IsSubnormal N X :=
    CFSG.Open.IsSubnormal.step hNX (by rw [Subgroup.normal_subgroupOf_iff hNX]; exact fun h k hh hk => hNn k hk h hh) (CFSG.Open.IsSubnormal.refl X)
  rcases CFSG.Fischer.Classification.Recognition.IsSubnormal.eq_or_le_center hAsub hImq with h1 | h2
  · exact hmin N hlt hsubN h1
  ·
    have hcomm : ∀ n ∈ N, ∀ x ∈ I, n * x = x * n := by
      intro n hn x hx
      have hnX : n ∈ X := hNX hn
      have hxX : x ∈ X := hIX hx
      have hmemA : mk ⟨n, hnX⟩ ∈ A :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hn)
      obtain ⟨z, hz', hzz⟩ := Subgroup.mem_map.1 (h2 hmemA)
      have hyI : mk ⟨x, hxX⟩ ∈ Im := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hx)
      have hc := congrArg Subtype.val (Subgroup.mem_center_iff.1 hz' ⟨mk ⟨x, hxX⟩, hyI⟩)
      simp only [Subgroup.coe_mul] at hc
      have hzz' : (z : Im).1 = mk ⟨n, hnX⟩ := hzz
      rw [hzz'] at hc
      have hc2 : mk ⟨x, hxX⟩ * mk ⟨n, hnX⟩ = mk ⟨n, hnX⟩ * mk ⟨x, hxX⟩ := hc
      rw [← map_mul, ← map_mul] at hc2
      have hq := QuotientGroup.eq.1 hc2
      have hqN : (⟨x, hxX⟩ * ⟨n, hnX⟩ : ↥X)⁻¹ * (⟨n, hnX⟩ * ⟨x, hxX⟩) ∈ N.subgroupOf X := by
        rw [Subgroup.mem_subgroupOf]
        have := hNn x⁻¹ (X.inv_mem hxX) n hn
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv] at this ⊢
        have hm := N.mul_mem (N.inv_mem hn) this
        simpa [mul_assoc] using hm
      have h1' := hNPC _ hqN hq
      rw [inv_mul_eq_one] at h1'
      have := congrArg Subtype.val h1'
      simp only [Subgroup.coe_mul] at this
      exact this.symm
    apply hnc
    exact ⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ (hNI b.2))⟩⟩

open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48 (SU4 μ3)
open CFSG.LocalAnalysis.GLTheoremA.CatB.U48
open CFSG.RankThree.PartTwo.KFacts.KS21.U58 (K)
open CFSG.ClassicalInvolution.Phan (Su blockEmb blockEmb_injective)

@[expose] noncomputable def detA (ζ : K) (hζ : IsPrimitiveRoot ζ 3) :
    ↥(Subgroup.centralizer ({c022 ζ hζ} : Set SU4)) →* Kˣ where
  toFun x := Units.mk0 (blkA x).det (by
    exact (blkA_det_ne x.2))
  map_one' := by
    apply Units.ext
    simp [blkA_one]
  map_mul' x y := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_mk0, Subgroup.coe_mul]
    rw [blkA_mul x.2 y.2, Matrix.det_mul]

theorem KA_le_C (ζ : K) (hζ : IsPrimitiveRoot ζ 3) :
    KA ζ hζ ≤ Subgroup.centralizer ({c022 ζ hζ} : Set SU4) := fun _ hx => hx.1

theorem piA_surj {ζ : K} {hζ : IsPrimitiveRoot ζ 3} {w : SU4} (hw : w ∈ W0) :
    ∃ y : KA ζ hζ, piA ζ hζ y = w := by
  obtain ⟨a, rfl⟩ := hw
  have hK : blockEmb K 2 3 4 2 0 (by norm_num) a ∈ KA ζ hζ := W0_le_KA ⟨a, rfl⟩
  refine ⟨⟨_, hK⟩, ?_⟩
  have hθ : thetaA ζ hζ ⟨_, hK⟩ = a := by
    apply Subtype.ext
    apply Units.ext
    exact blkA_blockEmb a
  show blockEmb K 2 3 4 2 0 (by norm_num) (thetaA ζ hζ ⟨_, hK⟩) = _
  rw [hθ]

theorem piA_range (ζ : K) (hζ : IsPrimitiveRoot ζ 3) : (piA ζ hζ).range = W0 := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact piA_mem_W0 ζ hζ x
  · intro w hw
    obtain ⟨y, hy⟩ := piA_surj (ζ := ζ) (hζ := hζ) hw
    exact ⟨y, hy⟩

noncomputable def W1equivW0 : ↥W1 ≃* ↥W0 :=
  (MonoidHom.ofInjective (blockEmb_injective (K := K) (p := 2) (f := 3)
    (by norm_num : 2 + 2 ≤ 4))).symm.trans
    (MonoidHom.ofInjective (blockEmb_injective (K := K) (p := 2) (f := 3)
      (by norm_num : 0 + 2 ≤ 4)))

theorem not_isMulCommutative_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (hH : ¬ IsMulCommutative H) : ¬ IsMulCommutative G := by
  intro hG
  apply hH
  exact ⟨⟨fun a b => by
    have := hG.is_comm.comm (e.symm a) (e.symm b)
    have h2 := congrArg e this
    simpa using h2⟩⟩

theorem goodCent_c022 (ζ : K) (hζ : IsPrimitiveRoot ζ 3) : GoodCent (c022 ζ hζ) := by
  intro I hI
  have hIC : I ≤ Subgroup.centralizer ({c022 ζ hζ} : Set SU4) := hI.1
  have hperf : ⁅I.subgroupOf (Subgroup.centralizer ({c022 ζ hζ} : Set SU4)),
      I.subgroupOf (Subgroup.centralizer ({c022 ζ hζ} : Set SU4))⁆ =
      I.subgroupOf (Subgroup.centralizer ({c022 ζ hζ} : Set SU4)) := by
    apply Subgroup.map_injective
      (f := (Subgroup.centralizer ({c022 ζ hζ} : Set SU4)).subtype)
      (Subgroup.centralizer ({c022 ζ hζ} : Set SU4)).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hIC]
    exact glaPComponent_perfect hI
  haveI : IsSimpleGroup ↥W0 := isSimpleGroup_W0
  have hIKA : I ≤ KA ζ hζ := by
    intro x hx
    have hmem : (⟨x, hIC hx⟩ : ↥(Subgroup.centralizer ({c022 ζ hζ} : Set SU4))) ∈
        I.subgroupOf (Subgroup.centralizer ({c022 ζ hζ} : Set SU4)) :=
      Subgroup.mem_subgroupOf.2 hx
    have hk := MonoidHom.mem_ker.1 (le_ker_of_perfect (detA ζ hζ) hperf hmem)
    exact ⟨hIC hx, congrArg Units.val hk⟩
  by_cases hW : ∀ x ∈ I, x ∈ W1 → x = 1
  ·
    have hIKA' : CFSG.Open.IsSubnormal I (KA ζ hζ) := by
      have h := hI.2.1.inf_of_le (KA_le_C ζ hζ)
      rwa [inf_eq_left.2 hIKA] at h
    let ι : ↥I →* ↥(KA ζ hζ) := Subgroup.inclusion hIKA
    let ρ : ↥I →* SU4 := (piA ζ hζ).comp ι
    have hρinj : Function.Injective ρ := by
      rw [injective_iff_map_eq_one]
      intro x hx
      exact Subtype.ext (hW x.1 x.2 (piA_ker (ι x) hx))
    have hr : ρ.range = (I.subgroupOf (KA ζ hζ)).map (piA ζ hζ) := by
      ext w
      constructor
      · rintro ⟨x, rfl⟩
        exact Subgroup.mem_map.2 ⟨ι x, Subgroup.mem_subgroupOf.2 x.2, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨y.1, Subgroup.mem_subgroupOf.1 hy⟩, rfl⟩
    have hsubI : CFSG.Open.IsSubnormal ρ.range W0 := by
      have h1 := CFSG.Open.IsSubnormal.map (piA ζ hζ)
        (CFSG.Open.IsSubnormal.of_mathlib
          (CFSG.Assembly.isSubnormal_iff_open.2 hIKA').subgroupOf)
      rw [← MonoidHom.range_eq_map, piA_range] at h1
      rw [hr]
      exact h1
    rcases CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hsubI isSimpleGroup_W0 with h | h
    · exfalso
      apply glaPComponent_ne_bot' hI
      rw [eq_bot_iff]
      intro x hx
      have hmem : ρ ⟨x, hx⟩ ∈ ρ.range := ⟨_, rfl⟩
      rw [h] at hmem
      have h1 : ρ ⟨x, hx⟩ = ρ 1 := by rw [map_one]; exact Subgroup.mem_bot.1 hmem
      have h2 := congrArg Subtype.val (hρinj h1)
      rw [Subgroup.mem_bot]
      exact h2
    · let e : ↥I ≃* ↥W0 := (MonoidHom.ofInjective hρinj).trans (MulEquiv.subgroupCongr h)
      haveI : IsSimpleGroup ↥I := e.isSimpleGroup
      have hnc : ¬ IsMulCommutative ↥I := not_isMulCommutative_of_mulEquiv e not_isMulCommutative_W0
      have h3 : 3 ∣ Nat.card ↥I := by
        rw [Nat.card_congr e.toEquiv]
        exact three_dvd_W0
      obtain ⟨f⟩ := pSimple_equiv_of_simple I hnc h3
      rw [CFSG.LocalAnalysis.GLTheoremA.kLevel_congr 3 f,
        CFSG.LocalAnalysis.GLTheoremA.kLevel_congr 3 e]
      exact kLevel_W0_le_two
  ·
    push_neg at hW
    obtain ⟨x0, hx0I, hx0W, hx0ne⟩ := hW
    haveI : IsSimpleGroup ↥W1 := W1equivW0.isSimpleGroup
    have hW1sub := hI.2.1.inf_of_le (W1_le_centralizer_c022 ζ hζ)
    have hW1I : W1 ≤ I := by
      rcases CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hW1sub inferInstance with h' | h'
      · exfalso
        have hm : x0 ∈ I ⊓ W1 := ⟨hx0I, hx0W⟩
        rw [h'] at hm
        exact hx0ne (Subgroup.mem_bot.1 hm)
      · intro y hy
        have hm : y ∈ I ⊓ W1 := by
          rw [h']
          exact hy
        exact hm.1
    have hnc1 : ¬ IsMulCommutative ↥W1 :=
      not_isMulCommutative_of_mulEquiv W1equivW0 not_isMulCommutative_W0
    have h31 : 3 ∣ Nat.card ↥W1 := by
      rw [Nat.card_congr W1equivW0.toEquiv]
      exact three_dvd_W0
    have hIW1 : I = W1 := eq_of_contains_normal hI (W1_le_centralizer_c022 ζ hζ)
      (fun g hg n hn => W1_normal_c022 hg hn) hW1I inferInstance hnc1 h31
    rw [hIW1]
    obtain ⟨f⟩ := pSimple_equiv_of_simple W1 hnc1 h31
    rw [CFSG.LocalAnalysis.GLTheoremA.kLevel_congr 3 f,
      CFSG.LocalAnalysis.GLTheoremA.kLevel_congr 3 W1equivW0]
    exact kLevel_W0_le_two

theorem kdLieRowU4Eight_holds : KDLieRowU4Eight :=
  kdLieRowU4Eight_of_c022 goodCent_c022

end CFSG.LocalAnalysis.GLTheoremA.LevelLieU4E
