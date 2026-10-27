module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs141d
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympFieldExport
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympFieldExport
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympAssembly
import all CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.SympInner
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthInnerExport
import all CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.OrthInner
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthFieldExport
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthAssembly
import CFSG.RankThree.PartOne.S11d.OrthSubfieldDickson
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4FieldInner
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Duality
import CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.Bridge
import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4AmbientForm
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofEvenDesc
import CFSG.RankThree.PartTwo.Sec16.KS16ProofMeet

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141d

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141c
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup PerfectInLayer)

section TwoTame

@[expose] def TwoTame (G : Type*) [Group G] : Prop :=
  Group.IsSolvable G ∨ Nat.card G < 20160 ∨
    ∀ g : G, IsPGroup 2 ↥(Subgroup.zpowers g) → g ∈ commutator G

theorem twoTame_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (h : TwoTame H) : TwoTame G := by
  rcases h with hs | hc | h2
  · left
    haveI := hs
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  · right
    left
    rwa [Nat.card_congr e.toEquiv]
  · right
    right
    intro g hg
    have hg' : IsPGroup 2 ↥(Subgroup.zpowers (e g)) := by
      have h1 := hg.map e.toMonoidHom
      rwa [MonoidHom.map_zpowers] at h1
    have hmap : (commutator G).map e.toMonoidHom = commutator H := by
      rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        MonoidHom.range_eq_top.2 e.surjective]
    have h1 := h2 (e g) hg'
    rw [← hmap] at h1
    obtain ⟨g', hg'', he⟩ := h1
    rwa [← e.injective he]

theorem twoTame_of_perfect {G : Type*} [Group G] (h : commutator G = ⊤) : TwoTame G :=
  Or.inr (Or.inr fun g _ => h ▸ Subgroup.mem_top g)

theorem twoTame_of_comm {G : Type*} [Group G] (h : ∀ a b : G, a * b = b * a) : TwoTame G :=
  Or.inl (Group.isSolvable_of_comm h)

theorem le_commutator_of_perfect {G : Type*} [Group G] {H : Subgroup G} (hH : ⁅H, H⁆ = H) :
    H ≤ commutator G := by
  rw [← hH, _root_.commutator_def]
  exact Subgroup.commutator_mono le_top le_top

theorem twoTame_generalLinearGroup {E W : Type} [Field E] [CharP E 2] [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] (h4 : 3 ≤ Module.finrank E W ∨ ∃ s : Finset E, s.card = 4) :
    TwoTame (LinearMap.GeneralLinearGroup E W) := by
  by_cases hm : 2 ≤ Module.finrank E W
  · right
    right
    have hq := CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_ker_det hm h4
    intro g hg
    obtain ⟨m, hm'⟩ := exists_pow_eq_one_of_isPGroup hg
    have hgk : g ∈ (Units.map (LinearMap.det : Module.End E W →* E)).ker := by
      rw [MonoidHom.mem_ker]
      exact Units.ext (det_eq_one_of_pow_two hm')
    exact le_commutator_of_perfect (Subgroup.isPerfect_iff.1 hq.1) hgk
  · refine twoTame_of_comm fun a b => Units.ext ?_
    rw [Units.val_mul, Units.val_mul]
    exact (CFSG.RankThree.PartOne.KCUnitary.End_commute_of_finrank_le_one (by omega) _ _).eq

open CFSG.LocalAnalysis.ComponentInitial in
theorem twoTame_sesqUnitaryGroup {f' : ℕ} {E : Type} [Field E] (hE : UnitaryFieldData 2 f' E) {W : Type}
    [AddCommGroup W] [Module E W] [FiniteDimensional E W] {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E} (hHf : Hf.IsSymm)
    (hHfl : Hf.SeparatingLeft) : TwoTame ↥(sesqUnitaryGroup Hf) := by
  haveI : CharP E 2 := hE.charP
  have hq2 : 2 ≤ 2 ^ f' := by
    have := Nat.one_lt_pow (by have := hE.one_le; omega : f' ≠ 0) (by norm_num : 1 < 2)
    omega
  by_cases hm : 2 ≤ Module.finrank E W
  · by_cases hq : (Module.finrank E W = 2 → 4 ≤ 2 ^ f') ∧ (Module.finrank E W = 3 → 3 ≤ 2 ^ f')
    · right
      right
      have hSU := CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_sesqSpecialUnitaryGroup_of_two_le hE hHf hHfl hm hq
      have hSU' : CFSG.IsQuasisimple ↥((sesqSpecialUnitaryGroup Hf).subgroupOf (sesqUnitaryGroup Hf)) :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv
          (Subgroup.subgroupOfEquivOfLe (sesqSpecialUnitaryGroup_le Hf)).symm hSU
      intro g hg
      obtain ⟨m, hm'⟩ := exists_pow_eq_one_of_isPGroup hg
      have hm'' : (g : LinearMap.GeneralLinearGroup E W) ^ (2 ^ m) = 1 := by
        simpa using congrArg Subtype.val hm'
      have hgS : g ∈ (sesqSpecialUnitaryGroup Hf).subgroupOf (sesqUnitaryGroup Hf) :=
        Subgroup.mem_subgroupOf.2 (mem_sesqSpecialUnitaryGroup.2 ⟨g.2, det_eq_one_of_pow_two hm''⟩)
      exact le_commutator_of_perfect (Subgroup.isPerfect_iff.1 hSU'.1) hgS
    · right
      left
      haveI : Finite E := hE.finite
      obtain ⟨hcard, -, -, -, -, -⟩ := CFSG.LinearGroups.unitary_full_group_order hE hHf hHfl rfl
        (by omega : 1 ≤ Module.finrank E W)
      have hexc : (Module.finrank E W = 2 ∧ 2 ^ f' = 2) ∨ (Module.finrank E W = 3 ∧ 2 ^ f' = 2) := by
        have h2f : 2 ^ f' = 2 ∨ 4 ≤ 2 ^ f' := by
          rcases Nat.lt_or_ge f' 2 with hf | hf
          · left
            have : f' = 1 := by have := hE.one_le; omega
            subst this
            norm_num
          · right
            calc 4 = 2 ^ 2 := by norm_num
              _ ≤ 2 ^ f' := Nat.pow_le_pow_right (by norm_num) hf
        by_contra hn
        push Not at hn
        apply hq
        refine ⟨fun h2' => ?_, fun h3' => ?_⟩
        · rcases h2f with h | h
          · exact absurd h (hn.1 h2')
          · exact h
        · rcases h2f with h | h
          · exact absurd h (hn.2 h3')
          · omega
      rcases hexc with ⟨hm2, hQ⟩ | ⟨hm3, hQ⟩
      · rw [hm2, hQ] at hcard
        have e : ((2 : ℕ) : ℤ) ^ (2 * (2 - 1) / 2) *
            ∏ i ∈ Finset.Icc 1 2, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 18 := by decide +kernel
        have h18 : Nat.card ↥(sesqUnitaryGroup Hf) = 18 := by exact_mod_cast hcard.trans e
        rw [h18]
        norm_num
      · rw [hm3, hQ] at hcard
        have e : ((2 : ℕ) : ℤ) ^ (3 * (3 - 1) / 2) *
            ∏ i ∈ Finset.Icc 1 3, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 648 := by decide +kernel
        have h648 : Nat.card ↥(sesqUnitaryGroup Hf) = 648 := by exact_mod_cast hcard.trans e
        rw [h648]
        norm_num
  · refine twoTame_of_comm fun a b => Subtype.ext (Units.ext ?_)
    have := (CFSG.RankThree.PartOne.KCUnitary.End_commute_of_finrank_le_one (E := E) (W := W)
      (by omega) ((a : LinearMap.GeneralLinearGroup E W) : Module.End E W)
      ((b : LinearMap.GeneralLinearGroup E W) : Module.End E W)).eq
    simpa [Subgroup.coe_mul, Units.val_mul] using this

theorem twoTame_statedSp (s : ℕ) (K : Type) [Field K] [Finite K] : TwoTame ↥(StatedSp s K) := by
  have hcard := CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp (K := K) s
  by_cases hs : 1 ≤ s
  · by_cases hq : (Infinite K ∨ 4 ≤ Nat.card K) ∨ (Nat.card K = 3 ∧ 2 ≤ s) ∨ (Nat.card K = 2 ∧ 3 ≤ s)
    · exact twoTame_of_perfect
        (Group.isPerfect_def.mp (CFSG.LieType.Universal.Symplectic.isQuasisimple s K hs hq).1)
    · right
      left
      have hK2 : 2 ≤ Nat.card K := Nat.succ_le_of_lt Finite.one_lt_card
      have hK4 : Nat.card K < 4 := by
        by_contra h
        exact hq (Or.inl (Or.inr (by omega)))
      rcases (show Nat.card K = 2 ∨ Nat.card K = 3 by omega) with hK | hK
      · rcases (show s = 1 ∨ s = 2 by
          by_contra h
          exact hq (Or.inr (Or.inr ⟨hK, by omega⟩))) with rfl | rfl
        · rw [hcard, hK]
          decide
        · rw [hcard, hK]
          decide
      · have hs1 : s = 1 := by
          by_contra h
          exact hq (Or.inr (Or.inl ⟨hK, by omega⟩))
        subst hs1
        rw [hcard, hK]
        decide
  · right
    left
    obtain rfl : s = 0 := by omega
    rw [hcard]
    simp

end TwoTame

section OrbitFamily

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (not_isSolvable_of_isQuasisimple_commutator
  fixSubgroup_conj_eq_centralizer)

theorem structAt_conj_of_orbit_family {X T : Type} [Group X] [Group T] [Finite X] [Finite T] (π : X →* T)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center X) (hodd : Nat.Coprime 2 (Nat.card π.ker))
    (x : X) {ι : Type} [Finite ι] (A : ι → Subgroup X)
    (hc : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b)
    (hjoin : ⨆ i, A i = Subgroup.centralizer ({x} : Set X))
    (htame : ∀ i, CFSG.IsQuasisimple ↥⁅A i, A i⁆ ∨ Group.IsSolvable ↥(A i))
    (h2 : ∀ i, TwoTame ↥(A i))
    {J : Subgroup T} (hJ : GLAPComponent 3 (fixSubgroup (MulAut.conj (π x))) J) (hJ20 : 20160 ∣ Nat.card ↥J) :
    StructAt (MulAut.conj (π x)) J := by
  classical
  have hlay := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_conj_of_orbit_family π hπ hker
    x A hc hjoin htame
  have hJc := isComponentOf_of_perfectInLayer hlay hJ
  obtain ⟨i₀, hq₀, hJi⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.components_conj_of_orbit_family π hπ hker
    x A hc hjoin htame J hJc
  have hle₀ : ⁅A i₀, A i₀⁆ ≤ A i₀ := Subgroup.commutator_le_self _
  have h2i₀ : ∀ g ∈ A i₀, IsPGroup 2 ↥(Subgroup.zpowers g) → g ∈ ⁅A i₀, A i₀⁆ := by
    rcases h2 i₀ with hs | hcard | h2'
    · exact absurd hs (not_isSolvable_of_isQuasisimple_commutator hq₀)
    · exfalso
      have h1 : Nat.card ↥J ∣ Nat.card ↥⁅A i₀, A i₀⁆ := hJi ▸ Subgroup.card_map_dvd _ _
      have h3 : Nat.card ↥⁅A i₀, A i₀⁆ ≤ Nat.card ↥(A i₀) := Subgroup.card_le_of_le hle₀
      have h4 := Nat.le_of_dvd Nat.card_pos hJ20
      have h5 := Nat.le_of_dvd Nat.card_pos h1
      omega
    · intro g hg hg2
      obtain ⟨m, hm⟩ := exists_pow_eq_one_of_isPGroup hg2
      have h1 : (⟨g, hg⟩ : ↥(A i₀)) ∈ commutator ↥(A i₀) :=
        h2' _ (isPGroup_zpowers_of_pow (m := m) (Subtype.ext (by simpa using hm)))
      have h3 := Subgroup.mem_map_of_mem (A i₀).subtype h1
      rwa [Subgroup.map_subtype_commutator] at h3
  let B : ι → Subgroup X := fun i => if i = i₀ then ⁅A i₀, A i₀⁆ else A i
  have hBA : ∀ i, B i ≤ A i := by
    intro i
    by_cases hi : i = i₀
    · subst hi
      simp only [B, if_true]
      exact hle₀
    · simp only [B, if_neg hi, le_refl]
  refine structAt_of_family π hπ hker hodd (MulAut.conj x) (MulAut.conj (π x))
    (fun g => by simp [MulAut.conj_apply]) B (fun i j hij a ha b hb => hc i j hij a (hBA i ha) b (hBA j hb))
    ?_ hJc i₀ ?_
  · intro g hg hg2
    have hgC : g ∈ ⨆ i, A i := by
      rw [hjoin, ← fixSubgroup_conj_eq_centralizer]
      exact hg
    refine mem_iSup_of_two A B hc (fun i y hy hy2 => ?_) hgC hg2
    by_cases hi : i = i₀
    · subst hi
      simp only [B, if_true]
      exact h2i₀ y hy hy2
    · simp only [B, if_neg hi]
      exact hy
  · simp only [B, if_true]
    exact hJi

end OrbitFamily

section Symplectic

open Polynomial CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldAut)
open CFSG.RankThree.PartOne.KCSpIsotypic (exists_mulEquiv_sesqUnitaryGroup_statedSp)
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple (exists_finset_card_four_of_paired)

variable {r : ℕ} {K : Type} [Field K]

theorem twoTame_spSupported [Finite K] [CharP K 2] {f : ℕ} (hq : 2 ≤ 2 ^ f) {x : StatedSp r K}
    {a : StatedProj (StatedSp r K)} (blocks : SpPrimaryBlocks 2 f 3 x a)
    (O : reciprocalOrbits (spEnd x)) : TwoTame ↥(spSupported x (O : Set K[X])) := by
  obtain ⟨O, h, hh, rfl⟩ := O
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  by_cases hself : CFSG.RankThree.PartOne.KCOrthogonal.reciprocalPolynomial h = h
  · have hO : ({h, CFSG.RankThree.PartOne.KCOrthogonal.reciprocalPolynomial h} : Set K[X]) = {h} := by
      rw [hself, Set.pair_eq_singleton]
    show TwoTame ↥(spSupported x {h, CFSG.RankThree.PartOne.KCOrthogonal.reciprocalPolynomial h})
    rw [hO]
    by_cases h1 : h = X - 1
    · subst h1
      obtain ⟨φ, -⟩ := blocks.fixedFactor hh
      obtain ⟨s, -, ⟨e⟩⟩ := exists_mulEquiv_sesqUnitaryGroup_statedSp
        (B := (spForm r K).restrict (primaryComponent (spEnd x) (X - 1)))
        (fun v => spForm_isAlt (v : Fin r ⊕ Fin r → K)) blocks.fixed_nondegenerate
      exact twoTame_of_mulEquiv (φ.trans e) (twoTame_statedSp s K)
    · obtain ⟨d, -, -, σ, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, -, φ, -⟩ :=
        (blocks.selfDual ⟨h, hh⟩ h1 hself).exists_half
      exact twoTame_of_mulEquiv φ (twoTame_sesqUnitaryGroup hE hHf hHfl)
  · have hP := blocks.paired ⟨h, hh⟩ (fun e => hself e.symm)
    obtain ⟨φ, -, -⟩ := hP.factor
    haveI : CharP (AdjoinRoot ((⟨h, hh⟩ : primaryFactors (spEnd x)) : K[X])) 2 :=
      charP_of_injective_algebraMap
        (algebraMap K (AdjoinRoot ((⟨h, hh⟩ : primaryFactors (spEnd x)) : K[X]))).injective 2
    exact twoTame_of_mulEquiv φ
      (twoTame_generalLinearGroup (Or.inr (exists_finset_card_four_of_paired (by norm_num) hq hP)))

theorem structAt_conj_sp [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f) (hr : 1 ≤ r)
    (x : StatedSp r K) (hx : x ^ 3 = 1) (hx1 : proj r K x ≠ 1) {J : Subgroup (StatedProj (StatedSp r K))}
    (hJ : GLAPComponent 3 (fixSubgroup (MulAut.conj (proj r K x))) J) (hJ20 : 20160 ∣ Nat.card ↥J) :
    StructAt (MulAut.conj (proj r K x)) J := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  have ha : orderOf (proj r K x) = 3 := orderOf_eq_prime (by rw [← map_pow, hx, map_one]) hx1
  have hx1' : x ≠ 1 := fun h => hx1 (by rw [h, map_one])
  have hxp : orderOf x = 3 := orderOf_eq_prime hx hx1'
  have blocks := (symplectic_cross_prime_primary_centralizer_blocks Nat.prime_two hf hK Nat.prime_three
    (by norm_num) (by norm_num) hr _ ha).2 x rfl hxp
  have hpK : ((3 : ℕ) : K) ≠ 0 := three_ne_zero_of_charTwo
  have hsq := (altPrimaryData_spLin hpK hx).squarefree
  haveI : Finite (reciprocalOrbits (spEnd x)) := (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
  obtain ⟨hcomm, -, hjoin⟩ := blocks.directProduct
  have hq : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hker : (proj r K).ker ≤ Subgroup.center ↥(StatedSp r K) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.ker_proj]
    exact CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars_le_center
  have hodd : Nat.Coprime 2 (Nat.card (proj r K).ker) := by
    rw [CFSG.RankThree.PartOne.KCSpFull.ker_proj_eq_bot_of_even hr (by rw [hK]; exact dvd_pow_self 2 (by omega)),
      Subgroup.card_bot]
    exact Nat.coprime_one_right 2
  exact structAt_conj_of_orbit_family (proj r K)
    CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective hker hodd x
    (fun O : reciprocalOrbits (spEnd x) => spSupported x (O : Set K[X]))
    (fun i j hij a ha b hb => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) a ha b hb) hjoin
    (fun O => CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.quasisimple_or_solvable_spSupported
      (by norm_num) hq hsq blocks O)
    (fun O => twoTame_spSupported hq blocks O) hJ hJ20

open CFSG.ComponentClassification.UnbalancedCatalog (descentField)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (nonempty_fixSubgroup_equiv)

theorem structAt_fieldAut_sp (hr : 2 ≤ r) [Finite K] (σ : K ≃+* K) (hσ : orderOf σ = 3)
    {J : Subgroup (StatedProj (StatedSp r K))} (hJ : GLAPComponent 3 (fixSubgroup (fieldAut r K σ)) J)
    (hJ20 : 20160 ∣ Nat.card ↥J) : StructAt (fieldAut r K σ) J := by
  haveI : NeZero r := ⟨by omega⟩
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  obtain ⟨e⟩ := nonempty_fixSubgroup_equiv (r := r) (by decide : Odd 3) hσ3
  haveI : Finite ↥(descentField σ) := Subtype.finite
  by_cases hex : r = 2 ∧ Nat.card ↥(descentField σ) = 2
  · exfalso
    obtain ⟨rfl, hk2⟩ := hex
    have hC : Nat.card ↥(fixSubgroup (fieldAut 2 K σ)) ≤ 720 := by
      rw [Nat.card_congr e.toEquiv]
      calc Nat.card (StatedProj (StatedSp 2 ↥(descentField σ)))
          ≤ Nat.card ↥(StatedSp 2 ↥(descentField σ)) :=
            Nat.card_le_card_of_surjective _ CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective
        _ = 720 := by
            rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hk2]
            decide
    have h1 := Nat.le_of_dvd Nat.card_pos (hJ20.trans (Subgroup.card_dvd_of_le hJ.1))
    omega
  · obtain ⟨hs, hp⟩ := CFSG.RankThree.PartOne.KCSpComm.simple_perfect_statedProj (k := ↥(descentField σ)) hr hex
    have hperf : commutator (StatedProj (StatedSp r ↥(descentField σ))) = ⊤ := Group.isPerfect_def.mp hp
    have hnc : ∃ a b : StatedProj (StatedSp r ↥(descentField σ)), a * b ≠ b * a := by
      by_contra hab
      push Not at hab
      have hc : commutator (StatedProj (StatedSp r ↥(descentField σ))) = ⊥ := by
        rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro a _
        rw [Subgroup.mem_centralizer_iff]
        intro b _
        exact hab b a
      rw [hperf] at hc
      exact top_ne_bot hc
    have hq := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1
    have hqC : CFSG.IsQuasisimple ↥(fixSubgroup (fieldAut r K σ)) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq
    exact structAt_of_isQuasisimple_fixSubgroup ⟨hqC.1.1, hqC.2.1⟩ hJ.1

end Symplectic

section SymplecticCatalogue

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldAut spLinearAutGroup spSemilinearAutGroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

theorem lieIndexChar_eq_characteristic (d : TauCeti.LieTypeIndex) :
    CFSG.HardMathSupport.Solomon.Coordinator.lieIndexChar d = d.characteristic := by
  cases d <;> simp [CFSG.HardMathSupport.Solomon.Coordinator.lieIndexChar]

theorem congr_conj_eq {S G : Type} [Group S] [Group G] (e : S ≃* G) (s : S) :
    MulAut.congr e (MulAut.conj s) = MulAut.conj (e s) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem input14_1StructFor_symplectic :
    Input14_1StructFor fun d => (∃ r q, d = TauCeti.LieTypeIndex.B r q ∧ (q.p = 2 ∨ r = 2)) ∨
      ∃ r q, d = TauCeti.LieTypeIndex.C r q := by
  intro S _ _ hs hna idx hsp hchar he β hβ hβ1 J hJ hJt
  haveI := hs
  obtain ⟨e⟩ := he
  obtain ⟨r, f, ⟨-, hf, hr, -⟩, K, _, _, hK, ⟨e'⟩⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_statedClassicalModel_psp idx hsp e
  have hℓ2 : CFSG.HardMathSupport.Solomon.Coordinator.lieIndexChar idx.1 = 2 := by
    rw [lieIndexChar_eq_characteristic]
    exact hchar
  have hK2 : Nat.card K = 2 ^ f := by rw [hK, hℓ2]
  have hβ' : MulAut.congr e' β ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
  have hβ1' : MulAut.congr e' β ≠ 1 := fun h1 =>
    hβ1 ((MulAut.congr e').injective (h1.trans (map_one _).symm))
  have hJ20 : 20160 ∣ Nat.card ↥(J.map e'.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective e'.injective]
    exact card_dvd_of_isLThreeFour hJt
  have hJ' := glaPComponent_congr e' hJ
  refine structAt_of_congr e' ?_
  have hO := CFSG.RankThree.PartOne.KCSpComm.spOuter (K := K) Nat.prime_two hf hr hK2
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hodd : Odd (orderOf (MulAut.congr e' β)) :=
    (Nat.prime_three.odd_of_ne_two (by norm_num)).of_dvd_nat (orderOf_dvd_of_pow_eq_one hβ')
  have hE : MulAut.congr e' β ∈ spSemilinearAutGroup r K :=
    CFSG.RankThree.PartOne.KCSpComm.mem_of_odd_orderOf_of_index_dvd_two _ hO.index_dvd hodd
  by_cases hD : MulAut.congr e' β ∈ spLinearAutGroup r K
  ·
    have : (inner (StatedProj (StatedSp r K))).Normal := inner_normal _
    have hrel : (inner (StatedProj (StatedSp r K))).relIndex (spLinearAutGroup r K) ∣ 2 :=
      hO.relIndex_dvd.trans (Nat.gcd_dvd_left 2 _)
    obtain ⟨t, ht⟩ := CFSG.RankThree.PartOne.KCSpComm.mem_of_pow_eq_one_of_relIndex_dvd_two hrel
      Nat.prime_three (by norm_num) hD hβ'
    have hβs : β = MulAut.conj (e'.symm t) := by
      apply (MulAut.congr e').injective
      rw [← ht, congr_conj_eq, MulEquiv.apply_symm_apply]
    have hs3 : (e'.symm t) ^ 3 = 1 := by
      have hc : (e'.symm t) ^ 3 ∈ Subgroup.center S := by
        rw [Subgroup.mem_center_iff]
        intro g
        have h1 := congrArg (fun φ : MulAut S => φ g)
          (show MulAut.conj ((e'.symm t) ^ 3) = 1 by rw [map_pow, ← hβs]; exact hβ)
        simp only [MulAut.conj_apply, MulAut.one_apply] at h1
        calc g * (e'.symm t) ^ 3
            = (e'.symm t) ^ 3 * g * ((e'.symm t) ^ 3)⁻¹ * (e'.symm t) ^ 3 := by rw [h1]
          _ = (e'.symm t) ^ 3 * g := by group
      rw [CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_center_eq_bot hna, Subgroup.mem_bot] at hc
      exact hc
    have ht3 : t ^ 3 = 1 := by
      have := congrArg e' hs3
      rwa [map_pow, MulEquiv.apply_symm_apply, map_one] at this
    obtain ⟨x, hx, hx3⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_proj_eq_pow_eq_one_sp
      (by omega) Nat.prime_three (by norm_num) ht3
    have hx1 : proj r K x ≠ 1 := by
      rw [hx]
      intro h1
      apply hβ1'
      rw [← ht, h1, map_one]
    rw [← ht, ← hx] at hJ' ⊢
    exact structAt_conj_sp hK2 hf (by omega) x hx3 hx1 hJ' hJ20
  ·
    have hord : orderOf (MulAut.congr e' β) = 3 := orderOf_eq_prime hβ' hβ1'
    obtain ⟨-, σ, hσ, h, -, hβeq⟩ := hO.descent 3 Nat.prime_three _ hE hD hord
    have hc : MulAut.congr (h⁻¹ : MulAut (StatedProj (StatedSp r K))) (MulAut.congr e' β) =
        fieldAut r K σ := by
      have e1 : MulAut.congr (h⁻¹ : MulAut (StatedProj (StatedSp r K))) (MulAut.congr e' β) =
          h⁻¹ * MulAut.congr e' β * h⁻¹⁻¹ := by
        ext y
        rfl
      rw [e1, hβeq]
      group
    refine structAt_of_congr (h⁻¹ : MulAut (StatedProj (StatedSp r K))) ?_
    have hJ'' := glaPComponent_congr (h⁻¹ : MulAut (StatedProj (StatedSp r K))) hJ'
    have hJ20' : 20160 ∣ Nat.card ↥((J.map e'.toMonoidHom).map
        (h⁻¹ : MulAut (StatedProj (StatedSp r K))).toMonoidHom) := by
      rw [Subgroup.card_map_of_injective (h⁻¹ : MulAut (StatedProj (StatedSp r K))).injective]
      exact hJ20
    rw [hc] at hJ'' ⊢
    exact structAt_fieldAut_sp hr σ hσ hJ'' hJ20'

end SymplecticCatalogue

section OmegaDerived

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.RankThree.Classical2
open CFSG.RankThree.PartOne.KCOrthogonal (SmallFixedException exists_threeSingular_of_le)
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit (determinant_isometry_exhaustion rho tau
  specialImage commonDeterminant)

theorem index_le_two_of_forall {G : Type*} [Group G] {H : Subgroup G} [H.Normal] (t : G)
    (h : ∀ g : G, g ∈ H ∨ g * t⁻¹ ∈ H) : H.index ≤ 2 := by
  classical
  have hsurj : Function.Surjective
      (fun b : Bool => if b then (QuotientGroup.mk t : G ⧸ H) else (QuotientGroup.mk 1 : G ⧸ H)) := by
    intro c
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    rcases h g with hg | hg
    · refine ⟨false, ?_⟩
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact QuotientGroup.eq.2 (by simpa using hg)
    · refine ⟨true, ?_⟩
      simp only [↓reduceIte]
      refine QuotientGroup.eq.2 ?_
      have := ‹H.Normal›.conj_mem _ hg t⁻¹
      simpa [mul_assoc] using this
  rw [Subgroup.index]
  calc Nat.card (G ⧸ H) ≤ Nat.card Bool := Nat.card_le_card_of_surjective _ hsurj
    _ = 2 := by simp

theorem exists_sq_eq_units {K : Type} [Field K] [Finite K] [CharP K 2] (d : Kˣ) : ∃ c : Kˣ, c ^ 2 = d := by
  obtain ⟨c₀, hc₀⟩ := Finite.surjective_of_injective (frobenius_inj K 2) (d : K)
  have hc₀' : c₀ ^ 2 = (d : K) := hc₀
  have hne : c₀ ≠ 0 := by
    rintro rfl
    exact d.ne_zero (by rw [← hc₀']; simp)
  refine ⟨Units.mk0 c₀ hne, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, Units.val_mk0, hc₀']

theorem omegaGroup_le_orthDerived_of_listed {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type*}
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] (Q : QuadraticForm K W)
    (hQ : (polarBilin Q).Nondegenerate) (h3 : 3 ≤ finrank K W) (hne : ¬ SmallFixedException Q) :
    omegaGroup Q hQ ≤ orthDerived Q := by
  classical
  by_cases hT : ∃ T : Submodule K W, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0
  · exact CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQ hT
  have : Finite W := Module.finite_of_finite K
  have : Finite (W ≃ₗ[K] W) := Finite.of_injective (fun e : W ≃ₗ[K] W => (e : W → W))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hsub : (orthDerived Q).subgroupOf (TauCeti.QuadraticMap.orthogonalGroup Q) =
      commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := by
    rw [orthDerived, ← Subgroup.map_subtype_commutator]
    exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
  have hidx : (orthDerived Q).relIndex (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ 2 := by
    obtain ⟨⟨n, hn⟩, -, hnf, -⟩ :=
      CFSG.ComponentClassification.UnbalancedCatalog.finite_even_regular_quadratic_normal_forms Q hQ
    by_cases hS : ∃ U : Submodule K W, finrank K U = n ∧ ∀ u ∈ U, Q u = 0
    ·
      obtain ⟨U, hUn, hUQ⟩ := hS
      have hn2 : n = 2 := by
        by_contra hne2
        exact hT (exists_threeSingular_of_le Q hUQ (by omega))
      subst hn2
      have hK2 : Nat.card K ≠ 2 := fun h => hne (Or.inr ⟨⟨by omega, U, hUn, hUQ⟩, Or.inl h⟩)
      have hK3 : Nat.card K ≠ 3 := by
        intro h
        haveI : Fintype K := Fintype.ofFinite K
        have h2 := FiniteField.cast_card_eq_zero K
        rw [Fintype.card_eq_nat_card, h] at h2
        have h3' : ((3 : ℕ) : K) = 1 := by
          have : ((2 : ℕ) : K) = 0 := CharP.cast_eq_zero K 2
          rw [show (3 : ℕ) = 2 + 1 by norm_num, Nat.cast_add, this, zero_add, Nat.cast_one]
        rw [h3'] at h2
        exact one_ne_zero h2
      obtain ⟨-, -, -, hsplit, -⟩ :=
        CFSG.LocalAnalysis.ComponentInitial.orthogonal_low_dimensional_fixed_derived_component_coverage Q hQ
          (Or.inr (Or.inr ⟨by omega, U, hUn, hUQ⟩))
      obtain ⟨ψ, e, -, -, hcomm, -⟩ := hsplit (by omega) ⟨U, hUn, hUQ⟩ hK2 hK3
      rw [← Subgroup.map_sup, CFSG.LocalAnalysis.ComponentInitial.determinantFactors_sup] at hcomm
      have hρ : ∀ z, rho z ∈ specialImage K := fun z => by
        obtain ⟨c, hc⟩ := exists_sq_eq_units (commonDeterminant z)
        exact CFSG.LocalAnalysis.ComponentInitial.rho_mem_specialImage_of_commonDeterminant_eq_sq z hc.symm
      rw [Subgroup.relIndex, hsub]
      refine index_le_two_of_forall (e.symm tau) fun g => ?_
      obtain ⟨z, hz | hz⟩ := determinant_isometry_exhaustion (e g)
      · left
        rw [hcomm]
        exact ⟨e g, by rw [hz]; exact hρ z, e.symm_apply_apply g⟩
      · right
        rw [hcomm]
        refine ⟨rho z, hρ z, ?_⟩
        apply e.injective
        change e (e.symm (rho z)) = e (g * (e.symm tau)⁻¹)
        rw [MulEquiv.apply_symm_apply, map_mul, map_inv, MulEquiv.apply_symm_apply, hz, mul_inv_cancel_right]
    ·
      have hts : ∀ U : Submodule K W, finrank K U = n → ∃ u ∈ U, Q u ≠ 0 := by
        intro U hU
        by_contra hcon
        push Not at hcon
        exact hS ⟨U, hU, hcon⟩
      rcases hnf n (by omega) hn with ⟨b, hb⟩ | ⟨β, γ, -, -, b, hb⟩
      · exfalso
        refine hS ⟨Submodule.span K (Set.range fun i : Fin n => b (Sum.inl i)), ?_, ?_⟩
        · exact (finrank_span_eq_card (b.linearIndependent.comp _ Sum.inl_injective)).trans (by simp)
        · intro u hu
          obtain ⟨x, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hu
          simpa using hb x 0
      · have hU : ∀ u ∈ Submodule.span K (Set.range fun i : Fin (n - 1) => b (Sum.inl i)), Q u = 0 := by
          intro u hu
          obtain ⟨x, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hu
          simpa using hb x 0 0 0
        have hdU : finrank K (Submodule.span K (Set.range fun i : Fin (n - 1) => b (Sum.inl i))) = n - 1 :=
          (finrank_span_eq_card (b.linearIndependent.comp _ Sum.inl_injective)).trans (by simp)
        have hn23 : n = 2 ∨ n = 3 := by
          by_contra hne'
          exact hT (exists_threeSingular_of_le Q hU (by omega))
        rcases hn23 with rfl | rfl
        · obtain ⟨E, _, _, D, ψ, ρ, -, -, -, -, hcomm, -, -, -, -, hidx2, -, -⟩ :=
            CFSG.RankThree.PartOne.even_minus_four_actual_derived_extraction Q hQ (by omega) hts
          rw [Subgroup.relIndex, orthDerived, hcomm, hidx2]
        · obtain ⟨E, _, _, D, ψ, ρ, -, -, -, -, hcomm, -, -, -, -, hidx2, -, -⟩ :=
            CFSG.RankThree.PartOne.even_minus_six_actual_derived_extraction Q hQ (by omega) hts
          rw [Subgroup.relIndex, orthDerived, hcomm, hidx2]
  have hΩO : omegaGroup Q hQ ≤ TauCeti.QuadraticMap.orthogonalGroup Q := omegaGroup_le Q hQ
  have hNΩ : orthDerived Q ≤ omegaGroup Q hQ := CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hQ
  have hmul := Subgroup.relIndex_mul_relIndex (orthDerived Q) (omegaGroup Q hQ)
    (TauCeti.QuadraticMap.orthogonalGroup Q) hNΩ hΩO
  rw [relIndex_omegaGroup Q hQ] at hmul
  have hne' : (orthDerived Q).relIndex (omegaGroup Q hQ) ≠ 0 := Subgroup.index_ne_zero_of_finite
  exact Subgroup.relIndex_eq_one.mp (by omega)

end OmegaDerived

section OrthBlocks

open Module QuadraticMap Polynomial CFSG.RankThree.OrthogonalInvolutions CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem exists_fixedFactors_comm (hx : OddOrderIsometry Q p x) :
    ∃ (n : ℕ) (F : Fin n → Subgroup (V ≃ₗ[K] V)),
      (∀ i, CFSG.IsQuasisimple ↥(F i) ∧ F i ≤ supportedFixedDerived Q x ∧
        ((F i).subgroupOf (supportedFixedDerived Q x)).Normal) ∧
      (∀ i j, i ≠ j → ∀ u ∈ F i, ∀ v ∈ F j, u * v = v * u) ∧
      (FixedLayerListed Q x → ⨆ i, F i = supportedFixedDerived Q x) ∧
      (¬ FixedLayerListed Q x → n = 0) := by
  by_cases hlist : FixedLayerListed Q x
  · have hQW := hx.polarBilin_fixed_nondegenerate
    by_cases hT : ∃ U : Submodule K (fixedSpace x), finrank K U = 3 ∧
        ∀ u ∈ U, (Q.comp (fixedSpace x).subtype) u = 0
    · refine ⟨1, fun _ => supportedFixedDerived Q x, fun _ =>
        ⟨hx.isQuasisimple_supportedFixedDerived hT, le_rfl, ?_⟩,
        fun i j hij => absurd (Subsingleton.elim i j) hij, fun _ => iSup_const, fun h => absurd hlist h⟩
      rw [Subgroup.subgroupOf_self]
      exact Subgroup.normal_top
    · obtain ⟨-, h2⟩ := orthogonal_regular_space_coverage (Q.comp (fixedSpace x).subtype) hQW hlist.1
      obtain ⟨n, F, -, -, hsup, hF, hcomm, -⟩ := hx.exists_supported_factors (h2 hlist.2)
      exact ⟨n, F, hF, hcomm, fun _ => hsup, fun h => absurd hlist h⟩
  · exact ⟨0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun h => absurd h hlist, fun _ => rfl⟩

variable [CharP K 2]

theorem supportedBlock_le_orthDerived (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) (hx : OddOrderIsometry Q p x) (hp : Odd p)
    {r : K[X]} (hr : r ∈ primaryFactors x.toLinearMap) (hr1 : r ≠ X - 1) :
    supportedBlock Q x r ≤ orthDerived Q := by
  intro g hg
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    (Subgroup.mem_inf.mp (supportedBlock_le_isometryCentralizer r hg)).1
  exact CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQ hT
    (mem_omegaGroup.mpr ⟨hgO, hx.even_finrank_commSpace_of_mem_supportedBlock hp hr hr1 hg⟩)

theorem X_sub_one_mem_of_fixed (h : 1 ≤ finrank K (fixedSpace x)) :
    (X - 1 : K[X]) ∈ primaryFactors x.toLinearMap := by
  by_contra hX
  rw [fixedSpace_eq_bot_of_not_mem hX, finrank_bot] at h
  omega

theorem mem_supportedFixedDerived_of_mem_orthDerived (hQ : (polarBilin Q).Nondegenerate)
    (hx : OddOrderIsometry Q p x) (hp : Odd p) (hlist : FixedLayerListed Q x) {w : V ≃ₗ[K] V}
    (hw : w ∈ supportedBlock Q x (X - 1)) (hwΩ : w ∈ orthDerived Q) : w ∈ supportedFixedDerived Q x := by
  have hX := X_sub_one_mem_of_fixed (x := x) (by have := hlist.1; omega)
  have hQW := hx.polarBilin_fixed_nondegenerate
  have hD := hx.dicksonHom_eq_restrict_of_mem_supportedBlock hp hQ hX hw
  have hwev := (mem_omegaGroup.mp (CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hQ hwΩ)).2
  have hw1 : dicksonHom Q hQ ⟨w, (Subgroup.mem_inf.mp (supportedBlock_le_isometryCentralizer _ hw)).1⟩ = 1 := by
    rw [dicksonHom_apply, ← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff]
    exact (ZMod.natCast_eq_zero_iff_even).mpr hwev
  rw [hw1, dicksonHom_apply, ← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff] at hD
  have hWΩ : isometryRestrictFixed Q x ⟨w, supportedBlock_le_isometryCentralizer _ hw⟩ ∈
      omegaGroup (Q.comp (fixedSpace x).subtype) hQW :=
    mem_omegaGroup.mpr ⟨isometryRestrictFixed_mem_orthogonalGroup _,
      (ZMod.natCast_eq_zero_iff_even).mp hD.symm⟩
  have h1 := omegaGroup_le_orthDerived_of_listed (Q.comp (fixedSpace x).subtype) hQW hlist.1 hlist.2 hWΩ
  rw [mem_supportedFixedDerived]
  refine ⟨hw, ?_⟩
  rw [← isometryRestrictFixed_restrictFixed]
  exact h1

theorem exists_two_decomp (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) (hx : OddOrderIsometry Q 3 x)
    {Rep : Finset K[X]} (hRep : IsOrbitRepresentatives x Rep) {y : V ≃ₗ[K] V}
    (hy : y ∈ isometryCentralizer Q x) (hyΩ : y ∈ orthDerived Q) (hy2 : IsPGroup 2 ↥(Subgroup.zpowers y)) :
    ∃ w ∈ supportedBlock Q x (X - 1), w ∈ orthDerived Q ∧
      ∃ z ∈ ⨆ r : {r : ↥Rep // (r : K[X]) ≠ X - 1}, specialBlock Q x ((r.1 : K[X])), y = w * z := by
  classical
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  set A : {r : ↥Rep // (r : K[X]) ≠ X - 1} → Subgroup (V ≃ₗ[K] V) := fun r => supportedBlock Q x (r.1 : K[X])
    with hA
  have hle : isometryCentralizer Q x ≤ supportedBlock Q x (X - 1) ⊔ ⨆ r, A r := by
    rw [← hx.blocks_iSup_eq hRep]
    refine iSup_le fun i => ?_
    by_cases hi : (i : K[X]) = X - 1
    · rw [hi]
      exact le_sup_left
    · exact le_sup_of_le_right (le_iSup A ⟨i, hi⟩)
  have hcomm : ∀ a ∈ supportedBlock Q x (X - 1), ∀ c ∈ ⨆ r, A r, a * c = c * a := by
    intro a ha c hc
    by_cases hX : (X - 1 : K[X]) ∈ primaryFactors x.toLinearMap
    · have hle' : (⨆ r, A r) ≤ Subgroup.centralizer (supportedBlock Q x (X - 1) : Set (V ≃ₗ[K] V)) :=
        iSup_le fun r g hg => Subgroup.mem_centralizer_iff.2 fun a ha =>
          (hx.commute_supportedBlock hX (hRep.1 r.1.2) r.2
            (by rw [reciprocalPolynomial_X_sub_one]; exact r.2) ha hg).eq
      exact Subgroup.mem_centralizer_iff.1 (hle' hc) a ha
    · have ha1 : a = 1 := by
        refine hx.eq_one_of_restrictFixed_eq_one ha (LinearEquiv.ext fun v => Subtype.ext ?_)
        have hv : (v : V) ∈ (⊥ : Submodule K V) := by
          rw [← fixedSpace_eq_bot_of_not_mem hX]
          exact v.2
        have h0 : (v : V) = 0 := (Submodule.mem_bot K).1 hv
        have h1 : ((restrictFixed Q x ⟨a, ha⟩ v : fixedSpace x) : V) ∈ (⊥ : Submodule K V) := by
          rw [← fixedSpace_eq_bot_of_not_mem hX]
          exact (restrictFixed Q x ⟨a, ha⟩ v).2
        rw [(Submodule.mem_bot K).1 h1]
        exact h0.symm
      rw [ha1, one_mul, mul_one]
  obtain ⟨a, ha, c, hc, rfl⟩ := Input183.mem_sup_of_commute hcomm (hle hy)
  have hac : Commute a c := hcomm a ha c hc
  obtain ⟨k, hk, -, hck⟩ := exists_two_parts hac hy2
  have hck' : c ^ k ∈ ⨆ r : {r : ↥Rep // (r : K[X]) ≠ X - 1}, specialBlock Q x ((r.1 : K[X])) := by
    refine mem_iSup_of_two A (fun r => specialBlock Q x ((r.1 : K[X]))) ?_ ?_ (pow_mem hc k) hck
    · intro r s hrs g hg g' hg'
      exact hx.blocks_commute hRep (fun e => hrs (Subtype.ext e)) g g' hg hg'
    · intro r g hg hg2
      obtain ⟨m, hm⟩ := exists_pow_eq_one_of_isPGroup hg2
      haveI : Fact (Irreducible ((r.1 : K[X]))) := ⟨irreducible_of_mem_primaryFactors (hRep.1 r.1.2)⟩
      haveI : CharP (AdjoinRoot ((r.1 : K[X]))) 2 :=
        charP_of_injective_algebraMap (algebraMap K (AdjoinRoot ((r.1 : K[X])))).injective 2
      refine mem_specialBlock.mpr ⟨hg, eq_one_of_pow_two_pow_eq_one (m := m) ?_⟩
      have e1 : (⟨g, hg⟩ : ↥(supportedBlock Q x ((r.1 : K[X])))) ^ (2 ^ m) = 1 :=
        Subtype.ext (by simpa using hm)
      rw [← map_pow, e1, map_one]
  have hMΩ : (⨆ r : {r : ↥Rep // (r : K[X]) ≠ X - 1}, specialBlock Q x ((r.1 : K[X]))) ≤ orthDerived Q :=
    iSup_le fun r => (specialBlock_le_supportedBlock _).trans
      (supportedBlock_le_orthDerived hQ hT hx (by decide) (hRep.1 r.1.2) r.2)
  refine ⟨a ^ k, pow_mem ha k, ?_, c ^ k, hck', ?_⟩
  · have e2 : a ^ k = (a * c) ^ k * (c ^ k)⁻¹ := by rw [hac.mul_pow, mul_inv_cancel_right]
    rw [e2, hk]
    exact mul_mem hyΩ (inv_mem (hMΩ hck'))
  · rw [← hac.mul_pow, hk]

end OrthBlocks

section OrthInner

open Module QuadraticMap Polynomial CFSG.RankThree.OrthogonalInvolutions
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived ProjOrthDerived)
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple (exists_solvable_comm_le perfect_le_of_le_sup_solvable
  isComponentOf_of_normal_normal)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (component_mem_named_factors)

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem orth_component_cases {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hQ : (polarBilin Q).Nondegenerate)
    (x : ↥(orthDerived Q)) (hx : OddOrderIsometry Q p (x : V ≃ₗ[K] V)) {Rep : Finset K[X]}
    (hRep : IsOrbitRepresentatives (x : V ≃ₗ[K] V) Rep) {n : ℕ} {F : Fin n → Subgroup (V ≃ₗ[K] V)}
    (hFq : ∀ i, CFSG.IsQuasisimple ↥(F i) ∧ F i ≤ supportedFixedDerived Q (x : V ≃ₗ[K] V) ∧
      ((F i).subgroupOf (supportedFixedDerived Q (x : V ≃ₗ[K] V))).Normal)
    (hFsup : FixedLayerListed Q (x : V ≃ₗ[K] V) → ⨆ i, F i = supportedFixedDerived Q (x : V ≃ₗ[K] V))
    (hFn0 : ¬ FixedLayerListed Q (x : V ≃ₗ[K] V) → n = 0)
    {J : Subgroup (ProjOrthDerived Q)} (hJ : CFSG.Open.IsComponentOf J (centralizerImage Q (x : V ≃ₗ[K] V))) :
    (∃ r ∈ Rep, r ≠ X - 1 ∧ J = componentImage Q (x : V ≃ₗ[K] V) r) ∨
      ∃ i, J = ((F i).subgroupOf (orthDerived Q)).map
        (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  set ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) with hρ
  set xe : V ≃ₗ[K] V := (x : V ≃ₗ[K] V) with hxe
  set N : Subgroup (ProjOrthDerived Q) := centralizerImage Q xe with hN
  have hFΩ : ∀ i, F i ≤ orthDerived Q := fun i =>
    (hFq i).2.1.trans hx.supportedFixedDerived_le_orthDerived
  set C : Fin n → Subgroup (ProjOrthDerived Q) := fun i => ((F i).subgroupOf (orthDerived Q)).map ρ
    with hC
  have hCsup : (⨆ i, C i) = fixedLayerImage Q xe := by
    by_cases hlist : FixedLayerListed Q xe
    · rw [fixedLayerImage_of_listed hlist]
      unfold fixedComponentImage
      rw [← hFsup hlist, subgroupOf_iSup_of_le F _ hFΩ, Subgroup.map_iSup]
    · have hn := hFn0 hlist
      subst hn
      simp [fixedLayerImage, hlist]
  have hCle : ∀ i, C i ≤ fixedComponentImage Q xe := fun i =>
    Subgroup.map_mono fun g hg => Subgroup.mem_subgroupOf.mpr
      ((hFq i).2.1 (Subgroup.mem_subgroupOf.mp hg))
  have hCcomp : ∀ i, CFSG.Open.IsComponentOf (C i) N := by
    intro i
    have hconj := map_conj_mem ρ (F := (F i).subgroupOf (orthDerived Q))
      (F' := (supportedFixedDerived Q xe).subgroupOf (orthDerived Q)) (fun h k hh hk => by
        have := (Subgroup.normal_subgroupOf_iff (hFq i).2.1).mp (hFq i).2.2 (h : V ≃ₗ[K] V)
          (k : V ≃ₗ[K] V) (Subgroup.mem_subgroupOf.mp hh) (Subgroup.mem_subgroupOf.mp hk)
        exact Subgroup.mem_subgroupOf.mpr this)
    refine isComponentOf_of_normal_normal (hCle i) fixedComponentImage_le_centralizerImage ?_
      hx.normal_fixedComponentImage (isQuasisimple_map_projective (hFΩ i) (hFq i).1)
    rw [Subgroup.normal_subgroupOf_iff (hCle i)]
    intro h k hh hk
    exact hconj _ _ hh hk
  let ι₁ := {r : ↥Rep // r.1 ≠ X - 1 ∧ CFSG.IsQuasisimple ↥(specialBlock Q xe r.1)}
  have hspecΩ : ∀ r : ι₁, specialBlock Q xe r.1.1 ≤ orthDerived Q := fun r =>
    specialBlock_le_orthDerived_of_perfect r.2.2.1
      ((specialBlock_le_isometryCentralizer r.1.1).trans (fun _ hg => (Subgroup.mem_inf.mp hg).1))
  let S : ι₁ → Subgroup (ProjOrthDerived Q) := fun r => componentImage Q xe r.1.1
  have hScomp : ∀ r, CFSG.Open.IsComponentOf (S r) N := fun r =>
    isComponentOf_of_normal_normal componentImage_le_centralizerImage le_rfl normal_componentImage
      (by rw [Subgroup.subgroupOf_self]; exact Subgroup.normal_top)
      (isQuasisimple_map_projective (hspecΩ r) r.2.2)
  set EN : Subgroup (ProjOrthDerived Q) := (⨆ r, S r) ⊔ fixedLayerImage Q xe with hEN
  have hSN : ∀ r, S r ≤ N := fun r => componentImage_le_centralizerImage
  have hENN : EN ≤ N :=
    sup_le (iSup_le hSN) fixedLayerImage_le_centralizerImage
  have hENnormal : (EN.subgroupOf N).Normal :=
    normal_subgroupOf_sup (iSup_le hSN) fixedLayerImage_le_centralizerImage
      (normal_subgroupOf_iSup S hSN fun r => normal_componentImage) hx.normal_fixedLayerImage
  have hENn : ∀ c ∈ N, ∀ e ∈ EN, c * e * c⁻¹ ∈ EN := fun c hc e he =>
    (Subgroup.normal_subgroupOf_iff hENN).mp hENnormal e c he hc
  have hperf : ∀ P : Subgroup (ProjOrthDerived Q), P ≤ N → commutator ↥P = ⊤ → P ≤ EN := by
    intro P hPN hP
    obtain ⟨S₀, hS₀N, hS₀sol, hcomm⟩ := exists_solvable_comm_le hQ hp hp2 x hx hRep EN
      (fun h hh hne hq => le_sup_of_le_left
        (le_iSup S (⟨⟨h, hh⟩, hne, hq⟩ : ι₁)))
      (fun hlist => by
        rw [← fixedLayerImage_of_listed hlist]
        exact le_sup_right)
    haveI := hS₀sol
    exact perfect_le_of_le_sup_solvable hENN hS₀N hENn hcomm hPN (Subgroup.isPerfect_iff.1 ⟨hP⟩)
  let Fm : ι₁ ⊕ Fin n → Subgroup (ProjOrthDerived Q) := Sum.elim S C
  have hFm : ∀ i, CFSG.Open.IsComponentOf (Fm i) N := by
    rintro (r | i)
    · exact hScomp r
    · exact hCcomp i
  have hiSup : (⨆ i, Fm i) = EN := by
    rw [iSup_sum]
    simp only [Fm, Sum.elim_inl, Sum.elim_inr]
    rw [hCsup]
  obtain ⟨i, rfl⟩ := component_mem_named_factors Fm hFm
    (fun P hPN hP => hiSup ▸ hperf P hPN hP) hJ
  rcases i with ⟨⟨h, hh⟩, hne, -⟩ | i
  · exact Or.inl ⟨h, hh, hne, rfl⟩
  · exact Or.inr ⟨i, rfl⟩

theorem commute_fixed_supportedBlock {p : ℕ} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) {r : K[X]}
    (hr : r ∈ primaryFactors x.toLinearMap) (hr1 : r ≠ X - 1) {a c : V ≃ₗ[K] V}
    (ha : a ∈ supportedBlock Q x (X - 1)) (hc : c ∈ supportedBlock Q x r) : Commute a c := by
  by_cases hX : (X - 1 : K[X]) ∈ primaryFactors x.toLinearMap
  · exact hx.commute_supportedBlock hX hr hr1 (by rw [reciprocalPolynomial_X_sub_one]; exact hr1) ha hc
  · have ha1 : a = 1 := by
      refine hx.eq_one_of_restrictFixed_eq_one ha (LinearEquiv.ext fun v => Subtype.ext ?_)
      have hv : (v : V) ∈ (⊥ : Submodule K V) := by
        rw [← fixedSpace_eq_bot_of_not_mem hX]
        exact v.2
      have h0 : (v : V) = 0 := (Submodule.mem_bot K).1 hv
      have h1 : ((restrictFixed Q x ⟨a, ha⟩ v : fixedSpace x) : V) ∈ (⊥ : Submodule K V) := by
        rw [← fixedSpace_eq_bot_of_not_mem hX]
        exact (restrictFixed Q x ⟨a, ha⟩ v).2
      rw [(Submodule.mem_bot K).1 h1]
      exact h0.symm
    rw [ha1]
    exact Commute.one_left c

variable [CharP K 2]

theorem coprime_two_card_scalars_orthDerived [Nontrivial V] :
    Nat.Coprime 2 (Nat.card ((scalars K V).subgroupOf (orthDerived Q))) := by
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
  intro h2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hz2 : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
  obtain ⟨c, hc⟩ : ∃ c : K, ∀ v, ((z : ↥(orthDerived Q)) : V ≃ₗ[K] V) v = c • v :=
    mem_scalars.mp (Subgroup.mem_subgroupOf.mp z.2)
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hc2 : c ^ (2 ^ 1) = 1 := by
    have h1 : (((z ^ 2 : ↥((scalars K V).subgroupOf (orthDerived Q))) : ↥(orthDerived Q)) : V ≃ₗ[K] V) v = v := by
      rw [hz2]
      rfl
    have h2 : (((z ^ 2 : ↥((scalars K V).subgroupOf (orthDerived Q))) : ↥(orthDerived Q)) : V ≃ₗ[K] V) v =
        (c ^ 2) • v := by
      have e : (((z ^ 2 : ↥((scalars K V).subgroupOf (orthDerived Q))) : ↥(orthDerived Q)) : V ≃ₗ[K] V) =
          ((z : ↥(orthDerived Q)) : V ≃ₗ[K] V) * ((z : ↥(orthDerived Q)) : V ≃ₗ[K] V) := by
        rw [pow_two]
        rfl
      rw [e, LinearEquiv.mul_apply, hc, hc, smul_smul, ← pow_two]
    rw [h2] at h1
    have h3 : (c ^ 2 - 1) • v = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    rcases smul_eq_zero.mp h3 with h4 | h4
    · simpa [sub_eq_zero] using h4
    · exact absurd h4 hv
  have hc1 : c = 1 := eq_one_of_pow_two_pow_eq_one hc2
  have hz1 : z = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro w
    rw [hc w, hc1, one_smul]
    rfl
  rw [hz1, orderOf_one] at hz
  exact absurd hz (by norm_num)

theorem structAt_conj_orth (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (a : ProjOrthDerived Q) (ha : a ^ 3 = 1) (ha1 : a ≠ 1)
    {J : Subgroup (ProjOrthDerived Q)} (hJ : GLAPComponent 3 (fixSubgroup (MulAut.conj a)) J) :
    StructAt (MulAut.conj a) J := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have : Nontrivial V := by
    obtain ⟨U, hU, -⟩ := hT
    exact Module.nontrivial_of_finrank_pos (R := K)
      (lt_of_lt_of_le (by norm_num : 0 < 3) (hU ▸ Submodule.finrank_le U))
  have h3ℓ : 3 ≠ ringChar K := by rw [ringChar.eq K 2]; norm_num
  have hao : orderOf a = 3 := orderOf_eq_prime ha ha1
  obtain ⟨-, -, -, -, -, -, -, -, hlift⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  obtain ⟨x, ⟨hxa, hxp⟩, -, hcent⟩ := hlift 3 Nat.prime_three (by norm_num) a hao
  have hx : OddOrderIsometry Q 3 (x : V ≃ₗ[K] V) :=
    oddOrderIsometry_of_orthDerived Nat.prime_three h3ℓ hQ x hxp
  set ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) with hρ
  set xe : V ≃ₗ[K] V := (x : V ≃ₗ[K] V) with hxe
  have hker : ρ.ker ≤ Subgroup.center ↥(orthDerived Q) := by
    rw [QuotientGroup.ker_mk']
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨c, hc⟩ : ∃ c : K, ∀ v, (z : V ≃ₗ[K] V) v = c • v := mem_scalars.mp (Subgroup.mem_subgroupOf.mp hz)
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, hc, map_smul]
  have hodd : Nat.Coprime 2 (Nat.card ρ.ker) := by
    rw [QuotientGroup.ker_mk']
    exact coprime_two_card_scalars_orthDerived
  have hαβ : ∀ g, ρ (MulAut.conj x g) = MulAut.conj a (ρ g) := fun g => by
    rw [← hxa]
    show ρ (x * g * x⁻¹) = ρ x * ρ g * (ρ x)⁻¹
    rw [map_mul, map_mul, map_inv]
  have hlay := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_conj_projOrth_of_orderOf hQ hT
    Nat.prime_three (by norm_num) h3ℓ a hao
  have hJc := isComponentOf_of_perfectInLayer hlay hJ
  have hfix : fixSubgroup (MulAut.conj a) = centralizerImage Q xe := by
    have e1 : fixSubgroup (MulAut.conj a) = Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_conj_eq_centralizer a
    rw [e1, hcent, CFSG.RankThree.PartOne.map_centralizer_eq_centralizerImage x]
  have hJc' : CFSG.Open.IsComponentOf J (centralizerImage Q xe) := hfix ▸ hJc
  obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
  obtain ⟨n, F, hFq, hFcomm, hFsup, hFn0⟩ := exists_fixedFactors_comm hx
  have h2 : ∀ g ∈ fixSubgroup (MulAut.conj x), IsPGroup 2 ↥(Subgroup.zpowers g) →
      ∃ w ∈ supportedBlock Q xe (X - 1), ∃ hwΩ : w ∈ orthDerived Q,
        ∃ z ∈ ⨆ r : {r : ↥Rep // (r : K[X]) ≠ X - 1}, specialBlock Q xe ((r.1 : K[X])),
          ∃ hzΩ : z ∈ orthDerived Q, g = ⟨w, hwΩ⟩ * ⟨z, hzΩ⟩ := by
    intro g hg hg2
    have hgx : g ∈ Subgroup.centralizer ({x} : Set ↥(orthDerived Q)) := by
      rw [← CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_conj_eq_centralizer]
      exact hg
    have hgC : (g : V ≃ₗ[K] V) ∈ isometryCentralizer Q xe := by
      refine Subgroup.mem_inf.mpr ⟨orthDerived_le_orthogonalGroup g.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hgx ⊢
      exact congrArg Subtype.val hgx
    have hg2' : IsPGroup 2 ↥(Subgroup.zpowers (g : V ≃ₗ[K] V)) := by
      have h1 := hg2.map (orthDerived Q).subtype
      rwa [MonoidHom.map_zpowers] at h1
    obtain ⟨w, hw, hwΩ, z, hz, hgwz⟩ := exists_two_decomp hQ hT hx hRep hgC g.2 hg2'
    have hzΩ : z ∈ orthDerived Q := by
      have e2 : z = w⁻¹ * (g : V ≃ₗ[K] V) := by rw [hgwz, inv_mul_cancel_left]
      rw [e2]
      exact mul_mem (inv_mem hwΩ) g.2
    exact ⟨w, hw, hwΩ, z, hz, hzΩ, Subtype.ext hgwz⟩
  have hspecle : ∀ r : {r : ↥Rep // (r : K[X]) ≠ X - 1}, specialBlock Q xe ((r.1 : K[X])) ≤ orthDerived Q :=
    fun r => (specialBlock_le_supportedBlock _).trans
      (supportedBlock_le_orthDerived hQ hT hx (by decide) (hRep.1 r.1.2) r.2)
  have hzmem : ∀ z ∈ ⨆ r : {r : ↥Rep // (r : K[X]) ≠ X - 1}, specialBlock Q xe ((r.1 : K[X])),
      ∀ hzΩ : z ∈ orthDerived Q, (⟨z, hzΩ⟩ : ↥(orthDerived Q)) ∈
        ⨆ r : {r : ↥Rep // (r : K[X]) ≠ X - 1}, (specialBlock Q xe ((r.1 : K[X]))).subgroupOf (orthDerived Q) := by
    intro z hz hzΩ
    rw [← subgroupOf_iSup_of_le _ _ hspecle]
    exact Subgroup.mem_subgroupOf.mpr hz
  rcases orth_component_cases Nat.prime_three (by norm_num) hQ x hx hRep hFq hFsup hFn0 hJc' with
    ⟨r₀, hr₀, hr₀1, hJr⟩ | ⟨i₀, hJi⟩
  ·
    let B : Option {r : ↥Rep // (r : K[X]) ≠ X - 1} → Subgroup ↥(orthDerived Q) := fun o =>
      match o with
      | none => (supportedBlock Q xe (X - 1)).subgroupOf (orthDerived Q)
      | some r => (specialBlock Q xe ((r.1 : K[X]))).subgroupOf (orthDerived Q)
    refine structAt_of_family ρ (QuotientGroup.mk'_surjective _) hker hodd (MulAut.conj x) (MulAut.conj a) hαβ B
      ?_ ?_ hJc (some ⟨⟨r₀, hr₀⟩, hr₀1⟩) hJr
    · rintro (_ | r) (_ | s) hrs u hu v hv
      · exact absurd rfl hrs
      · exact Subtype.ext (commute_fixed_supportedBlock hx (hRep.1 s.1.2) s.2 hu
          (specialBlock_le_supportedBlock _ hv)).eq
      · exact Subtype.ext (commute_fixed_supportedBlock hx (hRep.1 r.1.2) r.2 hv
          (specialBlock_le_supportedBlock _ hu)).symm.eq
      · have hrs' : r.1 ≠ s.1 := fun e => hrs (by rw [Subtype.ext e])
        exact Subtype.ext (hx.blocks_commute hRep hrs' _ _ (specialBlock_le_supportedBlock _ hu)
          (specialBlock_le_supportedBlock _ hv)).eq
    · intro g hg hg2
      obtain ⟨w, hw, hwΩ, z, hz, hzΩ, rfl⟩ := h2 g hg hg2
      refine mul_mem (Subgroup.mem_iSup_of_mem none (Subgroup.mem_subgroupOf.mpr hw)) ?_
      refine (iSup_le fun r => le_iSup B (some r) : (⨆ r : {r : ↥Rep // (r : K[X]) ≠ X - 1},
        (specialBlock Q xe ((r.1 : K[X]))).subgroupOf (orthDerived Q)) ≤ ⨆ o, B o) (hzmem z hz hzΩ)
  ·
    have hlist : FixedLayerListed Q xe := by
      by_contra h
      have := hFn0 h
      subst this
      exact i₀.elim0
    let B : Fin n ⊕ {r : ↥Rep // (r : K[X]) ≠ X - 1} → Subgroup ↥(orthDerived Q) :=
      Sum.elim (fun i => (F i).subgroupOf (orthDerived Q))
        (fun r => (specialBlock Q xe ((r.1 : K[X]))).subgroupOf (orthDerived Q))
    have hFB : ∀ i, F i ≤ supportedBlock Q xe (X - 1) := fun i =>
      (hFq i).2.1.trans supportedFixedDerived_le_supportedBlock
    refine structAt_of_family ρ (QuotientGroup.mk'_surjective _) hker hodd (MulAut.conj x) (MulAut.conj a) hαβ B
      ?_ ?_ hJc (Sum.inl i₀) hJi
    · rintro (i | r) (j | s) hrs u hu v hv
      · have hij : i ≠ j := fun e => hrs (by rw [e])
        exact Subtype.ext (hFcomm i j hij _ hu _ hv)
      · exact Subtype.ext (commute_fixed_supportedBlock hx (hRep.1 s.1.2) s.2 (hFB i hu)
          (specialBlock_le_supportedBlock _ hv)).eq
      · exact Subtype.ext (commute_fixed_supportedBlock hx (hRep.1 r.1.2) r.2 (hFB j hv)
          (specialBlock_le_supportedBlock _ hu)).symm.eq
      · have hrs' : r.1 ≠ s.1 := fun e => hrs (by rw [Subtype.ext e])
        exact Subtype.ext (hx.blocks_commute hRep hrs' _ _ (specialBlock_le_supportedBlock _ hu)
          (specialBlock_le_supportedBlock _ hv)).eq
    · intro g hg hg2
      obtain ⟨w, hw, hwΩ, z, hz, hzΩ, rfl⟩ := h2 g hg hg2
      have hwF : w ∈ ⨆ i, F i := by
        rw [hFsup hlist]
        exact mem_supportedFixedDerived_of_mem_orthDerived hQ hx (by decide) hlist hw hwΩ
      have hwF' : (⟨w, hwΩ⟩ : ↥(orthDerived Q)) ∈ ⨆ i, (F i).subgroupOf (orthDerived Q) := by
        rw [← subgroupOf_iSup_of_le _ _ (fun i => (hFq i).2.1.trans hx.supportedFixedDerived_le_orthDerived)]
        exact Subgroup.mem_subgroupOf.mpr hwF
      refine mul_mem ((iSup_le fun i => le_iSup B (Sum.inl i) : (⨆ i, (F i).subgroupOf (orthDerived Q)) ≤
        ⨆ o, B o) hwF') ?_
      exact (iSup_le fun r => le_iSup B (Sum.inr r) : (⨆ r : {r : ↥Rep // (r : K[X]) ≠ X - 1},
        (specialBlock Q xe ((r.1 : K[X]))).subgroupOf (orthDerived Q)) ≤ ⨆ o, B o) (hzmem z hz hzΩ)

end OrthInner

section OrthOuter

open Module QuadraticMap CFSG.RankThree.PartOne.KCOrthogonalSubfield
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {k : Subfield K} {d : ℕ}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)} {σ : K ≃+* K} {p : ℕ}

theorem structAt_fieldAutT (S : SubfieldSetup k Q₀ Q σ p) {J : Subgroup (matrixProjectiveDerived Q)}
    (hJ : GLAPComponent 3 (fixSubgroup (fieldAutT Q σ S.hQσ)) J) : StructAt (fieldAutT Q σ S.hQσ) J := by
  have hd0 : 0 < d := three_le_of_totallySingular k S.hT₀
  have hfix : fixSubgroup (fieldAutT Q σ S.hQσ) = subfieldDerivedImage k S.hext := by
    have h1 : fixSubgroup (fieldAutT Q σ S.hQσ) = subfieldFixedGroup k Q₀ Q :=
      Subgroup.ext fun t => (mem_fixSubgroup).trans (fieldAutT_apply_iff S t)
    rw [h1]
    exact le_antisymm (CFSG.RankThree.PartOne.FieldFix.subfieldFixedGroup_le_derivedImage S.hext S.hnd₀ S.hT₀ S.hnd)
      (subfieldDerivedImage_le k S.hext)
  obtain ⟨hsimp, hnonab⟩ := matrix_simple_nonabelian hd0 S.hnd₀ S.hT₀
  have hJq : CFSG.IsQuasisimple ↥(subfieldDerivedImage k S.hext) :=
    CFSG.IsQuasisimple.of_mulEquiv (inclEquiv k S.hext hd0).symm
      (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isQuasisimple_of_isSimpleGroup hsimp hnonab)
  have hq : CFSG.IsQuasisimple ↥(fixSubgroup (fieldAutT Q σ S.hQσ)) := hfix ▸ hJq
  exact structAt_of_isQuasisimple_fixSubgroup ⟨hq.1.1, hq.2.1⟩ hJ.1

end OrthOuter

section OrthCatalogue

open Module QuadraticMap CFSG.RankThree.PartOne.KCOrthogonalSubfield
open CFSG.RankThree.Classical2 (orthDerived ProjOrthDerived)

@[expose] def D4OuterCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] {f : ℕ},
    CFSG.Open.StatedClassicalModel G CFSG.Open.StatedLieTag.POmegaPlus 4 2 f →
    ∀ β : MulAut G, β ^ 3 = 1 → (∀ a : G, MulAut.conj a ≠ β) →
    ∀ J : Subgroup G, GLAPComponent 3 (fixSubgroup β) J → IsLThreeFour (barOf 3 J ⧸ Subgroup.center (barOf 3 J)) →
    ∀ k : G, k ∈ fixSubgroup β → IsPGroup 2 ↥(Subgroup.zpowers k) → InducesInner 3 J k

theorem input14_1CoreFor_orthogonal (hD4 : D4OuterCore) :
    Input14_1CoreFor fun d => ∃ r q, d = TauCeti.LieTypeIndex.D r q ∨ d = TauCeti.LieTypeIndex.twistedD r q := by
  intro S _ _ hS hna idx hd hchar he β hβ hβ1 J hJ hJt k hk hk2
  haveI := hS
  obtain ⟨e⟩ := he
  have hor : (∃ r q, idx.1 = TauCeti.LieTypeIndex.B r q ∧ q.p ≠ 2 ∧ 3 ≤ r) ∨
      (∃ r q, idx.1 = TauCeti.LieTypeIndex.D r q) ∨ ∃ r q, idx.1 = TauCeti.LieTypeIndex.twistedD r q := by
    obtain ⟨r, q, hrq | hrq⟩ := hd
    · exact Or.inr (Or.inl ⟨r, q, hrq⟩)
    · exact Or.inr (Or.inr ⟨r, q, hrq⟩)
  obtain ⟨t, n, f, ht, hG⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_statedClassicalModel_orth idx hor e
  have hℓ2 : CFSG.HardMathSupport.Solomon.Coordinator.lieIndexChar idx.1 = 2 := by
    rw [lieIndexChar_eq_characteristic]
    exact hchar
  rw [hℓ2] at hG
  have hJ20 := card_dvd_of_isLThreeFour hJt
  by_cases hin : ∃ a : S, MulAut.conj a = β
  ·
    obtain ⟨a, rfl⟩ := hin
    refine inducesInner_of_structAt hJ ?_ hk hk2
    obtain ⟨K, _, _, V, _, _, _, Q, hQ, hT, hring, ⟨e'⟩⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_projOrth_model ht hG
    haveI : CharP K 2 := hring ▸ ringChar.charP K
    have ha3 : a ^ 3 = 1 := by
      have hc : a ^ 3 ∈ Subgroup.center S := by
        rw [Subgroup.mem_center_iff]
        intro g
        have h1 := congrArg (fun φ : MulAut S => φ g)
          (show MulAut.conj (a ^ 3) = 1 by rw [map_pow]; exact hβ)
        simp only [MulAut.conj_apply, MulAut.one_apply] at h1
        calc g * a ^ 3 = a ^ 3 * g * (a ^ 3)⁻¹ * a ^ 3 := by rw [h1]
          _ = a ^ 3 * g := by group
      rw [CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_center_eq_bot hna, Subgroup.mem_bot] at hc
      exact hc
    have ha1 : e' a ≠ 1 := by
      intro h1
      apply hβ1
      rw [show a = 1 from e'.injective (h1.trans (map_one e').symm), map_one]
    have hJ' := glaPComponent_congr e' hJ
    rw [congr_conj_eq] at hJ'
    refine structAt_of_congr e' ?_
    rw [congr_conj_eq]
    exact structAt_conj_orth hQ hT (e' a) (by rw [← map_pow, ha3, map_one]) ha1 hJ'
  · have hout : ∀ a : S, MulAut.conj a ≠ β := fun a h => hin ⟨a, h⟩
    by_cases hd4 : t = CFSG.Open.StatedLieTag.POmegaPlus ∧ n = 4
    ·
      obtain ⟨rfl, rfl⟩ := hd4
      exact hD4 S hG β hβ hout J hJ hJt k hk hk2
    ·
      refine inducesInner_of_structAt hJ ?_ hk hk2
      have hc : CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OmegaFieldConj S β 2 3 := by
        rcases ht with rfl | rfl | rfl
        · exfalso
          exact hG.1.2.2.2 rfl
        · exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.omegaFieldConj_plus Nat.prime_three (by norm_num) hG
            (fun h => absurd ⟨rfl, h⟩ hd4) β hβ hout
        · exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.omegaFieldConj_minus Nat.prime_three (by norm_num) hG
            β hβ hout
      obtain ⟨K, _, _, k', d, Q₀, Q, σ, Sf, e', -, hch, he'⟩ := hc.out
      haveI : CharP K 2 := hch ▸ ringChar.charP K
      have hJ' := glaPComponent_congr e' hJ
      rw [he'] at hJ'
      refine structAt_of_congr e' ?_
      rw [he']
      exact structAt_fieldAutT Sf hJ'

end OrthCatalogue

section GoodFixed

@[expose] def GoodFixed (H : Type*) [Group H] : Prop :=
  (∃ (M : Subgroup H) (_ : M.Normal), CFSG.IsQuasisimple ↥M ∧ Group.IsSolvable (H ⧸ M) ∧
    ∀ g : H, IsPGroup 2 ↥(Subgroup.zpowers g) → g ∈ M) ∨
  ∀ P : Subgroup H, ⁅P, P⁆ = P → Nat.card ↥P < 20160

theorem eq_bot_of_perfect_of_isSolvable {H : Type*} [Group H] [Group.IsSolvable H] {P : Subgroup H}
    (hP : ⁅P, P⁆ = P) : P = ⊥ := by
  have hle : ∀ n, P ≤ derivedSeries H n := by
    intro n
    induction n with
    | zero => exact le_top
    | succ n ih =>
      rw [derivedSeries_succ, ← hP]
      exact Subgroup.commutator_mono ih ih
  obtain ⟨n, hn⟩ := (inferInstance : Group.IsSolvable H).solvable
  exact le_bot_iff.mp (hn ▸ hle n)

theorem goodFixed_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (h : GoodFixed H) :
    GoodFixed G := by
  rcases h with ⟨M, hMn, hMq, hMs, hM2⟩ | hP
  · left
    have hmap : (M.comap e.toMonoidHom).map e.toMonoidHom = M :=
      Subgroup.map_comap_eq_self_of_surjective e.surjective M
    refine ⟨M.comap e.toMonoidHom, hMn.comap _, ?_, ?_, fun g hg => ?_⟩
    · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (((M.comap e.toMonoidHom).equivMapOfInjective e.toMonoidHom e.injective).trans
          (MulEquiv.subgroupCongr hmap)).symm hMq
    · haveI := hMs
      exact Group.isSolvable_of_isSolvable_injective
        (f := (QuotientGroup.congr (M.comap e.toMonoidHom) M e hmap).toMonoidHom)
        (QuotientGroup.congr (M.comap e.toMonoidHom) M e hmap).injective
    · have hg' : IsPGroup 2 ↥(Subgroup.zpowers (e g)) := by
        have h1 := hg.map e.toMonoidHom
        rwa [MonoidHom.map_zpowers] at h1
      exact hM2 (e g) hg'
  · right
    intro P hPP
    have h1 : ⁅P.map e.toMonoidHom, P.map e.toMonoidHom⁆ = P.map e.toMonoidHom := by
      rw [← Subgroup.map_commutator, hPP]
    have h2 := hP _ h1
    rwa [Subgroup.card_map_of_injective e.injective] at h2

theorem goodFixed_of_isQuasisimple {H : Type*} [Group H] (h : CFSG.IsQuasisimple H) : GoodFixed H := by
  left
  refine ⟨⊤, Subgroup.normal_top, CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm h, ?_,
    fun g _ => Subgroup.mem_top g⟩
  haveI : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top
  infer_instance

theorem goodFixed_of_isSolvable {H : Type*} [Group H] [Group.IsSolvable H] : GoodFixed H := by
  right
  intro P hP
  rw [eq_bot_of_perfect_of_isSolvable hP, Subgroup.card_bot]
  norm_num

theorem structAt_of_goodFixed {S : Type} [Group S] [Finite S] {β : MulAut S} (h : GoodFixed ↥(fixSubgroup β))
    {J : Subgroup S} (hJ : GLAPComponent 3 (fixSubgroup β) J) (hJ20 : 20160 ∣ Nat.card ↥J) : StructAt β J := by
  have hJC : J ≤ fixSubgroup β := hJ.1
  have hJ0 : ⁅J.subgroupOf (fixSubgroup β), J.subgroupOf (fixSubgroup β)⁆ = J.subgroupOf (fixSubgroup β) := by
    apply Subgroup.map_injective (fixSubgroup β).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hJC]
    exact glaPComponent_perfect hJ
  rcases h with ⟨M, hMn, hMq, hMs, hM2⟩ | hP
  · set M' : Subgroup S := M.map (fixSubgroup β).subtype with hM'
    have hMC : M' ≤ fixSubgroup β := Subgroup.map_subtype_le M
    have hM'eq : M'.subgroupOf (fixSubgroup β) = M :=
      Subgroup.comap_map_eq_self_of_injective (fixSubgroup β).subtype_injective M
    have hMn' : (M'.subgroupOf (fixSubgroup β)).Normal := hM'eq ▸ hMn
    have hMq' : CFSG.IsQuasisimple ↥M' :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (M.equivMapOfInjective _ (fixSubgroup β).subtype_injective) hMq
    have h2 : ∀ k ∈ fixSubgroup β, IsPGroup 2 ↥(Subgroup.zpowers k) → k ∈ M' := by
      intro k hk hk2
      obtain ⟨m, hm⟩ := exists_pow_eq_one_of_isPGroup hk2
      exact ⟨⟨k, hk⟩, hM2 _ (isPGroup_zpowers_of_pow (m := m) (Subtype.ext (by simpa using hm))), rfl⟩
    have hJM : J ≤ M' := by
      haveI := hMs
      have hP0 : ⁅(J.subgroupOf (fixSubgroup β)).map (QuotientGroup.mk' M),
          (J.subgroupOf (fixSubgroup β)).map (QuotientGroup.mk' M)⁆ =
          (J.subgroupOf (fixSubgroup β)).map (QuotientGroup.mk' M) := by
        rw [← Subgroup.map_commutator, hJ0]
      have hbot := eq_bot_of_perfect_of_isSolvable hP0
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
      intro x hx
      exact ⟨⟨x, hJC hx⟩, hbot (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
    exact structAt_of_normal_quasisimple hMC hMn' ⟨hMq'.1.1, hMq'.2.1⟩ h2 hJM
  · exfalso
    have h1 := hP _ hJ0
    have h2 : Nat.card ↥(J.subgroupOf (fixSubgroup β)) = Nat.card ↥J := by
      rw [← Subgroup.card_map_of_injective (fixSubgroup β).subtype_injective,
        Subgroup.map_subgroupOf_eq_of_le hJC]
    have h3 := Nat.le_of_dvd Nat.card_pos hJ20
    omega

end GoodFixed

section D4Outer

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.D4Three
  CFSG.HardMathSupport.Lang.E6Descent
open CFSG.RankThree.PartTwo (Sec4.PiField Sec4.glPi Sec4.slPi Sec4.autFix)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped Pointwise commutatorElement

private theorem exists_frobenius_data' {K : Type} [Field K] [Finite K] (σ : K ≃+* K) (hσ : σ ≠ 1)
    (hσ3 : σ ^ 3 = 1) :
    ∃ (ℓ e : ℕ) (T : K ≃+* K), ℓ.Prime ∧ CharP K ℓ ∧ 1 ≤ e ∧ Nat.card K = ℓ ^ (e * 3) ∧
      (∀ c, T c = c ^ (ℓ ^ e)) ∧ (σ = T ∨ σ = T⁻¹) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hpr, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hpr⟩
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ
  obtain ⟨e, T, he, hef, hT, hσT⟩ :=
    exists_frobenius_eq_or_inv_of_orderOf_three hpr n.pos K hK σ hord
  exact ⟨ringChar K, e, T, hpr, ringChar.charP K, he, by rw [hef, hK], hT, hσT⟩

private theorem mem_of_pow_mem_of_coprime {G : Type*} [Group G] {H : Subgroup G} {y : G} {a b : ℕ}
    (hab : Nat.Coprime a b) (ha : y ^ a ∈ H) (hb : y ^ b ∈ H) : y ∈ H := by
  have h := Nat.gcd_eq_gcd_ab a b
  rw [hab.gcd_eq_one, Nat.cast_one] at h
  have hy : y = (y ^ a) ^ (Nat.gcdA a b) * (y ^ b) ^ (Nat.gcdB a b) := by
    rw [← zpow_natCast y a, ← zpow_natCast y b, ← zpow_mul, ← zpow_mul, ← zpow_add, ← h, zpow_one]
  rw [hy]
  exact mul_mem (zpow_mem ha _) (zpow_mem hb _)

private theorem goodFixed_of_conj_eq {S : Type} [Group S] {α δ ψ : MulAut S} (h : ψ * α * ψ⁻¹ = δ)
    (hδ : GoodFixed ↥(fixSubgroup δ)) : GoodFixed ↥(fixSubgroup α) := by
  have hc : MulAut.congr ψ α = δ := by
    rw [← h]
    exact MulEquiv.ext fun _ => rfl
  rw [← hc, Inputs141c.fixSubgroup_congr] at hδ
  exact goodFixed_of_mulEquiv ((fixSubgroup α).equivMapOfInjective ψ.toMonoidHom ψ.injective) hδ

private theorem goodFixed_of_inv {S : Type} [Group S] {β : MulAut S} (h : GoodFixed ↥(fixSubgroup β)) :
    GoodFixed ↥(fixSubgroup β⁻¹) := by
  rw [CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.fixSubgroup_inv_eq]
  exact h

private theorem goodFixed_projImage_glPi {π : Bool} {f : ℕ} {F : Type} [Field F] (hF : Sec4.PiField π 2 f F)
    (hπ2 : π = true → 2 < 2 ^ f) : GoodFixed ↥(projImage (Sec4.glPi π 3 (2 ^ f) F)) := by
  have := hF.finite
  by_cases hq2 : 2 < 2 ^ f
  · left
    have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f F := fun h => by
      subst h
      exact hF.unitary
    have hSP : projImage (Sec4.slPi π 3 (2 ^ f) F) ≤ projImage (Sec4.glPi π 3 (2 ^ f) F) :=
      Subgroup.map_mono (CFSG.RankThree.PartTwo.Sec4.slPi_le_glPi hπ)
    have hperfS : Group.IsPerfect (projImage (Sec4.slPi π 3 (2 ^ f) F)) :=
      CFSG.RankThree.PartTwo.Sec13.isPerfect_projImage_slPi hF hq2
    have hs := CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.isSimpleGroup_projImage_slPi hF hq2
    have : Nontrivial (projImage (Sec4.slPi π 3 (2 ^ f) F)) := hs.toNontrivial
    have hq := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup
      (CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.exists_ne_comm_of_isPerfect hperfS)).1
    have hcomm := CFSG.RankThree.PartTwo.Sec13.commutator_projImage_glPi hF hq2
    refine ⟨commutator ↥(projImage (Sec4.glPi π 3 (2 ^ f) F)), inferInstance, ?_, ?_, ?_⟩
    · rw [hcomm]
      exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hSP).symm hq
    · refine Group.isSolvable_of_comm fun a b => ?_
      induction a using QuotientGroup.induction_on with | H x => ?_
      induction b using QuotientGroup.induction_on with | H y => ?_
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have hxy : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by
        rw [commutatorElement_def]
        group
      rw [hxy, commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    · intro y hy
      obtain ⟨m, hm⟩ := exists_pow_eq_one_of_isPGroup hy
      rw [hcomm]
      obtain ⟨δ, hδ, hδy⟩ := y.2
      have h3 : y ^ 3 ∈ (projImage (Sec4.slPi π 3 (2 ^ f) F)).subgroupOf
          (projImage (Sec4.glPi π 3 (2 ^ f) F)) := by
        rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow, ← hδy]
        exact CFSG.RankThree.PartTwo.Sec16.KS1615MeetProof.mk_pow_three_mem hF hδ
      refine mem_of_pow_mem_of_coprime (Nat.Coprime.pow_right m (by norm_num : Nat.Coprime 3 2)) h3 ?_
      rw [hm]
      exact one_mem _
  · have h2 : 2 ^ f = 2 := by
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hF.one_le
      omega
    cases π
    · haveI := CFSG.RankThree.PartTwo.Sec13.isSolvable_projImage_glPi_two hF h2
      exact goodFixed_of_isSolvable
    · exact absurd (hπ2 rfl) hq2


private theorem isSimpleGroup_adjointGroup_D4' (k : Type) [Field k] [Finite k] :
    IsSimpleGroup (adjointGroup Tag.D4 k) ∧ ∃ x y : adjointGroup Tag.D4 k, x * y ≠ y * x := by
  have hnc := (opposite_simple_root_noncommutativity Tag.D4 k).2.2.1
  have : Group.IsPerfect (adjointGroup Tag.D4 k) :=
    ⟨single_edge_perfect Tag.D4 k (Or.inr (Or.inl rfl))⟩
  have : Nontrivial (adjointGroup Tag.D4 k) := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨⟨a * b, b * a, hab⟩⟩
  have hZ : Subgroup.center (adjointGroup Tag.D4 k) = ⊥ := center_adjointGroup_eq_bot
  refine ⟨IsSimpleGroup.mk fun M hM => ?_, hnc⟩
  by_cases hbot : M = ⊥
  · exact Or.inl hbot
  · right
    have hnot : ¬ M ≤ Subgroup.center (adjointGroup Tag.D4 k) := by
      rw [hZ]
      exact fun h => hbot (le_bot_iff.1 h)
    have hsolv := (noncentral_normal_solvable_quotient Tag.D4 k M hnot).2.1
    by_contra htop
    have : Nontrivial (adjointGroup Tag.D4 k ⧸ M) := by
      rw [← not_subsingleton_iff_nontrivial, QuotientGroup.subsingleton_iff]
      exact htop
    exact Group.IsPerfect.not_isSolvable _ hsolv

private theorem goodFixed_entrywiseAdjointAut_D4 {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) :
    GoodFixed ↥(fixSubgroup (entrywiseAdjointAut Tag.D4 σ)) := by
  classical
  have : Finite (ModGL Tag.D4 K) := finite_modGL
  obtain ⟨-, hinj, -, hJΓ, hΓeq, hJnormal, hcomm⟩ :=
    Chevalley_coordinate_field_fixed_normal_subgroup Tag.D4 K σ
  have : Finite (fixSubfield σ) := inferInstance
  obtain ⟨hs, hnc⟩ :=
    isSimpleGroup_adjointGroup_D4' (fixSubfield σ)
  have hJC : fixedFieldImage Tag.D4 σ ≤ adjointGroup Tag.D4 K := fun g hg => (hJΓ hg).1
  have hΓnorm : entrywiseFixedGroup Tag.D4 σ ≤
      Subgroup.normalizer (fixedFieldImage Tag.D4 σ : Set (ModGL Tag.D4 K)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJΓ).1 hJnormal
  have hfix : ∀ x : adjointGroup Tag.D4 K,
      x ∈ fixSubgroup (entrywiseAdjointAut Tag.D4 σ) ↔
        (x : ModGL Tag.D4 K) ∈ entrywiseFixedGroup Tag.D4 σ := fun x => by
    rw [mem_fixSubgroup, mem_entrywiseFixedGroup]
    constructor
    · intro h
      exact ⟨x.2, (coe_entrywiseAdjointAut Tag.D4 σ x).symm.trans (congrArg Subtype.val h)⟩
    · rintro ⟨-, h⟩
      exact Subtype.ext ((coe_entrywiseAdjointAut Tag.D4 σ x).trans h)
  let J : Subgroup ↥(adjointGroup Tag.D4 K) :=
    (fixedFieldImage Tag.D4 σ).subgroupOf (adjointGroup Tag.D4 K)
  have hJmem : ∀ x : adjointGroup Tag.D4 K,
      x ∈ J ↔ (x : ModGL Tag.D4 K) ∈ fixedFieldImage Tag.D4 σ := fun x => Iff.rfl
  have hJle : J ≤ fixSubgroup (entrywiseAdjointAut Tag.D4 σ) := fun x hx =>
    (hfix x).2 (hJΓ ((hJmem x).1 hx))
  have hJn : (J.subgroupOf (fixSubgroup (entrywiseAdjointAut Tag.D4 σ))).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hJle).2 fun g hg => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hJmem, hJmem]
    exact Subgroup.mem_normalizer_iff.1 (hΓnorm ((hfix g).1 hg)) (h : ModGL Tag.D4 K)
  let eJ : J ≃* adjointGroup Tag.D4 (fixSubfield σ) :=
    (Subgroup.subgroupOfEquivOfLe hJC).trans
      ((adjointGroup Tag.D4 (fixSubfield σ)).equivMapOfInjective _ hinj).symm
  haveI := hs
  have hq : CFSG.IsQuasisimple ↥(J.subgroupOf (fixSubgroup (entrywiseAdjointAut Tag.D4 σ))) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv ((Subgroup.subgroupOfEquivOfLe hJle).trans eJ).symm
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1
  have hsol : Group.IsSolvable
      (↥(fixSubgroup (entrywiseAdjointAut Tag.D4 σ)) ⧸
        J.subgroupOf (fixSubgroup (entrywiseAdjointAut Tag.D4 σ))) := by
    refine Group.isSolvable_of_comm fun a b => ?_
    induction a using QuotientGroup.induction_on with | H x => ?_
    induction b using QuotientGroup.induction_on with | H y => ?_
    have hx : ((x : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) ∈ entrywiseFixedGroup Tag.D4 σ :=
      (hfix x.1).1 x.2
    have hy : ((y : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) ∈ entrywiseFixedGroup Tag.D4 σ :=
      (hfix y.1).1 y.2
    have hq := hcomm (QuotientGroup.mk ⟨_, hx⟩) (QuotientGroup.mk ⟨_, hy⟩)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at hq
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf,
      hJmem]
    exact hq
  have h2 : ∀ g : ↥(fixSubgroup (entrywiseAdjointAut Tag.D4 σ)), IsPGroup 2 ↥(Subgroup.zpowers g) →
      g ∈ J.subgroupOf (fixSubgroup (entrywiseAdjointAut Tag.D4 σ)) := by
    intro g hg
    obtain ⟨m, hm⟩ := exists_pow_eq_one_of_isPGroup hg
    have hxΓ : ((g : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) ∈ entrywiseFixedGroup Tag.D4 σ :=
      (hfix g.1).1 g.2
    let N := (fixedFieldImage Tag.D4 σ).subgroupOf (entrywiseFixedGroup Tag.D4 σ)
    let x : ↥(entrywiseFixedGroup Tag.D4 σ) := ⟨_, hxΓ⟩
    have hx2 : x ^ (2 ^ m) = 1 := by
      apply Subtype.ext
      have h1 := congrArg (fun y : ↥(fixSubgroup (entrywiseAdjointAut Tag.D4 σ)) =>
        ((y : adjointGroup Tag.D4 K) : ModGL Tag.D4 K)) hm
      simpa using h1
    have hmem : (x : ModGL Tag.D4 K) ∈ (entrywiseFixedTorus Tag.D4 σ : Set (ModGL Tag.D4 K)) *
        (fixedFieldImage Tag.D4 σ : Set (ModGL Tag.D4 K)) := by
      rw [← hΓeq]
      exact hxΓ
    obtain ⟨t, ht, j, hj, htj⟩ := Set.mem_mul.1 hmem
    have htΓ : t ∈ entrywiseFixedGroup Tag.D4 σ := ht.2
    have hjΓ : j ∈ entrywiseFixedGroup Tag.D4 σ := hJΓ hj
    have hxeq : x = ⟨t, htΓ⟩ * ⟨j, hjΓ⟩ := Subtype.ext htj.symm
    have hjN : (⟨j, hjΓ⟩ : ↥(entrywiseFixedGroup Tag.D4 σ)) ∈ N := hj
    have hqx : (QuotientGroup.mk x : ↥(entrywiseFixedGroup Tag.D4 σ) ⧸ N) =
        QuotientGroup.mk ⟨t, htΓ⟩ := by
      rw [hxeq, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 hjN, mul_one]
    have ht1 : (⟨t, htΓ⟩ : ↥(entrywiseFixedGroup Tag.D4 σ)) ^ (Nat.card K - 1) = 1 :=
      Subtype.ext (by
        simpa using pow_card_sub_one_eq_one_of_mem_diagonalGroup (torusGroup_le_diagonalGroup ht.1))
    have hA : (QuotientGroup.mk x : ↥(entrywiseFixedGroup Tag.D4 σ) ⧸ N) ^ (2 ^ m) = 1 := by
      rw [← QuotientGroup.mk_pow, hx2, QuotientGroup.mk_one]
    have hB : (QuotientGroup.mk x : ↥(entrywiseFixedGroup Tag.D4 σ) ⧸ N) ^ (Nat.card K - 1) = 1 := by
      rw [hqx, ← QuotientGroup.mk_pow, ht1, QuotientGroup.mk_one]
    have hK2 : 2 ∣ Nat.card K := prime_dvd_card (K := K) 2
    have hK1 : 1 ≤ Nat.card K := Nat.card_pos
    have hcop : Nat.Coprime (2 ^ m) (Nat.card K - 1) :=
      Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega))
    have h1 := (pow_gcd_eq_one (a := (QuotientGroup.mk x : ↥(entrywiseFixedGroup Tag.D4 σ) ⧸ N))).2 ⟨hA, hB⟩
    rw [hcop.gcd_eq_one, pow_one, QuotientGroup.eq_one_iff] at h1
    exact Subgroup.mem_subgroupOf.2 ((hJmem _).2 h1)
  exact Or.inl ⟨_, hJn, hq, hsol, h2⟩

private theorem goodFixed_twistedEntrywiseAut_one {K : Type} [Field K] [Finite K] {ℓ e : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (he : 1 ≤ e) (hK : Nat.card K = ℓ ^ (e * 3)) (σ : K ≃+* K) (r : ℕ) (hr : r = 1 ∨ r = 2)
    (hσ : ∀ c, σ c = c ^ ((ℓ ^ e) ^ r)) :
    GoodFixed ↥(fixSubgroup (twistedEntrywiseAut TwistTag.D4 1 σ)) := by
  classical
  haveI : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  obtain ⟨-, -, hfixeq, hsimple, hnc⟩ :=
    triality_both_field_orientations_simple_full_ambient_fixed_group ℓ e Fact.out he K
      (by rw [hK, pow_mul]) (AlgebraicClosure K) r hr σ.toRingHom hσ
      (iterateFrobenius (AlgebraicClosure K) ℓ e) (fun c => by simp [iterateFrobenius_def])
  let eΓ : fixedSubgroup (twistedEntrywiseAut TwistTag.D4 1 σ) ≃*
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    (fixedSubgroupTwistedEntrywiseAutOneEquiv TwistTag.D4 σ).trans
      (MulEquiv.subgroupCongr hfixeq)
  haveI := hsimple
  exact goodFixed_of_mulEquiv eΓ
    (goodFixed_of_isQuasisimple (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1)

private theorem goodFixed_twistedEntrywiseAut_D4 {K : Type} [Field K] [Finite K] {ℓ e : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (he : 1 ≤ e) (hK : Nat.card K = ℓ ^ (e * 3)) (T : K ≃+* K) (hT : ∀ c, T c = c ^ (ℓ ^ e))
    (j : ℤ) (hj : j % 3 = 1 ∨ j % 3 = 2) :
    GoodFixed ↥(fixSubgroup (twistedEntrywiseAut TwistTag.D4 j T)) := by
  have : Fintype K := Fintype.ofFinite K
  have hq3 : ∀ c : K, c ^ ((ℓ ^ e) ^ 3) = c := fun c => by
    rw [← pow_mul, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hT3 : T ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    change T (T (T c)) = c
    rw [hT, hT, hT, ← pow_mul, ← pow_mul, show ℓ ^ e * (ℓ ^ e * ℓ ^ e) = (ℓ ^ e) ^ 3 by ring, hq3]
  have hinv : ∀ c, T⁻¹ c = c ^ ((ℓ ^ e) ^ 2) := by
    have h1 : T⁻¹ = T ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hT3)
    intro c
    rw [h1, pow_two]
    change T (T c) = _
    rw [hT, hT, ← pow_mul, sq]
  have hper : twistedEntrywiseAut TwistTag.D4 j T = twistedEntrywiseAut TwistTag.D4 (j % 3) T := by
    have h := twistedEntrywiseAut_add_mul_order TwistTag.D4 (j % 3) (j / 3) T
    rw [show j % 3 + j / 3 * ((TwistTag.D4.order : ℕ) : ℤ) = j by
      change j % 3 + j / 3 * 3 = j
      omega] at h
    exact h
  rw [hper]
  rcases hj with h | h
  · rw [h]
    exact goodFixed_twistedEntrywiseAut_one he hK T 1 (Or.inl rfl) (fun c => by rw [hT, pow_one])
  · rw [h]
    exact goodFixed_of_mulEquiv (MulEquiv.subgroupCongr (fixedSubgroup_twistedEntrywiseAut_D4_two T))
      (goodFixed_twistedEntrywiseAut_one he hK T⁻¹ 2 (Or.inr rfl) hinv)

private theorem goodFixed_of_lang {K : Type} [Field K] [Finite K] {ℓ e : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (he : 1 ≤ e) (hK : Nat.card K = ℓ ^ (e * 3)) (T : K ≃+* K) (hT : ∀ c, T c = c ^ (ℓ ^ e))
    (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K)
    (hσT : σ = T ∨ σ = T⁻¹) (ε : ℕ)
    (hP : ∀ j : ℤ, (j = (ε : ℤ) ∨ j = -(ε : ℤ)) →
      GoodFixed ↥(fixSubgroup (twistedEntrywiseAut TwistTag.D4 j T)))
    (hα : (MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) ^ 3 = 1) :
    GoodFixed ↥(fixSubgroup (MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε))) := by
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ ℓ ^ 2 := Nat.pow_le_pow_left (Fact.out : ℓ.Prime).two_le 2
      _ ≤ ℓ ^ (e * 3) := Nat.pow_le_pow_right (Fact.out : ℓ.Prime).pos (by omega)
  set α := MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε) with hαdef
  rcases hσT with hσT | hσT
  · subst hσT
    obtain ⟨ψ, hψ⟩ := exists_conj_eq_twistedEntrywiseAut_of_normalForm K hK hK4 he rfl σ hT α hα
      g a ε hαdef
    exact goodFixed_of_conj_eq hψ (hP _ (Or.inl rfl))
  · subst hσT
    obtain ⟨ψ, hψ⟩ := exists_conj_inv_eq_twistedEntrywiseAut_of_normalForm K hK hK4 he rfl T T⁻¹
      hT (mul_inv_cancel T) α hα g a ε hαdef
    have h := goodFixed_of_inv (goodFixed_of_conj_eq hψ (hP _ (Or.inr rfl)))
    rwa [inv_inv] at h

set_option linter.unusedSectionVars false in
private theorem d4Graph_zero_eq {K : Type} [Field K] [Finite K] : d4Graph K 0 = 1 := by
  ext h
  simp [coe_d4Graph]

private theorem goodFixed_d4_field {K : Type} [Field K] [Finite K] [hc2 : CharP K 2]
    (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (hσ : σ ≠ 1) (hσ3 : σ ^ 3 = 1)
    (hα : (MulAut.conj g * exactNormalAut Tag.D4 K a σ 0) ^ 3 = 1) :
    GoodFixed ↥(fixSubgroup (MulAut.conj g * exactNormalAut Tag.D4 K a σ 0)) := by
  obtain ⟨ℓ, e, T, hℓ, hchar, he, hK, hT, hσT⟩ := exists_frobenius_data' σ hσ hσ3
  obtain rfl : ℓ = 2 := CharP.eq K hchar hc2
  haveI : Fact (Nat.Prime 2) := ⟨hℓ⟩
  have hα' : (MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K 0)) ^ 3 = 1 := by
    rwa [d4Graph_zero_eq, mul_one]
  have h := goodFixed_of_lang he hK T hT g a σ hσT 0 (fun j hj => ?_) hα'
  · rwa [d4Graph_zero_eq, mul_one] at h
  · have hj0 : j = 0 := by rcases hj with h | h <;> simpa using h
    subst hj0
    have e0 : twistedEntrywiseAut TwistTag.D4 0 T = entrywiseAdjointAut Tag.D4 T := by
      unfold twistedEntrywiseAut
      rw [zpow_zero, one_mul]
      rfl
    rw [e0]
    exact goodFixed_entrywiseAdjointAut_D4 T

private theorem goodFixed_d4_graphField {K : Type} [Field K] [Finite K] (g : adjointGroup Tag.D4 K)
    (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (hσ : σ ≠ 1) (hσ3 : σ ^ 3 = 1) {ε : ℕ}
    (hε : ε = 1 ∨ ε = 2)
    (hα : (MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) ^ 3 = 1) :
    GoodFixed ↥(fixSubgroup (MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε))) := by
  obtain ⟨ℓ, e, T, hℓ, hchar, he, hK, hT, hσT⟩ :=
    exists_frobenius_data' σ hσ hσ3
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  refine goodFixed_of_lang he hK T hT g a σ hσT ε (fun j hj => ?_) hα
  refine goodFixed_twistedEntrywiseAut_D4 he hK T hT j ?_
  rcases hε with rfl | rfl <;> rcases hj with rfl | rfl <;> omega


private theorem goodFixed_adjointGroup_G2 (k : Type) [Field k] [Finite k] :
    GoodFixed ↥(adjointGroup Tag.G2 k) := by
  by_cases hk : 3 ≤ Nat.card k
  · exact goodFixed_of_isQuasisimple (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card k hk)
  · have h2 : Nat.card k = 2 := by
      have := Finite.one_lt_card (α := k)
      omega
    right
    intro P _
    have : Finite (ModGL Tag.G2 k) := finite_modGL
    have h1 : Nat.card ↥P ≤ Nat.card ↥(adjointGroup Tag.G2 k) := Subgroup.card_le_card_group P
    have h3 : Nat.card ↥(adjointGroup Tag.G2 k) = 12096 := by
      rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, h2]
      rfl
    omega

private theorem goodFixed_fieldActor_two {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hK : Nat.card K = (2 ^ f) ^ 3) : GoodFixed ↥(fixSubgroup (fieldActor (t := TwistTag.D4) σ σ)) := by
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK3
  have hK2 : ringChar K = 2 := ringChar.eq K 2
  obtain ⟨e⟩ := CFSG.RankThree.PartTwo.KFacts.nonempty_fixedPoints_fieldActor_mulEquiv_g2 (σ := σ) hK2
  have hfix : fixSubgroup (fieldActor (t := TwistTag.D4) σ σ) =
      (fieldActor (t := TwistTag.D4) σ σ).toMonoidHom.eqLocus (MonoidHom.id _) :=
    Subgroup.ext fun _ => Iff.rfl
  exact goodFixed_of_mulEquiv ((MulEquiv.subgroupCongr hfix).trans e) (goodFixed_adjointGroup_G2 _)


theorem goodFixed_triality_outer_even {f : ℕ} (hf : 1 ≤ f) {K₃ : Type} [Field K₃] [Finite K₃]
    (hK₃ : Nat.card K₃ = (2 ^ f) ^ 3) (Fr : K₃ ≃+* K₃) (hFr : ∀ c, Fr c = c ^ (2 ^ f))
    (φ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)) (hφ3 : φ ^ 3 = 1)
    (hφ : φ ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)).range) :
    GoodFixed ↥(fixSubgroup φ) := by
  have hG2 := goodFixed_fieldActor_two hf Fr hK₃
  rcases CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.isStdGraphFieldConj_or_nonempty_autFix_equiv hf hK₃ hFr
      hφ3 hφ with ⟨β, hβ | hβ⟩ | he₂
  · exact goodFixed_of_conj_eq (ψ := β⁻¹) (by rw [hβ]; group) hG2
  · exact goodFixed_of_conj_eq (ψ := β⁻¹) (by rw [hβ]; group) (goodFixed_of_inv hG2)
  · obtain ⟨e₂⟩ := he₂
    have hfixφ : fixSubgroup φ = Sec4.autFix φ := Subgroup.ext fun _ => Iff.rfl
    let ef : ↥(fixSubgroup φ) ≃* ↥(Sec4.autFix φ) := MulEquiv.subgroupCongr hfixφ
    rcases Nat.even_or_odd f with hfe | hfo
    · obtain ⟨F, _, _, hF, ⟨e₃⟩⟩ :=
        CFSG.RankThree.PartTwo.Sec8.kF82D4SecondCentY0Even_holds f hfe hf K₃ Fr hK₃ hFr
      have hPi : Sec4.PiField true 2 f F := ⟨Nat.prime_two, hf, hF⟩
      have hf2 : 2 ≤ f := by
        obtain ⟨k, hk⟩ := hfe
        omega
      have h2 : 2 < 2 ^ f := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf2)
      exact goodFixed_of_mulEquiv (ef.trans (e₂.trans e₃)) (goodFixed_projImage_glPi hPi fun _ => h2)
    · obtain ⟨F, _, _, hF, ⟨e₃⟩⟩ := CFSG.RankThree.PartTwo.Sec8.kF82D4SecondCentY0_holds f hfo K₃ Fr hK₃ hFr
      have hPi : Sec4.PiField false 2 f F := ⟨Nat.prime_two, hf, hF⟩
      exact goodFixed_of_mulEquiv (ef.trans (e₂.trans e₃))
        (goodFixed_projImage_glPi hPi fun h => absurd h (by decide))

private theorem goodFixed_d4_graph {K : Type} [Field K] [Finite K] [CharP K 2] (g : adjointGroup Tag.D4 K)
    (a : Fin Tag.D4.rank → Kˣ) {ε : ℕ} (hε : ε = 1 ∨ ε = 2)
    (hα : (MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K ε)) ^ 3 = 1) :
    GoodFixed ↥(fixSubgroup (MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K ε))) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  obtain ⟨K₃, _, _, Fr, hK₃, hFr, φ, hφ3, hφout, ⟨e⟩⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual.exists_dual_fixEquiv n.pos K hK _ hα g a
      hε rfl
  exact goodFixed_of_mulEquiv e (goodFixed_triality_outer_even n.pos hK₃ Fr hFr φ hφ3 hφout)

private theorem goodFixed_d4_adjoint {F : Type} [Field F] [Finite F] [CharP F 2]
    (α : MulAut ↥(adjointGroup Tag.D4 F)) (hα : α ^ 3 = 1)
    (hout : ∀ h : ↥(adjointGroup Tag.D4 F), MulAut.conj h ≠ α) : GoodFixed ↥(fixSubgroup α) := by
  have hchar : ringChar F ≠ 3 := by
    rw [ringChar.eq F 2]
    norm_num
  obtain ⟨g, a, σ, ε, hε, hσ3, rfl⟩ := exists_cube_normal_form_sigma α hα
  interval_cases ε
  · rw [d4Graph_zero_eq, mul_one] at hα hout ⊢
    by_cases hσ1 : σ = 1
    · subst hσ1
      obtain ⟨h, hh⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.d4_inner_of_diag hchar g a hα
      exact absurd hh.symm (hout h)
    · exact goodFixed_d4_field g a σ hσ1 hσ3 hα
  · by_cases hσ1 : σ = 1
    · subst hσ1
      exact goodFixed_d4_graph g a (Or.inl rfl) hα
    · exact goodFixed_d4_graphField g a σ hσ1 hσ3 (Or.inl rfl) hα
  · by_cases hσ1 : σ = 1
    · subst hσ1
      exact goodFixed_d4_graph g a (Or.inr rfl) hα
    · exact goodFixed_d4_graphField g a σ hσ1 hσ3 (Or.inr rfl) hα


private theorem goodFixed_d4_outer {G : Type} [Group G] [Finite G] {f : ℕ}
    (hG : CFSG.Open.StatedClassicalModel G CFSG.Open.StatedLieTag.POmegaPlus 4 2 f) (β : MulAut G)
    (hβ : β ^ 3 = 1) (hout : ∀ a : G, MulAut.conj a ≠ β) : GoodFixed ↥(fixSubgroup β) := by
  obtain ⟨⟨-, hf, -⟩, F, _, _, hF, ⟨eG⟩⟩ := hG
  obtain ⟨eC⟩ := CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup F
  let e₂ : G ≃* ↥(adjointGroup Tag.D4 F) := eG.trans eC
  have : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hF
  have hα : MulAut.congr e₂ β ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
  have hout' : ∀ h : ↥(adjointGroup Tag.D4 F), MulAut.conj h ≠ MulAut.congr e₂ β := by
    intro h hh
    apply hout (e₂.symm h)
    ext x
    have h1 := congrArg (fun φ : MulAut ↥(adjointGroup Tag.D4 F) => e₂.symm (φ (e₂ x))) hh
    simp only [MulAut.congr_apply, MulAut.conj_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      map_mul, map_inv] at h1
    rw [MulAut.conj_apply]
    exact h1
  have key := goodFixed_d4_adjoint (MulAut.congr e₂ β) hα hout'
  rw [Inputs141c.fixSubgroup_congr] at key
  exact goodFixed_of_mulEquiv ((fixSubgroup β).equivMapOfInjective e₂.toMonoidHom e₂.injective) key

theorem d4OuterCore_holds : D4OuterCore := by
  intro G _ _ f hG β hβ3 hβout J hJ hJt k hk hk2
  exact inducesInner_of_structAt hJ
    (structAt_of_goodFixed (goodFixed_d4_outer hG β hβ3 hβout) hJ (card_dvd_of_isLThreeFour hJt)) hk hk2

end D4Outer

section Rest

theorem input14_1CoreFor_symplecticOrthogonal_of_orthogonal
    (hO : Input14_1CoreFor fun d => ∃ r q, d = TauCeti.LieTypeIndex.D r q ∨ d = TauCeti.LieTypeIndex.twistedD r q) :
    Input14_1CoreFor fun d =>
      CFSG.Yardstones.Md42047359a2a.lieFamily d = CFSG.Yardstones.Md42047359a2a.LieFamily.symplecticOrthogonal := by
  intro S _ _ hS hnc d hd hchar
  obtain ⟨d, hv⟩ := d
  cases d with
  | B r q =>
    have hq2 : q.p = 2 := by
      have h1 : (TauCeti.LieTypeIndex.B r q).characteristic = q.p := TauCeti.LieTypeIndex.characteristic_B r q
      rw [← h1]
      exact hchar
    exact input14_1CoreFor_of_struct input14_1StructFor_symplectic S hS hnc ⟨_, hv⟩
      (Or.inl ⟨r, q, rfl, Or.inl hq2⟩) hchar
  | C r q =>
    exact input14_1CoreFor_of_struct input14_1StructFor_symplectic S hS hnc ⟨_, hv⟩ (Or.inr ⟨r, q, rfl⟩) hchar
  | D r q => exact hO S hS hnc ⟨_, hv⟩ ⟨r, q, Or.inl rfl⟩ hchar
  | twistedD r q => exact hO S hS hnc ⟨_, hv⟩ ⟨r, q, Or.inr rfl⟩ hchar
  | _ => simp [CFSG.Yardstones.Md42047359a2a.lieFamily] at hd

theorem input14_1CoreFor_symplecticOrthogonal (hD4 : D4OuterCore) :
    Input14_1CoreFor fun d =>
      CFSG.Yardstones.Md42047359a2a.lieFamily d = CFSG.Yardstones.Md42047359a2a.LieFamily.symplecticOrthogonal :=
  input14_1CoreFor_symplecticOrthogonal_of_orthogonal (input14_1CoreFor_orthogonal hD4)

theorem input14_1CoreRest_of_D4_exceptional (hD4 : D4OuterCore)
    (hE : Input14_1CoreFor fun d =>
      CFSG.Yardstones.Md42047359a2a.lieFamily d = CFSG.Yardstones.Md42047359a2a.LieFamily.exceptional) :
    Inputs141c.Input14_1CoreRest :=
  ⟨input14_1CoreFor_unitary, input14_1CoreFor_symplecticOrthogonal hD4, hE⟩

theorem input14_1CoreRest_of_exceptional
    (hE : Input14_1CoreFor fun d =>
      CFSG.Yardstones.Md42047359a2a.lieFamily d = CFSG.Yardstones.Md42047359a2a.LieFamily.exceptional) :
    Inputs141c.Input14_1CoreRest :=
  input14_1CoreRest_of_D4_exceptional d4OuterCore_holds hE


@[expose] def Input14_1CoreExc : Prop :=
  Inputs141c.Input14_1CoreFor fun d =>
    CFSG.Yardstones.Md42047359a2a.lieFamily d = CFSG.Yardstones.Md42047359a2a.LieFamily.exceptional

end Rest

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141d

end
