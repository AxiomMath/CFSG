module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenNineWIndex
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexFiveUnitary
import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Unitary
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexFiveBlockOK

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.FieldIndexW

open Matrix CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
open CFSG.RankThree.PartOne.OutStructure (exists_pow_eq_of_pow_eq ringAut_comm)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndexP
open CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus (IsWBlock)
open scoped Pointwise commutatorElement

section LeviData

variable {f t s ε : ℕ} {K : Type} [Field K]

theorem blockOK_gu_suP_of_ne_bot {p : ℕ} [OddPrime p] (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1)
    (hne : hypSU h s ε ≠ ⊥) : BlockOKP p (hypUnitary h s ε) (hypSU h s ε) := by
  classical
  haveI : Finite K := h.finite
  have hm2 : 2 ≤ 2 * s + ε := by
    by_contra hlt
    have hs0 : s = 0 := by omega
    subst hs0
    haveI := subsingleton_hypSU_zero h hε
    exact hne (Subgroup.eq_bot_of_subsingleton _)
  intro g hg _ k hk
  by_cases hdiv : p ∣ Nat.gcd (2 * s + ε) (2 ^ f + 1)
  · right
    have h3m : p ∣ 2 * s + ε := hdiv.trans (Nat.gcd_dvd_left _ _)
    have := Nat.le_of_dvd (by omega) h3m
    have := OddPrime.three_le p
    exact uniExists_elemAbelian_sq_su (by omega) (hdiv.trans (Nat.gcd_dvd_right _ _))
  · left
    have hr : 1 ≤ s := by omega
    have hgk : g ^ (p ^ k) ∈ hypUnitary h s ε := pow_mem hg _
    obtain ⟨c, hc⟩ := uniScalar_of_centralizes h hε hm2 hgk hk
    have hcn : h.norm (c : K) = 1 := uniNorm_eq_one_of_scalar hr (hc ▸ hgk)
    have hδ : h.norm ((GeneralLinearGroup.det g : Kˣ) : K) = 1 := by
      rw [GeneralLinearGroup.val_det_apply]
      exact uniNorm_det_eq_one hg
    have hdu : (GeneralLinearGroup.det g : Kˣ) ^ (p ^ k) = c ^ (2 * s + ε) := by
      rw [← map_pow, hc, uniDet_scalar]
    obtain ⟨μ, hμn, hμ⟩ := uniExists_pow_eq_normOneP h hdiv hδ hcn hdu
    have hμ'n : h.norm ((μ⁻¹ : Kˣ) : K) = 1 := by
      rw [Units.val_inv_eq_inv_val, norm_inv_eq h, hμn, inv_one]
    have hp1 : (GeneralLinearGroup.scalar (HypIndex s ε) μ⁻¹ * g : GL (HypIndex s ε) K) ∈
        hypUnitary h s ε := mul_mem (uniScalar_mem_hypUnitary hμ'n) hg
    have hdetp : GeneralLinearGroup.det
        (GeneralLinearGroup.scalar (HypIndex s ε) μ⁻¹ * g : GL (HypIndex s ε) K) = 1 := by
      rw [map_mul, uniDet_scalar, inv_pow, hμ, inv_mul_cancel]
    have hpS : (GeneralLinearGroup.scalar (HypIndex s ε) μ⁻¹ * g : GL (HypIndex s ε) K) ∈
        hypSU h s ε := by
      refine ⟨mem_hypUnitary.1 hp1, ?_⟩
      rw [← GeneralLinearGroup.val_det_apply, hdetp, Units.val_one]
    refine ⟨_, hpS, fun y _ => ?_⟩
    have hgp : g = GeneralLinearGroup.scalar (HypIndex s ε) μ *
        (GeneralLinearGroup.scalar (HypIndex s ε) μ⁻¹ * g) := by
      rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
    have hc' := (commute_scalar μ (GeneralLinearGroup.scalar (HypIndex s ε) μ⁻¹ * g * y *
      (GeneralLinearGroup.scalar (HypIndex s ε) μ⁻¹ * g)⁻¹)).eq
    calc g * y * g⁻¹ = (GeneralLinearGroup.scalar (HypIndex s ε) μ *
          (GeneralLinearGroup.scalar (HypIndex s ε) μ⁻¹ * g)) * y *
          (GeneralLinearGroup.scalar (HypIndex s ε) μ *
            (GeneralLinearGroup.scalar (HypIndex s ε) μ⁻¹ * g))⁻¹ := by rw [← hgp]
      _ = GeneralLinearGroup.scalar (HypIndex s ε) μ *
          ((GeneralLinearGroup.scalar (HypIndex s ε) μ⁻¹ * g) * y *
            (GeneralLinearGroup.scalar (HypIndex s ε) μ⁻¹ * g)⁻¹) *
          (GeneralLinearGroup.scalar (HypIndex s ε) μ)⁻¹ := by group
      _ = (GeneralLinearGroup.scalar (HypIndex s ε) μ⁻¹ * g) * y *
            (GeneralLinearGroup.scalar (HypIndex s ε) μ⁻¹ * g)⁻¹ := by
          rw [← hc']
          group

theorem uniBlockOKPW {p : ℕ} [OddPrime p] (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1)
    {I : Finset ℕ} (j : Option ↥I) (hne : uniBlockSub (s := s) (ε := ε) h I j ≠ ⊥) :
    BlockOKP p (uniBlockH h s ε I j) (uniBlockSub (s := s) (ε := ε) h I j) := by
  haveI : Finite K := h.finite
  haveI : CharP K 2 := h.charP
  rcases j with _ | b
  · exact blockOK_gu_suP_of_ne_bot h hε hne
  · have h4 := four_le_card_of_unitaryFieldData_two h
    rcases ParabCensus.range_toGL_cases (K := K) (b.1 - predCut I b.1) with h1 | h2 | ⟨hq, -⟩
    · exact absurd h1 hne
    · exact absurd h2.1 (by omega)
    · exact blockOK_gl_slP _ (two_le_of_isQuasisimple_specialLinear
        (isQuasisimple_of_mulEquiv (slEquivToGLRange (K := K) _).symm hq))

theorem uniBlockSub_eq_bot_or_isWBlock (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1)
    {I : Finset ℕ} (hI : IsTopCut I t) (j : Option ↥I) :
    uniBlockSub (s := s) (ε := ε) h I j = ⊥ ∨
      IsWBlock ↥(uniBlockSub (s := s) (ε := ε) h I j) := by
  rcases j with _ | b
  · exact ParabCensus.hypSU_eq_bot_or_isWBlock h hε s
  · exact ParabCensus.uniBlockSub_some_eq_bot_or_isWBlock h hε hI b

theorem odd_relIndex_uniLeviHom (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1) {I : Finset ℕ}
    (hI : IsTopCut I t) :
    Odd ((Subgroup.pi Set.univ (uniBlockSub (s := s) (ε := ε) h I)).relIndex
      (uniLeviHom h hε hI).range) := by
  haveI : Finite K := h.finite
  haveI : CharP K 2 := h.charP
  refine Nat.not_even_iff_odd.mp fun he => ?_
  refine ParabCensus.not_two_dvd_relIndex_pi_of_finite (T := uniBlockH h s ε I) ?_
    (pi_uniBlockSub_le_range h hε hI) ?_ ?_ (even_iff_two_dvd.mp he)
  · intro j
    rcases j with _ | b
    · exact hypSU_le_hypUnitary h
    · exact le_top
  · rintro _ ⟨z, rfl⟩
    rw [Subgroup.mem_pi]
    exact fun j _ => uniLeviHom_mem_H h hε hI z j
  · intro j
    rcases j with _ | b
    · exact (ParabCensus.odd_relIndex_hypSU_hypUnitary h s ε).not_two_dvd_nat
    · change ¬ 2 ∣ ((Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin (b.1 - predCut I b.1)) K →*
          GL (Fin (b.1 - predCut I b.1)) K).range).relIndex ⊤
      rw [Subgroup.relIndex_top_right]
      exact ParabCensus.not_two_dvd_index_range_toGL _

theorem uniConj_mem_blockSub (h : UnitaryFieldData 2 f K) {I : Finset ℕ} (j : Option ↥I)
    {g x : uniBlockGroup K s ε I j} (hg : g ∈ uniBlockH h s ε I j)
    (hx : x ∈ uniBlockSub (s := s) (ε := ε) h I j) :
    g * x * g⁻¹ ∈ uniBlockSub (s := s) (ε := ε) h I j := by
  rcases j with _ | b
  · change g ∈ hypUnitary h s ε at hg
    change x ∈ hypSU h s ε at hx
    change g * x * g⁻¹ ∈ hypSU h s ε
    have hu : g * x * g⁻¹ ∈ hypUnitary h s ε :=
      mul_mem (mul_mem hg (hypSU_le_hypUnitary h hx)) (inv_mem hg)
    have hdx : GeneralLinearGroup.det x = 1 :=
      Units.ext (by rw [GeneralLinearGroup.val_det_apply]; exact hx.2)
    refine ⟨mem_hypUnitary.1 hu, ?_⟩
    rw [← GeneralLinearGroup.val_det_apply, map_mul, map_mul, hdx, mul_one, map_inv,
      mul_inv_cancel, Units.val_one]
  · have hN : (SpecialLinearGroup.toGL :
        SpecialLinearGroup (Fin (b.1 - predCut I b.1)) K →* GL _ K).range.Normal := by
      rw [SpecialLinearGroup.range_toGL_eq_ker_det]
      infer_instance
    exact hN.conj_mem x hx g

theorem uniOdd_card_ker {M : Type*} [Group M] (h : UnitaryFieldData 2 f K) {r : ℕ}
    (hn : 1 ≤ 2 * r + ε) (ρ : hypSU h r ε →* M) (hker : ρ.ker ≤ hypScalars h r ε) :
    Odd (Nat.card ρ.ker) := by
  have hodd : Odd (2 ^ f + 1) :=
    ((Nat.even_pow' (by have := h.one_le; omega)).2 even_two).add_one
  have hdvd : Nat.card ρ.ker ∣ Nat.card (hypScalars h r ε) := Subgroup.card_dvd_of_le hker
  rw [card_hypScalars h hn] at hdvd
  exact Odd.of_dvd_nat hodd (hdvd.trans (Nat.gcd_dvd_right _ _))

theorem uniHZW {Y : Type} [Group Y] {L : Subgroup Y} (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1)
    {I : Finset ℕ} (hI : IsTopCut I t) (ρ : hypSU h (t + s) ε →* ↥L)
    (hZ : ∀ y, ρ y ∈ Subgroup.center ↥L ↔ y ∈ hypScalars h (t + s) ε) (j : Option ↥I)
    (hq : ¬ CFSG.Open.IsQuasisimple ↥(uniBlockSub (s := s) (ε := ε) h I j))
    (x : ↥(flagStabilizer h (t + s) ε ↑I)) (hρx : ρ (x : hypSU h (t + s) ε) = 1)
    (hβx : uniLeviHom h hε hI x ∈
      (uniBlockSub (s := s) (ε := ε) h I j).map (MonoidHom.mulSingle (uniBlockGroup K s ε I) j)) :
    uniLeviHom h hε hI x = 1 := by
  haveI : Finite K := h.finite
  haveI : CharP K 2 := h.charP
  rcases j with _ | b
  · have hxs : (x : hypSU h (t + s) ε) ∈ hypScalars h (t + s) ε :=
      (hZ _).1 (by rw [hρx]; exact Subgroup.one_mem _)
    have hone : ∀ b : ↥I, uniLeviHom h hε hI x (some b) = 1 := by
      intro b
      obtain ⟨y, -, hyx⟩ := hβx
      rw [← hyx]
      exact Pi.mulSingle_eq_of_ne (M := uniBlockGroup K s ε I) (Option.some_ne_none b) y
    rw [ParabCensus.eq_one_of_mem_hypScalars_of_some_eq_one h hε hI x hxs hone, map_one]
  · have hbot : uniBlockSub (s := s) (ε := ε) h I (some b) = ⊥ := by
      have h4 := four_le_card_of_unitaryFieldData_two h
      rcases ParabCensus.range_toGL_cases (K := K) (b.1 - predCut I b.1) with h1 | h2 | h3
      · exact h1
      · exact absurd h2.1 (by omega)
      · exact absurd h3.1 hq
    rw [hbot, Subgroup.map_bot, Subgroup.mem_bot] at hβx
    exact hβx

theorem uniActsInnerlyW_of_compatP {p : ℕ} [OddPrime p]
    {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y} [L.Normal] (hCP : CompParab L P)
    (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1) {I : Finset ℕ} (hI : IsTopCut I t)
    (ρ : hypSU h (t + s) ε →* ↥L) (hρs : Function.Surjective ρ)
    (hZ : ∀ y, ρ y ∈ Subgroup.center ↥L ↔ y ∈ hypScalars h (t + s) ε)
    (hcomap : (P.subgroupOf L).comap ρ = flagStabilizer h (t + s) ε ↑I)
    (hrankp : Open.pRank p L ≤ 3)
    {A : GL (HypIndex (t + s) ε) K} (hA : A ∈ hypUnitary h (t + s) ε) {a : Y}
    (haN : a ∈ Subgroup.normalizer (P : Set Y))
    (hcm : ∀ y : hypSU h (t + s) ε, (MulAut.conjNormal a : MulAut ↥L) (ρ y) *
      (ρ (uniConjSU A hA y))⁻¹ ∈ Subgroup.center ↥L)
    (hpow : ∃ m : ℕ, ∀ w ∈ wPre P, a ^ (p ^ m) * w = w * a ^ (p ^ m))
    (hrk : Open.pRank p (wPre P) ≤ 1) :
    ∃ v ∈ wPre P, ∀ w ∈ wPre P, ⁅a * v, w⁆ ∈ pCoreOf 2 P := by
  classical
  haveI : Finite K := h.finite
  have ht1 : 1 ≤ t := (hI.le t hI.mem).1
  have hr : 0 < t + s := by omega
  have hIr : ∀ c ∈ (↑I : Set ℕ), c ≤ t + s := fun c hc =>
    (hI.le c hc).2.trans (Nat.le_add_right t s)
  set Q := flagStabilizer h (t + s) ε ↑I with hQdef
  have hmemQ : ∀ x : hypSU h (t + s) ε, x ∈ Q ↔ ((ρ x : ↥L) : Y) ∈ P := fun x => by
    rw [← hcomap]
    rfl
  have hQA : ∀ x ∈ Q, uniConjSU A hA x ∈ Q := by
    intro x hx
    rw [hmemQ] at hx ⊢
    have h1 := hcm x
    have h2 : ρ (uniConjSU A hA x) = ((MulAut.conjNormal a : MulAut ↥L) (ρ x) *
        (ρ (uniConjSU A hA x))⁻¹)⁻¹ * (MulAut.conjNormal a : MulAut ↥L) (ρ x) := by group
    rw [h2]
    exact P.mul_mem (uniCenter_le_of_compParab hCP (Subgroup.inv_mem _ h1))
      ((Subgroup.mem_normalizer_iff.1 haN _).1 hx)
  set δ : Kˣ := GeneralLinearGroup.det A with hδ
  have hδn : h.norm (δ : K) = 1 := by
    rw [hδ, GeneralLinearGroup.val_det_apply]
    exact uniNorm_det_eq_one hA
  obtain ⟨a₀, ha₀⟩ := uniHilbert90 h hδn
  let i₀ : Fin (t + s) := ⟨0, hr⟩
  let a' : Fin (t + s) → Kˣ := fun i => if i = i₀ then a₀ else 1
  let d : HypIndex (t + s) ε → Kˣ := uniTorusUnits h a'
  let D : GL (HypIndex (t + s) ε) K := uniDiagGL d
  have hDd : D = uniDiagGL d := rfl
  have hD : D ∈ hypUnitary h (t + s) ε := uniDiagGL_torus_mem_hypUnitary a'
  have hdetD : GeneralLinearGroup.det D = δ := by
    rw [hDd, uniDiagGL_det]
    show ∏ x : HypIndex (t + s) ε, uniTorusUnits h a' x = δ
    rw [prod_uniTorusUnits]
    have e1 : ∏ i, a' i = a₀ := by simp [a']
    have e2 : ∏ i, (Units.map (h.bar : K →* K) (a' i))⁻¹ =
        (Units.map (h.bar : K →* K) a₀)⁻¹ := by
      simp [a', apply_ite]
    rw [e1, e2]
    exact ha₀
  have hD' : D⁻¹ ∈ hypUnitary h (t + s) ε := (hypUnitary h (t + s) ε).inv_mem hD
  have hs₀ : A * D⁻¹ ∈ hypSU h (t + s) ε := by
    refine ⟨mem_hypUnitary.1 ((hypUnitary h (t + s) ε).mul_mem hA hD'), ?_⟩
    rw [← GeneralLinearGroup.val_det_apply, map_mul, map_inv, hdetD, mul_inv_cancel,
      Units.val_one]
  let s₁ : hypSU h (t + s) ε := ⟨A * D⁻¹, hs₀⟩
  have hAs : A = (s₁ : GL (HypIndex (t + s) ε) K) * D := by
    simp [s₁]
  have hdQ : ∀ x ∈ Q, uniConjSU D hD x ∈ Q := fun x hx =>
    uniDiag_conj_mem_flagStabilizer hε hIr d hDd hD hx
  have hdQ' : ∀ x ∈ Q, uniConjSU D⁻¹ hD' x ∈ Q := fun x hx =>
    uniDiag_conj_mem_flagStabilizer hε hIr d⁻¹ (uniDiagGL_inv d) hD' hx
  have hs₁N : ∀ x ∈ Q, s₁ * x * s₁⁻¹ ∈ Q := by
    intro x hx
    have e : s₁ * x * s₁⁻¹ = uniConjSU A hA (uniConjSU D⁻¹ hD' x) :=
      Subtype.ext (by simp [s₁, uniConjSU_coe, mul_assoc])
    rw [e]
    exact hQA _ (hdQ' x hx)
  have hs₁Q : s₁ ∈ Q := uniMem_of_normalizes_coverSub hCP ρ hρs hcomap.symm hs₁N
  let φ₀ : ↥Q →* ↥Q := ((uniConjSU A hA).toMonoidHom.comp Q.subtype).codRestrict Q
    fun x => hQA x x.2
  have hφinj : Function.Injective φ₀ := fun x y hxy =>
    Subtype.ext ((uniConjSU A hA).injective (congrArg Subtype.val hxy))
  have hφsurj : Function.Surjective φ₀ := Finite.injective_iff_surjective.1 hφinj
  let φ : MulAut ↥Q := MulEquiv.ofBijective φ₀ ⟨hφinj, hφsurj⟩
  have hφval : ∀ x : ↥Q, ((φ x : ↥Q) : hypSU h (t + s) ε) =
      uniConjSU A hA (x : hypSU h (t + s) ε) := fun x => rfl
  let g : ∀ j : Option ↥I, uniBlockGroup K s ε I j :=
    uniLeviHom h hε hI ⟨s₁, hs₁Q⟩ * uniDiagBlocks hI d
  have hdres : (d ∘ resIdx t : HypIndex s ε → Kˣ) = fun _ => 1 := by
    funext y
    have hne : ∀ i : Fin s, (Fin.natAdd t i : Fin (t + s)) ≠ i₀ := fun i hi => by
      have := congrArg Fin.val hi
      simp [i₀] at this
      omega
    rcases y with i | k | i
    · simp [d, uniTorusUnits, resIdx, a', hne i]
    · simp [d, uniTorusUnits, resIdx]
    · simp [d, uniTorusUnits, resIdx, a', hne i]
  have hg : ∀ j, g j ∈ uniBlockH h s ε I j := by
    intro j
    rcases j with _ | b
    · have h1 := uniLeviHom_mem_H h hε hI ⟨s₁, hs₁Q⟩ none
      have h2 : uniDiagBlocks hI d none = 1 := by
        change uniDiagGL (d ∘ resIdx t) = 1
        rw [hdres]
        exact uniDiagGL_one
      show uniLeviHom h hε hI ⟨s₁, hs₁Q⟩ none * uniDiagBlocks hI d none ∈ _
      rw [h2, mul_one]
      exact h1
    · exact Subgroup.mem_top _
  have hφ : ∀ x : ↥Q, uniLeviHom h hε hI (φ x) = g * uniLeviHom h hε hI x * g⁻¹ := by
    intro x
    have hxD := hdQ x x.2
    have e1 : φ x = ⟨s₁, hs₁Q⟩ * ⟨uniConjSU D hD x, hxD⟩ * ⟨s₁, hs₁Q⟩⁻¹ := by
      apply Subtype.ext
      apply Subtype.ext
      simp only [hφval, uniConjSU_coe, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hAs]
      group
    rw [e1, map_mul, map_mul, map_inv, uniLeviHom_conj_diag h hε hI d hDd hD x hxD]
    simp only [g]
    group
  have hker : ρ.ker ≤ Subgroup.center (hypSU h (t + s) ε) := fun y hy =>
    normOneScalars_le_center h _ _
      ((hZ y).1 (by rw [MonoidHom.mem_ker.1 hy]; exact Subgroup.one_mem _))
  exact actsInnerlyW_of_levi_data_index (OddPrime.ne_two p) hCP.parab.1 hCP.odd ρ hρs hker
    (uniOdd_card_ker h (by omega) ρ fun y hy =>
      (hZ y).1 (by rw [MonoidHom.mem_ker.1 hy]; exact Subgroup.one_mem _))
    Q hcomap.symm
    (G := uniBlockGroup K s ε I) (uniBlockSub (s := s) (ε := ε) h I) (uniBlockH h s ε I)
    (uniLeviHom h hε hI) (isPGroup_ker_uniLeviHom h hε hI) (pi_uniBlockSub_le_range h hε hI)
    (commutator_range_le_pi h hε hI) (odd_relIndex_uniLeviHom h hε hI)
    (uniBlockSub_eq_bot_or_isWBlock h hε hI) (fun j hj => uniBlockOKPW h hε j hj)
    (fun j E hES hE hcard x hρx hβx => uniHZP h hε hI ρ hZ hrankp j E hES hE hcard x hρx hβx)
    (fun j hq x hρx hβx => uniHZW h hε hI ρ hZ j hq x hρx hβx)
    φ g hg hφ (fun j x hx => uniConj_mem_blockSub h j (hg j) hx) haN (fun x => hcm x) hpow hrk

end LeviData

theorem fieldIndexOnPW_unitary (p : ℕ) [OddPrime p] :
    FieldIndexOnPW p (IsLieOf IdxTwistedA) := by
  intro Y _ _ L P hCP hC hLn hrank h3 hrk a ha3 haN hout
  haveI := hLn
  obtain ⟨K, hK, f, t, s, ε, h, ρ, I, hε, hI, hn3, hnq, hρs, hZ, hcomap⟩ :=
    exists_uniCover_std hCP hC
  haveI : Finite K := h.finite
  have ht1 : 1 ≤ t := (hI.le t hI.mem).1
  have hr : 1 ≤ t + s := by omega
  obtain ⟨θ, hθ⟩ : ∃ θ : hypPSU h (t + s) ε ≃* ↥L ⧸ Subgroup.center ↥L,
      ∀ y, θ (hypProj h (t + s) ε y) = (QuotientGroup.mk (ρ y) : ↥L ⧸ Subgroup.center ↥L) :=
    ⟨uniCoverEquiv ρ hρs hZ, uniCoverEquiv_hypProj ρ hρs hZ⟩
  let ψ : ↥(semilinearSimilitudes h (t + s) ε) →* (K ≃+* K) :=
    (SemidirectProduct.rightHom).comp (semilinearSimilitudes h (t + s) ε).subtype
  have hΦs : Function.Surjective (semilinearAutHom h hr hε) :=
    semilinearAutHom_surjective_of_admissible h hr hε hn3 hnq
  have hDpc : PCentral p (ψ.ker.map (semilinearAutHom h hr hε)) :=
    uniPCentral_map _ hΦs ψ (ringAut_comm K)
  have hD : PCentral p ((ψ.ker.map (semilinearAutHom h hr hε)).comap
      (MulAut.congr θ.symm).toMonoidHom) :=
    uniPCentral_comap_of_mulEquiv (MulAut.congr θ.symm) hDpc
  refine fieldIndexW_coreP hD ha3 hout fun hmem => ?_
  obtain ⟨x₀, hx₀k, hx₀⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hmem)
  obtain ⟨x, hxΦ, hxr, hxU⟩ := exists_unitary_rep h hr hε hn3 x₀
  have hA : (x : SemiGL (HypIndex (t + s) ε) K).left ∈ hypUnitary h (t + s) ε := hxU
  have hr0 : (x₀ : SemiGL (HypIndex (t + s) ε) K).right = 1 := by
    have := MonoidHom.mem_ker.1 hx₀k
    simpa [ψ] using this
  have hxr1 : (x : SemiGL (HypIndex (t + s) ε) K).right = 1 := hxr.trans hr0
  have hcm : ∀ y : hypSU h (t + s) ε, (MulAut.conjNormal a : MulAut ↥L) (ρ y) *
      (ρ (uniConjSU (x : SemiGL (HypIndex (t + s) ε) K).left hA y))⁻¹ ∈
        Subgroup.center ↥L := by
    intro y
    have h1 : semilinearAutHom h hr hε x (hypProj h (t + s) ε y) =
        hypProj h (t + s) ε (uniConjSU (x : SemiGL (HypIndex (t + s) ε) K).left hA y) := by
      rw [semilinearAutHom_apply]
      congr 1
      apply Subtype.ext
      change (x : SemiGL (HypIndex (t + s) ε) K).left *
        glAut (x : SemiGL (HypIndex (t + s) ε) K).right (y : GL (HypIndex (t + s) ε) K) *
          (x : SemiGL (HypIndex (t + s) ε) K).left⁻¹ =
        (x : SemiGL (HypIndex (t + s) ε) K).left * (y : GL (HypIndex (t + s) ε) K) *
          (x : SemiGL (HypIndex (t + s) ε) K).left⁻¹
      rw [hxr1, map_one]
      rfl
    have h2 : semilinearAutHom h hr hε x (hypProj h (t + s) ε y) =
        θ.symm (convAut L a (θ (hypProj h (t + s) ε y))) := by
      rw [hxΦ, hx₀]
      rfl
    have h4 : θ (hypProj h (t + s) ε
        (uniConjSU (x : SemiGL (HypIndex (t + s) ε) K).left hA y)) =
          convAut L a (QuotientGroup.mk (ρ y)) := by
      rw [← h1, h2, θ.apply_symm_apply, hθ]
    rw [hθ] at h4
    have h5 : (QuotientGroup.mk (ρ (uniConjSU (x : SemiGL (HypIndex (t + s) ε) K).left hA y)) :
        ↥L ⧸ Subgroup.center ↥L) =
          QuotientGroup.mk ((MulAut.conjNormal a : MulAut ↥L) (ρ y)) := h4
    simpa only [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.1 h5.symm
  obtain ⟨k, hk⟩ := ha3 ⟨a, Subgroup.mem_zpowers a⟩
  have hak : a ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  exact uniActsInnerlyW_of_compatP hCP h hε hI ρ hρs hZ hcomap
    (hrank p OddPrime.prime (OddPrime.ne_two p)) hA haN hcm
    ⟨k, fun w _ => by rw [hak, one_mul, mul_one]⟩ hrk

end CFSG.LocalAnalysis.RankThreeTheoremC.FieldIndexW
