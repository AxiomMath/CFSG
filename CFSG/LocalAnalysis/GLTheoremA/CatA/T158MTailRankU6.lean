module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MTailFaith
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSetup
import CFSG.LocalAnalysis.GLTheoremA.CatA.I91T1
public import CFSG.RankThree.PartTwo.Census.TripleCoverLift
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeLowerBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResAll

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.GLTheoremA.T171Sh
open CFSG.RankThree.CentralCover
open CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverLift
open CFSG.RankThree.Classical2
open CFSG.RankThree.Classical
open CFSG.SectionRank.OddCover
open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag

variable {ℓ f : ℕ} {K : Type} [Field K]

section Cover

variable [Fintype K] {p r n : ℕ} {Y : Type*} [Group Y] [Finite Y]

theorem uniTorus_of_cover (hK : UnitaryFieldData ℓ f K) (hℓ2 : ℓ = 2) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f + 1) (hnr : r + 2 = n)
    {φ : Y →* unitaryPSU hK n} (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) :
    ∃ E : Subgroup Y, IsElemAbelian p E ∧ p ^ r * Nat.card ↥(E ⊓ φ.ker) = Nat.card E := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hchar : CharP K 2 := hℓ2 ▸ hK.charP
  have h2K : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hneg : (-1 : K) = 1 := by linear_combination -h2K
  obtain ⟨ζ, hζ, hζN⟩ := exists_orderOf_eq_norm_one hK hp hpq
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  let pos : Fin r → Fin n := fun j => ⟨j.val + 1, by omega⟩
  let L : Fin n := ⟨r + 1, by omega⟩
  have hpos_inj : Function.Injective pos := fun j j' h => by
    simp only [pos, Fin.ext_iff] at h
    exact Fin.ext (by omega)
  have hposL : ∀ j, pos j ≠ L := fun j h => by
    simp only [pos, L, Fin.ext_iff] at h
    have := j.isLt
    omega
  set c : Fin r → Fin n → Kˣ := fun j i =>
    if i = pos j then ζ else if i = L then ζ⁻¹ else 1 with hcdef
  have hcp : ∀ j i, c j i ^ p = 1 := by
    intro j i
    simp only [hcdef]
    split_ifs
    · exact hζp
    · rw [inv_pow, hζp, inv_one]
    · exact one_pow p
  have hcnorm : ∀ j i, c j i ^ (ℓ ^ f + 1) = 1 := by
    intro j i
    simp only [hcdef]
    split_ifs
    · exact hζN
    · rw [inv_pow, hζN, inv_one]
    · exact one_pow _
  have hcpos : ∀ j j', c j (pos j') = if j = j' then ζ else 1 := by
    intro j j'
    simp only [hcdef]
    by_cases h : j = j'
    · subst h
      simp
    · have : pos j' ≠ pos j := fun hh => h (hpos_inj hh).symm
      simp [this, hposL j', h]
  have hcL : ∀ j, c j L = ζ⁻¹ := by
    intro j
    simp only [hcdef]
    have : L ≠ pos j := fun hh => hposL j hh.symm
    simp [this]
  have hcother : ∀ j i, i ≠ pos j → i ≠ L → c j i = 1 := by
    intro j i h1 h2
    simp [hcdef, h1, h2]
  have hcprod : ∀ j, ∏ i, c j i = 1 := by
    intro j
    rw [Fintype.prod_eq_mul (pos j) L (hposL j) (fun x hx => hcother j x hx.1 hx.2),
      hcpos j j, hcL j]
    simp
  have hpriv : ∀ j, ∃ i, (∀ j', j' ≠ j → c j' i = 1) ∧ orderOf (c j i) = p := by
    intro j
    refine ⟨pos j, fun j' hj' => ?_, ?_⟩
    · simp [hcpos, hj']
    · simp [hcpos, hζ]
  have hswapS : ∀ a b : Fin n, permGL (Equiv.swap a b) ∈ unitarySU ℓ f K n := by
    intro a b
    rw [mem_unitarySU_iff hK]
    refine ⟨?_, permGL_unitary hK _⟩
    rw [det_permGL]
    rcases eq_or_ne a b with rfl | hab
    · rw [Equiv.swap_self, Equiv.Perm.sign_refl]
      simp
    · rw [Equiv.Perm.sign_swap hab]
      simp [hneg]
  have hcswap : ∀ j j' : Fin r, c j ∘ (Equiv.swap (pos j) (pos j')).symm = c j' := by
    intro j j'
    funext i
    rw [Function.comp_apply, Equiv.symm_swap]
    by_cases h1 : i = pos j
    · subst h1
      rw [Equiv.swap_apply_left, hcpos, hcpos]
      by_cases hjj : j = j'
      · subst hjj; simp
      · simp [hjj, Ne.symm hjj]
    by_cases h2 : i = pos j'
    · subst h2
      rw [Equiv.swap_apply_right, hcpos, hcpos]
      simp
    · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
      by_cases h3 : i = L
      · subst h3
        rw [hcL, hcL]
      · rw [hcother j i h1 h3, hcother j' i h2 h3]
  have hcinv : ∀ j, c j ∘ (Equiv.swap (pos j) L).symm = fun i => (c j i)⁻¹ := by
    intro j
    funext i
    rw [Function.comp_apply, Equiv.symm_swap]
    by_cases h1 : i = pos j
    · subst h1
      rw [Equiv.swap_apply_left, hcL, hcpos]; simp
    by_cases h2 : i = L
    · subst h2
      rw [Equiv.swap_apply_right, hcL, hcpos]; simp
    · rw [Equiv.swap_apply_of_ne_of_ne h1 h2, hcother j i h1 h2, inv_one]
  have hcS : ∀ a, diagHom n (expHom (p := p) c hcp a) ∈ unitarySU ℓ f K n :=
    diagHom_expHom_mem_unitarySU hK c hcp hcprod hcnorm
  have hinj : Function.Injective (expHom (p := p) c hcp) := expHom_injective c hcp hpriv
  set S := unitarySU ℓ f K n with hSdef
  set Ee := expHom (p := p) c hcp with hEdef
  let δ : Multiplicative (Fin r → ZMod p) →* S := ((diagHom n).comp Ee).codRestrict S hcS
  have hδ : ∀ a, (δ a : GL (Fin n) K) = diagHom n (Ee a) := fun a => rfl
  let θ : Multiplicative (Fin r → ZMod p) →* unitaryPSU hK n := (unitaryProj hK n).comp δ
  have hθsingle : ∀ j, (δ (Multiplicative.ofAdd (Pi.single j 1)) : GL (Fin n) K) =
      diagHom n (c j) := fun j => by rw [hδ, hEdef, expHom_single]
  set D := θ.range with hDdef
  have hDp : ∀ x ∈ D, x ^ p = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have ha : a ^ p = 1 := CFSG.RankThree.CentralCover.pow_eq_one_of_zmod a
    rw [ha, map_one]
  set g : Fin r → unitaryPSU hK n := fun j => θ (Multiplicative.ofAdd (Pi.single j 1)) with hgdef
  have hgp : ∀ j, g j ^ p = 1 := fun j => hDp _ (by rw [hDdef]; exact ⟨_, rfl⟩)
  have hθS : ∀ (w : GL (Fin n) K) (hw : w ∈ S) (a e : Multiplicative (Fin r → ZMod p))
      (hwe : w * diagHom n (Ee a) * w⁻¹ = diagHom n (Ee e)),
      unitaryProj hK n ⟨w, hw⟩ * θ a * (unitaryProj hK n ⟨w, hw⟩)⁻¹ = θ e := by
    intro w hw a e hwe
    change unitaryProj hK n (⟨w, hw⟩ * δ a * ⟨w, hw⟩⁻¹) = unitaryProj hK n (δ e)
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hδ, hδ]
    exact hwe
  have hswap : ∀ j j' : Fin r, j ≠ j' → ∃ w : unitaryPSU hK n,
      w * g j * w⁻¹ = g j' ∧ w * g j' * w⁻¹ = g j := by
    intro j j' _
    refine ⟨unitaryProj hK n ⟨permGL (Equiv.swap (pos j) (pos j')), hswapS _ _⟩, ?_, ?_⟩
    · refine hθS _ (hswapS _ _) _ _ ?_
      rw [hEdef, expHom_single, expHom_single, permGL_mul_diagHom_mul_inv, hcswap]
    · refine hθS _ (hswapS _ _) _ _ ?_
      rw [hEdef, expHom_single, expHom_single, permGL_mul_diagHom_mul_inv, Equiv.swap_comm,
        hcswap]
  have hinv : ∀ j : Fin r, ∃ w : unitaryPSU hK n,
      w * g j * w⁻¹ = (g j)⁻¹ := by
    intro j
    refine ⟨unitaryProj hK n ⟨permGL (Equiv.swap (pos j) L), hswapS _ _⟩, ?_⟩
    have hθinv : (θ (Multiplicative.ofAdd (Pi.single j (1 : ZMod p))))⁻¹ =
        θ (Multiplicative.ofAdd (-(Pi.single j (1 : ZMod p)))) := by
      rw [ofAdd_neg]
      exact (map_inv θ _).symm
    rw [show g j = θ (Multiplicative.ofAdd (Pi.single j (1 : ZMod p))) from rfl, hθinv]
    refine hθS _ (hswapS _ _) _ _ ?_
    have hEinv : Ee (Multiplicative.ofAdd (-(Pi.single j (1 : ZMod p)))) = fun i => (c j i)⁻¹ := by
      have h1 : Ee (Multiplicative.ofAdd (-(Pi.single j (1 : ZMod p)))) =
          (Ee (Multiplicative.ofAdd (Pi.single j (1 : ZMod p))))⁻¹ := by
        rw [ofAdd_neg]
        exact map_inv Ee _
      rw [h1, hEdef, expHom_single]
      rfl
    rw [hEinv, hEdef, expHom_single, permGL_mul_diagHom_mul_inv, hcinv]
  have hgen : Subgroup.closure (Set.range g) = D := by
    have h1 : (Subgroup.closure (Set.range fun j : Fin r =>
        (Multiplicative.ofAdd (Pi.single j (1 : ZMod p)) :
          Multiplicative (Fin r → ZMod p)))).map θ = D := by
      rw [hDdef, CFSG.RankThree.PartOne.K159.closure_range_ofAdd_single,
        ← MonoidHom.range_eq_map]
    rw [MonoidHom.map_closure] at h1
    rw [← h1]
    congr 1
    rw [hgdef]
    exact Set.range_comp _ _
  have hS : ∀ x y : Y, φ x ∈ Set.range g → φ y ∈ Set.range g → φ x ≠ φ y → x * y = y * x := by
    rintro x y ⟨j, hj⟩ ⟨j', hj'⟩ hne
    have hjj : j ≠ j' := fun h => hne (by rw [← hj, ← hj', h])
    obtain ⟨w, hw1, hw2⟩ := hswap j j' hjj
    exact commute_of_conj hφ hker (hp.odd_of_ne_two hp2) (x := x) (y := y)
      (by rw [← hj, ← hj']; exact (Commute.all _ _).map θ) (by rw [← hj']; exact hgp j')
      (n := w) (Or.inr ⟨by rw [← hj, ← hj']; exact hw1, by rw [← hj, ← hj']; exact hw2⟩)
  have hF : ∀ x ∈ D.comap φ, ∀ y ∈ D.comap φ, x * y = y * x := by
    intro x hx y hy
    refine commute_of_mem_closure hφ hker hS ?_ ?_
    · rw [hgen]; exact hx
    · rw [hgen]; exact hy
  have hlift : ∀ e ∈ D, ∃ y : Y, φ y = e ∧ y ^ p = 1 := by
    intro e he
    have hSE : Set.range g ⊆ D := by rw [← hgen]; exact Subgroup.subset_closure
    have hSgen : ∀ s ∈ Set.range g, ∃ y : Y, φ y = s ∧ y ^ p = 1 := by
      rintro _ ⟨j, rfl⟩
      exact exists_lift_pow_eq_one_of_conj_eq_inv hφ hker (hp.odd_of_ne_two hp2) (hgp j)
        (hinv j).choose_spec
    exact exists_lift_pow_eq_one_of_mem_closure hF hSE hSgen (hgen ▸ he)
  have hθinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hmem : δ a ∈ unitaryScalars hK n := by
      rw [← ker_unitaryProj hK n]
      exact ha
    obtain ⟨c', -, -, hc⟩ := mem_unitaryScalars.mp hmem
    have h0 : (⟨0, by omega⟩ : Fin n) ≠ L := by simp [L, Fin.ext_iff]
    have hc0 : ∀ j, c j ⟨0, by omega⟩ = 1 := fun j =>
      hcother j _ (fun h => by simp only [pos, Fin.ext_iff] at h; omega) h0
    have hE0 : Ee a ⟨0, by omega⟩ = 1 := by
      rw [hEdef, expHom_apply]
      simp [hc0]
    have h1 := congrArg (fun g : GL (Fin n) K =>
      (g : Matrix (Fin n) (Fin n) K) ⟨0, by omega⟩ ⟨0, by omega⟩) (hc.symm.trans (hδ a))
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, coe_diagHom,
      Matrix.diagonal_apply_eq, hE0, Units.val_one] at h1
    have hc1 : c' = 1 := Units.ext h1
    have h2 : Ee a = 1 := by
      apply diagHom_injective n
      rw [← hδ a, hc, hc1, map_one, map_one]
    exact hinj (h2.trans (map_one Ee).symm)
  obtain ⟨E, hEab, hEmap, hEcard⟩ := exists_elemAbelian_index_of_lift hF hlift
  have hDcard : Nat.card D = p ^ r := by
    rw [hDdef, ← Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv]
    exact card_multiplicative_zmod r
  exact ⟨E, hEab, by rw [← hDcard]; exact hEcard⟩

end Cover

theorem t158RankU6_holds : T158RankU6 := by
  intro Y _ _ n hn hn1 _ hcat
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hlm : CFSG.Blueprint.LieModel (Y ⧸ Subgroup.center Y) .PSU 6 2 n :=
    CFSG.LocalAnalysis.GLTheoremA.I91T.lieModel_of_catalogIs_isU6n hcat
  obtain ⟨-, K, hKfield, hKfin, hKcard, ⟨eStated⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel hlm
      (by decide : StatedLieTag.PSU ∈ CFSG.Blueprint.classicalTags)
  letI := hKfield
  letI := hKfin
  haveI : Fintype K := Fintype.ofFinite K
  have hKcard' : Nat.card K = (2 ^ n) ^ 2 := hKcard
  have hK : UnitaryFieldData 2 n K :=
    ⟨Nat.prime_two, by omega, by rw [hKcard', ← pow_mul, mul_comm]⟩
  have h3 : 3 ∣ 2 ^ n + 1 := by
    obtain ⟨k, rfl⟩ := hn
    have h1 : 2 ^ (2 * k + 1) % 3 = 2 := by
      rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
    generalize 2 ^ (2 * k + 1) = N at h1 ⊢
    omega
  let eAll : (Y ⧸ Subgroup.center Y) ≃* unitaryPSU hK 6 :=
    eStated.trans (unitaryPSUEquiv hK (by omega)).symm
  let φ : Y →* unitaryPSU hK 6 := eAll.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y))
  have hφ : Function.Surjective φ := eAll.surjective.comp (QuotientGroup.mk'_surjective _)
  have hφker : φ.ker = Subgroup.center Y := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : (QuotientGroup.mk' (Subgroup.center Y)) x = 1 := by
        apply eAll.injective
        rw [map_one]
        exact hx
      exact (QuotientGroup.eq_one_iff _).1 h1
    · intro hx
      change eAll ((QuotientGroup.mk' (Subgroup.center Y)) x) = 1
      rw [show (QuotientGroup.mk' (Subgroup.center Y)) x = 1 from
        (QuotientGroup.eq_one_iff _).2 hx, map_one]
  obtain ⟨E, hEab, hEcard⟩ := uniTorus_of_cover (hK := hK) (Y := Y) (p := 3) (r := 4) (n := 6)
    (φ := φ) rfl Nat.prime_three (by norm_num) h3 rfl hφ (by rw [hφker])
  obtain ⟨F, hFE, -, hFW, hFsup⟩ := exists_isCompl_of_isElemAbelian Nat.prime_three hEab
    (inf_le_left : E ⊓ φ.ker ≤ E) (bot_le : (⊥ : Subgroup Y) ≤ E) (by simp)
  have hFel : IsElemAbelian 3 F := hEab.mono hFE
  refine ⟨F, hFel, ?_, ?_⟩
  · have hFN : F ≤ Subgroup.normalizer ((E ⊓ φ.ker : Subgroup Y) : Set Y) := by
      intro a ha
      rw [Subgroup.mem_normalizer_iff]
      intro w
      constructor
      · intro hw
        have hc : a * w = w * a := hEab.comm (hFE ha) hw.1
        rw [hc, mul_inv_cancel_right]
        exact hw
      · intro hw
        have hw' : w ∈ E := by
          have := E.mul_mem (E.mul_mem (E.inv_mem (hFE ha)) hw.1) (hFE ha)
          simpa [mul_assoc] using this
        have hc : a * w = w * a := hEab.comm (hFE ha) hw'
        rw [hc, mul_inv_cancel_right] at hw
        exact hw
    have hmul :=
      CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf hFN
    rw [hFsup, hFW, Subgroup.card_bot, mul_one, ← hEcard] at hmul
    have hpos : 0 < Nat.card ↥(E ⊓ φ.ker) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos hmul.symm
  · rw [← hφker]
    have : F ⊓ φ.ker = F ⊓ (E ⊓ φ.ker) := by
      rw [← inf_assoc, inf_eq_left.mpr hFE]
    rw [this, hFW]

theorem t158TailFaith_of_te6 {Q : TauCeti.CFSGIndex → Prop} (hN : T158NormConj Q) (hE : T158RankTE6) :
    T158TailFaith Q :=
  t158TailFaith_of hN t158RankU6_holds hE

end CFSG.LocalAnalysis.GLTheoremA.T158

end
