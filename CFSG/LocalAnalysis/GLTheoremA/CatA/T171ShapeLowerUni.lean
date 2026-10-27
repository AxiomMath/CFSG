module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeLowerBase
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172AGrp
public import CFSG.Models.Blueprint
public import CFSG.RankThree.CentralCover.SteinbergBNLinearTorus
public import CFSG.RankThree.PartOne.K159.BorelConj
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeDefs
public import CFSG.RankThree.CentralCover.SteinbergBNCoverPairingCore
public import CFSG.RankThree.PartOne.K159.CoverLift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.CentralCover
open CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverLift
open CFSG.RankThree.Classical2
open CFSG.RankThree.Classical
open CFSG.SectionRank.OddCover
open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag

variable {ℓ f : ℕ} {K : Type} [Field K]

section Cover

variable [Fintype K] {p r n : ℕ} {Y : Type*} [Group Y] [Finite Y]

theorem lowerUni_of_cover (hK : UnitaryFieldData ℓ f K) (hℓ2 : ℓ = 2) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f + 1) (hn : 3 ≤ n) (hnr : r + 3 = n)
    {φ : Y →* unitaryPSU hK n} (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) :
    ∃ E U : Subgroup Y, IsElemAbelian p E ∧ IsPGroup 2 U ∧ U ≠ ⊥ ∧
      E ≤ Subgroup.normalizer (U : Set Y) ∧
      p ^ (n - 3) * Nat.card ↥(E ⊓ φ.ker) ≤ Nat.card E := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hchar : CharP K 2 := hℓ2 ▸ hK.charP
  have h2K : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hneg : (-1 : K) = 1 := by linear_combination -h2K
  obtain ⟨ζ, hζ, hζN⟩ := exists_orderOf_eq_norm_one hK hp hpq
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  let pos : Fin r → Fin n := fun j => ⟨j.val + 2, by omega⟩
  let L : Fin n := ⟨r + 2, by omega⟩
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
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  set z : unitaryPSU hK n :=
    unitaryProj hK n ⟨permGL (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩),
      hswapS _ _⟩ with hzdef
  have hz1 : z ≠ 1 := by
    intro h
    have hmem : (⟨permGL (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩),
        hswapS _ _⟩ : S) ∈ unitaryScalars hK n := by
      rw [← ker_unitaryProj hK n]
      exact h
    obtain ⟨c', -, -, hc⟩ := mem_unitaryScalars.mp hmem
    exact permGL_not_mem_statedScalars (fun h' => h01 (Equiv.swap_eq_one_iff.mp h'))
      (show permGL (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩) ∈
        StatedScalars (Fin n) K from ⟨c', hc.symm⟩)
  have hz2 : z ^ 2 = 1 := by
    rw [hzdef, ← map_pow]
    have hzz : (⟨permGL (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩),
        hswapS _ _⟩ : S) ^ 2 = 1 := by
      refine Subtype.ext ?_
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← map_pow, pow_two, Equiv.swap_mul_self, map_one]
    rw [hzz, map_one]
  have hcoord0 : ∀ a, Ee a ⟨0, by omega⟩ = 1 := by
    intro a
    rw [hEdef, expHom_apply]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [hcother j _ (fun h => by simp only [pos, Fin.ext_iff] at h; omega)
      (by simp [L, Fin.ext_iff])]
    exact one_pow _
  have hcoord1 : ∀ a, Ee a ⟨1, by omega⟩ = 1 := by
    intro a
    rw [hEdef, expHom_apply]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [hcother j _ (fun h => by simp only [pos, Fin.ext_iff] at h; omega)
      (by simp [L, Fin.ext_iff])]
    exact one_pow _
  have hzE : ∀ a, Commute z (θ a) := by
    intro a
    have hinner : Commute (⟨permGL (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩),
        hswapS _ _⟩ : S) (δ a) := by
      apply Subtype.ext
      change (permGL (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩) : GL (Fin n) K) *
        (δ a : GL (Fin n) K) = (δ a : GL (Fin n) K) *
        permGL (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩)
      rw [hδ]
      have hcomp : Ee a ∘ (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩).symm = Ee a := by
        funext i
        rw [Function.comp_apply, Equiv.symm_swap]
        by_cases hi0 : i = ⟨0, by omega⟩
        · subst hi0
          rw [Equiv.swap_apply_left, hcoord1, hcoord0]
        by_cases hi1 : i = ⟨1, by omega⟩
        · subst hi1
          rw [Equiv.swap_apply_right, hcoord0, hcoord1]
        · rw [Equiv.swap_apply_of_ne_of_ne hi0 hi1]
      have h1 : permGL (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩) *
          diagHom n (Ee a) *
          (permGL (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩))⁻¹ =
          diagHom n (Ee a) := by
        rw [permGL_mul_diagHom_mul_inv, hcomp]
      calc permGL (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩) * diagHom n (Ee a)
          = permGL (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩) * diagHom n (Ee a) *
              (permGL (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩))⁻¹ *
              permGL (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩) := by group
        _ = diagHom n (Ee a) *
              permGL (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩) := by rw [h1]
    exact hinner.map (unitaryProj hK n)
  have hDU : D ≤ Subgroup.normalizer (Subgroup.zpowers z : Set (unitaryPSU hK n)) := by
    refine CFSG.RankThree.PartOne.K159.le_normalizer_of_forall_conj_mem fun d hd x hx => ?_
    obtain ⟨a, rfl⟩ := hd
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hc : Commute (θ a) z := (hzE a).symm
    rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) k
  have hQ1 : Subgroup.zpowers z ≠ ⊥ := by
    intro h
    have hmem : z ∈ Subgroup.zpowers z := Subgroup.mem_zpowers z
    rw [h] at hmem
    exact hz1 (Subgroup.mem_bot.1 hmem)
  have hQ2 : IsPGroup 2 (Subgroup.zpowers z) := (isElemAbelian_zpowers hz2).isPGroup
  have hEU : ∀ x ∈ E, ∀ u ∈ Subgroup.zpowers z, φ x * u * (φ x)⁻¹ ∈ Subgroup.zpowers z := by
    intro x hx u hu
    exact ((Subgroup.mem_normalizer_iff.mp (hDU (hEmap ▸ Subgroup.mem_map_of_mem φ hx))) u).1 hu
  obtain ⟨U, hU1, hU2, hEU'⟩ :=
    exists_two_subgroup_normalized_of_cover hφ hker hQ1 hQ2 hEU
  refine ⟨E, U, hEab, hU2, hU1, hEU', ?_⟩
  have hn3 : n - 3 = r := by omega
  have hfinal : p ^ (n - 3) * Nat.card ↥(E ⊓ φ.ker) = Nat.card E := by
    rw [hn3, ← hDcard]
    exact hEcard
  exact hfinal.le

end Cover

theorem lowerUni_holds : LowerUni := by
  intro G _ _ L p N hp hp2 hN hq hcat
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  obtain ⟨i, hQi, ⟨eCat⟩⟩ := hcat
  rcases i with ⟨pr, hpr⟩ | ⟨deg, hdeg⟩ | d | s
  · exact hQi.elim
  · exact hQi.elim
  · obtain ⟨idx, hv⟩ := d
    obtain ⟨q, hidx, hq2, hpq⟩ := hQi
    subst hidx
    have hlm : CFSG.Blueprint.LieModel (PSimple p L) .PSU (m + 1) 2 q.exponent := by
      have h := CFSG.Models.lieModel_twistedA m q hv eCat
      have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA m q, hv⟩ = q.p :=
        TauCeti.LieTypeIndex.characteristic_twistedA m q
      have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA m q, hv⟩ = q.exponent :=
        TauCeti.LieTypeIndex.fieldExponent_twistedA m q
      rw [hc, hf, hq2] at h
      exact CFSG.Models.LieModel.toBlueprint (by decide) h
    obtain ⟨hadm, K, hKfield, hKfin, hKcard, ⟨eStated⟩⟩ :=
      CFSG.Blueprint.LieModel.statedClassicalModel hlm
        (by decide : StatedLieTag.PSU ∈ CFSG.Blueprint.classicalTags)
    letI := hKfield
    letI := hKfin
    haveI : Fintype K := Fintype.ofFinite K
    have hKcard' : Nat.card K = (2 ^ q.exponent) ^ 2 := hKcard
    have hK : UnitaryFieldData 2 q.exponent K :=
      ⟨Nat.prime_two, q.exponent_pos, by rw [hKcard', ← pow_mul, mul_comm]⟩
    have hpq' : p ∣ 2 ^ q.exponent + 1 := by
      rw [← hq2, ← TauCeti.PrimePower.card_def q]
      exact hpq
    haveI hU : Nontrivial (unitaryPSU hK (m + 1)) := by
      obtain ⟨-, U, -, -, hU1, -, -⟩ :=
        lowerUni_of_cover (hK := hK) (Y := unitaryPSU hK (m + 1)) (p := p) (r := m - 2)
          (n := m + 1) rfl hp hp2 hpq' (by omega) (by omega) (φ := MonoidHom.id _)
          Function.surjective_id (by simp)
      have hx : ∃ x ∈ U, x ≠ 1 := by
        by_contra h
        push_neg at h
        refine hU1 (by
          rw [Subgroup.eq_bot_iff_forall]
          intro x hxU
          exact h x hxU)
      obtain ⟨x, hxU, hx1⟩ := hx
      exact ⟨x, 1, by simpa using hx1⟩
    haveI hNtriv : Nontrivial (PSimple p L) := by
      let ePN : PSimple p L ≃* unitaryPSU hK (m + 1) :=
        eStated.trans (unitaryPSUEquiv hK (by omega)).symm
      obtain ⟨x, hx⟩ := exists_ne (1 : unitaryPSU hK (m + 1))
      exact ⟨ePN.symm x, 1, fun h => hx (by
        have := congrArg ePN h
        simpa using this)⟩
    have hO : GLAPPrimeCore p ↥L ≠ ⊤ := by
      intro htop
      haveI : Subsingleton (PQuot p L) := by
        rw [PQuot, htop]
        exact QuotientGroup.subsingleton_quotient_top
      haveI : Subsingleton (PSimple p L) :=
        (QuotientGroup.mk'_surjective (Subgroup.center (PQuot p L))).subsingleton
      obtain ⟨x, hx⟩ := exists_ne (1 : PSimple p L)
      exact hx (Subsingleton.elim x 1)
    have hOZ : GLAPPrimeCore p ↥L ≤ Subgroup.center ↥L :=
      CFSG.LocalAnalysis.GLTheoremA.le_center_of_normal_of_isQuasisimple hq inferInstance hO
    haveI : Group.IsPerfect ↥L := ⟨hq.1⟩
    let eP : (↥L ⧸ Subgroup.center ↥L) ≃* PSimple p L :=
      CFSG.LocalAnalysis.GLTheoremA.S172A.pSimpleEquivCenterQuot p hOZ
    let eAll : (↥L ⧸ Subgroup.center ↥L) ≃* unitaryPSU hK (m + 1) :=
      eP.trans (eStated.trans (unitaryPSUEquiv hK (by omega)).symm)
    let φ : ↥L →* unitaryPSU hK (m + 1) :=
      eAll.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
    have hφ : Function.Surjective φ :=
      eAll.surjective.comp (QuotientGroup.mk'_surjective _)
    have hφker : φ.ker = Subgroup.center ↥L := by
      ext x
      rw [MonoidHom.mem_ker]
      constructor
      · intro hx
        have h1 : (QuotientGroup.mk' (Subgroup.center ↥L)) x = 1 := by
          apply eAll.injective
          rw [map_one]
          exact hx
        exact (QuotientGroup.eq_one_iff _).1 h1
      · intro hx
        change eAll ((QuotientGroup.mk' (Subgroup.center ↥L)) x) = 1
        rw [show (QuotientGroup.mk' (Subgroup.center ↥L)) x = 1 from
          (QuotientGroup.eq_one_iff _).2 hx, map_one]
    obtain ⟨E, U, hEab, hU2, hU1, hEU, hEcard⟩ :=
      lowerUni_of_cover (hK := hK) (Y := ↥L) (p := p) (r := m - 2) (n := m + 1) (φ := φ)
        rfl hp hp2 hpq' (by omega) (by omega) hφ (by rw [hφker])
    refine ⟨E.map L.subtype, U.map L.subtype, Subgroup.map_subtype_le E,
      Subgroup.map_subtype_le U, hEab.map L.subtype, hU2.map L.subtype, ?_, ?_, ?_⟩
    · intro h
      exact hU1 ((Subgroup.map_eq_bot_iff_of_injective U L.subtype_injective).1 h)
    · refine (Subgroup.map_mono hEU).trans ?_
      exact Subgroup.le_normalizer_map L.subtype
    ·
      have hkerE : E ⊓ φ.ker = E ⊓ Subgroup.center ↥L := by rw [hφker]
      have h1 : Nat.card ↥(E.map L.subtype) = Nat.card E :=
        Subgroup.card_map_of_injective L.subtype_injective
      have h2 : Nat.card ↥((E.map L.subtype) ⊓ Subgroup.centralizer (L : Set G)) =
          Nat.card ↥(E ⊓ Subgroup.center ↥L) := by
        rw [inf_centralizer_map_eq, Subgroup.card_map_of_injective L.subtype_injective]
      rw [h1, h2]
      rw [hkerE] at hEcard
      exact hEcard

  · exact hQi.elim

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
