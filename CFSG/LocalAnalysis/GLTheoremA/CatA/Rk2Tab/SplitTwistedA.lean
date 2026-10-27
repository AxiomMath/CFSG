module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.SplitLinearCentre
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXSparePairTorus
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUAct

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.SectionRank.ClassicalEven CFSG.SectionRank.ClassicalOdd Matrix
open CFSG.LocalAnalysis.RankThreeUC.S15.ACore
open CFSG.LocalAnalysis.GorensteinLyons
open CFSG.LocalAnalysis.ComponentInitial

variable {F : Type} [Field F]

variable {p f : ℕ} {K : Type} [Field K]

private theorem monPermGL_mem_statedSU {n d : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (σ : Equiv.Perm (Fin d)) :
    monPermGL d σ ∈ StatedSU d (2 ^ n) K := by
  have hh := CFSG.StandardType.LineU.permGL_mem_unitarySU h σ
  change monPermGL d σ ∈ CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 n K d
  exact hh

private def diagStatedSUHom (h : UnitaryFieldData p f K) (n : ℕ) :
    normOneProdOne h n →* StatedSU n (p ^ f) K where
  toFun v := by
    have hv := (mem_normOneProdOne h).mp v.2
    have hq : p ^ f ≠ 0 := pow_ne_zero _ h.prime.ne_zero
    have hdq : ((v : Fin n → Kˣ) ^ (p ^ f + 1)) = 1 := by
      funext j
      apply Units.ext
      rw [Pi.pow_apply, Units.val_pow_eq_pow_val, ← h.norm_eq_pow]
      exact hv.2 j
    exact ⟨torusDiag (v : Fin n → Kˣ), torusDiag_mem_SU hq hv.1 hdq⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' v w := Subtype.ext (map_mul (torusDiag (K := K)) _ _)

private noncomputable def unitaryDeltaStated (h : UnitaryFieldData p f K) (n : ℕ) :
    normOneProdOne h n →* StatedProj (StatedSU n (p ^ f) K) :=
  (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (p ^ f) K))).comp
    (diagStatedSUHom h n)

private theorem unitaryDeltaStated_eq_one {h : UnitaryFieldData p f K} {n : ℕ}
    {v : normOneProdOne h n} (hv : unitaryDeltaStated h n v = 1) (j k : Fin n) :
    (v : Fin n → Kˣ) j = (v : Fin n → Kˣ) k := by
  have hv' : diagStatedSUHom h n v ∈
      (StatedScalars (Fin n) K).subgroupOf (StatedSU n (p ^ f) K) :=
    (QuotientGroup.eq_one_iff _).mp hv
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hv'
  have h1 : ∀ x : Fin n, ((v : Fin n → Kˣ) x : K) = (c : K) := by
    intro x
    have := congrArg (fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) x x) hc
    simpa [diagStatedSUHom, coe_torusDiag, GeneralLinearGroup.coe_scalar, scalar_apply] using
      this.symm
  exact Units.ext ((h1 j).trans (h1 k).symm)

end CFSG.LocalAnalysis.GLTheoremA

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.SectionRank.ClassicalEven CFSG.SectionRank.ClassicalOdd Matrix
open CFSG.LocalAnalysis.RankThreeUC.S15.ACore
open CFSG.LocalAnalysis.GorensteinLyons
open CFSG.LocalAnalysis.ComponentInitial


theorem exists_crossedInversionBasis_twA {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (htag : lab.tag = .twA) (hpq : p ∣ 2 ^ lab.n + 1) :
    ∃ (R : Type) (_ : Group R) (θ : K ⧸ Subgroup.center K ≃* R)
      (h w : Fin (lab.rank - 2) → R) (X : Subgroup R),
      (∀ i, h i ^ p = 1) ∧ (∀ i j, Commute (h i) (h j)) ∧
      Nat.card (Subgroup.closure (Set.range h)) = p ^ (lab.rank - 2) ∧
      (∀ i, w i * h i * (w i)⁻¹ = (h i)⁻¹) ∧
      (∀ i j, i ≠ j → w i * h j * (w i)⁻¹ * (h j)⁻¹ ∈ Subgroup.zpowers (h i)) ∧
      X ≠ ⊥ ∧ IsPGroup 2 X ∧ ∀ i, h i ∈ Subgroup.normalizer (X : Set R) := by
  classical
  obtain ⟨-, hlab, hM⟩ := rk2_model_of_isLabel hK
  obtain ⟨t, ℓ, nlab⟩ := lab
  simp only at htag
  subst htag
  simp only [CFSG.Assembly.LargeEvenInLambda2] at hlab
  have hℓ2 : 2 ≤ ℓ := hlab.2.1
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSU (ℓ + 1) 2 nlab := by
    simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
      CFSG.StandardType.markRank, CFSG.StandardType.markChar,
      CFSG.StandardType.markDeg] using hM
  obtain ⟨-, F, hFld, hFin, hFcard, ⟨θ⟩⟩ := hM'.statedClassicalModel (by decide)
  letI : Field F := hFld
  letI : Finite F := hFin
  letI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := nlab) hFcard
  have hFD : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 nlab F :=
    ⟨Nat.prime_two, by omega, by rw [hFcard, ← pow_mul, mul_comm]⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ζ, hζN, hζ⟩ := exists_norm_one_orderOf_of_dvd hFD (by simpa using hpq)
  let k := ℓ - 2
  have hk : ℓ = k + 2 := by omega
  let N := k + 3
  have hN : ℓ + 1 = N := by omega
  rw [hN] at θ
  let pos : Fin k → Fin N := fun i => ⟨i.val + 2, by omega⟩
  let d : Fin N := ⟨k + 2, by omega⟩
  let e : Fin N := ⟨0, by omega⟩
  let A : Subgroup (Fin N → Fˣ) := normOneProdOne hFD N
  let δ : A →* StatedProj (StatedSU N (2 ^ nlab) F) := unitaryDeltaStated hFD N
  let P : Equiv.Perm (Fin N) →* StatedSU N (2 ^ nlab) F :=
    { toFun := fun σ => ⟨monPermGL N σ, monPermGL_mem_statedSU hFD σ⟩
      map_one' := Subtype.ext (map_one (monPermGL N))
      map_mul' := fun σ τ => Subtype.ext (map_mul (monPermGL N) σ τ) }
  let W : Fin N → Fin N → StatedProj (StatedSU N (2 ^ nlab) F) := fun a b =>
    QuotientGroup.mk (P (Equiv.swap a b))
  have hW : ∀ (a b : Fin N) (v : A), W a b * δ v * (W a b)⁻¹ =
      δ ⟨(v : Fin N → Fˣ) ∘ Equiv.swap a b,
        comp_mem_normOneProdOne hFD (Equiv.swap a b) v.2⟩ := by
    intro a b v
    exact quotient_conj_diag (StatedSU N (2 ^ nlab) F) A (diagStatedSUHom hFD N) P
      (fun v => rfl) (fun σ => rfl) (Equiv.swap a b) v
      ⟨(v : Fin N → Fˣ) ∘ Equiv.swap a b,
        comp_mem_normOneProdOne hFD (Equiv.swap a b) v.2⟩ rfl
  have hτ : ∀ i : Fin k, CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d ∈ A := fun i =>
    torusVec_mem_normOneProdOne hFD hζN (pos i) d
  have hposinj : Function.Injective pos := fun i j h => Fin.ext (by
    have := congrArg Fin.val h
    simp [pos] at this
    omega)
  have hpd : ∀ i, pos i ≠ d := fun i h => by
    have := congrArg Fin.val h
    simp [pos, d] at this
    omega
  have hpe : ∀ i, pos i ≠ e := fun i h => by
    have := congrArg Fin.val h
    simp [pos, e] at this
  have hde : d ≠ e := by
    intro h
    have := congrArg Fin.val h
    simp [d, e] at this
  obtain ⟨hcp, hc1, hcomm, hind, -, -⟩ :=
    torus_weyl_hypotheses A (fun σ v hv => comp_mem_normOneProdOne hFD σ hv) δ
      (fun v hv j k => unitaryDeltaStated_eq_one hv j k) W hW hp2 hζ pos hposinj d e hpd hpe hde hτ
  let h : Fin k → StatedProj (StatedSU N (2 ^ nlab) F) := fun i =>
    δ ⟨CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d, hτ i⟩
  have hpow : ∀ i, h i ^ p = 1 := hcp
  have hcomm' : ∀ i j, Commute (h i) (h j) := hcomm
  have hord : ∀ i, orderOf (h i) = p := fun i => orderOf_eq_prime (hpow i) (hc1 i)
  have hcard : Nat.card (Subgroup.closure (Set.range h)) = p ^ k := by
    rw [card_closure_range_of_iSupIndep h hcomm' hind]
    simp [hord]
  have hinv : ∀ i, W (pos i) d * h i * (W (pos i) d)⁻¹ = (h i)⁻¹ := by
    intro i
    have hv := hW (pos i) d ⟨CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d, hτ i⟩
    have hcompA : (⟨CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d ∘ Equiv.swap (pos i) d,
        comp_mem_normOneProdOne hFD (Equiv.swap (pos i) d) (hτ i)⟩ : A) =
        ⟨(CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d)⁻¹, A.inv_mem (hτ i)⟩ :=
      Subtype.ext (torusVec_comp_swap_self ζ (hpd i))
    have hcalc : W (pos i) d * h i * (W (pos i) d)⁻¹ =
        δ ⟨(CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d)⁻¹, A.inv_mem (hτ i)⟩ := by
      calc W (pos i) d * h i * (W (pos i) d)⁻¹
          = δ ⟨CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d ∘ Equiv.swap (pos i) d,
              comp_mem_normOneProdOne hFD (Equiv.swap (pos i) d) (hτ i)⟩ := hv
        _ = δ ⟨(CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d)⁻¹, A.inv_mem (hτ i)⟩ := by rw [hcompA]
    have hmapinv : δ ⟨(CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d)⁻¹, A.inv_mem (hτ i)⟩ = (h i)⁻¹ := by
      show δ (⟨CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d, hτ i⟩⁻¹) = (δ ⟨CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d, hτ i⟩)⁻¹
      rw [map_inv]
    rw [hcalc, hmapinv]
  have hcross : ∀ i j, i ≠ j → W (pos i) d * h j * (W (pos i) d)⁻¹ * (h j)⁻¹ ∈
      Subgroup.zpowers (h i) := by
    intro i j hij
    have hv := hW (pos i) d ⟨CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos j) d, hτ j⟩
    have hcomp : (CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos j) d) ∘ Equiv.swap (pos i) d =
        CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos j) (pos i) := by
      rw [SparePermutationLift.torusVec_comp_perm]
      congr 2
      · rw [Equiv.swap_inv, Equiv.swap_apply_of_ne_of_ne]
        · exact fun hh => hij (hposinj hh.symm)
        · exact hpd j
      · rw [Equiv.swap_inv, Equiv.swap_apply_right]
    have hcompA : (⟨CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos j) d ∘ Equiv.swap (pos i) d,
        comp_mem_normOneProdOne hFD (Equiv.swap (pos i) d) (hτ j)⟩ : A) =
        ⟨CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos j) (pos i), torusVec_mem_normOneProdOne hFD hζN (pos j) (pos i)⟩ :=
      Subtype.ext hcomp
    have hcalc : W (pos i) d * h j * (W (pos i) d)⁻¹ =
        δ ⟨CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos j) (pos i),
          torusVec_mem_normOneProdOne hFD hζN (pos j) (pos i)⟩ := by
      calc W (pos i) d * h j * (W (pos i) d)⁻¹
          = δ ⟨CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos j) d ∘ Equiv.swap (pos i) d,
              comp_mem_normOneProdOne hFD (Equiv.swap (pos i) d) (hτ j)⟩ := hv
        _ = δ ⟨CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos j) (pos i),
              torusVec_mem_normOneProdOne hFD hζN (pos j) (pos i)⟩ := by rw [hcompA]
    have hA : (⟨CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos j) (pos i),
          torusVec_mem_normOneProdOne hFD hζN (pos j) (pos i)⟩ : A) *
        (⟨CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos j) d, hτ j⟩ : A)⁻¹ =
      ⟨(CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d)⁻¹, A.inv_mem (hτ i)⟩ :=
      Subtype.ext (torusVec_mul_inv_left ζ (pos j) (pos i) d)
    have hmul : δ ⟨CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos j) (pos i),
          torusVec_mem_normOneProdOne hFD hζN (pos j) (pos i)⟩ * (h j)⁻¹ =
        δ ⟨(CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d)⁻¹, A.inv_mem (hτ i)⟩ := by
      have h := congrArg δ hA
      rw [map_mul, map_inv] at h
      exact h
    have hmapinv : δ ⟨(CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d)⁻¹, A.inv_mem (hτ i)⟩ = (h i)⁻¹ := by
      show δ (⟨CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d, hτ i⟩⁻¹) = (δ ⟨CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d, hτ i⟩)⁻¹
      rw [map_inv]
    rw [hcalc, hmul, hmapinv]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers (h i))
  let s : StatedProj (StatedSU N (2 ^ nlab) F) := W ⟨0, by omega⟩ ⟨1, by omega⟩
  let X : Subgroup (StatedProj (StatedSU N (2 ^ nlab) F)) := Subgroup.zpowers s
  have hs2 : s * s = 1 := by
    show W ⟨0, by omega⟩ ⟨1, by omega⟩ * W ⟨0, by omega⟩ ⟨1, by omega⟩ = 1
    rw [show W ⟨0, by omega⟩ ⟨1, by omega⟩ = QuotientGroup.mk
      (P (Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩)) from rfl,
      ← QuotientGroup.mk_mul]
    have hswap : Equiv.swap (⟨0, by omega⟩ : Fin N) ⟨1, by omega⟩ *
        Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩ = 1 :=
      Equiv.swap_mul_self _ _
    rw [← map_mul, hswap, map_one, QuotientGroup.mk_one]
  have hs1 : s ≠ 1 := by
    intro h1
    have h2 : P (Equiv.swap (⟨0, by omega⟩ : Fin N) ⟨1, by omega⟩) ∈
        (StatedScalars (Fin N) F).subgroupOf (StatedSU N (2 ^ nlab) F) :=
      (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp h2
    have h3 := congrArg (fun A : GL (Fin N) F => (A : Matrix (Fin N) (Fin N) F)
      ⟨0, by omega⟩ ⟨0, by omega⟩) hc
    have hne : (Equiv.swap (⟨0, by omega⟩ : Fin N) ⟨1, by omega⟩)⁻¹ ⟨0, by omega⟩ ≠
        ⟨0, by omega⟩ := by
      rw [Equiv.swap_inv, Equiv.swap_apply_left]
      intro hh
      have := congrArg Fin.val hh
      simp at this
    rw [GeneralLinearGroup.coe_scalar, scalar_apply, Matrix.diagonal_apply_eq,
      show (P (Equiv.swap (⟨0, by omega⟩ : Fin N)
        ⟨1, by omega⟩) : GL (Fin N) F) = monPermGL N (Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩)
      from rfl, coe_monPermGL, permMatrix_apply_eq_ite] at h3
    simp only [if_neg hne] at h3
    exact c.ne_zero h3
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hordS : orderOf s = 2 := orderOf_eq_prime (by rw [pow_two]; exact hs2) hs1
  have hcardX : Nat.card X = 2 := by
    rw [show X = Subgroup.zpowers s from rfl, Nat.card_zpowers, hordS]
  have hX1 : X ≠ ⊥ := by
    refine (Subgroup.one_lt_card_iff_ne_bot X).1 ?_
    rw [hcardX]; norm_num
  have hX2 : IsPGroup 2 X :=
    IsPGroup.of_card (n := 1) (by rw [hcardX, pow_one])
  have hcommS : ∀ i, Commute (h i) s := by
    intro i
    have hfix : CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d ∘ (Equiv.swap (⟨0, by omega⟩ : Fin N) ⟨1, by omega⟩).symm =
        CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d := by
      rw [Equiv.symm_swap]
      refine torusVec_comp_swap_of_ne ζ ?_ ?_ ?_ ?_
      · intro h; have := congrArg Fin.val h; simp [pos] at this
      · intro h; have := congrArg Fin.val h; simp [d] at this
      · intro h; have := congrArg Fin.val h; simp [pos] at this
      · intro h; have := congrArg Fin.val h; simp [d] at this
    have hGL : Commute (monPermGL N (Equiv.swap (⟨0, by omega⟩ : Fin N) ⟨1, by omega⟩))
        (torusDiag (CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d)) := by
      have h := monPermGL_mul_torusDiag_mul_inv
        (Equiv.swap (⟨0, by omega⟩ : Fin N) ⟨1, by omega⟩) (CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d)
      rw [hfix] at h
      calc monPermGL N (Equiv.swap (⟨0, by omega⟩ : Fin N) ⟨1, by omega⟩) *
            torusDiag (CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d)
          = (monPermGL N (Equiv.swap (⟨0, by omega⟩ : Fin N) ⟨1, by omega⟩) *
              torusDiag (CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d) *
              (monPermGL N (Equiv.swap (⟨0, by omega⟩ : Fin N) ⟨1, by omega⟩))⁻¹) *
              monPermGL N (Equiv.swap (⟨0, by omega⟩ : Fin N) ⟨1, by omega⟩) := by group
        _ = torusDiag (CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d) *
              monPermGL N (Equiv.swap (⟨0, by omega⟩ : Fin N) ⟨1, by omega⟩) := by rw [h]
    have hsub : Commute (diagStatedSUHom hFD N ⟨CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d, hτ i⟩)
        (P (Equiv.swap (⟨0, by omega⟩ : Fin N) ⟨1, by omega⟩)) :=
      Subtype.ext hGL.symm.eq
    have hq := hsub.map (QuotientGroup.mk' ((StatedScalars (Fin N) F).subgroupOf
      (StatedSU N (2 ^ nlab) F)))
    exact hq
  have hNX : ∀ i, h i ∈ Subgroup.normalizer (X : Set (StatedProj (StatedSU N (2 ^ nlab) F))) := by
    intro i
    have hcen : h i ∈ Subgroup.centralizer (X : Set (StatedProj (StatedSU N (2 ^ nlab) F))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact ((hcommS i).zpow_right m).eq.symm
    exact Subgroup.centralizer_le_normalizer (X : Set (StatedProj (StatedSU N (2 ^ nlab) F))) hcen
  exact ⟨StatedProj (StatedSU N (2 ^ nlab) F), inferInstance, θ, h, fun i => W (pos i) d, X,
    hpow, hcomm', hcard, hinv, hcross, hX1, hX2, hNX⟩

theorem rk2_split_low_twA {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (htag : lab.tag = .twA) (hpq : p ∣ 2 ^ lab.n + 1) :
    lab.rank - 2 + CFSG.Open.pRank p (Subgroup.center K) ≤
      CFSG.Open.twoLocalPrimeRank p K := by
  obtain ⟨R, hR, θ, h, w, X, hpow, hcomm, hind, hinv, hcross, hX1, hX2, hNX⟩ :=
    exists_crossedInversionBasis_twA hK hp hp2 htag hpq
  letI := hR
  exact central_lift_le_twoLocalPrimeRank θ hp hp2 hpow hcomm hind hinv hcross hX1 hX2 hNX

end CFSG.LocalAnalysis.GLTheoremA
