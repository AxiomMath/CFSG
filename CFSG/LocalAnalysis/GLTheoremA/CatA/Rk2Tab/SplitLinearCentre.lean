module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.CentralLift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerLinear
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreMonEmb
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Quot
public import CFSG.RankThree.PartOne.S11c.EvenClassical
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBLSparePermutationLift

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.SectionRank.ClassicalEven CFSG.SectionRank.ClassicalOdd Matrix
open CFSG.LocalAnalysis.RankThreeUC.S15.ACore
open CFSG.LocalAnalysis.GorensteinLyons

variable {F : Type} [Field F]

private theorem diagHom_eq_torusDiag {n : ℕ} (d : Fin n → Fˣ) :
    CFSG.SectionRank.OddCover.diagHom (K := F) n d = torusDiag d := by
  exact Units.ext rfl

private theorem monPermGL_mem_statedSL [CharP F 2] {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    monPermGL n σ ∈ StatedSL n F :=
  CFSG.RankThree.PartOne.HNRed.permGL_mem_statedSL_even (k := F) σ

theorem monPermGL_mul_torusDiag_mul_inv {n : ℕ} (σ : Equiv.Perm (Fin n))
    (d : Fin n → Fˣ) :
    monPermGL n σ * torusDiag d * (monPermGL n σ)⁻¹ = torusDiag (d ∘ σ.symm) := by
  have h := CFSG.RankThree.Classical2.permGL_mul_diagHom_mul_inv (K := F) σ d
  rw [← diagHom_eq_torusDiag d, ← diagHom_eq_torusDiag (d ∘ σ.symm)] at *
  exact h

theorem torusVec_mul_inv_left {M : Type} [CommGroup M] {n : ℕ} (ζ : M) (a i d : Fin n) :
    CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ a i *
      (CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ a d)⁻¹ =
        (CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ i d)⁻¹ := by
  rw [CFSG.LocalAnalysis.GorensteinLyons.SparePermutationLift.torusVec_inv ζ a d,
    CFSG.LocalAnalysis.GorensteinLyons.SparePermutationLift.torusVec_inv ζ i d]
  have hinv : CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ a i =
      (CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ i a)⁻¹ :=
    (CFSG.LocalAnalysis.GorensteinLyons.SparePermutationLift.torusVec_inv ζ i a).symm
  rw [hinv, mul_comm, CFSG.LocalAnalysis.GorensteinLyons.SparePermutationLift.torusVec_mul_inv]

theorem quotient_conj_diag {n : ℕ} [Fintype F] (H : Subgroup (GL (Fin n) F))
    (A : Subgroup (Fin n → Fˣ)) (T : A →* H)
    (P : Equiv.Perm (Fin n) →* H)
    (hT : ∀ v : A, (T v : GL (Fin n) F) = torusDiag (v : Fin n → Fˣ))
    (hP : ∀ σ, (P σ : GL (Fin n) F) = monPermGL n σ)
    (σ : Equiv.Perm (Fin n)) (v w : A)
    (hw : (w : Fin n → Fˣ) = (v : Fin n → Fˣ) ∘ σ.symm) :
    (QuotientGroup.mk (P σ) : StatedProj H) * QuotientGroup.mk (T v) *
        (QuotientGroup.mk (P σ))⁻¹ = QuotientGroup.mk (T w) := by
  have hGL : (P σ : GL (Fin n) F) * (T v : GL (Fin n) F) *
      ((P σ : H) : GL (Fin n) F)⁻¹ = (T w : GL (Fin n) F) := by
    rw [hP, hT, hT, hw, monPermGL_mul_torusDiag_mul_inv]
  have hH : P σ * T v * (P σ)⁻¹ = T w := Subtype.ext hGL
  calc (QuotientGroup.mk (P σ) : StatedProj H) * QuotientGroup.mk (T v) *
        (QuotientGroup.mk (P σ))⁻¹
      = QuotientGroup.mk (P σ * T v * (P σ)⁻¹) := by
          rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    _ = QuotientGroup.mk (T w) := by rw [hH]

private def diagStatedSLHom (n : ℕ) : prodOneUnits F n →* StatedSL n F where
  toFun v := ⟨torusDiag (v : Fin n → Fˣ), torusDiag_mem_SL (mem_prodOneUnits.mp v.2)⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' v w := Subtype.ext (map_mul (torusDiag (K := F)) _ _)

private noncomputable def linearDeltaStated (n : ℕ) :
    prodOneUnits F n →* StatedProj (StatedSL n F) :=
  (QuotientGroup.mk' ((StatedScalars (Fin n) F).subgroupOf (StatedSL n F))).comp
    (diagStatedSLHom (F := F) n)

private theorem linearDeltaStated_eq_one {n : ℕ} {v : prodOneUnits F n}
    (hv : linearDeltaStated (F := F) n v = 1) (j k : Fin n) :
    (v : Fin n → Fˣ) j = (v : Fin n → Fˣ) k := by
  have hv' : diagStatedSLHom (F := F) n v ∈
      (StatedScalars (Fin n) F).subgroupOf (StatedSL n F) :=
    (QuotientGroup.eq_one_iff _).mp hv
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hv'
  have h1 : ∀ x : Fin n, ((v : Fin n → Fˣ) x : F) = (c : F) := by
    intro x
    have := congrArg (fun A : GL (Fin n) F => (A : Matrix (Fin n) (Fin n) F) x x) hc
    simpa [diagStatedSLHom, coe_torusDiag, GeneralLinearGroup.coe_scalar, scalar_apply] using this.symm
  exact Units.ext ((h1 j).trans (h1 k).symm)

private theorem torusDiag_mul_rootSubgroupGL_mul_inv [Fintype F] (k : ℕ)
    (v : Fin (k + 2) → Fˣ) {x : GL (Fin (k + 2)) F}
    (hx : x ∈ rootSubgroupGL (F := F) (k + 2)) :
    torusDiag v * x * (torusDiag v)⁻¹ ∈ rootSubgroupGL (F := F) (k + 2) := by
  rw [mem_rootSubgroupGL] at hx ⊢
  obtain ⟨s, rfl⟩ := hx
  refine ⟨Multiplicative.ofAdd (fun _ => (v 0 : F) * s.toAdd ⟨0, 0⟩ *
    (((v 1)⁻¹ : Fˣ) : F)), ?_⟩
  rw [← map_inv (torusDiag (K := F))]
  exact (torusDiag_mul_linHom_mul_inv k v s).symm

private theorem torusDiag_mem_normalizer_rootSubgroupGL [Fintype F] (k : ℕ)
    (v : Fin (k + 2) → Fˣ) :
    torusDiag v ∈ Subgroup.normalizer
      (rootSubgroupGL (F := F) (k + 2) : Set (GL (Fin (k + 2)) F)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact torusDiag_mul_rootSubgroupGL_mul_inv k v
  · intro hx
    have h2 := torusDiag_mul_rootSubgroupGL_mul_inv k (fun i => (v i)⁻¹) hx
    have hv : torusDiag (fun i => (v i)⁻¹) = (torusDiag v)⁻¹ := by
      rw [← map_inv]
      rfl
    rw [hv, inv_inv] at h2
    have heq : (torusDiag v)⁻¹ * (torusDiag v * x * (torusDiag v)⁻¹) * torusDiag v = x := by
      group
    rwa [heq] at h2


theorem rk2_split_low_A {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (htag : lab.tag = .A) (hpq : p ∣ 2 ^ lab.n - 1) :
    lab.rank - 1 + CFSG.Open.pRank p (Subgroup.center K) ≤
      CFSG.Open.twoLocalPrimeRank p K := by
  classical
  obtain ⟨-, hlab, hM⟩ := rk2_model_of_isLabel hK
  have hpos : 1 ≤ lab.rank := by
    have h := hlab
    simp only [CFSG.Assembly.LargeEvenInLambda2, htag] at h
    exact h.2.1
  have hn1 : 1 ≤ lab.n := hlab.1
  obtain ⟨F, hF, hFin, hcardF, ⟨e₀⟩⟩ :=
    exists_model_psl_of_isLabel hM (d := lab.rank + 1) (n := lab.n)
      (by simp [CFSG.StandardType.markTag, htag])
      (by simp [CFSG.StandardType.markRank, htag])
      (by simp [CFSG.StandardType.markChar, htag])
      (by simp [CFSG.StandardType.markDeg, htag])
  letI : Field F := hF
  letI : Finite F := hFin
  letI : Fintype F := Fintype.ofFinite F
  have hcard' : Fintype.card F = 2 ^ lab.n := by
    rw [← Nat.card_eq_fintype_card]; exact hcardF
  haveI : CharP F 2 := charP_of_card_eq_prime_pow hcard'
  have hpq' : p ∣ Nat.card F - 1 := by rw [hcardF]; exact hpq
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p (by
    rw [Nat.card_units]; exact hpq')
  let k := lab.rank - 1
  have hk : lab.rank = k + 1 := by omega
  let n := k + 2
  have hn : lab.rank + 1 = n := by omega
  rw [hn] at e₀
  let pos : Fin k → Fin n := fun i => ⟨i.val, by omega⟩
  let d : Fin n := ⟨k, by omega⟩
  let e : Fin n := ⟨k + 1, by omega⟩
  let A : Subgroup (Fin n → Fˣ) := prodOneUnits F n
  let δ : A →* StatedProj (StatedSL n F) := linearDeltaStated (F := F) n
  let P : Equiv.Perm (Fin n) →* StatedSL n F :=
    { toFun := fun σ => ⟨monPermGL n σ, monPermGL_mem_statedSL σ⟩
      map_one' := Subtype.ext (map_one (monPermGL n))
      map_mul' := fun σ τ => Subtype.ext (map_mul (monPermGL n) σ τ) }
  let W : Fin n → Fin n → StatedProj (StatedSL n F) := fun a b =>
    QuotientGroup.mk (P (Equiv.swap a b))
  have hW : ∀ (a b : Fin n) (v : A), W a b * δ v * (W a b)⁻¹ =
      δ ⟨(v : Fin n → Fˣ) ∘ Equiv.swap a b,
        comp_mem_prodOneUnits (Equiv.swap a b) v.2⟩ := by
    intro a b v
    exact quotient_conj_diag (StatedSL n F) A (diagStatedSLHom (F := F) n) P
      (fun v => rfl) (fun σ => rfl) (Equiv.swap a b) v
      ⟨(v : Fin n → Fˣ) ∘ Equiv.swap a b, comp_mem_prodOneUnits _ v.2⟩ rfl
  have hτ : ∀ i : Fin k, CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d ∈ A := fun i =>
    torusVec_mem_prodOneUnits ζ (pos i) d
  have hp2' : p ≠ 2 := hp2
  have hposinj : Function.Injective pos := fun i j h => Fin.ext (by
    have := congrArg Fin.val h
    simpa [pos] using this)
  have hpd : ∀ i, pos i ≠ d := fun i h => by
    have := congrArg Fin.val h
    simp [pos, d] at this
    omega
  have hpe : ∀ i, pos i ≠ e := fun i h => by
    have := congrArg Fin.val h
    simp [pos, e] at this
    omega
  have hde : d ≠ e := by
    intro h
    have := congrArg Fin.val h
    simp [d, e] at this
  obtain ⟨hcp, hc1, hcomm, hind, -, -⟩ :=
    torus_weyl_hypotheses A (fun σ v hv => comp_mem_prodOneUnits σ hv) δ
      (fun v hv j k => linearDeltaStated_eq_one hv j k) W hW hp2 hζ pos hposinj d e hpd hpe hde hτ
  let h : Fin k → StatedProj (StatedSL n F) := fun i => δ ⟨CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d, hτ i⟩
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
        comp_mem_prodOneUnits (Equiv.swap (pos i) d) (hτ i)⟩ : A) =
        ⟨(CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d)⁻¹, A.inv_mem (hτ i)⟩ :=
      Subtype.ext (CFSG.LocalAnalysis.GorensteinLyons.torusVec_comp_swap_self ζ (hpd i))
    have hcalc : W (pos i) d * h i * (W (pos i) d)⁻¹ =
        δ ⟨(CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d)⁻¹, A.inv_mem (hτ i)⟩ := by
      calc W (pos i) d * h i * (W (pos i) d)⁻¹
          = δ ⟨CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d ∘ Equiv.swap (pos i) d,
              comp_mem_prodOneUnits (Equiv.swap (pos i) d) (hτ i)⟩ := hv
        _ = δ ⟨(CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d)⁻¹, A.inv_mem (hτ i)⟩ := by
            rw [hcompA]
    have hmapinv : δ ⟨(CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d)⁻¹,
        A.inv_mem (hτ i)⟩ = (h i)⁻¹ := by
      show δ (⟨CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d, hτ i⟩⁻¹) =
        (δ ⟨CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d, hτ i⟩)⁻¹
      rw [map_inv]
    rw [hcalc, hmapinv]
  have hcross : ∀ i j, i ≠ j → W (pos i) d * h j * (W (pos i) d)⁻¹ * (h j)⁻¹ ∈
      Subgroup.zpowers (h i) := by
    intro i j hij
    have hv := hW (pos i) d ⟨CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos j) d, hτ j⟩
    have hcomp : (CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos j) d) ∘
        Equiv.swap (pos i) d =
        CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos j) (pos i) := by
      rw [SparePermutationLift.torusVec_comp_perm]
      congr 2
      · rw [Equiv.swap_inv, Equiv.swap_apply_of_ne_of_ne]
        · exact fun h => hij (hposinj h.symm)
        · exact hpd j
      · rw [Equiv.swap_inv, Equiv.swap_apply_right]
    have hcompA : (⟨CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos j) d ∘ Equiv.swap (pos i) d,
        comp_mem_prodOneUnits (Equiv.swap (pos i) d) (hτ j)⟩ : A) =
        ⟨CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos j) (pos i),
          torusVec_mem_prodOneUnits ζ (pos j) (pos i)⟩ := Subtype.ext hcomp
    have hcalc : W (pos i) d * h j * (W (pos i) d)⁻¹ =
        δ ⟨CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos j) (pos i),
          torusVec_mem_prodOneUnits ζ (pos j) (pos i)⟩ := by
      calc W (pos i) d * h j * (W (pos i) d)⁻¹
          = δ ⟨CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos j) d ∘ Equiv.swap (pos i) d,
              comp_mem_prodOneUnits (Equiv.swap (pos i) d) (hτ j)⟩ := hv
        _ = δ ⟨CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos j) (pos i),
              torusVec_mem_prodOneUnits ζ (pos j) (pos i)⟩ := by rw [hcompA]
    have hA : (⟨CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos j) (pos i),
          torusVec_mem_prodOneUnits ζ (pos j) (pos i)⟩ : A) *
        (⟨CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos j) d, hτ j⟩ : A)⁻¹ =
      ⟨(CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d)⁻¹, A.inv_mem (hτ i)⟩ :=
      Subtype.ext (torusVec_mul_inv_left ζ (pos j) (pos i) d)
    have hmul : δ ⟨CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos j) (pos i),
          torusVec_mem_prodOneUnits ζ (pos j) (pos i)⟩ * (h j)⁻¹ =
        δ ⟨(CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d)⁻¹, A.inv_mem (hτ i)⟩ := by
      have h := congrArg δ hA
      rw [map_mul, map_inv] at h
      exact h
    have hmapinv : δ ⟨(CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d)⁻¹,
        A.inv_mem (hτ i)⟩ = (h i)⁻¹ := by
      show δ (⟨CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d, hτ i⟩⁻¹) =
        (δ ⟨CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d, hτ i⟩)⁻¹
      rw [map_inv]
    rw [hcalc, hmul, hmapinv]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers (h i))
  let X : Subgroup (StatedProj (StatedSL n F)) := rootClassSubgroup (F := F) n
  have hX1 : X ≠ ⊥ := rootClassSubgroup_ne_bot (F := F) (by omega)
  have hX2 : IsPGroup 2 X := isPGroup_two_rootClassSubgroup (F := F) (by omega)
  have hNX : ∀ i, h i ∈ Subgroup.normalizer (X : Set (StatedProj (StatedSL n F))) := by
    intro i
    have hHX : Subgroup.zpowers (torusDiag (CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d)) ≤
        Subgroup.normalizer (rootSubgroupGL (F := F) n : Set (GL (Fin n) F)) :=
      Subgroup.zpowers_le.2 (torusDiag_mem_normalizer_rootSubgroupGL (F := F) k
        (CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d))
    have hle := CFSG.LocalAnalysis.RankThreeTheoremC.map_subgroupOf_le_normalizer_map
      (G := GL (Fin n) F) (N := StatedSL n F)
      (U := Subgroup.zpowers (torusDiag (CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d)))
      (W := rootSubgroupGL (F := F) n) hHX
      (QuotientGroup.mk' ((StatedScalars (Fin n) F).subgroupOf (StatedSL n F)))
    have hmemSL : torusDiag (CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d) ∈ StatedSL n F :=
      torusDiag_mem_SL (prod_torusVec ζ (pos i) d)
    have himg : (QuotientGroup.mk (⟨torusDiag (CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d),
          hmemSL⟩ : StatedSL n F) : StatedProj (StatedSL n F)) ∈
        Subgroup.map (QuotientGroup.mk' ((StatedScalars (Fin n) F).subgroupOf (StatedSL n F)))
          ((Subgroup.zpowers (torusDiag (CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d))).subgroupOf
            (StatedSL n F)) :=
      Subgroup.mem_map_of_mem
        (QuotientGroup.mk' ((StatedScalars (Fin n) F).subgroupOf (StatedSL n F)))
        (Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers _))
    have heq : (QuotientGroup.mk (⟨torusDiag (CFSG.LocalAnalysis.GorensteinLyons.torusVec ζ (pos i) d),
          hmemSL⟩ : StatedSL n F) : StatedProj (StatedSL n F)) = h i := rfl
    rw [heq] at himg
    exact hle himg
  have hbound := central_lift_le_twoLocalPrimeRank e₀ hp hp2 hpow hcomm' hcard hinv hcross
    hX1 hX2 hNX
  simpa [k] using hbound


end CFSG.LocalAnalysis.GLTheoremA
