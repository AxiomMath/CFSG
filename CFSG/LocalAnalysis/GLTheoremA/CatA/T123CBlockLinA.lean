module

public import CFSG.RankThree.PartOne.KC.LinearPlaneBlocks
public import CFSG.RankThree.PartOne.KC.ExactLiftingGeneric
public import CFSG.RankThree.PartOne.KC.LinearPlaneCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearSmall
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T123CB

open Polynomial Module Matrix CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCLinComm
  CFSG.RankThree.PartOne.KCLinPlane

section SL

theorem dvd_card_quot_center_of_pow {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {g : G} (hg : g ^ p = 1) (hgc : g ∉ Subgroup.center G) :
    p ∣ Nat.card (G ⧸ Subgroup.center G) := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 : (QuotientGroup.mk g : G ⧸ Subgroup.center G) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, hg, QuotientGroup.mk_one]
  have h2 : (QuotientGroup.mk g : G ⧸ Subgroup.center G) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]
    exact hgc
  rw [← orderOf_eq_prime h1 h2]
  exact orderOf_dvd_natCard _

theorem dvd_card_quot_center_of_le {G : Type*} [Group G] {P M : Subgroup G} (hPM : P ≤ M)
    [Finite ↥M] {p : ℕ} (hP : p ∣ Nat.card (↥P ⧸ Subgroup.center ↥P)) :
    p ∣ Nat.card (↥M ⧸ Subgroup.center ↥M) := by
  set φ : ↥P →* ↥M ⧸ Subgroup.center ↥M :=
    (QuotientGroup.mk' (Subgroup.center ↥M)).comp (Subgroup.inclusion hPM) with hφ
  have hker : φ.ker ≤ Subgroup.center ↥P := by
    intro g hg
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hg
    rw [Subgroup.mem_center_iff]
    intro h
    have := congrArg (fun z : ↥M => (z : G))
      (Subgroup.mem_center_iff.mp hg (Subgroup.inclusion hPM h))
    exact Subtype.ext this
  have h1 : (Subgroup.center ↥P).index ∣ φ.ker.index := Subgroup.index_dvd_of_le hker
  have h2 : φ.ker.index = Nat.card φ.range := by
    rw [Subgroup.index_ker]
  have h3 : Nat.card φ.range ∣ Nat.card (↥M ⧸ Subgroup.center ↥M) :=
    Subgroup.card_subgroup_dvd_card _
  rw [← Subgroup.index] at hP
  exact hP.trans (h1.trans (h2 ▸ h3))

variable {E : Type*} [Field E]

theorem exists_pow_not_mem_center_of_root {m p : ℕ} (hm : 2 ≤ m) (hp2 : Odd p) {ζ : E}
    (hζ : ζ ^ p = 1) (hζ1 : ζ ≠ 1) :
    ∃ s : SpecialLinearGroup (Fin m) E, s ^ p = 1 ∧
      s ∉ Subgroup.center (SpecialLinearGroup (Fin m) E) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by obtain ⟨j, hj⟩ := hp2; omega)] at hζ
    exact zero_ne_one hζ
  set d : Fin (k + 2) → E := fun i => if i.val = 0 then ζ else if i.val = 1 then ζ⁻¹ else 1
    with hd
  have hdet : (Matrix.diagonal d).det = 1 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_succ, Fin.prod_univ_succ]
    have hrest : ∏ i : Fin k, d i.succ.succ = 1 :=
      Finset.prod_eq_one fun i _ => by simp [hd]
    rw [hrest]
    simp [hd, mul_inv_cancel₀ hζ0]
  set s : SpecialLinearGroup (Fin (k + 2)) E := ⟨Matrix.diagonal d, hdet⟩ with hs
  refine ⟨s, ?_, ?_⟩
  · apply Subtype.ext
    change (Matrix.diagonal d) ^ p = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) E)
    rw [Matrix.diagonal_pow, ← Matrix.diagonal_one]
    congr 1
    funext i
    simp only [Pi.pow_apply, hd]
    split_ifs
    · exact hζ
    · rw [inv_pow, hζ, inv_one]
    · exact one_pow p
  · intro hc
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
    have hr' : Matrix.scalar (Fin (k + 2)) r = Matrix.diagonal d := hr
    have e0 : r = ζ := by
      simpa [hd, Matrix.scalar_apply] using
        congrArg (fun A : Matrix (Fin (k + 2)) (Fin (k + 2)) E => A 0 0) hr'
    have e1 : r = ζ⁻¹ := by
      simpa [hd, Matrix.scalar_apply] using
        congrArg (fun A : Matrix (Fin (k + 2)) (Fin (k + 2)) E => A 1 1) hr'
    rw [e0] at e1
    have hsq : ζ ^ 2 = 1 := by
      rw [sq]
      calc ζ * ζ = ζ * ζ⁻¹ := by rw [← e1]
        _ = 1 := mul_inv_cancel₀ hζ0
    obtain ⟨j, hj⟩ := hp2
    apply hζ1
    calc ζ = ζ ^ (2 * j + 1) * ((ζ ^ 2) ^ j)⁻¹ := by
          rw [← pow_mul, pow_succ, mul_comm (ζ ^ (2 * j)) ζ, mul_assoc,
            mul_inv_cancel₀ (pow_ne_zero _ hζ0), mul_one]
      _ = 1 := by rw [← hj, hζ, hsq, one_pow, inv_one, one_mul]

theorem eq_one_of_pow_eq_one_of_not_dvd [Fintype E] {p : ℕ} (hp : p.Prime)
    (hpE : ¬ p ∣ Fintype.card E - 1) {c : E} (hc : c ^ p = 1) : c = 1 := by
  classical
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hc
    exact zero_ne_one hc
  set u : Eˣ := Units.mk0 c hc0
  have hu : u ^ p = 1 := Units.ext (by simp [u, hc])
  have h1 : orderOf u ∣ p := orderOf_dvd_of_pow_eq_one hu
  have h2 : orderOf u ∣ Fintype.card E - 1 := by
    rw [← Fintype.card_units]
    exact orderOf_dvd_card
  rcases (Nat.dvd_prime hp).mp h1 with h | h
  · have : u = 1 := orderOf_eq_one_iff.mp h
    simpa [u] using congrArg Units.val this
  · exact absurd (h ▸ h2) hpE

theorem exists_pow_not_mem_center_of_dvd [Fintype E] {m p : ℕ} (hp : p.Prime) (hm : 2 ≤ m)
    (hdvd : p ∣ Fintype.card E ^ 2 - 1) (hpE : ¬ p ∣ Fintype.card E - 1) :
    ∃ s : SpecialLinearGroup (Fin m) E, s ^ p = 1 ∧
      s ∉ Subgroup.center (SpecialLinearGroup (Fin m) E) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero m := ⟨by omega⟩
  set q := Fintype.card E with hq
  have hq1 : 1 ≤ q := Fintype.card_pos
  have hGL : p ∣ Nat.card (GL (Fin m) E) := by
    rw [Matrix.card_GL_field]
    have hmem : (⟨m - 2, by omega⟩ : Fin m) ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ _
    refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ hmem)
    have e : q ^ m - q ^ (m - 2) = q ^ (m - 2) * (q ^ 2 - 1) := by
      have h1 : q ^ m = q ^ (m - 2) * q ^ 2 := by rw [← pow_add]; congr 1; omega
      rw [h1, Nat.mul_sub_one]
    rw [e]
    exact dvd_mul_of_dvd_right hdvd _
  have hSL : p ∣ Nat.card (SpecialLinearGroup (Fin m) E) := by
    have h1 := Matrix.card_SL_mul_card_units (n := Fin m) (R := E)
    have hu : Nat.card Eˣ = q - 1 := by rw [Nat.card_units, Nat.card_eq_fintype_card]
    rw [← h1, hu] at hGL
    exact (Nat.Prime.dvd_mul hp).mp hGL |>.resolve_right hpE
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' p hSL
  refine ⟨s, hs ▸ pow_orderOf_eq_one s, fun hc => ?_⟩
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  have hsp : s ^ p = 1 := hs ▸ pow_orderOf_eq_one s
  have hrp : r ^ p = 1 := by
    have h1 : ((s ^ p : SpecialLinearGroup (Fin m) E) : Matrix (Fin m) (Fin m) E) = 1 := by
      rw [hsp]
      rfl
    have h2 : (s : Matrix (Fin m) (Fin m) E) ^ p = 1 := h1
    have h3 : Matrix.scalar (Fin m) (r ^ p) = 1 := by
      rw [map_pow, hr]
      exact h2
    have h4 := congrArg (fun A : Matrix (Fin m) (Fin m) E => A ⟨0, by omega⟩ ⟨0, by omega⟩) h3
    simpa [Matrix.scalar_apply] using h4
  have hr1 : r = 1 := eq_one_of_pow_eq_one_of_not_dvd hp hpE hrp
  have hs1 : s = 1 := Subtype.ext (by rw [← hr, hr1, map_one]; rfl)
  rw [hs1, orderOf_one] at hs
  exact hp.one_lt.ne hs

end SL

section Block

open scoped _root_.Classical

variable {n : ℕ} {K : Type} [Field K] {x : Module.End K (Fin n → K)}

theorem toLin'_commutantUnitsToGL (u : (commutant x)ˣ) :
    Matrix.toLin' ((commutantUnitsToGL x u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((u : commutant x) : Module.End K (Fin n → K)) := by
  rw [coe_commutantUnitsToGL, ← toLinAlgEquiv'_eq_toLin']
  exact AlgEquiv.apply_symm_apply _ _

variable (hx : Squarefree (minpoly K x))

theorem toLin'_blockTheta_apply (w : PiGL (Efac x) (mult x)) (b : primaryFactors x)
    (v : primaryComponent x (b : K[X])) :
    Matrix.toLin' ((blockTheta hx w : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) (v : Fin n → K) =
      ((Matrix.toLin (Module.finBasis (AdjoinRoot (b : K[X])) (primaryComponent x (b : K[X])))
        (Module.finBasis (AdjoinRoot (b : K[X])) (primaryComponent x (b : K[X])))
        ((w b : GL (Fin (mult x b)) (Efac x b)) :
          Matrix (Fin (mult x b)) (Fin (mult x b)) (Efac x b)) v :
        primaryComponent x (b : K[X])) : Fin n → K) := by
  set u : (commutant x)ˣ := thetaEquivUnits hx w with hu
  have h1 : Matrix.toLin' ((blockTheta hx w : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((u : commutant x) : Module.End K (Fin n → K)) :=
    toLin'_commutantUnitsToGL u
  rw [h1]
  have h2 := congrFun (commutantEquivMatrix_thetaEquivUnits hx w) b
  have h3 : commutantRestrict (b : K[X]) (u : commutant x) =
      Matrix.toLin (Module.finBasis (AdjoinRoot (b : K[X])) (primaryComponent x (b : K[X])))
        (Module.finBasis (AdjoinRoot (b : K[X])) (primaryComponent x (b : K[X])))
        ((w b : GL (Fin (mult x b)) (Efac x b)) :
          Matrix (Fin (mult x b)) (Fin (mult x b)) (Efac x b)) := by
    rw [← h2, ← Matrix.toLin_toMatrix (Module.finBasis (AdjoinRoot (b : K[X]))
      (primaryComponent x (b : K[X]))) (Module.finBasis (AdjoinRoot (b : K[X]))
      (primaryComponent x (b : K[X]))) (commutantRestrict (b : K[X]) (u : commutant x))]
    rfl
  rw [← h3]
  rfl

theorem blockImage_apply_of_ne {a b : primaryFactors x} (hab : b ≠ a) {g : GL (Fin n) K}
    (hg : g ∈ blockImage hx a) {v : Fin n → K} (hv : v ∈ primaryComponent x (b : K[X])) :
    Matrix.toLin' (g : Matrix (Fin n) (Fin n) K) v = v := by
  obtain ⟨s, rfl⟩ := mem_blockImage.mp hg
  have h := toLin'_blockTheta_apply hx (blockEmbed (Efac x) (mult x) a s) b ⟨v, hv⟩
  rw [blockEmbed_apply_of_ne hab, Units.val_one, Matrix.toLin_one] at h
  exact h

theorem commute_toLin'_of_mem_blockImage {a : primaryFactors x} {g : GL (Fin n) K}
    (hg : g ∈ blockImage hx a) : Commute (Matrix.toLin' (g : Matrix (Fin n) (Fin n) K)) x := by
  obtain ⟨u, rfl⟩ := blockImage_le_range hx a hg
  rw [toLin'_commutantUnitsToGL]
  exact (mem_commutant x).mp (u : commutant x).2

theorem blockImage_apply_mem {a : primaryFactors x} {g : GL (Fin n) K}
    (hg : g ∈ blockImage hx a) {b : K[X]} {v : Fin n → K} (hv : v ∈ primaryComponent x b) :
    Matrix.toLin' (g : Matrix (Fin n) (Fin n) K) v ∈ primaryComponent x b :=
  apply_mem_primaryComponent (commute_toLin'_of_mem_blockImage hx hg) hv

theorem commute_of_mem_blockImage {a : primaryFactors x} {g : GL (Fin n) K}
    (hgx : Commute (Matrix.toLin' (g : Matrix (Fin n) (Fin n) K)) x) (f : K[X])
    (hgf : ∀ v ∈ primaryComponent x (a : K[X]),
      Matrix.toLin' (g : Matrix (Fin n) (Fin n) K) v = aeval x f v)
    {β : GL (Fin n) K} (hβ : β ∈ blockImage hx a) : g * β = β * g := by
  have hinj : Function.Injective (fun h : GL (Fin n) K =>
      Matrix.toLin' (h : Matrix (Fin n) (Fin n) K)) := fun h₁ h₂ h =>
    Units.ext (Matrix.toLin'.injective h)
  apply hinj
  simp only [Units.val_mul, Matrix.toLin'_mul]
  refine ext_primaryComponent hx (fun b hb v hv => ?_)
  simp only [LinearMap.comp_apply]
  by_cases hba : (⟨b, hb⟩ : primaryFactors x) = a
  · have hb' : b = (a : K[X]) := congrArg Subtype.val hba
    subst hb'
    rw [hgf _ (blockImage_apply_mem hx hβ hv), hgf v hv]
    exact (congrArg (fun T : Module.End K (Fin n → K) => T v)
      (commute_aeval (commute_toLin'_of_mem_blockImage hx hβ) f).eq).symm
  · have hgv : Matrix.toLin' (g : Matrix (Fin n) (Fin n) K) v ∈ primaryComponent x b :=
      apply_mem_primaryComponent hgx hv
    rw [blockImage_apply_of_ne hx hba hβ hv, blockImage_apply_of_ne hx hba hβ hgv]

@[expose] noncomputable def centralizerToCommutantUnits (a₀ : GL (Fin n) K)
    (hax : Matrix.toLin' (a₀ : Matrix (Fin n) (Fin n) K) = x) :
    ↥(Subgroup.centralizer ({a₀} : Set (GL (Fin n) K))) →* (commutant x)ˣ where
  toFun g := commutantUnitOfCommute a₀ g hax (Subgroup.mem_centralizer_singleton_iff.mp g.2)
  map_one' := Units.ext (Subtype.ext (by
    change Matrix.toLinAlgEquiv' ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1
    rw [Units.val_one, map_one]))
  map_mul' g h := Units.ext (Subtype.ext (by
    change Matrix.toLinAlgEquiv' (((g : GL (Fin n) K) * (h : GL (Fin n) K) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) =
      Matrix.toLinAlgEquiv' ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        Matrix.toLinAlgEquiv' ((h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    rw [Units.val_mul, map_mul]))

@[expose] noncomputable def restrictDet (a₀ : GL (Fin n) K)
    (hax : Matrix.toLin' (a₀ : Matrix (Fin n) (Fin n) K) = x) (a : K[X]) :
    ↥(Subgroup.centralizer ({a₀} : Set (GL (Fin n) K))) →* AdjoinRoot a :=
  LinearMap.det.comp ((MonoidHomClass.toMonoidHom (commutantRestrictHom a)).comp
    ((Units.coeHom (commutant x)).comp (centralizerToCommutantUnits a₀ hax)))

theorem restrictDet_apply (a₀ : GL (Fin n) K)
    (hax : Matrix.toLin' (a₀ : Matrix (Fin n) (Fin n) K) = x) (a : K[X])
    (g : ↥(Subgroup.centralizer ({a₀} : Set (GL (Fin n) K)))) :
    restrictDet a₀ hax a g = LinearMap.det (commutantRestrict a
      ((commutantUnitOfCommute a₀ g hax
        (Subgroup.mem_centralizer_singleton_iff.mp g.2) : (commutant x)ˣ) : commutant x)) :=
  rfl

theorem le_blockImage_of_perfect (a : primaryFactors x) {a₀ : GL (Fin n) K}
    (hax : Matrix.toLin' (a₀ : Matrix (Fin n) (Fin n) K) = x) {P : Subgroup (GL (Fin n) K)}
    (hPp : Group.IsPerfect ↥P) (hPc : P ≤ Subgroup.centralizer ({a₀} : Set (GL (Fin n) K)))
    (hPf : ∀ g ∈ P, ∀ b : primaryFactors x, b ≠ a → ∀ v ∈ primaryComponent x (b : K[X]),
      Matrix.toLin' (g : Matrix (Fin n) (Fin n) K) v = v) :
    P ≤ blockImage hx a := by
  intro g hg
  set φ : ↥P →* (AdjoinRoot (a : K[X]))ˣ :=
    ((restrictDet a₀ hax (a : K[X])).comp (Subgroup.inclusion hPc)).toHomUnits with hφ
  have h1 := CFSG.RankThree.PartOne.KCGeneric.eq_one_of_perfect_of_commutative hPp
    (fun u v => mul_comm u v) φ ⟨g, hg⟩
  have h2 : restrictDet a₀ hax (a : K[X]) ⟨g, hPc hg⟩ = 1 := by
    have := congrArg Units.val h1
    rwa [hφ, MonoidHom.coe_toHomUnits, Units.val_one] at this
  refine mem_blockImage_of_restrict hx a hax (Subgroup.mem_centralizer_singleton_iff.mp (hPc hg))
    (fun b hb v hv => hPf g hg b hb v hv) (fun r hr => ?_)
  have hr' : r = ((commutantUnitOfCommute a₀ g hax
      (Subgroup.mem_centralizer_singleton_iff.mp (hPc hg)) : (commutant x)ˣ) : commutant x) :=
    Subtype.ext (by rw [hr]; exact (toLinAlgEquiv'_eq_toLin' _).symm)
  rw [hr']
  rw [restrictDet_apply] at h2
  exact h2

theorem eq_one_of_perfect_of_isSolvable {G H : Type*} [Group G] [Group H] [Group.IsPerfect G]
    [hH : Group.IsSolvable H] (f : G →* H) (g : G) : f g = 1 := by
  obtain ⟨k, hk⟩ := hH.solvable
  have htop : ∀ j, derivedSeries G j = ⊤ := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [derivedSeries_succ, ih]
      exact Group.IsPerfect.commutator_eq_top
  have h1 : f g ∈ (derivedSeries G k).map f := ⟨g, by rw [htop k]; trivial, rfl⟩
  have h2 := map_derivedSeries_le_derivedSeries f k h1
  rwa [hk, Subgroup.mem_bot] at h2

@[expose] noncomputable def glOfPow (w : Module.End K (Fin n → K)) {m : ℕ} (hw : w ^ m = 1)
    (hm : m ≠ 0) : GL (Fin n) K :=
  Matrix.GeneralLinearGroup.toLin.symm (Units.ofPowEqOne w m hw hm)

theorem toLin'_glOfPow (w : Module.End K (Fin n → K)) {m : ℕ} (hw : w ^ m = 1) (hm : m ≠ 0) :
    Matrix.toLin' ((glOfPow w hw hm : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = w := by
  have h1 : (Matrix.GeneralLinearGroup.toLin (glOfPow w hw hm) : Module.End K (Fin n → K)) =
      Matrix.toLin' ((glOfPow w hw hm : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := rfl
  rw [← h1, glOfPow, MulEquiv.apply_symm_apply]
  rfl

theorem blockImage_apply_of_primaryProjection_eq_zero {a : primaryFactors x} {g : GL (Fin n) K}
    (hg : g ∈ blockImage hx a) {v : Fin n → K} (hv : primaryProjection x (a : K[X]) v = 0) :
    Matrix.toLin' (g : Matrix (Fin n) (Fin n) K) v = v := by
  have hsum : ∑ b ∈ primaryFactors x, primaryProjection x b v = v := by
    have := LinearMap.congr_fun (sum_primaryProjection hx) v
    rwa [LinearMap.sum_apply, Module.End.one_apply] at this
  rw [← hsum, map_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  by_cases hba : b = (a : K[X])
  · rw [hba, hv, map_zero]
  · exact blockImage_apply_of_ne hx (b := ⟨b, hb⟩) (fun h => hba (congrArg Subtype.val h)) hg
      (primaryProjection_mem hx hb v)

theorem blockImage_le_blockImage {y : Module.End K (Fin n → K)} (hy : Squarefree (minpoly K y))
    (hxy : Commute x y) {y₀ : GL (Fin n) K}
    (hy₀ : Matrix.toLin' (y₀ : Matrix (Fin n) (Fin n) K) = y) (a : primaryFactors x)
    (b : primaryFactors y) (hab : primaryComponent x (a : K[X]) ≤ primaryComponent y (b : K[X]))
    (hperf : Group.IsPerfect ↥(blockImage hx a))
    (hc : ∀ g ∈ blockImage hx a, g * y₀ = y₀ * g) :
    blockImage hx a ≤ blockImage hy b := by
  refine le_blockImage_of_perfect hy b hy₀ hperf
    (fun g hg => Subgroup.mem_centralizer_singleton_iff.mpr (hc g hg)) ?_
  intro g hg k hkb v hv
  refine blockImage_apply_of_primaryProjection_eq_zero hx hg ?_
  have h1 : primaryProjection x (a : K[X]) v ∈ primaryComponent y (k : K[X]) :=
    apply_mem_primaryComponent (commute_aeval hxy.symm _).symm hv
  have h2 : primaryProjection x (a : K[X]) v ∈ primaryComponent y (b : K[X]) :=
    hab (primaryProjection_mem hx a.2 v)
  exact eq_zero_of_mem_primaryComponent_ne k.2 b.2 (fun h => hkb (Subtype.ext h)) h1 h2

include hx in
theorem apply_eq_of_perfect_of_isSolvable (a : primaryFactors x) {a₀ : GL (Fin n) K}
    (hax : Matrix.toLin' (a₀ : Matrix (Fin n) (Fin n) K) = x) {R : Subgroup (GL (Fin n) K)}
    [Group.IsPerfect ↥R] (hRc : R ≤ Subgroup.centralizer ({a₀} : Set (GL (Fin n) K)))
    [Group.IsSolvable (GL (Fin (mult x a)) (Efac x a))] {g : GL (Fin n) K} (hg : g ∈ R)
    {v : Fin n → K} (hv : v ∈ primaryComponent x (a : K[X])) :
    Matrix.toLin' (g : Matrix (Fin n) (Fin n) K) v = v := by
  set φ : ↥R →* GL (Fin (mult x a)) (Efac x a) :=
    (Pi.evalMonoidHom (fun b : primaryFactors x => GL (Fin (mult x b)) (Efac x b)) a).comp
      ((thetaEquivUnits hx).symm.toMonoidHom.comp
        ((centralizerToCommutantUnits a₀ hax).comp (Subgroup.inclusion hRc))) with hφ
  have h1 : φ ⟨g, hg⟩ = 1 := eq_one_of_perfect_of_isSolvable φ ⟨g, hg⟩
  set u : (commutant x)ˣ := commutantUnitOfCommute a₀ g hax
    (Subgroup.mem_centralizer_singleton_iff.mp (hRc hg)) with hu
  set w : PiGL (Efac x) (mult x) := (thetaEquivUnits hx).symm u with hw
  have hθ : blockTheta hx w = g := by
    have : blockTheta hx w = commutantUnitsToGL x u := by simp [blockTheta, hw]
    rw [this, hu]
    exact commutantUnitsToGL_commutantUnitOfCommute a₀ g hax _
  have hwa : w a = 1 := h1
  have h2 := toLin'_blockTheta_apply hx w a ⟨v, hv⟩
  rw [hθ, hwa, Units.val_one, Matrix.toLin_one] at h2
  exact h2

theorem isSolvable_of_not_goodBlock [Finite K] {a : primaryFactors x} (hg : ¬ GoodBlock a) :
    Group.IsSolvable (GL (Fin (mult x a)) (Efac x a)) := by
  have : Module.Finite K (Efac x a) :=
    (AdjoinRoot.powerBasis (Fact.out : Irreducible (a : K[X])).ne_zero).finite
  have : Finite (Efac x a) := Module.finite_of_finite K
  have h2 : 1 < Nat.card (Efac x a) := Finite.one_lt_card
  simp only [GoodBlock, not_or, not_and, not_le, not_lt] at hg
  obtain ⟨h3, h4⟩ := hg
  rcases Nat.lt_or_ge (mult x a) 2 with h | h
  · exact Group.isSolvable_of_comm fun u v => commute_of_le_one (by omega) u v
  · exact CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_small_solvable
      (mult x a) (Efac x a) (Or.inr ⟨by omega, by have := h4 h; omega⟩)

theorem exists_aeval_of_commute_blockImage (a : primaryFactors x) {a₀ g : GL (Fin n) K}
    (hax : Matrix.toLin' (a₀ : Matrix (Fin n) (Fin n) K) = x) (hga : g * a₀ = a₀ * g)
    (hg : ∀ β ∈ blockImage hx a, g * β = β * g) :
    ∃ f : K[X], ∀ v ∈ primaryComponent x (a : K[X]),
      Matrix.toLin' (g : Matrix (Fin n) (Fin n) K) v = aeval x f v := by
  set u : (commutant x)ˣ := commutantUnitOfCommute a₀ g hax hga with hu
  set w : PiGL (Efac x) (mult x) := (thetaEquivUnits hx).symm u with hw
  have hθ : blockTheta hx w = g := by
    have : blockTheta hx w = commutantUnitsToGL x u := by simp [blockTheta, hw]
    rw [this, hu]
    exact commutantUnitsToGL_commutantUnitOfCommute a₀ g hax hga
  have hcomm : ∀ s : SpecialLinearGroup (Fin (mult x a)) (Efac x a),
      blockEmbed (Efac x) (mult x) a s * w = w * blockEmbed (Efac x) (mult x) a s := by
    intro s
    apply blockTheta_injective hx
    rw [map_mul, map_mul, hθ]
    exact (hg _ (mem_blockImage.mpr ⟨s, rfl⟩)).symm
  have hcen : w a ∈ Subgroup.center (GL (Fin (mult x a)) (Efac x a)) := by
    by_cases hb : 2 ≤ mult x a
    · have hc : ∀ s : SpecialLinearGroup (Fin (mult x a)) (Efac x a),
          Commute (s : Matrix (Fin (mult x a)) (Fin (mult x a)) (Efac x a))
            ((w a : GL (Fin (mult x a)) (Efac x a)) :
              Matrix (Fin (mult x a)) (Fin (mult x a)) (Efac x a)) := by
        intro s
        have h1 := congrFun (hcomm s) a
        simp only [Pi.mul_apply, blockEmbed_apply_self] at h1
        have h2 := congrArg (fun g : GL (Fin (mult x a)) (Efac x a) =>
          (g : Matrix (Fin (mult x a)) (Fin (mult x a)) (Efac x a))) h1
        have h3 : (s : Matrix (Fin (mult x a)) (Fin (mult x a)) (Efac x a)) *
            ((w a : GL (Fin (mult x a)) (Efac x a)) :
              Matrix (Fin (mult x a)) (Fin (mult x a)) (Efac x a)) =
            ((w a : GL (Fin (mult x a)) (Efac x a)) :
              Matrix (Fin (mult x a)) (Fin (mult x a)) (Efac x a)) * s := by
          simpa using h2
        exact h3
      refine GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr ?_
      exact Matrix.mem_range_scalar_of_commute_transvectionStruct fun t =>
        hc ⟨t.toMatrix, t.det⟩
    · exact Subgroup.mem_center_iff.mpr fun g => commute_of_le_one (by omega) g (w a)
  obtain ⟨c, hc⟩ := GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hcen
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective c
  refine ⟨f, fun v hv => ?_⟩
  have h2 := toLin'_blockTheta_apply hx w a ⟨v, hv⟩
  rw [hθ] at h2
  rw [h2, ← hc, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, map_smul, Matrix.toLin_one]
  exact coe_mk_smul_primaryComponent x (a : K[X]) f ⟨v, hv⟩

theorem dvd_card_center_quot_blockImage [Finite K] (a : primaryFactors x) {p : ℕ} (hp : p.Prime)
    {s : SpecialLinearGroup (Fin (mult x a)) (Efac x a)} (hs : s ^ p = 1)
    (hsc : s ∉ Subgroup.center (SpecialLinearGroup (Fin (mult x a)) (Efac x a))) :
    p ∣ Nat.card (↥(blockImage hx a) ⧸ Subgroup.center ↥(blockImage hx a)) := by
  set φ : SpecialLinearGroup (Fin (mult x a)) (Efac x a) →* GL (Fin n) K :=
    (blockTheta hx).comp (blockEmbed (Efac x) (mult x) a) with hφ
  have hinj : Function.Injective φ := (blockTheta_injective hx).comp (blockEmbed_injective a)
  have hmem : ∀ t, φ t ∈ blockImage hx a := fun t => mem_blockImage.mpr ⟨t, rfl⟩
  refine dvd_card_quot_center_of_pow hp (g := ⟨φ s, hmem s⟩) (Subtype.ext ?_) ?_
  · change φ s ^ p = 1
    rw [← map_pow, hs, map_one]
  · intro hc
    apply hsc
    rw [Subgroup.mem_center_iff]
    intro t
    apply hinj
    have := Subgroup.mem_center_iff.mp hc ⟨φ t, hmem t⟩
    have h2 := congrArg Subtype.val this
    simpa only [Subgroup.coe_mul, map_mul] using h2

end Block

end CFSG.LocalAnalysis.GLTheoremA.T123CB

end
