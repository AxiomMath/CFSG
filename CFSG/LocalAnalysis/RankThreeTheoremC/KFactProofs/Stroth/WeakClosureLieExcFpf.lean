module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNGenFix
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcTorus
public import CFSG.RankThree.PartOne.KE.CTStatement

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross CFSG.RankThree.PartOne.KE
  CFSG.RankThree.Lattice
open CFSG.Timmesfeld.ExceptionalOrders (zpowMatrix zpowMatrix_apply zpowMatrix_zpowMatrix zpowMatrix_one)
open scoped commutatorElement Matrix

variable {τ : Tag}

section Elementary

theorem eq_one_of_pow_eq_one_of_not_dvd {G : Type*} [Group G] {x : G} {p : ℕ} (hp : p.Prime)
    (hxp : x ^ p = 1) {N : ℤ} (hxN : x ^ N = 1) (hN : ¬ (p : ℤ) ∣ N) : x = 1 := by
  have h1 : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hxp
  have h2 : (orderOf x : ℤ) ∣ N := orderOf_dvd_iff_zpow_eq_one.2 hxN
  rcases (Nat.dvd_prime hp).1 h1 with h | h
  · exact orderOf_eq_one_iff.1 h
  · rw [h] at h2
    exact absurd h2 hN

end Elementary

section Weyl

@[expose] def wp (τ : Tag) (l : List (Fin τ.rank)) : WeylGroup τ := (coxeterSystem τ).wordProd l

@[expose] def cw {n : ℕ} (x y : List (Fin n)) : List (Fin n) := x ++ y ++ x.reverse ++ y.reverse

theorem wp_append (l l' : List (Fin τ.rank)) : wp τ (l ++ l') = wp τ l * wp τ l' :=
  (coxeterSystem τ).wordProd_append l l'

theorem wp_nil : wp τ ([] : List (Fin τ.rank)) = 1 := (coxeterSystem τ).wordProd_nil

theorem wp_reverse (l : List (Fin τ.rank)) : wp τ l.reverse = (wp τ l)⁻¹ :=
  (coxeterSystem τ).wordProd_reverse l

theorem wp_cw (x y : List (Fin τ.rank)) : wp τ (cw x y) = ⁅wp τ x, wp τ y⁆ := by
  simp [wp, cw, commutatorElement_def, CoxeterSystem.wordProd_append, mul_assoc]

theorem weylMat_mul (v v' : WeylGroup τ) : weylMat (v * v') = weylMat v * weylMat v' := by
  ext i j
  have h1 : (weylMat (v * v')) *ᵥ (Pi.single j 1 : Fin τ.rank → ℤ) =
      (weylMat v * weylMat v') *ᵥ (Pi.single j 1 : Fin τ.rank → ℤ) := by
    rw [weylMat_mulVec, ← Matrix.mulVec_mulVec, weylMat_mulVec, weylMat_mulVec, mul_smul]
  simpa [Matrix.mulVec_single_one] using congrFun h1 i

theorem weylMat_one : weylMat (1 : WeylGroup τ) = 1 := by
  ext i j
  have h : weylMat (1 : WeylGroup τ) *ᵥ (Pi.single j 1 : Fin τ.rank → ℤ) =
      (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) *ᵥ (Pi.single j 1 : Fin τ.rank → ℤ) := by
    rw [weylMat_mulVec, one_smul, Matrix.one_mulVec]
  simpa [Matrix.mulVec_single_one] using congrFun h i

theorem weylMat_pow (v : WeylGroup τ) (k : ℕ) : weylMat (v ^ k) = weylMat v ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, weylMat_one]
  | succ k ih => rw [pow_succ, pow_succ, weylMat_mul, ih]

theorem weylMat_wp (l : List (Fin τ.rank)) : weylMat (wp τ l) = wordMat τ l := by
  ext i j
  have h : weylMat (wp τ l) *ᵥ (Pi.single j 1 : Fin τ.rank → ℤ) =
      wordMat τ l *ᵥ (Pi.single j 1 : Fin τ.rank → ℤ) := by
    rw [weylMat_mulVec]
    exact wordProd_smul_eq_wordMat_mulVec τ l _
  simpa [Matrix.mulVec_single_one] using congrFun h i

theorem weylMat_inj {v v' : WeylGroup τ} (h : weylMat v = weylMat v') : v = v' :=
  ext_single fun i => by
    have := congrArg (fun M => M *ᵥ (Pi.single i 1 : Fin τ.rank → ℤ)) h
    simpa only [weylMat_mulVec] using this

theorem weylMat_wp_inv (l : List (Fin τ.rank)) : weylMat (wp τ l)⁻¹ = wordMat τ l.reverse := by
  rw [← wp_reverse, weylMat_wp]

theorem weylMat_cw_inv (a b : List (Fin τ.rank)) :
    weylMat ⁅wp τ a, wp τ b⁆⁻¹ = wordMat τ (cw a b).reverse := by
  rw [← wp_cw, weylMat_wp_inv]

theorem wp_cw_pow_eq_one {a b : List (Fin τ.rank)} {k : ℕ}
    (h : wordMat τ (cw a b) ^ k = 1) : ⁅wp τ a, wp τ b⁆ ^ k = 1 := by
  apply weylMat_inj
  rw [weylMat_pow, ← wp_cw, weylMat_wp, h, weylMat_one]

theorem wp_mem_centralizer {a w : List (Fin τ.rank)}
    (h : wordMat τ a * wordMat τ w = wordMat τ w * wordMat τ a) :
    wp τ a ∈ Subgroup.centralizer ({wp τ w} : Set (WeylGroup τ)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  rw [Set.mem_singleton_iff] at hg
  subst hg
  apply weylMat_inj
  rw [weylMat_mul, weylMat_mul, weylMat_wp, weylMat_wp]
  exact h.symm

theorem wp_dcw_eq {a b c d w : List (Fin τ.rank)} {z : WeylGroup τ} {s : ℤ} {k : ℕ}
    (hz : weylMat z = s • (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ))
    (h : wordMat τ (cw (cw a b) (cw c d)) = s • wordMat τ w ^ k) :
    ⁅⁅wp τ a, wp τ b⁆, ⁅wp τ c, wp τ d⁆⁆ = z * wp τ w ^ k := by
  apply weylMat_inj
  rw [← wp_cw, ← wp_cw, ← wp_cw, weylMat_wp, h, weylMat_mul, weylMat_pow, weylMat_wp, hz,
    smul_mul_assoc, one_mul]

end Weyl

section Fpf

variable {L : Type} [Field L]

theorem pow_eq_one_of_rootDiagUnit_pow {β : Fin τ.rank → Lˣ} {p : ℕ}
    (h : rootDiagUnit τ β ^ p = 1) (i : Fin τ.rank) : β i ^ p = 1 := by
  have h1 : rootDiagUnit τ (β ^ p) = rootDiagUnit τ 1 := by
    have : rootDiagUnit τ (β ^ p) = rootDiagUnit τ β ^ p := map_pow (rootDiagUnitHom τ L) β p
    rw [this, h, rootDiagUnit_one]
  have h2 := congrFun (rootDiagUnit_injective h1) i
  simpa using h2

theorem fpf_of_matrix_cert {v : WeylGroup τ} {Y : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} {N : ℤ}
    (hY : (weylMat v⁻¹ - 1) * Y = N • (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)) {p : ℕ}
    (hp : p.Prime) (hN : ¬ (p : ℤ) ∣ N) {β : Fin τ.rank → Lˣ}
    (hβp : rootDiagUnit τ β ^ p = 1) (hβ : weylTuple v β = β) : rootDiagUnit τ β = 1 := by
  rw [weylTuple_eq_zpowMatrix] at hβ
  have h1 : zpowMatrix (weylMat v⁻¹ - 1) β = 1 := by
    rw [zpowMatrix_sub, zpowMatrix_one, hβ, mul_inv_cancel]
  have h2 : zpowMatrix ((weylMat v⁻¹ - 1) * Y) β = 1 := by
    rw [← zpowMatrix_zpowMatrix, h1, map_one]
  rw [hY] at h2
  have hβ1 : β = 1 := by
    funext i
    rw [Pi.one_apply]
    refine eq_one_of_pow_eq_one_of_not_dvd hp (pow_eq_one_of_rootDiagUnit_pow hβp i) ?_ hN
    have h3 := congrFun h2 i
    rw [zpowMatrix_apply] at h3
    simpa [Matrix.smul_apply, Matrix.one_apply] using h3
  rw [hβ1, rootDiagUnit_one]

end Fpf

section Scalar

variable {L : Type} [Field L] [IsAlgClosed L]

theorem weylTuple_eq_pow_of_mem_twistedTorus {w : WeylGroup τ} {Fr : L →+* L} {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) {p q' : ℕ} (hqq' : q * q' ≡ 1 [MOD p])
    {β : Fin τ.rank → Lˣ}
    (hβ : rootDiagUnit τ β ∈
      twistedTorusOf (canonicalRep (coxeterSystem τ) L w) (Units.map (entrywiseHom Fr)))
    (hβp : rootDiagUnit τ β ^ p = 1) : weylTuple w β = fun i => β i ^ q' := by
  have h := canonicalRep_conj_eq_pow_of_mem_twistedTorus hFr hβ hβp hqq'
  rw [canonicalRep_conj_rootDiagUnit] at h
  have h2 : rootDiagUnit τ β ^ q' = rootDiagUnit τ (β ^ q') :=
    (map_pow (rootDiagUnitHom τ L) β q').symm
  rw [h2] at h
  exact rootDiagUnit_injective h

theorem weylTuple_pow_eq {w : WeylGroup τ} {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    {p q' : ℕ} (hqq' : q * q' ≡ 1 [MOD p]) (k : ℕ) :
    ∀ β : Fin τ.rank → Lˣ,
      rootDiagUnit τ β ∈
        twistedTorusOf (canonicalRep (coxeterSystem τ) L w) (Units.map (entrywiseHom Fr)) →
      rootDiagUnit τ β ^ p = 1 → weylTuple (w ^ k) β = fun i => β i ^ q' ^ k := by
  induction k with
  | zero =>
    intro β _ _
    rw [pow_zero, weylTuple_one]
    funext i
    simp
  | succ k ih =>
    intro β hβ hβp
    rw [pow_succ', ← weylTuple_weylTuple, ih β hβ hβp]
    have hmem : rootDiagUnit τ (β ^ q' ^ k) ∈
        twistedTorusOf (canonicalRep (coxeterSystem τ) L w) (Units.map (entrywiseHom Fr)) := by
      have : rootDiagUnit τ (β ^ q' ^ k) = rootDiagUnit τ β ^ q' ^ k :=
        map_pow (rootDiagUnitHom τ L) β (q' ^ k)
      rw [this]
      exact Subgroup.pow_mem _ hβ _
    have hmemp : rootDiagUnit τ (β ^ q' ^ k) ^ p = 1 := by
      have : rootDiagUnit τ (β ^ q' ^ k) = rootDiagUnit τ β ^ q' ^ k :=
        map_pow (rootDiagUnitHom τ L) β (q' ^ k)
      rw [this, ← pow_mul, mul_comm, pow_mul, hβp, one_pow]
    have h := weylTuple_eq_pow_of_mem_twistedTorus hFr hqq' hmem hmemp
    rw [show (fun i => β i ^ q' ^ k) = β ^ q' ^ k from rfl, h]
    funext i
    simp [pow_succ, pow_mul]

theorem fpf_scalar {w z u : WeylGroup τ} {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    {p q' : ℕ} (hp : p.Prime) (hqq' : q * q' ≡ 1 [MOD p]) {s : ℤ}
    (hz : ∀ β : Fin τ.rank → Lˣ, weylTuple z β = fun i => β i ^ s) {k : ℕ}
    (hu : u = z * w ^ k) (harith : ¬ (p : ℤ) ∣ (q' : ℤ) ^ k * s - 1) {β : Fin τ.rank → Lˣ}
    (hβ : rootDiagUnit τ β ∈
      twistedTorusOf (canonicalRep (coxeterSystem τ) L w) (Units.map (entrywiseHom Fr)))
    (hβp : rootDiagUnit τ β ^ p = 1) (hfix : weylTuple u β = β) : rootDiagUnit τ β = 1 := by
  rw [hu, ← weylTuple_weylTuple, weylTuple_pow_eq hFr hqq' k β hβ hβp, hz] at hfix
  have hβ1 : β = 1 := by
    funext i
    rw [Pi.one_apply]
    refine eq_one_of_pow_eq_one_of_not_dvd hp (pow_eq_one_of_rootDiagUnit_pow hβp i) ?_ harith
    have h := congrFun hfix i
    rw [← zpow_natCast, ← zpow_mul] at h
    push_cast at h
    rw [zpow_sub, zpow_one, h]
    exact div_self' _
  rw [hβ1, rootDiagUnit_one]

end Scalar

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw
