module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115CharTwoTools
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ConfinedInvolution
public import CFSG.LieType.Steinberg.CentralExt.SUThree
public import CFSG.Open.StatedAPI
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import Certificates.Certificate113

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.LieType.Steinberg Matrix
open scoped MatrixGroups

section Generic

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem statedProj_mk_eq_iff (Hg : Subgroup (GL ι K)) (x y : Hg) :
    (QuotientGroup.mk x : StatedProj Hg) = QuotientGroup.mk y ↔
      ∃ u : Kˣ, ((y : GL ι K) : Matrix ι ι K) =
        ((x : GL ι K) : Matrix ι ι K) * ((u : K) • (1 : Matrix ι ι K)) :=
  CFSG.Open.StatedAPI.statedProj_mk_eq_iff Hg x y

theorem mem_centralizer_mk_iff (Hg : Subgroup (GL ι K)) (A g : Hg) :
    (QuotientGroup.mk g : StatedProj Hg) ∈
        Subgroup.centralizer ({(QuotientGroup.mk A : StatedProj Hg)} : Set (StatedProj Hg)) ↔
      ∃ u : Kˣ, ((g : GL ι K) : Matrix ι ι K) * ((A : GL ι K) : Matrix ι ι K) =
        (((A : GL ι K) : Matrix ι ι K) * ((g : GL ι K) : Matrix ι ι K)) *
          ((u : K) • (1 : Matrix ι ι K)) := by
  rw [Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    statedProj_mk_eq_iff Hg (A * g) (g * A)]
  simp only [Subgroup.coe_mul, Units.val_mul]

theorem not_charTwo_centralizer_of_component [Finite K] (Hg : Subgroup (GL ι K)) (A : Hg)
    (N : Subgroup (GL ι K)) (hNH : N ≤ Hg) (hNq : CFSG.IsQuasisimple N)
    (hNA : ∀ n ∈ N, n * (A : GL ι K) = (A : GL ι K) * n)
    (hNn : ∀ g ∈ Hg, ∀ u : Kˣ,
      ((g : GL ι K) : Matrix ι ι K) * ((A : GL ι K) : Matrix ι ι K) =
        (((A : GL ι K) : Matrix ι ι K) * ((g : GL ι K) : Matrix ι ι K)) *
          ((u : K) • (1 : Matrix ι ι K)) → ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (hNz : ∀ n ∈ N, n ∈ StatedScalars ι K → n = 1) :
    ¬ CharTwo (Subgroup.centralizer
      ({(QuotientGroup.mk A : StatedProj Hg)} : Set (StatedProj Hg))) := by
  intro hC
  let π : Hg →* StatedProj Hg := QuotientGroup.mk' ((StatedScalars ι K).subgroupOf Hg)
  let Nh : Subgroup Hg := N.subgroupOf Hg
  let ρ : Nh →* StatedProj Hg := π.comp Nh.subtype
  have hρ : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : (QuotientGroup.mk (x : Hg) : StatedProj Hg) = 1 := hx
    have hx1 : (x : Hg) ∈ (StatedScalars ι K).subgroupOf Hg := (QuotientGroup.eq_one_iff _).1 hx'
    have hxN : ((x : Hg) : GL ι K) ∈ N := x.2
    exact Subtype.ext (Subtype.ext (hNz _ hxN hx1))
  let Nb : Subgroup (StatedProj Hg) := ρ.range
  let e : N ≃* Nb := (Subgroup.subgroupOfEquivOfLe hNH).symm.trans (MonoidHom.ofInjective hρ)
  have hNbq : CFSG.IsQuasisimple Nb := CFSG.LocalCores.isQuasisimple_of_mulEquiv e hNq
  set C := Subgroup.centralizer
    ({(QuotientGroup.mk A : StatedProj Hg)} : Set (StatedProj Hg)) with hCdef
  have hle : Nb ≤ C := by
    rintro _ ⟨n, rfl⟩
    rw [hCdef, Subgroup.mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
    have hnN : ((n : Hg) : GL ι K) ∈ N := n.2
    have hcomm : (A : Hg) * (n : Hg) = (n : Hg) * A :=
      Subtype.ext ((hNA _ hnN).symm)
    change (QuotientGroup.mk A : StatedProj Hg) * QuotientGroup.mk (n : Hg) =
      QuotientGroup.mk (n : Hg) * QuotientGroup.mk A
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm]
  have hnorm : (Nb.subgroupOf C).Normal := by
    refine ⟨fun x hx c => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨n, hn⟩ := hx
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (c : StatedProj Hg)
    have hcC : (c : StatedProj Hg) ∈ C := c.2
    rw [← hg] at hcC
    obtain ⟨u, hu⟩ := (mem_centralizer_mk_iff Hg A g).1 hcC
    have hnN : ((n : Hg) : GL ι K) ∈ N := n.2
    have hgn : ((g : Hg) : GL ι K) * ((n : Hg) : GL ι K) * ((g : Hg) : GL ι K)⁻¹ ∈ N :=
      hNn _ g.2 u hu _ hnN
    refine ⟨⟨g * (n : Hg) * g⁻¹, hgn⟩, ?_⟩
    change (QuotientGroup.mk (g * (n : Hg) * g⁻¹) : StatedProj Hg) = _
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hg]
    have hn' : (QuotientGroup.mk (n : Hg) : StatedProj Hg) = (x : StatedProj Hg) := hn
    rw [← hn', QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hcomp : IsComponentIn Nb C :=
    ⟨hle, CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hle).symm hNbq, hnorm.isSubnormal⟩
  exact not_le_of_isComponentIn_of_charTwo hC le_rfl hcomp hle

theorem exists_involution_lift (hcard : Fintype.card ι = 3) (Hg : Subgroup (GL ι K))
    (hdet : ∀ g ∈ Hg, ((g : GL ι K) : Matrix ι ι K).det = 1)
    {s : StatedProj Hg} (hs2 : s * s = 1) (hs1 : s ≠ 1) :
    ∃ A : Hg, (QuotientGroup.mk A : StatedProj Hg) = s ∧ A * A = 1 ∧
      (A : GL ι K) ∉ StatedScalars ι K := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective s
  have hgg : (QuotientGroup.mk (g * g) : StatedProj Hg) = 1 := by
    rw [QuotientGroup.mk_mul]
    exact hs2
  have hz : (g * g : Hg) ∈ (StatedScalars ι K).subgroupOf Hg := (QuotientGroup.eq_one_iff _).1 hgg
  obtain ⟨c, hc⟩ : ((g * g : Hg) : GL ι K) ∈ StatedScalars ι K := hz
  have hc3 : c ^ 3 = 1 := by
    have hd := congrArg (fun y : GL ι K => ((y : GL ι K) : Matrix ι ι K).det) hc
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, hcard] at hd
    have h1 := hdet _ (g * g).2
    rw [h1] at hd
    exact Units.ext (by simpa using hd)
  have hz3 : (g * g) ^ 3 = 1 := by
    apply Subtype.ext
    change ((g * g : Hg) : GL ι K) ^ 3 = 1
    rw [← hc, ← map_pow, hc3, map_one]
  refine ⟨g ^ 3, ?_, ?_, ?_⟩
  · rw [QuotientGroup.mk_pow, pow_succ, pow_two, hs2, one_mul]
  · calc g ^ 3 * g ^ 3 = g ^ 6 := by rw [← pow_add]
      _ = (g * g) ^ 3 := by rw [← sq, ← pow_mul]
      _ = 1 := hz3
  · intro hmem
    have : (QuotientGroup.mk (g ^ 3) : StatedProj Hg) = 1 :=
      (QuotientGroup.eq_one_iff _).2 hmem
    rw [QuotientGroup.mk_pow, pow_succ, pow_two, hs2, one_mul] at this
    exact hs1 this

theorem commute_of_scalar_commute (hcard : Fintype.card ι = 3) {A g : Matrix ι ι K}
    (hA2 : A * A = 1) (hdA : A.det = 1) (hdg : g.det = 1) (u : K)
    (h : g * A = (A * g) * (u • (1 : Matrix ι ι K))) : g * A = A * g := by
  have h' : g * A = u • (A * g) := by
    rw [h, Matrix.mul_smul, Matrix.mul_one]
  have hu3 : u ^ 3 = 1 := by
    have := congrArg Matrix.det h'
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_mul, hcard, hdA, hdg] at this
    simpa using this.symm
  have hgu : g = u ^ 2 • g := by
    calc g = g * (A * A) := by rw [hA2, Matrix.mul_one]
      _ = (g * A) * A := by rw [Matrix.mul_assoc]
      _ = (u • (A * g)) * A := by rw [h']
      _ = u • (A * (g * A)) := by rw [Matrix.smul_mul, Matrix.mul_assoc]
      _ = u • (A * (u • (A * g))) := by rw [h']
      _ = (u * u) • ((A * A) * g) := by
          rw [Matrix.mul_smul, smul_smul, ← Matrix.mul_assoc]
      _ = u ^ 2 • g := by rw [hA2, Matrix.one_mul, sq]
  have hu2 : u ^ 2 = 1 := by
    have hunit : IsUnit g.det := by rw [hdg]; exact isUnit_one
    have hginv : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hunit
    have h1 : (1 : Matrix ι ι K) = u ^ 2 • (1 : Matrix ι ι K) := by
      calc (1 : Matrix ι ι K) = g * g⁻¹ := hginv.symm
        _ = (u ^ 2 • g) * g⁻¹ := by rw [← hgu]
        _ = u ^ 2 • (g * g⁻¹) := by rw [Matrix.smul_mul]
        _ = u ^ 2 • (1 : Matrix ι ι K) := by rw [hginv]
    have hne : Nonempty ι := by
      rw [← Fintype.card_pos_iff, hcard]
      norm_num
    obtain ⟨i⟩ := hne
    have h2 := congrFun (congrFun h1 i) i
    simpa using h2.symm
  have hu1 : u = 1 := by
    calc u = u * u ^ 2 := by rw [hu2, mul_one]
      _ = u ^ 3 := by ring
      _ = 1 := hu3
  rw [h, hu1, one_smul, Matrix.mul_one]

end Generic

end CFSG.QuasithinUnique.Ch1
