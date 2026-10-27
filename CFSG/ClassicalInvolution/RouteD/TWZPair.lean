module

public import CFSG.ClassicalInvolution.RouteD.TWZAct
public import CFSG.ClassicalInvolution.RouteD.TWYBridge
public import CFSG.ClassicalInvolution.RouteD.TwinYR2AtT
public import CFSG.ClassicalInvolution.Asc77.AscT7S2RA
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate3952
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterL4Model
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterSp4Model
public import CFSG.ClassicalInvolution.RouteD.TWZLayer

public section

namespace CFSG.ClassicalInvolution.RouteD.TWZ

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.NonClassical
  CFSG.ClassicalInvolution.RouteD.TwinY CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.FrameVertex CFSG.Assembly.LowTwoRank
open CFSG.Open (classicalInvolutionOddCore)

set_option linter.unusedSectionVars false

section Aux

variable {X : Type} [Group X]

theorem mulAut_mul_conj_mul_inv (α : MulAut X) (g : X) :
    α * MulAut.conj g * α⁻¹ = MulAut.conj (α g) := by
  ext y
  simp [MulAut.conj_apply]

theorem inv_mul_mem_center_of_conj_eq {a b : X} (h : MulAut.conj a = MulAut.conj b) :
    a⁻¹ * b ∈ Subgroup.center X := by
  rw [Subgroup.mem_center_iff]
  intro w
  have h1 : a * w * a⁻¹ = b * w * b⁻¹ := by
    have := DFunLike.congr_fun h w
    simpa [MulAut.conj_apply] using this
  calc w * (a⁻¹ * b) = a⁻¹ * (a * w * a⁻¹) * b := by group
    _ = a⁻¹ * (b * w * b⁻¹) * b := by rw [h1]
    _ = a⁻¹ * b * w := by group

theorem conj_eq_of_toInducedAutOn_eq {H : Type} [Group H] (L : Subgroup H)
    {n₁ n₂ : ↥(Subgroup.normalizer (L : Set H))}
    (h : toInducedAutOn L n₁ = toInducedAutOn L n₂) {l : H} (hl : l ∈ L) :
    (n₁ : H) * l * (n₁ : H)⁻¹ = (n₂ : H) * l * (n₂ : H)⁻¹ :=
  congrArg (fun w : ↥(inducedAutOn L) => (((w : MulAut ↥L) ⟨l, hl⟩ : ↥L) : H)) h

theorem mem_normalizer_range_conj {M : Type} [Group M] (ψ : M →* X)
    (hψ : Function.Surjective ψ) (α : MulAut X) :
    α ∈ Subgroup.normalizer
      ((((MulAut.conj : X →* MulAut X).comp ψ).range : Subgroup (MulAut X)) : Set (MulAut X)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have key : ∀ g : X, α * MulAut.conj g * α⁻¹ ∈
      ((MulAut.conj : X →* MulAut X).comp ψ).range := by
    intro g
    rw [mulAut_mul_conj_mul_inv]
    obtain ⟨m, hm⟩ := hψ (α g)
    exact ⟨m, by simp [hm]⟩
  constructor
  · rintro ⟨m, rfl⟩
    exact key (ψ m)
  · intro hh
    obtain ⟨m, hm⟩ := hh
    have hm' : MulAut.conj (ψ m) = α * h * α⁻¹ := hm
    have e : h = α⁻¹ * MulAut.conj (ψ m) * α⁻¹⁻¹ := by rw [hm']; group
    rw [e, mulAut_mul_conj_mul_inv]
    obtain ⟨m', hm''⟩ := hψ (α⁻¹ (ψ m))
    exact ⟨m', by simp [hm'']⟩

end Aux

section Pair

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G}

theorem exists_twinPairOn (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    (hP1 : LocalOddCentral Ω {x}) (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x))
    (hcard : D.card = 1) (i : Fin D.card)
    (hperf : FundPerfect (D.tag i) (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D)
    (hnc : ¬ (D.tag i = .PSL ∧ D.rank i = 2))
    (hperfK : Group.IsPerfect (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K)
    {J J₂ : Subgroup G} {t : G} (hJ : J ∈ centralizingMembers Ω {x})
    (hJ₂ : J₂ ∈ centralizingMembers Ω {x}) (hne : J ≠ J₂) (hc : Commutes J J₂)
    (hJt : IsClassicalMember p f J t) (hJ₂t : IsClassicalMember p f J₂ t) :
    ∃ (RJ RJ₂ : Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K)
      (xJ xJ₂ : (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K),
      Corr Ω x D i J RJ ∧ Corr Ω x D i J₂ RJ₂ ∧
      D.hom i xJ = locMk Ω x ⟨t, le_centralizingLayer hJ hJt.mem⟩ ∧
      D.hom i xJ₂ = locMk Ω x ⟨t, le_centralizingLayer hJ hJt.mem⟩ ∧
      TwinPairOn (D.tag i) (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out)
        ((MulAut.conj : locQuot Ω x →* MulAut (locQuot Ω x)).comp (D.hom i)) RJ RJ₂ xJ xJ₂ := by
  classical
  obtain ⟨RJ, hRJ⟩ := TWY.exists_corr_of_card_one hΩ hex D hcard i hJ
  obtain ⟨RJ₂, hRJ₂⟩ := TWY.exists_corr_of_card_one hΩ hex D hcard i hJ₂
  obtain ⟨xJ, hxJR, hxJ⟩ := exists_model_elt hRJ hJt.mem
  obtain ⟨xJ₂, hxJ₂R, hxJ₂⟩ := exists_model_elt hRJ₂ hJ₂t.mem
  have hty : t ∈ locLayer Ω x := le_centralizingLayer hJ hJt.mem
  have hsqt : locMk Ω x ⟨t, hty⟩ * locMk Ω x ⟨t, hty⟩ = 1 := by
    rw [← map_mul]
    have : (⟨t, hty⟩ : ↥(locLayer Ω x)) * ⟨t, hty⟩ = 1 :=
      Subtype.ext (mul_self_eq_one_of_orderOf_eq_two hJt.orderOf_eq_two)
    rw [this, map_one]
  have hnt : locMk Ω x ⟨t, hty⟩ ≠ 1 := locMk_involution_ne_one hJ hJt
  have key : ∀ (R : Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K)
      (hR : R ∈ compFund D i) (y : (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K),
      y ∈ R → D.hom i y = locMk Ω x ⟨t, hty⟩ → y * y = 1 ∧ y ≠ 1 := by
    intro R hR y hy h
    have h1 : D.hom i (y * y) = 1 := by rw [map_mul, h, hsqt]
    have hker : y * y ∈ Subgroup.center (modelUniv (D.tag i) (D.rank i) p (D.exp i)
        Fact.out).K := D.ker_le_center i (MonoidHom.mem_ker.mpr h1)
    have h2 : y * y = 1 := by
      refine Gaps.fundNoncentral p (D.tag i) (D.rank i) (D.exp i) (D.isFundTag i)
        (D.admissible i) hnc R hR (y * y) (R.mul_mem hy hy) (fun w => ?_)
      have h' := Subgroup.mem_center_iff.mp hker w
      have e : y * y * w * (y * y)⁻¹ * w⁻¹ = 1 := by
        calc y * y * w * (y * y)⁻¹ * w⁻¹ = w * (y * y) * (y * y)⁻¹ * w⁻¹ := by rw [h']
          _ = 1 := by group
      rw [e]
      exact one_mem _
    exact ⟨h2, fun h3 => hnt (by rw [← h, h3, map_one])⟩
  obtain ⟨hxJ2, hxJ1⟩ := key RJ hRJ.2.1 xJ hxJR hxJ
  obtain ⟨hxJ₂2, hxJ₂1⟩ := key RJ₂ hRJ₂.2.1 xJ₂ hxJ₂R hxJ₂
  have hker' : ((MulAut.conj : locQuot Ω x →* MulAut (locQuot Ω x)).comp (D.hom i)).ker ≤
      Subgroup.center (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K := by
    intro m hm
    have hm1 : MulAut.conj (D.hom i m) = 1 := hm
    have hcentral : D.hom i m ∈ Subgroup.center (locQuot Ω x) := by
      rw [Subgroup.mem_center_iff]
      intro w
      have h1 : D.hom i m * w * (D.hom i m)⁻¹ = w := by
        have := DFunLike.congr_fun hm1 w
        simpa [MulAut.conj_apply] using this
      calc w * D.hom i m = (D.hom i m * w * (D.hom i m)⁻¹) * D.hom i m := by rw [h1]
        _ = D.hom i m * w := by group
    have : Group.IsPerfect (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K := hperfK
    refine mem_center_of_comm_mem_center fun s => ?_
    apply D.ker_le_center i
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_center_iff.mp hcentral (D.hom i s)).symm
  refine ⟨RJ, RJ₂, xJ, xJ₂, hRJ, hRJ₂, hxJ, hxJ₂, ?_⟩
  exact {
    ker := hker'
    mem := hRJ.2.1
    mem' := hRJ₂.2.1
    ne := fun h => hne (corr_unique_right hΩ hP1 hRJ (h ▸ hRJ₂))
    comm := (corr_commutes hΩ hP1 hperf hRJ hRJ₂).mp hc
    hx := hxJR
    hx2 := hxJ2
    hx1 := hxJ1
    hx' := hxJ₂R
    hx'2 := hxJ₂2
    hx'1 := hxJ₂1
    same := by
      show MulAut.conj (D.hom i xJ) = MulAut.conj (D.hom i xJ₂)
      rw [hxJ, hxJ₂] }

end Pair

end CFSG.ClassicalInvolution.RouteD.TWZ
