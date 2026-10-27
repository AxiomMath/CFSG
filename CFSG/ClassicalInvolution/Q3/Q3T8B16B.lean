module

public import CFSG.ClassicalInvolution.Q3.Q3T8AF05

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open scoped commutatorElement

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77

section Component


variable {G : Type} [Group G] [Finite G]

theorem oddCoreOf_inf_le {N : Subgroup G} {c : G}
    (hCN : ∀ g ∈ Subgroup.centralizer ({c} : Set G), conjSub g N = N) :
    oddCoreOf N ⊓ Subgroup.centralizer ({c} : Set G) ≤
      oddCoreOf (Subgroup.centralizer ({c} : Set G)) := by
  set C := Subgroup.centralizer ({c} : Set G) with hC
  have hconj : ∀ g ∈ C, conjSub g (oddCoreOf N ⊓ C) = oddCoreOf N ⊓ C := by
    intro g hg
    have h1 : conjSub g (oddCoreOf N) = oddCoreOf N := by
      rw [← CFSG.ClassicalInvolution.Asc77.Thompson.oddCoreOf_conjSub_eq, hCN g hg]
    have h2 : conjSub g C = C := conjSub_eq_self_of_mem hg
    have h3 : conjSub g (oddCoreOf N ⊓ C) = conjSub g (oddCoreOf N) ⊓ conjSub g C :=
      Subgroup.map_inf _ _ _ (MulAut.conj g).injective
    rw [h3, h1, h2]
  refine CFSG.ClassicalInvolution.Asc77.T8V.le_oddCoreOf_of_normal_odd' inf_le_right ?_ ?_
  · intro g hg
    exact mem_normalizer_iff_conjSub_eq.mpr (hconj g hg)
  · exact Odd.of_dvd_nat (oddCoreOf_odd_natCard N) (Subgroup.card_dvd_of_le inf_le_left)

theorem exists_mul_mem_centralizer_of_acts_trivially {N : Subgroup G} {c : G} (hc2 : c * c = 1)
    (hCN : ∀ g ∈ Subgroup.centralizer ({c} : Set G), conjSub g N = N)
    (hcN : ∀ n ∈ N, ⁅n, c⁆ ∈ oddCoreOf N) {n : G} (hn : n ∈ N) :
    ∃ o ∈ oddCoreOf N, o⁻¹ * n ∈ Subgroup.centralizer ({c} : Set G) := by
  have hcC : c ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hOc : conjSub c (oddCoreOf N) = oddCoreOf N := by
    rw [← CFSG.ClassicalInvolution.Asc77.Thompson.oddCoreOf_conjSub_eq, hCN c hcC]
  exact exists_mul_mem_centralizer (Y := Subgroup.normalizer ((oddCoreOf N : Subgroup G) : Set G))
    (O := oddCoreOf N) (oddCoreOf_odd_natCard N)
    (fun y hy o ho => (Subgroup.mem_normalizer_iff.mp hy o).mp ho)
    (mem_normalizer_iff_conjSub_eq.mpr hOc) hc2 (hcN n hn)

theorem isComponent_modOdd {N : Subgroup G} {c z : G} (hc2 : c * c = 1)
    (hCN : ∀ g ∈ Subgroup.centralizer ({c} : Set G), conjSub g N = N)
    (hcN : ∀ n ∈ N, ⁅n, c⁆ ∈ oddCoreOf N)
    (hsimple : IsSimpleGroup (↥N ⧸ classicalInvolutionOddCore ↥N))
    (hnab : ∃ a b : ↥N ⧸ classicalInvolutionOddCore ↥N, a * b ≠ b * a)
    (hzN : z ∈ N) (hzC : z ∈ Subgroup.centralizer ({c} : Set G)) (hz2 : z * z = 1)
    (hz1 : z ≠ 1) : CFSG.IsComponent (modOdd c N) := by
  classical
  set C := Subgroup.centralizer ({c} : Set G) with hC
  let Y : Subgroup ↥C := N.subgroupOf C
  let ι : ↥Y →* ↥N :=
    { toFun := fun y => ⟨((y : ↥C) : G), Subgroup.mem_subgroupOf.mp y.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let ψ : ↥Y →* ↥N ⧸ classicalInvolutionOddCore ↥N := (QuotientGroup.mk' _).comp ι
  let ρ : ↥Y →* OddQuot c := (oddQuotMk c).comp Y.subtype
  have hψ : Function.Surjective ψ := by
    intro x
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨o, ho, hoC⟩ := exists_mul_mem_centralizer_of_acts_trivially hc2 hCN hcN n.2
    have hoN : o ∈ N := oddCoreOf_le_self N ho
    have hyN : (⟨o⁻¹ * (n : G), hoC⟩ : ↥C) ∈ Y :=
      Subgroup.mem_subgroupOf.mpr (N.mul_mem (N.inv_mem hoN) n.2)
    refine ⟨⟨⟨o⁻¹ * (n : G), hoC⟩, hyN⟩, ?_⟩
    show (QuotientGroup.mk' _ : ↥N →* _) ⟨o⁻¹ * (n : G), _⟩ = QuotientGroup.mk n
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq]
    have ho' : (⟨o, hoN⟩ : ↥N) ∈ classicalInvolutionOddCore ↥N := (mem_oddCoreOf_iff.mp ho).2
    have := (inferInstance : (classicalInvolutionOddCore ↥N).Normal).conj_mem _ ho' n⁻¹
    convert this using 1
    apply Subtype.ext
    simp [mul_assoc]
  have hker : ψ.ker ≤ ρ.ker := by
    intro y hy
    have h1 : ι y ∈ classicalInvolutionOddCore ↥N := (QuotientGroup.eq_one_iff _).mp hy
    have h2 : ((y : ↥C) : G) ∈ oddCoreOf N :=
      mem_oddCoreOf_iff.mpr ⟨Subgroup.mem_subgroupOf.mp y.2, h1⟩
    have h3 : ((y : ↥C) : G) ∈ oddCoreOf C :=
      oddCoreOf_inf_le hCN ⟨h2, (y : ↥C).2⟩
    obtain ⟨h5, h4⟩ := mem_oddCoreOf_iff.mp h3
    exact (QuotientGroup.eq_one_iff _).mpr h4
  let f : (↥N ⧸ classicalInvolutionOddCore ↥N) →* OddQuot c :=
    (MonoidHom.liftOfRightInverse ψ (Function.surjInv hψ) (Function.rightInverse_surjInv hψ))
      ⟨ρ, hker⟩
  have hfψ : ∀ y, f (ψ y) = ρ y := fun y =>
    MonoidHom.liftOfRightInverse_comp_apply ψ (Function.surjInv hψ)
      (Function.rightInverse_surjInv hψ) ⟨ρ, hker⟩ y
  have hrange : f.range = modOdd c N := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨y, rfl⟩ := hψ q
      rw [hfψ]
      exact ⟨y.1, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨ψ ⟨y, hy⟩, hfψ ⟨y, hy⟩⟩
  have hfker : f.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
    · exact h
    · exfalso
      have hy : (⟨⟨z, hzC⟩, Subgroup.mem_subgroupOf.mpr hzN⟩ : ↥Y) ∈ ρ.ker := by
        have : ψ ⟨⟨z, hzC⟩, Subgroup.mem_subgroupOf.mpr hzN⟩ ∈ f.ker := by
          rw [h]
          trivial
        rw [MonoidHom.mem_ker, hfψ] at this
        exact this
      have h1 : ⟨z, hzC⟩ ∈ classicalInvolutionOddCore ↥C := (QuotientGroup.eq_one_iff _).mp hy
      have h2 : z ∈ oddCoreOf C := mem_oddCoreOf_iff.mpr ⟨hzC, h1⟩
      exact hz1 (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard C) h2
        (isPGroup_zpowers_of_mul_self_eq_one hz2 hz1))
  have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hfker
  have hq : CFSG.IsQuasisimple ↥(modOdd c N) := by
    rw [← hrange]
    exact CFSG.ClassicalInvolution.Asc77.AscFusion.isQuasisimple_of_mulEquiv
      (MonoidHom.ofInjective hinj).symm
      (CFSG.ClassicalInvolution.Asc77.T3Core.isQuasisimple_of_simple_nonabelian hnab)
  have hnorm : (modOdd c N).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (componentClassificationOddCore ↥C) g
    have hhN : conjSub (h : G) N = N := hCN h h.2
    have hyN : (y : G) ∈ N := Subgroup.mem_subgroupOf.mp hy
    have hcn : (h : G) * y * (h : G)⁻¹ ∈ N := by
      have : (h : G) * y * (h : G)⁻¹ ∈ conjSub (h : G) N := ⟨y, hyN, rfl⟩
      rwa [hhN] at this
    refine ⟨h * y * h⁻¹, Subgroup.mem_subgroupOf.mpr hcn, ?_⟩
    simp only [map_mul, map_inv]
    rfl
  exact ⟨hq, hnorm.isSubnormal⟩

theorem centralizes_modOdd {N : Subgroup G} {c v : G}
    (hCN : ∀ g ∈ Subgroup.centralizer ({c} : Set G), conjSub g N = N)
    (hvC : v ∈ Subgroup.centralizer ({c} : Set G)) (hvN : ∀ n ∈ N, ⁅v, n⁆ ∈ oddCoreOf N) :
    ∀ y ∈ modOdd c N, oddQuotMk c ⟨v, hvC⟩ * y = y * oddQuotMk c ⟨v, hvC⟩ := by
  intro y hy
  obtain ⟨w, hw, rfl⟩ := hy
  have hwN : (w : G) ∈ N := Subgroup.mem_subgroupOf.mp hw
  have hcomm : (⁅(⟨v, hvC⟩ : ↥(Subgroup.centralizer ({c} : Set G))), w⁆ :
      ↥(Subgroup.centralizer ({c} : Set G))) ∈
      classicalInvolutionOddCore ↥(Subgroup.centralizer ({c} : Set G)) := by
    have h1 : ((⁅(⟨v, hvC⟩ : ↥(Subgroup.centralizer ({c} : Set G))), w⁆ :
        ↥(Subgroup.centralizer ({c} : Set G))) : G) ∈ oddCoreOf N := by
      have := hvN (w : G) hwN
      simpa [commutatorElement_def] using this
    obtain ⟨h2, h3⟩ := mem_oddCoreOf_iff.mp
      (oddCoreOf_inf_le hCN ⟨h1, (⁅(⟨v, hvC⟩ : ↥(Subgroup.centralizer ({c} : Set G))), w⁆ :
        ↥(Subgroup.centralizer ({c} : Set G))).2⟩)
    exact h3
  have h4 := (QuotientGroup.eq_one_iff _).mpr hcomm
  have h5 : (oddQuotMk c) (⁅(⟨v, hvC⟩ : ↥(Subgroup.centralizer ({c} : Set G))), w⁆ :
      ↥(Subgroup.centralizer ({c} : Set G))) = 1 := h4
  rw [map_commutatorElement] at h5
  exact commutatorElement_eq_one_iff_mul_comm.mp h5

end Component

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
