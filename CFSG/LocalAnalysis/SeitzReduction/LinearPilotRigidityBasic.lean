module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFieldComponent
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFusionGenericSetting
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPositionCore

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.EvenSmallLie CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect
  normalizer_le_normalizer_perfectCore)

section Conjugate

variable {G : Type*} [Group G]

theorem mem_conjugate_iff_mul_mul_inv_mem {L : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate L g ↔ g * x * g⁻¹ ∈ L := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    have h : g * ((MulAut.conj g⁻¹).toMonoidHom l) * g⁻¹ = l := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [h]
    exact hl
  · intro h
    refine ⟨g * x * g⁻¹, h, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group

theorem mem_normalizer_conjugate_of_conj_mem {L : Subgroup G} {g y : G}
    (h : g * y * g⁻¹ ∈ normalizer (L : Set G)) : y ∈ normalizer (CFSG.conjugate L g : Set G) := by
  rw [mem_normalizer_iff] at h ⊢
  intro x
  rw [mem_conjugate_iff_mul_mul_inv_mem, mem_conjugate_iff_mul_mul_inv_mem, h (g * x * g⁻¹)]
  constructor <;> intro hx <;> convert hx using 1 <;> group

theorem centralizer_conj_le_normalizer_conjugate {L : Subgroup G} {t : G}
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G)) (g : G) :
    centralizer ({g⁻¹ * t * g} : Set G) ≤ normalizer (CFSG.conjugate L g : Set G) := by
  intro y hy
  refine mem_normalizer_conjugate_of_conj_mem (hCN ?_)
  rw [mem_centralizer_singleton_iff] at hy ⊢
  calc g * y * g⁻¹ * t = g * (y * (g⁻¹ * t * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * t * g) * y) * g⁻¹ := by rw [hy]
    _ = t * (g * y * g⁻¹) := by group

theorem mem_normalizer_perfectCore_inf_centralizer {L : Subgroup G} {s y : G}
    (hyL : y ∈ normalizer (L : Set G)) (hys : y ∈ centralizer ({s} : Set G)) :
    y ∈ normalizer (perfectCore (L ⊓ centralizer ({s} : Set G)) : Set G) :=
  normalizer_le_normalizer_perfectCore _
    (inf_normalizer_le_normalizer_inf ⟨hyL, le_normalizer hys⟩)

end Conjugate

section Symmetry

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem perfectCore_inf_centralizer_conj_eq (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (g : G) :
    perfectCore (L ⊓ centralizer ({g⁻¹ * t * g} : Set G)) =
      perfectCore (CFSG.conjugate L g ⊓ centralizer ({t} : Set G)) := by
  have hLt : L ≤ centralizer ({t} : Set G) := le_centralizer_of_mem_centralizer htC
  have hL'g : CFSG.conjugate L g ≤ centralizer ({g⁻¹ * t * g} : Set G) :=
    EPilot.conjugate_le_centralizer_conj htC g
  apply le_antisymm
  · have hp := perfectCore_perfect (L ⊓ centralizer ({g⁻¹ * t * g} : Set G))
    have h1 : perfectCore (L ⊓ centralizer ({g⁻¹ * t * g} : Set G)) ≤ L :=
      (perfectCore_le _).trans inf_le_left
    have h2 : perfectCore (L ⊓ centralizer ({g⁻¹ * t * g} : Set G)) ≤
        centralizer ({g⁻¹ * t * g} : Set G) :=
      (perfectCore_le _).trans inf_le_right
    have h3 := std_perfect_le_inf_conjugate hset hOut htC ht g hp (h1.trans hLt) h2
    exact le_perfectCore_of_perfect (le_inf (h3.trans inf_le_right) (h1.trans hLt)) hp
  · have hp := perfectCore_perfect (CFSG.conjugate L g ⊓ centralizer ({t} : Set G))
    have h1 : perfectCore (CFSG.conjugate L g ⊓ centralizer ({t} : Set G)) ≤ CFSG.conjugate L g :=
      (perfectCore_le _).trans inf_le_left
    have h2 : perfectCore (CFSG.conjugate L g ⊓ centralizer ({t} : Set G)) ≤
        centralizer ({t} : Set G) :=
      (perfectCore_le _).trans inf_le_right
    have h3 := std_perfect_le_inf_conjugate hset hOut htC ht g hp h2 (h1.trans hL'g)
    exact le_perfectCore_of_perfect (le_inf (h3.trans inf_le_left) (h1.trans hL'g)) hp

end Symmetry

section Chart

variable {G : Type*} [Group G] {L : Subgroup G} {X : Type*} [Group X]

@[expose] noncomputable def conjugateToSelf (L : Subgroup G) (g : G) :
    CFSG.conjugate L g ≃* L where
  toFun x := ⟨g * x * g⁻¹, mem_conjugate_iff_mul_mul_inv_mem.1 x.2⟩
  invFun l := ⟨g⁻¹ * l * g, EPilot.conj_mem_conjugate l.2 g⟩
  left_inv x := Subtype.ext (by simp only; group)
  right_inv l := Subtype.ext (by simp only; group)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem coe_conjugateToSelf (L : Subgroup G) (g : G) (x : CFSG.conjugate L g) :
    ((conjugateToSelf L g x : L) : G) = g * x * g⁻¹ :=
  rfl

theorem coe_conjugateToSelf_symm (L : Subgroup G) (g : G) (l : L) :
    (((conjugateToSelf L g).symm l : CFSG.conjugate L g) : G) = g⁻¹ * l * g :=
  rfl

@[expose] noncomputable def conjChart (e : L ≃* X) (g : G) : CFSG.conjugate L g ≃* X :=
  (conjugateToSelf L g).trans e

theorem conjChart_apply (e : L ≃* X) (g : G) (x : CFSG.conjugate L g) :
    conjChart e g x = e (conjugateToSelf L g x) :=
  rfl

variable {n : ℕ} {K : Type*} [Field K]

theorem normalizerAut_conjChart (e : L ≃* projectiveSL n K) (g : G) {y : G}
    (hy : y ∈ normalizer (CFSG.conjugate L g : Set G))
    (hgy : g * y * g⁻¹ ∈ normalizer (L : Set G)) :
    normalizerAut (conjChart e g) ⟨y, hy⟩ = normalizerAut e ⟨g * y * g⁻¹, hgy⟩ := by
  ext p
  apply e.symm.injective
  apply Subtype.ext
  obtain ⟨l, rfl⟩ := e.surjective p
  have hp : e l = conjChart e g ((conjugateToSelf L g).symm l) := by
    rw [conjChart_apply, MulEquiv.apply_symm_apply]
  have h2 := coe_symm_normalizerAut_apply e ⟨g * y * g⁻¹, hgy⟩ l
  have h1 := coe_symm_normalizerAut_apply (conjChart e g) ⟨y, hy⟩ ((conjugateToSelf L g).symm l)
  rw [← hp] at h1
  rw [h2]
  have h3 : e.symm (normalizerAut (conjChart e g) ⟨y, hy⟩ (e l)) =
      conjugateToSelf L g ((conjChart e g).symm
        (normalizerAut (conjChart e g) ⟨y, hy⟩ (e l))) := by
    apply e.injective
    rw [MulEquiv.apply_symm_apply, ← conjChart_apply, MulEquiv.apply_symm_apply]
  rw [h3, coe_conjugateToSelf, h1, coe_conjugateToSelf_symm]
  simp only [Subgroup.coe_inv]
  group

variable [Finite K]

theorem fieldComponent_conjChart (hn : 3 ≤ n) (e : L ≃* projectiveSL n K) (g : G) {y : G}
    (hy : y ∈ normalizer (CFSG.conjugate L g : Set G))
    (hgy : g * y * g⁻¹ ∈ normalizer (L : Set G)) :
    fieldComponent hn (conjChart e g) ⟨y, hy⟩ = fieldComponent hn e ⟨g * y * g⁻¹, hgy⟩ := by
  rw [fieldComponent_apply, fieldComponent_apply, normalizerAut_conjChart]

end Chart

section Residual

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_fieldComponent_rigid (hset : SeitzSetting G L) {n : ℕ} (hn : 3 ≤ n) {K : Type*}
    [Field K] [Finite K] (e : L ≃* projectiveSL n K) {t : G} (ht : orderOf t = 2)
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G)) (S : Sylow 2 G)
    (hSt : (S : Subgroup G) ≤ centralizer ({t} : Set G))
    (hS : ∃ (s : G) (hs : s ∈ (S : Subgroup G)), fieldComponent hn e ⟨s, hCN (hSt hs)⟩ ≠ 1)
    (hrig : ∀ g y : G, g⁻¹ * t * g ∈ centralizer ({t} : Set G) → g⁻¹ * t * g ≠ t →
      ∀ (hy : y ∈ normalizer (L : Set G)) (hgy : g * y * g⁻¹ ∈ normalizer (L : Set G)),
        y ∈ centralizer ({t} : Set G) → y * (g⁻¹ * t * g) = (g⁻¹ * t * g) * y →
          fieldComponent hn e ⟨y, hy⟩ = fieldComponent hn e ⟨g * y * g⁻¹, hgy⟩) :
    False := by
  have := isCyclic_ringEquiv (K := K)
  set φ : centralizer ({t} : Set G) →* (K ≃+* K) := (fieldComponent hn e).comp (inclusion hCN)
    with hφ
  set SC : Sylow 2 (centralizer ({t} : Set G)) := S.subtype hSt with hSC
  have hφS : ∃ s ∈ (SC : Subgroup (centralizer ({t} : Set G))), φ s ≠ 1 := by
    obtain ⟨s, hs, hs1⟩ := hS
    refine ⟨⟨s, hSt hs⟩, ?_, hs1⟩
    rw [hSC, Sylow.coe_subtype, mem_subgroupOf]
    exact hs
  obtain ⟨χ, hker, s, hsS, hχs⟩ := exists_zmod_two_hom_of_isCyclic φ SC hφS
  refine false_of_rigid hset ht S hSt χ ⟨s, ?_, ?_⟩ fun g y hgt hy hgy hyt => ?_
  · rw [hSC, Sylow.coe_subtype, mem_subgroupOf] at hsS
    exact hsS
  · exact hχs
  · by_cases hne : g⁻¹ * t * g = t
    ·
      have hg : g ∈ centralizer ({t} : Set G) := by
        rw [mem_centralizer_singleton_iff]
        calc g * t = g * (g⁻¹ * t * g) := by rw [hne]
          _ = t * g := by group
      have hconj : (⟨g * y * g⁻¹, hgy⟩ : centralizer ({t} : Set G)) =
          ⟨g, hg⟩ * ⟨y, hy⟩ * (⟨g, hg⟩ : centralizer ({t} : Set G))⁻¹ := rfl
      rw [hconj, map_mul, map_mul, map_inv]
      exact (mul_inv_cancel_comm _ _).symm
    ·
      have h := hrig g y hgt hne (hCN hy) (hCN hgy) hy hyt
      have hmem : (⟨y, hy⟩ : centralizer ({t} : Set G))⁻¹ * ⟨g * y * g⁻¹, hgy⟩ ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
        exact h
      have h2 := hker hmem
      rw [MonoidHom.mem_ker, map_mul, map_inv] at h2
      exact inv_mul_eq_one.1 h2

end Residual

end CFSG.SeitzReduction.LinearPilot
