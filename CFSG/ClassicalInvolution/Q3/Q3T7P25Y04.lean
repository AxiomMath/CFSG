module

public import CFSG.ClassicalInvolution.Q3.Q3T7P25Y03
public import CFSG.ClassicalInvolution.Asc77.AscC5O10
public import CFSG.RankThree.PartTwo.Sec8.TransferExtremal

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77.C5O
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C5O
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77.ExactLayer
section Layer
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem conjSub_exactLayer_eq (hΩ : ConjInvariant Ω) {c c' g : G} (hg : g * c * g⁻¹ = c') :
    conjSub g (ExactLayer.exactLayer Ω c) = ExactLayer.exactLayer Ω c' := by
  rw [← hg, ExactLayer.exactLayer_conj hΩ g c]

theorem conj_mem_exactLayer (hΩ : ConjInvariant Ω) {c c' g : G} (hg : g * c * g⁻¹ = c')
    {y : G} (hy : y ∈ ExactLayer.exactLayer Ω c) : g * y * g⁻¹ ∈ ExactLayer.exactLayer Ω c' := by
  rw [← conjSub_exactLayer_eq hΩ hg]
  exact conj_mem_conjSub hy

@[expose] noncomputable def conjLayer (hΩ : ConjInvariant Ω) {c c' g : G}
    (hg : g * c * g⁻¹ = c') : ↥(ExactLayer.exactLayer Ω c) ≃* ↥(ExactLayer.exactLayer Ω c') :=
  (Subgroup.equivMapOfInjective (ExactLayer.exactLayer Ω c) (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr (conjSub_exactLayer_eq hΩ hg))

@[expose] noncomputable def layerIso (hΩ : ConjInvariant Ω) {c c' g : G}
    (hg : g * c * g⁻¹ = c') : (↥(ExactLayer.exactLayer Ω c) ⧸ classicalInvolutionOddCore
        ↥(ExactLayer.exactLayer Ω c)) ≃*
      (↥(ExactLayer.exactLayer Ω c') ⧸ classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω c')) :=
  QuotientGroup.congr _ _ (conjLayer hΩ hg)
    (CFSG.ComponentClassification.OddCore.equiv_invariant (conjLayer hΩ hg))

theorem layerIso_mk (hΩ : ConjInvariant Ω) {c c' g : G} (hg : g * c * g⁻¹ = c')
    (y : ↥(ExactLayer.exactLayer Ω c)) :
    layerIso hΩ hg (QuotientGroup.mk y) =
      QuotientGroup.mk ⟨g * y * g⁻¹, conj_mem_exactLayer hΩ hg y.2⟩ :=
  rfl

theorem map_exactImg_layerIso (hΩ : ConjInvariant Ω) {c c' g : G} (hg : g * c * g⁻¹ = c')
    (K : Subgroup G) :
    (T7H.exactImg Ω c K).map (layerIso hΩ hg).toMonoidHom = T7H.exactImg Ω c' (conjSub g K) := by
  have hcore : ExactLayer.exactCore c' (conjSub g K) = conjSub g (ExactLayer.exactCore c K) := by
    rw [← hg]
    exact ExactLayer.exactCore_conjSub g c K
  have hg' : g⁻¹ * c' * g⁻¹⁻¹ = c := by rw [← hg]; group
  ext e
  constructor
  · rintro ⟨e₀, he₀, rfl⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp he₀
    refine Subgroup.mem_map.mpr ⟨⟨g * y * g⁻¹, conj_mem_exactLayer hΩ hg y.2⟩, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf, hcore]
    exact conj_mem_conjSub (Subgroup.mem_subgroupOf.mp hy)
  · intro he
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp he
    have hy' : (y : G) ∈ conjSub g (ExactLayer.exactCore c K) := by
      rw [← hcore]
      exact Subgroup.mem_subgroupOf.mp hy
    refine ⟨QuotientGroup.mk ⟨g⁻¹ * y * g⁻¹⁻¹, conj_mem_exactLayer hΩ hg' y.2⟩,
      Subgroup.mem_map.mpr ⟨⟨g⁻¹ * y * g⁻¹⁻¹, conj_mem_exactLayer hΩ hg' y.2⟩, ?_, rfl⟩, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      have := (mem_conjSub_iff).mp hy'
      simpa using this
    · show layerIso hΩ hg (QuotientGroup.mk _) = QuotientGroup.mk' _ y
      rw [layerIso_mk]
      congr 1
      apply Subtype.ext
      show g * (g⁻¹ * y.1 * g⁻¹⁻¹) * g⁻¹ = y.1
      group

theorem map_exactImg_layerAut (hΩ : ConjInvariant Ω) {c g : G}
    (hgc : g ∈ Subgroup.centralizer ({c} : Set G))
    (hb : conjSub g (ExactLayer.exactLayer Ω c) = ExactLayer.exactLayer Ω c) (K : Subgroup G) :
    (T7H.exactImg Ω c K).map (C25Y.layerAut (ExactLayer.exactLayer Ω c) hb).toMonoidHom =
      T7H.exactImg Ω c (conjSub g K) := by
  have hg : g * c * g⁻¹ = c := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hgc]
    group
  have heq : C25Y.layerAut (ExactLayer.exactLayer Ω c) hb = layerIso hΩ hg := by
    ext e
    induction e using QuotientGroup.induction_on with
    | H y => rfl
  rw [heq]
  exact map_exactImg_layerIso hΩ hg K

theorem layerAut_conj (hΩ : ConjInvariant Ω) {c c' g y : G} (hg : g * c * g⁻¹ = c')
    (hy : conjSub y (ExactLayer.exactLayer Ω c) = ExactLayer.exactLayer Ω c)
    (hy' : conjSub (g * y * g⁻¹) (ExactLayer.exactLayer Ω c') = ExactLayer.exactLayer Ω c')
    (e : (↥(ExactLayer.exactLayer Ω c') ⧸ classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω
        c'))) :
    C25Y.layerAut (ExactLayer.exactLayer Ω c') hy' e =
      layerIso hΩ hg (C25Y.layerAut (ExactLayer.exactLayer Ω c) hy ((layerIso hΩ hg).symm e)) := by
  obtain ⟨e₀, rfl⟩ := (layerIso hΩ hg).surjective e
  rw [MulEquiv.symm_apply_apply]
  induction e₀ using QuotientGroup.induction_on with
  | H w =>
    rw [layerIso_mk, C25Y.layerAut_mk, C25Y.layerAut_mk, layerIso_mk]
    congr 1
    apply Subtype.ext
    show g * y * g⁻¹ * (g * w.1 * g⁻¹) * (g * y * g⁻¹)⁻¹ = g * (y * w.1 * y⁻¹) * g⁻¹
    group
end Layer
section Ctx
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ a : G}
omit [Finite G] in

theorem exactCore_mul_eq [Finite G] {L : Subgroup G} (hL : L ≤ Subgroup.centralizer ({z} : Set G))
    (a : G) :
    ExactLayer.exactCore (a * z) L = ExactLayer.exactCore a L := by
  rw [ExactLayer.exactCore_def, ExactLayer.exactCore_def]
  ext k
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hk, h⟩
    refine ⟨hk, ?_⟩
    have hkz : k * z = z * k := Subgroup.mem_centralizer_singleton_iff.mp (hL hk)
    have : k * a * z = a * k * z := by
      calc k * a * z = k * (a * z) := by group
        _ = a * z * k := h
        _ = a * (z * k) := by group
        _ = a * (k * z) := by rw [hkz]
        _ = a * k * z := by group
    exact mul_right_cancel this
  · rintro ⟨hk, h⟩
    refine ⟨hk, ?_⟩
    have hkz : k * z = z * k := Subgroup.mem_centralizer_singleton_iff.mp (hL hk)
    calc k * (a * z) = k * a * z := by group
      _ = a * k * z := by rw [h]
      _ = a * (k * z) := by group
      _ = a * (z * k) := by rw [hkz]
      _ = a * z * k := by group

theorem Ctx.exactCore_az (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) :
    ExactLayer.exactCore (a * z) K = ExactLayer.exactCore a K :=
  exactCore_mul_eq (le_centralizer_of_isUniqueInvolution C.hyp.std.setting.hz) a

theorem Ctx.exactCore_az' (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) :
    ExactLayer.exactCore (a * z) K' = ExactLayer.exactCore a K' :=
  exactCore_mul_eq (le_centralizer_of_isUniqueInvolution
    (isUniqueInvolution_of_mem_twinSet C.hyp.std.setting.hz C.hyp.std.setting.hK')) a
end Ctx
end Asc77.C5O

end

section

namespace Asc77.C5O
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C5O
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ a : G}
namespace Swaps
open CFSG.ClassicalInvolution.Asc77.C5O.Swaps
variable {τ σ : G}

theorem false_of_comm [IsSimpleGroup G] (hM : ModelFacts)
    (D : Swaps Ω K K' W S R R' z t u₁ u₂ a τ σ)
    (hT1 : ∀ x ∈ (S : Subgroup G), ∀ y ∈ (S : Subgroup G), x * y * x⁻¹ * y⁻¹ ∈
      hBig D.ctx.hyp.std.setting.stand.modU.conjInvariant z a τ σ D.τC D.σC) : False := by
  have C := D.ctx
  have haS : a ∈ (S : Subgroup G) := C.haA.1
  have hne := CFSG.RankThree.PartTwo.Sec8.commutator_ne_top_of_extremal S hT1 haS
    (D.a_not_mem_hBig hM) (by rw [pow_two]; exact C.ha2) (fun g hg => by
      have hgS : g⁻¹ * a * g ∈ (S : Subgroup G) :=
        hg a ⟨haS, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
      exact D.extremal_mem_hBig hM (C.hyp.hzS _ hgS))
  apply hne
  obtain ⟨t', hT⟩ := T7T.exists_hyp25T C.hyp
  obtain ⟨x, -, y, -, hxy⟩ := hT.hqR.exists_not_commute
  rcases (Subgroup.commutator_normal (⊤ : Subgroup G) (⊤ : Subgroup G)).eq_bot_or_eq_top with
    h | h
  · exact (hxy ((isMulCommutative_iff.mp ((commutator_eq_bot_iff G).mp h)) x y)).elim
  · exact h
end Swaps
namespace Ctx
open CFSG.ClassicalInvolution.Asc77.C5O.Ctx

theorem exists_conj_mem_S [IsSimpleGroup G] (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) {w : G}
    (hwa : w * a = a * w) (hwz : w * z = z * w) (hw2 : IsPGroup 2 (Subgroup.zpowers w)) :
    ∃ g ∈ Subgroup.normalizer
      (((S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) :
        Subgroup G) : Set G), g⁻¹ * w * g ∈ (S : Subgroup G) := by
  set A₀ := (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) with hA₀
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer (A₀ : Set G) := fun s hs =>
    mem_normalizer_of_conjSub_eq (T7T.conjSub_centralizer_of_hyp C.hyp hs)
  have hSsyl : IsSylow2In (S : Subgroup G) (Subgroup.normalizer (A₀ : Set G)) :=
    ⟨hSN, S.isPGroup', fun V' _ hV' hle => S.is_maximal' hV' hle⟩
  have hfixA : ∀ h ∈ A₀, w * h * w⁻¹ = h := by
    intro h hh
    rcases C.hA0 h hh with e | e | e | e <;> rw [e]
    · group
    · rw [hwa]; group
    · rw [hwz]; group
    · calc w * (a * z) * w⁻¹ = (w * a) * z * w⁻¹ := by group
        _ = a * (w * z) * w⁻¹ := by rw [hwa]; group
        _ = a * z := by rw [hwz]; group
  have hwN : Subgroup.zpowers w ≤ Subgroup.normalizer (A₀ : Set G) := by
    refine Subgroup.zpowers_le.mpr (Subgroup.mem_normalizer_iff.mpr fun h => ⟨fun hh => ?_,
      fun hh => ?_⟩)
    · rw [hfixA h hh]; exact hh
    · have e1 := hfixA _ hh
      have e2 : h = w * h * w⁻¹ := by
        calc h = w⁻¹ * (w * h * w⁻¹) * w := by group
          _ = w⁻¹ * (w * (w * h * w⁻¹) * w⁻¹) * w := by rw [e1]
          _ = w * h * w⁻¹ := by group
      rw [e2]; exact hh
  obtain ⟨V, hV, hVle⟩ := IsSylow2In.exists_ge hw2 hwN
  obtain ⟨g, hg, hVeq⟩ := IsSylow2Of.exists_conj (show IsSylow2Of _ _ from hSsyl)
    (show IsSylow2Of _ _ from hV)
  refine ⟨g, hg, ?_⟩
  have h := hVle (Subgroup.mem_zpowers w)
  rw [hVeq] at h
  exact mem_conjSubgroup_iff.mp h

theorem mk_swaps [IsSimpleGroup G] (hM : ModelFacts)
    (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) {τ σ hτ hσ : G}
    (hhτX : hτ ∈ ExactLayer.exactLayer Ω (a * z)) (hhτ : hτ * z * hτ⁻¹ = τ) (hτz : τ * z = z * τ)
    (hτK : conjSub τ K = K') (hτn : ∀ h : G, h * a = a * h → h * z * h⁻¹ ≠ τ)
    (haτ : ¬ ∃ g : G, g * z * g⁻¹ = a * τ) (hhσX : hσ ∈ ExactLayer.exactLayer Ω a)
    (hhσ : hσ * z * hσ⁻¹ = σ) (hσz : σ * z = z * σ)
    (hσn : ∀ h : G, h * (a * z) = (a * z) * h → h * z * h⁻¹ ≠ σ)
    (haσ : ¬ ∃ g : G, g * z * g⁻¹ = (a * z) * σ) :
    Swaps Ω K K' W S R R' z t u₁ u₂ a τ σ := by
  obtain ⟨hzY, -, -, -, -, -⟩ := C.om5
  obtain ⟨hzY', -, -, -, -, -⟩ := C.swap.om5
  have hτX : τ ∈ ExactLayer.exactLayer Ω (a * z) := by
    rw [← hhτ]; exact mul_mem (mul_mem hhτX hzY') (inv_mem hhτX)
  have hσX : σ ∈ ExactLayer.exactLayer Ω a := by
    rw [← hhσ]; exact mul_mem (mul_mem hhσX hzY) (inv_mem hhσX)
  have hτaz : τ * (a * z) = (a * z) * τ :=
    Subgroup.mem_centralizer_singleton_iff.mp (ExactLayer.exactLayer_le_centralizer Ω (a * z) hτX)
  have hτa : τ * a = a * τ := by
    have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right C.hz2
    calc τ * a = τ * (a * z) * z⁻¹ := by group
      _ = (a * z) * τ * z⁻¹ := by rw [hτaz]
      _ = (a * z) * (τ * z) := by rw [hzi]; group
      _ = (a * z) * (z * τ) := by rw [hτz]
      _ = a * τ := by rw [← mul_assoc, C.mul_z_mul_z]
  have hσa : σ * a = a * σ :=
    Subgroup.mem_centralizer_singleton_iff.mp (ExactLayer.exactLayer_le_centralizer Ω a hσX)
  exact ⟨C, ⟨hτ, hhτ⟩, hτa, hτz, hτn, haτ, hτX, hτK, ⟨hσ, hhσ⟩, hσa, hσz, hσn, haσ, hσX,
    C.swap.interchange hM hhτX hhτ hτz hτK⟩

theorem exists_swaps [IsSimpleGroup G] (hM : ModelFacts)
    (C : Ctx Ω K K' W S R R' z t u₁ u₂ a) :
    (∃ τ σ : G, Swaps Ω K K' W S R R' z t u₁ u₂ a τ σ ∧ τ ∈ (S : Subgroup G)) ∨
      ∃ τ σ : G, Swaps Ω K K' W S R R' z t u₁ u₂ (a * z) τ σ ∧ τ ∈ (S : Subgroup G) := by
  classical
  have hs : Hyp23Setting Ω K K' z := C.hyp.std.setting
  have hΩ : HypOmegaModT Ω := hs.stand.modU
  have hz2 := C.hz2
  have hazz := C.mul_z_mul_z
  obtain ⟨t₀, ⟨h₀, hh₀X, hh₀⟩, ht₀z, -, ht₀K, -, ht₀n⟩ := C.swap.refSwap hM
  obtain ⟨s₀, ⟨k₀, hk₀X, hk₀⟩, hs₀z, -, hs₀K, -, hs₀n⟩ := C.refSwap hM
  have has₀ := C.not_conj_az_swap hM hk₀X hk₀ hs₀z hs₀K
  have hat₀ := C.swap.not_conj_az_swap hM hh₀X hh₀ ht₀z ht₀K
  rw [hazz] at hat₀
  have ht₀n' : ∀ h : G, h * a = a * h → h * z * h⁻¹ ≠ t₀ := by
    intro h hh hhz
    apply ht₀n h hhz
    rw [hazz]; exact hh
  have hs₀n' : ∀ h : G, h * (a * z) = (a * z) * h → h * z * h⁻¹ ≠ s₀ :=
    fun h hh hhz => hs₀n h hhz hh
  obtain ⟨hzY, -, -, -, -, -⟩ := C.om5
  obtain ⟨hzY', -, -, -, -, -⟩ := C.swap.om5
  have ht₀X : t₀ ∈ ExactLayer.exactLayer Ω (a * z) := by
    rw [← hh₀]; exact mul_mem (mul_mem hh₀X hzY') (inv_mem hh₀X)
  have ht₀az : t₀ * (a * z) = (a * z) * t₀ :=
    Subgroup.mem_centralizer_singleton_iff.mp (ExactLayer.exactLayer_le_centralizer Ω (a * z) ht₀X)
  have ht₀a : t₀ * a = a * t₀ := by
    have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
    calc t₀ * a = t₀ * (a * z) * z⁻¹ := by group
      _ = (a * z) * t₀ * z⁻¹ := by rw [ht₀az]
      _ = (a * z) * (t₀ * z) := by rw [hzi]; group
      _ = (a * z) * (z * t₀) := by rw [ht₀z]
      _ = a * t₀ := by rw [← mul_assoc, hazz]
  have ht₀2 : t₀ * t₀ = 1 := by
    rw [← hh₀]
    calc h₀ * z * h₀⁻¹ * (h₀ * z * h₀⁻¹) = h₀ * (z * z) * h₀⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  obtain ⟨g, hg, hgS⟩ := C.exists_conj_mem_S ht₀a ht₀z (isPGroup_zpowers_of_sq_eq_one ht₀2)
  have hgi := Subgroup.inv_mem _ hg
  have hgz : g⁻¹ * z * g = z := by
    have := C.norm_fix_z hgi
    rwa [inv_inv] at this
  set t₁ := g⁻¹ * t₀ * g with ht₁
  have ht₁z : t₁ * z = z * t₁ := by
    calc t₁ * z = g⁻¹ * (t₀ * (g * z * g⁻¹)) * g := by rw [ht₁]; group
      _ = g⁻¹ * (t₀ * z) * g := by
          rw [show g * z * g⁻¹ = z by
            calc g * z * g⁻¹ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [hgz]
              _ = z := by group]
      _ = g⁻¹ * (z * t₀) * g := by rw [ht₀z]
      _ = (g⁻¹ * z * g) * t₁ := by rw [ht₁]; group
      _ = z * t₁ := by rw [hgz]
  have hgzc : g * z * g⁻¹ = z := by
    calc g * z * g⁻¹ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [hgz]
      _ = z := by group
  have ht₁K : conjSub t₁ K = K' := by
    have ht₀K' : conjSub t₀ K' = K := by
      rw [← ht₀K, ← conjSub_mul, ht₀2, conjSub_one]
    rw [ht₁, conjSub_mul, conjSub_mul]
    rcases C25Y.conjSub_pair_of_central hs hgzc with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, ht₀K, ← e2, ← conjSub_mul, inv_mul_cancel, conjSub_one, e2]
    · rw [e1, ht₀K', ← e2, ← conjSub_mul, inv_mul_cancel, conjSub_one]
  have hpull : ∀ (b w : G), (∀ h : G, h * b = b * h → h * z * h⁻¹ ≠ w) →
      ∀ h : G, h * (g⁻¹ * b * g) = (g⁻¹ * b * g) * h → h * z * h⁻¹ ≠ g⁻¹ * w * g := by
    intro b w hn h hh hhz
    apply hn (g * h * g⁻¹)
    · calc g * h * g⁻¹ * b = g * (h * (g⁻¹ * b * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * b * g) * h) * g⁻¹ := by rw [hh]
        _ = b * (g * h * g⁻¹) := by group
    · calc g * h * g⁻¹ * z * (g * h * g⁻¹)⁻¹ = g * (h * (g⁻¹ * z * g) * h⁻¹) * g⁻¹ := by group
        _ = g * (g⁻¹ * w * g) * g⁻¹ := by rw [hgz, hhz]
        _ = w := by group
  have hpullG : ∀ b : G, (¬ ∃ g' : G, g' * z * g'⁻¹ = b * t₀) →
      ¬ ∃ g' : G, g' * z * g'⁻¹ = (g⁻¹ * b * g) * t₁ := by
    rintro b hn ⟨g', hg'⟩
    apply hn ⟨g * g', ?_⟩
    calc g * g' * z * (g * g')⁻¹ = g * (g' * z * g'⁻¹) * g⁻¹ := by group
      _ = g * ((g⁻¹ * b * g) * t₁) * g⁻¹ := by rw [hg']
      _ = b * t₀ := by rw [ht₁]; group
  have hh₁ : (g⁻¹ * h₀ * g) * z * (g⁻¹ * h₀ * g)⁻¹ = t₁ := by
    calc (g⁻¹ * h₀ * g) * z * (g⁻¹ * h₀ * g)⁻¹ = g⁻¹ * (h₀ * (g * z * g⁻¹) * h₀⁻¹) * g := by group
      _ = t₁ := by rw [hgzc, hh₀, ht₁]
  have hconjX : ∀ c : G, g⁻¹ * h₀ * g ∈ ExactLayer.exactLayer Ω (g⁻¹ * c * g) ↔
      h₀ ∈ ExactLayer.exactLayer Ω c := by
    intro c
    have e := ExactLayer.exactLayer_conj hΩ.conjInvariant g⁻¹ c
    rw [inv_inv] at e
    rw [e, mem_conjSub_iff, inv_inv]
    constructor <;> intro h <;> simpa [mul_assoc] using h
  rcases C.norm_a_cases hgi with hga | hga <;> rw [inv_inv] at hga
  ·
    left
    have hgaz : g⁻¹ * (a * z) * g = a * z := by
      calc g⁻¹ * (a * z) * g = (g⁻¹ * a * g) * (g⁻¹ * z * g) := by group
        _ = a * z := by rw [hga, hgz]
    have hX1 : g⁻¹ * h₀ * g ∈ ExactLayer.exactLayer Ω (a * z) := by
      rw [← hgaz]; exact (hconjX (a * z)).mpr hh₀X
    refine ⟨t₁, s₀, C.mk_swaps hM hX1 hh₁ ht₁z ht₁K ?_ ?_ hk₀X hk₀ hs₀z hs₀n' has₀, hgS⟩
    · have := hpull a t₀ ht₀n'
      rwa [hga] at this
    · have := hpullG a hat₀
      rwa [hga] at this
  ·
    right
    have hgaz : g⁻¹ * (a * z) * g = a * z * z := by
      calc g⁻¹ * (a * z) * g = (g⁻¹ * a * g) * (g⁻¹ * z * g) := by group
        _ = a * z * z := by rw [hga, hgz]
    have hX1 : g⁻¹ * h₀ * g ∈ ExactLayer.exactLayer Ω (a * z * z) := by
      rw [← hgaz]; exact (hconjX (a * z)).mpr hh₀X
    refine ⟨t₁, t₀, C.swap.mk_swaps hM hX1 hh₁ ht₁z ht₁K ?_ ?_ hh₀X hh₀ ht₀z ?_ ?_, hgS⟩
    · have := hpull a t₀ ht₀n'
      rwa [hga] at this
    · have := hpullG a hat₀
      rwa [hga] at this
    · intro h hh hhz
      apply ht₀n' h _ hhz
      rw [hazz] at hh; exact hh
    · rw [hazz]; exact hat₀
end Ctx
end Asc77.C5O

end

section

namespace Asc77.C5O
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C5O
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
variable {G : Type} [Group G] [Finite G]

@[expose] def twinM (a : G) (K K' : Subgroup G) : Subgroup G := ExactLayer.exactCore a K ⊔
    ExactLayer.exactCore a K'

@[expose] noncomputable def twinπ (Ω : Set (Subgroup G)) (c : G) {M : Subgroup G}
    (h : M ≤ ExactLayer.exactLayer Ω c) :
    ↥M →* ↥(ExactLayer.exactLayer Ω c) ⧸ classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω c) :=
  (QuotientGroup.mk' (classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω c))).comp
      (Subgroup.inclusion h)

theorem twinπ_apply (Ω : Set (Subgroup G)) (c : G) {M : Subgroup G} (h : M ≤ ExactLayer.exactLayer
    Ω c)
    (m : ↥M) : twinπ Ω c h m = QuotientGroup.mk ⟨(m : G), h m.2⟩ := rfl

theorem map_twinπ (Ω : Set (Subgroup G)) (c : G) {M B : Subgroup G} (h : M ≤ ExactLayer.exactLayer
    Ω c)
    (hB : B ≤ M) : (B.subgroupOf M).map (twinπ Ω c h) =
      (B.subgroupOf (ExactLayer.exactLayer Ω c)).map
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω c))) := by
  ext e
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨⟨m, h m.2⟩, hm, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hB hy⟩, hy, rfl⟩

theorem odd_card_ker_twinπ (Ω : Set (Subgroup G)) (c : G) {M : Subgroup G}
    (h : M ≤ ExactLayer.exactLayer Ω c) : Odd (Nat.card (twinπ Ω c h).ker) := by
  have h1 : Nat.card ((twinπ Ω c h).ker.map M.subtype) = Nat.card (twinπ Ω c h).ker :=
    Subgroup.card_map_of_injective M.subtype_injective
  have h2 : (twinπ Ω c h).ker.map M.subtype ≤ oddCoreIn (ExactLayer.exactLayer Ω c) := by
    rintro _ ⟨m, hm, rfl⟩
    exact (mk_eq_one_iff (ExactLayer.exactLayer Ω c) ⟨m, h m.2⟩).mp hm
  rw [← h1]
  exact Odd.of_dvd_nat (odd_card_oddCoreIn _) (Subgroup.card_dvd_of_le h2)
variable {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ a : G}
namespace Swaps
open CFSG.ClassicalInvolution.Asc77.C5O.Swaps
variable {τ σ : G}

theorem twinShare [IsSimpleGroup G]
    (D : Swaps Ω K K' W S R R' z t u₁ u₂ a τ σ)
    (hzY : z ∈ ExactLayer.exactLayer Ω a) (hu₁Y : u₁ ∈ ExactLayer.exactLayer Ω a) (hu₂Y : u₂ ∈
        ExactLayer.exactLayer Ω a)
    (hzY' : z ∈ ExactLayer.exactLayer Ω (a * z)) (hu₁Y' : u₁ ∈ ExactLayer.exactLayer Ω (a * z))
    (hu₂Y' : u₂ ∈ ExactLayer.exactLayer Ω (a * z))
    (hMa : twinM a K K' ≤ ExactLayer.exactLayer Ω a) (hMaz : twinM a K K' ≤ ExactLayer.exactLayer Ω
        (a * z)) :
    TwinShare (oddQuotientFamily (ExactLayer.exactPair Ω a)) (T7H.exactImg Ω a K)
      (T7H.exactImg Ω a K') (T7H.toBar Ω a z hzY) (T7H.toBar Ω a u₁ hu₁Y)
      (T7H.toBar Ω a u₂ hu₂Y) (oddQuotientFamily (ExactLayer.exactPair Ω (a * z)))
      (T7H.exactImg Ω (a * z) K) (T7H.exactImg Ω (a * z) K') (T7H.toBar Ω (a * z) z hzY')
      (T7H.toBar Ω (a * z) u₁ hu₁Y') (T7H.toBar Ω (a * z) u₂ hu₂Y')
      (twinπ Ω a hMa) (twinπ Ω (a * z) hMaz)
      ((ExactLayer.exactCore a K).subgroupOf (twinM a K K'))
      ((ExactLayer.exactCore a K').subgroupOf (twinM a K K')) := by
  classical
  have C := D.ctx
  have hs : Hyp23Setting Ω K K' z := C.hyp.std.setting
  have hΩ : HypOmegaModT Ω := hs.stand.modU
  obtain ⟨hzY₀, hu₁Y₀, hu₂Y₀, hK₂, hK₂', hD⟩ := C.om5
  obtain ⟨hzY₁, hu₁Y₁, hu₂Y₁, hK₃, hK₃', hD'⟩ := C.swap.om5
  have hcK := ExactLayer.exactCore_le_exactLayer hK₂
  have hcK' := ExactLayer.exactCore_le_exactLayer hK₂'
  have hcKz := C.exactCore_az ▸ ExactLayer.exactCore_le_exactLayer hK₃
  have hcKz' := C.exactCore_az' ▸ ExactLayer.exactCore_le_exactLayer hK₃'
  have hL : ExactLayer.exactCore a K ≤ twinM a K K' := le_sup_left
  have hL' : ExactLayer.exactCore a K' ≤ twinM a K K' := le_sup_right
  have hrange : ∀ (c : G) (hc : twinM a K K' ≤ ExactLayer.exactLayer Ω c),
      ExactLayer.exactCore a K ≤ ExactLayer.exactLayer Ω c → ExactLayer.exactCore a K' ≤
          ExactLayer.exactLayer Ω c →
      (twinπ Ω c hc).range =
        ((ExactLayer.exactCore a K).subgroupOf (ExactLayer.exactLayer Ω c)).map
          (QuotientGroup.mk' (classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω c))) ⊔
        ((ExactLayer.exactCore a K').subgroupOf (ExactLayer.exactLayer Ω c)).map
          (QuotientGroup.mk' (classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω c))) := by
    intro c hc h1 h2
    rw [MonoidHom.range_eq_map, ← Subgroup.subgroupOf_self, map_twinπ Ω c hc le_rfl, twinM,
      Subgroup.subgroupOf_sup h1 h2, Subgroup.map_sup]
  have hτ2 : τ * τ = 1 := by
    obtain ⟨cτ, hcτ⟩ := D.τG
    rw [← hcτ]
    calc cτ * z * cτ⁻¹ * (cτ * z * cτ⁻¹) = cτ * (z * z) * cτ⁻¹ := by group
      _ = 1 := by rw [C.hz2]; group
  have hτaC : τ * a * τ⁻¹ = a := by rw [D.τa]; group
  have hτK' : conjSub τ K' = K := by rw [← D.τK, ← conjSub_mul, hτ2, conjSub_one]
  have hcτ1 : conjSub τ (ExactLayer.exactCore a K) = ExactLayer.exactCore a K' := by
    rw [← ExactLayer.exactCore_conjSub, hτaC, D.τK]
  have hcτ2 : conjSub τ (ExactLayer.exactCore a K') = ExactLayer.exactCore a K := by
    rw [← ExactLayer.exactCore_conjSub, hτaC, hτK']
  have hτM : ∀ m ∈ twinM a K K', τ * m * τ⁻¹ ∈ twinM a K K' := by
    intro m hm
    have h1 : τ * m * τ⁻¹ ∈ conjSub τ (twinM a K K') := ⟨m, hm, rfl⟩
    have h2 : conjSub τ (twinM a K K') = twinM a K K' := by
      unfold twinM
      rw [conjSub, Subgroup.map_sup, ← conjSub, ← conjSub, hcτ1, hcτ2, sup_comm]
    rwa [h2] at h1
  have hτXa : conjSub τ (ExactLayer.exactLayer Ω a) = ExactLayer.exactLayer Ω a :=
    ExactLayer.conjSub_exactLayer hΩ.conjInvariant D.τC
  have hτXaz : conjSub τ (ExactLayer.exactLayer Ω (a * z)) = ExactLayer.exactLayer Ω (a * z) :=
    conjSub_eq_self_of_mem D.τX
  obtain ⟨D₀, hD1, i₀, hDi⟩ := hD.lie
  have hD4 : ∀ i, D₀.tag i ≠ .G2 ∧ D₀.tag i ≠ .trialityD4 := by
    intro i
    have hi : i = i₀ := Fin.ext (by have h1 := i.2; have h2 := i₀.2; omega)
    subst hi
    simp only [IsOrthTag] at hDi
    rcases hDi with ⟨-, ht, -⟩ | ⟨h6, -⟩ | ⟨h6, -⟩ | ⟨h7, -⟩ | ⟨h8, -⟩ | ⟨h8, -⟩
    · rw [ht]; exact ⟨by decide, by decide⟩
    all_goals omega
  obtain ⟨cτ, hcτ⟩ := D.τG
  refine ⟨hD, hD', ?_, ?_, odd_card_ker_twinπ Ω a hMa, odd_card_ker_twinπ Ω (a * z) hMaz,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [hrange a hMa hcK hcK']; rfl
  · rw [hrange (a * z) hMaz hcKz hcKz']
    unfold T7H.exactImg
    rw [C.exactCore_az, C.exactCore_az']
  · rw [map_twinπ Ω a hMa hL]; rfl
  · rw [map_twinπ Ω a hMa hL']; rfl
  · rw [map_twinπ Ω (a * z) hMaz hL]
    unfold T7H.exactImg
    rw [C.exactCore_az]
  · rw [map_twinπ Ω (a * z) hMaz hL']
    unfold T7H.exactImg
    rw [C.exactCore_az']
  · refine ⟨fun m => ⟨τ * m * τ⁻¹, hτM m m.2⟩, C25Y.layerAut _ hτXa, C25Y.layerAut _ hτXaz,
      fun m hm => ?_, fun m hm => ?_, fun m => rfl, fun m => rfl,
      ⟨QuotientGroup.mk ⟨τ, D.τX⟩, fun x => layerAut_of_mem _ D.τX hτXaz x⟩,
      C25Y.layerAut_involutive _ hτXa hτ2, ?_, C.not_hasBigFix hτ2 hτXa hcτ⟩
    · have h1 : τ * (m : G) * τ⁻¹ ∈ conjSub τ (ExactLayer.exactCore a K) := ⟨m, hm, rfl⟩
      rw [hcτ1] at h1
      exact h1
    · have h1 : τ * (m : G) * τ⁻¹ ∈ conjSub τ (ExactLayer.exactCore a K') := ⟨m, hm, rfl⟩
      rw [hcτ2] at h1
      exact h1
    · intro J hJ x hxJ hx4 hx2 hfix
      have hwC : cτ * z * cτ⁻¹ ∈ Subgroup.centralizer ({a} : Set G) := by
        rw [hcτ]; exact D.τC
      subst hcτ
      obtain ⟨h, hhC, hh⟩ := C25Y.c25_8_one C.hyp C.ha2 hzY hK₂ D₀ hD1 hD4 hwC hJ hxJ hx4 hx2
        hfix
      exact D.τn h (Subgroup.mem_centralizer_singleton_iff.mp hhC) hh

theorem comm_mem_hInf_fix [IsSimpleGroup G] (hM : ModelFacts) (hM8 : M8GFacts)
    (D : Swaps Ω K K' W S R R' z t u₁ u₂ a τ σ) {x y : G}
    (hxa : x * a = a * x) (hxz : x * z = z * x) (hxK : conjSub x K = K)
    (hya : y * a = a * y) (hyz : y * z = z * y) (hyK : conjSub y K = K) :
    x * y * x⁻¹ * y⁻¹ ∈ hSub D.ctx.hyp.std.setting.stand.modU.conjInvariant a τ D.τC ⊓
      hSub D.ctx.hyp.std.setting.stand.modU.conjInvariant (a * z) σ D.σC := by
  classical
  have C := D.ctx
  have hs : Hyp23Setting Ω K K' z := C.hyp.std.setting
  have hΩ : HypOmegaModT Ω := hs.stand.modU
  obtain ⟨hzY, hu₁Y, hu₂Y, hK₂, hK₂', -⟩ := C.om5
  obtain ⟨hzY', hu₁Y', hu₂Y', hK₃, hK₃', -⟩ := C.swap.om5
  have hMa : twinM a K K' ≤ ExactLayer.exactLayer Ω a :=
    sup_le (ExactLayer.exactCore_le_exactLayer hK₂) (ExactLayer.exactCore_le_exactLayer hK₂')
  have hMaz : twinM a K K' ≤ ExactLayer.exactLayer Ω (a * z) :=
    sup_le (C.exactCore_az ▸ ExactLayer.exactCore_le_exactLayer hK₃)
      (C.exactCore_az' ▸ ExactLayer.exactCore_le_exactLayer hK₃')
  have TS := D.twinShare hzY hu₁Y hu₂Y hzY' hu₁Y' hu₂Y' hMa hMaz
  have hcA : ∀ v : G, v * a = a * v → v * z = z * v →
      v ∈ Subgroup.centralizer ({a} : Set G) ∧ v ∈ Subgroup.centralizer ({a * z} : Set G) := by
    intro v hva hvz
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr hva,
      Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc v * (a * z) = (v * a) * z := by group
      _ = a * (v * z) := by rw [hva]; group
      _ = a * z * v := by rw [hvz]; group
  obtain ⟨hxCa, hxCaz⟩ := hcA x hxa hxz
  obtain ⟨hyCa, hyCaz⟩ := hcA y hya hyz
  have hK'of : ∀ v : G, v * z = z * v → conjSub v K = K → conjSub v K' = K' := by
    intro v hvz hvK
    have hvz' : v * z * v⁻¹ = z := by rw [hvz]; group
    rcases C25Y.conjSub_pair_of_central hs hvz' with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact h2
    · exact absurd (hvK.symm.trans h1) hs.hne.symm
  have hxK' := hK'of x hxz hxK
  have hyK' := hK'of y hyz hyK
  have hMv : ∀ v : G, v * a = a * v → conjSub v K = K → conjSub v K' = K' →
      ∀ m ∈ twinM a K K', v * m * v⁻¹ ∈ twinM a K K' := by
    intro v hva hvK hvK' m hm
    have hva' : v * a * v⁻¹ = a := by rw [hva]; group
    have h1 : conjSub v (ExactLayer.exactCore a K) = ExactLayer.exactCore a K := by
      rw [← ExactLayer.exactCore_conjSub, hva', hvK]
    have h2 : conjSub v (ExactLayer.exactCore a K') = ExactLayer.exactCore a K' := by
      rw [← ExactLayer.exactCore_conjSub, hva', hvK']
    have h3 : conjSub v (twinM a K K') = twinM a K K' := by
      unfold twinM
      rw [conjSub, Subgroup.map_sup, ← conjSub, ← conjSub, h1, h2]
    have : v * m * v⁻¹ ∈ conjSub v (twinM a K K') := ⟨m, hm, rfl⟩
    rwa [h3] at this
  set hX := hΩ.conjInvariant with hXdef
  have hxXa : conjSub x (ExactLayer.exactLayer Ω a) = ExactLayer.exactLayer Ω a :=
      ExactLayer.conjSub_exactLayer hX hxCa
  have hxXaz : conjSub x (ExactLayer.exactLayer Ω (a * z)) = ExactLayer.exactLayer Ω (a * z) :=
    ExactLayer.conjSub_exactLayer hX hxCaz
  have hyXa : conjSub y (ExactLayer.exactLayer Ω a) = ExactLayer.exactLayer Ω a :=
      ExactLayer.conjSub_exactLayer hX hyCa
  have hyXaz : conjSub y (ExactLayer.exactLayer Ω (a * z)) = ExactLayer.exactLayer Ω (a * z) :=
    ExactLayer.conjSub_exactLayer hX hyCaz
  obtain ⟨w, hw1, hw2⟩ := hM8.comm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ TS
    (C25Y.layerAut _ hxXa) (C25Y.layerAut _ hyXa) (C25Y.layerAut _ hxXaz)
    (C25Y.layerAut _ hyXaz)
    (by rw [map_exactImg_layerAut hX hxCa, hxK]) (by rw [map_exactImg_layerAut hX hxCa, hxK'])
    (by rw [map_exactImg_layerAut hX hxCaz, hxK]) (by rw [map_exactImg_layerAut hX hxCaz, hxK'])
    (by rw [map_exactImg_layerAut hX hyCa, hyK]) (by rw [map_exactImg_layerAut hX hyCa, hyK'])
    (by rw [map_exactImg_layerAut hX hyCaz, hyK]) (by rw [map_exactImg_layerAut hX hyCaz, hyK'])
    (fun m => ⟨⟨x * m * x⁻¹, hMv x hxa hxK hxK' m m.2⟩, rfl, rfl⟩)
    (fun m => ⟨⟨y * m * y⁻¹, hMv y hya hyK hyK' m m.2⟩, rfl, rfl⟩)
  have hwa : (w : G) ∈ ExactLayer.exactLayer Ω a := hMa w.2
  have hwaz : (w : G) ∈ ExactLayer.exactLayer Ω (a * z) := hMaz w.2
  have hcCa : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.centralizer ({a} : Set G) :=
    mul_mem (mul_mem (mul_mem hxCa hyCa) (inv_mem hxCa)) (inv_mem hyCa)
  have hcCaz : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.centralizer ({a * z} : Set G) :=
    mul_mem (mul_mem (mul_mem hxCaz hyCaz) (inv_mem hxCaz)) (inv_mem hyCaz)
  have htriv : ∀ (b : G) (hcb : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.centralizer ({b} : Set G))
      (hwb : (w : G) ∈ ExactLayer.exactLayer Ω b) (hMb : twinM a K K' ≤ ExactLayer.exactLayer Ω b)
      (hxb : conjSub x (ExactLayer.exactLayer Ω b) = ExactLayer.exactLayer Ω b)
      (hyb : conjSub y (ExactLayer.exactLayer Ω b) = ExactLayer.exactLayer Ω b),
      (∀ e, C25Y.layerAut _ hxb (C25Y.layerAut _ hyb ((C25Y.layerAut _ hxb).symm
        ((C25Y.layerAut _ hyb).symm e))) = twinπ Ω b hMb w * e * (twinπ Ω b hMb w)⁻¹) →
      x * y * x⁻¹ * y⁻¹ * (w : G)⁻¹ ∈ trivialOnQuot (ExactLayer.exactLayer Ω b) := by
    intro b hcb hwb hMb hxb hyb hw
    have hcX : conjSub (x * y * x⁻¹ * y⁻¹) (ExactLayer.exactLayer Ω b) = ExactLayer.exactLayer Ω b
        :=
      ExactLayer.conjSub_exactLayer hX hcb
    have hwi : conjSub (w : G)⁻¹ (ExactLayer.exactLayer Ω b) = ExactLayer.exactLayer Ω b :=
      conjSub_eq_self_of_mem (inv_mem hwb)
    have hcw : conjSub (x * y * x⁻¹ * y⁻¹ * (w : G)⁻¹) (ExactLayer.exactLayer Ω b) =
        ExactLayer.exactLayer Ω b := by
      rw [conjSub_mul, hwi, hcX]
    rw [← layerAut_eq_id_iff (ExactLayer.exactLayer Ω b) hcw]
    intro e
    rw [layerAut_mul_apply _ hcX hwi hcw, layerAut_comm_apply _ hxb hyb hcX, hw,
      layerAut_of_mem _ (inv_mem hwb), twinπ_apply]
    have e1 : (QuotientGroup.mk ⟨(w : G)⁻¹, inv_mem hwb⟩ :
        ↥(ExactLayer.exactLayer Ω b) ⧸ classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω b)) =
        (QuotientGroup.mk ⟨(w : G), hwb⟩)⁻¹ := by
      rw [← QuotientGroup.mk_inv]; rfl
    rw [e1]
    group
  exact D.mem_hInf_of_triv hM hcCa hcCaz hwa hwaz
    (htriv a hcCa hwa hMa hxXa hyXa hw1) (htriv (a * z) hcCaz hwaz hMaz hxXaz hyXaz hw2)

theorem comm_mem_hInf_swap [IsSimpleGroup G] (hM : ModelFacts) (hM8 : M8GFacts)
    (D : Swaps Ω K K' W S R R' z t u₁ u₂ a τ σ) {g y : G}
    (hga : g * a * g⁻¹ = a * z) (hgz : g * z = z * g) (hgK : conjSub g K = K)
    (hya : y * a = a * y) (hyz : y * z = z * y) (hyK : conjSub y K = K) :
    g * y * g⁻¹ * y⁻¹ ∈ hSub D.ctx.hyp.std.setting.stand.modU.conjInvariant a τ D.τC ⊓
      hSub D.ctx.hyp.std.setting.stand.modU.conjInvariant (a * z) σ D.σC := by
  classical
  have C := D.ctx
  have hs : Hyp23Setting Ω K K' z := C.hyp.std.setting
  have hΩ : HypOmegaModT Ω := hs.stand.modU
  obtain ⟨hzY, hu₁Y, hu₂Y, hK₂, hK₂', -⟩ := C.om5
  obtain ⟨hzY', hu₁Y', hu₂Y', hK₃, hK₃', -⟩ := C.swap.om5
  have hMa : twinM a K K' ≤ ExactLayer.exactLayer Ω a :=
    sup_le (ExactLayer.exactCore_le_exactLayer hK₂) (ExactLayer.exactCore_le_exactLayer hK₂')
  have hMaz : twinM a K K' ≤ ExactLayer.exactLayer Ω (a * z) :=
    sup_le (C.exactCore_az ▸ ExactLayer.exactCore_le_exactLayer hK₃)
      (C.exactCore_az' ▸ ExactLayer.exactCore_le_exactLayer hK₃')
  have TS := D.twinShare hzY hu₁Y hu₂Y hzY' hu₁Y' hu₂Y' hMa hMaz
  set hX := hΩ.conjInvariant with hXdef
  have hgz' : g * z * g⁻¹ = z := by rw [hgz]; group
  have hga' : g * (a * z) * g⁻¹ = a := by
    calc g * (a * z) * g⁻¹ = (g * a * g⁻¹) * (g * z * g⁻¹) := by group
      _ = a := by rw [hga, hgz', C.mul_z_mul_z]
  have hK'of : ∀ v : G, v * z * v⁻¹ = z → conjSub v K = K → conjSub v K' = K' := by
    intro v hvz hvK
    rcases C25Y.conjSub_pair_of_central hs hvz with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact h2
    · exact absurd (hvK.symm.trans h1) hs.hne.symm
  have hgK' := hK'of g hgz' hgK
  have hyz' : y * z * y⁻¹ = z := by rw [hyz]; group
  have hyK' := hK'of y hyz' hyK
  have hyCa : y ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hya
  have hyCaz : y ∈ Subgroup.centralizer ({a * z} : Set G) := by
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc y * (a * z) = (y * a) * z := by group
      _ = a * (y * z) := by rw [hya]; group
      _ = a * z * y := by rw [hyz]; group
  have hyXa : conjSub y (ExactLayer.exactLayer Ω a) = ExactLayer.exactLayer Ω a :=
      ExactLayer.conjSub_exactLayer hX hyCa
  have hyXaz : conjSub y (ExactLayer.exactLayer Ω (a * z)) = ExactLayer.exactLayer Ω (a * z) :=
    ExactLayer.conjSub_exactLayer hX hyCaz
  have hMv : ∀ (v : G) (b : G), v * a * v⁻¹ = b → ExactLayer.exactCore b K = ExactLayer.exactCore a
      K →
      ExactLayer.exactCore b K' = ExactLayer.exactCore a K' → conjSub v K = K → conjSub v K' = K' →
      ∀ m ∈ twinM a K K', v * m * v⁻¹ ∈ twinM a K K' := by
    intro v b hvb hb hb' hvK hvK' m hm
    have h1 : conjSub v (ExactLayer.exactCore a K) = ExactLayer.exactCore a K := by
      rw [← ExactLayer.exactCore_conjSub, hvb, hvK, hb]
    have h2 : conjSub v (ExactLayer.exactCore a K') = ExactLayer.exactCore a K' := by
      rw [← ExactLayer.exactCore_conjSub, hvb, hvK', hb']
    have h3 : conjSub v (twinM a K K') = twinM a K K' := by
      unfold twinM
      rw [conjSub, Subgroup.map_sup, ← conjSub, ← conjSub, h1, h2]
    have : v * m * v⁻¹ ∈ conjSub v (twinM a K K') := ⟨m, hm, rfl⟩
    rwa [h3] at this
  have hya' : y * a * y⁻¹ = a := by rw [hya]; group
  obtain ⟨w, hw1, hw2⟩ := hM8.commSwap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ TS
    (layerIso hX hga) (layerIso hX hga') (C25Y.layerAut _ hyXa) (C25Y.layerAut _ hyXaz)
    (by rw [map_exactImg_layerIso, hgK]) (by rw [map_exactImg_layerIso, hgK'])
    (by rw [map_exactImg_layerIso, hgK]) (by rw [map_exactImg_layerIso, hgK'])
    (by rw [map_exactImg_layerAut hX hyCa, hyK]) (by rw [map_exactImg_layerAut hX hyCa, hyK'])
    (by rw [map_exactImg_layerAut hX hyCaz, hyK]) (by rw [map_exactImg_layerAut hX hyCaz, hyK'])
    (fun m => ⟨⟨g * m * g⁻¹, hMv g (a * z) hga C.exactCore_az C.exactCore_az' hgK hgK' m m.2⟩,
      rfl, rfl⟩)
    (fun m => ⟨⟨y * m * y⁻¹, hMv y a hya' rfl rfl hyK hyK' m m.2⟩, rfl, rfl⟩)
  have hwa : (w : G) ∈ ExactLayer.exactLayer Ω a := hMa w.2
  have hwaz : (w : G) ∈ ExactLayer.exactLayer Ω (a * z) := hMaz w.2
  have hgyCaz : g * y * g⁻¹ ∈ Subgroup.centralizer ({a} : Set G) := by
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have h := Subgroup.mem_centralizer_singleton_iff.mp hyCaz
    calc g * y * g⁻¹ * a = g * (y * (g⁻¹ * a * g)) * g⁻¹ := by group
      _ = g * (y * (a * z)) * g⁻¹ := by
          rw [show g⁻¹ * a * g = a * z by
            calc g⁻¹ * a * g = g⁻¹ * (g * (a * z) * g⁻¹) * g := by rw [hga']
              _ = a * z := by group]
      _ = g * ((a * z) * y) * g⁻¹ := by rw [h]
      _ = (g * (a * z) * g⁻¹) * (g * y * g⁻¹) := by group
      _ = a * (g * y * g⁻¹) := by rw [hga']
  have hgyCa : g * y * g⁻¹ ∈ Subgroup.centralizer ({a * z} : Set G) := by
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have h := Subgroup.mem_centralizer_singleton_iff.mp hyCa
    calc g * y * g⁻¹ * (a * z) = g * (y * (g⁻¹ * (a * z) * g)) * g⁻¹ := by group
      _ = g * (y * a) * g⁻¹ := by
          rw [show g⁻¹ * (a * z) * g = a by
            calc g⁻¹ * (a * z) * g = g⁻¹ * (g * a * g⁻¹) * g := by rw [hga]
              _ = a := by group]
      _ = g * (a * y) * g⁻¹ := by rw [h]
      _ = (g * a * g⁻¹) * (g * y * g⁻¹) := by group
      _ = a * z * (g * y * g⁻¹) := by rw [hga]
  have hcCa : g * y * g⁻¹ * y⁻¹ ∈ Subgroup.centralizer ({a} : Set G) :=
    mul_mem hgyCaz (inv_mem hyCa)
  have hcCaz : g * y * g⁻¹ * y⁻¹ ∈ Subgroup.centralizer ({a * z} : Set G) :=
    mul_mem hgyCa (inv_mem hyCaz)
  have hyia : conjSub y⁻¹ (ExactLayer.exactLayer Ω a) = ExactLayer.exactLayer Ω a :=
    ExactLayer.conjSub_exactLayer hX (inv_mem hyCa)
  have hyiaz : conjSub y⁻¹ (ExactLayer.exactLayer Ω (a * z)) = ExactLayer.exactLayer Ω (a * z) :=
    ExactLayer.conjSub_exactLayer hX (inv_mem hyCaz)
  have hgyXa : conjSub (g * y * g⁻¹) (ExactLayer.exactLayer Ω a) = ExactLayer.exactLayer Ω a :=
    ExactLayer.conjSub_exactLayer hX hgyCaz
  have hgyXaz : conjSub (g * y * g⁻¹) (ExactLayer.exactLayer Ω (a * z)) = ExactLayer.exactLayer Ω
      (a * z) :=
    ExactLayer.conjSub_exactLayer hX hgyCa
  refine D.mem_hInf_of_triv hM hcCa hcCaz hwa hwaz
    (mul_inv_mem_trivialOnQuot _ hwa (ExactLayer.conjSub_exactLayer hX hcCa) fun e => ?_)
    (mul_inv_mem_trivialOnQuot _ hwaz (ExactLayer.conjSub_exactLayer hX hcCaz) fun e => ?_)
  · rw [layerAut_mul_apply _ hgyXa hyia, ← layerAut_symm_apply _ hyXa hyia,
      layerAut_conj hX hga' hyXaz hgyXa, hw1]
    rfl
  · rw [layerAut_mul_apply _ hgyXaz hyiaz, ← layerAut_symm_apply _ hyXaz hyiaz,
      layerAut_conj hX hga hyXa hgyXaz, hw2]
    rfl

theorem comm_mem_hBig [IsSimpleGroup G] (hM : ModelFacts) (hM8 : M8GFacts)
    (D : Swaps Ω K K' W S R R' z t u₁ u₂ a τ σ) (hτS : τ ∈ (S : Subgroup G)) :
    ∀ x ∈ (S : Subgroup G), ∀ y ∈ (S : Subgroup G), x * y * x⁻¹ * y⁻¹ ∈
      hBig D.ctx.hyp.std.setting.stand.modU.conjInvariant z a τ σ D.τC D.σC := by
  classical
  have C := D.ctx
  have hs : Hyp23Setting Ω K K' z := C.hyp.std.setting
  have hΩ := D.ctx.hyp.std.setting.stand.modU.conjInvariant
  obtain ⟨hzY', -, -, -, -, -⟩ := C.swap.om5
  have hτH₀ : τ ∈ hSub hΩ a τ D.τC ⊓ hSub hΩ (a * z) σ D.σC :=
    ⟨mem_hSub_self hΩ D.τC, le_hSub_layer hΩ D.σC D.τX⟩
  have hH₀ : hSub hΩ a τ D.τC ⊓ hSub hΩ (a * z) σ D.σC ≤ hBig hΩ z a τ σ D.τC D.σC :=
    le_mulSub_left _
  have hSz : ∀ v ∈ (S : Subgroup G), v * z * v⁻¹ = z := by
    intro v hv; rw [C.hyp.hzS v hv]; group
  set N₀ := (S : Subgroup G) ⊓ Subgroup.normalizer (K : Set G) with hN₀
  have hNK : ∀ v ∈ N₀, conjSub v K = K := fun v hv => conjSub_eq_of_mem_normalizer hv.2
  have hfix : ∀ v ∈ N₀, v * a * v⁻¹ = a → v * a = a * v := by
    intro v _ h
    calc v * a = (v * a * v⁻¹) * v := by group
      _ = a * v := by rw [h]
  have hcomm : ∀ x ∈ N₀, ∀ y ∈ N₀, x * a * x⁻¹ = a ∨ y * a * y⁻¹ = a →
      x * y * x⁻¹ * y⁻¹ ∈ hSub hΩ a τ D.τC ⊓ hSub hΩ (a * z) σ D.σC := by
    intro x hx y hy hxy
    rcases C.hconj x hx.1 with hxa | hxa <;> rcases C.hconj y hy.1 with hya | hya
    · exact D.comm_mem_hInf_fix hM hM8 (hfix x hx hxa) (C.hyp.hzS x hx.1) (hNK x hx)
        (hfix y hy hya) (C.hyp.hzS y hy.1) (hNK y hy)
    ·
      have h := D.comm_mem_hInf_swap hM hM8 hya (C.hyp.hzS y hy.1) (hNK y hy)
        (hfix x hx hxa) (C.hyp.hzS x hx.1) (hNK x hx)
      have e : x * y * x⁻¹ * y⁻¹ = (y * x * y⁻¹ * x⁻¹)⁻¹ := by group
      rw [e]; exact inv_mem h
    · exact D.comm_mem_hInf_swap hM hM8 hxa (C.hyp.hzS x hx.1) (hNK x hx)
        (hfix y hy hya) (C.hyp.hzS y hy.1) (hNK y hy)
    · rcases hxy with h | h
      · rw [h] at hxa; exact absurd (mul_left_cancel (a := a) (hxa.symm.trans (mul_one a).symm))
          C.hz1
      · rw [h] at hya; exact absurd (mul_left_cancel (a := a) (hya.symm.trans (mul_one a).symm))
          C.hz1
  have hcommN : ∀ x ∈ N₀, ∀ y ∈ N₀, x * y * x⁻¹ * y⁻¹ ∈ hBig hΩ z a τ σ D.τC D.σC := by
    intro x hx y hy
    by_cases hxa : x * a * x⁻¹ = a
    · exact hH₀ (hcomm x hx y hy (Or.inl hxa))
    by_cases hya : y * a * y⁻¹ = a
    · exact hH₀ (hcomm x hx y hy (Or.inr hya))
    have hxa' : x * a * x⁻¹ = a * z := (C.hconj x hx.1).resolve_left hxa
    have hya' : y * a * y⁻¹ = a * z := (C.hconj y hy.1).resolve_left hya
    have hyx : y * x⁻¹ ∈ N₀ := mul_mem hy (inv_mem hx)
    have hyxa : (y * x⁻¹) * a * (y * x⁻¹)⁻¹ = a := by
      have h1 : x⁻¹ * a * x = a * z := by
        have hz' : x⁻¹ * z * x = z := by
          have := hSz x⁻¹ (inv_mem hx.1)
          rwa [inv_inv] at this
        calc x⁻¹ * a * x = x⁻¹ * (x * a * x⁻¹ * z⁻¹) * x := by rw [hxa']; group
          _ = a * (x⁻¹ * z * x)⁻¹ := by group
          _ = a * z := by rw [hz', inv_eq_of_mul_eq_one_right C.hz2]
      calc (y * x⁻¹) * a * (y * x⁻¹)⁻¹ = y * (x⁻¹ * a * x) * y⁻¹ := by group
        _ = y * (a * z) * y⁻¹ := by rw [h1]
        _ = (y * a * y⁻¹) * (y * z * y⁻¹) := by group
        _ = a := by rw [hya', hSz y hy.1, C.mul_z_mul_z]
    have e : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹) * x⁻¹ * (y * x⁻¹)⁻¹ := by group
    rw [e]
    exact hH₀ (hcomm x hx _ hyx (Or.inr hyxa))
  refine comm_mem_of_factor (fun s hs q hq => conj_mem_hBig hM D (hSz s hs) hq) inf_le_left
    (fun s hsS => ?_) hcommN
  by_cases hsK : conjSub s K = K
  · exact ⟨s, ⟨hsS, mem_normalizer_of_conjSub_eq hsK⟩, 1, one_mem _, (mul_one s).symm⟩
  · have hsK' : conjSub s K = K' := by
      rcases C25Y.conjSub_pair_of_central hs (hSz s hsS) with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact absurd h1 hsK
      · exact h1
    have hsK'' : conjSub s K' = K := by
      rcases C25Y.conjSub_pair_of_central hs (hSz s hsS) with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact absurd h1 hsK
      · exact h2
    refine ⟨s * τ, ⟨mul_mem hsS hτS, mem_normalizer_of_conjSub_eq ?_⟩, τ⁻¹,
      inv_mem (hH₀ hτH₀), by group⟩
    rw [conjSub_mul, D.τK, hsK'']
end Swaps
end Asc77.C5O

end

section

namespace Asc77.C5O
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C5O

theorem c25_11Om5_of (hM : ModelFacts) (hM8 : M8GFacts) : C25Y.C25_11Ω5 := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haA ha2 ha1 haz hconj hA0 hbad hbad' h5' h5
  have C : Ctx Ω K K' W S R R' z t u₁ u₂ a :=
    ⟨hyp, haA, ha2, ha1, haz, hconj, hA0, hbad, hbad', h5, h5'⟩
  rcases C.exists_swaps hM with ⟨τ, σ, D, hτS⟩ | ⟨τ, σ, D, hτS⟩
  · exact D.false_of_comm hM (D.comm_mem_hBig hM hM8 hτS)
  · exact D.false_of_comm hM (D.comm_mem_hBig hM hM8 hτS)
end Asc77.C5O

end

end CFSG.ClassicalInvolution.Q3.Q3T8
