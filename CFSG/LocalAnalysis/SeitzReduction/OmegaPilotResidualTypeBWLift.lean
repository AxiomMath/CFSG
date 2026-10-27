module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeBCWall
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeBCCore
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeAFixSpace

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Module Subgroup CFSG.Assembly.LowTwoRank
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect
  map_perfectCore perfectCore_eq_self_of_perfect)
open LinearPilot (autFixSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (isometryConjugationHom)
open CFSG.RankThree.PartOne.KCAlternating (IsSymplecticBasis)
open scoped commutatorElement

section Groups

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def linPointFixer (C : Submodule K V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | ∀ c ∈ C, g c = c}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {a b} ha hb c hc => by
    change a (b c) = c
    rw [hb c hc, ha c hc]
  inv_mem' := fun {a} ha c hc => by
    change a.symm c = c
    conv_lhs => rw [← ha c hc]
    exact a.symm_apply_apply c

@[expose] def linSetStabilizer [FiniteDimensional K V] (U : Submodule K V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | ∀ u ∈ U, g u ∈ U}
  one_mem' := fun _ hu => hu
  mul_mem' := fun ha hb u hu => ha _ (hb u hu)
  inv_mem' := fun ha u hu => symm_mem_of_mapsTo ha u hu

@[expose] noncomputable def stabRestrictHom [FiniteDimensional K V] (U : Submodule K V) :
    ↥(linSetStabilizer U) →* Module.End K U where
  toFun g := ((g : V ≃ₗ[K] V) : V →ₗ[K] V).restrict g.2
  map_one' := by
    apply LinearMap.ext
    intro u
    rfl
  map_mul' g g' := by
    apply LinearMap.ext
    intro u
    rfl

end Groups

section Split

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  (N : (Fin d → K) →ₗ[K] (Fin d → K)) {U C : Submodule K (Fin d → K)}

theorem isCompl_comap_ker (hUK : U ≤ LinearMap.ker N) (hCK : C ≤ LinearMap.ker N)
    (hdisj : U ⊓ C = ⊥) (hsup : U ⊔ C = LinearMap.ker N) :
    IsCompl (U.comap (LinearMap.ker N).subtype) (C.comap (LinearMap.ker N).subtype) := by
  refine IsCompl.of_eq ?_ ?_
  · rw [← Submodule.comap_inf, hdisj, Submodule.comap_bot, Submodule.ker_subtype]
  · rw [eq_top_iff]
    intro z _
    have hz : (z : Fin d → K) ∈ U ⊔ C := by
      rw [hsup]
      exact z.2
    obtain ⟨u, hu, c, hc, huc⟩ := Submodule.mem_sup.mp hz
    have e : z = ⟨u, hUK hu⟩ + ⟨c, hCK hc⟩ := Subtype.ext huc.symm
    rw [e]
    exact Submodule.add_mem_sup (show _ ∈ U.comap (LinearMap.ker N).subtype from hu)
      (show _ ∈ C.comap (LinearMap.ker N).subtype from hc)

theorem exists_decomp_of_mem_ker (hsup : U ⊔ C = LinearMap.ker N) {z : Fin d → K}
    (hz : z ∈ LinearMap.ker N) : ∃ (u : U) (c : Fin d → K), c ∈ C ∧ z = (u : Fin d → K) + c := by
  rw [← hsup] at hz
  obtain ⟨u, hu, c, hc, rfl⟩ := Submodule.mem_sup.mp hz
  exact ⟨⟨u, hu⟩, c, hc, rfl⟩

variable (h : U →ₗ[K] U) (hUK : U ≤ LinearMap.ker N) (hCK : C ≤ LinearMap.ker N)
  (hdisj : U ⊓ C = ⊥) (hsup : U ⊔ C = LinearMap.ker N)

@[expose] noncomputable def splitLiftMap : LinearMap.ker N →ₗ[K] (Fin d → K) :=
  LinearMap.ofIsCompl (isCompl_comap_ker N hUK hCK hdisj hsup)
    (U.subtype ∘ₗ h ∘ₗ (Submodule.comapSubtypeEquivOfLe hUK).toLinearMap)
    ((LinearMap.ker N).subtype ∘ₗ (C.comap (LinearMap.ker N).subtype).subtype)

theorem splitLiftMap_apply_add (u : U) {c : Fin d → K} (hc : c ∈ C) :
    splitLiftMap N h hUK hCK hdisj hsup ⟨(u : Fin d → K) + c, add_mem (hUK u.2) (hCK hc)⟩ =
      (h u : Fin d → K) + c := by
  have e : (⟨(u : Fin d → K) + c, add_mem (hUK u.2) (hCK hc)⟩ : LinearMap.ker N) =
      ((⟨⟨u, hUK u.2⟩, u.2⟩ : U.comap (LinearMap.ker N).subtype) : LinearMap.ker N) +
      ((⟨⟨c, hCK hc⟩, hc⟩ : C.comap (LinearMap.ker N).subtype) : LinearMap.ker N) := rfl
  rw [e, map_add, splitLiftMap, LinearMap.ofIsCompl_apply_left, LinearMap.ofIsCompl_apply_right]
  rfl

theorem splitLiftMap_apply (z : LinearMap.ker N) : ∃ (u : U) (c : Fin d → K), c ∈ C ∧
    (z : Fin d → K) = (u : Fin d → K) + c ∧
      splitLiftMap N h hUK hCK hdisj hsup z = (h u : Fin d → K) + c := by
  obtain ⟨u, c, hc, hz⟩ := exists_decomp_of_mem_ker N hsup z.2
  refine ⟨u, c, hc, hz, ?_⟩
  have e : z = ⟨(u : Fin d → K) + c, add_mem (hUK u.2) (hCK hc)⟩ := Subtype.ext hz
  rw [e]
  exact splitLiftMap_apply_add N h hUK hCK hdisj hsup u hc

theorem quad_splitLiftMap
    (hadj : ∀ x y, QuadraticMap.polarBilin Q (N x) y = QuadraticMap.polarBilin Q x (N y))
    (hUW : U ≤ LinearMap.range N) (hQU : ∀ u ∈ U, Q u = 0) (z : LinearMap.ker N) :
    Q (splitLiftMap N h hUK hCK hdisj hsup z) = Q z := by
  obtain ⟨u, c, hc, hz, hφ⟩ := splitLiftMap_apply N h hUK hCK hdisj hsup z
  rw [hφ, hz, quad_add_eq, quad_add_eq, hQU _ (h u).2, hQU _ u.2,
    polar_mem_range_ker N hadj (hUW (h u).2) (hCK hc), polar_mem_range_ker N hadj (hUW u.2) (hCK hc)]

theorem splitLiftMap_injective (hh : Function.Injective h) :
    Function.Injective (splitLiftMap N h hUK hCK hdisj hsup) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz0
  obtain ⟨u, c, hc, hz, hφ⟩ := splitLiftMap_apply N h hUK hCK hdisj hsup z
  rw [hz0] at hφ
  have hhu : (h u : Fin d → K) = -c := eq_neg_of_add_eq_zero_left hφ.symm
  have hmem : (h u : Fin d → K) ∈ U ⊓ C := ⟨(h u).2, by rw [hhu]; exact C.neg_mem hc⟩
  rw [hdisj, Submodule.mem_bot] at hmem
  have hu0 : h u = 0 := Subtype.ext hmem
  have hu : u = 0 := hh (by rw [hu0, map_zero])
  have hc0 : c = 0 := by
    rw [hmem] at hhu
    exact neg_eq_zero.mp hhu.symm
  apply Subtype.ext
  rw [hz, hu, hc0, Submodule.coe_zero, add_zero, Submodule.coe_zero]

end Split

section Witt

variable {K : Type} [Field K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  (N : (Fin d → K) →ₗ[K] (Fin d → K))
  (hadj : ∀ x y, QuadraticMap.polarBilin Q (N x) y = QuadraticMap.polarBilin Q x (N y))
  {U C : Submodule K (Fin d → K)} (h : U →ₗ[K] U) (hUK : U ≤ LinearMap.ker N)
  (hCK : C ≤ LinearMap.ker N) (hdisj : U ⊓ C = ⊥) (hsup : U ⊔ C = LinearMap.ker N)

include hadj hUK hCK hdisj hsup in
theorem exists_orth_splitLift (hB : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hUW : U ≤ LinearMap.range N) (hQU : ∀ u ∈ U, Q u = 0) (hh : Function.Injective h) :
    ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, (∀ u : U, g u = h u) ∧ ∀ c ∈ C, g c = c := by
  have hφinj := splitLiftMap_injective N h hUK hCK hdisj hsup hh
  have hquad := quad_splitLiftMap N h hUK hCK hdisj hsup hadj hUW hQU
  let b := Module.finBasis K (LinearMap.ker N)
  have l1 : LinearIndependent K ((LinearMap.ker N).subtype ∘ b) :=
    b.linearIndependent.map' (LinearMap.ker N).subtype (Submodule.ker_subtype _)
  have l2 : LinearIndependent K (splitLiftMap N h hUK hCK hdisj hsup ∘ b) :=
    b.linearIndependent.map' (splitLiftMap N h hUK hCK hdisj hsup)
      (LinearMap.ker_eq_bot.mpr hφinj)
  obtain ⟨g, hgO, hg⟩ :=
    CFSG.RankThree.OrthogonalInvolutions.exists_mem_orthogonalGroup_apply_eq hB
      ((LinearMap.ker N).subtype ∘ b) (splitLiftMap N h hUK hCK hdisj hsup ∘ b) l1 l2
      (fun i => hquad (b i))
      (fun i j => by
        simp only [Function.comp_apply]
        rw [QuadraticMap.polar, QuadraticMap.polar, ← map_add (splitLiftMap N h hUK hCK hdisj hsup),
          hquad, hquad, hquad, Submodule.coe_add]
        rfl)
  have hgφ : ∀ z : LinearMap.ker N, g z = splitLiftMap N h hUK hCK hdisj hsup z := by
    have hext : (g : (Fin d → K) →ₗ[K] (Fin d → K)) ∘ₗ (LinearMap.ker N).subtype =
        splitLiftMap N h hUK hCK hdisj hsup := b.ext fun i => hg i
    intro z
    exact LinearMap.congr_fun hext z
  refine ⟨g, hgO, fun u => ?_, fun c hc => ?_⟩
  · have e := hgφ ⟨(u : Fin d → K) + 0, add_mem (hUK u.2) (hCK C.zero_mem)⟩
    rw [splitLiftMap_apply_add N h hUK hCK hdisj hsup u C.zero_mem] at e
    simpa using e
  · have e := hgφ ⟨((0 : U) : Fin d → K) + c, add_mem (hUK (0 : U).2) (hCK hc)⟩
    rw [splitLiftMap_apply_add N h hUK hCK hdisj hsup 0 hc, map_zero] at e
    simpa using e

omit [CharP K 2] in
include hadj hsup in
theorem commute_splitLift (hB : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hNN : ∀ v, N (N v) = 0) (hUW : U ≤ LinearMap.range N)
    (hD : ∀ u ∈ U, ∀ z, N z ∈ C → QuadraticMap.polar Q (u : Fin d → K) z = 0)
    (βU : LinearMap.BilinForm K U)
    (hβU : ∀ (u u' : U) (z : Fin d → K), N z = u' → βU u u' = QuadraticMap.polar Q u z)
    (hh : ∀ u u', βU (h u) (h u') = βU u u')
    {g : (Fin d → K) ≃ₗ[K] (Fin d → K)} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hgU : ∀ u : U, g u = h u) (hgC : ∀ c ∈ C, g c = c) (x : Fin d → K) :
    g (N x) = N (g x) := by
  have hdec : ∀ a : Fin d → K, ∃ (ua : U) (ca : Fin d → K), ca ∈ C ∧
      ca ∈ LinearMap.range N ∧ N a = (ua : Fin d → K) + ca := by
    intro a
    obtain ⟨ua, ca, hca, ha⟩ :=
      exists_decomp_of_mem_ker N hsup (range_le_ker N hNN (LinearMap.mem_range_self N a))
    refine ⟨ua, ca, hca, ?_, ha⟩
    have e : ca = N a - ua := by rw [ha]; abel
    rw [e]
    exact sub_mem (LinearMap.mem_range_self N a) (hUW ua.2)
  refine commute_of_wall_isometry hB N hadj hg (fun b => ?_) x
  obtain ⟨ub, cb, hcb, hcbW, hb⟩ := hdec b
  obtain ⟨c₁, hc₁⟩ := hUW (h ub).2
  obtain ⟨c₂, hc₂⟩ := hcbW
  obtain ⟨b₁, hb₁⟩ := hUW ub.2
  have hgNb : g (N b) = (h ub : Fin d → K) + cb := by rw [hb, map_add, hgU, hgC cb hcb]
  refine ⟨c₁ + c₂, by rw [hgNb, map_add, hc₁, hc₂], fun a => ?_⟩
  obtain ⟨ua, ca, hca, hcaW, ha⟩ := hdec a
  obtain ⟨za, hza⟩ := hcaW
  have hgNa : g (N a) = (h ua : Fin d → K) + ca := by rw [ha, map_add, hgU, hgC ca hca]
  have k1 : QuadraticMap.polar Q (h ua : Fin d → K) c₁ = βU ua ub := by
    rw [← hβU _ _ c₁ hc₁, hh]
  have k2 : QuadraticMap.polar Q (h ua : Fin d → K) c₂ = 0 :=
    hD _ (h ua).2 c₂ (by rw [hc₂]; exact hcb)
  have k3 : QuadraticMap.polar Q ca c₁ = 0 := by
    rw [← hza, ← QuadraticMap.polarBilin_apply_apply, hadj, QuadraticMap.polarBilin_apply_apply,
      hc₁, QuadraticMap.polar_comm]
    exact hD _ (h ub).2 za (by rw [hza]; exact hca)
  have k4 : QuadraticMap.polar Q (ua : Fin d → K) b₁ = βU ua ub := (hβU ua ub b₁ hb₁).symm
  have k5 : QuadraticMap.polar Q ca b₁ = 0 := by
    rw [← hza, ← QuadraticMap.polarBilin_apply_apply, hadj, QuadraticMap.polarBilin_apply_apply,
      hb₁, QuadraticMap.polar_comm]
    exact hD _ ub.2 za (by rw [hza]; exact hca)
  have k6 : QuadraticMap.polar Q (ua : Fin d → K) c₂ = 0 :=
    hD _ ua.2 c₂ (by rw [hc₂]; exact hcb)
  have hker : b - b₁ - c₂ ∈ LinearMap.ker N := by
    rw [LinearMap.mem_ker, map_sub, map_sub, hb₁, hc₂, hb]
    abel
  have k7 : QuadraticMap.polar Q (N a) b = QuadraticMap.polar Q (N a) (b₁ + c₂) := by
    have e := polar_range_ker N hadj a hker
    rw [QuadraticMap.polar_sub_right, QuadraticMap.polar_sub_right] at e
    rw [QuadraticMap.polar_add_right]
    linear_combination e
  rw [hgNa, k7, ha]
  simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right]
  rw [k1, k2, k3, k4, k5, k6]

end Witt

section Core

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem exists_core_restrict_eq (hQ : ∃ v, Q v ≠ 0)
    (hB : (QuadraticMap.polarBilin Q).Nondegenerate) (hq4 : 4 ≤ Nat.card K)
    (s : matrixIsometries Q) (hss : s * s = 1) {U C : Submodule K (Fin d → K)}
    (hUW : U ≤ LinearMap.range (sNil s.val)) (hQU : ∀ u ∈ U, Q u = 0)
    (hCK : C ≤ LinearMap.ker (sNil s.val)) (hdisj : U ⊓ C = ⊥)
    (hsup : U ⊔ C = LinearMap.ker (sNil s.val))
    (hD : ∀ u ∈ U, ∀ z, sNil s.val z ∈ C → QuadraticMap.polar Q (u : Fin d → K) z = 0)
    (βU : LinearMap.BilinForm K U)
    (hβU : ∀ (u u' : U) (z : Fin d → K), sNil s.val z = u' →
      βU u u' = QuadraticMap.polar Q u z)
    (hβ : βU.IsAlt) (hβn : βU.Nondegenerate)
    (h : U →ₗ[K] U) (hh : ∀ u u', βU (h u) (h u') = βU u u') :
    ∃ x ∈ perfectCore (autFixSubgroup (isometryConjugationHom Q s)),
      (∀ u : U, projLift hQ x u = h u) ∧ ∀ c ∈ C, projLift hQ x c = c := by
  classical
  have := finite_linearEquiv_pi (K := K) (d := d)
  have hNN : ∀ v, sNil s.val (sNil s.val v) = 0 := sNil_sNil (congrArg Subtype.val hss)
  have hadj := polar_sNil_left s hss
  have hUK : U ≤ LinearMap.ker (sNil s.val) := hUW.trans (range_le_ker _ hNN)
  let G₀ : Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K)) :=
    TauCeti.QuadraticMap.orthogonalGroup Q ⊓ nilCommutant (sNil s.val) ⊓ linPointFixer C ⊓
      linSetStabilizer U
  have hG₀O : G₀ ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    inf_le_left.trans (inf_le_left.trans inf_le_left)
  have hG₀N : G₀ ≤ nilCommutant (sNil s.val) := inf_le_left.trans (inf_le_left.trans inf_le_right)
  have hG₀C : G₀ ≤ linPointFixer C := inf_le_left.trans inf_le_right
  have hG₀U : G₀ ≤ linSetStabilizer U := inf_le_right
  let φ₀ : ↥G₀ →* Module.End K U := (stabRestrictHom U).comp (Subgroup.inclusion hG₀U)
  have hφ₀v : ∀ (g : ↥G₀) (u : U), (φ₀ g u : Fin d → K) = (g : (Fin d → K) ≃ₗ[K] _) u :=
    fun _ _ => rfl
  have hφ₀ : ∀ (g : ↥G₀) u u', βU (φ₀ g u) (φ₀ g u') = βU u u' := by
    intro g u u'
    obtain ⟨z, hz⟩ := hUW u'.2
    have hgz : sNil s.val ((g : (Fin d → K) ≃ₗ[K] _) z) = (φ₀ g u' : Fin d → K) := by
      rw [hφ₀v, ← hz]
      exact ((mem_nilCommutant _).mp (hG₀N g.2) z).symm
    rw [hβU _ _ _ hgz, hβU _ _ _ hz, hφ₀v]
    exact polar_apply_of_mem_orth (hG₀O g.2) u z
  have hlift : ∀ f : U →ₗ[K] U, (∀ u u', βU (f u) (f u') = βU u u') → ∃ g, φ₀ g = f := by
    intro f hf
    have hfinj : Function.Injective f := by
      refine (injective_iff_map_eq_zero f).mpr fun u hu => hβn.1 u fun w => ?_
      rw [← hf, hu, map_zero, LinearMap.zero_apply]
    obtain ⟨g, hgO, hgU, hgC⟩ :=
      exists_orth_splitLift (sNil s.val) hadj f hUK hCK hdisj hsup hB hUW hQU hfinj
    have hgN := commute_splitLift (sNil s.val) hadj f hsup hB hNN hUW hD βU hβU hf hgO hgU hgC
    have hgS : ∀ u ∈ U, g u ∈ U := fun u hu => by
      rw [show u = ((⟨u, hu⟩ : U) : Fin d → K) from rfl, hgU]
      exact (f _).2
    refine ⟨⟨g, ⟨⟨⟨hgO, (mem_nilCommutant _).mpr hgN⟩, hgC⟩, hgS⟩⟩, ?_⟩
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    exact hgU u
  obtain ⟨r, b, -, hb⟩ := CFSG.RankThree.PartOne.KCAlternating.exists_isSymplecticBasis hβ hβn
  let ρ₀ := sympChart hβ hb φ₀ hφ₀
  have hρ₀ : Function.Surjective ρ₀ := sympChart_surjective hβ hb φ₀ hφ₀ hlift
  let G₁ : Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K)) := ⁅G₀, G₀⁆
  have hG₁Ω : G₁ ≤ CFSG.RankThree.Classical2.orthDerived Q := Subgroup.commutator_mono hG₀O hG₀O
  have hG₁G₀ : G₁ ≤ G₀ := CFSG.Quasithin.A3.commutator_self_le G₀
  let ρ₁ : ↥G₁ →* StatedSp r K := ρ₀.comp (Subgroup.inclusion hG₁G₀)
  have hperf : Group.IsPerfect (StatedSp r K) :=
    CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp r K (Or.inl (exists_finset_card_four hq4))
  have hρ₁ : Function.Surjective ρ₁ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hperf.commutator_eq_top, commutator_def,
      Subgroup.commutator_le]
    intro A _ B _
    obtain ⟨gA, rfl⟩ := hρ₀ A
    obtain ⟨gB, rfl⟩ := hρ₀ B
    refine ⟨⟨⁅(gA : (Fin d → K) ≃ₗ[K] (Fin d → K)), (gB : (Fin d → K) ≃ₗ[K] (Fin d → K))⁆,
      Subgroup.commutator_mem_commutator gA.2 gB.2⟩, ?_⟩
    change ρ₀ (Subgroup.inclusion hG₁G₀ ⟨_, _⟩) = ⁅ρ₀ gA, ρ₀ gB⁆
    rw [← map_commutatorElement]
    rfl
  have hcore : (perfectCore (⊤ : Subgroup ↥G₁)).map ρ₁ = ⊤ := by
    rw [map_perfectCore, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hρ₁]
    exact perfectCore_eq_self_of_perfect (by rw [← commutator_def]; exact hperf.commutator_eq_top)
  let ψ₁ : ↥G₁ →* matrixProjectiveDerived Q := (projHom Q).comp (Subgroup.inclusion hG₁Ω)
  have hH : (perfectCore (⊤ : Subgroup ↥G₁)).map ψ₁ ≤
      perfectCore (autFixSubgroup (isometryConjugationHom Q s)) := by
    refine le_perfectCore_of_perfect ?_ ?_
    · rintro _ ⟨y, -, rfl⟩
      exact kappa_projHom_eq_of_commute hQ s _ fun x => (hG₀N (hG₁G₀ y.2)) x
    · rw [← Subgroup.map_commutator, perfectCore_perfect]
  obtain ⟨gh, hgh⟩ := hlift h hh
  have hA : ρ₀ gh ∈ (perfectCore (⊤ : Subgroup ↥G₁)).map ρ₁ := by
    rw [hcore]
    exact Subgroup.mem_top _
  obtain ⟨y, hy, hyA⟩ := hA
  have hl : projLift hQ (ψ₁ y) = ((y : ↥G₁) : (Fin d → K) ≃ₗ[K] (Fin d → K)) :=
    projLift_projHom hQ _
  have e2 : φ₀ (Subgroup.inclusion hG₁G₀ y) = h := by
    apply (LinearMap.toMatrix b b).injective
    have h1 := congrArg (fun A : StatedSp r K =>
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) hyA
    change LinearMap.toMatrix b b (φ₀ (Subgroup.inclusion hG₁G₀ y)) =
      LinearMap.toMatrix b b (φ₀ gh) at h1
    rw [h1, hgh]
  refine ⟨ψ₁ y, hH ⟨y, hy, rfl⟩, fun u => ?_, fun c hc => ?_⟩
  · rw [hl]
    have e3 := congrArg (fun f : Module.End K U => (f u : Fin d → K)) e2
    exact e3
  · rw [hl]
    exact (hG₀C (hG₁G₀ y.2)) c hc

theorem exists_core_torus (hQ : ∃ v, Q v ≠ 0)
    (hB : (QuadraticMap.polarBilin Q).Nondegenerate) (hq4 : 4 ≤ Nat.card K)
    (s : matrixIsometries Q) (hss : s * s = 1) {U C : Submodule K (Fin d → K)}
    (hUW : U ≤ LinearMap.range (sNil s.val)) (hQU : ∀ u ∈ U, Q u = 0)
    (hCK : C ≤ LinearMap.ker (sNil s.val)) (hdisj : U ⊓ C = ⊥)
    (hsup : U ⊔ C = LinearMap.ker (sNil s.val))
    (hD : ∀ u ∈ U, ∀ z, sNil s.val z ∈ C → QuadraticMap.polar Q (u : Fin d → K) z = 0)
    (βU : LinearMap.BilinForm K U)
    (hβU : ∀ (u u' : U) (z : Fin d → K), sNil s.val z = u' →
      βU u u' = QuadraticMap.polar Q u z)
    (hβ : βU.IsAlt) (hβn : βU.Nondegenerate) {u : Fin d → K} (hu : u ∈ U) (hu0 : u ≠ 0)
    (a : Kˣ) :
    ∃ x ∈ perfectCore (autFixSubgroup (isometryConjugationHom Q s)),
      projLift hQ x u = (a : K) • u ∧ ∀ c ∈ C, projLift hQ x c = c := by
  obtain ⟨w, hw⟩ : ∃ w, βU ⟨u, hu⟩ w ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hu0 (congrArg Subtype.val (hβn.1 ⟨u, hu⟩ hall))
  have huw : βU ⟨u, hu⟩ ((βU ⟨u, hu⟩ w)⁻¹ • w) = 1 := by
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hw]
  obtain ⟨r, c, -, hc, hc0, -⟩ :=
    CFSG.RankThree.PartOne.KCAlternating.exists_isSymplecticBasis_of_apply_eq_one hβ hβn huw
  let A : StatedSp (r + 1) K := ⟨torusSpGL 0 a, torusSpGL_mem 0 a⟩
  have hf : ∀ u₁ u₂, βU (Matrix.toLin c c ((A : GL (Fin (r + 1) ⊕ Fin (r + 1)) K) :
      Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) K) u₁)
      (Matrix.toLin c c ((A : GL (Fin (r + 1) ⊕ Fin (r + 1)) K) :
        Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) K) u₂) = βU u₁ u₂ :=
    toLin_isometry_of_mem hβ hc (statedSp_transpose_mul_J_mul A)
  obtain ⟨x, hx, hxU, hxC⟩ :=
    exists_core_restrict_eq hQ hB hq4 s hss hUW hQU hCK hdisj hsup hD βU hβU hβ hβn _ hf
  refine ⟨x, hx, ?_, hxC⟩
  have e := hxU ⟨u, hu⟩
  have e2 := toLin_torusSpGL c 0 a (.inl 0)
  rw [hc0] at e2
  change projLift hQ x u = _ at e
  rw [e]
  change ((Matrix.toLin c c ((torusSpGL 0 a : GL (Fin (r + 1) ⊕ Fin (r + 1)) K) :
    Matrix _ _ K) ⟨u, hu⟩ : U) : Fin d → K) = _
  rw [e2]
  simp [torusSpEntry]

end Core

end CFSG.SeitzReduction.OmegaPilot
