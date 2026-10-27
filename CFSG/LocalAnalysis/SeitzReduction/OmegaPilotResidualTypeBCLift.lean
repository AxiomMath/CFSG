module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviPerp

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Module LinearMap

section Commute

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

theorem polar_apply_of_mem_orth {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (x y : V) :
    QuadraticMap.polar Q (g x) (g y) = QuadraticMap.polar Q x y := by
  have h := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg
  simp only [QuadraticMap.polar, ← map_add, h]

theorem commute_of_fix_range (hB : (QuadraticMap.polarBilin Q).Nondegenerate) (N : V →ₗ[K] V)
    (hadj : ∀ x y, QuadraticMap.polarBilin Q (N x) y = QuadraticMap.polarBilin Q x (N y))
    {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hfix : ∀ w ∈ LinearMap.range N, g w = w) (x : V) : g (N x) = N (g x) := by
  rw [hfix _ (LinearMap.mem_range_self N x)]
  symm
  rw [← sub_eq_zero]
  refine hB.2 _ fun a => ?_
  rw [map_sub, ← hadj, ← hadj, QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polarBilin_apply_apply, ← hfix _ (LinearMap.mem_range_self N a),
    polar_apply_of_mem_orth hg, hfix _ (LinearMap.mem_range_self N a), sub_self]

end Commute

section Sqrt

variable {K : Type*} [Field K] [CharP K 2] [PerfectRing K 2]

noncomputable abbrev sqrtTwo (K : Type*) [Field K] [CharP K 2] [PerfectRing K 2] : K ≃+* K :=
  (frobeniusEquiv K 2).symm

theorem sqrtTwo_mul_self (a : K) : sqrtTwo K a * sqrtTwo K a = a := by
  rw [← pow_two]
  exact frobeniusEquiv_symm_pow_p K 2 a

theorem sqrtTwo_mul_self_mul (c a : K) : sqrtTwo K (c * c * a) = c * sqrtTwo K a := by
  rw [map_mul, ← pow_two, frobeniusEquiv_symm_pow]

end Sqrt

section Isotropy

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (N : V →ₗ[K] V)
  (hadj : ∀ x y, QuadraticMap.polarBilin Q (N x) y = QuadraticMap.polarBilin Q x (N y))

include hadj in
theorem polar_range_ker (a : V) {z : V} (hz : z ∈ LinearMap.ker N) :
    QuadraticMap.polar Q (N a) z = 0 := by
  rw [← QuadraticMap.polarBilin_apply_apply, hadj, LinearMap.mem_ker.mp hz, map_zero]

include hadj in
theorem polar_mem_range_ker {w z : V} (hw : w ∈ LinearMap.range N) (hz : z ∈ LinearMap.ker N) :
    QuadraticMap.polar Q w z = 0 := by
  obtain ⟨a, rfl⟩ := hw
  exact polar_range_ker N hadj a hz

theorem range_le_ker (hNN : ∀ v, N (N v) = 0) : LinearMap.range N ≤ LinearMap.ker N := by
  rintro _ ⟨a, rfl⟩
  exact hNN a

end Isotropy

section Lift

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  (N : (Fin d → K) →ₗ[K] (Fin d → K))

omit [Field K] in
theorem quad_add_eq {K : Type} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (x y : V) : Q (x + y) = Q x + Q y + QuadraticMap.polar Q x y := by
  rw [QuadraticMap.polar]
  abel

variable {U : Submodule K (LinearMap.ker N)} (hU : IsCompl (rangeInKer N) U)

@[expose] noncomputable def kerQuotRep :
    (LinearMap.ker N ⧸ rangeInKer N) →ₗ[K] (Fin d → K) :=
  (LinearMap.ker N).subtype ∘ₗ U.subtype ∘ₗ
    (Submodule.quotientEquivOfIsCompl (rangeInKer N) U hU).toLinearMap

theorem kerQuotRep_mem_ker (p : LinearMap.ker N ⧸ rangeInKer N) :
    kerQuotRep N hU p ∈ LinearMap.ker N :=
  ((Submodule.quotientEquivOfIsCompl (rangeInKer N) U hU p : U) : LinearMap.ker N).2

theorem mk_kerQuotRep (p : LinearMap.ker N ⧸ rangeInKer N) :
    (Submodule.Quotient.mk (⟨kerQuotRep N hU p, kerQuotRep_mem_ker N hU p⟩ : LinearMap.ker N) :
      LinearMap.ker N ⧸ rangeInKer N) = p :=
  Submodule.mk_quotientEquivOfIsCompl_apply hU p

theorem mem_rangeInKer_iff (z : LinearMap.ker N) :
    z ∈ rangeInKer N ↔ (z : Fin d → K) ∈ LinearMap.range N := Iff.rfl

theorem sub_kerQuotRep_mem_range (z : LinearMap.ker N) :
    (z : Fin d → K) - kerQuotRep N hU (Submodule.Quotient.mk z) ∈ LinearMap.range N := by
  have h := mk_kerQuotRep N hU (Submodule.Quotient.mk z)
  have h' := (Submodule.Quotient.eq (rangeInKer N)).mp h.symm
  exact h'

variable (hadj : ∀ x y, QuadraticMap.polarBilin Q (N x) y = QuadraticMap.polarBilin Q x (N y))

theorem polar_kerQuotRep (p q : LinearMap.ker N ⧸ rangeInKer N) :
    QuadraticMap.polar Q (kerQuotRep N hU p) (kerQuotRep N hU q) = kerQuotForm N hadj p q := by
  conv_rhs => rw [← mk_kerQuotRep N hU p, ← mk_kerQuotRep N hU q]
  rw [kerQuotForm_mk]

variable (h : (LinearMap.ker N ⧸ rangeInKer N) →ₗ[K] (LinearMap.ker N ⧸ rangeInKer N))

@[expose] noncomputable def kerQuotDelta (p : LinearMap.ker N ⧸ rangeInKer N) : K :=
  Q (kerQuotRep N hU p) + Q (kerQuotRep N hU (h p))

variable [CharP K 2]

include hadj in
theorem kerQuotDelta_add (hh : ∀ p q, kerQuotForm N hadj (h p) (h q) = kerQuotForm N hadj p q)
    (p q : LinearMap.ker N ⧸ rangeInKer N) :
    kerQuotDelta (Q := Q) N hU h (p + q) =
      kerQuotDelta (Q := Q) N hU h p + kerQuotDelta (Q := Q) N hU h q := by
  simp only [kerQuotDelta, map_add, quad_add_eq, polar_kerQuotRep N hU hadj, hh]
  have h0 : kerQuotForm N hadj p q + kerQuotForm N hadj p q = 0 := CharTwo.add_self_eq_zero _
  linear_combination h0

omit [CharP K 2] in
theorem kerQuotDelta_smul (c : K) (p : LinearMap.ker N ⧸ rangeInKer N) :
    kerQuotDelta (Q := Q) N hU h (c • p) = c * c * kerQuotDelta (Q := Q) N hU h p := by
  simp only [kerQuotDelta, map_smul, QuadraticMap.map_smul, smul_eq_mul]
  ring

variable [PerfectRing K 2]

@[expose] noncomputable def sqrtDelta
    (hh : ∀ p q, kerQuotForm N hadj (h p) (h q) = kerQuotForm N hadj p q) :
    (LinearMap.ker N ⧸ rangeInKer N) →ₗ[K] K where
  toFun p := sqrtTwo K (kerQuotDelta (Q := Q) N hU h p)
  map_add' p q := by rw [kerQuotDelta_add N hU hadj h hh, map_add]
  map_smul' c p := by
    rw [kerQuotDelta_smul, sqrtTwo_mul_self_mul, RingHom.id_apply, smul_eq_mul]

variable (hh : ∀ p q, kerQuotForm N hadj (h p) (h q) = kerQuotForm N hadj p q)

theorem sqrtDelta_mul_self (p : LinearMap.ker N ⧸ rangeInKer N) :
    sqrtDelta N hU hadj h hh p * sqrtDelta N hU hadj h hh p = kerQuotDelta (Q := Q) N hU h p :=
  sqrtTwo_mul_self _

@[expose] noncomputable def kerQuotLiftMap (w₁ : Fin d → K) :
    LinearMap.ker N →ₗ[K] (Fin d → K) :=
  (LinearMap.ker N).subtype - kerQuotRep N hU ∘ₗ (rangeInKer N).mkQ +
    kerQuotRep N hU ∘ₗ h ∘ₗ (rangeInKer N).mkQ +
      (sqrtDelta N hU hadj h hh ∘ₗ (rangeInKer N).mkQ).smulRight w₁

theorem kerQuotLiftMap_apply (w₁ : Fin d → K) (z : LinearMap.ker N) :
    kerQuotLiftMap N hU hadj h hh w₁ z =
      (z : Fin d → K) - kerQuotRep N hU (Submodule.Quotient.mk z) +
        kerQuotRep N hU (h (Submodule.Quotient.mk z)) +
          sqrtDelta N hU hadj h hh (Submodule.Quotient.mk z) • w₁ :=
  rfl

theorem kerQuotLiftMap_of_mk_eq_zero (w₁ : Fin d → K) {z : LinearMap.ker N}
    (hz : (Submodule.Quotient.mk z : LinearMap.ker N ⧸ rangeInKer N) = 0) :
    kerQuotLiftMap N hU hadj h hh w₁ z = z := by
  rw [kerQuotLiftMap_apply, hz, map_zero, map_zero, map_zero, map_zero, zero_smul, sub_zero,
    add_zero, add_zero]

variable (hNN : ∀ v, N (N v) = 0) {w₁ : Fin d → K} (hw₁ : w₁ ∈ LinearMap.range N)

include hNN hw₁ in
theorem kerQuotLiftMap_mem_ker (z : LinearMap.ker N) :
    kerQuotLiftMap N hU hadj h hh w₁ z ∈ LinearMap.ker N := by
  rw [kerQuotLiftMap_apply]
  refine add_mem (add_mem (sub_mem z.2 (kerQuotRep_mem_ker N hU _)) (kerQuotRep_mem_ker N hU _))
    (Submodule.smul_mem _ _ (range_le_ker N hNN hw₁))

include hw₁ in
theorem mk_kerQuotLiftMap (z : LinearMap.ker N) :
    (Submodule.Quotient.mk (⟨kerQuotLiftMap N hU hadj h hh w₁ z,
        kerQuotLiftMap_mem_ker N hU hadj h hh hNN hw₁ z⟩ : LinearMap.ker N) :
      LinearMap.ker N ⧸ rangeInKer N) = h (Submodule.Quotient.mk z) := by
  conv_rhs => rw [← mk_kerQuotRep N hU (h (Submodule.Quotient.mk z))]
  rw [Submodule.Quotient.eq, mem_rangeInKer_iff]
  have e : (((⟨kerQuotLiftMap N hU hadj h hh w₁ z, kerQuotLiftMap_mem_ker N hU hadj h hh hNN hw₁ z⟩ :
      LinearMap.ker N) - ⟨kerQuotRep N hU (h (Submodule.Quotient.mk z)),
        kerQuotRep_mem_ker N hU _⟩ : LinearMap.ker N) : Fin d → K) =
      ((z : Fin d → K) - kerQuotRep N hU (Submodule.Quotient.mk z)) +
        sqrtDelta N hU hadj h hh (Submodule.Quotient.mk z) • w₁ := by
    rw [Submodule.coe_sub]
    change kerQuotLiftMap N hU hadj h hh w₁ z - kerQuotRep N hU (h (Submodule.Quotient.mk z)) = _
    rw [kerQuotLiftMap_apply]
    abel
  rw [e]
  exact add_mem (sub_kerQuotRep_mem_range N hU z) (Submodule.smul_mem _ _ hw₁)

include hNN hw₁ in
theorem quad_kerQuotLiftMap (hQw₁ : Q w₁ = 1) (z : LinearMap.ker N) :
    Q (kerQuotLiftMap N hU hadj h hh w₁ z) = Q z := by
  set a := (z : Fin d → K) - kerQuotRep N hU (Submodule.Quotient.mk z) with ha
  set r := kerQuotRep N hU (Submodule.Quotient.mk z) with hr
  set c := kerQuotRep N hU (h (Submodule.Quotient.mk z)) with hc
  set t := sqrtDelta N hU hadj h hh (Submodule.Quotient.mk z) with ht
  have haW : a ∈ LinearMap.range N := sub_kerQuotRep_mem_range N hU z
  have hrK : r ∈ LinearMap.ker N := kerQuotRep_mem_ker N hU _
  have hcK : c ∈ LinearMap.ker N := kerQuotRep_mem_ker N hU _
  have hw₁K : w₁ ∈ LinearMap.ker N := range_le_ker N hNN hw₁
  have e1 : kerQuotLiftMap N hU hadj h hh w₁ z = a + c + t • w₁ := by
    rw [kerQuotLiftMap_apply]
  have e2 : (z : Fin d → K) = a + r := by rw [ha, hr, sub_add_cancel]
  have hac : QuadraticMap.polar Q a c = 0 := polar_mem_range_ker N hadj haW hcK
  have har : QuadraticMap.polar Q a r = 0 := polar_mem_range_ker N hadj haW hrK
  have haw : QuadraticMap.polar Q a w₁ = 0 := polar_mem_range_ker N hadj haW hw₁K
  have hcw : QuadraticMap.polar Q c w₁ = 0 := by
    rw [QuadraticMap.polar_comm]
    exact polar_mem_range_ker N hadj hw₁ hcK
  have htt : t * t = Q r + Q c := sqrtDelta_mul_self N hU hadj h hh _
  rw [e1, e2, quad_add_eq, quad_add_eq, quad_add_eq, QuadraticMap.map_smul, hQw₁,
    QuadraticMap.polar_add_left, QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right,
    hac, har, haw, hcw, smul_eq_mul, smul_eq_mul, mul_zero, htt]
  have h0 : Q c + Q c = 0 := CharTwo.add_self_eq_zero _
  linear_combination h0

include hNN hw₁ in
theorem kerQuotLiftMap_injective (hB : (QuadraticMap.polarBilin Q).Nondegenerate) :
    Function.Injective (kerQuotLiftMap N hU hadj h hh w₁) := by
  have hBn := kerQuotForm_nondegenerate N hadj hB
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  have hmk := mk_kerQuotLiftMap N hU hadj h hh hNN hw₁ z
  have h0 : (⟨kerQuotLiftMap N hU hadj h hh w₁ z, kerQuotLiftMap_mem_ker N hU hadj h hh hNN hw₁ z⟩ :
      LinearMap.ker N) = 0 := Subtype.ext hz
  rw [h0, Submodule.Quotient.mk_zero] at hmk
  have hz0 : (Submodule.Quotient.mk z : LinearMap.ker N ⧸ rangeInKer N) = 0 := by
    refine hBn.1 _ fun q => ?_
    rw [← hh, ← hmk, map_zero, LinearMap.zero_apply]
  have := kerQuotLiftMap_of_mk_eq_zero N hU hadj h hh w₁ hz0
  rw [hz] at this
  exact Subtype.ext this.symm

end Lift

section Witt

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  (N : (Fin d → K) →ₗ[K] (Fin d → K))

theorem exists_orth_lift_kerQuot (hB : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hNN : ∀ v, N (N v) = 0)
    (hadj : ∀ x y, QuadraticMap.polarBilin Q (N x) y = QuadraticMap.polarBilin Q x (N y))
    {w₁ : Fin d → K} (hw₁ : w₁ ∈ LinearMap.range N) (hQw₁ : Q w₁ = 1)
    (h : (LinearMap.ker N ⧸ rangeInKer N) →ₗ[K] (LinearMap.ker N ⧸ rangeInKer N))
    (hh : ∀ p q, kerQuotForm N hadj (h p) (h q) = kerQuotForm N hadj p q) :
    ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, (∀ w ∈ LinearMap.range N, g w = w) ∧
      ∃ hg : ∀ x, (g : (Fin d → K) →ₗ[K] (Fin d → K)) (N x) =
          N ((g : (Fin d → K) →ₗ[K] (Fin d → K)) x),
        kerQuotMap N (g : (Fin d → K) →ₗ[K] (Fin d → K)) hg = h := by
  obtain ⟨U, hU⟩ := (rangeInKer N).exists_isCompl
  have hφinj := kerQuotLiftMap_injective N hU hadj h hh hNN hw₁ hB
  have hquad := quad_kerQuotLiftMap N hU hadj h hh hNN hw₁ hQw₁
  have hmem := kerQuotLiftMap_mem_ker N hU hadj h hh hNN hw₁
  have hmk : ∀ z hz, (Submodule.Quotient.mk (⟨kerQuotLiftMap N hU hadj h hh w₁ z, hz⟩ :
      LinearMap.ker N) : LinearMap.ker N ⧸ rangeInKer N) = h (Submodule.Quotient.mk z) :=
    fun z _ => mk_kerQuotLiftMap N hU hadj h hh hNN hw₁ z
  have hfixφ : ∀ z : LinearMap.ker N, (Submodule.Quotient.mk z : LinearMap.ker N ⧸ rangeInKer N) = 0 →
      kerQuotLiftMap N hU hadj h hh w₁ z = z :=
    fun z hz => kerQuotLiftMap_of_mk_eq_zero N hU hadj h hh w₁ hz
  generalize kerQuotLiftMap N hU hadj h hh w₁ = φ at hφinj hquad hmem hmk hfixφ
  let b := Module.finBasis K (LinearMap.ker N)
  have l1 : LinearIndependent K ((LinearMap.ker N).subtype ∘ b) :=
    b.linearIndependent.map' (LinearMap.ker N).subtype (Submodule.ker_subtype _)
  have l2 : LinearIndependent K (φ ∘ b) :=
    b.linearIndependent.map' φ (LinearMap.ker_eq_bot.mpr hφinj)
  obtain ⟨g, hgO, hg⟩ :=
    CFSG.RankThree.OrthogonalInvolutions.exists_mem_orthogonalGroup_apply_eq hB
      ((LinearMap.ker N).subtype ∘ b) (φ ∘ b) l1 l2
      (fun i => hquad (b i))
      (fun i j => by
        simp only [Function.comp_apply]
        rw [QuadraticMap.polar, QuadraticMap.polar, ← map_add φ, hquad, hquad, hquad,
          Submodule.coe_add]
        rfl)
  have hgφ : ∀ z : LinearMap.ker N, g z = φ z := by
    have hext : (g : (Fin d → K) →ₗ[K] (Fin d → K)) ∘ₗ (LinearMap.ker N).subtype = φ :=
      b.ext fun i => hg i
    intro z
    exact LinearMap.congr_fun hext z
  have hfix : ∀ w ∈ LinearMap.range N, g w = w := by
    intro w hw
    have h2 : (Submodule.Quotient.mk (⟨w, range_le_ker N hNN hw⟩ : LinearMap.ker N) :
        LinearMap.ker N ⧸ rangeInKer N) = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hw
    exact (hgφ ⟨w, range_le_ker N hNN hw⟩).trans (hfixφ _ h2)
  have hcomm := commute_of_fix_range hB N hadj hgO hfix
  refine ⟨g, hgO, hfix, hcomm, ?_⟩
  apply Submodule.linearMap_qext
  apply LinearMap.ext
  intro z
  change kerQuotMap N (g : (Fin d → K) →ₗ[K] (Fin d → K)) hcomm (Submodule.Quotient.mk z) =
    h (Submodule.Quotient.mk z)
  rw [kerQuotMap_mk', ← hmk z (hmem z)]
  congr 1
  exact Subtype.ext (hgφ z)

end Witt

end CFSG.SeitzReduction.OmegaPilot
