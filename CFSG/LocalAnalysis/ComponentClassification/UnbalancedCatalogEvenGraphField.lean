module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenLinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityUnitary
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearGraphFieldDescent
public import CFSG.ClassicalGroups.Unitary.Simple

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)
open CFSG.LinearGroups (stdHermForm stdHermForm_apply stdHermForm_single)

namespace EvenCatalog

section Conj

variable {M : Type*} [Group M]

@[expose] def centralizerConjEquivMap (H : Subgroup M) (g t : M) :
    ↥(H ⊓ Subgroup.centralizer {g * t * g⁻¹}) ≃*
      ↥(H.map (MulAut.conj g⁻¹).toMonoidHom ⊓ Subgroup.centralizer {t}) where
  toFun x := ⟨g⁻¹ * x * g, Subgroup.mem_inf.mpr
    ⟨⟨x, (Subgroup.mem_inf.mp x.2).1, by simp⟩, by
      have hx := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp x.2).2
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * t * g⁻¹) * x) * g := by rw [hx]
        _ = t * (g⁻¹ * x * g) := by group⟩⟩
  invFun y := ⟨g * y * g⁻¹, Subgroup.mem_inf.mpr
    ⟨by
      obtain ⟨z, hz, hzy⟩ := (Subgroup.mem_inf.mp y.2).1
      have hz' : (y : M) = g⁻¹ * z * g := by
        rw [← hzy]
        simp
      rw [hz']
      simpa [mul_assoc] using hz, by
      have hy := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp y.2).2
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g * y * g⁻¹ * (g * t * g⁻¹) = g * (y * t) * g⁻¹ := by group
        _ = g * (t * y) * g⁻¹ := by rw [hy]
        _ = g * t * g⁻¹ * (g * y * g⁻¹) := by group⟩⟩
  left_inv x := Subtype.ext (by simp only; group)
  right_inv y := Subtype.ext (by simp only; group)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem inner_le_map_conj {G : Type*} [Group G] {H : Subgroup (MulAut G)} (hH : inner G ≤ H)
    (g : MulAut G) : inner G ≤ H.map (MulAut.conj g⁻¹).toMonoidHom := by
  intro y hy
  refine ⟨g * y * g⁻¹, hH ((inner_normal G).conj_mem y hy g), ?_⟩
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

end Conj

theorem finite_mulAut (G : Type*) [Group G] [Finite G] : Finite (MulAut G) :=
  Finite.of_injective (fun e : MulAut G => (e : G → G)) fun _ _ hab => MulEquiv.ext (congrFun hab)

end EvenCatalog

open EvenCatalog

theorem even_linear_graph_field_involution_odd_core_exception {n f : ℕ} (hn : 3 ≤ n)
    (hf : 1 ≤ f) {K : Type} [Field K] (hK : Nat.card K = 2 ^ f)
    {H : Subgroup (MulAut (projectiveSL n K))} (hH : inner (projectiveSL n K) ≤ H)
    (A : GL (Fin n) K) {σ : K ≃+* K} (hσ : σ ≠ 1)
    (hα : orderOf (conjAut n K A * fieldAut n K σ * dualAut n K) = 2) :
    (¬(n = 3 ∧ Nat.card K = 4) →
      CFSG.oddCore ↥(H ⊓ Subgroup.centralizer
        {conjAut n K A * fieldAut n K σ * dualAut n K}) = ⊥) ∧
    (CFSG.oddCore ↥(H ⊓ Subgroup.centralizer
        {conjAut n K A * fieldAut n K σ * dualAut n K}) ≠ ⊥ → n = 3 ∧ Nat.card K = 4) := by
  have hmain : ¬(n = 3 ∧ Nat.card K = 4) →
      CFSG.oddCore ↥(H ⊓ Subgroup.centralizer
        {conjAut n K A * fieldAut n K σ * dualAut n K}) = ⊥ := by
    intro hq
    have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
    have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := finite_mulAut (projectiveSL n K)
    have hα2 : (conjAut n K A * fieldAut n K σ * dualAut n K) ^ 2 = 1 := by
      rw [← hα]
      exact pow_orderOf_eq_one _
    obtain ⟨hfe, hσx, B, hαB⟩ :=
      UnitaryHigher.linear_graph_field_involution_descent Nat.prime_two hf hK hn A σ hσ hα2
    obtain ⟨m, hm⟩ := hfe
    have he : 1 ≤ f / 2 := by omega
    have hKe : Nat.card K = 2 ^ (2 * (f / 2)) := by rw [hK]; congr 1; omega
    have h : UnitaryFieldData 2 (f / 2) K := ⟨Nat.prime_two, he, hKe⟩
    have hσbar : ∀ x, σ x = h.bar x := fun x => by rw [hσx, h.bar_apply]
    obtain ⟨hker, ⟨ι, -⟩, hNinn, -, hNC, hNnormal, hcentN⟩ :=
      linear_graph_field_full_centralizer_rigidity h hn σ hσbar
    set β := fieldAut n K σ * dualAut n K with hβ
    set N := (unitarySU 2 (f / 2) K n).map (conjAut n K) with hN
    set g := conjAut n K B with hg
    rw [hαB]
    refine oddCore_eq_bot_of_mulEquiv (centralizerConjEquivMap H g β).symm ?_
    set H' := H.map (MulAut.conj g⁻¹).toMonoidHom with hH'
    have hinnH' : inner (projectiveSL n K) ≤ H' := inner_le_map_conj hH g
    have hβ2 : β ^ 2 = 1 := by
      have h1 : β = g⁻¹ * (conjAut n K A * fieldAut n K σ * dualAut n K) * g := by
        rw [hαB]
        group
      rw [h1, sq, show g⁻¹ * (conjAut n K A * fieldAut n K σ * dualAut n K) * g *
          (g⁻¹ * (conjAut n K A * fieldAut n K σ * dualAut n K) * g) =
          g⁻¹ * ((conjAut n K A * fieldAut n K σ * dualAut n K) *
            (conjAut n K A * fieldAut n K σ * dualAut n K)) * g by group, ← sq, hα2, mul_one,
        inv_mul_cancel]
    have hNodd : CFSG.oddCore N = ⊥ := by
      have hnq : (n, 2 ^ (f / 2)) ≠ (3, 2) := by
        intro h32
        simp only [Prod.mk.injEq] at h32
        obtain ⟨h3, h2⟩ := h32
        have hf2 : f / 2 = 1 := by
          rcases Nat.lt_or_ge (f / 2) 2 with h' | h'
          · omega
          · have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h'
            omega
        exact hq ⟨h3, by rw [hKe, hf2]; norm_num⟩
      have hK2 : Nat.card K = (2 ^ (f / 2)) ^ 2 := by rw [hKe, ← pow_mul, mul_comm]
      have hsimpU := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 (f / 2)
        hK2 n hn hnq
      have : IsSimpleGroup N :=
        ((ι.symm.trans (unitaryPSUEquiv h (by omega : 1 ≤ n)))).isSimpleGroup
      have hn1 : 1 < n := by omega
      set i0 : Fin n := ⟨0, by omega⟩ with hi0
      set i1 : Fin n := ⟨1, hn1⟩ with hi1
      have hi01 : i0 ≠ i1 := by simp [hi0, hi1, Fin.ext_iff]
      obtain ⟨v, hv⟩ : ∃ v : Fin n → K, v = Pi.single i0 1 + Pi.single i1 1 := ⟨_, rfl⟩
      have hv0 : v i0 = 1 := by rw [hv]; simp [hi01.symm]
      have hvv : stdHermForm h n v v = 0 := by
        rw [hv, map_add (stdHermForm h n), LinearMap.add_apply, stdHermForm_single,
          stdHermForm_single]
        simp [hi01, hi01.symm, CharTwo.add_self_eq_zero]
      have htr : (1 : K) ∈ h.traceZero := by
        rw [h.mem_traceZero, UnitaryFieldData.trace, map_one, CharTwo.add_self_eq_zero]
      obtain ⟨t, ht⟩ := exists_mem_unitarySU_hermTransvection h hvv htr
      have htx : ∀ x, ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x =
          x + stdHermForm h n v x • v := fun x => by
        have h1 := LinearMap.congr_fun ht x
        rw [Matrix.mulVecLin_apply, CFSG.LinearGroups.hermTransvection_apply, one_mul] at h1
        exact h1
      set c : N := ⟨conjAut n K t, ⟨t, t.2, rfl⟩⟩ with hc
      have hc2 : c ^ 2 = 1 := by
        refine Subtype.ext ?_
        rw [Subgroup.coe_pow, hc, ← map_pow]
        have htt : (t : GL (Fin n) K) ^ 2 = 1 := by
          refine Units.ext (Matrix.toLin'.injective (LinearMap.ext fun x => ?_))
          rw [Units.val_pow_eq_pow_val, sq, Matrix.toLin'_apply, Matrix.toLin'_apply,
            ← mulVec_mulVec, htx, htx, map_add, map_smul, hvv, smul_eq_mul, mul_zero, add_zero,
            Units.val_one, one_mulVec, add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul,
            add_zero]
        rw [htt, map_one]
        rfl
      have hc1 : c ≠ 1 := by
        intro hc1
        have h1 : t ∈ ((conjAut n K).comp (unitarySU 2 (f / 2) K n).subtype).ker := by
          rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
          exact congrArg Subtype.val hc1
        rw [hker] at h1
        obtain ⟨u, -, -, hu⟩ := mem_unitaryScalars.mp h1
        have hu1 : (u : K) = 1 := by
          have h2 := congrFun (htx v) i0
          rw [hu, GeneralLinearGroup.coe_scalar, scalar_apply, mulVec_diagonal, hvv, zero_smul,
            add_zero, hv0, mul_one] at h2
          exact h2
        have hve0 : stdHermForm h n v (Pi.single i0 1) = 1 := by
          rw [← (CFSG.LinearGroups.stdHermForm_isSymm h n).eq, stdHermForm_single, hv0, map_one]
        have h3 := congrFun (htx (Pi.single i0 1)) i0
        rw [hu, GeneralLinearGroup.coe_scalar, scalar_apply, mulVec_diagonal, hu1, one_mul,
          Pi.add_apply, Pi.smul_apply, hve0, one_smul, hv0, Pi.single_eq_same,
          CharTwo.add_self_eq_zero] at h3
        exact one_ne_zero h3
      have heven : Even (Nat.card N) :=
        even_iff_two_dvd.mpr (orderOf_eq_prime hc2 hc1 ▸ orderOf_dvd_natCard c)
      exact oddCore_eq_bot_of_isSimpleGroup heven
    refine oddCore_eq_bot_of_normal_of_centralizer (R := N) ?_ ?_ hNodd ?_
    · intro r hr
      exact Subgroup.mem_inf.mpr ⟨hinnH' (hNinn hr), hNC hr⟩
    · intro x hx r hr
      have h1 := hNnormal.conj_mem ⟨r, hNC hr⟩ (Subgroup.mem_subgroupOf.mpr hr)
        ⟨x, (Subgroup.mem_inf.mp hx).2⟩
      exact Subgroup.mem_subgroupOf.mp h1
    · intro x hx hcomm
      have hxN : x ∈ Subgroup.centralizer (N : Set (MulAut (projectiveSL n K))) :=
        Subgroup.mem_centralizer_iff.mpr fun r hr => (hcomm r hr).symm
      rw [hcentN] at hxN
      obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxN
      refine ⟨1, ?_⟩
      rw [pow_one, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast,
        hβ2, _root_.one_zpow]
  exact ⟨hmain, fun hne => by
    by_contra hq
    exact hne (hmain hq)⟩

end CFSG.ComponentClassification.UnbalancedCatalog
