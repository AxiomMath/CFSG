module

public import CFSG.HardMathSupport.Solomon.Coordinator.I22_7Defs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs CFSG.LocalAnalysis.GLTheoremB
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped commutatorElement

section Orbit

variable {K : Type} [Group K]

@[expose] def i227cmp_perm (O : Set (Subgroup K)) (hO : ∀ k : K, ∀ L ∈ O, GLBConj k L ∈ O) :
    K →* Equiv.Perm O where
  toFun k :=
    { toFun := fun L => ⟨GLBConj k⁻¹ L.1, hO _ _ L.2⟩
      invFun := fun L => ⟨GLBConj k L.1, hO _ _ L.2⟩
      left_inv := fun L => Subtype.ext (gLBConj_gLBConj_inv k L.1)
      right_inv := fun L => Subtype.ext (gLBConj_inv_gLBConj k L.1) }
  map_one' := Equiv.ext fun L => Subtype.ext (by simp [gLBConj_one])
  map_mul' a b := Equiv.ext fun L => Subtype.ext (by
    show GLBConj (a * b)⁻¹ L.1 = GLBConj a⁻¹ (GLBConj b⁻¹ L.1)
    rw [gLBConj_gLBConj, mul_inv_rev])

theorem i227cmp_orbit_dichotomy [Finite K] (hperf : commutator K = ⊤) (J : Subgroup K) :
    5 ≤ Nat.card (Set.range fun k : K => GLBConj k J) ∨ ∀ k : K, GLBConj k J = J := by
  by_contra hcon
  obtain ⟨h1, h2⟩ := not_or.1 hcon
  set O : Set (Subgroup K) := Set.range fun k : K => GLBConj k J with hO
  have hOc : ∀ k : K, ∀ L ∈ O, GLBConj k L ∈ O := by
    rintro k _ ⟨k', rfl⟩
    exact ⟨k' * k, by simp only [gLBConj_gLBConj]⟩
  have hJO : J ∈ O := ⟨1, gLBConj_one J⟩
  have hsol : Group.IsSolvable (Equiv.Perm O) := Equiv.Perm.isSolvable (by omega)
  have : Group.IsPerfect K := ⟨hperf⟩
  have h3 := CFSG.ComponentClassification.SolvableKernelContainment.hom_eq_one
    (i227cmp_perm O hOc)
  apply h2
  intro k
  have h4 := congrArg (fun f : Equiv.Perm O => ((f ⟨J, hJO⟩ : O) : Subgroup K))
    (DFunLike.congr_fun h3 k⁻¹)
  simpa [i227cmp_perm] using h4

end Orbit

section Cover

variable {K : Type} [Group K] [Finite K]

theorem i227cmp_isQuasisimple_of_simple {X : Type*} [Group X] (hs : IsSimpleGroup X)
    (hnc : ∃ a b : X, a * b ≠ b * a) : CFSG.Open.IsQuasisimple X := by
  have hZ : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a)
  refine ⟨?_, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      have : ⁅a, b⁆ = 1 := by
        rw [← Subgroup.mem_bot, ← h]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      exact hab (commutatorElement_eq_one_iff_mul_comm.mp this)
    · exact h
  · exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).isSimpleGroup

theorem i227cmp_cover_eq_top (hK : FiCoverK K) (hS : IsSimpleGroup (K ⧸ GLAPPrimeCore 5 K))
    (hnc : ∃ a b : K ⧸ GLAPPrimeCore 5 K, a * b ≠ b * a) (C : Subgroup K) [C.Normal]
    (hC : C ⊔ GLAPPrimeCore 5 K = ⊤) : C = ⊤ := by
  set T : Subgroup K := ⊤ with hT
  let e : ↥T ≃* K := Subgroup.topEquiv
  have hR : (GLAPPrimeCore 5 ↥T).map e.toMonoidHom = GLAPPrimeCore 5 K :=
    glaPPrimeCore_map_iso 5 e
  let q : (↥T ⧸ GLAPPrimeCore 5 ↥T) ≃* (K ⧸ GLAPPrimeCore 5 K) :=
    QuotientGroup.congr _ _ e hR
  have hq : CFSG.Open.IsQuasisimple (barOf 5 T) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv q.symm
      (i227cmp_isQuasisimple_of_simple hS hnc)
  obtain ⟨K0, hK0, hlay, -⟩ := exists_layer_eq_component Nat.prime_five hq
  have hK0top : K0 = ⊤ := by rw [← hlay]; exact hK.layer
  subst hK0top
  by_contra hne
  have hlt : C < ⊤ := lt_top_iff_ne_top.2 hne
  refine hK0.2.2.2 C hlt (isSubnormal_of_normal inferInstance) ?_
  rw [Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _),
    eq_top_iff]
  rintro z -
  obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective _ z
  have ht : (t : K) ∈ C ⊔ GLAPPrimeCore 5 K := by rw [hC]; exact Subgroup.mem_top _
  obtain ⟨c, hc, r, hr, hcr⟩ := Subgroup.mem_sup_of_normal_left.1 ht
  have hr' : (⟨r, Subgroup.mem_top r⟩ : ↥T) ∈ GLAPPrimeCore 5 ↥T := by
    rw [← hR] at hr
    obtain ⟨r0, hr0, hr0e⟩ := hr
    have : r0 = ⟨r, Subgroup.mem_top r⟩ := Subtype.ext hr0e
    rwa [this] at hr0
  refine ⟨⟨c, Subgroup.mem_top c⟩, Subgroup.mem_subgroupOf.2 hc, ?_⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  have : (⟨c, Subgroup.mem_top c⟩ : ↥T)⁻¹ * t = ⟨r, Subgroup.mem_top r⟩ := by
    apply Subtype.ext
    simp [← hcr]
  rw [this]
  exact hr'

omit [Finite K] in
theorem i227cmp_not_normal (hperf : commutator K = ⊤) {R J : Subgroup K} (hJR : J ≤ R)
    [J.Normal] (hq : CFSG.Open.IsQuasisimple ↥J) (hOut : Group.IsSolvable (Outer ↥J))
    (hcov : ∀ C : Subgroup K, C.Normal → C ⊔ R = ⊤ → C = ⊤) : False := by
  have : Group.IsPerfect K := ⟨hperf⟩
  have := hOut
  have hin : ∀ k : K, ∃ j : J, (MulAut.conjNormal (H := J) k) = MulAut.conj j := fun k =>
    CFSG.ComponentClassification.OuterAutomorphisms.perfect_action_inner
      (MulAut.conjNormal (H := J)) k
  set C : Subgroup K := Subgroup.centralizer (J : Set K) with hC
  have hCsup : C ⊔ J = ⊤ := by
    refine eq_top_iff.2 fun k _ => ?_
    obtain ⟨j, hj⟩ := hin k
    have hkj : k * (j : K)⁻¹ ∈ C := by
      rw [hC, Subgroup.mem_centralizer_iff]
      intro a ha
      have hb : (j : K)⁻¹ * a * j ∈ J := J.mul_mem (J.mul_mem (J.inv_mem j.2) ha) j.2
      have h1 := congrArg (fun f : MulAut ↥J => ((f ⟨(j : K)⁻¹ * a * j, hb⟩ : J) : K)) hj
      simp only [MulAut.conjNormal_apply, MulAut.conj_apply] at h1
      have h2 : k * ((j : K)⁻¹ * a * j) * k⁻¹ = a := by
        rw [h1]
        show (j : K) * ((j : K)⁻¹ * a * j) * (j : K)⁻¹ = a
        group
      calc a * (k * (j : K)⁻¹) = (k * ((j : K)⁻¹ * a * j) * k⁻¹) * (k * (j : K)⁻¹) := by rw [h2]
        _ = k * (j : K)⁻¹ * a := by group
    have : k = (k * (j : K)⁻¹) * j := by group
    rw [this]
    exact Subgroup.mul_mem_sup hkj j.2
  have hCR : C ⊔ R = ⊤ := eq_top_iff.2 (hCsup ▸ sup_le_sup_left hJR C)
  have hCtop : C = ⊤ := hcov C inferInstance hCR
  have hcomm : ∀ a b : ↥J, a * b = b * a := by
    intro a b
    have hb : (b : K) ∈ C := by rw [hCtop]; exact Subgroup.mem_top _
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 hb) a a.2)
  have hbot : commutator ↥J = ⊥ := by
    rw [commutator_def, eq_bot_iff]
    refine Subgroup.commutator_le.2 fun a _ b _ => ?_
    simp [commutatorElement_def, hcomm a b]
  have hnt : Nontrivial ↥J := CFSG.ComponentClassification.Quasisimple.nontrivial hq
  obtain ⟨a, ha⟩ := exists_ne (1 : ↥J)
  have : a ∈ commutator ↥J := by rw [hq.1]; exact Subgroup.mem_top a
  rw [hbot, Subgroup.mem_bot] at this
  exact ha this

end Cover

end CFSG.HardMathSupport.Solomon.Coordinator
