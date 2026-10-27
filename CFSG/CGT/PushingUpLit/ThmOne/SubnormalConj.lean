module

public import CFSG.GroupTheory.ConjugatePairSubnormality

public section

namespace CFSG.CGT.PushingUpLit.ThmOne

variable {G : Type} [Group G]

@[expose] def relConjCore (M K : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ K ∧ ∀ k ∈ K, k⁻¹ * g * k ∈ M}
  one_mem' := ⟨K.one_mem, fun k _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨haK, ha⟩ ⟨hbK, hb⟩
    refine ⟨K.mul_mem haK hbK, fun k hk => ?_⟩
    rw [show k⁻¹ * (a * b) * k = (k⁻¹ * a * k) * (k⁻¹ * b * k) by group]
    exact M.mul_mem (ha k hk) (hb k hk)
  inv_mem' := by
    rintro a ⟨haK, ha⟩
    refine ⟨K.inv_mem haK, fun k hk => ?_⟩
    rw [show k⁻¹ * a⁻¹ * k = (k⁻¹ * a * k)⁻¹ by group]
    exact M.inv_mem (ha k hk)

theorem relConjCore_le_left (M K : Subgroup G) : relConjCore M K ≤ M := fun g hg => by
  simpa using hg.2 1 K.one_mem

theorem relConjCore_le_right (M K : Subgroup G) : relConjCore M K ≤ K := fun _ hg => hg.1

theorem relConjCore_normal (M K : Subgroup G) : ((relConjCore M K).subgroupOf K).Normal := by
  refine ⟨fun g hg k => ?_⟩
  obtain ⟨hgK, hg⟩ := (Subgroup.mem_subgroupOf).mp hg
  refine (Subgroup.mem_subgroupOf).mpr ⟨K.mul_mem (K.mul_mem k.2 hgK) (K.inv_mem k.2),
    fun k' hk' => ?_⟩
  have e : k'⁻¹ * ((k : G) * g * (k : G)⁻¹) * k' =
      ((k : G)⁻¹ * k')⁻¹ * g * ((k : G)⁻¹ * k') := by group
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [e]
  exact hg _ (K.mul_mem (K.inv_mem k.2) hk')

theorem isSubnormal_of_conj_le {X M K : Subgroup G} (hsub : (X.subgroupOf M).IsSubnormal)
    (hXK : X ≤ K) (hconj : ∀ k ∈ K, ∀ x ∈ X, k⁻¹ * x * k ∈ M) :
    (X.subgroupOf K).IsSubnormal := by
  have hXI : X ≤ relConjCore M K := fun x hx => ⟨hXK hx, fun k hk => hconj k hk x hx⟩
  exact CFSG.GroupTheory.isSubnormal_subgroupOf_trans hXI (relConjCore_le_right M K)
    (CFSG.GroupTheory.isSubnormal_subgroupOf_of_le (relConjCore_le_left M K) hsub)
    (relConjCore_normal M K).isSubnormal

theorem conj_mem_of_threeThree {X R U Z V : Subgroup G} (hUZ : U ≤ Z) (hZV : Z ≤ V)
    (hVR : V ≤ R) (hZ : ∀ g ∈ Subgroup.normalizer (R : Set G), ∀ z ∈ Z, g * z * g⁻¹ ∈ Z)
    (hRX : ∀ r ∈ R, ∀ x ∈ X, r * x * r⁻¹ * x⁻¹ ∈ U)
    {g : G} (hg : g ∈ Subgroup.normalizer (R : Set G)) {x : G} (hx : x ∈ X) {v : G}
    (hv : v ∈ V) : (g⁻¹ * x * g) * v * (g⁻¹ * x * g)⁻¹ ∈ V := by
  have hw : g * v * g⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hg v).mp (hVR hv)
  have hu : (g * v * g⁻¹)⁻¹ * x * (g * v * g⁻¹) * x⁻¹ ∈ U := by
    simpa [mul_assoc] using hRX _ (R.inv_mem hw) x hx
  have hz : g⁻¹ * ((g * v * g⁻¹)⁻¹ * x * (g * v * g⁻¹) * x⁻¹) * g⁻¹⁻¹ ∈ Z :=
    hZ _ (Subgroup.inv_mem _ hg) _ (hUZ hu)
  rw [show (g⁻¹ * x * g) * v * (g⁻¹ * x * g)⁻¹ =
      v * (g⁻¹ * ((g * v * g⁻¹)⁻¹ * x * (g * v * g⁻¹) * x⁻¹) * g⁻¹⁻¹) by group]
  exact V.mul_mem hv (hZV hz)

theorem threeThree {X M R U Z V : Subgroup G} (hsub : (X.subgroupOf M).IsSubnormal)
    (hM : Subgroup.normalizer (V : Set G) = M) (hXR : X ≤ Subgroup.normalizer (R : Set G))
    (hUZ : U ≤ Z) (hZV : Z ≤ V) (hVR : V ≤ R)
    (hZ : ∀ g ∈ Subgroup.normalizer (R : Set G), ∀ z ∈ Z, g * z * g⁻¹ ∈ Z)
    (hRX : ∀ r ∈ R, ∀ x ∈ X, r * x * r⁻¹ * x⁻¹ ∈ U) :
    (X.subgroupOf (Subgroup.normalizer (R : Set G))).IsSubnormal := by
  refine isSubnormal_of_conj_le hsub hXR fun g hg x hx => ?_
  rw [← hM]
  refine Subgroup.mem_normalizer_iff.mpr fun v => ⟨fun hv => ?_, fun hv => ?_⟩
  · exact conj_mem_of_threeThree hUZ hZV hVR hZ hRX hg hx hv
  · have h := conj_mem_of_threeThree hUZ hZV hVR hZ hRX hg (X.inv_mem hx) hv
    rwa [show (g⁻¹ * x⁻¹ * g) * (g⁻¹ * x * g * v * (g⁻¹ * x * g)⁻¹) *
        (g⁻¹ * x⁻¹ * g)⁻¹ = v by group] at h

end CFSG.CGT.PushingUpLit.ThmOne
