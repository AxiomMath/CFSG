module

public import CFSG.ClassicalInvolution.Generic.Induction
public import CFSG.LieType.Steinberg.TwistedE6.Clause0

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.TitsSimplicity CFSG.ClassicalInvolution.Generic

theorem exc3_pow_three_eq_one {G : Type*} [CommGroup G] {u : Fin (Tag.rank .E6) → G}
    (h : ∀ i, ∏ a, u a ^ Tag.cartan .E6 a i = 1) (m : Fin (Tag.rank .E6)) : u m ^ 3 = 1 := by
  set B : Fin (Tag.rank .E6) → Fin (Tag.rank .E6) → ℤ :=
    ![![4, 3, 5, 6, 4, 2], ![3, 6, 6, 9, 6, 3], ![5, 6, 10, 12, 8, 4], ![6, 9, 12, 18, 12, 6],
      ![4, 6, 8, 12, 10, 5], ![2, 3, 4, 6, 5, 4]]
  have key : ∀ a m : Fin (Tag.rank .E6),
      ∑ i, Tag.cartan .E6 a i * B i m = if a = m then 3 else 0 := by
    decide
  have h1 : ∏ i, (∏ a, u a ^ Tag.cartan .E6 a i) ^ B i m = 1 :=
    Finset.prod_eq_one fun i _ => by rw [h i, one_zpow]
  have h2 : ∏ i, (∏ a, u a ^ Tag.cartan .E6 a i) ^ B i m = u m ^ (3 : ℤ) := by
    simp_rw [← Finset.prod_zpow, ← zpow_mul]
    rw [Finset.prod_comm]
    simp_rw [Finset.prod_zpow_eq_zpow_sum, key]
    rw [Finset.prod_eq_single m]
    · simp
    · intro a _ ha
      simp [ha]
    · simp
  rw [h2] at h1
  exact_mod_cast h1

section Torus

variable {k : Type} [Field k]

theorem exc3_torusHom_conj_xm (u : Fin (Tag.rank .E6) → kˣ) {γ : Fin (Tag.rank .E6) → ℤ}
    (hγ : IsRoot .E6 γ) (c : k) :
    torusHom k u * e6Data_valid.xm k γ c * (torusHom k u)⁻¹ =
      e6Data_valid.xm k γ (((∏ a, u a ^ MinData.toWeight γ a : kˣ) : k) * c) := by
  have key : ∀ s : Finset (Fin (Tag.rank .E6)),
      torusHom k (∏ a ∈ s, Pi.mulSingle a (u a)) * e6Data_valid.xm k γ c *
          (torusHom k (∏ a ∈ s, Pi.mulSingle a (u a)))⁻¹ =
        e6Data_valid.xm k γ (((∏ a ∈ s, u a ^ MinData.toWeight γ a : kˣ) : k) * c) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, map_mul, torusHom_mulSingle, mul_inv_rev,
        show e6Data_valid.hm k a (u a) * torusHom k (∏ a ∈ s, Pi.mulSingle a (u a)) *
            e6Data_valid.xm k γ c * ((torusHom k (∏ a ∈ s, Pi.mulSingle a (u a)))⁻¹ *
              (e6Data_valid.hm k a (u a))⁻¹) =
          e6Data_valid.hm k a (u a) * (torusHom k (∏ a ∈ s, Pi.mulSingle a (u a)) *
            e6Data_valid.xm k γ c * (torusHom k (∏ a ∈ s, Pi.mulSingle a (u a)))⁻¹) *
              (e6Data_valid.hm k a (u a))⁻¹ from by group,
        ih, e6Data_valid.hm_conj_xm k hγ, Units.val_mul, mul_assoc]
  simpa [Finset.univ_prod_mulSingle] using key Finset.univ

theorem exc3_char_eq_one_of_fixed {θ : k →+* k} {u : Fin (Tag.rank .E6) → kˣ}
    (hc : ∀ g ∈ fixedGroup k θ, torusHom k u * g = g * torusHom k u)
    {a : Fin (Tag.rank .E6)} (ha : rhoPerm a = a) :
    ∏ x, u x ^ Tag.cartan .E6 x a = 1 := by
  have hρ : rho (Pi.single a 1) = Pi.single a 1 := by rw [rho_single, ha]
  have hα : IsRoot .E6 (Pi.single a 1) := isRoot_single .E6 a
  have hy := hc _ (xFixed θ hα hρ 1 (map_one θ)).2
  rw [xFixed_val] at hy
  have h1 : torusHom k u * e6Data_valid.xm k (Pi.single a 1) 1 * (torusHom k u)⁻¹ =
      e6Data_valid.xm k (Pi.single a 1) 1 := by
    rw [hy, mul_inv_cancel_right]
  rw [exc3_torusHom_conj_xm u hα] at h1
  have h2 := e6Data_valid.xm_injective k hα h1
  rw [mul_one] at h2
  have h3 : (∏ x, u x ^ MinData.toWeight (Pi.single a 1 : Fin (Tag.rank .E6) → ℤ) x : kˣ) = 1 :=
    Units.ext (by rw [h2, Units.val_one])
  simpa only [MinData.toWeight_single] using h3

theorem exc3_char_eq_one_of_pair {θ : k →+* k} (hθ : ∀ c, θ (θ c) = c)
    {u : Fin (Tag.rank .E6) → kˣ}
    (hc : ∀ g ∈ fixedGroup k θ, torusHom k u * g = g * torusHom k u)
    {a : Fin (Tag.rank .E6)} (ha : rhoPerm a ≠ a) :
    ∏ x, u x ^ Tag.cartan .E6 x a = 1 := by
  have hα : IsRoot .E6 (Pi.single a 1) := isRoot_single .E6 a
  have hne : rho (Pi.single a 1) ≠ Pi.single a 1 := by
    rw [rho_single]
    intro h
    have h' := congrFun h (rhoPerm a)
    rw [Pi.single_eq_same, Pi.single_eq_of_ne ha] at h'
    exact one_ne_zero h'
  have hy := hc _ (xPair θ hθ hα hne 1).2
  rw [xPair_val] at hy
  have h1 : torusHom k u * (e6Data_valid.xm k (Pi.single a 1) 1 *
        e6Data_valid.xm k (rho (Pi.single a 1)) ((twistSign (Pi.single a 1) : k) * θ 1)) *
        (torusHom k u)⁻¹ = e6Data_valid.xm k (Pi.single a 1) 1 *
        e6Data_valid.xm k (rho (Pi.single a 1)) ((twistSign (Pi.single a 1) : k) * θ 1) := by
    rw [hy, mul_inv_cancel_right]
  rw [show ∀ X Y : e6Data_valid.minGroup k, torusHom k u * (X * Y) * (torusHom k u)⁻¹ =
      (torusHom k u * X * (torusHom k u)⁻¹) * (torusHom k u * Y * (torusHom k u)⁻¹) from
        fun X Y => by group, exc3_torusHom_conj_xm u hα,
    exc3_torusHom_conj_xm u (isRoot_rho hα)] at h1
  have h2 := (xm_mul_xm_rho_inj hα hne h1).1
  rw [mul_one] at h2
  have h3 : (∏ x, u x ^ MinData.toWeight (Pi.single a 1 : Fin (Tag.rank .E6) → ℤ) x : kˣ) = 1 :=
    Units.ext (by rw [h2, Units.val_one])
  simpa only [MinData.toWeight_single] using h3

theorem exc3_exists_torusHom_of_mem_iSup_torus {g : e6Data_valid.minGroup k}
    (hg : g ∈ ⨆ a, e6Data_valid.torus k a) : ∃ u, torusHom k u = g := by
  have hle : (⨆ a, e6Data_valid.torus k a) ≤ (torusHom k).range := by
    refine iSup_le fun a => ?_
    intro _ hx
    obtain ⟨t, rfl⟩ := (e6Data_valid.mem_torus k).1 hx
    exact ⟨Pi.mulSingle a t, torusHom_mulSingle a t⟩
  exact hle hg

theorem exc3_center_fixedGroup (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    (hk : Nat.Coprime 3 (Nat.card k - 1)) : Subgroup.center (fixedGroup k θ) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hct := twistedDatum_isCTGroupDatum θ hθ (iSup_twistedDatum_rootGroup θ hθ)
  have h1 := (center_eq_normalCore_borel hct (twistedDatum_steinbergExtras θ hθ)
    (twistedDatum_bruhatExtras θ)) ▸ hz
  have hzT : z ∈ ⨆ i, hHat k θ i := normalCore_borel_le_iSup hct (twistedDatum_bruhatExtras θ) h1
  have hle : (⨆ i, hHat k θ i : Subgroup (fixedGroup k θ)) ≤
      (⨆ a, e6Data_valid.torus k a).comap (fixedGroup k θ).subtype :=
    iSup_le fun i x hx => hHatE_le_iSup_torus θ i (Subgroup.mem_subgroupOf.mp hx)
  obtain ⟨u, hu⟩ := exc3_exists_torusHom_of_mem_iSup_torus (Subgroup.mem_comap.mp (hle hzT))
  have hc : ∀ g ∈ fixedGroup k θ, torusHom k u * g = g * torusHom k u := by
    intro g hg
    have := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨g, hg⟩)
    rw [hu]
    exact this.symm
  have hchar : ∀ i, ∏ x, u x ^ Tag.cartan .E6 x i = 1 := fun i => by
    by_cases hi : rhoPerm i = i
    · exact exc3_char_eq_one_of_fixed hc hi
    · exact exc3_char_eq_one_of_pair hθ hc hi
  have hu1 : u = 1 := by
    funext m
    refine (pow_eq_one_iff_of_coprime hk).1 ⟨exc3_pow_three_eq_one hchar m, ?_⟩
    rw [← Nat.card_units, pow_card_eq_one']
  rw [Subgroup.mem_bot]
  have hu' : torusHom k u = (z : e6Data_valid.minGroup k) := hu
  apply Subtype.ext
  rw [← hu', hu1, map_one]
  rfl

end Torus

theorem exc3_center_twistedE6 [Fact (Nat.Prime 3)] :
    Subgroup.center (twistedE6Group 3 1) = ⊥ := by
  refine exc3_center_fixedGroup (frobQ 3 1) (frobQ_frobQ 3 1 le_rfl) ?_
  rw [GaloisField.card 3 (2 * 1) (by norm_num)]
  norm_num

theorem exc3_center_twistedE6_model (hp : Nat.Prime 3) :
    Subgroup.center (modelUniv .twistedE6 0 3 1 hp).K = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  exact exc3_center_twistedE6

end CFSG.ClassicalInvolution.Q3
