module

public import CFSG.LieType.Chevalley.OddDiagramFrobeniusFixedDerived

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley
open scoped Pointwise commutatorElement

theorem map_baseChangeGL_graphFixedRootGroup_eq
    (t : TwistTag) {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = (p ^ f) ^ t.order) (σ : K →+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) {L : Type} [Field L] (ι : K →+* L) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ (p ^ f)) (hFrsurj : Function.Surjective Fr) :
    (graphFixedRootGroup t K σ).map (baseChangeGL ι) = graphFixedRootGroup t L Fr := by
  classical
  set q := p ^ f
  have : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos (pow_pos hp.pos f) _).ne')
  have hq1 : 1 < q := lt_of_lt_of_le hp.one_lt (Nat.le_self_pow (by omega) p)
  have hσsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  have hcomm : ∀ c, Fr (ι c) = ι (σ c) := fun c => by rw [hFr, hσ, map_pow]
  obtain ⟨σ', hσ', -, hcard, -⟩ := finite_graph_field_parameter_fields t hp hf K hK
  have hσσ' : σ'.toRingHom = σ := RingHom.ext fun c => by
    change σ' c = σ c
    rw [hσ', hσ]
  have hpar : ∀ a, ∀ c ∈ orbitField t L Fr a, ∃ c₀ ∈ orbitField t K σ a, ι c₀ = c := by
    intro a c hc
    have : Fintype (orbitField t K σ a) := Fintype.ofFinite _
    have hN : 1 < q ^ (t.orbit a).card :=
      Nat.one_lt_pow (Finset.card_ne_zero.2 (t.orbit_nonempty a)) hq1
    have hS : ∀ x ∈ Finset.univ.image (fun c₀ : orbitField t K σ a => ι c₀),
        x ^ q ^ (t.orbit a).card = x := fun x hx => by
      obtain ⟨c₀, -, rfl⟩ := Finset.mem_image.1 hx
      rw [← map_pow, ← pow_apply_eq_pow hσ, (mem_orbitField (t := t)).1 c₀.2]
    have hSc : q ^ (t.orbit a).card ≤
        (Finset.univ.image (fun c₀ : orbitField t K σ a => ι c₀)).card := by
      rw [Finset.card_image_of_injective (f := fun c₀ : orbitField t K σ a => ι c₀) _
          (ι.injective.comp Subtype.val_injective),
        Finset.card_univ, ← Nat.card_eq_fintype_card, ← hσσ', hcard]
    have hc' : c ^ q ^ (t.orbit a).card = c := by
      rw [← pow_apply_eq_pow hFr]
      exact (mem_orbitField (t := t)).1 hc
    obtain ⟨c₀, -, hc₀⟩ := Finset.mem_image.1 (mem_of_pow_eq_self_of_le_card hN hS hSc hc')
    exact ⟨c₀, c₀.2, hc₀⟩
  exact le_antisymm (map_baseChangeGL_graphFixedRootGroup_le hσsurj hcomm)
    (graphFixedRootGroup_le_map_baseChangeGL hFrsurj hcomm hpar)

theorem exceptional_ambient_twisted_Frobenius_fixed_normalizer
    (t : TwistTag) {p f : ℕ}
    (hp : p.Prime) (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = (p ^ f) ^ t.order)
    (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) (L : Type) [Field L] [Algebra K L]
    [IsAlgClosure K L] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (p ^ f)) :
    (twistedFixedGroup t L Fr : Set (ModGL t.tag L)) =
      (graphFixedTorus t L Fr : Set (ModGL t.tag L)) *
        ((graphFixedRootGroup t K σ).map (baseChangeGL (algebraMap K L)) :
          Set (ModGL t.tag L)) ∧
    (graphFixedRootGroup t K σ).map (baseChangeGL (algebraMap K L)) ≤
      twistedFixedGroup t L Fr ∧
    (((graphFixedRootGroup t K σ).map (baseChangeGL (algebraMap K L))).subgroupOf
      (twistedFixedGroup t L Fr)).Normal ∧
    (∀ [(((graphFixedRootGroup t K σ).map (baseChangeGL (algebraMap K L))).subgroupOf
        (twistedFixedGroup t L Fr)).Normal],
      ∀ a b : ↥(twistedFixedGroup t L Fr) ⧸
        ((graphFixedRootGroup t K σ).map (baseChangeGL (algebraMap K L))).subgroupOf
          (twistedFixedGroup t L Fr), a * b = b * a) ∧
    ⁅twistedFixedGroup t L Fr, twistedFixedGroup t L Fr⁆ =
      (graphFixedRootGroup t K σ).map (baseChangeGL (algebraMap K L)) ∧
    twistedFixedGroup t L Fr ≤ Subgroup.normalizer
      ((graphFixedRootGroup t K σ).map (baseChangeGL (algebraMap K L)) : Set (ModGL t.tag L)) := by
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hq : 0 < p ^ f := pow_pos hp.pos f
  have hFrsurj : Function.Surjective Fr := fun y => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq y hq
    exact ⟨z, by rw [hFr, hz]⟩
  set σL : L ≃+* L := RingEquiv.ofBijective Fr ⟨Fr.injective, hFrsurj⟩
  have hσL : σL.toRingHom = Fr := RingHom.ext fun _ => rfl
  have hH := map_baseChangeGL_graphFixedRootGroup_eq t hp hf K hK σ hσ (algebraMap K L) hFr
    hFrsurj
  have hperf : ⁅graphFixedRootGroup t L Fr, graphFixedRootGroup t L Fr⁆ =
      graphFixedRootGroup t L Fr := by
    rw [← hH, ← Subgroup.map_commutator, (finite_fixed_root_group_perfect t hp hf K hK σ hσ).1]
  obtain ⟨hnormal, hmul, -, -, hder⟩ := fixed_root_generated_normal_subgroup t L σL
  rw [hσL] at hnormal hmul hder
  have hder' := hder hperf
  rw [hH]
  refine ⟨hmul, graphFixedRootGroup_le t L Fr, hnormal, fun a b => ?_, hder',
    (Subgroup.normal_subgroupOf_iff_le_normalizer (graphFixedRootGroup_le t L Fr)).1 hnormal⟩
  induction a using QuotientGroup.induction_on with | H r => ?_
  induction b using QuotientGroup.induction_on with | H s => ?_
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf,
    ← hder']
  have e : (((r * s)⁻¹ * (s * r) : twistedFixedGroup t L Fr) : ModGL t.tag L) =
      ⁅((s : ModGL t.tag L))⁻¹, ((r : ModGL t.tag L))⁻¹⁆ := by
    rw [commutatorElement_def, inv_inv, inv_inv]
    simp [mul_assoc]
  rw [e]
  exact Subgroup.commutator_mem_commutator (inv_mem s.2) (inv_mem r.2)

end CFSG.LieType.Chevalley
