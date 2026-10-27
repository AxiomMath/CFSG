module

public import CFSG.GroupActions.SubgroupStabilizerOuterBound
public import CFSG.LocalAnalysis.ComponentInitial.SelfCentralizingCoreAutomorphisms

public section

namespace CFSG.GroupActions

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.LocalAnalysis.ComponentInitial (pointwiseFixingAut mem_pointwiseFixingAut
  Tits_self_centralizing_core_automorphism_kernel)
open scoped Pointwise

variable {G : Type*} [Group G]

theorem mulAut_smul_subgroup_eq_map (β : MulAut G) (K : Subgroup G) :
    β • K = K.map β.toMonoidHom := by
  ext x
  rw [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
  rfl

theorem self_centralizing_local_core_Sylow_automorphism_outer_prime_bound [Finite G] {p q : ℕ}
    [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p ≠ q) (S : Sylow q G) (V H : Subgroup G)
    (hVS : V ≤ S) (hSH : (S : Subgroup G) ≤ H) (hVq : IsPGroup q V)
    (hN : Subgroup.normalizer (V : Set G) = H) (hC : Subgroup.centralizer (V : Set G) ⊓ H ≤ V)
    (hCp : ¬ p ∣ Nat.card (pointwiseFixingAut H)) :
    p ^ (Nat.card (Outer G)).factorization p ∣
      p ^ (Nat.card (MulAut (S : Subgroup G))).factorization p := by
  classical
  have : Finite (MulAut G) := Finite.of_injective _ (DFunLike.coe_injective (F := MulAut G))
  have : Finite (MulAut (S : Subgroup G)) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := MulAut (S : Subgroup G)))
  set D := subgroupStabAut (S : Subgroup G) with hD
  set r := subgroupStabRestrict (S : Subgroup G) with hr
  let π : D →* Outer G := (QuotientGroup.mk' (inner G)).comp D.subtype
  have hπ : Function.Surjective π := by
    intro x
    obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective (inner G) x
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S (α • S)
    have hgs : MulAut.conj g • (S : Subgroup G) = α • (S : Subgroup G) := by
      have := congrArg (fun P : Sylow q G => (P : Subgroup G)) hg
      simp only [Sylow.pointwise_smul_def] at this
      exact this
    have hβ : (MulAut.conj g)⁻¹ * α ∈ D := by
      change (S : Subgroup G).map ((MulAut.conj g)⁻¹ * α).toMonoidHom = S
      rw [← mulAut_smul_subgroup_eq_map, mul_smul, ← hgs, inv_smul_smul]
    refine ⟨⟨_, hβ⟩, ?_⟩
    change (((MulAut.conj g)⁻¹ * α : MulAut G) : Outer G) = (α : Outer G)
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (N := inner G)
      ((MulAut.conj g)⁻¹)).2 ⟨g⁻¹, by rw [map_inv]⟩, one_mul]
  have hker : ¬ p ∣ Nat.card r.ker := by
    intro hdvd
    obtain ⟨γ, hγ⟩ := exists_prime_orderOf_dvd_card' (G := r.ker) p hdvd
    set β : D := (γ : D) with hβdef
    have hβord : orderOf (β : MulAut G) = p := by
      rw [Subgroup.orderOf_coe, hβdef, Subgroup.orderOf_coe, hγ]
    have hβS : ∀ s ∈ (S : Subgroup G), (β : MulAut G) s = s := by
      intro s hs
      have h1 := congrArg (fun φ : MulAut (S : Subgroup G) => ((φ ⟨s, hs⟩ : S) : G))
        ((MonoidHom.mem_ker).1 γ.2)
      exact h1
    have hβV : V.map (β : MulAut G).toMonoidHom = V := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        change (β : MulAut G) y ∈ V
        rw [hβS y (hVS hy)]
        exact hy
      · intro hx
        exact ⟨x, hx, hβS x (hVS hx)⟩
    have hβH : (β : MulAut G) ∈ subgroupStabAut H := by
      change H.map (β : MulAut G).toMonoidHom = H
      rw [← hN, Subgroup.map_equiv_normalizer_eq, hβV]
    have hVH : V ≤ H := hVS.trans hSH
    set V' := V.subgroupOf H with hV'
    have hV'n : V'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hVH).2 (hN ▸ le_rfl)
    have hV'c : Subgroup.centralizer (V' : Set H) ≤ V' := by
      intro x hx
      have hxG : (x : G) ∈ Subgroup.centralizer (V : Set G) ⊓ H := by
        refine ⟨Subgroup.mem_centralizer_iff.2 fun v hv => ?_, x.2⟩
        have := Subgroup.mem_centralizer_iff.1 hx ⟨v, hVH hv⟩ hv
        exact congrArg Subtype.val this
      exact hC hxG
    have hV'q : IsPGroup q V' :=
      hVq.of_equiv (Subgroup.subgroupOfEquivOfLe hVH).symm
    have hcore := (Tits_self_centralizing_core_automorphism_kernel hV'c q hV'q).2.2.1
    set ρH := subgroupStabRestrict H ⟨(β : MulAut G), hβH⟩ with hρH
    have hρmem : ρH ∈ pointwiseFixingAut V' := by
      intro v hv
      apply Subtype.ext
      rw [hρH, subgroupStabRestrict_apply]
      exact hβS _ (hVS (Subgroup.mem_subgroupOf.1 hv))
    have hρpow : ρH ^ p = 1 := by
      rw [hρH, ← map_pow]
      have : (⟨(β : MulAut G), hβH⟩ : subgroupStabAut H) ^ p = 1 := by
        apply Subtype.ext
        rw [SubgroupClass.coe_pow, ← hβord, pow_orderOf_eq_one]
        rfl
      rw [this, map_one]
    have hρ1 : ρH = 1 := by
      obtain ⟨k, hk⟩ := hcore ⟨ρH, hρmem⟩
      have h1 : orderOf (⟨ρH, hρmem⟩ : pointwiseFixingAut V') ∣ q ^ k :=
        orderOf_dvd_of_pow_eq_one hk
      have h2 : orderOf (⟨ρH, hρmem⟩ : pointwiseFixingAut V') ∣ p := by
        apply orderOf_dvd_of_pow_eq_one
        exact Subtype.ext hρpow
      have hcop : Nat.Coprime p (q ^ k) :=
        Nat.Coprime.pow_right k ((Nat.coprime_primes hp.out hq.out).2 hpq)
      have h3 := Nat.eq_one_of_dvd_coprimes hcop h2 h1
      have h4 := orderOf_eq_one_iff.1 h3
      exact congrArg Subtype.val h4
    have hβC : (β : MulAut G) ∈ pointwiseFixingAut H := by
      intro h hh
      have := congrArg (fun φ : MulAut H => ((φ ⟨h, hh⟩ : H) : G)) hρ1
      simpa [hρH, subgroupStabRestrict_apply] using this
    apply hCp
    have hord : orderOf (⟨(β : MulAut G), hβC⟩ : pointwiseFixingAut H) = p := by
      rw [← hβord, Subgroup.orderOf_mk]
    rw [← hord]
    exact orderOf_dvd_natCard _
  have hOut : Nat.card (Outer G) ∣ Nat.card D := Subgroup.card_dvd_of_surjective hπ
  have hD : Nat.card r.ker * Nat.card r.range = Nat.card D := Subgroup.card_ker_mul_card_range r
  have hrange : Nat.card r.range ∣ Nat.card (MulAut (S : Subgroup G)) :=
    Subgroup.card_subgroup_dvd_card _
  have hne : ∀ (X : Type _) [Finite X] [Nonempty X], Nat.card X ≠ 0 := fun X _ _ =>
    Nat.card_pos.ne'
  apply pow_dvd_pow p
  have h1 := (Nat.factorization_le_iff_dvd (hne _) (hne _)).2 hOut p
  have h2 := (Nat.factorization_le_iff_dvd (hne _) (hne _)).2 hrange p
  rw [← hD, Nat.factorization_mul (hne _) (hne _), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hker, zero_add] at h1
  exact h1.trans h2

end CFSG.GroupActions
