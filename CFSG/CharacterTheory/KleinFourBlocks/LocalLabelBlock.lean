module

public import CFSG.CharacterTheory.KleinFourBlocks.DefectZeroBlock
public import CFSG.CharacterTheory.KleinFourBlocks.ExactOrder

public section

open scoped BigOperators Classical

namespace CFSG.KleinFourBlocks

open CFSG CFSG.Semidihedral.Principal CFSG.TwoRankLowerBound.Helpers

section Vanishing

variable {X : Type} [Group X] [Fintype X]

omit [Fintype X] in
theorem not_subgroupSubconjugate_zpowers_of_elemAbelianFactor {V R : Subgroup X}
    (h : ElemAbelianFactor V R) {u : X} (hu : u ∈ R) (hu1 : u ≠ 1) :
    ¬ subgroupSubconjugate (Subgroup.zpowers u) V := by
  rintro ⟨c, hc⟩
  have hmem : (MulAut.conj c) u ∈ V := hc (Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers u))
  obtain ⟨a, ha, r, hr, rfl⟩ := h.prod_eq c
  have hRmem : r * u * r⁻¹ ∈ R := R.mul_mem (R.mul_mem hr hu) (R.inv_mem hr)
  have hconj : (MulAut.conj (a * r)) u = r * u * r⁻¹ := by
    rw [MulAut.conj_apply]
    have hcomm : a * (r * u * r⁻¹) = (r * u * r⁻¹) * a := h.comm a ha _ hRmem
    calc a * r * u * (a * r)⁻¹ = a * (r * u * r⁻¹) * a⁻¹ := by group
      _ = (r * u * r⁻¹) * a * a⁻¹ := by rw [hcomm]
      _ = r * u * r⁻¹ := by group
  rw [hconj] at hmem
  have hbot : r * u * r⁻¹ ∈ V ⊓ R := ⟨hmem, hRmem⟩
  rw [h.inf_eq_bot, Subgroup.mem_bot] at hbot
  apply hu1
  calc u = r⁻¹ * (r * u * r⁻¹) * r := by group
    _ = 1 := by rw [hbot]; group

theorem character_eq_zero_of_defect_elemAbelianFactor
    (wb : FiniteIrreducibleCharacterBasis X) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] {V R : Subgroup X}
    (h : ElemAbelianFactor V R) (n : wb.index) (hD : coefficientBlockDefect wb ideal 2 n V)
    {x : X} (hx : x ∈ R) (h2 : 2 ∣ orderOf x) : (wb.representation n).character x = 0 := by
  obtain ⟨u, v, e, hux, -, huv, hprod, hu, hv⟩ :=
    finite_prime_primary_factorization x 2 Nat.prime_two
  have huR : u ∈ R := (Subgroup.zpowers_le.mpr hx) hux
  have hcop : Nat.Coprime (orderOf u) (orderOf v) :=
    Nat.Coprime.coprime_dvd_left hu (Nat.Coprime.pow_left e hv)
  have hord : orderOf x = orderOf u * orderOf v := by
    rw [← hprod]
    exact huv.orderOf_mul_eq_mul_orderOf_of_coprime hcop
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one, one_mul] at hord
    rw [hord] at h2
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hv) h2
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hu
  exact (block_characters_vanish_outside_defect_primary wb ideal 2 n V hD x u v hprod.symm huv
    ⟨k, hk⟩ hv).1 (not_subgroupSubconjugate_zpowers_of_elemAbelianFactor h huR hu1) n
    (coefficientBlock_self_mem _ _ n)

end Vanishing

section LocalSetup

variable {C : Type} [Group C]

theorem closure_pair_le_centralizer (t s : C) (htcent : ∀ g : C, g * t = t * g)
    (ht : orderOf t = 2) (hs : orderOf s = 2) :
    Subgroup.closure ({t, s} : Set C) ≤ Subgroup.centralizer (Subgroup.zpowers s : Set C) := by
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hs2 : s * s = 1 := by rw [← pow_two, ← hs, pow_orderOf_eq_one]
  have hts : t * s = s * t := (htcent s).symm
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hc : s * v = v * s := by
    rcases mem_closure_pair_of_commuting_involutions ht2 hs2 hts hv with rfl | rfl | rfl | rfl
    · rw [one_mul, mul_one]
    · exact hts.symm
    · rfl
    · rw [← mul_assoc, ← hts]
  exact (Commute.zpow_left hc k).eq

theorem elemAbelianFactor_closure_pair_subgroupOf (t s : C) (htcent : ∀ g : C, g * t = t * g)
    (ht : orderOf t = 2) (hs : orderOf s = 2) (R : Subgroup C)
    (hRD : R ≤ Subgroup.centralizer (Subgroup.zpowers s : Set C))
    (hDVR : ∀ x ∈ Subgroup.centralizer (Subgroup.zpowers s : Set C),
      ∃ v ∈ Subgroup.closure ({t, s} : Set C), ∃ r ∈ R, x = v * r)
    (hVR : Subgroup.closure ({t, s} : Set C) ⊓ R = ⊥) :
    ElemAbelianFactor
      ((Subgroup.closure ({t, s} : Set C)).subgroupOf
        (Subgroup.centralizer (Subgroup.zpowers s : Set C)))
      (R.subgroupOf (Subgroup.centralizer (Subgroup.zpowers s : Set C))) := by
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hs2 : s * s = 1 := by rw [← pow_two, ← hs, pow_orderOf_eq_one]
  have hts : t * s = s * t := (htcent s).symm
  have hVmem : ∀ v ∈ Subgroup.closure ({t, s} : Set C), v = 1 ∨ v = t ∨ v = s ∨ v = t * s :=
    fun v hv => mem_closure_pair_of_commuting_involutions ht2 hs2 hts hv
  have hV2 : ∀ v ∈ Subgroup.closure ({t, s} : Set C), v * v = 1 := by
    intro v hv
    rcases hVmem v hv with rfl | rfl | rfl | rfl
    · exact one_mul 1
    · exact ht2
    · exact hs2
    · rw [mul_assoc, ← mul_assoc s, ← hts, mul_assoc, hs2, mul_one, ht2]
  have hsD : ∀ x ∈ Subgroup.centralizer (Subgroup.zpowers s : Set C), s * x = x * s := by
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp hx s (Subgroup.mem_zpowers s))
  have hVcomm : ∀ v ∈ Subgroup.closure ({t, s} : Set C),
      ∀ x ∈ Subgroup.centralizer (Subgroup.zpowers s : Set C), v * x = x * v := by
    intro v hv x hx
    rcases hVmem v hv with rfl | rfl | rfl | rfl
    · rw [one_mul, mul_one]
    · exact (htcent x).symm
    · exact hsD x hx
    · rw [mul_assoc, hsD x hx, ← mul_assoc, ← htcent x, mul_assoc]
  have hVD := closure_pair_le_centralizer t s htcent ht hs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    exact Subtype.ext (hV2 (v : C) (Subgroup.mem_subgroupOf.mp hv))
  · intro a ha b hb
    exact Subtype.ext (hVcomm (a : C) (Subgroup.mem_subgroupOf.mp ha) (b : C) b.2)
  · intro v hv r hr
    exact Subtype.ext (hVcomm (v : C) (Subgroup.mem_subgroupOf.mp hv) (r : C) r.2)
  · rw [eq_bot_iff]
    intro x hx
    have hmem : (x : C) ∈ Subgroup.closure ({t, s} : Set C) ⊓ R :=
      ⟨Subgroup.mem_subgroupOf.mp hx.1, Subgroup.mem_subgroupOf.mp hx.2⟩
    rw [hVR, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]
    exact Subtype.ext hmem
  · intro x
    obtain ⟨v, hv, r, hr, hxr⟩ := hDVR x x.2
    exact ⟨⟨v, hVD hv⟩, hv, ⟨r, hRD hr⟩, hr, Subtype.ext hxr⟩

end LocalSetup

theorem local_label_block_description {C : Type} [Group C] [Fintype C] (t s : C)
    (htcent : ∀ g : C, g * t = t * g) (ht : orderOf t = 2) (hs : orderOf s = 2) (hst : s ≠ t)
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers s : Set C)))
    (R : Subgroup C) (hRD : R ≤ Subgroup.centralizer (Subgroup.zpowers s : Set C))
    (hDVR : ∀ x ∈ Subgroup.centralizer (Subgroup.zpowers s : Set C),
      ∃ v ∈ Subgroup.closure ({t, s} : Set C), ∃ r ∈ R, x = v * r)
    (hVR : Subgroup.closure ({t, s} : Set C) ⊓ R = ⊥)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (n : localBasis.index)
    (hN1 : ∀ (x x' : Subgroup.centralizer (Subgroup.zpowers s : Set C)) (v : C),
      v ∈ Subgroup.closure ({t, s} : Set C) → (x : C) = v * (x' : C) → (x' : C) ∈ R →
        (localBasis.representation n).character x = (localBasis.representation n).character x')
    (hdeg : ∃ d : ℕ, (localBasis.representation n).character 1 = d ∧
      2 ^ (Nat.card R).factorization 2 ∣ d) :
    (∀ x : Subgroup.centralizer (Subgroup.zpowers s : Set C), (x : C) ∈ R →
        2 ∣ orderOf (x : C) → (localBasis.representation n).character x = 0) ∧
    (∀ lam : ↥(Subgroup.closure ({t, s} : Set C)) →* ℂˣ,
        ∃ ψ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) n,
          ∀ (x x' : Subgroup.centralizer (Subgroup.zpowers s : Set C))
            (v : ↥(Subgroup.closure ({t, s} : Set C))),
            (x : C) = (v : C) * (x' : C) → (x' : C) ∈ R →
              (localBasis.representation ψ).character x =
                (localBasis.representation n).character x' * (lam v : ℂ)) ∧
    (∀ f : Subgroup.centralizer (Subgroup.zpowers s : Set C) → ℂ,
        f ∈ coefficientCharacterSpace localBasis
            (coefficientBlock localBasis (localizedComplexIntegerRing ideal) n) ↔
          ∃ F : ↥(Subgroup.closure ({t, s} : Set C)) → ℂ,
            ∀ (x x' : Subgroup.centralizer (Subgroup.zpowers s : Set C))
              (v : ↥(Subgroup.closure ({t, s} : Set C))),
              (x : C) = (v : C) * (x' : C) → (x' : C) ∈ R →
                f x = (localBasis.representation n).character x' * F v) := by
  have _ := hst
  have E := elemAbelianFactor_closure_pair_subgroupOf t s htcent ht hs R hRD hDVR hVR
  have hVX := closure_pair_le_centralizer t s htcent ht hs
  have hcard : Nat.card ↥(R.subgroupOf (Subgroup.centralizer (Subgroup.zpowers s : Set C))) =
      Nat.card ↥R := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRD).toEquiv
  obtain ⟨-, hb, hc, hd⟩ := defect_zero_twist_block_and_class_functions localBasis ideal _ _
    E.sq_eq_one E.comm_V E.comm E.inf_eq_bot E.prod_eq n
    (fun x x' v hv hx hx' => hN1 x x' (v : C) hv (by rw [hx]; rfl) hx')
    (by rw [hcard]; exact hdeg)
  refine ⟨fun x hxR h2 => ?_, fun lam => ?_, fun f => ?_⟩
  · refine character_eq_zero_of_defect_elemAbelianFactor localBasis ideal E n hd
      (Subgroup.mem_subgroupOf.mpr hxR) ?_
    rwa [Subgroup.orderOf_coe] at h2
  · obtain ⟨ψ, hψ, hψval⟩ := hb (lam.comp (Subgroup.subgroupOfEquivOfLe hVX).toMonoidHom)
    refine ⟨ψ, hψ, fun x x' v hx hx' => ?_⟩
    have h := hψval x x' ((Subgroup.subgroupOfEquivOfLe hVX).symm v) (Subtype.ext hx)
      (Subgroup.mem_subgroupOf.mpr hx')
    simpa using h
  · rw [hc f]
    constructor
    · rintro ⟨F, hF⟩
      refine ⟨fun v => F ((Subgroup.subgroupOfEquivOfLe hVX).symm v), fun x x' v hx hx' => ?_⟩
      exact hF x x' ((Subgroup.subgroupOfEquivOfLe hVX).symm v) (Subtype.ext hx)
        (Subgroup.mem_subgroupOf.mpr hx')
    · rintro ⟨F, hF⟩
      refine ⟨fun v => F (Subgroup.subgroupOfEquivOfLe hVX v), fun x x' v hx hx' => ?_⟩
      exact hF x x' (Subgroup.subgroupOfEquivOfLe hVX v) (by rw [hx]; rfl)
        (Subgroup.mem_subgroupOf.mp hx')

end CFSG.KleinFourBlocks
