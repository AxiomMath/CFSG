module

public import CFSG.LargeExtraspecial.S8CorBStatement

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup
open scoped commutatorElement

@[expose] def InvCentSectAbelianSylow (S : Type*) [Group S] : Prop :=
  ∀ s : S, orderOf s = 2 → ∀ R N : Subgroup S, N ≤ R → R ≤ centralizer ({s} : Set S) →
    ∀ (_ : (N.subgroupOf R).Normal), IsSimpleGroup (↥R ⧸ N.subgroupOf R) →
      ∃ P : Sylow 2 (↥R ⧸ N.subgroupOf R),
        ∀ x ∈ (P : Subgroup (↥R ⧸ N.subgroupOf R)),
          ∀ y ∈ (P : Subgroup (↥R ⧸ N.subgroupOf R)), x * y = y * x

section Reduction

variable {X : Type*} [Group X] {U : Subgroup X}

theorem mem_of_mem_center_of_nonabelian {R N : Subgroup X} (hRU : R ≤ U)
    [(N.subgroupOf R).Normal] [IsSimpleGroup (↥R ⧸ N.subgroupOf R)]
    (hnab : ∃ a b : ↥R ⧸ N.subgroupOf R, a * b ≠ b * a) {z : X} (hzR : z ∈ R)
    (hzU : ∀ u ∈ U, u * z = z * u) : z ∈ N := by
  have hc : (QuotientGroup.mk ⟨z, hzR⟩ : ↥R ⧸ N.subgroupOf R) ∈
      center (↥R ⧸ N.subgroupOf R) := by
    rw [mem_center_iff]
    intro q
    induction q using QuotientGroup.induction_on with
    | H r =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (hzU r (hRU r.2))
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (↥R ⧸ N.subgroupOf R)) with h | h
  · rw [h, mem_bot, QuotientGroup.eq_one_iff, mem_subgroupOf] at hc
    exact hc
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ center (↥R ⧸ N.subgroupOf R) := h ▸ mem_top a
    exact hab (mem_center_iff.mp ha b).symm

theorem exists_section_quotient_center {t : X} (htU : t ∈ U) (hto : orderOf t = 2)
    (hnc : ∃ u ∈ U, u * t ≠ t * u) {R N : Subgroup X} (hNR : N ≤ R)
    (hR : R ≤ U ⊓ centralizer ({t} : Set X)) [hNn : (N.subgroupOf R).Normal]
    [IsSimpleGroup (↥R ⧸ N.subgroupOf R)]
    (hnab : ∃ a b : ↥R ⧸ N.subgroupOf R, a * b ≠ b * a) :
    ∃ s : ↥U ⧸ center ↥U, orderOf s = 2 ∧ ∃ R' N' : Subgroup (↥U ⧸ center ↥U), N' ≤ R' ∧
      R' ≤ centralizer ({s} : Set (↥U ⧸ center ↥U)) ∧ ∃ (_ : (N'.subgroupOf R').Normal),
        Nonempty ((↥R ⧸ N.subgroupOf R) ≃* (↥R' ⧸ N'.subgroupOf R')) := by
  have hRU : R ≤ U := fun x hx => (hR hx).1
  have hRt : ∀ x ∈ R, x * t = t * x := fun x hx => mem_centralizer_singleton_iff.mp (hR hx).2
  let π : ↥U →* ↥U ⧸ center ↥U := QuotientGroup.mk' (center ↥U)
  let R' : Subgroup (↥U ⧸ center ↥U) := (R.subgroupOf U).map π
  let N' : Subgroup (↥U ⧸ center ↥U) := (N.subgroupOf U).map π
  refine ⟨π ⟨t, htU⟩, ?_, R', N', ?_, ?_, ?_⟩
  · apply orderOf_eq_prime
    · rw [← map_pow]
      have h2 : (⟨t, htU⟩ : U) ^ 2 = 1 :=
        Subtype.ext (by simp [← hto])
      rw [h2, map_one]
    · intro h1
      obtain ⟨u, hu, hut⟩ := hnc
      have h1' : (⟨t, htU⟩ : U) ∈ center ↥U := (QuotientGroup.eq_one_iff _).mp h1
      exact hut (congrArg Subtype.val (mem_center_iff.mp h1' ⟨u, hu⟩))
  · rintro _ ⟨n, hn, rfl⟩
    exact ⟨n, mem_subgroupOf.mpr (hNR (mem_subgroupOf.mp hn)), rfl⟩
  · rintro _ ⟨r, hr, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact congrArg π (Subtype.ext (hRt r (mem_subgroupOf.mp hr)))
  have hN'n : (N'.subgroupOf R').Normal := by
    constructor
    intro n hn g
    rw [mem_subgroupOf] at hn ⊢
    obtain ⟨m, hm, hmn⟩ := hn
    obtain ⟨r, hr, hrg⟩ := g.2
    refine ⟨r * m * r⁻¹, ?_, ?_⟩
    · have hc := hNn.conj_mem ⟨m, hNR (mem_subgroupOf.mp hm)⟩ (mem_subgroupOf.mpr
        (mem_subgroupOf.mp hm)) ⟨r, mem_subgroupOf.mp hr⟩
      change r * m * r⁻¹ ∈ N.subgroupOf U
      rw [mem_subgroupOf] at hc ⊢
      simpa using hc
    · simp only [map_mul, map_inv, coe_mul, coe_inv]
      rw [hmn, hrg]
  refine ⟨hN'n, ⟨?_⟩⟩
  let ψ : ↥R →* ↥R' := (π.comp (Subgroup.inclusion hRU)).codRestrict R'
    (fun r => ⟨Subgroup.inclusion hRU r, mem_subgroupOf.mpr r.2, rfl⟩)
  let φ : ↥R →* ↥R' ⧸ N'.subgroupOf R' := (QuotientGroup.mk' (N'.subgroupOf R')).comp ψ
  have hφ : Function.Surjective φ := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ q
    obtain ⟨r0, hr0, hy⟩ := y.2
    refine ⟨⟨r0, mem_subgroupOf.mp hr0⟩, ?_⟩
    change QuotientGroup.mk' _ (ψ ⟨r0, mem_subgroupOf.mp hr0⟩) = QuotientGroup.mk' _ y
    congr 1
    exact Subtype.ext hy
  have hker : N.subgroupOf R = φ.ker := by
    ext r
    rw [mem_subgroupOf, MonoidHom.mem_ker]
    change (r : X) ∈ N ↔ QuotientGroup.mk' (N'.subgroupOf R') (ψ r) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
    constructor
    · intro hrN
      exact ⟨Subgroup.inclusion hRU r, mem_subgroupOf.mpr hrN, rfl⟩
    · rintro ⟨m, hm, hmr⟩
      have hz : m⁻¹ * Subgroup.inclusion hRU r ∈ center ↥U := QuotientGroup.eq.mp hmr
      have hmN : (m : X) ∈ N := mem_subgroupOf.mp hm
      have hzR : (m : X)⁻¹ * r ∈ R := mul_mem (inv_mem (hNR hmN)) r.2
      have hzU : ∀ u ∈ U, u * ((m : X)⁻¹ * r) = ((m : X)⁻¹ * r) * u := fun u hu =>
        congrArg Subtype.val (mem_center_iff.mp hz ⟨u, hu⟩)
      have hzN := mem_of_mem_center_of_nonabelian hRU hnab hzR hzU
      have hr : (r : X) = m * ((m : X)⁻¹ * r) := by group
      rw [hr]
      exact mul_mem hmN hzN
  exact (QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)

theorem sect_of_invCentSectAbelianSylow [Finite X] (U : Subgroup X)
    (hS : InvCentSectAbelianSylow (↥U ⧸ center ↥U)) :
    ∀ t ∈ U, orderOf t = 2 → (∃ u ∈ U, u * t ≠ t * u) →
      ∀ R N : Subgroup X, N ≤ R → R ≤ U ⊓ centralizer ({t} : Set X) →
        ∀ (_ : (N.subgroupOf R).Normal), IsSimpleGroup (↥R ⧸ N.subgroupOf R) →
          ∃ P : Sylow 2 (↥R ⧸ N.subgroupOf R),
            ∀ x ∈ (P : Subgroup (↥R ⧸ N.subgroupOf R)),
              ∀ y ∈ (P : Subgroup (↥R ⧸ N.subgroupOf R)), x * y = y * x := by
  intro t htU hto hnc R N hNR hR hNn hs
  by_cases hcomm : ∀ a b : ↥R ⧸ N.subgroupOf R, a * b = b * a
  · obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 (↥R ⧸ N.subgroupOf R)))
    exact ⟨P, fun x _ y _ => hcomm x y⟩
  push Not at hcomm
  obtain ⟨s, hso, R', N', hN'R', hR'C, hN'n, ⟨e⟩⟩ :=
    exists_section_quotient_center htU hto hnc hNR hR hcomm
  have hs' : IsSimpleGroup (↥R' ⧸ N'.subgroupOf R') := e.symm.isSimpleGroup
  obtain ⟨P', hP'⟩ := hS s hso R' N' hN'R' hR'C hN'n hs'
  refine ⟨P'.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective, fun x hx y hy => ?_⟩
  have hx1 : x ∈ (P' : Subgroup (↥R' ⧸ N'.subgroupOf R')).map e.symm.toMonoidHom := hx
  have hy1 : y ∈ (P' : Subgroup (↥R' ⧸ N'.subgroupOf R')).map e.symm.toMonoidHom := hy
  obtain ⟨a, ha, rfl⟩ := mem_map.mp hx1
  obtain ⟨b, hb, rfl⟩ := mem_map.mp hy1
  rw [← map_mul, ← map_mul, hP' a ha b hb]

theorem comm_of_section_of_isSolvable_centralizer (U : Subgroup X)
    (hS : ∀ s : ↥U ⧸ center ↥U, orderOf s = 2 →
      Group.IsSolvable (centralizer ({s} : Set (↥U ⧸ center ↥U))))
    {t : X} (htU : t ∈ U) (hto : orderOf t = 2) (hnc : ∃ u ∈ U, u * t ≠ t * u)
    {R N : Subgroup X} (hNR : N ≤ R) (hR : R ≤ U ⊓ centralizer ({t} : Set X))
    [(N.subgroupOf R).Normal] [IsSimpleGroup (↥R ⧸ N.subgroupOf R)] :
    ∀ a b : ↥R ⧸ N.subgroupOf R, a * b = b * a := by
  by_contra hcomm
  push Not at hcomm
  obtain ⟨s, hso, R', N', -, hR'C, hN'n, ⟨e⟩⟩ :=
    exists_section_quotient_center htU hto hnc hNR hR hcomm
  have := hS s hso
  have hR' : Group.IsSolvable R' :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hR'C)
  have hQ : Group.IsSolvable (↥R' ⧸ N'.subgroupOf R') := inferInstance
  have hQ' : Group.IsSolvable (↥R ⧸ N.subgroupOf R) :=
    Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact hcomm.elim fun a h => h.elim fun b hab =>
    hab (IsSimpleGroup.comm_iff_isSolvable.mpr hQ' a b)

end Reduction

section Criteria

variable {S : Type*} [Group S]

theorem invCentSectAbelianSylow_of_isSolvable
    (h : ∀ s : S, orderOf s = 2 → Group.IsSolvable (centralizer ({s} : Set S))) :
    InvCentSectAbelianSylow S := by
  intro s hs R N _ hR _ hsimple
  have := h s hs
  have hR' : Group.IsSolvable R :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hR)
  have hQ : Group.IsSolvable (↥R ⧸ N.subgroupOf R) := inferInstance
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 (↥R ⧸ N.subgroupOf R)))
  exact ⟨P, fun x _ y _ => IsSimpleGroup.comm_iff_isSolvable.mpr hQ x y⟩

theorem invCentSectAbelianSylow_of_commutator_le [Finite S]
    (h : ∀ s : S, orderOf s = 2 → ∃ Q : Subgroup S, Q ≤ centralizer ({s} : Set S) ∧
      (∀ c ∈ centralizer ({s} : Set S), ∀ q ∈ Q, c * q * c⁻¹ ∈ Q) ∧ IsPGroup 2 Q ∧
      ∀ P : Subgroup S, P ≤ centralizer ({s} : Set S) → IsPGroup 2 P → ⁅P, P⁆ ≤ Q) :
    InvCentSectAbelianSylow S := by
  intro s hs R N _ hR hNn hsimple
  obtain ⟨Q, -, hQn, hQ2, hPQ⟩ := h s hs
  by_cases hcomm : ∀ a b : ↥R ⧸ N.subgroupOf R, a * b = b * a
  · obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 (↥R ⧸ N.subgroupOf R)))
    exact ⟨P, fun x _ y _ => hcomm x y⟩
  let K : Subgroup (↥R ⧸ N.subgroupOf R) := (Q.subgroupOf R).map (QuotientGroup.mk' _)
  have hKn : K.Normal := by
    constructor
    rintro _ ⟨q, hq, rfl⟩ g
    obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective _ g
    refine ⟨r * q * r⁻¹, ?_, by simp⟩
    change q ∈ Q.subgroupOf R at hq
    change r * q * r⁻¹ ∈ Q.subgroupOf R
    rw [mem_subgroupOf] at hq ⊢
    simpa using hQn r (hR r.2) q hq
  have hK2 : IsPGroup 2 K := (hQ2.comap_subtype (K := R)).map _
  have hRQ : ∀ r : R, (r : S) ∈ Q → r ∈ N.subgroupOf R := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with hK | hK
    · intro r hrQ
      have hr : (QuotientGroup.mk' (N.subgroupOf R) r) ∈ K :=
        ⟨r, mem_subgroupOf.mpr hrQ, rfl⟩
      rw [hK, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hr
      exact hr
    · exfalso
      have h2 : IsPGroup 2 (↥R ⧸ N.subgroupOf R) := by
        have hK2' : IsPGroup 2 (⊤ : Subgroup (↥R ⧸ N.subgroupOf R)) := hK ▸ hK2
        exact hK2'.of_equiv Subgroup.topEquiv
      have : Group.IsSolvable (↥R ⧸ N.subgroupOf R) := by
        have := Fact.mk Nat.prime_two
        have := h2.isNilpotent
        infer_instance
      exact hcomm (IsSimpleGroup.comm_iff_isSolvable.mpr this)
  obtain ⟨P₀⟩ := (inferInstance : Nonempty (Sylow 2 R))
  have := Fact.mk Nat.prime_two
  refine ⟨P₀.mapSurjective (QuotientGroup.mk'_surjective (N.subgroupOf R)), fun x hx y hy => ?_⟩
  have hx1 : x ∈ (P₀ : Subgroup R).map (QuotientGroup.mk' (N.subgroupOf R)) := hx
  have hy1 : y ∈ (P₀ : Subgroup R).map (QuotientGroup.mk' (N.subgroupOf R)) := hy
  obtain ⟨a, ha, rfl⟩ := mem_map.mp hx1
  obtain ⟨b, hb, rfl⟩ := mem_map.mp hy1
  have hP' : ⁅(P₀ : Subgroup R).map R.subtype, (P₀ : Subgroup R).map R.subtype⁆ ≤ Q := by
    refine hPQ _ ?_ (P₀.isPGroup'.map _)
    rintro _ ⟨r, -, rfl⟩
    exact hR r.2
  have habQ : ((⁅a, b⁆ : R) : S) ∈ Q := by
    have := hP' (commutator_mem_commutator (mem_map_of_mem R.subtype ha)
      (mem_map_of_mem R.subtype hb))
    rw [← map_commutatorElement] at this
    exact this
  have habN := hRQ _ habQ
  rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact habN

end Criteria

end CFSG.LargeExtraspecial.S8
