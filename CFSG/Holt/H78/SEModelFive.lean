module

public import CFSG.Holt.H78.SEModelAction
public import CFSG.Holt.H78.Lemma17
public import CFSG.GH74.Uniqueness.Bender.Out
public import CFSG.GH74.Uniqueness.Bender.Sylow2SpecialSuzuki

public section

namespace CFSG.Holt.H78

open MulAction CFSG.GH74.Uniqueness.Bender

namespace BenderType

variable {X : Type*} [Group X] [Finite X] {n i e : ℕ}

theorem mem_rootCenter_of_mem_sylow (hX : BenderType X n i e) (Q : Sylow 2 X) {x : X}
    (hx : x ∈ (Q : Subgroup X)) (hx2 : orderOf x = 2) : x ∈ rootCenter (Q : Subgroup X) := by
  obtain ⟨t, hc⟩ := hX.exists_benderCore Q
  exact hc.center_of_involution x (le_borel _ hx) hx2

theorem commute_of_commute (hX : BenderType X n i e) {z a b : X} (hz : orderOf z = 2)
    (ha : orderOf a = 2) (hb : orderOf b = 2) (haz : a * z = z * a) (hbz : b * z = z * b) :
    a * b = b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  obtain ⟨t, hc⟩ := hX.exists_benderCore Q
  have hzQ : z ∈ (Q : Subgroup X) := hQ (Subgroup.mem_zpowers z)
  have hC := (hX.lemma_3_4_b Q hc.sq_eq_one hc.not_mem ⟨le_borel _ hzQ, hz⟩).1
  have haZ := hc.center_of_involution a (hC (Subgroup.mem_centralizer_singleton_iff.mpr haz)) ha
  have hbZ := hc.center_of_involution b (hC (Subgroup.mem_centralizer_singleton_iff.mpr hbz)) hb
  exact (mem_rootCenter_iff.mp hbZ).2 a (rootCenter_le _ haZ)

omit [Finite X] in
private theorem alternating_six_witness :
    ∃ a b z : alternatingGroup (Fin 6), a * a = 1 ∧ a ≠ 1 ∧ b * b = 1 ∧ b ≠ 1 ∧
      z * z = 1 ∧ z ≠ 1 ∧ a * z = z * a ∧ b * z = z * b ∧ a * b ≠ b * a := by
  refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    ⟨Equiv.swap 1 2 * Equiv.swap 4 5, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    ⟨Equiv.swap 0 3 * Equiv.swap 1 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩, ?_⟩
  decide

theorem not_mulEquiv_alternatingGroup (hX : BenderType X n i e) {Δ : Type*} [Fintype Δ]
    [DecidableEq Δ] (h6 : 6 ≤ Fintype.card Δ) (φ : X ≃* alternatingGroup Δ) : False := by
  classical
  obtain ⟨ι⟩ : Nonempty (Fin 6 ↪ Δ) :=
    Function.Embedding.nonempty_of_card_le (by simpa using h6)
  set F : Equiv.Perm (Fin 6) →* Equiv.Perm Δ := Equiv.Perm.extendDomainHom ι.toEquivRange
  have hF : Function.Injective F := Equiv.Perm.extendDomainHom_injective _
  have hFalt : ∀ σ : alternatingGroup (Fin 6), F σ ∈ alternatingGroup Δ := fun σ => by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.extendDomainHom_apply,
      Equiv.Perm.sign_extendDomain]
    exact Equiv.Perm.mem_alternatingGroup.mp σ.2
  set F' : alternatingGroup (Fin 6) →* alternatingGroup Δ :=
    (F.comp (alternatingGroup (Fin 6)).subtype).codRestrict _ hFalt
  have hF' : Function.Injective F' := fun x y h => Subtype.ext (hF (congrArg Subtype.val h))
  set f : alternatingGroup (Fin 6) →* X := φ.symm.toMonoidHom.comp F'
  have hf : Function.Injective f := φ.symm.injective.comp hF'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, b, z, ha2, ha1, hb2, hb1, hz2, hz1, haz, hbz, hab⟩ := alternating_six_witness
  have hord : ∀ y, y * y = 1 → y ≠ 1 → orderOf (f y) = 2 := fun y h2 h1 => by
    rw [orderOf_injective f hf]
    exact orderOf_eq_prime (by rw [sq]; exact h2) h1
  apply hab
  apply hf
  rw [map_mul, map_mul]
  exact commute_of_commute hX (hord z hz2 hz1) (hord a ha2 ha1) (hord b hb2 hb1)
    (by rw [← map_mul, haz, map_mul]) (by rw [← map_mul, hbz, map_mul])

omit [Finite X] in
theorem isSolvable_outer {X : Type} [Group X] (hX : BenderType X n i e) :
    Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) := by
  rcases hX.cases' with ⟨rfl, rfl, -⟩ | ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩
  · have := hX.outer_linear.1
    exact Group.isSolvable_of_comm fun a b => IsCyclic.commGroup.mul_comm a b
  · have := hX.outer_suzuki.1
    exact Group.isSolvable_of_comm fun a b => IsCyclic.commGroup.mul_comm a b
  · obtain ⟨Dd, hDd, hDdc, -, hQc, -⟩ := hX.outer_unitary
    have : Group.IsSolvable Dd :=
      Group.isSolvable_of_comm fun a b => IsCyclic.commGroup.mul_comm a b
    have : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer X ⧸ Dd) :=
      Group.isSolvable_of_comm fun a b => IsCyclic.commGroup.mul_comm a b
    exact Group.isSolvable_of_subgroup_quotient Dd

end BenderType

namespace IsNaturalSE

variable {Δ : Type*} [Finite Δ] {M : Subgroup (Equiv.Perm Δ)}

theorem exists_isBenderAction (hM : IsNaturalSE M) : ∃ n i e : ℕ, IsBenderAction M Δ n i e :=
  isNaturalSE_iff.mp hM

theorem existsUnique_fixed (hM : IsNaturalSE M) {x : M} (hx : orderOf x = 2) :
    ∃! δ : Δ, x • δ = δ := by
  obtain ⟨n, i, e, hA⟩ := hM.exists_isBenderAction
  exact hA.existsUnique_fixed hx

theorem isConj (hM : IsNaturalSE M) {x y : M} (hx : orderOf x = 2) (hy : orderOf y = 2) :
    IsConj x y := by
  obtain ⟨n, i, e, hA⟩ := hM.exists_isBenderAction
  exact hA.isConj_of_orderOf_eq_two hx hy

theorem odd_card_and_five_le (hM : IsNaturalSE M) : Odd (Nat.card Δ) ∧ 5 ≤ Nat.card Δ := by
  obtain ⟨n, i, e, hA⟩ := hM.exists_isBenderAction
  refine ⟨hA.odd_card, ?_⟩
  rw [hA.card_eq]
  have := hA.four_le_pow
  omega

theorem isStronglyEmbedded_stabilizer (hM : IsNaturalSE M) (δ : Δ) :
    CFSG.IsStronglyEmbedded (stabilizer M δ) := by
  obtain ⟨n, i, e, hA⟩ := hM.exists_isBenderAction
  exact hA.isStronglyEmbedded_stabilizer δ

end IsNaturalSE

theorem IsNaturalSE.not_mulEquiv_alternatingGroup {Δ : Type*} [Finite Δ]
    {M : Subgroup (Equiv.Perm Δ)} (hM : IsNaturalSE M) {Δ' : Type*} [Fintype Δ']
    [DecidableEq Δ'] (h6 : 6 ≤ Fintype.card Δ') : IsEmpty (M ≃* alternatingGroup Δ') := by
  obtain ⟨n, i, e, hA⟩ := isNaturalSE_iff.mp hM
  exact ⟨fun φ => BenderType.not_mulEquiv_alternatingGroup hA.benderType h6 φ⟩

open scoped LinearAlgebra.Projectivization in
theorem isNaturalSE_alternatingGroup_five {Δ : Type*} [Fintype Δ] [DecidableEq Δ]
    (h5 : Fintype.card Δ = 5) : IsNaturalSE (alternatingGroup Δ) := by
  classical
  have hA := isBenderAction_projectiveLine (n := 2) le_rfl
  have := hA.finite
  have := hA.faithfulSMul
  let : Fintype (ℙ (GaloisField 2 2) (Fin 2 → GaloisField 2 2)) := Fintype.ofFinite _
  have hcardL : Fintype.card (ℙ (GaloisField 2 2) (Fin 2 → GaloisField 2 2)) =
      Fintype.card Δ := by
    rw [← Nat.card_eq_fintype_card, hA.card_eq, h5]
    norm_num
  set ψ : ℙ (GaloisField 2 2) (Fin 2 → GaloisField 2 2) ≃ Δ := Fintype.equivOfCardEq hcardL
  set ρ : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2) →* Equiv.Perm Δ :=
    (ψ.permCongrHom :
      Equiv.Perm (ℙ (GaloisField 2 2) (Fin 2 → GaloisField 2 2)) →* Equiv.Perm Δ).comp
      (MulAction.toPermHom (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)) _)
  have hρ_apply : ∀ g p, ρ g (ψ p) = ψ (g • p) := fun g p => by
    simp [ρ, Equiv.permCongr_apply]
  have hρ : Function.Injective ρ := by
    intro x y hxy
    refine eq_of_smul_eq_smul (α := ℙ (GaloisField 2 2) (Fin 2 → GaloisField 2 2)) fun p => ?_
    have h1 := congrArg (fun π : Equiv.Perm Δ => π (ψ p)) hxy
    simp only [hρ_apply] at h1
    exact ψ.injective h1
  have hM : IsNaturalSE ρ.range := isNaturalSE_iff.mpr ⟨2, 1, 1,
    hA.of_equiv (MonoidHom.ofInjective hρ) ψ fun g p => (hρ_apply g p).symm⟩
  have hcardP : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)) = 60 := by
    rw [hA.benderType.card_eq]
    norm_num
  have hidx : ρ.range.index = 2 := by
    have h1 := Subgroup.card_mul_index ρ.range
    rw [← Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv, hcardP, Nat.card_perm,
      Nat.card_eq_fintype_card, h5] at h1
    norm_num [Nat.factorial] at h1
    omega
  rwa [Equiv.Perm.eq_alternatingGroup_of_index_eq_two hidx] at hM

section Lemma17

variable {G : Type*} [Group G] [Finite G] {Q : Type*} [Group Q]

private theorem two_pow_sub_one_mul (n : ℕ) : (2 ^ n - 1) * (2 ^ n + 1) = 2 ^ (2 * n) - 1 := by
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  rw [pow_mul', sq]
  zify [h1, Nat.one_le_two_pow (n := n) |>.trans (Nat.le_mul_self _)]
  ring

private theorem unitary_cartan_order {n : ℕ} (hn : 2 ≤ n) :
    (2 ^ n - 1) * ((2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1)) = 2 ^ (2 * n) - 1 ∨
      (3 * ((2 ^ n - 1) * ((2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1))) = 2 ^ (2 * n) - 1 ∧
        6 ≤ 2 * n) := by
  have hg : Nat.gcd 3 (2 ^ n + 1) = 1 ∨ Nat.gcd 3 (2 ^ n + 1) = 3 :=
    (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_left _ _)
  rcases hg with hg | hg
  · left
    rw [hg, Nat.div_one, two_pow_sub_one_mul]
  · right
    have h3 : 3 ∣ 2 ^ n + 1 := hg ▸ Nat.gcd_dvd_right _ _
    refine ⟨?_, ?_⟩
    · rw [hg, ← two_pow_sub_one_mul, ← mul_assoc, mul_comm 3, mul_assoc, Nat.mul_div_cancel' h3]
    · by_contra hlt
      have hn2 : n = 2 := by omega
      subst hn2
      norm_num at h3

theorem lemma_1_7_of_benderType (π : G →* Q) (hπ : Function.Surjective π)
    (hSc : π.ker ≤ Subgroup.center G) (hS2 : IsPGroup 2 π.ker) {n i e : ℕ}
    (hQ : BenderType Q n i e) (hi : 2 ≤ i) (T : Sylow 2 G) {U : Subgroup G} (hUT : U ≤ T)
    (hUS : U ⊓ π.ker = ⊥)
    (hU : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (U : Set G))
    (hUZ : U.map π = rootCenter ((T : Subgroup G).map π)) :
    ∃ Gs : Subgroup G, Gs.Normal ∧ Gs ⊓ π.ker = ⊥ ∧ Gs ⊔ π.ker = ⊤ ∧ U ≤ Gs := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite Q := Finite.of_surjective π hπ
  set P : Sylow 2 Q := T.mapSurjective hπ
  have hP : (P : Subgroup Q) = (T : Subgroup G).map π := Sylow.coe_mapSurjective hπ T
  obtain ⟨t, hc⟩ := hQ.exists_benderCore P
  have hA : IsBenderAction Q (Q ⧸ borel (P : Subgroup Q)) n i e :=
    ⟨hQ, inferInstance, hc.index_eq⟩
  set α : Q ⧸ borel (P : Subgroup Q) := ((1 : Q) : Q ⧸ borel (P : Subgroup Q))
  have hPα : (P : Subgroup Q) ≤ stabilizer Q α := by
    rw [MulAction.stabilizer_quotient]
    exact le_borel _
  have htα : t • α ≠ α := fun h => hc.not_mem ((hA.mem_borel_iff hPα).mpr h)
  have hαβ : α ≠ t • α := htα.symm
  have hD := hA.stabilizer_inf_eq_cartan hPα hc.sq_eq_one rfl
  obtain ⟨-, -, -, hEA, hcardQZ⟩ := hQ.lemma_3_5_a hi P
  have hNk : 3 ≤ n * (i - 1) ∧ ((2 ^ n - 1) * e = 2 ^ (n * (i - 1)) - 1 ∨
      (3 * ((2 ^ n - 1) * e) = 2 ^ (n * (i - 1)) - 1 ∧ 6 ≤ n * (i - 1))) := by
    rcases hQ.cases' with ⟨hi1, -, -⟩ | ⟨hi2, he, a, ha, hna⟩ | ⟨hi3, he, hn⟩
    · omega
    · subst hi2 he hna
      exact ⟨by omega, Or.inl (by norm_num)⟩
    · subst hi3 he
      rw [show n * (3 - 1) = 2 * n by omega]
      exact ⟨by omega, unitary_cartan_order hn⟩
  obtain ⟨g, hg⟩ := hc.isCyclic.exists_generator
  have hgord : orderOf (g : Q) = (2 ^ n - 1) * e := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hc.card_cartan]
  obtain ⟨d, hd, hd1⟩ : ∃ d ∈ ⁅cartan (P : Subgroup Q) t, Subgroup.zpowers t⁆, d ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : ⁅cartan (P : Subgroup Q) t, Subgroup.zpowers t⁆ = ⊥ :=
      (Subgroup.eq_bot_iff_forall _).mpr hcon
    have h1 := hc.card_commutator_cartan
    rw [hbot, Subgroup.card_bot] at h1
    have := hA.four_le_q
    omega
  refine lemma_1_7_of_surjective π hπ hSc hS2 T hUT hUS hU hNk.1 hNk.2 ?_ ?_
    (gbar := (g : Q)) ?_ hgord ?_ (dbar := d) ?_ ?_
  ·
    intro x hx
    rw [← hP] at hx
    rw [hUZ, ← hP]
    have h1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hEA.exponent_dvd_p
      ((⟨x, hx⟩ : (P : Subgroup Q)) : (P : Subgroup Q) ⧸
        (rootCenter (P : Subgroup Q)).subgroupOf (P : Subgroup Q))
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    simpa using h1
  ·
    rw [hUZ, ← hP]
    change Nat.card (↥(P : Subgroup Q) ⧸
      (rootCenter (P : Subgroup Q)).subgroupOf (P : Subgroup Q)) = _
    rw [hcardQZ, ← pow_mul]
  · rw [← hP]
    exact cartan_le_borel _ _ g.2
  ·
    intro j x hx hmem
    rw [← hP] at hx
    rw [hUZ, ← hP] at hmem ⊢
    by_cases hj : (g : Q) ^ j = 1
    · exact Or.inr hj
    · left
      have hdj : (g : Q) ^ j ∈ stabilizer Q α ⊓ stabilizer Q (t • α) := by
        rw [hD]
        exact pow_mem g.2 j
      have hzc := (mem_rootCenter_iff.mp hmem).2 x hx
      have h1 : (g : Q) ^ j * x * ((g : Q) ^ j)⁻¹ * x⁻¹ =
          x⁻¹ * ((g : Q) ^ j * x * ((g : Q) ^ j)⁻¹) := by
        calc (g : Q) ^ j * x * ((g : Q) ^ j)⁻¹ * x⁻¹
            = x * (x⁻¹ * ((g : Q) ^ j * x * ((g : Q) ^ j)⁻¹)) * x⁻¹ := by group
          _ = x⁻¹ * ((g : Q) ^ j * x * ((g : Q) ^ j)⁻¹) * x * x⁻¹ := by rw [hzc]
          _ = x⁻¹ * ((g : Q) ^ j * x * ((g : Q) ^ j)⁻¹) := by group
      exact hA.mem_rootCenter_of_commutator_mem hPα hαβ hdj hj hx (h1 ▸ hmem)
  · rw [← hP]
    exact cartan_le_borel _ _ (hc.commutator_cartan_le hd)
  ·
    intro z hz hdz
    rw [hUZ, ← hP] at hz
    have hd' : d ∈ ⁅stabilizer Q α ⊓ stabilizer Q (t • α), Subgroup.zpowers t⁆ := by
      rw [hD]
      exact hd
    exact hA.eq_one_of_commute_of_mem_commutator hPα hαβ hc.sq_eq_one rfl hd' hd1
      (rootCenter_le _ hz) (by
        calc z * d = d * z * d⁻¹ * d := by rw [hdz]
          _ = d * z := by group)

end Lemma17

namespace IsBenderNormal

variable {K : Type*} [Group K] [Finite K] {Ω : Type*} [MulAction K Ω] {N : Subgroup K}
  {q i : ℕ}

theorem mem_of_orderOf_eq_two (h : IsBenderNormal Ω N q i) {x : K} (hx : orderOf x = 2) :
    x ∈ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact h.le_of_isPGroup (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one]))
    (Subgroup.mem_zpowers x)

theorem existsUnique_fixed (h : IsBenderNormal Ω N q i) {x : K} (hx : orderOf x = 2) :
    ∃! ω : Ω, x • ω = ω := by
  obtain ⟨n, e, -, hA⟩ := IsBenderNormal.isBenderAction h
  have hxN := mem_of_orderOf_eq_two h hx
  exact hA.existsUnique_fixed (x := ⟨x, hxN⟩) (by rw [Subgroup.orderOf_mk, hx])

theorem mem_longInv_iff (h : IsBenderNormal Ω N q i) {x : K} :
    x ∈ longInv K Ω ↔ orderOf x = 2 :=
  ⟨fun hx => hx.1, fun hx => ⟨hx, existsUnique_fixed h hx⟩⟩

end IsBenderNormal

end CFSG.Holt.H78
