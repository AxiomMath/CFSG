module

public import CFSG.HardMathSupport.Malle.SeitzCube.Landing
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

section Comap

variable {G H : Type*} [Group G] [Group H] {p r : ℕ}

theorem CubeNormalizing.comap {E R : Subgroup G} (h : CubeNormalizing p r E R) (φ : H →* G)
    (hφ : Function.Injective φ) (hE : E ≤ φ.range) (hR : R ≤ φ.range) :
    CubeNormalizing p r (E.comap φ) (R.comap φ) := by
  obtain ⟨⟨hEc, hEp⟩, hc, hR0, hRp, hN⟩ := h
  have hmapE : (E.comap φ).map φ = E := Subgroup.map_comap_eq_self hE
  have hmapR : (R.comap φ).map φ = R := Subgroup.map_comap_eq_self hR
  refine ⟨⟨⟨⟨fun a b => Subtype.ext (hφ ?_)⟩⟩, fun x hx => hφ ?_⟩, ?_, ?_, ?_, fun x hx => ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact congrArg Subtype.val (hEc.is_comm.comm (⟨φ a, a.2⟩ : E) ⟨φ b, b.2⟩)
  · rw [map_pow, map_one]
    exact hEp _ hx
  · rw [← hc]
    conv_rhs => rw [← hmapE]
    exact (Subgroup.card_map_of_injective hφ).symm
  · intro hbot
    refine hR0 ?_
    rw [← hmapR, hbot, Subgroup.map_bot]
  · exact hRp.comap_of_injective φ hφ
  · refine le_antisymm ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      change φ (x * y * x⁻¹) ∈ R
      rw [map_mul, map_mul, map_inv, ← hN (φ x) hx]
      exact ⟨φ y, hy, rfl⟩
    · intro y hy
      have hy' : φ y ∈ R.map (MulAut.conj (φ x)).toMonoidHom := by rw [hN (φ x) hx]; exact hy
      obtain ⟨z, hz, hzy⟩ := hy'
      obtain ⟨z', rfl⟩ := hR hz
      refine ⟨z', hz, hφ ?_⟩
      change φ (x * z' * x⁻¹) = φ y
      rw [map_mul, map_mul, map_inv]
      exact hzy

end Comap

section E7


theorem mem_map_baseChange_of_frobenius_fixed_E7 {K L : Type} [Field K] [Finite K] [Field L]
    [Algebra K L] [IsAlgClosure K L] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {x : ModGL .E7 L} (hx : x ∈ adjointGroup .E7 L) (hxF : Units.map (entrywiseHom Fr) x = x)
    (hodd : Odd (Nat.card K) → Odd (orderOf x)) :
    x ∈ (adjointGroup .E7 K).map (baseChangeGL (algebraMap K L)) := by
  classical
  have : Algebra.IsAlgebraic K L := IsAlgClosure.isAlgebraic
  by_cases hK : Odd (Nat.card K)
  · obtain ⟨hfin, -, hidx⟩ := odd_E7_rational_derived_index_at_most_two K hK L Fr hFr
    set RF := adjointGroup Tag.E7 L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _)
      with hRF
    set H := (adjointGroup Tag.E7 K).map (baseChangeGL (algebraMap K L)) with hH
    have hxR : x ∈ RF := ⟨hx, hxF⟩
    have hsq : (⟨x, hxR⟩ : RF) ^ 2 ∈ H.subgroupOf RF := by
      have hpos : (H.subgroupOf RF).index ≠ 0 := Subgroup.index_ne_zero_of_finite
      rcases (by omega : (H.subgroupOf RF).index = 1 ∨ (H.subgroupOf RF).index = 2) with h1 | h2
      · rw [Subgroup.index_eq_one.1 h1]
        exact Subgroup.mem_top _
      · exact Subgroup.sq_mem_of_index_two h2 _
    have hsq' : x ^ 2 ∈ H := by
      rw [Subgroup.mem_subgroupOf] at hsq
      exact hsq
    obtain ⟨m, hm⟩ := hodd hK
    have hx' : x = (x ^ 2) ^ (m + 1) := by
      rw [← pow_mul, show 2 * (m + 1) = orderOf x + 1 by omega, pow_succ, pow_orderOf_eq_one,
        one_mul]
    rw [hx']
    exact pow_mem hsq' _
  · have : Fintype K := Fintype.ofFinite K
    obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
    have h2 : ringChar K = 2 := by
      by_contra hne
      refine hK ?_
      rw [Nat.card_eq_fintype_card, hf]
      exact (Nat.odd_pow_iff f.ne_zero).2 (hℓ.eq_two_or_odd'.resolve_left hne)
    obtain ⟨a, u, hu, rfl⟩ := exists_rootDiagUnit_mul_of_frobenius_fixed .E7 Fr hFr hx hxF
    exact mul_mem (Subgroup.mem_map_of_mem _
      (rootDiagUnit_mem_adjointGroup_E7_E8 (Or.inl rfl) h2 a)) hu

end E7

section Cat


theorem exists_cube_cat_E7_of_twisted (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.E7 q).Valid) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : ∀ (K : Type) [Field K] [Finite K], Nat.card K = q.card → CharP K q.p →
      ∀ (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] (Fr : L →+* L),
        (∀ c, Fr c = c ^ q.card) → TwistedCube .E7 L Fr p q.p) :
    ∃ E : Subgroup (Cat ⟨TauCeti.LieTypeIndex.E7 q, hv⟩), IsElemAbelian p E ∧
      Nat.card E = p ^ 3 ∧ NormalizesRSub ⟨TauCeti.LieTypeIndex.E7 q, hv⟩ E := by
  classical
  obtain ⟨K, _, _, hK, hKc, ⟨ε⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : Fintype K := Fintype.ofFinite K
  let L := AlgebraicClosure K
  have : CharP L q.p := charP_of_injective_algebraMap (algebraMap K L).injective q.p
  let Fr : L →+* L := iterateFrobenius L q.p q.exponent
  have hFr : ∀ c, Fr c = c ^ q.card := fun c => by
    rw [TauCeti.PrimePower.card_def q]
    exact iterateFrobenius_def q.p q.exponent c
  have hFrK : ∀ c, Fr c = c ^ Nat.card K := fun c => by rw [hFr, hK]
  obtain ⟨n, hn, E, R, hET, hRT, hER⟩ := h K hK hKc L Fr hFr
  have hq : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  obtain ⟨g0, hg0C, hg0⟩ := CFSG.RankThree.PartOne.KE.lang_conjugator_gen .E7 K
    (ℓ := q.p) (f := q.exponent) q.exponent_pos L n hn
  have hg0' : Units.map (entrywiseHom Fr) g0 = g0 * n := hg0
  let ι : ↥(adjointGroup .E7 K) →* ModGL .E7 L :=
    (baseChangeGL (algebraMap K L)).comp (adjointGroup .E7 K).subtype
  have hι : Function.Injective ι := (baseChangeGL_injective _).comp Subtype.val_injective
  have hrange : ι.range = (adjointGroup .E7 K).map (baseChangeGL (algebraMap K L)) := by
    change ((baseChangeGL (algebraMap K L)).comp (adjointGroup .E7 K).subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let c : ModGL .E7 L →* ModGL .E7 L := (MulAut.conj g0).toMonoidHom
  have hc : Function.Injective c := (MulAut.conj g0).injective
  have hland : ∀ x ∈ twistFix .E7 Fr n, (Odd (Nat.card K) → Odd (orderOf x)) → c x ∈ ι.range := by
    intro x hx hodd
    obtain ⟨hxC, hxF⟩ := hx
    have hxF' : n * Units.map (entrywiseHom Fr) x * n⁻¹ = x := hxF
    have hF : Units.map (entrywiseHom Fr) (g0 * x * g0⁻¹) = g0 * x * g0⁻¹ := by
      rw [map_mul, map_mul, map_inv, hg0']
      calc g0 * n * Units.map (entrywiseHom Fr) x * (g0 * n)⁻¹
          = g0 * (n * Units.map (entrywiseHom Fr) x * n⁻¹) * g0⁻¹ := by group
        _ = g0 * x * g0⁻¹ := by rw [hxF']
    rw [hrange]
    refine mem_map_baseChange_of_frobenius_fixed_E7 Fr hFrK
      (mul_mem (mul_mem hg0C hxC) (inv_mem hg0C)) hF fun hK' => ?_
    have : orderOf (c x) = orderOf x := MulEquiv.orderOf_eq (MulAut.conj g0) x
    rw [this]
    exact hodd hK'
  have hoddK : Odd (Nat.card K) → Odd q.p := fun h' => by
    rw [hK, hq] at h'
    exact (Nat.odd_pow_iff q.exponent_pos.ne').1 h'
  have hE : E.map c ≤ ι.range := by
    rintro _ ⟨x, hx, rfl⟩
    refine hland x (hET hx) fun _ => ?_
    have hdvd : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one (hER.1.2 x hx)
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
    · rw [h1]; exact odd_one
    · rw [h1]; exact hp.eq_two_or_odd'.resolve_left hp2
  have hR : R.map c ≤ ι.range := by
    rintro _ ⟨x, hx, rfl⟩
    refine hland x (hRT hx) fun hK' => ?_
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hER.2.2.2.1 ⟨x, hx⟩
    have hxo : orderOf x = q.p ^ k := by
      rw [← hk]
      exact (orderOf_submonoid (H := R.toSubmonoid) ⟨x, hx⟩)
    rw [hxo]
    exact (hoddK hK').pow
  have hφ : Function.Injective (ε.symm.toMonoidHom) := ε.symm.injective
  obtain ⟨hE', hc', hR0, hRp, hN⟩ := ((hER.map c hc).comap ι hι hE hR).map _ hφ
  refine ⟨_, hE', hc', _, hR0, ?_, hN⟩
  rw [TauCeti.LieTypeIndex.characteristic_E7]
  exact hRp

end Cat

end CFSG.HardMathSupport.Malle.SeitzCube
