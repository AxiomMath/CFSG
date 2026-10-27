module

public import CFSG.HardMathSupport.Malle.SeitzCube.LandingE7
public import CFSG.HardMathSupport.Malle.SeitzCube.LandingE6
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge


theorem exists_plane_cat_E7_of_twisted (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.E7 q).Valid) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : ∀ (K : Type) [Field K] [Finite K], Nat.card K = q.card → CharP K q.p →
      ∀ (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] (Fr : L →+* L),
        (∀ c, Fr c = c ^ q.card) → ∃ n ∈ adjointGroup Tag.E7 L, ∃ E R : Subgroup (ModGL Tag.E7 L),
          E ≤ twistFix Tag.E7 Fr n ∧ R ≤ twistFix Tag.E7 Fr n ∧ PlaneNormalizing p q.p E R) :
    ∃ E : Subgroup (MulAut (Cat ⟨TauCeti.LieTypeIndex.E7 q, hv⟩)), IsElemAbelian p E ∧
      Nat.card E = p ^ 2 ∧ InnerPlane ⟨TauCeti.LieTypeIndex.E7 q, hv⟩ p E ∧
        NormalizesRSubgroup ⟨TauCeti.LieTypeIndex.E7 q, hv⟩ E := by
  classical
  obtain ⟨K, _, _, hK, hKc, ⟨ε⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  let L := AlgebraicClosure K
  have : CharP L q.p := charP_of_injective_algebraMap (algebraMap K L).injective q.p
  let Fr : L →+* L := iterateFrobenius L q.p q.exponent
  have hFr : ∀ c, Fr c = c ^ q.card := fun c => by
    rw [TauCeti.PrimePower.card_def q]
    exact iterateFrobenius_def q.p q.exponent c
  have hFrK : ∀ c, Fr c = c ^ Nat.card K := fun c => by rw [hFr, hK]
  have hq : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  obtain ⟨n, hn, E, R, hET, hRT, hER⟩ := h K hK hKc L Fr hFr
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
  have hinj := conj_injective_cat_E7 q hv
  have hn' : ((E.map c).comap ι).map ε.symm.toMonoidHom ≤
      Subgroup.normalizer ((((R.map c).comap ι).map ε.symm.toMonoidHom : Subgroup _) : Set _) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hx' := hN x hx
    constructor
    · intro hy
      rw [← hx']
      exact ⟨y, hy, rfl⟩
    · intro hy
      rw [← hx'] at hy
      obtain ⟨z, hz, hzy⟩ := hy
      have : z = y := by
        have h := congrArg (fun t => x⁻¹ * t * x) hzy
        simpa [MulAut.conj_apply, mul_assoc] using h
      rwa [← this]
  obtain ⟨A, hA, hAc, hAin, hAN⟩ := exists_plane_of_subgroup hinj hE' hc' hn'
  refine ⟨A, hA, hAc, hAin, _, hR0, ?_, hAN⟩
  rw [TauCeti.LieTypeIndex.characteristic_E7]
  exact hRp

end CFSG.HardMathSupport.Malle.SeitzCube
