module

public import CFSG.LieType.SeitzGeneration.UnitaryNonabPlane
public import CFSG.LieType.SeitzGeneration.HeisTorusUGen

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.Open CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.RankThree.PartOne.KCUnitaryModel

variable {ℓ f n p : ℕ} {K : Type} [Field K]

theorem planeGen_isPrimitiveRoot {c : K} {p : ℕ} (hp : p.Prime) (hcp : c ^ p = 1) (hc1 : c ≠ 1) :
    IsPrimitiveRoot c p := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [← orderOf_eq_prime hcp hc1]
  exact IsPrimitiveRoot.orderOf c

theorem planeGen_heis_scalar_one (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hp2 : p ≠ 2)
    {x y : GL (Fin p) K} (hx : x ∈ unitarySU ℓ f K p) (hy : y ∈ unitarySU ℓ f K p) {α β c : K}
    (hcpow : c ^ p = 1) (hc1 : c ≠ 1)
    (hx3 : ((x ^ p : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) = α • 1)
    (hy3 : ((y ^ p : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) = β • 1)
    (hc : (y : Matrix (Fin p) (Fin p) K) * (x : Matrix (Fin p) (Fin p) K) =
      c • ((x : Matrix (Fin p) (Fin p) K) * (y : Matrix (Fin p) (Fin p) K))) :
    α = 1 ∧ β = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hcpow
    exact zero_ne_one hcpow
  have hζ := planeGen_isPrimitiveRoot hp hcpow hc1
  have hcinv : (x : Matrix (Fin p) (Fin p) K) * (y : Matrix (Fin p) (Fin p) K) =
      c⁻¹ • ((y : Matrix (Fin p) (Fin p) K) * (x : Matrix (Fin p) (Fin p) K)) := by
    rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hζ' := planeGen_isPrimitiveRoot hp (by rw [inv_pow, hcpow, inv_one]) (inv_ne_one.2 hc1)
  have e1 := det_eq_scalar_of_heis hp hp2 hζ hx3 hc
  have e2 := det_eq_scalar_of_heis hp hp2 hζ' hy3 hcinv
  have hdx := ((mem_unitarySU_iff h).1 hx).1
  have hdy := ((mem_unitarySU_iff h).1 hy).1
  exact ⟨by rw [← e1, hdx], by rw [← e2, hdy]⟩

theorem closure_centralizers_statedProj_su_p
    (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ ℓ ^ f + 1)
    (hn : 3 ≤ n) (E : Subgroup (StatedProj (StatedSU n (ℓ ^ f) K)))
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hexp : ∀ a ∈ E, a ^ p = 1)
    (hcard : Nat.card E = p ^ 2) :
    Subgroup.closure {k : StatedProj (StatedSU n (ℓ ^ f) K) |
      ∃ z ∈ E, z ≠ 1 ∧ k * z = z * k} = ⊤ := by
  classical
  haveI := h.finite
  haveI : Fact ℓ.Prime := ⟨h.prime⟩
  haveI : CharP K ℓ := h.charP
  haveI : Fact p.Prime := ⟨hp⟩
  have hn0 : 0 < n := by omega
  have hp2 : p ≠ 2 := by omega
  have hT : TorusFourierGenU h p := torusFourierGenU_of_prime h hp5 hpq
  obtain ⟨x, y, hxE, hyE, hy1, hxy, α, β, c, hα, hβ, hx3, hy3, hc⟩ :=
    exists_psu_lift_pair_p h hp hn0 E hcomm hexp hcard
  have hxG : (x : GL (Fin n) K) ∈ primeFormUnitary h (idGram K n) :=
    CFSG.RankThree.PartOne.KFU.unitarySU_le_primeFormUnitary h x.2
  have hyG : (y : GL (Fin n) K) ∈ primeFormUnitary h (idGram K n) :=
    CFSG.RankThree.PartOne.KFU.unitarySU_le_primeFormUnitary h y.2
  have hxp : piSUn ℓ f n K x ^ p = 1 := by rw [← map_pow]; exact hexp _ hxE
  have hyp : piSUn ℓ f n K y ^ p = 1 := by rw [← map_pow]; exact hexp _ hyE
  have hind : ∀ a b : ℕ,
      (∃ c' : K, (((x : GL (Fin n) K) ^ a * (y : GL (Fin n) K) ^ b : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = c' • 1) → p ∣ a ∧ p ∣ b := by
    rintro a b ⟨c', hc'⟩
    exact dvd_of_scalar_pow_mul_pow_p hp hn0 hxp hyp hy1 hxy hc'
  have hcpow : c ^ p = 1 := pow_eq_one_of_smul_comm_p hn0 hα hx3 hc
  have hexcl : n = p → c ≠ 1 → (∃ μ : K, μ ^ p = α) ∧ ∃ ν : K, ν ^ p = β := by
    intro hnp hc1
    subst hnp
    obtain ⟨h1, h2⟩ := planeGen_heis_scalar_one h hp hp2 x.2 y.2 hcpow hc1 hx3 hy3 hc
    exact ⟨⟨1, by rw [one_pow, h1]⟩, ⟨1, by rw [one_pow, h2]⟩⟩
  have hgen := closure_planeFixUnW_gu h hT hp hp5 hpq hn hxG hyG hα hβ hx3 hy3 hc hind hexcl
  have hS : ∀ g ∈ planeFixUnW ℓ f n p K (x : GL (Fin n) K) (y : GL (Fin n) K),
      ∃ z ∈ E, z ≠ 1 ∧ piSUn ℓ f n K g * z = z * piSUn ℓ f n K g := by
    rintro g ⟨a, b, hab, c', hg⟩
    obtain ⟨w, hwdef⟩ : ∃ w : unitarySU ℓ f K n, w = x ^ a * y ^ b := ⟨_, rfl⟩
    have hw : ((w : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (((x : GL (Fin n) K) ^ a * (y : GL (Fin n) K) ^ b : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) := by
      rw [hwdef]
      simp
    refine ⟨piSUn ℓ f n K w, ?_, ?_, ?_⟩
    · rw [hwdef, map_mul, map_pow, map_pow]
      exact E.mul_mem (E.pow_mem hxE a) (E.pow_mem hyE b)
    · intro h1
      obtain ⟨u, hu⟩ := exists_smul_of_piSUn_eq (a := w) (b := 1) (by rw [map_one]; exact h1)
      apply hab
      apply dvd_of_scalar_pow_mul_pow_p hp hn0 hxp hyp hy1 hxy (c := u)
      rw [← hw]
      simpa using hu
    · exact piSUn_commute_of_smul h hn0 g w c' (by rw [hw]; exact hg)
  exact closure_centralizers_of_forall E _ hS hgen

theorem planeGen_inner_unitary_nonab_p {m : ℕ}
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedA m q).Valid) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hlift : p ∣ q.card + 1 ∧ p ∣ m + 1)
    {E : Subgroup (MulAut (Cat ⟨.twistedA m q, hv⟩))} (hE : IsElemAbelian p E)
    (hc : Nat.card E = p ^ 2) (hinner : InnerPlane ⟨.twistedA m q, hv⟩ p E) : PlaneGen E := by
  have : Fact p.Prime := ⟨hp⟩
  refine planeGen_inner_unitary_of_model hv hp ?_ hE hc hinner
  intro E₁ hE₁ hcard₁
  have hU := CFSG.RankThree.PartTwo.Census.unitaryFieldData_galoisField
    (TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA m q, hv⟩)
    (TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA m q, hv⟩)
    (TauCeti.ValidLieTypeIndex.fieldExponent_pos ⟨.twistedA m q, hv⟩)
  have hqcard : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA m q, hv⟩ ^
      TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA m q, hv⟩ = q.card := by
    simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent,
      TauCeti.PrimePower.card_def]
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hm2 : 2 ≤ m := hrange.1
  have hcomm : ∀ a ∈ E₁, ∀ b ∈ E₁, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE₁.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  exact closure_centralizers_statedProj_su_p hU hp hp5 (by rw [hqcard]; exact hlift.1)
    (by omega) E₁ hcomm hE₁.2 hcard₁

end CFSG.LieType.SeitzGeneration
