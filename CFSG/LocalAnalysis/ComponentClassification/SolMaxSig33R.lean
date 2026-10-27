module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig33Q
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig35B
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig33P

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv
open scoped Pointwise

variable {X : Type} [Group X]

theorem exists_conj_mem_of_card_eq {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (hH : Nat.card H = 2 ^ (Nat.card G).factorization 2) {x : G}
    (hx : IsPGroup 2 (zpowers x)) : ∃ c : G, c * x * c⁻¹ ∈ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hxP⟩ := hx.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G P (Sylow.ofCard H hH)
  refine ⟨c, ?_⟩
  have h1 : MulAut.conj c • x ∈ MulAut.conj c • (P : Subgroup G) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ (hxP (mem_zpowers x))
  rw [← Sylow.coe_subgroup_smul, hc, Sylow.coe_ofCard] at h1
  simpa [MulAut.smul_def] using h1

theorem mem_centralizer_conj_iff {t c x : X} :
    x ∈ centralizer ({t} : Set X) ↔ c * x * c⁻¹ ∈ centralizer ({c * t * c⁻¹} : Set X) := by
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro hx
    calc c * x * c⁻¹ * (c * t * c⁻¹) = c * (x * t) * c⁻¹ := by group
      _ = c * (t * x) * c⁻¹ := by rw [hx]
      _ = c * t * c⁻¹ * (c * x * c⁻¹) := by group
  · intro hx
    have h1 : c * (x * t) * c⁻¹ = c * (t * x) * c⁻¹ := by
      calc c * (x * t) * c⁻¹ = c * x * c⁻¹ * (c * t * c⁻¹) := by group
        _ = c * t * c⁻¹ * (c * x * c⁻¹) := hx
        _ = c * (t * x) * c⁻¹ := by group
    simpa using h1

theorem isAltTwoComponent_conj [Finite X] {t : X} {J : Subgroup X} {n : ℕ}
    (h : SolAltLit.IsAltTwoComponent t J n) {c : X} (hc : c ∈ normalizer (J : Set X)) :
    SolAltLit.IsAltTwoComponent (c * t * c⁻¹) J n := by
  obtain ⟨ht, hJC, hJpc, hθ⟩ := h
  have hinv : ∀ x : X, c * (c⁻¹ * x * c) * c⁻¹ = x := fun x => by group
  let φ : ↥(centralizer ({t} : Set X)) ≃* ↥(centralizer ({c * t * c⁻¹} : Set X)) :=
    { toFun := fun x => ⟨c * x * c⁻¹, mem_centralizer_conj_iff.mp x.2⟩
      invFun := fun x => ⟨c⁻¹ * x * c, mem_centralizer_conj_iff.mpr (by rw [hinv]; exact x.2)⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  have hJC' : J ≤ centralizer ({c * t * c⁻¹} : Set X) := by
    intro x hx
    have h1 : c⁻¹ * x * c ∈ J := by
      have := (mem_normalizer_iff.mp (inv_mem hc) x).mp hx
      simpa using this
    have h2 := mem_centralizer_conj_iff (c := c).mp (hJC h1)
    rwa [hinv] at h2
  have hmap : (J.subgroupOf (centralizer ({t} : Set X))).map φ.toMonoidHom =
      J.subgroupOf (centralizer ({c * t * c⁻¹} : Set X)) := by
    ext x
    rw [mem_map, mem_subgroupOf]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [mem_subgroupOf] at hz
      exact (mem_normalizer_iff.mp hc z).mp hz
    · intro hx
      refine ⟨φ.symm x, ?_, φ.apply_symm_apply x⟩
      rw [mem_subgroupOf]
      change c⁻¹ * (x : X) * c ∈ J
      have := (mem_normalizer_iff.mp (inv_mem hc) x).mp hx
      simpa using this
  have hpc := ((LocalAnalysis.ComponentInitial.p_component_isomorphism_transport 2 Nat.prime_two
    φ).1 (J.subgroupOf (centralizer ({t} : Set X)))).mp hJpc
  rw [hmap] at hpc
  refine ⟨?_, hJC', hpc, hθ⟩
  change orderOf ((MulAut.conj c) t) = 2
  rw [MulEquiv.orderOf_eq]
  exact ht

theorem isSolomonPair_conj [Finite X] {t : X} {J : Subgroup X} {n : ℕ}
    (h : Sol78.IsSolomonPair t J n) {c : X} (hc : c ∈ normalizer (J : Set X)) :
    Sol78.IsSolomonPair (c * t * c⁻¹) J n := by
  obtain ⟨hJ, hodd, h9, hmax, hmax2, S, hSN, hS2, hScard, htS, hSC⟩ := h
  refine ⟨isAltTwoComponent_conj hJ hc, hodd, h9, hmax, hmax2,
    S.map (MulAut.conj c).toMonoidHom, ?_, hS2.map _, ?_, mem_map_of_mem _ htS, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact mul_mem (mul_mem hc (hSN hs)) (inv_mem hc)
  · rw [card_map_of_injective (MulAut.conj c).injective]
    exact hScard
  · rintro _ ⟨s, hs, rfl⟩
    exact mem_centralizer_conj_iff.mp (hSC hs)

theorem exists_isSolomonPair_commute [Finite X] {t : X} {J : Subgroup X} {n : ℕ}
    (h : Sol78.IsSolomonPair t J n) {y : X} (hyN : y ∈ normalizer (J : Set X))
    (hy2 : y * y = 1) : ∃ t' : X, Sol78.IsSolomonPair t' J n ∧ t' * y = y * t' := by
  obtain ⟨S, hSN, -, hScard, -, hSC⟩ := h.2.2.2.2.2
  set N := normalizer (J : Set X) with hNdef
  have hH : Nat.card ↥(S.subgroupOf N) = 2 ^ (Nat.card ↥N).factorization 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hSN).toEquiv]
    exact hScard
  have hx : IsPGroup 2 (zpowers (⟨y, hyN⟩ : ↥N)) :=
    isPGroup_zpowers_of_mul_self (Subtype.ext hy2)
  obtain ⟨c, hc⟩ := exists_conj_mem_of_card_eq hH hx
  rw [mem_subgroupOf] at hc
  have hcS : (c : X) * y * (c : X)⁻¹ ∈ S := by simpa using hc
  have h1 : (c : X) * y * (c : X)⁻¹ * t = t * ((c : X) * y * (c : X)⁻¹) :=
    mem_centralizer_singleton_iff.mp (hSC hcS)
  have hpair := isSolomonPair_conj h (inv_mem c.2)
  rw [inv_inv] at hpair
  refine ⟨(c : X)⁻¹ * t * c, hpair, ?_⟩
  calc (c : X)⁻¹ * t * c * y = (c : X)⁻¹ * (t * ((c : X) * y * (c : X)⁻¹)) * c := by group
    _ = (c : X)⁻¹ * ((c : X) * y * (c : X)⁻¹ * t) * c := by rw [h1]
    _ = y * ((c : X)⁻¹ * t * c) := by group

theorem balanceLemma_of_large (hbal : Sol78.BalanceTwoComponentInput)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion)
    [Finite X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) (hKP : Assembly.KProper Blueprint.Catalog X)
    (hunb : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hnU : ¬ OutcomeLocal.UOutcome X) {t : X} {J : Subgroup X} {n : ℕ}
    (hpair : Sol78.IsSolomonPair t J n) (hn : 13 ≤ n)
    (θ : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) {E : Subgroup X} (hEJ : E ≤ J)
    (hE : Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))
    {D : Finset (Fin n)} (hD : D.card = 4)
    (hsupp : ∀ x : J, (x : X) ∈ E → ∀ ω ∉ D,
      ((θ (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ω = ω)
    {y : X} (hy : orderOf y = 2) (hyE : y ∈ centralizer (E : Set X))
    (hyK : y ∈ UnbalancedLayer.coreActionKernel J) (hyJ : y ∉ J) {a b : X}
    (ha : a ∈ E ⊔ zpowers y) (ha1 : a ≠ 1) (hb : b ∈ E ⊔ zpowers y) (hb1 : b ≠ 1) :
    SolAltLit.thetaFunctor E a ⊓ centralizer ({b} : Set X) ≤ SolAltLit.thetaFunctor E b := by
  have hy2 : y * y = 1 := by rw [← sq, ← hy, pow_orderOf_eq_one]
  obtain ⟨t', hpair', hty⟩ := exists_isSolomonPair_commute hpair hyK.1 hy2
  have S : Sol33 X t' J n θ E D y :=
    { nonab := hnab
      kProper := hKP
      unbal := hunb
      notU := hnU
      pair := hpair'
      le := hEJ
      klein := hE
      card := hD
      supp := fun x hx hxE => support_coreImage_subset θ hsupp hx hxE
      hy := hy
      hyE := hyE
      hyK := hyK
      hyJ := hyJ
      hty := hty }
  have hdag : ∀ a' ∈ E ⊔ zpowers y, a' ≠ 1 → ∀ b' ∈ E ⊔ zpowers y, b' ≠ 1 →
      DaggerAt E a' b' := fun a' ha' ha'1 b' hb' hb'1 L hLC hLpc hLX =>
    S.dagger hbal (S.pumpOracle_of_large hbal hPump hN1 hn) ha' ha'1 hb' hb'1 hLC hLpc hLX
  have hEC : ∀ c ∈ E ⊔ zpowers y, E ≤ centralizer ({c} : Set X) := fun c hc x hx =>
    mem_centralizer_singleton_iff.mpr (S.comm_of_mem (mem_sup_left hx) hc)
  exact thetaFunctor_inf_le_of_dagger hbal hE (S.mul_self_of_mem ha) ha1
    (S.mul_self_of_mem hb) hb1 (S.comm_of_mem ha hb) (hEC a ha) (hEC b hb)
    (hdag a ha ha1 b hb hb1) fun e he he1 => hdag a ha ha1 e (mem_sup_left he) he1

end CFSG.ComponentClassification.SolMax
