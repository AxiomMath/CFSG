module

public import CFSG.HardMathSupport.Lang.E6Descent.OutRankE6

open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.E6Descent
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

public section

namespace CFSG.LieType.SeitzGeneration.ExcOuterLeOne


theorem not_dvd_det_cartan_E {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) : ¬ p ∣ τ.cartan.det.natAbs := by
  rcases hτ with rfl | rfl | rfl
  · rw [det_cartan_E6]
    intro h
    have := Nat.le_of_dvd (by norm_num) h
    omega
  · rw [det_cartan_E7]
    intro h
    have := Nat.le_of_dvd (by norm_num) h
    omega
  · rw [det_cartan_E8]
    intro h
    have := Nat.le_of_dvd (by norm_num) h
    omega

theorem not_dvd_det_cartan_E_of_odd {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : ¬ p ∣ τ.cartan.det.natAbs := by
  have h2 := hp.two_le
  rcases hτ with rfl | rfl
  · rw [det_cartan_E7]
    intro h
    have := Nat.le_of_dvd (by norm_num) h
    omega
  · rw [det_cartan_E8]
    intro h
    have := Nat.le_of_dvd (by norm_num) h
    omega

theorem mem_inner_of_mem_ker_E (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K]
    [Finite K] {p : ℕ} (hp : p.Prime) (hdet : ¬ p ∣ τ.cartan.det.natAbs)
    (Θ : MulAut (adjointGroup τ K) →* RingAut K × Multiplicative (ZMod (exactE τ)))
    (hker : ∀ α : MulAut (adjointGroup τ K), α ∈ Θ.ker ↔
      ∃ (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ), ∀ h : adjointGroup τ K,
        (α h : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a * (h : ModGL τ K) *
          (rootDiagUnit τ a)⁻¹ * (g : ModGL τ K)⁻¹)
    {x : MulAut (adjointGroup τ K)} (hx : x ∈ Θ.ker) (hxp : x ^ p = 1) :
    x ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup τ K) := by
  classical
  have : Finite (ModGL τ K) := finite_modGL
  obtain ⟨Φ, -, hΦker, hcard⟩ := exists_outer_hom_E (K := K) (τ := τ) hτ
  set o := QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
    (adjointGroup τ K)) with ho
  have hmem : o x ∈ Φ.ker := by
    rw [hΦker]
    obtain ⟨g, a, h⟩ := (hker x).1 hx
    have hxe : x = MulAut.conj g * rootDiagAut τ K a :=
      MulEquiv.ext fun y => Subtype.ext (by
        rw [h y, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
          coe_rootDiagAut, Subgroup.coe_inv]
        simp only [mul_assoc])
    refine ⟨a, ?_⟩
    change o (rootDiagAut τ K a) = o x
    rw [hxe, map_mul]
    have : o (MulAut.conj g) = 1 := (QuotientGroup.eq_one_iff _).2 ⟨g, rfl⟩
    rw [this, one_mul]
  have h1 : orderOf (o x) ∣ p := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hxp, map_one])
  have h2 : orderOf (o x) ∣ τ.cartan.det.natAbs := by
    have h3 : orderOf (⟨o x, hmem⟩ : Φ.ker) ∣ Nat.card Φ.ker := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h3
    exact h3.trans hcard
  have h4 : orderOf (o x) ∣ Nat.gcd p τ.cartan.det.natAbs := Nat.dvd_gcd h1 h2
  rw [((Nat.Prime.coprime_iff_not_dvd hp).2 hdet)] at h4
  have h5 : o x = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 h4)
  exact (QuotientGroup.eq_one_iff _).1 h5

theorem exactE_facts (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    Finite (Multiplicative (ZMod (exactE τ))) ∧
      ∀ e : Multiplicative (ZMod (exactE τ)), e ^ 2 = 1 := by
  rcases hτ with rfl | rfl | rfl
  · refine ⟨by change Finite (Multiplicative (ZMod 2)); infer_instance, ?_⟩
    change ∀ e : Multiplicative (ZMod 2), e ^ 2 = 1
    decide
  · refine ⟨by change Finite (Multiplicative (ZMod 1)); infer_instance, ?_⟩
    change ∀ e : Multiplicative (ZMod 1), e ^ 2 = 1
    decide
  · refine ⟨by change Finite (Multiplicative (ZMod 1)); infer_instance, ?_⟩
    change ∀ e : Multiplicative (ZMod 1), e ^ 2 = 1
    decide

theorem exists_inner_mem_of_plane_E_of_odd (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type}
    [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdet : ¬ p ∣ τ.cartan.det.natAbs)
    (E : Subgroup (MulAut ↥(adjointGroup τ K))) [hE : CFSG.IsElementaryAbelian p ↥E]
    (hEc : Nat.card ↥E = p ^ 2) : ∃ g : ↥(adjointGroup τ K), g ≠ 1 ∧ MulAut.conj g ∈ E := by
  classical
  have : Finite (ModGL τ K) := finite_modGL
  have : Finite (adjointGroup τ K) := Subtype.finite
  obtain ⟨Θ, -, -, hker, -⟩ := ordinary_E_field_graph_quotient_and_involutions τ hτ K
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  obtain ⟨-, hcyc⟩ := CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hℓ K hK
  have : Finite (RingAut K) := Finite.of_injective (fun σ : RingAut K => (σ : K → K))
    DFunLike.coe_injective
  obtain ⟨hfin, hε2⟩ := exactE_facts τ hτ
  have : Finite (Multiplicative (ZMod (exactE τ))) := hfin
  have hε : ∀ e : Multiplicative (ZMod (exactE τ)), e ^ p = 1 → e = 1 := by
    intro e hep
    have h2 : orderOf e ∣ Nat.gcd p 2 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hep) (orderOf_dvd_of_pow_eq_one (hε2 e))
    rw [(Nat.coprime_primes hp Nat.prime_two).2 hp2] at h2
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h2)
  have hH : Nat.card {h : RingAut K × Multiplicative (ZMod (exactE τ)) // h ^ p = 1} ≤ p := by
    have := Fintype.ofFinite (RingAut K)
    have hinj : Function.Injective
        (fun h : {h : RingAut K × Multiplicative (ZMod (exactE τ)) // h ^ p = 1} =>
          (⟨h.1.1, by
            have := congrArg Prod.fst h.2
            simpa using this⟩ : {σ : RingAut K // σ ^ p = 1})) := by
      intro h h' hh
      have h1 : h.1.1 = h'.1.1 := congrArg Subtype.val hh
      have e2 := hε h.1.2 (by have := congrArg Prod.snd h.2; simpa using this)
      have e2' := hε h'.1.2 (by have := congrArg Prod.snd h'.2; simpa using this)
      exact Subtype.ext (Prod.ext h1 (e2.trans e2'.symm))
    refine (Nat.card_le_card_of_injective _ hinj).trans ?_
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact IsCyclic.card_pow_eq_one_le hp.pos
  have : Finite {h : RingAut K × Multiplicative (ZMod (exactE τ)) // h ^ p = 1} :=
    Finite.of_injective Subtype.val Subtype.val_injective
  obtain ⟨a, b, hab, hΘ⟩ := exists_ne_map_eq_of_plane hp Θ hH E
    (fun x hx => elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) x hx) hEc
  have hxE : (a : MulAut (adjointGroup τ K))⁻¹ * (b : MulAut (adjointGroup τ K)) ∈ E :=
    E.mul_mem (E.inv_mem a.2) b.2
  have hxker : (a : MulAut (adjointGroup τ K))⁻¹ * (b : MulAut (adjointGroup τ K)) ∈
      Θ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hΘ, inv_mul_cancel]
  have hxp := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) _ hxE
  obtain ⟨g, hg⟩ := mem_inner_of_mem_ker_E τ hτ hp hdet Θ hker hxker hxp
  refine ⟨g, ?_, ?_⟩
  · rintro rfl
    rw [map_one] at hg
    apply hab
    have h1 : (a : MulAut (adjointGroup τ K)) = b := by
      have := congrArg (fun z => (a : MulAut (adjointGroup τ K)) * z) hg
      simpa using this
    exact Subtype.ext h1
  · rw [hg]
    exact hxE

theorem exists_inner_mem_of_plane_E (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type}
    [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (E : Subgroup (MulAut ↥(adjointGroup τ K))) [hE : CFSG.IsElementaryAbelian p ↥E]
    (hEc : Nat.card ↥E = p ^ 2) : ∃ g : ↥(adjointGroup τ K), g ≠ 1 ∧ MulAut.conj g ∈ E :=
  exists_inner_mem_of_plane_E_of_odd τ hτ hp (by omega) (not_dvd_det_cartan_E hτ hp hp3) E hEc

end CFSG.LieType.SeitzGeneration.ExcOuterLeOne
