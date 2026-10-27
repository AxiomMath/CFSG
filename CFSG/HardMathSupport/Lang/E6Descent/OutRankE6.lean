module

public import CFSG.LieType.Chevalley.OrdinaryEOuterOrder

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Abstract

theorem exists_ne_map_eq_of_plane {A H : Type*} [Group A] [Group H] {p : ℕ} (hp : p.Prime)
    (Θ : A →* H) [Finite {h : H // h ^ p = 1}] (hH : Nat.card {h : H // h ^ p = 1} ≤ p) (E : Subgroup A) [Finite E]
    (hE : ∀ x ∈ E, x ^ p = 1) (hEc : Nat.card E = p ^ 2) :
    ∃ a b : E, a ≠ b ∧ Θ (a : A) = Θ (b : A) := by
  classical
  have := Fintype.ofFinite E
  have := Fintype.ofFinite {h : H // h ^ p = 1}
  let φ : E → {h : H // h ^ p = 1} := fun e =>
    ⟨Θ (e : A), by rw [← map_pow, hE _ e.2, map_one]⟩
  have hlt : Fintype.card {h : H // h ^ p = 1} < Fintype.card E := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hEc]
    have := hp.two_le
    nlinarith
  obtain ⟨a, b, hab, h⟩ := Fintype.exists_ne_map_eq_of_card_lt φ hlt
  exact ⟨a, b, hab, congrArg Subtype.val h⟩

end Abstract

section Main


theorem mem_inner_of_mem_ker_E6 {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p)
    (Θ : MulAut (adjointGroup Tag.E6 K) →* RingAut K × Multiplicative (ZMod (exactE Tag.E6)))
    (hker : ∀ α : MulAut (adjointGroup Tag.E6 K), α ∈ Θ.ker ↔
      ∃ (g : adjointGroup Tag.E6 K) (a : Fin Tag.E6.rank → Kˣ), ∀ h : adjointGroup Tag.E6 K,
        (α h : ModGL Tag.E6 K) = (g : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 a * (h : ModGL Tag.E6 K) *
          (rootDiagUnit Tag.E6 a)⁻¹ * (g : ModGL Tag.E6 K)⁻¹)
    {x : MulAut (adjointGroup Tag.E6 K)} (hx : x ∈ Θ.ker) (hxp : x ^ p = 1) :
    x ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.E6 K) := by
  classical
  have : Finite (ModGL Tag.E6 K) := finite_modGL
  obtain ⟨Φ, -, hΦker, hcard⟩ := exists_outer_hom_E (K := K) (τ := Tag.E6) (Or.inl rfl)
  set o := QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
    (adjointGroup Tag.E6 K)) with ho
  have hmem : o x ∈ Φ.ker := by
    rw [hΦker]
    obtain ⟨g, a, h⟩ := (hker x).1 hx
    have hxe : x = MulAut.conj g * rootDiagAut Tag.E6 K a :=
      MulEquiv.ext fun y => Subtype.ext (by
        rw [h y, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
          coe_rootDiagAut, Subgroup.coe_inv]
        simp only [mul_assoc])
    refine ⟨a, ?_⟩
    change o (rootDiagAut Tag.E6 K a) = o x
    rw [hxe, map_mul]
    have : o (MulAut.conj g) = 1 := (QuotientGroup.eq_one_iff _).2 ⟨g, rfl⟩
    rw [this, one_mul]
  have h1 : orderOf (o x) ∣ p := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hxp, map_one])
  have h2 : orderOf (o x) ∣ 3 := by
    have h3 : orderOf (⟨o x, hmem⟩ : Φ.ker) ∣ Nat.card Φ.ker := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h3
    have hd : Tag.E6.cartan.det.natAbs = 3 := by rw [det_cartan_E6]; rfl
    exact h3.trans (hcard.trans (hd ▸ dvd_rfl))
  have h4 : orderOf (o x) ∣ Nat.gcd p 3 := Nat.dvd_gcd h1 h2
  rw [(Nat.coprime_primes hp Nat.prime_three).2 (by omega)] at h4
  have h5 : o x = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 h4)
  exact (QuotientGroup.eq_one_iff _).1 h5

theorem exists_inner_mem_of_plane_E6 {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (E : Subgroup (MulAut (adjointGroup Tag.E6 K))) [hE : IsElementaryAbelian p E]
    (hEc : Nat.card E = p ^ 2) :
    ∃ g : adjointGroup Tag.E6 K, g ≠ 1 ∧ MulAut.conj g ∈ E := by
  classical
  have : Finite (ModGL Tag.E6 K) := finite_modGL
  have : Finite (adjointGroup Tag.E6 K) := Subtype.finite
  obtain ⟨Θ, -, -, hker, -⟩ := ordinary_E_field_graph_quotient_and_involutions Tag.E6 (Or.inl rfl) K
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  obtain ⟨-, hcyc⟩ := CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hℓ K hK
  have : Finite (RingAut K) := Finite.of_injective (fun σ : RingAut K => (σ : K → K))
    DFunLike.coe_injective
  have hε2 : ∀ e : Multiplicative (ZMod 2), e ^ 2 = 1 := by decide
  have : Finite (Multiplicative (ZMod (exactE Tag.E6))) := by
    change Finite (Multiplicative (ZMod 2))
    infer_instance
  have hε : ∀ e : Multiplicative (ZMod (exactE Tag.E6)), e ^ p = 1 → e = 1 := by
    intro e hep
    have h2 : orderOf e ∣ Nat.gcd p 2 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hep) (orderOf_dvd_of_pow_eq_one (hε2 e))
    rw [(Nat.coprime_primes hp Nat.prime_two).2 (by omega)] at h2
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h2)
  have hH : Nat.card {h : RingAut K × Multiplicative (ZMod (exactE Tag.E6)) // h ^ p = 1} ≤ p := by
    have := Fintype.ofFinite (RingAut K)
    have hinj : Function.Injective
        (fun h : {h : RingAut K × Multiplicative (ZMod (exactE Tag.E6)) // h ^ p = 1} =>
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
  have : Finite {h : RingAut K × Multiplicative (ZMod (exactE Tag.E6)) // h ^ p = 1} :=
    Finite.of_injective Subtype.val Subtype.val_injective
  obtain ⟨a, b, hab, hΘ⟩ := exists_ne_map_eq_of_plane hp Θ hH E
    (fun x hx => elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) x hx) hEc
  have hxE : (a : MulAut (adjointGroup Tag.E6 K))⁻¹ * (b : MulAut (adjointGroup Tag.E6 K)) ∈ E :=
    E.mul_mem (E.inv_mem a.2) b.2
  have hxker : (a : MulAut (adjointGroup Tag.E6 K))⁻¹ * (b : MulAut (adjointGroup Tag.E6 K)) ∈
      Θ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hΘ, inv_mul_cancel]
  have hxp := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) _ hxE
  obtain ⟨g, hg⟩ := mem_inner_of_mem_ker_E6 hp hp3 Θ hker hxker hxp
  refine ⟨g, ?_, ?_⟩
  · rintro rfl
    rw [map_one] at hg
    apply hab
    have h1 : (a : MulAut (adjointGroup Tag.E6 K)) = b := by
      have := congrArg (fun z => (a : MulAut (adjointGroup Tag.E6 K)) * z) hg
      simpa using this
    exact Subtype.ext h1
  · rw [hg]
    exact hxE

end Main

end CFSG.HardMathSupport.Lang.E6Descent
