module

public import CFSG.HardMathSupport.Solomon.Coordinator.WeakModel

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo Matrix
  Subgroup

@[expose] def HeisUpper (p : ℕ) (S : Type*) [Group S] (R : Subgroup (MulAut S)) : Prop :=
  ∀ D : Subgroup (MulAut S), IsElemAbelian p D → Nat.card D = p ^ 2 →
    ∀ H : Subgroup (MulAut S), innerAut S ≤ H → D ≤ normalizer (H : Set (MulAut S)) →
      localDeltaIn p H D ≠ ⊥ → ∀ A : Subgroup (MulAut S), D ≤ A → IsElemAbelian p A →
        Nat.card A ≤ p ^ 3 ∧ ∀ z ∈ A, z ∈ R → z ∈ D

section Model

variable {p : ℕ} {S : Type*} [Group S] [Finite S] {K : Type*} [Field K] {M : Type*} [Group M]

omit [Finite S] in
open CFSG.HardMathSupport.Timmesfeld.LocalTwo.HeisP in
theorem inter_range_le_of_model (hp : p.Prime) (hpK : (p : K) ≠ 0)
    (ι : M →* GL (Fin p) K) (hι : Function.Injective ι) (ρ : M →* MulAut S)
    (hker : ∀ g : M, ρ g = 1 → ∃ c : Kˣ, ι g = GeneralLinearGroup.scalar (Fin p) c)
    (hscalar : ∀ (g : M) (c : Kˣ), ι g = GeneralLinearGroup.scalar (Fin p) c → ρ g = 1)
    (hplane : ∀ A B : M, A * B = B * A → ρ A ^ p = 1 → ρ B ^ p = 1 → ρ A ≠ 1 →
      ρ B ∉ zpowers (ρ A) → ∀ H : Subgroup (MulAut S), innerAut S ≤ H →
        closure {ρ A, ρ B} ≤ normalizer (H : Set (MulAut S)) →
          localDeltaIn p H (closure {ρ A, ρ B}) = ⊥)
    (houter : ∀ D : Subgroup (MulAut S), IsElemAbelian p D → ¬ D ≤ ρ.range →
      ∀ H : Subgroup (MulAut S), innerAut S ≤ H → localDeltaIn p H D = ⊥)
    {D : Subgroup (MulAut S)} (hD : IsElemAbelian p D) (hcard : Nat.card D = p ^ 2)
    {H : Subgroup (MulAut S)} (hH : innerAut S ≤ H) (hDH : D ≤ normalizer (H : Set (MulAut S)))
    (hΔ : localDeltaIn p H D ≠ ⊥) {A : Subgroup (MulAut S)} (hDA : D ≤ A)
    (hA : IsElemAbelian p A) : ∀ z ∈ A, z ∈ ρ.range → z ∈ D := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hDr : D ≤ ρ.range := by
    by_contra h
    exact hΔ (houter D hD h H hH)
  obtain ⟨x, hx, y, hy, hx1, hyx, hgen⟩ := exists_gen_pair hp hD hcard
  obtain ⟨A0, rfl⟩ := MonoidHom.mem_range.1 (hDr hx)
  obtain ⟨B0, rfl⟩ := MonoidHom.mem_range.1 (hDr hy)
  have hxy : ρ A0 * ρ B0 = ρ B0 * ρ A0 :=
    congrArg Subtype.val (hD.1.is_comm.comm ⟨_, hx⟩ ⟨_, hy⟩)
  obtain ⟨z, hz⟩ := hker (A0 * B0 * A0⁻¹ * B0⁻¹) (by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hxy]; group)
  simp only [map_mul, map_inv] at hz
  by_cases hz1 : z = 1
  · exfalso
    apply hΔ
    have hAB : A0 * B0 = B0 * A0 := by
      apply hι
      rw [hz1, map_one, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hz
      rw [map_mul, map_mul]
      exact hz
    rw [← hgen]
    exact hplane A0 B0 hAB (hD.2 _ hx) (hD.2 _ hy) hx1 hyx H hH (hgen ▸ hDH)
  have hpow : ∀ X : M, ρ X ^ p = 1 →
      ∃ a0 : Kˣ, ι X ^ p = GeneralLinearGroup.scalar (Fin p) a0 := by
    intro X hX
    obtain ⟨a0, ha0⟩ := hker (X ^ p) (by rw [map_pow, hX])
    exact ⟨a0, by rw [← map_pow]; exact ha0⟩
  obtain ⟨a0, ha0⟩ := hpow A0 (hD.2 _ hx)
  obtain ⟨b0, hb0⟩ := hpow B0 (hD.2 _ hy)
  have hzp : z ^ p = 1 := by
    have := pow_eq_one_of_conj ha0 (rel_BA hz)
    rwa [inv_pow, inv_eq_one] at this
  have hω : IsPrimitiveRoot z p := by
    have := orderOf_eq_prime hzp hz1
    rw [← this]
    exact IsPrimitiveRoot.orderOf z
  intro w hwA hwr
  obtain ⟨C0, rfl⟩ := MonoidHom.mem_range.1 hwr
  have hCA : ρ C0 * ρ A0 = ρ A0 * ρ C0 :=
    congrArg Subtype.val (hA.1.is_comm.comm ⟨_, hwA⟩ ⟨_, hDA hx⟩)
  have hCB : ρ C0 * ρ B0 = ρ B0 * ρ C0 :=
    congrArg Subtype.val (hA.1.is_comm.comm ⟨_, hwA⟩ ⟨_, hDA hy⟩)
  obtain ⟨α, hα⟩ := hker (C0 * A0 * C0⁻¹ * A0⁻¹) (by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hCA]; group)
  obtain ⟨β, hβ⟩ := hker (C0 * B0 * C0⁻¹ * B0⁻¹) (by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hCB]; group)
  simp only [map_mul, map_inv] at hα hβ
  have hCA' := rel_AB hα
  have hCB' := rel_AB hβ
  obtain ⟨i, j, m, hm⟩ := heisenberg_normalizer_p hω hz hpK (pow_eq_one_of_conj ha0 hCA')
    (pow_eq_one_of_conj hb0 hCB') hCA' hCB'
  have hm0 : ρ ((A0 ^ i * B0 ^ j)⁻¹ * C0) = 1 := by
    refine hscalar _ m ?_
    rw [map_mul, map_inv, map_mul, map_pow, map_pow, hm, inv_mul_cancel_left]
  have hC0 : C0 = (A0 ^ i * B0 ^ j) * ((A0 ^ i * B0 ^ j)⁻¹ * C0) := by group
  rw [hC0, map_mul, hm0, mul_one, map_mul, map_pow, map_pow]
  exact mul_mem (pow_mem hx i) (pow_mem hy j)

theorem heisUpper_of_model (hp : p.Prime) (hpK : (p : K) ≠ 0)
    (ι : M →* GL (Fin p) K) (hι : Function.Injective ι) (ρ : M →* MulAut S)
    (hker : ∀ g : M, ρ g = 1 → ∃ c : Kˣ, ι g = GeneralLinearGroup.scalar (Fin p) c)
    (hscalar : ∀ (g : M) (c : Kˣ), ι g = GeneralLinearGroup.scalar (Fin p) c → ρ g = 1)
    (hplane : ∀ A B : M, A * B = B * A → ρ A ^ p = 1 → ρ B ^ p = 1 → ρ A ≠ 1 →
      ρ B ∉ zpowers (ρ A) → ∀ H : Subgroup (MulAut S), innerAut S ≤ H →
        closure {ρ A, ρ B} ≤ normalizer (H : Set (MulAut S)) →
          localDeltaIn p H (closure {ρ A, ρ B}) = ⊥)
    (houter : ∀ D : Subgroup (MulAut S), IsElemAbelian p D → ¬ D ≤ ρ.range →
      ∀ H : Subgroup (MulAut S), innerAut S ≤ H → localDeltaIn p H D = ⊥)
    (hcyc : ∀ A : Subgroup (MulAut S), IsElemAbelian p A →
      ∃ (C : Type) (_ : Group C) (_ : IsCyclic C) (α : A →* C),
        ∀ x : A, α x = 1 → (x : MulAut S) ∈ ρ.range) :
    HeisUpper p S ρ.range := by
  classical
  intro D hD hcard H hH hDH hΔ A hDA hA
  have hmem := inter_range_le_of_model hp hpK ι hι ρ hker hscalar hplane houter hD hcard hH hDH hΔ
    hDA hA
  refine ⟨?_, hmem⟩
  obtain ⟨Cc, _, _, α, hα⟩ := hcyc A hA
  have hle := card_le_mul_card_ker' hp (fun h : A => Subtype.ext (hA.2 h h.2)) α
  have hkerD : Nat.card α.ker ≤ Nat.card D := by
    refine Nat.card_le_card_of_injective
      (fun k => (⟨(k.1 : MulAut S), hmem _ k.1.2 (hα k.1 k.2)⟩ : D)) ?_
    intro k1 k2 h
    have h' : ((k1 : A) : MulAut S) = ((k2 : A) : MulAut S) :=
      congrArg (fun d : D => (d : MulAut S)) h
    exact Subtype.ext (Subtype.ext h')
  calc Nat.card A ≤ p * Nat.card α.ker := hle
    _ ≤ p * p ^ 2 := by
        apply Nat.mul_le_mul_left
        rw [← hcard]; exact hkerD
    _ = p ^ 3 := by ring

end Model

section Transport

variable {p : ℕ} {S S' : Type*} [Group S] [Group S']

theorem HeisUpper.of_injective {R' : Subgroup (MulAut S')} (ψ : MulAut S →* MulAut S')
    (hψ : Function.Injective ψ) (hinn : innerAut S' ≤ (innerAut S).map ψ)
    (h : HeisUpper p S' R') : HeisUpper p S (R'.comap ψ) := by
  intro D hD hcard H hH hDH hΔ A hDA hA
  have hel : ∀ E : Subgroup (MulAut S), IsElemAbelian p E → IsElemAbelian p (E.map ψ) := by
    intro E hE
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
      obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
      apply Subtype.ext
      change ψ x * ψ y = ψ y * ψ x
      have := congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      rw [← map_mul, ← map_mul]
      exact congrArg ψ this
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hE.2 x hx, map_one]
  have hH' : innerAut S' ≤ H.map ψ := hinn.trans (map_mono hH)
  have hDH' : D.map ψ ≤ normalizer ((H.map ψ : Subgroup (MulAut S')) : Set (MulAut S')) :=
    (map_mono hDH).trans (le_normalizer_map ψ)
  have hΔ' : localDeltaIn p (H.map ψ) (D.map ψ) ≠ ⊥ := by
    intro h0
    have hle := CFSG.HardMathSupport.Timmesfeld.Coordinator.map_localDeltaIn_le p ψ hψ H D
    rw [h0, le_bot_iff, map_eq_bot_iff_of_injective _ hψ] at hle
    exact hΔ hle
  obtain ⟨h1, h2⟩ := h (D.map ψ) (hel D hD) (by rw [card_map_of_injective hψ, hcard]) (H.map ψ)
    hH' hDH' hΔ' (A.map ψ) (map_mono hDA) (hel A hA)
  refine ⟨by rwa [card_map_of_injective hψ] at h1, fun z hz hzR => ?_⟩
  obtain ⟨w, hw, hwz⟩ := h2 (ψ z) ⟨z, hz, rfl⟩ hzR
  rwa [← hψ hwz]

end Transport

section Linear

variable {F : Type} [Field F] [Finite F] {p : ℕ}

theorem heisUpper_projectiveSL (hp : p.Prime) (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1) :
    HeisUpper p (projectiveSL p F) (linearAutGroup p F) := by
  have hn : 3 ≤ p := by have := hp.two_le; omega
  have hpF' : ¬ p ∣ Nat.card F := by
    intro hd
    have h1 : p ∣ Nat.card F - (Nat.card F - 1) := Nat.dvd_sub hd hpF
    have hc : 1 ≤ Nat.card F := Nat.card_pos
    rw [show Nat.card F - (Nat.card F - 1) = 1 by omega] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  have hR : (conjAut p F).range = linearAutGroup p F := by
    ext x
    rw [MonoidHom.mem_range, mem_linearAutGroup_iff]
  rw [← hR]
  refine heisUpper_of_model hp
    (CFSG.RankThree.PartOne.CTP.natCast_ne_zero_of_not_dvd_card hp hpF') (MonoidHom.id _)
    (fun _ _ h => h) (conjAut p F) (fun g hg => ?_) (fun g c hg => ?_) ?_ ?_
    (fun A hA => exists_cyclic_quotient_linear hn hp hp2 A hA)
  · obtain ⟨c, hc⟩ := Heis.eq_scalar_of_conjAut_eq_one hn hg
    exact ⟨c, hc.symm⟩
  · rw [MonoidHom.id_apply] at hg
    rw [hg]
    exact conjAut_scalar_eq_one c
  · intro A B hAB hAp hBp hA1 hBA H hH hnorm
    exact diagAbelianPlaneBalance_holds p F hn p hp hp2 hpF dvd_rfl A B hAB hAp hBp hA1 hBA H hH
      hnorm
  · intro D hD hDl H hH
    exact localDeltaIn_eq_bot_of_not_le_linearAutGroup hn hp hp2 hpF hD
      (fun h => hDl fun x hx => MonoidHom.mem_range.2 (mem_linearAutGroup_iff.1 (h hx))) hH

end Linear

section Unitary

variable {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) {p : ℕ}

theorem heisUpper_primeFormP (hp : p.Prime) (hp2 : p ≠ 2) (hne : ¬(p = 3 ∧ ℓ ^ f = 2))
    (h8 : ¬(p = 3 ∧ ℓ ^ f = 8)) (hpq : p ∣ ℓ ^ f + 1) :
    HeisUpper p (primeFormP h (idGram K p)) (primeFormD h (idGram K p)) := by
  have := h.finite
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (primeFormP h (idGram K p)) := finite_primeFormP
  have hn : 3 ≤ p := by have := hp.two_le; omega
  have hpℓ : ¬ p ∣ ℓ := by
    intro hd
    have h1 : p ∣ ℓ ^ f := hd.trans (dvd_pow_self ℓ (by have := h.one_le; omega))
    exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h1).1 hpq))
  have hpK : ((p : ℕ) : K) ≠ 0 := by
    refine CFSG.RankThree.PartOne.CTP.natCast_ne_zero_of_not_dvd_card hp ?_
    rw [h.card]
    exact fun hd => hpℓ (hp.dvd_of_dvd_pow hd)
  have hq3 := three_lt_of_dvd_add_one h hp hp2 hne hpq
  refine heisUpper_of_model hp hpK (primeFormUnitary h (idGram K p)).subtype
    (Subgroup.subtype_injective _) (primeFormConjHom h (idGram K p)) (fun g hg => ?_)
    (fun g c hg => primeFormConjHom_eq_one_of_scalar h hn hne hg) ?_ ?_ ?_
  · obtain ⟨c, -, hc⟩ := (primeFormConjHom_eq_one_iff_of_ne hn hne g).1 hg
    exact ⟨c, hc⟩
  · intro A B hAB hAp hBp hA1 hBA H hH _
    exact localDeltaIn_eq_bot_of_unitary_plane hn hne hq3 hp hp2 hpq hAB hAp hBp hA1 hBA hH
  · intro D hD hDl H hH
    exact localDeltaIn_eq_bot_of_not_le_primeFormD h hn hne hp hp2 hpq
      (not_three_pow_div_eq_two h hne h8 hD hDl) hD hDl hH
  · intro A hA
    have hcyc : IsCyclic (K ≃+* K) :=
      CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
    refine ⟨K ≃+* K, inferInstance, hcyc,
      (primeFormFieldFactor h isPrimeFormGram_one hn hne).comp A.subtype, fun x hx => ?_⟩
    have hx' : (x : MulAut (primeFormP h (idGram K p))) ∈
        (primeFormFieldFactor h isPrimeFormGram_one hn hne).ker := hx
    rw [ker_primeFormFieldFactor] at hx'
    exact hx'

end Unitary

end CFSG.HardMathSupport.Solomon.Coordinator
