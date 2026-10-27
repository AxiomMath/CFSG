module

public import CFSG.LargeExtraspecial.AS35KAut
public import CFSG.LargeExtraspecial.AS35NFlagD

public section

namespace CFSG.LargeExtraspecial.Asc611

open Subgroup Matrix CFSG.Fischer.Classification.Unitary CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.ComponentClassification
open CFSG.Blueprint.Fischer (K)

variable {m : ℕ}

@[expose] noncomputable def fieldFactor (hm : 4 ≤ m) : MulAut (PG m) →* (K ≃+* K) :=
  (primeFormFieldFactor AS35U.hF isPrimeFormGram_one (n := m) (by omega) (by omega)).comp
    (MulAut.congr (AS35K.pgPrimeEquiv (m := m) (by omega))).toMonoidHom

theorem card_ringEquiv_le_two : Nat.card (K ≃+* K) ≤ 2 := by
  classical
  have hinj : Function.Injective (fun φ : K ≃+* K => decide (φ ω = ω)) := by
    intro φ ψ h
    have hval : φ ω = ψ ω := by
      have hφ := AS35N.ringEquiv_cases φ
      have hψ := AS35N.ringEquiv_cases ψ
      have hne : frob ω ≠ ω := by
        rw [frob_omega]
        intro h0
        have : (1 : K) = 0 := by
          calc (1 : K) = ω + 1 + ω := by rw [add_comm ω 1, add_assoc, add_self_K, add_zero]
            _ = 0 := by rw [h0, add_self_K]
        exact one_ne_zero this
      have h' : φ ω = ω ↔ ψ ω = ω := by simpa using h
      rcases hφ with hφ | hφ <;> rcases hψ with hψ | hψ
      · rw [hφ, hψ]
      · exact absurd (h'.mp (hφ ω)) (by rw [hψ]; exact hne)
      · exact absurd (h'.mpr (hψ ω)) (by rw [hφ]; exact hne)
      · rw [hφ, hψ]
    ext c
    rcases AS35N.K_cases' c with rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact hval
    · simp [map_add, hval]
  have := Nat.card_le_card_of_injective _ hinj
  simpa using this

theorem fieldFactor_of_realize (hm : 4 ≤ m) {β : MulAut (PG m)}
    {A : primeFormUnitary AS35U.hF ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)}
    {φ : K ≃+* K} (hβ : ∀ g : SUid frob m, ∃ g' : SUid frob m,
      (g' : GL (Fin m) K) = (A : GL (Fin m) K) * glAut φ g * (A : GL (Fin m) K)⁻¹ ∧
        β (QuotientGroup.mk g) = QuotientGroup.mk g') :
    fieldFactor hm β = φ := by
  set Θ := AS35K.pgPrimeEquiv (m := m) (by omega) with hΘ
  have hα : MulAut.congr Θ β = primeFormConjHom AS35U.hF _ A *
      primeFormFieldHom AS35U.hF isPrimeFormGram_one φ := by
    refine MulEquiv.ext fun y => QuotientGroup.induction_on y fun s => ?_
    obtain ⟨g', hg', hβg⟩ := hβ ((AS35K.suEquiv m).symm s)
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, hΘ,
      AS35K.pgPrimeEquiv_symm_mk, hβg, AS35K.pgPrimeEquiv_mk, MulAut.mul_apply]
    change _ = primeFormConjHom AS35U.hF _ A
      (primeFormFieldAut AS35U.hF isPrimeFormGram_one φ (s : primeFormP AS35U.hF _))
    rw [primeFormFieldAut_mk, primeFormConjHom_mk]
    congr 1
    apply Subtype.ext
    rw [AS35K.coe_suEquiv, hg']
    rfl
  show (primeFormFieldFactor AS35U.hF isPrimeFormGram_one (n := m) (by omega) (by omega))
    (MulAut.congr Θ β) = φ
  rw [hα, primeFormFieldFactor_apply]

theorem exists_conj_of_fieldFactor_eq_one (hm : 4 ≤ m) {β : MulAut (PG m)}
    (hβ : fieldFactor hm β = 1) {k : ℕ} (hk : β ^ (2 ^ k) = 1) :
    ∃ g : PG m, β = MulAut.conj g := by
  set Θ := AS35K.pgPrimeEquiv (m := m) (by omega) with hΘ
  set α := MulAut.congr Θ β with hαdef
  have hαD : α ∈ primeFormD AS35U.hF ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) := by
    rw [← ker_primeFormFieldFactor AS35U.hF isPrimeFormGram_one (n := m) (by omega) (by omega),
      MonoidHom.mem_ker]
    exact hβ
  set D := primeFormD AS35U.hF ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) with hD
  set δ : D := ⟨α, hαD⟩ with hδ
  have hδk : δ ^ (2 ^ k) = 1 := by
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, hδ]
    change (MulAut.congr Θ) β ^ (2 ^ k) = 1
    rw [← map_pow, hk, map_one]
  set q := QuotientGroup.mk' ((OuterAutomorphisms.inner (primeFormP AS35U.hF
    ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K))).subgroupOf D) with hq
  have hcard := card_primeFormD_quotient_dvd AS35U.hF ((1 : GL (Fin m) K))
  have h1 : orderOf (q δ) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hδk, map_one])
  have h2 : orderOf (q δ) ∣ 2 ^ 1 + 1 := (orderOf_dvd_natCard (q δ)).trans hcard
  have h3 : orderOf (q δ) = 1 := by
    have hcop : Nat.Coprime (2 ^ k) (2 ^ 1 + 1) := by
      rw [show (2 : ℕ) ^ 1 + 1 = 3 by norm_num]
      exact Nat.Coprime.pow_left _ (by norm_num)
    have h6 := Nat.dvd_gcd h1 h2
    rw [Nat.Coprime.gcd_eq_one hcop] at h6
    exact Nat.dvd_one.mp h6
  have h4 : δ ∈ (OuterAutomorphisms.inner (primeFormP AS35U.hF
      ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K))).subgroupOf D := by
    rw [orderOf_eq_one_iff, hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
    exact h3
  rw [mem_subgroupOf] at h4
  obtain ⟨p, hp⟩ := h4
  have hpα : MulAut.conj p = α := hp
  refine ⟨Θ.symm p, ?_⟩
  have h5 : β = (MulAut.congr Θ).symm α := by rw [hαdef, MulEquiv.symm_apply_apply]
  rw [h5, ← hpα, MulAut.congr_symm_apply]
  apply MulEquiv.ext
  intro y
  simp [MulAut.conj_apply]

theorem finite_ringEquiv : Finite (K ≃+* K) := by
  have : Finite K := AS35U.hF.finite
  exact Finite.of_injective (fun φ : K ≃+* K => (φ : K → K)) fun a b h =>
    RingEquiv.ext (congrFun h)

section Normal

variable {H : Type} [Group H] (L : Subgroup H) [L.Normal]

@[expose] noncomputable def actPG (ψ : L ≃* PG m) : H →* MulAut (PG m) :=
  (MulAut.congr ψ).toMonoidHom.comp MulAut.conjNormal

theorem mem_of_fieldFactor_eq_one (hm : 4 ≤ m) (ψ : L ≃* PG m)
    (hC : centralizer (L : Set H) = ⊥) {u : H} (hu : fieldFactor hm (actPG L ψ u) = 1)
    {k : ℕ} (huk : u ^ (2 ^ k) = 1) : u ∈ L := by
  have hk : actPG L ψ u ^ (2 ^ k) = 1 := by rw [← map_pow, huk, map_one]
  obtain ⟨g, hg⟩ := exists_conj_of_fieldFactor_eq_one hm hu hk
  set l : L := ψ.symm g with hl
  have h1 : (MulAut.conjNormal u : MulAut L) = MulAut.conj l := by
    apply (MulAut.congr ψ).injective
    rw [OuterAutomorphisms.congr_conj, hl, MulEquiv.apply_symm_apply]
    exact hg
  have h2 : (l : H)⁻¹ * u ∈ centralizer (L : Set H) := by
    rw [mem_centralizer_iff]
    intro x hx
    have h3 := congrArg (fun α : MulAut L => ((α ⟨x, hx⟩ : L) : H)) h1
    simp only [MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at h3
    calc x * ((l : H)⁻¹ * u) = (l : H)⁻¹ * ((l : H) * x * (l : H)⁻¹) * u := by group
      _ = (l : H)⁻¹ * (u * x * u⁻¹) * u := by rw [h3]
      _ = (l : H)⁻¹ * u * x := by group
  rw [hC, mem_bot] at h2
  have : u = l := by
    calc u = (l : H) * ((l : H)⁻¹ * u) := by group
      _ = l := by rw [show (l : H)⁻¹ * u = 1 from by simpa using h2, mul_one]
  rw [this]
  exact l.2

theorem card_le_two_mul_card_inf [Finite H] (hm : 4 ≤ m) (ψ : L ≃* PG m)
    (hC : centralizer (L : Set H) = ⊥) {U : Subgroup H} (hU : IsPGroup 2 U) :
    Nat.card U ≤ 2 * Nat.card ↥(U ⊓ L) := by
  have := finite_ringEquiv
  set f : U →* (K ≃+* K) := (fieldFactor hm).comp ((actPG L ψ).comp U.subtype) with hf
  have hker : Nat.card f.ker ≤ Nat.card ↥(U ⊓ L) := by
    let e : f.ker → ↥(U ⊓ L) := fun x => ⟨((x : U) : H), mem_inf.mpr ⟨(x : U).2, by
      obtain ⟨k, hk⟩ := hU (x : U)
      refine mem_of_fieldFactor_eq_one L hm ψ hC (k := k) (MonoidHom.mem_ker.mp x.2) ?_
      have := congrArg Subtype.val hk
      simpa using this⟩⟩
    refine Nat.card_le_card_of_injective e fun x y h => ?_
    have := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext this)
  have hrange : Nat.card f.range ≤ 2 :=
    (Subgroup.card_le_card_group f.range).trans card_ringEquiv_le_two
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker] at h1
  rw [← h1]
  calc Nat.card f.ker * Nat.card f.range ≤ Nat.card ↥(U ⊓ L) * 2 :=
        Nat.mul_le_mul hker hrange
    _ = 2 * Nat.card ↥(U ⊓ L) := mul_comm _ _

end Normal

end CFSG.LargeExtraspecial.Asc611
