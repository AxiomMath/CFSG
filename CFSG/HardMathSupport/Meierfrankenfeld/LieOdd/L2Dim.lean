module

public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HyperplaneOrbit
public import CFSG.LocalAnalysis.SectionRank.OddCover.PSL2
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.FieldStab

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.Quasithin CFSG.SectionRank.OddCover CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
open Matrix

section Aux

variable {K : Type*} [Field K]

theorem slD_mul (a b : Kˣ) : slD (a * b) = slD a * slD b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_slD, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem slD_one : slD (1 : Kˣ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_slD]

@[expose] def slDHom : Kˣ →* SpecialLinearGroup (Fin 2) K where
  toFun := slD
  map_one' := slD_one
  map_mul' := slD_mul

@[expose] def addOfMul (D : Subgroup (Multiplicative K)) : AddSubgroup K where
  carrier := {x | Multiplicative.ofAdd x ∈ D}
  add_mem' ha hb := D.mul_mem ha hb
  zero_mem' := D.one_mem
  neg_mem' ha := D.inv_mem ha

theorem index_addOfMul [Finite K] (D : Subgroup (Multiplicative K)) :
    (addOfMul D).index = D.index := by
  have h1 : Nat.card (addOfMul D) * (addOfMul D).index = Nat.card K := AddSubgroup.card_mul_index _
  have h2 : Nat.card D * D.index = Nat.card (Multiplicative K) := Subgroup.card_mul_index D
  have h3 : Nat.card (addOfMul D) = Nat.card D := Nat.card_congr (Equiv.refl _)
  have h4 : Nat.card (Multiplicative K) = Nat.card K := Nat.card_congr Multiplicative.toAdd
  have hpos : 0 < Nat.card D := Nat.card_pos
  rw [h3, ← h4, ← h2] at h1
  exact Nat.eq_of_mul_eq_mul_left hpos h1

end Aux

section Main

variable {W : Type} [CommGroup W] [Finite W]

theorem two_pow_le_card_of_psl2_aux (hW : ∀ w : W, w * w = 1) {K : Type} [Field K] [Finite K]
    {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2) {L : Subgroup (MulAut W)}
    (θ : ↥L ≃* CFSG.GorensteinWalter.PSL2 K) {P : Kˣ → Prop} {c : ℕ}
    (hP : ∀ (D' : AddSubgroup K) (a : Kˣ), D'.index = p →
      (∀ x ∈ D', (a : K) ^ 2 * x ∈ D') → P a)
    (hcount : Nat.card {a : Kˣ // P a} ≤ c) :
    2 ^ (orderOf (2 : ZMod p) * ((Nat.card K - 1) / c)) ≤ Nat.card W := by
  classical
  let G : CFSG.GorensteinWalter.PSL2 K →* MulAut W := L.subtype.comp θ.symm.toMonoidHom
  have hG : Function.Injective G := L.subtype_injective.comp θ.symm.injective
  let φ : Multiplicative K →* MulAut W := G.comp pslU
  let ψ : Kˣ →* MulAut W := G.comp (pslMk.comp slDHom)
  have hφ : Function.Injective φ := hG.comp pslU_injective
  have hconj : ∀ (a : Kˣ) (t : K), ψ a * φ (Multiplicative.ofAdd t) * (ψ a)⁻¹ =
      φ (Multiplicative.ofAdd ((a : K) ^ 2 * t)) := by
    intro a t
    have := congrArg G (pslD_conj_pslU a t)
    simpa [φ, ψ, map_mul, map_inv, slDHom] using this
  have hUc : ∀ a ∈ φ.range, ∀ b ∈ φ.range, a * b = b * a := by
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  have hUp : ∀ a ∈ φ.range, a ^ p = 1 := by
    rintro _ ⟨t, rfl⟩
    rw [← map_pow, multiplicative_pow_char_eq_one, map_one]
  have hU1 : φ.range ≠ ⊥ := by
    intro h
    have hm : φ (Multiplicative.ofAdd (1 : K)) ∈ φ.range := ⟨_, rfl⟩
    rw [h, Subgroup.mem_bot, ← map_one φ] at hm
    have := hφ hm
    simp at this
  have hTN : ψ.range ≤ Subgroup.normalizer (φ.range : Set (MulAut W)) := by
    rintro _ ⟨a, rfl⟩
    rw [Subgroup.mem_set_normalizer_iff]
    intro h
    constructor
    · rintro ⟨s, rfl⟩
      refine ⟨Multiplicative.ofAdd ((a : K) ^ 2 * s.toAdd), ?_⟩
      rw [← hconj a s.toAdd, ofAdd_toAdd]
    · rintro ⟨s', hs'⟩
      have e : h = ψ a⁻¹ * φ s' * (ψ a⁻¹)⁻¹ := by rw [map_inv, hs']; group
      refine ⟨Multiplicative.ofAdd (((a⁻¹ : Kˣ) : K) ^ 2 * s'.toAdd), ?_⟩
      rw [← hconj a⁻¹ s'.toAdd, ofAdd_toAdd, ← e]
  have hunits : Nat.card Kˣ = Nat.card K - 1 := by
    have := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units]
  have horb : ∀ D : Subgroup (MulAut W), D ≤ φ.range → D.relIndex φ.range = p →
      (Nat.card K - 1) / c ≤ (ψ.range ⊓ Subgroup.normalizer (D : Set (MulAut W))).relIndex ψ.range := by
    intro D hDU hrel
    obtain ⟨D'', hDD⟩ : ∃ D'' : Subgroup (Multiplicative K), D''.map φ = D :=
      ⟨D.comap φ, Subgroup.map_comap_eq_self hDU⟩
    have hidx : D''.index = p := by
      rw [← Subgroup.relIndex_top_right, ← Subgroup.relIndex_map_map_of_injective D'' ⊤ hφ, hDD,
        ← MonoidHom.range_eq_map]
      exact hrel
    have hD'idx : (addOfMul D'').index = p := (index_addOfMul D'').trans hidx
    let S : Subgroup Kˣ := ((ψ.range ⊓ Subgroup.normalizer (D : Set (MulAut W))).subgroupOf
      ψ.range).comap ψ.rangeRestrict
    have hSP : ∀ a ∈ S, P a := by
      intro a ha
      apply hP (addOfMul D'') a hD'idx
      intro x hx
      have hN : ψ a ∈ Subgroup.normalizer (D : Set (MulAut W)) :=
        (Subgroup.mem_inf.1 ha).2
      have hxD : φ (Multiplicative.ofAdd x) ∈ D := by
        rw [← hDD]
        exact ⟨_, hx, rfl⟩
      have h1 := (Subgroup.mem_set_normalizer_iff.1 hN _).1 hxD
      rw [hconj, ← hDD] at h1
      obtain ⟨y, hy, hyeq⟩ := h1
      have h2 := hφ hyeq
      show Multiplicative.ofAdd ((a : K) ^ 2 * x) ∈ D''
      rw [← h2]
      exact hy
    have hSle : Nat.card S ≤ c :=
      (Nat.card_le_card_of_injective (fun a : S => (⟨a.1, hSP a.1 a.2⟩ : {a : Kˣ // P a}))
        (fun a b h => Subtype.ext (Subtype.mk.inj h))).trans hcount
    have hindex : S.index = (ψ.range ⊓ Subgroup.normalizer (D : Set (MulAut W))).relIndex
        ψ.range := by
      rw [Subgroup.relIndex]
      exact Subgroup.index_comap_of_surjective _ ψ.rangeRestrict_surjective
    have hcard : Nat.card S * S.index = Nat.card Kˣ := Subgroup.card_mul_index S
    rw [← hindex]
    apply Nat.div_le_of_le_mul
    calc Nat.card K - 1 = Nat.card S * S.index := by rw [hcard, hunits]
      _ ≤ c * S.index := Nat.mul_le_mul_right _ hSle
  have hker := two_pow_le_card_ker_of_hyperplane_orbit hW hp2 hUc hUp hU1 hTN horb
  calc 2 ^ (orderOf (2 : ZMod p) * ((Nat.card K - 1) / c))
      = 2 ^ (((Nat.card K - 1) / c) * orderOf (2 : ZMod p)) := by rw [mul_comm]
    _ ≤ Nat.card (normHom φ.range).ker := hker
    _ ≤ Nat.card W := Subgroup.card_le_card_group _

theorem two_pow_le_card_of_psl2 (hW : ∀ w : W, w * w = 1) {K : Type} [Field K] [Finite K]
    {p e : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2) (hK : Nat.card K = p ^ e) (_he : 1 ≤ e)
    {L : Subgroup (MulAut W)} (θ : ↥L ≃* CFSG.GorensteinWalter.PSL2 K) :
    2 ^ (orderOf (2 : ZMod p) * ((p ^ e - 1) / (2 * (p - 1)))) ≤ Nat.card W := by
  have h := two_pow_le_card_of_psl2_aux hW hp2 θ
    (P := fun a => ((a : K) ^ 2) ^ p = (a : K) ^ 2) (c := 2 * (p - 1))
    (fun _ _ hidx hD => pow_char_eq_self_of_mul_mem hidx hD) card_sq_pow_char_le
  rwa [hK] at h

theorem two_pow_le_card_of_psl2_of_odd (hW : ∀ w : W, w * w = 1) {K : Type} [Field K] [Finite K]
    {p e : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2) (hK : Nat.card K = p ^ e) (_he : 1 ≤ e)
    {L : Subgroup (MulAut W)} (θ : ↥L ≃* CFSG.GorensteinWalter.PSL2 K) (heo : Odd e) :
    2 ^ (orderOf (2 : ZMod p) * ((p ^ e - 1) / (p - 1))) ≤ Nat.card W := by
  have h := two_pow_le_card_of_psl2_aux hW hp2 θ
    (P := fun a => (a : K) ^ p = a) (c := p - 1)
    (fun _ _ hidx hD => pow_char_eq_self_of_sq hp2 hK heo (pow_char_eq_self_of_mul_mem hidx hD))
    card_pow_char_units_le
  rwa [hK] at h

end Main

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
