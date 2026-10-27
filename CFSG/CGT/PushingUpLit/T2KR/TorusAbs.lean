module

public import CFSG.CGT.PushingUpLit.T2KR.TorusSec3
public import CFSG.CGT.Timmesfeld75.Sec3Basic
public import CFSG.CGT.Timmesfeld75.BenderInputs6
public import CFSG.CGT.Timmesfeld75.Targets

public section

namespace CFSG.CGT.PushingUpLit.T2KR

open CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped MatrixGroups commutatorElement

@[expose] def SzTwoPointTorus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T T₁ : Subgroup G), Sec3 T T₁ → Sec3 T₁ T →
    ∀ [((cfgM T T₁).subgroupOf (T ⊔ T₁)).Normal] (a : ℕ), 1 ≤ a →
      Nonempty (↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁) ≃* Sz a) →
      ∃ k ∈ T ⊔ T₁, k ∈ Subgroup.normalizer (T : Set G) ∧ k ∈ Subgroup.normalizer (T₁ : Set G) ∧
        k ≠ 1 ∧ ∀ m ∈ cfgM T T₁, k * m * k⁻¹ = m → m = 1

section Dihedral

variable {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G}
  [hN : ((cfgM T T₁).subgroupOf (T ⊔ T₁)).Normal]

set_option quotPrecheck false in
local notation "XQ" => ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁)

set_option quotPrecheck false in
local notation "TQ" =>
  (T.subgroupOf (T ⊔ T₁)).map (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))

omit [Finite G] in
theorem card_eq_mul_card_map (hS : Sec3 T T₁) {k : ℕ} (hk : Nat.card TQ = k) :
    Nat.card T = Nat.card (normIn T T₁) * k := by
  let φ : ↥T →* XQ := (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))).comp
    (Subgroup.inclusion (le_sup_left : T ≤ T ⊔ T₁))
  have hrange : φ.range = TQ := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨Subgroup.inclusion le_sup_left t, Subgroup.mem_subgroupOf.2 t.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨(y : G), Subgroup.mem_subgroupOf.1 hy⟩, rfl⟩
  have hker : φ.ker = (normIn T T₁).subgroupOf T := by
    ext t
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hS.cfg.inf_cfgM, Subgroup.mem_inf]
    constructor
    · intro ht
      have h1 : (Subgroup.inclusion le_sup_left t : ↥(T ⊔ T₁)) ∈
          (cfgM T T₁).subgroupOf (T ⊔ T₁) := (QuotientGroup.eq_one_iff _).1 ht
      exact ⟨t.2, Subgroup.mem_subgroupOf.1 h1⟩
    · rintro ⟨-, hM⟩
      exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hM)
  have h1 := Subgroup.card_ker_mul_card_range φ
  rw [hker, hrange, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (normIn_le T T₁)).toEquiv,
    hk] at h1
  exact h1.symm

theorem card_map_eq_two_of_dihedral (hS : Sec3 T T₁) {n : ℕ} (hn : Odd n)
    (h : Nonempty (XQ ≃* DihedralGroup n)) : Nat.card TQ = 2 := by
  obtain ⟨e⟩ := h
  have hT2 : IsPGroup 2 TQ := isPGroup_two_of_isElemAbelian hS.isElemAbelian_map
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := 2)).1 hT2
  have hdvd : Nat.card TQ ∣ Nat.card XQ := Subgroup.card_subgroup_dvd_card _
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card] at hdvd
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hS.map_ne_bot (Subgroup.eq_bot_of_card_eq _ (by simpa using hj))
  have hj1 : j ≤ 1 := by
    by_contra hlt
    have h4 : 4 ∣ Nat.card TQ := by
      rw [hj]
      have h4' : 2 ^ 2 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
      simpa using h4'
    obtain ⟨c, hc⟩ := hn
    have : 4 ∣ 2 * (2 * c + 1) := h4.trans (hc ▸ hdvd)
    omega
  have : j = 1 := by omega
  rw [hj, this]
  norm_num

end Dihedral

section Main

variable {G : Type} [Group G] [Finite G]

theorem pair_torus_of_lemma214 (hL214 : Lemma214) (hSz : SzTwoPointTorus) {T : Subgroup G}
    (hT : IsWC T) {g : G} (hne : conjSubgroup g T ≠ T) (hL : normIn T (conjSubgroup g T) ≠ ⊥)
    (hbig : 2 < (normIn T (conjSubgroup g T)).relIndex T) :
    ∃ k : G, k ∈ Subgroup.normalizer (T : Set G) ∧
      k ∈ Subgroup.normalizer ((conjSubgroup g T : Subgroup G) : Set G) ∧ k ≠ 1 ∧
      ∀ m ∈ cfgM T (conjSubgroup g T), k * m * k⁻¹ = m → m = 1 := by
  have hS : Sec3 T (conjSubgroup g T) :=
    Sec3.of_inputs hL214 involutionClassInput_of_repo hT hne hL
  have hS' : Sec3 (conjSubgroup g T) T := by
    have hT₁ : IsWC (conjSubgroup g T) := hT.conj g
    have hne' : conjSubgroup g⁻¹ (conjSubgroup g T) ≠ conjSubgroup g T := by
      rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
      exact hne.symm
    have hL' : normIn (conjSubgroup g T) (conjSubgroup g⁻¹ (conjSubgroup g T)) ≠ ⊥ := by
      rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
      exact hS.cfg.ne₁
    have := Sec3.of_inputs hL214 involutionClassInput_of_repo hT₁ hne' hL'
    rwa [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at this
  obtain ⟨-, hNormal, hcases⟩ := hL214 G T hT g hne hL
  have := hNormal
  rcases hcases with ⟨f, hf, hiso⟩ | ⟨a, ha, hiso⟩ | ⟨n, hn, hn3, hiso⟩
  · obtain ⟨k, -, hkT, hkT₁, hk1, hfree⟩ := Sec3.exists_odd_normalizing_pair hS hS' hf hiso
    exact ⟨k, hkT, hkT₁, hk1, hfree⟩
  · obtain ⟨k, -, hkT, hkT₁, hk1, hfree⟩ := hSz G T (conjSubgroup g T) hS hS' a ha hiso
    exact ⟨k, hkT, hkT₁, hk1, hfree⟩
  · exfalso
    have hcard := card_map_eq_two_of_dihedral hS hn hiso
    have h1 := card_eq_mul_card_map hS hcard
    have h2 := Subgroup.relIndex_mul_card (normIn T (conjSubgroup g T)) T
    rw [inf_of_le_left (normIn_le T (conjSubgroup g T))] at h2
    have hpos : 0 < Nat.card (normIn T (conjSubgroup g T)) := Nat.card_pos
    have h3 : (normIn T (conjSubgroup g T)).relIndex T = 2 := by
      apply Nat.eq_of_mul_eq_mul_right hpos
      rw [h2, h1]
      ring
    omega

theorem exists_comm_of_free {B : Subgroup G} (hB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) {k : G}
    (hk : ∀ b ∈ B, k * b * k⁻¹ ∈ B) (hfree : ∀ b ∈ B, k * b * k⁻¹ = b → b = 1) :
    ∀ y ∈ B, ∃ y' ∈ B, y = ⁅y', k⁆ := by
  classical
  let _ : CommGroup B :=
    { (inferInstance : Group B) with mul_comm := fun x y => Subtype.ext (hB x x.2 y y.2) }
  let σ : B →* B :=
    { toFun := fun b => ⟨k * b * k⁻¹, hk b b.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  let φ : B →* B := MonoidHom.mk' (fun b => b * (σ b)⁻¹) (fun x y => by
    simp only [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _)
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro b hb
    have hb' : b * (σ b)⁻¹ = 1 := hb
    have hσ : σ b = b := (mul_inv_eq_one.1 hb').symm
    have hkb : k * (b : G) * k⁻¹ = b := congrArg Subtype.val hσ
    exact Subtype.ext (hfree b b.2 hkb)
  have hsurj : Function.Surjective φ := Finite.injective_iff_surjective.1 hinj
  intro y hy
  obtain ⟨b, hb⟩ := hsurj ⟨y, hy⟩
  refine ⟨b, b.2, ?_⟩
  have hb' : b * (σ b)⁻¹ = ⟨y, hy⟩ := hb
  have hy' : (b : G) * (k * (b : G) * k⁻¹)⁻¹ = y := congrArg Subtype.val hb'
  rw [← hy']
  simp only [commutatorElement_def]
  group

end Main

end CFSG.CGT.PushingUpLit.T2KR
