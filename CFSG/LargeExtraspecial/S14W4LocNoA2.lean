module

public import CFSG.LargeExtraspecial.S14W4LocAct
public import CFSG.LargeExtraspecial.S14W4LocWeak
public import CFSG.LargeExtraspecial.O62Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.W4Loc

open Subgroup Module CFSG.LargeExtraspecial.S4 CFSG.RankThree.OrthogonalInvolutions

@[expose] def WeaklyClosedE8Stmt : Prop :=
  ∀ {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {q : QuadraticForm (ZMod 2) V} (_ : finrank (ZMod 2) V = 6)
    (hq : q.polarBilin.Nondegenerate) {H E : Subgroup (V ≃ₗ[ZMod 2] V)},
    omegaGroup q hq ≤ H → H ≤ TauCeti.QuadraticMap.orthogonalGroup q → E ≤ H →
    Nat.card E = 8 → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ 2 = 1) →
    (∀ h ∈ H, E.map (MulAut.conj h).toMonoidHom ≤ normalizer (E : Set (V ≃ₗ[ZMod 2] V)) →
      E.map (MulAut.conj h).toMonoidHom = E) →
    O62.IsPlus q ∧ E ≤ omegaGroup q hq

theorem mem_normalizer_of_conj_mem {G : Type*} [Group G] [Finite G] {L : Subgroup G} {a : G}
    (h : ∀ ℓ ∈ L, a * ℓ * a⁻¹ ∈ L) : a ∈ normalizer (L : Set G) := by
  have hle : L.map (MulAut.conj a).toMonoidHom ≤ L := by
    rintro _ ⟨ℓ, hℓ, rfl⟩
    exact h ℓ hℓ
  have heq : L.map (MulAut.conj a).toMonoidHom = L :=
    Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj a).injective).ge
  refine mem_normalizer_iff.mpr fun z => ⟨fun hz => h z hz, fun hz => ?_⟩
  obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp (heq.ge hz)
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hwz
  have : w = z := by simpa using hwz
  exact this ▸ hw

theorem map_conj_map {K V : Type*} [Group K] [Group V] (f : K →* V) (L : Subgroup K) (x : K) :
    (L.map (MulAut.conj x).toMonoidHom).map f = (L.map f).map (MulAut.conj (f x)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext ℓ
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]

theorem mem_map_conj_subgroupOf {G : Type*} [Group G] {K L : Subgroup G} (hLK : L ≤ K) (x z : K) :
    z ∈ (L.subgroupOf K).map (MulAut.conj x).toMonoidHom ↔
      (z : G) ∈ L.map (MulAut.conj (x : G)).toMonoidHom := by
  constructor
  · rintro ⟨ℓ, hℓ, rfl⟩
    exact ⟨ℓ, Subgroup.mem_subgroupOf.mp hℓ, rfl⟩
  · rintro ⟨ℓ, hℓ, he⟩
    refine ⟨⟨ℓ, hLK hℓ⟩, Subgroup.mem_subgroupOf.mpr hℓ, Subtype.ext ?_⟩
    simpa using he

variable {X : Type*} [Group X] [Finite X] {T : Setting X}

theorem weaklyClosed_Lbar {g₀ : X} (C : Cons311 T g₀) (x : T.Mbar)
    (hx : ∀ a ∈ ((T.Lbar g₀).subgroupOf T.Mbar).map (MulAut.conj x).toMonoidHom,
      ∀ ℓ ∈ (T.Lbar g₀).subgroupOf T.Mbar, a * ℓ * a⁻¹ ∈ (T.Lbar g₀).subgroupOf T.Mbar) :
    ((T.Lbar g₀).subgroupOf T.Mbar).map (MulAut.conj x).toMonoidHom =
      (T.Lbar g₀).subgroupOf T.Mbar := by
  have hLM := T.Lbar_le_Mbar g₀
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp x.2
  have hLk : T.Lbar ((k : X) * g₀) = (T.Lbar g₀).map (MulAut.conj (x : T.O)).toMonoidHom := by
    rw [Lbar_mul T k g₀, hk]
  have hnorm : T.Lbar ((k : X) * g₀) ≤ normalizer (T.Lbar g₀ : Set T.O) := by
    intro a ha
    rw [hLk] at ha
    have haM : a ∈ T.Mbar := by
      obtain ⟨ℓ₀, hℓ₀, rfl⟩ := Subgroup.mem_map.mp ha
      exact mul_mem (mul_mem x.2 (hLM hℓ₀)) (inv_mem x.2)
    refine mem_normalizer_of_conj_mem fun ℓ hℓ => ?_
    have h1 := hx ⟨a, haM⟩ ((mem_map_conj_subgroupOf hLM x ⟨a, haM⟩).mpr ha) ⟨ℓ, hLM hℓ⟩
      (Subgroup.mem_subgroupOf.mpr hℓ)
    exact Subgroup.mem_subgroupOf.mp h1
  have hwc := C.weaklyClosed (k : X) k.2 hnorm
  rw [hLk] at hwc
  ext z
  rw [mem_map_conj_subgroupOf hLM x z, hwc, Subgroup.mem_subgroupOf]

variable {R : Subgroup X} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {π : T.M →* (V ≃ₗ[ZMod 2] V)}

theorem isPlus_of_cons311 (hM8 : WeaklyClosedE8Stmt) (A : Act T R π)
    (hcard : Nat.card T.Qt = 2 ^ 8) (hL : Lat T R) [FiniteDimensional (ZMod 2) V]
    (hV : finrank (ZMod 2) V = 6) {q : QuadraticForm (ZMod 2) V}
    (hq : q.polarBilin.Nondegenerate) (hR : (R.subgroupOf T.M).map π = omegaGroup q hq)
    (hO : ∀ k, π k ∈ TauCeti.QuadraticMap.orthogonalGroup q) {g₀ : X}
    (haQ : g₀ * T.z * g₀⁻¹ ∈ T.QG) (C : Cons311 T g₀) (hw : T.width = 4) : O62.IsPlus q := by
  set f := πbar T π A.Q_le_ker with hfdef
  set Lb := (T.Lbar g₀).subgroupOf T.Mbar with hLb
  have hLM := T.Lbar_le_Mbar g₀
  have hLb2 : IsPGroup 2 Lb :=
    (isPGroup_Lbar T haQ).of_equiv (Subgroup.subgroupOfEquivOfLe hLM).symm
  have hcardLb : Nat.card Lb = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv, C.card_Lbar, hw]
    norm_num
  have hf : ∀ y : T.Mbar, (∃ n : ℕ, y ^ 2 ^ n = 1) → f y = 1 → y = 1 :=
    fun y hy h1 => eq_one_of_πbar_eq_one A hcard hL y hy h1
  refine (hM8 hV hq (H := f.range) (E := Lb.map f) ?_ ?_ (map_le_range f Lb) ?_ ?_ ?_ ?_).1
  · intro x hx
    obtain ⟨r, -, rfl⟩ := Subgroup.mem_map.mp (hR.ge hx)
    exact ⟨⟨T.ρ r, ρ_mem_Mbar r⟩, πbar_ρ A.Q_le_ker r⟩
  · rw [MonoidHom.range_eq_map]
    exact map_πbar_le A.Q_le_ker hO ⊤
  · rw [card_map_πbar A hcard hL Lb hLb2, hcardLb]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Lbar_comm T haQ (Subgroup.mem_subgroupOf.mp ha)
      (Subgroup.mem_subgroupOf.mp hb))
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow]
    have h2 : a ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, pow_two]
      exact mul_self_of_mem_Lbar T haQ (Subgroup.mem_subgroupOf.mp ha))
    rw [h2, map_one]
  · rintro _ ⟨x, rfl⟩ hle
    rw [← map_conj_map]
    refine map_conj_eq_of_weaklyClosed f hf hLb2 (weaklyClosed_Lbar C) x fun a ha => ?_
    exact hle (by rw [← map_conj_map]; exact Subgroup.mem_map_of_mem f ha)

end CFSG.LargeExtraspecial.S14.W4Loc
