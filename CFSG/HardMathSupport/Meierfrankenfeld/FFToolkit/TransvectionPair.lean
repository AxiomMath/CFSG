module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Basic
import CFSG.Quasithin.Background.FixVZPowersMem

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1

variable {V : Type} [CommGroup V] [Finite V]

@[expose] def IsTransvCentred (τ : MulAut V) (u : V) : Prop :=
  τ ≠ 1 ∧ τ * τ = 1 ∧ u ≠ 1 ∧ τ u = u ∧ ∀ v : V, τ v = v ∨ τ v = v * u

theorem mem_zpowers_iff_eq_one_or_eq_of_mul_self {G : Type*} [Group G] {x w : G}
    (hx : x * x = 1) : w ∈ Subgroup.zpowers x ↔ w = 1 ∨ w = x := by
  have hxx : x ^ (2 : ℤ) = 1 := by rw [zpow_two, hx]
  constructor
  · intro hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
    · left
      rw [zpow_mul, hxx, one_zpow]
    · right
      rw [zpow_add, zpow_mul, hxx, one_zpow, one_mul, zpow_one]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

theorem IsTransvCentred.center_unique {τ : MulAut V} {u u' : V}
    (h : IsTransvCentred τ u) (h' : IsTransvCentred τ u') : u = u' := by
  obtain ⟨hτ1, -, -, -, hstep⟩ := h
  obtain ⟨-, -, -, -, hstep'⟩ := h'
  obtain ⟨v, hv⟩ : ∃ v, τ v ≠ v := by
    by_contra hcon
    push Not at hcon
    exact hτ1 (MulEquiv.ext hcon)
  have h1 : τ v = v * u := (hstep v).resolve_left hv
  have h2 : τ v = v * u' := (hstep' v).resolve_left hv
  exact mul_left_cancel (h1.symm.trans h2)

theorem IsTransvCentred.conj {τ : MulAut V} {u : V} (h : IsTransvCentred τ u)
    (k : MulAut V) : IsTransvCentred (k * τ * k⁻¹) (k u) := by
  obtain ⟨hτ1, hτ2, hu1, hu, hstep⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h1
    apply hτ1
    have h2 := congrArg (fun x => k⁻¹ * x * k) h1
    simpa [mul_assoc] using h2
  · calc (k * τ * k⁻¹) * (k * τ * k⁻¹) = k * (τ * τ) * k⁻¹ := by group
      _ = 1 := by rw [hτ2]; group
  · intro h1
    apply hu1
    have h2 := congrArg (fun x => k⁻¹ x) h1
    rw [MulAut.inv_apply_self] at h2
    simpa using h2
  · show (k * τ * k⁻¹) (k u) = k u
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hu]
  · intro v
    have h1 := hstep (k⁻¹ v)
    have hv : (k * τ * k⁻¹) v = k (τ (k⁻¹ v)) := by
      simp [MulAut.mul_apply]
    rw [hv]
    rcases h1 with h1 | h1
    · left
      rw [h1, MulAut.apply_inv_self]
    · right
      rw [h1, map_mul, MulAut.apply_inv_self]

theorem exists_isTransvCentred (hV : ∀ v : V, v * v = 1) {τ : MulAut V}
    (hτ2 : τ * τ = 1) (hτ1 : τ ≠ 1)
    (hcard : Nat.card V ≤ 2 * Nat.card (fixV (Subgroup.zpowers τ))) :
    ∃ u, IsTransvCentred τ u := by
  classical
  let δ : V →* V :=
    { toFun := fun v => v⁻¹ * τ v
      map_one' := by simp
      map_mul' := fun x y => by
        simp only [map_mul, mul_inv_rev]
        ac_rfl }
  have hδ_apply : ∀ v, δ v = v⁻¹ * τ v := fun v => rfl
  have hker : δ.ker = fixV (Subgroup.zpowers τ) := by
    ext v
    rw [MonoidHom.mem_ker, mem_fixV_zpowers_iff_apply]
    constructor
    · intro h
      have h' : v⁻¹ * τ v = 1 := by simpa only [hδ_apply] using h
      calc τ v = v * (v⁻¹ * τ v) := by group
        _ = v := by rw [h', mul_one]
    · intro h
      show v⁻¹ * τ v = 1
      rw [h, inv_mul_cancel]
  have hle : Nat.card δ.range ≤ 2 := by
    have hmul := Subgroup.card_ker_mul_card_range δ
    rw [hker] at hmul
    have hpos : 0 < Nat.card (fixV (Subgroup.zpowers τ)) := Nat.card_pos
    have hineq : Nat.card (fixV (Subgroup.zpowers τ)) * Nat.card δ.range ≤
        Nat.card (fixV (Subgroup.zpowers τ)) * 2 := by
      calc Nat.card (fixV (Subgroup.zpowers τ)) * Nat.card δ.range = Nat.card V := hmul
        _ ≤ 2 * Nat.card (fixV (Subgroup.zpowers τ)) := hcard
        _ = Nat.card (fixV (Subgroup.zpowers τ)) * 2 := by ring
    exact Nat.le_of_mul_le_mul_left hineq hpos
  have hrange_ne_bot : δ.range ≠ ⊥ := by
    intro hbot
    apply hτ1
    ext v
    have h1 : v⁻¹ * τ v = 1 := by
      have hmem : δ v ∈ δ.range := ⟨v, rfl⟩
      rw [hbot] at hmem
      simpa only [Subgroup.mem_bot, hδ_apply] using hmem
    calc τ v = v * (v⁻¹ * τ v) := by group
      _ = v := by rw [h1, mul_one]
  have hcard_range : Nat.card δ.range = 2 := by
    have hne : Nat.card δ.range ≠ 1 := by
      intro h1
      exact hrange_ne_bot ((Subgroup.card_eq_one).mp h1)
    have hpos : 0 < Nat.card δ.range := Nat.card_pos
    omega
  obtain ⟨⟨u, hu_mem⟩, hu_ne_sub⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hrange_ne_bot
  have hu_ne : u ≠ 1 := fun h => hu_ne_sub (Subtype.ext h)
  have hu2 : u * u = 1 := hV u
  have hker_le : δ.range ≤ δ.ker := by
    intro x hx
    obtain ⟨v, rfl⟩ := hx
    rw [MonoidHom.mem_ker]
    have hδτ : δ (τ v) = δ v := by
      rw [hδ_apply, hδ_apply]
      have h3 : τ (τ v) = v := by
        rw [← MulAut.mul_apply, hτ2, MulAut.one_apply]
      rw [h3, inv_eq_of_mul_eq_one_right (hV v), inv_eq_of_mul_eq_one_right (hV (τ v))]
      exact mul_comm _ _
    have h2 : δ (δ v) = 1 := by
      rw [hδ_apply v, map_mul, map_inv, hδτ]
      group
    exact h2
  have hfix_u : τ u = u := by
    have hmem : u ∈ δ.ker := hker_le hu_mem
    rw [MonoidHom.mem_ker] at hmem
    have hmem' : u⁻¹ * τ u = 1 := by simpa only [hδ_apply] using hmem
    calc τ u = u * (u⁻¹ * τ u) := by group
      _ = u := by rw [hmem', mul_one]
  refine ⟨u, hτ1, hτ2, hu_ne, hfix_u, fun v => ?_⟩
  have hv : δ v ∈ δ.range := ⟨v, rfl⟩
  have hzp : Subgroup.zpowers u ≤ δ.range := Subgroup.zpowers_le.mpr hu_mem
  have hcard_zp : Nat.card (Subgroup.zpowers u) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hu2) hu_ne]
  have hzp_eq : Subgroup.zpowers u = δ.range :=
    Subgroup.eq_of_le_of_card_ge hzp (by rw [hcard_zp, hcard_range])
  have hmem : δ v = 1 ∨ δ v = u :=
    (mem_zpowers_iff_eq_one_or_eq_of_mul_self hu2).mp (hzp_eq.symm ▸ hv)
  rcases hmem with h1 | h1
  · left
    have h1' : v⁻¹ * τ v = 1 := by simpa only [hδ_apply] using h1
    calc τ v = v * (v⁻¹ * τ v) := by group
      _ = v := by rw [h1', mul_one]
  · right
    have h1' : v⁻¹ * τ v = u := by simpa only [hδ_apply] using h1
    calc τ v = v * (v⁻¹ * τ v) := by group
      _ = v * u := by rw [h1']

theorem IsTransvCentred.card_eq_two_mul_card_fix (hV : ∀ v : V, v * v = 1)
    {τ : MulAut V} {u : V} (h : IsTransvCentred τ u) :
    Nat.card V = 2 * Nat.card (fixV (Subgroup.zpowers τ)) := by
  classical
  obtain ⟨hτ1, -, hu1, -, hstep⟩ := h
  let δ : V →* V :=
    { toFun := fun v => v⁻¹ * τ v
      map_one' := by simp
      map_mul' := fun x y => by
        simp only [map_mul, mul_inv_rev]
        ac_rfl }
  have hδ_apply : ∀ v, δ v = v⁻¹ * τ v := fun v => rfl
  have hker : δ.ker = fixV (Subgroup.zpowers τ) := by
    ext v
    rw [MonoidHom.mem_ker, mem_fixV_zpowers_iff_apply]
    constructor
    · intro hx
      have hx' : v⁻¹ * τ v = 1 := by simpa only [hδ_apply] using hx
      calc τ v = v * (v⁻¹ * τ v) := by group
        _ = v := by rw [hx', mul_one]
    · intro hx
      show v⁻¹ * τ v = 1
      rw [hx, inv_mul_cancel]
  have hrange : δ.range = Subgroup.zpowers u := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      have hmem : v⁻¹ * τ v = 1 ∨ v⁻¹ * τ v = u := by
        rcases hstep v with e | e
        · left
          rw [e, inv_mul_cancel]
        · right
          rw [e]
          exact inv_mul_cancel_left v u
      exact (mem_zpowers_iff_eq_one_or_eq_of_mul_self (hV u)).mpr hmem
    · have hu_range : u ∈ δ.range := by
        obtain ⟨v, hv⟩ : ∃ v, τ v ≠ v := by
          by_contra hcon
          push Not at hcon
          exact hτ1 (MulEquiv.ext hcon)
        have e : τ v = v * u := (hstep v).resolve_left hv
        exact ⟨v, by simpa only [hδ_apply, e] using inv_mul_cancel_left v u⟩
      exact Subgroup.zpowers_le.mpr hu_range
  have hmul := Subgroup.card_ker_mul_card_range δ
  rw [hker, hrange, Nat.card_zpowers,
    orderOf_eq_prime (by rw [pow_two]; exact hV u) hu1] at hmul
  simpa [mul_comm] using hmul.symm

theorem IsTransvCentred.mul_comm_of_fixes {τ τ' : MulAut V} {u u' : V}
    (h : IsTransvCentred τ u) (h' : IsTransvCentred τ' u')
    (hu' : τ u' = u') (hu : τ' u = u) : τ * τ' = τ' * τ := by
  obtain ⟨-, -, -, -, hstep⟩ := h
  obtain ⟨-, -, -, -, hstep'⟩ := h'
  refine MulEquiv.ext fun v => ?_
  rcases hstep v with e | e <;> rcases hstep' v with e' | e'
  · rw [MulAut.mul_apply, MulAut.mul_apply, e', e, e']
  · rw [MulAut.mul_apply, MulAut.mul_apply]
    calc τ (τ' v) = τ (v * u') := by rw [e']
      _ = τ v * τ u' := by rw [map_mul]
      _ = v * u' := by rw [e, hu']
      _ = τ' v := e'.symm
      _ = τ' (τ v) := by rw [e]
  · rw [MulAut.mul_apply, MulAut.mul_apply]
    calc τ (τ' v) = τ v := by rw [e']
      _ = v * u := e
      _ = τ' v * u := by rw [e']
      _ = τ' v * τ' u := by rw [hu]
      _ = τ' (v * u) := by rw [map_mul]
      _ = τ' (τ v) := by rw [e]
  · rw [MulAut.mul_apply, MulAut.mul_apply]
    calc τ (τ' v) = τ (v * u') := by rw [e']
      _ = τ v * τ u' := by rw [map_mul]
      _ = (v * u) * u' := by rw [e, hu']
      _ = (v * u') * u := by ac_rfl
      _ = τ' v * u := by rw [e']
      _ = τ' v * τ' u := by rw [hu]
      _ = τ' (v * u) := by rw [map_mul]
      _ = τ' (τ v) := by rw [e]

theorem IsTransvCentred.mul_ne_one_of_ne {τ τ' : MulAut V} {u u' : V}
    (h : IsTransvCentred τ u) (h' : IsTransvCentred τ' u') (hne : τ ≠ τ') :
    τ * τ' ≠ 1 := by
  intro h1
  apply hne
  calc τ = τ * (τ' * τ') := by rw [h'.2.1, mul_one]
    _ = (τ * τ') * τ' := by group
    _ = τ' := by rw [h1, one_mul]

theorem IsTransvCentred.mul_mul_self_of_comm {τ τ' : MulAut V} {u u' : V}
    (h : IsTransvCentred τ u) (h' : IsTransvCentred τ' u')
    (hcomm : τ * τ' = τ' * τ) : (τ * τ') * (τ * τ') = 1 := by
  calc (τ * τ') * (τ * τ') = τ * (τ' * τ) * τ' := by group
    _ = τ * (τ * τ') * τ' := by rw [hcomm]
    _ = (τ * τ) * (τ' * τ') := by group
    _ = 1 := by rw [h.2.1, h'.2.1, mul_one]

theorem fixV_inf_le_fixV_mul {τ τ' : MulAut V} :
    fixV (Subgroup.zpowers τ) ⊓ fixV (Subgroup.zpowers τ') ≤
      fixV (Subgroup.zpowers (τ * τ')) := by
  intro v hv
  obtain ⟨hv1, hv2⟩ := Subgroup.mem_inf.mp hv
  rw [mem_fixV_zpowers_iff_apply] at hv1 hv2 ⊢
  rw [MulAut.mul_apply, hv2, hv1]

theorem card_le_four_mul_card_fix_mul (hV : ∀ v : V, v * v = 1) {τ τ' : MulAut V} {u u' : V}
    (h : IsTransvCentred τ u) (h' : IsTransvCentred τ' u')
    (hu' : τ u' = u') (hu : τ' u = u) (hne : τ ≠ τ') :
    Nat.card V ≤ 4 * Nat.card (fixV (Subgroup.zpowers (τ * τ'))) := by
  let Cτ : Subgroup V := fixV (Subgroup.zpowers τ)
  let Cτ' : Subgroup V := fixV (Subgroup.zpowers τ')
  have hA : Nat.card V = Nat.card Cτ * 2 := by
    rw [h.card_eq_two_mul_card_fix hV]; ring
  have hB : Nat.card V = Nat.card Cτ' * 2 := by
    rw [h'.card_eq_two_mul_card_fix hV]; ring
  have hAi : Cτ.index = 2 := by
    have h1 := Subgroup.card_mul_index Cτ
    rw [hA] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  have hBi : Cτ'.index = 2 := by
    have h1 := Subgroup.card_mul_index Cτ'
    rw [hB] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  have hle : (Cτ ⊓ Cτ').index ≤ 4 := by
    refine (Subgroup.index_inf_le (H := Cτ) (K := Cτ')).trans ?_
    rw [hAi, hBi]
  have hcard : Nat.card V = Nat.card ↥(Cτ ⊓ Cτ') * (Cτ ⊓ Cτ').index :=
    (Subgroup.card_mul_index (Cτ ⊓ Cτ')).symm
  have hleAB : Nat.card ↥(Cτ ⊓ Cτ') ≤ Nat.card (fixV (Subgroup.zpowers (τ * τ'))) :=
    Subgroup.card_le_of_le fixV_inf_le_fixV_mul
  calc Nat.card V = Nat.card ↥(Cτ ⊓ Cτ') * (Cτ ⊓ Cτ').index := hcard
    _ ≤ Nat.card ↥(Cτ ⊓ Cτ') * 4 := Nat.mul_le_mul_left _ hle
    _ ≤ Nat.card (fixV (Subgroup.zpowers (τ * τ'))) * 4 := Nat.mul_le_mul_right _ hleAB
    _ = 4 * Nat.card (fixV (Subgroup.zpowers (τ * τ'))) := by ring

theorem IsTransvCentred.sq_mul_apply_of_fixes (hV : ∀ v : V, v * v = 1) {τ τ' : MulAut V}
    {u u' : V} (h : IsTransvCentred τ u) (h' : IsTransvCentred τ' u')
    (hu' : τ u' = u' * u) (hu : τ' u = u) {v : V} (hv : τ' v = v) :
    ((τ * τ') * (τ * τ')) v = v := by
  obtain ⟨-, -, -, hu_fix, hstep⟩ := h
  obtain ⟨-, -, -, hu'_fix, -⟩ := h'
  rcases hstep v with e | e
  · have h1 : (τ * τ') v = v := by rw [MulAut.mul_apply, hv, e]
    rw [MulAut.mul_apply, h1, h1]
  · have hw : (τ * τ') v = v * u := by rw [MulAut.mul_apply, hv, e]
    have h2 : (τ * τ') (v * u) = v := by
      rw [MulAut.mul_apply, map_mul, hv, hu, map_mul, e, hu_fix]
      rw [mul_assoc, hV u, mul_one]
    rw [MulAut.mul_apply, hw, h2]

theorem IsTransvCentred.sq_mul_apply_of_moves (hV : ∀ v : V, v * v = 1) {τ τ' : MulAut V}
    {u u' : V} (h : IsTransvCentred τ u) (h' : IsTransvCentred τ' u')
    (hu' : τ u' = u' * u) (hu : τ' u = u) {v : V} (hv : τ' v = v * u') :
    ((τ * τ') * (τ * τ')) v = v * u := by
  obtain ⟨-, -, -, hu_fix, hstep⟩ := h
  obtain ⟨-, -, -, hu'_fix, hstep'⟩ := h'
  rcases hstep v with e | e
  · have hw : (τ * τ') v = v * u' * u := by
      rw [MulAut.mul_apply, hv, map_mul, e, hu']
      group
    calc ((τ * τ') * (τ * τ')) v = (τ * τ') (v * u' * u) := by rw [MulAut.mul_apply, hw]
      _ = τ (τ' (v * u' * u)) := by rw [MulAut.mul_apply]
      _ = τ (v * u) := by
          congr 1
          rw [map_mul, map_mul, hv, hu'_fix, hu]
          calc (v * u') * u' * u = v * (u' * u') * u := by ac_rfl
            _ = v * u := by rw [hV u', mul_one]
      _ = v * u := by rw [map_mul, e, hu_fix]
  · have hw : (τ * τ') v = v * u' := by
      rw [MulAut.mul_apply, hv, map_mul, e, hu']
      calc (v * u) * (u' * u) = v * (u * u) * u' := by ac_rfl
        _ = v * u' := by rw [hV u, mul_one]
    calc ((τ * τ') * (τ * τ')) v = (τ * τ') (v * u') := by rw [MulAut.mul_apply, hw]
      _ = τ (τ' (v * u')) := by rw [MulAut.mul_apply]
      _ = τ v := by
          congr 1
          rw [map_mul, hv, hu'_fix]
          calc (v * u') * u' = v * (u' * u') := by ac_rfl
            _ = v := by rw [hV u', mul_one]
      _ = v * u := e

theorem IsTransvCentred.sq_mul_ne_one (hV : ∀ v : V, v * v = 1) {τ τ' : MulAut V} {u u' : V}
    (h : IsTransvCentred τ u) (h' : IsTransvCentred τ' u')
    (hu' : τ u' = u' * u) (hu : τ' u = u) :
    ((τ * τ') * (τ * τ')) ≠ 1 := by
  intro h1
  have hu1 : u ≠ 1 := h.2.2.1
  have hτ'1 : τ' ≠ 1 := h'.1
  have hstep' : ∀ v : V, τ' v = v ∨ τ' v = v * u' := h'.2.2.2.2
  obtain ⟨v, hv⟩ : ∃ v, τ' v ≠ v := by
    by_contra hcon
    push Not at hcon
    exact hτ'1 (MulEquiv.ext hcon)
  have hmove : τ' v = v * u' := (hstep' v).resolve_left hv
  have h2 := IsTransvCentred.sq_mul_apply_of_moves hV h h' hu' hu hmove
  rw [h1, MulAut.one_apply] at h2
  have : u = 1 := by
    have h3 := congrArg (fun x => v⁻¹ * x) h2
    rw [inv_mul_cancel, inv_mul_cancel_left] at h3
    exact h3.symm
  exact hu1 this

theorem IsTransvCentred.sq_mul_mul_self (hV : ∀ v : V, v * v = 1) {τ τ' : MulAut V} {u u' : V}
    (h : IsTransvCentred τ u) (h' : IsTransvCentred τ' u')
    (hu' : τ u' = u' * u) (hu : τ' u = u) :
    ((τ * τ') * (τ * τ')) * ((τ * τ') * (τ * τ')) = 1 := by
  refine MulEquiv.ext fun v => ?_
  rcases h'.2.2.2.2 v with hv | hv
  · have h1 : ((τ * τ') * (τ * τ')) v = v := IsTransvCentred.sq_mul_apply_of_fixes hV h h' hu' hu hv
    have h2 : τ' (((τ * τ') * (τ * τ')) v) = ((τ * τ') * (τ * τ')) v := by rw [h1, hv]
    have h3 : ((τ * τ') * (τ * τ')) (((τ * τ') * (τ * τ')) v) =
        ((τ * τ') * (τ * τ')) v := IsTransvCentred.sq_mul_apply_of_fixes hV h h' hu' hu h2
    calc (((τ * τ') * (τ * τ')) * ((τ * τ') * (τ * τ'))) v
        = ((τ * τ') * (τ * τ')) (((τ * τ') * (τ * τ')) v) := by rw [MulAut.mul_apply]
      _ = ((τ * τ') * (τ * τ')) v := h3
      _ = v := h1
  · have h1 : ((τ * τ') * (τ * τ')) v = v * u := IsTransvCentred.sq_mul_apply_of_moves hV h h' hu' hu hv
    have h2 : τ' (((τ * τ') * (τ * τ')) v) = ((τ * τ') * (τ * τ')) v * u' := by
      rw [h1, map_mul, hv, hu]
      ac_rfl
    have h3 : ((τ * τ') * (τ * τ')) (((τ * τ') * (τ * τ')) v) =
        ((τ * τ') * (τ * τ')) v * u := IsTransvCentred.sq_mul_apply_of_moves hV h h' hu' hu h2
    calc (((τ * τ') * (τ * τ')) * ((τ * τ') * (τ * τ'))) v
        = ((τ * τ') * (τ * τ')) (((τ * τ') * (τ * τ')) v) := by rw [MulAut.mul_apply]
      _ = ((τ * τ') * (τ * τ')) v * u := h3
      _ = (v * u) * u := by rw [h1]
      _ = v := by rw [mul_assoc, hV u, mul_one]

theorem card_le_two_mul_card_fix_sq (hV : ∀ v : V, v * v = 1) {τ τ' : MulAut V} {u u' : V}
    (h : IsTransvCentred τ u) (h' : IsTransvCentred τ' u')
    (hu' : τ u' = u' * u) (hu : τ' u = u) :
    Nat.card V ≤ 2 * Nat.card (fixV (Subgroup.zpowers ((τ * τ') * (τ * τ')))) := by
  have hcard := h'.card_eq_two_mul_card_fix hV
  have hle : fixV (Subgroup.zpowers τ') ≤
      fixV (Subgroup.zpowers ((τ * τ') * (τ * τ'))) := by
    intro v hv
    rw [mem_fixV_zpowers_iff_apply] at hv ⊢
    exact IsTransvCentred.sq_mul_apply_of_fixes hV h h' hu' hu hv
  calc Nat.card V = 2 * Nat.card (fixV (Subgroup.zpowers τ')) := hcard
    _ ≤ 2 * Nat.card (fixV (Subgroup.zpowers ((τ * τ') * (τ * τ')))) :=
        Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hle)

theorem conj_mul_conj_mem {L : Subgroup (MulAut V)} {σ : MulAut V}
    (hσN : σ ∈ Subgroup.normalizer (L : Set (MulAut V))) (hσ2 : σ * σ = 1)
    (g h : ↥L) :
    ((g : MulAut V) * σ * (g : MulAut V)⁻¹) *
      ((h : MulAut V) * σ * (h : MulAut V)⁻¹) ∈ L := by
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ2
  have hgh : (g : MulAut V)⁻¹ * (h : MulAut V) ∈ L :=
    L.mul_mem (L.inv_mem g.2) h.2
  have hconj : σ * ((g : MulAut V)⁻¹ * (h : MulAut V)) * σ⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp hσN _).mp hgh
  rw [hσinv] at hconj
  have heq : ((g : MulAut V) * σ * (g : MulAut V)⁻¹) *
      ((h : MulAut V) * σ * (h : MulAut V)⁻¹) =
      (g : MulAut V) * (σ * ((g : MulAut V)⁻¹ * (h : MulAut V)) * σ) *
        (h : MulAut V)⁻¹ := by group
  rw [heq]
  exact L.mul_mem (L.mul_mem g.2 hconj) (L.inv_mem h.2)

theorem exists_conj_mul_conj {L : Subgroup (MulAut V)} {σ : MulAut V}
    (hσN : σ ∈ Subgroup.normalizer (L : Set (MulAut V))) (hσ2 : σ * σ = 1)
    (g h : ↥L) :
    ∃ k : ↥L,
      ((g : MulAut V) * σ * (g : MulAut V)⁻¹) *
        ((h : MulAut V) * σ * (h : MulAut V)⁻¹) *
        ((g : MulAut V) * σ * (g : MulAut V)⁻¹)⁻¹ =
      (k : MulAut V) * σ * (k : MulAut V)⁻¹ := by
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ2
  have hgh : (g : MulAut V)⁻¹ * (h : MulAut V) ∈ L :=
    L.mul_mem (L.inv_mem g.2) h.2
  have hconj : σ * ((g : MulAut V)⁻¹ * (h : MulAut V)) * σ⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp hσN _).mp hgh
  rw [hσinv] at hconj
  let y : ↥L :=
    ⟨(g : MulAut V) * (σ * ((g : MulAut V)⁻¹ * (h : MulAut V)) * σ), L.mul_mem g.2 hconj⟩
  refine ⟨y, ?_⟩
  have hσy : σ * ((g : MulAut V)⁻¹ * (h : MulAut V)) * σ * σ =
      σ * ((g : MulAut V)⁻¹ * (h : MulAut V)) := by
    rw [mul_assoc (σ * _) σ σ, hσ2, mul_one]
  have hτgh : ((g : MulAut V) * σ * (g : MulAut V)⁻¹) * (h : MulAut V) =
      (y : MulAut V) * σ := by
    calc ((g : MulAut V) * σ * (g : MulAut V)⁻¹) * (h : MulAut V)
        = (g : MulAut V) * (σ * ((g : MulAut V)⁻¹ * (h : MulAut V))) := by group
      _ = (g : MulAut V) * (σ * ((g : MulAut V)⁻¹ * (h : MulAut V)) * σ * σ) := by rw [hσy]
      _ = (y : MulAut V) * σ := by
          show _ = ((g : MulAut V) * (σ * ((g : MulAut V)⁻¹ * (h : MulAut V)) * σ)) * σ
          group
  calc ((g : MulAut V) * σ * (g : MulAut V)⁻¹) *
        ((h : MulAut V) * σ * (h : MulAut V)⁻¹) *
        ((g : MulAut V) * σ * (g : MulAut V)⁻¹)⁻¹
      = ((((g : MulAut V) * σ * (g : MulAut V)⁻¹) * (h : MulAut V)) * σ *
          ((((g : MulAut V) * σ * (g : MulAut V)⁻¹) * (h : MulAut V)))⁻¹) := by group
    _ = ((y : MulAut V) * σ) * σ * ((y : MulAut V) * σ)⁻¹ := by rw [hτgh]
    _ = (y : MulAut V) * σ * (y : MulAut V)⁻¹ := by
        have hinv : ((y : MulAut V) * σ)⁻¹ = σ * (y : MulAut V)⁻¹ := by
          rw [mul_inv_rev, hσinv]
        rw [hinv]
        calc (y : MulAut V) * σ * σ * (σ * (y : MulAut V)⁻¹)
            = (y : MulAut V) * (σ * (σ * σ)) * (y : MulAut V)⁻¹ := by group
          _ = (y : MulAut V) * σ * (y : MulAut V)⁻¹ := by rw [hσ2, mul_one]

theorem exists_involution_of_transvection {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v * v = 1) {L : Subgroup (MulAut V)} (hirr : IsIrrOn L)
    (hperf : Group.IsPerfect ↥L) {σ : MulAut V}
    (hσN : σ ∈ Subgroup.normalizer (L : Set (MulAut V))) (hσ2 : σ * σ = 1)
    (hσV : Nat.card V ≤ 2 * Nat.card (fixV (Subgroup.zpowers σ)))
    (hσL : σ ∉ Subgroup.centralizer (L : Set (MulAut V))) :
    ∃ t ∈ L, t ≠ 1 ∧ t * t = 1 ∧ Nat.card V ≤ 4 * Nat.card (fixV (Subgroup.zpowers t)) := by
  classical
  have hσ1 : σ ≠ 1 := by
    intro h
    apply hσL
    rw [h]
    exact Subgroup.one_mem _
  obtain ⟨u₀, hσrep⟩ := exists_isTransvCentred hV hσ2 hσ1 hσV
  let τ : ↥L → MulAut V := fun g => (g : MulAut V) * σ * (g : MulAut V)⁻¹
  let u : ↥L → V := fun g => (g : MulAut V) u₀
  have hrep : ∀ g : ↥L, IsTransvCentred (τ g) (u g) := fun g => hσrep.conj (g : MulAut V)
  by_cases hcase : ∃ g : ↥L, ∃ h : ↥L, τ g ≠ τ h ∧ (τ g (u h) = u h ∨ τ h (u g) = u g)
  · obtain ⟨g, h, hne, hfix | hfix⟩ := hcase
    · by_cases h2 : τ h (u g) = u g
      · have hcomm := (hrep g).mul_comm_of_fixes (hrep h) hfix h2
        have hmulL : τ g * τ h ∈ L := by
          simpa [τ] using conj_mul_conj_mem hσN hσ2 g h
        have hne' : τ g * τ h ≠ 1 := (hrep g).mul_ne_one_of_ne (hrep h) hne
        have hsq := (hrep g).mul_mul_self_of_comm (hrep h) hcomm
        have hcard := card_le_four_mul_card_fix_mul hV (hrep g) (hrep h) hfix h2 hne
        exact ⟨τ g * τ h, hmulL, hne', hsq, hcard⟩
      · have hmove : τ h (u g) = u g * u h := by
          rcases (hrep h).2.2.2.2 (u g) with e | e
          · exact absurd e h2
          · exact e
        have hmulL : τ h * τ g ∈ L := by
          simpa [τ] using conj_mul_conj_mem hσN hσ2 h g
        have ht1 := IsTransvCentred.sq_mul_ne_one hV (hrep h) (hrep g) hmove hfix
        have htsq := IsTransvCentred.sq_mul_mul_self hV (hrep h) (hrep g) hmove hfix
        have hcard := card_le_two_mul_card_fix_sq hV (hrep h) (hrep g) hmove hfix
        have hcard' : Nat.card V ≤ 4 * Nat.card
            (fixV (Subgroup.zpowers ((τ h * τ g) * (τ h * τ g)))) :=
          hcard.trans (Nat.mul_le_mul_right _ (by norm_num : 2 ≤ 4))
        exact ⟨_, L.mul_mem hmulL hmulL, ht1, htsq, hcard'⟩
    · by_cases h1 : τ g (u h) = u h
      · have hcomm := (hrep g).mul_comm_of_fixes (hrep h) h1 hfix
        have hmulL : τ g * τ h ∈ L := by
          simpa [τ] using conj_mul_conj_mem hσN hσ2 g h
        have hne' : τ g * τ h ≠ 1 := (hrep g).mul_ne_one_of_ne (hrep h) hne
        have hsq := (hrep g).mul_mul_self_of_comm (hrep h) hcomm
        have hcard := card_le_four_mul_card_fix_mul hV (hrep g) (hrep h) h1 hfix hne
        exact ⟨τ g * τ h, hmulL, hne', hsq, hcard⟩
      · have hmove : τ g (u h) = u h * u g := by
          rcases (hrep g).2.2.2.2 (u h) with e | e
          · exact absurd e h1
          · exact e
        have hmulL : τ g * τ h ∈ L := by
          simpa [τ] using conj_mul_conj_mem hσN hσ2 g h
        have ht1 := IsTransvCentred.sq_mul_ne_one hV (hrep g) (hrep h) hmove hfix
        have htsq := IsTransvCentred.sq_mul_mul_self hV (hrep g) (hrep h) hmove hfix
        have hcard := card_le_two_mul_card_fix_sq hV (hrep g) (hrep h) hmove hfix
        have hcard' : Nat.card V ≤ 4 * Nat.card
            (fixV (Subgroup.zpowers ((τ g * τ h) * (τ g * τ h)))) :=
          hcard.trans (Nat.mul_le_mul_right _ (by norm_num : 2 ≤ 4))
        exact ⟨_, L.mul_mem hmulL hmulL, ht1, htsq, hcard'⟩
  · have hboth : ∀ g h : ↥L, τ g ≠ τ h →
        τ g (u h) ≠ u h ∧ τ h (u g) ≠ u g := by
      intro g h hne
      constructor
      · intro hcon
        exact hcase ⟨g, h, hne, Or.inl hcon⟩
      · intro hcon
        exact hcase ⟨g, h, hne, Or.inr hcon⟩
    have hrel : ∀ g h : ↥L, τ g ≠ τ h → τ g (u h) = u h * u g := by
      intro g h hne
      rcases (hrep g).2.2.2.2 (u h) with e | e
      · exact absurd e (hboth g h hne).1
      · exact e
    have hconjD : ∀ g h : ↥L, ∃ k : ↥L, τ k = τ g * τ h * (τ g)⁻¹ := by
      intro g h
      obtain ⟨k, hk⟩ := exists_conj_mul_conj hσN hσ2 g h
      exact ⟨k, by simpa [τ] using hk.symm⟩
    let S : Subgroup V :=
      { carrier := {v | v = 1 ∨ ∃ g : ↥L, u g = v}
        one_mem' := Or.inl rfl
        mul_mem' := by
          intro x y hx hy
          rcases hx with rfl | ⟨g, rfl⟩
          · simpa using hy
          rcases hy with rfl | ⟨h, rfl⟩
          · exact Or.inr ⟨g, by rw [mul_one]⟩
          by_cases hne : τ g = τ h
          · have hugh : u g = u h := (hrep g).center_unique (hne ▸ hrep h)
            exact Or.inl (by rw [hugh, hV (u h)])
          · obtain ⟨k, hk⟩ := hconjD g h
            have hcentre : IsTransvCentred (τ g * τ h * (τ g)⁻¹) (τ g (u h)) :=
              (hrep h).conj (τ g)
            rw [← hk] at hcentre
            have huk : τ g (u h) = u k := ((hrep k).center_unique hcentre).symm
            refine Or.inr ⟨k, ?_⟩
            calc u k = τ g (u h) := huk.symm
              _ = u h * u g := hrel g h hne
              _ = u g * u h := mul_comm _ _
        inv_mem' := by
          intro x hx
          rcases hx with rfl | ⟨g, rfl⟩
          · exact Or.inl (inv_one)
          · exact Or.inr ⟨g, (inv_eq_of_mul_eq_one_right (hV (u g))).symm⟩ }
    have hSinv : ∀ l ∈ L, ∀ v ∈ S, (l : MulAut V) v ∈ S := by
      intro l hl v hv
      rcases hv with rfl | ⟨g, rfl⟩
      · exact Or.inl (map_one _)
      · exact Or.inr ⟨⟨(l : MulAut V) * (g : MulAut V), L.mul_mem hl g.2⟩, rfl⟩
    have hSne : S ≠ ⊥ := by
      intro hbot
      have hmem : u₀ ∈ (⊥ : Subgroup V) := by
        rw [← hbot]
        exact Or.inr ⟨1, rfl⟩
      rw [Subgroup.mem_bot] at hmem
      exact hσrep.2.2.1 hmem
    have hStop : S = ⊤ := (hirr.2 S hSinv).resolve_left hSne
    have hfix_le : fixV (Subgroup.zpowers σ) ≤ Subgroup.zpowers u₀ := by
      intro v hv
      rw [mem_fixV_zpowers_iff_apply] at hv
      by_contra hnot
      have hv1 : v ≠ 1 := fun h => hnot (h ▸ Subgroup.one_mem _)
      have hvu : v ≠ u₀ := fun h => hnot (h ▸ Subgroup.mem_zpowers u₀)
      have hvS : v ∈ S := by rw [hStop]; exact Subgroup.mem_top v
      rcases hvS with rfl | ⟨g, hg⟩
      · exact hv1 rfl
      · by_cases hg1 : τ g = τ (1 : ↥L)
        · have hu_eq : u g = u (1 : ↥L) := (hrep g).center_unique (hg1 ▸ hrep 1)
          apply hvu
          have hu1 : u (1 : ↥L) = u₀ := rfl
          rw [← hg, hu_eq, hu1]
        · have hmove : τ (1 : ↥L) (u g) = u g * u (1 : ↥L) :=
            hrel (1 : ↥L) g (Ne.symm hg1)
          have hσv : σ v = v * u₀ := by
            rw [← hg]
            have hτ1 : τ (1 : ↥L) = σ := by simp [τ]
            have hu1 : u (1 : ↥L) = u₀ := rfl
            rw [hτ1, hu1] at hmove
            exact hmove
          rw [hv] at hσv
          exact hσrep.2.2.1 (mul_left_cancel (by rw [← hσv, mul_one]))
    have hfixcard : Nat.card (fixV (Subgroup.zpowers σ)) ≤ 2 := by
      calc Nat.card (fixV (Subgroup.zpowers σ)) ≤ Nat.card (Subgroup.zpowers u₀) :=
            Subgroup.card_le_of_le hfix_le
        _ = 2 := by
            rw [Nat.card_zpowers,
              orderOf_eq_prime (by rw [pow_two]; exact hV u₀) hσrep.2.2.1]
    have hV4 : Nat.card V ≤ 4 := by
      calc Nat.card V ≤ 2 * Nat.card (fixV (Subgroup.zpowers σ)) := hσV
        _ ≤ 2 * 2 := Nat.mul_le_mul_left _ hfixcard
        _ = 4 := by norm_num
    have hPerm : Group.IsSolvable (Equiv.Perm V) := Equiv.Perm.isSolvable (by simpa using hV4)
    have hAutSolv : Group.IsSolvable (MulAut V) := by
      haveI := hPerm
      refine Group.isSolvable_of_isSolvable_injective (f := MulAut.toPerm (M := V)) ?_
      intro f g hfg
      ext v
      exact congrArg (fun e : Equiv.Perm V => e v) hfg
    have hLsolv : Group.IsSolvable ↥L := by
      haveI := hAutSolv
      infer_instance
    have hLbot : L = ⊥ := by
      by_contra hne
      haveI : Nontrivial ↥L := (Subgroup.nontrivial_iff_ne_bot L).mpr hne
      exact Group.IsPerfect.not_isSolvable ↥L hLsolv
    have hσcent : σ ∈ Subgroup.centralizer (L : Set (MulAut V)) := by
      rw [hLbot, Subgroup.mem_centralizer_iff]
      intro l hl
      have hl' : l = 1 := by simpa using hl
      rw [hl']
      simp
    exact absurd hσcent hσL

end CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
