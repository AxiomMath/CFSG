module

public import CFSG.Milestones.OO_odd_order_solvable
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

theorem mulAut_conj_apply_eq {Y : Type*} [Group Y] (φ : MulAut Y) (y : Y) :
    MulAut.conj (φ y) = φ * MulAut.conj y * φ⁻¹ := by
  ext z
  simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

theorem mulAut_conj_commute_of_fixed {Y : Type*} [Group Y] {x : MulAut Y} {c : Y} (hc : x c = c) :
    MulAut.conj c * x = x * MulAut.conj c := by
  have h := mulAut_conj_apply_eq x c
  rw [hc] at h
  calc MulAut.conj c * x = x * MulAut.conj c * x⁻¹ * x := by rw [← h]
    _ = x * MulAut.conj c := by group

theorem hypOneStar_at_of_simple_fixed {Y : Type*} [Group Y] [Finite Y] {x u : MulAut Y}
    (hx : orderOf x = 2) (hu : u ^ 2 = x) (J : Subgroup Y) (hJfix : ∀ y : Y, x y = y ↔ y ∈ J)
    (hJ : IsSimpleGroup J) (hJnab : ∃ a b : J, a * b ≠ b * a)
    (hJ2 : ∀ P : Subgroup (MulAut Y), IsPGroup 2 P → (∀ β ∈ P, ∀ j ∈ J, β j = j) →
      Nat.card P ≤ 2)
    {E : Subgroup (MulAut Y)} (hEodd : Odd (Nat.card E)) (hEu : ∀ e ∈ E, u * e * u⁻¹ ∈ E)
    (hEJ : ∀ c ∈ J, ∀ e ∈ E, MulAut.conj c * e * (MulAut.conj c)⁻¹ ∈ E) :
    ∃ c ∈ J, MulAut.conj c * u * (MulAut.conj c)⁻¹ ∉ E ⊔ zpowers u := by
  classical
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  set H : Subgroup (MulAut Y) := E ⊔ zpowers u with hH
  set ι : Y →* MulAut Y := MulAut.conj with hι
  have hEH : E ≤ H := le_sup_left
  have huH : u ∈ H := (le_sup_right : zpowers u ≤ H) (mem_zpowers u)
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hu4 : u ^ 4 = 1 := by rw [show 4 = 2 * 2 from rfl, pow_mul, hu, hx2]
  have hu_ord : orderOf u = 4 := by
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := u)
      (by rw [pow_one, hu]; exact hx1) (by rw [show 2 ^ (1 + 1) = 4 from rfl]; exact hu4)
    rw [h]
    rfl
  have hxu : x * u = u * x := by
    rw [← hu]
    exact ((Commute.refl u).pow_left 2).eq
  have huJ : ∀ j ∈ J, u j ∈ J := by
    intro j hj
    rw [← hJfix] at hj ⊢
    have h := congrArg (fun φ : MulAut Y => φ j) hxu
    simp only [MulAut.mul_apply] at h
    rw [h, hj]
  have hιJ : ∀ c ∈ J, ι c = 1 → c = 1 := by
    have hker : (ι.comp J.subtype).ker = ⊥ := by
      rcases (MonoidHom.normal_ker (ι.comp J.subtype)).eq_bot_or_eq_top with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := hJnab
        apply hab
        have ha : a ∈ (ι.comp J.subtype).ker := h ▸ mem_top a
        rw [MonoidHom.mem_ker] at ha
        have hb := congrArg (fun φ : MulAut Y => φ (b : Y)) ha
        simp only [hι, MonoidHom.comp_apply, coe_subtype, MulAut.conj_apply,
          MulAut.one_apply] at hb
        apply Subtype.ext
        simp only [coe_mul]
        calc (a : Y) * b = a * b * (a : Y)⁻¹ * a := by group
          _ = b * a := by rw [hb]
    intro c hc h1
    have hmem : (⟨c, hc⟩ : J) ∈ (ι.comp J.subtype).ker := by
      rw [MonoidHom.mem_ker]
      exact h1
    rw [hker, mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hnorm : ∀ c ∈ J, ∀ h ∈ H, ι c * h * (ι c)⁻¹ ∈ H := by
    intro c hc
    have hle : H ≤ H.comap (MulAut.conj (ι c)).toMonoidHom := by
      apply sup_le
      · intro e he
        rw [mem_comap]
        exact hEH (hEJ c hc e he)
      · rw [zpowers_le, mem_comap]
        exact hcon c hc
    intro h hh
    exact hle hh
  set D : Subgroup J := H.comap (ι.comp J.subtype) with hD
  have hDn : D.Normal := by
    constructor
    intro n hn g
    rw [mem_comap] at hn ⊢
    simp only [MonoidHom.comp_apply, coe_subtype, map_mul, map_inv] at hn ⊢
    exact hnorm g g.2 _ hn
  have : IsSimpleGroup J := hJ
  rcases hDn.eq_bot_or_eq_top with hbot | htop
  ·
    have hfixJ : ∀ c ∈ J, u c = c := by
      intro c hc
      have hmem : (⟨c * (u c)⁻¹, mul_mem hc (inv_mem (huJ c hc))⟩ : J) ∈ D := by
        rw [mem_comap]
        change ι (c * (u c)⁻¹) ∈ H
        rw [map_mul, map_inv, hι, mulAut_conj_apply_eq]
        have h1 : MulAut.conj c * (u * MulAut.conj c * u⁻¹)⁻¹ =
            MulAut.conj c * u * (MulAut.conj c)⁻¹ * u⁻¹ := by group
        rw [h1]
        exact mul_mem (hcon c hc) (inv_mem huH)
      rw [hbot, mem_bot] at hmem
      have h2 : c * (u c)⁻¹ = 1 := congrArg Subtype.val hmem
      exact (mul_inv_eq_one.mp h2).symm
    let F : Subgroup (MulAut Y) :=
      { carrier := {β | ∀ j ∈ J, β j = j}
        mul_mem' := fun {β γ} hβ hγ j hj => by rw [MulAut.mul_apply, hγ j hj, hβ j hj]
        one_mem' := fun j _ => rfl
        inv_mem' := fun {β} hβ j hj => by
          rw [MulAut.inv_apply, MulEquiv.symm_apply_eq, hβ j hj] }
    have huF : u ∈ F := hfixJ
    have hcard : Nat.card (zpowers u) = 2 ^ 2 := by rw [Nat.card_zpowers, hu_ord]; rfl
    have h2 := hJ2 (zpowers u) (IsPGroup.of_card hcard) fun β hβ => (zpowers_le.mpr huF) hβ
    rw [hcard] at h2
    exact absurd h2 (by norm_num)
  ·
    have hJH : ∀ c : J, ι c ∈ H := fun c => by
      have hc : c ∈ D := htop ▸ mem_top c
      exact hc
    set D' : Subgroup J := E.comap (ι.comp J.subtype) with hD'
    have hD'n : D'.Normal := by
      constructor
      intro n hn g
      rw [mem_comap] at hn ⊢
      simp only [MonoidHom.comp_apply, coe_subtype, map_mul, map_inv] at hn ⊢
      exact hEJ g g.2 _ hn
    rcases hD'n.eq_bot_or_eq_top with hbot' | htop'
    ·
      have hpow : ∀ n : ℕ, ∀ e ∈ E, u ^ n * e * (u ^ n)⁻¹ ∈ E := by
        intro n
        induction n with
        | zero => intro e he; simpa using he
        | succ n ih =>
          intro e he
          have h1 : u ^ (n + 1) * e * (u ^ (n + 1))⁻¹ = u ^ n * (u * e * u⁻¹) * (u ^ n)⁻¹ := by
            rw [pow_succ]; group
          rw [h1]
          exact ih _ (hEu e he)
      have huN : u ∈ normalizer (E : Set (MulAut Y)) := by
        rw [mem_normalizer_iff]
        intro h
        refine ⟨hEu h, fun hh => ?_⟩
        have hu3 : u⁻¹ = u ^ 3 := by
          rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ]
          exact hu4
        have key : h = u ^ 3 * (u * h * u⁻¹) * (u ^ 3)⁻¹ := by rw [← hu3]; group
        rw [key]
        exact hpow 3 _ hh
      set N : Subgroup (MulAut Y) := normalizer (E : Set (MulAut Y)) with hN
      have hEN : (E.subgroupOf N).Normal := Subgroup.normal_in_normalizer
      let π : N →* N ⧸ E.subgroupOf N := QuotientGroup.mk' (E.subgroupOf N)
      have hπ : ∀ n : N, π n = 1 ↔ (n : MulAut Y) ∈ E := by
        intro n
        rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk', mem_subgroupOf]
      have hW : H ≤ ((zpowers (π ⟨u, huN⟩)).comap π).map N.subtype := by
        apply sup_le
        · intro e he
          refine ⟨⟨e, le_normalizer he⟩, ?_, rfl⟩
          rw [SetLike.mem_coe, mem_comap, (hπ ⟨e, le_normalizer he⟩).mpr he]
          exact one_mem _
        · rw [zpowers_le]
          exact ⟨⟨u, huN⟩, mem_zpowers _, rfl⟩
      have hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b * a⁻¹ * b⁻¹ ∈ E := by
        intro a ha b hb
        obtain ⟨a', ha', rfl⟩ := hW ha
        obtain ⟨b', hb', rfl⟩ := hW hb
        rw [SetLike.mem_coe, mem_comap] at ha' hb'
        obtain ⟨m, hm⟩ := mem_zpowers_iff.mp ha'
        obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hb'
        have h1 : π (a' * b' * a'⁻¹ * b'⁻¹) = 1 := by
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hm, ← hn,
            (Commute.zpow_zpow_self _ m n).eq]
          group
        have h2 := (hπ _).mp h1
        simpa using h2
      obtain ⟨a, b, hab⟩ := hJnab
      apply hab
      have hmem : a * b * a⁻¹ * b⁻¹ ∈ D' := by
        rw [mem_comap]
        simp only [MonoidHom.comp_apply, coe_subtype, map_mul, map_inv]
        exact hcomm _ (hJH a) _ (hJH b)
      rw [hbot', mem_bot] at hmem
      calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
        _ = b * a := by rw [hmem, one_mul]
    ·
      have hJE : ∀ c : J, (ι.comp J.subtype) c ∈ E := fun c => by
        have hc : c ∈ D' := htop' ▸ mem_top c
        exact hc
      let φ : J →* E := (ι.comp J.subtype).codRestrict E hJE
      have hφ : Function.Injective φ := by
        rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
        intro c hc
        rw [MonoidHom.mem_ker] at hc
        have h1 : ι c = 1 := congrArg Subtype.val hc
        rw [mem_bot]
        exact Subtype.ext (hιJ c c.2 h1)
      have hJodd : Odd (Nat.card J) := Odd.of_dvd_nat hEodd (Subgroup.card_dvd_of_injective φ hφ)
      have hsolv := CFSG.Milestones.odd_order_solvable hJodd
      obtain ⟨a, b, hab⟩ := hJnab
      exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv a b)

theorem hypOneStar_exists_of_simple_fixed {Y : Type*} [Group Y] [Finite Y] {x u : MulAut Y}
    (hx : orderOf x = 2) (hu : u ^ 2 = x) (J : Subgroup Y) (hJfix : ∀ y : Y, x y = y ↔ y ∈ J)
    (hJ : IsSimpleGroup J) (hJnab : ∃ a b : J, a * b ≠ b * a)
    (hJ2 : ∀ P : Subgroup (MulAut Y), IsPGroup 2 P → (∀ β ∈ P, ∀ j ∈ J, β j = j) →
      Nat.card P ≤ 2)
    {E : Subgroup (MulAut Y)} (hEodd : Odd (Nat.card E)) (hEu : ∀ e ∈ E, u * e * u⁻¹ ∈ E)
    (hE : ∀ c : Y, MulAut.conj c * x = x * MulAut.conj c →
      ∀ e ∈ E, MulAut.conj c * e * (MulAut.conj c)⁻¹ ∈ E) :
    ∃ c : Y, MulAut.conj c * x = x * MulAut.conj c ∧
      MulAut.conj c * u * (MulAut.conj c)⁻¹ ∉ E ⊔ zpowers u := by
  obtain ⟨c, hc, hcu⟩ := hypOneStar_at_of_simple_fixed hx hu J hJfix hJ hJnab hJ2 hEodd hEu
    fun c hc => hE c (mulAut_conj_commute_of_fixed ((hJfix c).mpr hc))
  exact ⟨c, mulAut_conj_commute_of_fixed ((hJfix c).mpr hc), hcu⟩

end CFSG.SeitzReduction.RankOne
