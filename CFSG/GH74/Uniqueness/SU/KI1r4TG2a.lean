module

public import CFSG.GH74.Uniqueness.SU.KI1r4TG1

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4

open Subgroup CFSG CFSG.GH74.Uniqueness.SU

variable {H : Type} [Group H] [Finite H]

omit [Finite H] in
theorem mem_or_mul_mem_of_mem_sup_zpowers_norm {R : Subgroup H} {x : H} (hx : x * x = 1)
    (hxn : ∀ r ∈ R, x * r * x⁻¹ ∈ R) {t : H} (ht : t ∈ R ⊔ zpowers x) :
    t ∈ R ∨ x * t ∈ R := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hxn' : ∀ r ∈ R, x * r * x ∈ R := fun r hr => by simpa [hxi] using hxn r hr
  let S : Subgroup H :=
    { carrier := {t | t ∈ R ∨ x * t ∈ R}
      one_mem' := Or.inl R.one_mem
      mul_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · exact Or.inl (R.mul_mem ha hb)
        · right
          have h : x * (a * b) = (x * a * x) * (x * b) := by
            calc x * (a * b) = x * a * 1 * b := by group
              _ = x * a * (x * x) * b := by rw [hx]
              _ = (x * a * x) * (x * b) := by group
          rw [h]
          exact R.mul_mem (hxn' a ha) hb
        · right
          rw [← mul_assoc]
          exact R.mul_mem ha hb
        · left
          have h : a * b = (x * (x * a) * x) * (x * b) := by
            calc a * b = (x * x) * a * 1 * b := by rw [hx]; group
              _ = (x * x) * a * (x * x) * b := by rw [hx]
              _ = (x * (x * a) * x) * (x * b) := by group
          rw [h]
          exact R.mul_mem (hxn' _ ha) hb
      inv_mem' := by
        rintro t (ht | ht)
        · exact Or.inl (R.inv_mem ht)
        · right
          have h : x * t⁻¹ = x * (x * t)⁻¹ * x := by group
          rw [h]
          exact hxn' _ (R.inv_mem ht) }
  have hSmem : ∀ t, t ∈ S ↔ t ∈ R ∨ x * t ∈ R := fun t => Iff.rfl
  have hle : R ⊔ zpowers x ≤ S := by
    refine sup_le (fun r hr => (hSmem r).mpr (Or.inl hr)) ?_
    rw [Subgroup.zpowers_le, hSmem]
    exact Or.inr (by rw [hx]; exact R.one_mem)
  exact (hSmem t).mp (hle ht)

theorem card_le_two_mul_inf_of_mul_mem {R E : Subgroup H} {x : H}
    (hE : ∀ e ∈ E, e ∈ R ∨ x * e ∈ R) : Nat.card E ≤ 2 * Nat.card ↥(E ⊓ R) := by
  by_cases hER : E ≤ R
  · rw [inf_eq_left.mpr hER]
    omega
  · obtain ⟨e0, he0E, he0R⟩ := IsConcreteLE.not_le_iff_exists.mp hER
    have hx0 : x * e0 ∈ R := (hE e0 he0E).resolve_left he0R
    let f : ↥(E ⊓ R) × Bool → ↥E := fun p =>
      if p.2 then ⟨e0 * p.1, E.mul_mem he0E (Subgroup.mem_inf.mp p.1.2).1⟩
      else ⟨p.1, (Subgroup.mem_inf.mp p.1.2).1⟩
    have hf : Function.Surjective f := by
      rintro ⟨e, heE⟩
      by_cases heR : e ∈ R
      · exact ⟨(⟨e, heE, heR⟩, false), rfl⟩
      · have hxe : x * e ∈ R := (hE e heE).resolve_left heR
        have hmem : e0⁻¹ * e ∈ E ⊓ R := by
          refine ⟨E.mul_mem (E.inv_mem he0E) heE, ?_⟩
          have h : e0⁻¹ * e = (x * e0)⁻¹ * (x * e) := by group
          rw [h]
          exact R.mul_mem (R.inv_mem hx0) hxe
        refine ⟨(⟨e0⁻¹ * e, hmem⟩, true), ?_⟩
        apply Subtype.ext
        simp [f]
    calc Nat.card E ≤ Nat.card (↥(E ⊓ R) × Bool) := Nat.card_le_card_of_surjective f hf
      _ = 2 * Nat.card ↥(E ⊓ R) := by
        rw [Nat.card_prod]
        simp [mul_comm]

theorem card_sq_eq_one_le_four_of_sup_zpowers {G : Type*} [Group G] [Finite G]
    (hcomm : ∀ a b : G, a * b = b * a) {c d : G} (hgen : zpowers c ⊔ zpowers d = ⊤) :
    Nat.card {g : G // g * g = 1} ≤ 4 := by
  let _ : CommGroup G := { ‹Group G› with mul_comm := hcomm }
  let φ : G →* G := powMonoidHom 2
  have h1 : Nat.card φ.ker * Nat.card φ.range = Nat.card G :=
    Subgroup.card_ker_mul_card_range φ
  have hpar : ∀ (a : G) (i : ℤ), ∃ (b : Bool) (q : ℤ),
      a ^ i = (if b then a else 1) * (a ^ q) ^ 2 := by
    intro a i
    obtain ⟨q, hq | hq⟩ := Int.even_or_odd' i
    · refine ⟨false, q, ?_⟩
      rw [hq, zpow_mul']
      simp
    · refine ⟨true, q, ?_⟩
      rw [hq, zpow_add, zpow_mul']
      simp [mul_comm]
  have h2 : Nat.card G ≤ 4 * Nat.card φ.range := by
    let f : (Bool × Bool) × φ.range → G := fun p =>
      (if p.1.1 then c else 1) * (if p.1.2 then d else 1) * (p.2 : G)
    have hf : Function.Surjective f := by
      intro g
      have hg : g ∈ zpowers c ⊔ zpowers d := hgen ▸ Subgroup.mem_top g
      obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hg
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      obtain ⟨b1, q, hq⟩ := hpar c i
      obtain ⟨b2, p, hp⟩ := hpar d j
      refine ⟨((b1, b2), φ.rangeRestrict (c ^ q * d ^ p)), ?_⟩
      have hs : ((φ.rangeRestrict (c ^ q * d ^ p) : φ.range) : G) = (c ^ q) ^ 2 * (d ^ p) ^ 2 := by
        show (c ^ q * d ^ p) ^ 2 = _
        rw [mul_pow]
      show _ * _ * ((φ.rangeRestrict (c ^ q * d ^ p) : φ.range) : G) = _
      rw [hs, hq, hp]
      exact (mul_mul_mul_comm _ _ _ _).symm
    calc Nat.card G ≤ Nat.card ((Bool × Bool) × φ.range) := Nat.card_le_card_of_surjective f hf
      _ = 4 * Nat.card φ.range := by simp [Nat.card_prod]
  have h3 : 0 < Nat.card φ.range := Nat.card_pos
  have h4 : Nat.card φ.ker ≤ 4 := by
    by_contra h
    push Not at h
    nlinarith
  have h5 : Nat.card {g : G // g * g = 1} = Nat.card φ.ker :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => by
      simp [φ, MonoidHom.mem_ker, pow_two])
  rw [h5]
  exact h4

theorem card_inf_le_four_of_abelian_two_gen {R : Subgroup H}
    (hab : ∀ r ∈ R, ∀ s ∈ R, r * s = s * r) {c d : H} (hc : c ∈ R) (hd : d ∈ R)
    (hgen : zpowers c ⊔ zpowers d = R) {E : Subgroup H} (hE : ∀ e ∈ E, e * e = 1) :
    Nat.card ↥(E ⊓ R) ≤ 4 := by
  have hcomm : ∀ a b : ↥R, a * b = b * a := fun a b => Subtype.ext (hab a a.2 b b.2)
  have hgen' : zpowers (⟨c, hc⟩ : ↥R) ⊔ zpowers (⟨d, hd⟩ : ↥R) = ⊤ := by
    apply Subgroup.map_injective R.subtype_injective
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
    exact hgen
  have h4 := card_sq_eq_one_le_four_of_sup_zpowers hcomm hgen'
  let g : ↥(E ⊓ R) → {z : ↥R // z * z = 1} := fun k =>
    ⟨⟨k, (Subgroup.mem_inf.mp k.2).2⟩, Subtype.ext (hE k (Subgroup.mem_inf.mp k.2).1)⟩
  have hg : Function.Injective g := fun a b hab' =>
    Subtype.ext (congrArg (fun z => ((z.1 : ↥R) : H)) hab')
  exact (Nat.card_le_card_of_injective g hg).trans h4

theorem RData.pRank_T_le_three {T : Sylow 2 H} {x : H} {A R : Subgroup H} {y : H}
    (hR : RData T x A R y) (hab : ∀ r ∈ R, ∀ s ∈ R, r * s = s * r)
    (hgen : ∃ c ∈ R, Subgroup.zpowers c ⊔ Subgroup.zpowers (y * c * y⁻¹) = R) :
    Open.pRank 2 (T : Subgroup H) ≤ 3 := by
  obtain ⟨c, hcR, hcgen⟩ := hgen
  have hdR : y * c * y⁻¹ ∈ R := hR.y_norm c hcR
  have hTR : ∀ t ∈ (T : Subgroup H), t ∈ R ∨ x * t ∈ R := fun t ht =>
    mem_or_mul_mem_of_mem_sup_zpowers_norm hR.x_sq hR.x_norm (by rwa [← hR.T_eq])
  refine SU1.pRank_le_of fun E hET hE k hk => ?_
  have hsq : ∀ e ∈ E, e * e = 1 := fun e he => by
    have := (SU1.isElemAbelian_iff.mp hE).2 e he
    rwa [pow_two] at this
  have h1 : Nat.card E ≤ 2 * Nat.card ↥(E ⊓ R) :=
    card_le_two_mul_inf_of_mul_mem fun e he => hTR e (hET he)
  have h2 : Nat.card ↥(E ⊓ R) ≤ 4 :=
    card_inf_le_four_of_abelian_two_gen hab hcR hdR hcgen hsq
  by_contra hk3
  push Not at hk3
  have h4 : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
  rw [← hk] at h4
  omega

end CFSG.GH74.Uniqueness.SU.K.R4
