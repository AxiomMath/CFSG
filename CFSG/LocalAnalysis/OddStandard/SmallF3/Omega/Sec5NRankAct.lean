module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5NRankPerm

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem nr_comm_cases {G : Type} [Group G] {x y a b z : G} (hzx : x * z = z * x)
    (hzy : y * z = z * y) (ha : a = x ∨ a = x * z) (hb : b = y ∨ b = y * z) :
    a * b * a⁻¹ * b⁻¹ = x * y * x⁻¹ * y⁻¹ := by
  have hzx' : x⁻¹ * z = z * x⁻¹ := by
    calc x⁻¹ * z = x⁻¹ * (z * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * z) * x⁻¹ := by rw [hzx]
      _ = z * x⁻¹ := by group
  have hzy' : z * y = y * z := hzy.symm
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb]
  · calc x * (y * z) * x⁻¹ * (y * z)⁻¹ = x * y * (z * x⁻¹) * z⁻¹ * y⁻¹ := by group
      _ = x * y * (x⁻¹ * z) * z⁻¹ * y⁻¹ := by rw [hzx']
      _ = x * y * x⁻¹ * y⁻¹ := by group
  · calc x * z * y * (x * z)⁻¹ * y⁻¹ = x * (z * y) * z⁻¹ * x⁻¹ * y⁻¹ := by group
      _ = x * (y * z) * z⁻¹ * x⁻¹ * y⁻¹ := by rw [hzy']
      _ = x * y * x⁻¹ * y⁻¹ := by group
  · calc x * z * (y * z) * (x * z)⁻¹ * (y * z)⁻¹ = x * (z * y) * x⁻¹ * z⁻¹ * y⁻¹ := by group
      _ = x * (y * z) * x⁻¹ * z⁻¹ * y⁻¹ := by rw [hzy']
      _ = x * y * (z * x⁻¹) * z⁻¹ * y⁻¹ := by group
      _ = x * y * (x⁻¹ * z) * z⁻¹ * y⁻¹ := by rw [hzx']
      _ = x * y * x⁻¹ * y⁻¹ := by group

variable {G : Type} [Group G] (Ψ : SL2F3 × SL2F3 →* G)

@[expose] def NrKer : Prop := ∀ p : SL2F3 × SL2F3, Ψ p = 1 ↔ p = 1 ∨ p = nrK

@[expose] def nrQ : Subgroup G := (q8SL.prod q8SL).map Ψ

@[expose] def nrzG : G := Ψ nrZ

@[expose] def nrqG (s : Bool × Fin 3) : G := Ψ (nrCls s)

theorem mem_nrQ {x : G} : x ∈ nrQ Ψ ↔ ∃ p : SL2F3 × SL2F3, IsQ8P p ∧ Ψ p = x := by
  unfold nrQ
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, rfl⟩

theorem map_mem_nrQ {p : SL2F3 × SL2F3} (hp : IsQ8P p) : Ψ p ∈ nrQ Ψ :=
  (mem_nrQ Ψ).mpr ⟨p, hp, rfl⟩

theorem nrMap_cls_mul (s : Bool × Fin 3) (a : Bool) :
    Ψ (nrCls s * (if a then nrZ else 1)) = nrqG Ψ s * (if a then nrzG Ψ else 1) := by
  cases a <;> simp [nrqG, nrzG, map_mul]

variable {Ψ}

theorem NrKer.map_nrK (h : NrKer Ψ) : Ψ nrK = 1 := (h nrK).mpr (Or.inr rfl)

theorem NrKer.map_eq (h : NrKer Ψ) {p q : SL2F3 × SL2F3} (hpq : NrEq p q) : Ψ p = Ψ q := by
  rcases hpq with rfl | rfl
  · rfl
  · rw [map_mul, h.map_nrK, mul_one]

theorem NrKer.eq_of_map (h : NrKer Ψ) {p q : SL2F3 × SL2F3} (hpq : Ψ p = Ψ q) : NrEq p q := by
  have h1 : Ψ (p * q⁻¹) = 1 := by rw [map_mul, map_inv, hpq, mul_inv_cancel]
  rcases (h _).mp h1 with h2 | h2
  · exact Or.inl (mul_inv_eq_one.mp h2)
  · refine Or.inr ?_
    rw [← nrK_mul_comm q]
    exact mul_inv_eq_iff_eq_mul.mp h2

theorem nrzG_mul_self : nrzG Ψ * nrzG Ψ = 1 := by
  rw [nrzG, ← map_mul, nrZ_mul_self, map_one]

theorem NrKer.nrzG_ne_one (h : NrKer Ψ) : nrzG Ψ ≠ 1 := by
  intro h1
  rcases (h nrZ).mp h1 with h2 | h2
  · exact nrZ_ne_one h2
  · exact nrZ_ne_nrK h2

theorem nrzG_mem : nrzG Ψ ∈ nrQ Ψ := map_mem_nrQ Ψ isQ8P_nrZ

theorem nrzG_comm {x : G} (hx : x ∈ nrQ Ψ) : x * nrzG Ψ = nrzG Ψ * x := by
  obtain ⟨p, -, rfl⟩ := (mem_nrQ Ψ).mp hx
  rw [nrzG, ← map_mul, ← map_mul, ← nrZ_mul_comm p]

theorem nrqG_mem (s : Bool × Fin 3) : nrqG Ψ s ∈ nrQ Ψ := map_mem_nrQ Ψ (isQ8P_nrCls s)

theorem NrKer.nrqG_sq (h : NrKer Ψ) (s : Bool × Fin 3) : nrqG Ψ s * nrqG Ψ s = nrzG Ψ := by
  rw [nrqG, ← map_mul]
  exact h.map_eq (sec5nr_sq_cls s)

theorem NrKer.nrqG_comm (h : NrKer Ψ) (s t : Bool × Fin 3) :
    nrqG Ψ s * nrqG Ψ t * (nrqG Ψ s)⁻¹ * (nrqG Ψ t)⁻¹ = if NrR s t then nrzG Ψ else 1 := by
  have h1 := h.map_eq (sec5nr_comm_cls s t)
  simp only [map_mul, map_inv] at h1
  by_cases hst : NrR s t
  · rw [if_pos hst]
    rw [if_pos hst] at h1
    exact h1
  · rw [if_neg hst]
    rw [if_neg hst] at h1
    simpa [nrqG] using h1

theorem NrKer.rel_unique (h : NrKer Ψ) {x : G} {t t' : Bool × Fin 3}
    (h1 : x = nrqG Ψ t ∨ x = nrqG Ψ t * nrzG Ψ) (h2 : x = nrqG Ψ t' ∨ x = nrqG Ψ t' * nrzG Ψ) :
    t = t' := by
  have key : ∀ {u : Bool × Fin 3}, (x = nrqG Ψ u ∨ x = nrqG Ψ u * nrzG Ψ) →
      ∃ a : Bool, x = Ψ (nrCls u * (if a then nrZ else 1)) := by
    intro u hu
    rcases hu with hu | hu
    · exact ⟨false, by rw [nrMap_cls_mul]; simpa using hu⟩
    · exact ⟨true, by rw [nrMap_cls_mul]; simpa using hu⟩
  obtain ⟨a, ha⟩ := key h1
  obtain ⟨b, hb⟩ := key h2
  exact sec5nr_distinct t t' a b (h.eq_of_map (ha.symm.trans hb))

structure NrSetting (Ψ : SL2F3 × SL2F3 →* G) (E : Subgroup G) : Prop where
  ker : NrKer Ψ
  norm : ∀ e ∈ E, ∀ x ∈ nrQ Ψ, e * x * e⁻¹ ∈ nrQ Ψ

variable {E : Subgroup G} (S : NrSetting Ψ E)

include S

theorem NrSetting.fix_z {e : G} (he : e ∈ E) : e * nrzG Ψ * e⁻¹ = nrzG Ψ := by
  have hg : e * nrzG Ψ * e⁻¹ ∈ nrQ Ψ := S.norm e he _ nrzG_mem
  obtain ⟨p, -, hpg⟩ := (mem_nrQ Ψ).mp hg
  have hcomm : ∀ x ∈ nrQ Ψ, (e * nrzG Ψ * e⁻¹) * x = x * (e * nrzG Ψ * e⁻¹) := by
    intro x hx
    have hx' : e⁻¹ * x * e ∈ nrQ Ψ := by
      have := S.norm e⁻¹ (E.inv_mem he) x hx
      simpa using this
    have hzx := nrzG_comm hx'
    calc (e * nrzG Ψ * e⁻¹) * x = e * (nrzG Ψ * (e⁻¹ * x * e)) * e⁻¹ := by group
      _ = e * ((e⁻¹ * x * e) * nrzG Ψ) * e⁻¹ := by rw [← hzx]
      _ = x * (e * nrzG Ψ * e⁻¹) := by group
  have hcen : NrEq p 1 ∨ NrEq p nrZ ∨ NrEq p (1, sl2f3NegOne) := by
    refine sec5nr_center p (fun p' hp' => ?_)
    have hc := hcomm (Ψ p') (map_mem_nrQ Ψ hp')
    have h1 : Ψ (p * p' * p⁻¹ * p'⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hpg, mul_inv_eq_iff_eq_mul.mpr hc, mul_inv_cancel]
    rcases (S.ker _).mp h1 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (by rw [h2, one_mul])
  have hz1 := S.ker.nrzG_ne_one
  rcases hcen with h | h | h
  · exfalso
    have h0 : e * nrzG Ψ * e⁻¹ = 1 := by rw [← hpg, S.ker.map_eq h, map_one]
    apply hz1
    calc nrzG Ψ = e⁻¹ * (e * nrzG Ψ * e⁻¹) * e := by group
      _ = e⁻¹ * 1 * e := by rw [h0]
      _ = 1 := by group
  · rw [← hpg]
    exact S.ker.map_eq h
  · rw [← hpg]
    exact (S.ker.map_eq h).trans (S.ker.map_eq (Or.inr nrZ'_eq))

theorem NrSetting.rel_exists {e : G} (he : e ∈ E) (s : Bool × Fin 3) :
    ∃ t : Bool × Fin 3, e * nrqG Ψ s * e⁻¹ = nrqG Ψ t ∨
      e * nrqG Ψ s * e⁻¹ = nrqG Ψ t * nrzG Ψ := by
  have hx : e * nrqG Ψ s * e⁻¹ ∈ nrQ Ψ := S.norm e he _ (nrqG_mem s)
  obtain ⟨p, hp, hpx⟩ := (mem_nrQ Ψ).mp hx
  have hsq : Ψ (p * p) = nrzG Ψ := by
    rw [map_mul, hpx]
    calc e * nrqG Ψ s * e⁻¹ * (e * nrqG Ψ s * e⁻¹) = e * (nrqG Ψ s * nrqG Ψ s) * e⁻¹ := by group
      _ = nrzG Ψ := by rw [S.ker.nrqG_sq, S.fix_z he]
  obtain ⟨t, ht⟩ := sec5nr_classify p hp (S.ker.eq_of_map hsq)
  refine ⟨t, ?_⟩
  rcases ht with ht | ht
  · exact Or.inl (hpx.symm.trans (S.ker.map_eq ht))
  · exact Or.inr (hpx.symm.trans ((S.ker.map_eq ht).trans (map_mul Ψ _ _)))

omit S

variable (Ψ) in
@[expose] def NrRel (e : G) (s t : Bool × Fin 3) : Prop :=
  e * nrqG Ψ s * e⁻¹ = nrqG Ψ t ∨ e * nrqG Ψ s * e⁻¹ = nrqG Ψ t * nrzG Ψ

include S

theorem NrSetting.rel_mul {e e' : G} (he : e ∈ E) {s t t' : Bool × Fin 3}
    (h1 : NrRel Ψ e' s t) (h2 : NrRel Ψ e t t') : NrRel Ψ (e * e') s t' := by
  have hz := S.fix_z he
  have hgroup : e * e' * nrqG Ψ s * (e * e')⁻¹ = e * (e' * nrqG Ψ s * e'⁻¹) * e⁻¹ := by group
  unfold NrRel at h1 h2 ⊢
  rw [hgroup]
  rcases h1 with h1 | h1
  · rw [h1]
    exact h2
  · rw [h1]
    have h3 : e * (nrqG Ψ t * nrzG Ψ) * e⁻¹ = (e * nrqG Ψ t * e⁻¹) * (e * nrzG Ψ * e⁻¹) := by
      group
    rw [h3, hz]
    rcases h2 with h2 | h2
    · right
      rw [h2]
    · left
      rw [h2, mul_assoc, nrzG_mul_self, mul_one]

noncomputable def nrAct (e : ↥E) (s : Bool × Fin 3) : Bool × Fin 3 :=
  Classical.choose (S.rel_exists e.2 s)

theorem NrSetting.rel_act (e : ↥E) (s : Bool × Fin 3) : NrRel Ψ (e : G) s (nrAct S e s) :=
  Classical.choose_spec (S.rel_exists e.2 s)

theorem NrSetting.act_eq_of_rel {e : ↥E} {s t : Bool × Fin 3} (h : NrRel Ψ (e : G) s t) :
    nrAct S e s = t :=
  S.ker.rel_unique (S.rel_act e s) h

theorem NrSetting.act_one (s : Bool × Fin 3) : nrAct S 1 s = s :=
  S.act_eq_of_rel (Or.inl (by simp))

theorem NrSetting.act_mul (e e' : ↥E) (s : Bool × Fin 3) :
    nrAct S (e * e') s = nrAct S e (nrAct S e' s) :=
  S.act_eq_of_rel (S.rel_mul e.2 (S.rel_act e' s) (S.rel_act e (nrAct S e' s)))

@[expose] noncomputable def nrRho : ↥E →* Equiv.Perm (Bool × Fin 3) where
  toFun e :=
    { toFun := nrAct S e
      invFun := nrAct S e⁻¹
      left_inv := fun s => by
        show nrAct S e⁻¹ (nrAct S e s) = s
        rw [← S.act_mul, inv_mul_cancel, S.act_one]
      right_inv := fun s => by
        show nrAct S e (nrAct S e⁻¹ s) = s
        rw [← S.act_mul, mul_inv_cancel, S.act_one] }
  map_one' := Equiv.ext fun s => S.act_one s
  map_mul' := fun e e' => Equiv.ext fun s => S.act_mul e e' s

theorem nrRho_apply (e : ↥E) (s : Bool × Fin 3) : nrRho S e s = nrAct S e s := rfl

theorem NrSetting.pres (e : ↥E) : NrPres (nrRho S e) := by
  intro s t
  rw [nrRho_apply, nrRho_apply]
  have hrs := S.rel_act e s
  have hrt := S.rel_act e t
  have hz := S.fix_z e.2
  have hcs : (e : G) * (nrqG Ψ s * nrqG Ψ t * (nrqG Ψ s)⁻¹ * (nrqG Ψ t)⁻¹) * (e : G)⁻¹ =
      ((e : G) * nrqG Ψ s * (e : G)⁻¹) * ((e : G) * nrqG Ψ t * (e : G)⁻¹) *
        ((e : G) * nrqG Ψ s * (e : G)⁻¹)⁻¹ * ((e : G) * nrqG Ψ t * (e : G)⁻¹)⁻¹ := by group
  rw [S.ker.nrqG_comm] at hcs
  rw [nr_comm_cases (nrzG_comm (nrqG_mem (nrAct S e s))) (nrzG_comm (nrqG_mem (nrAct S e t)))
    hrs hrt, S.ker.nrqG_comm] at hcs
  have hz1 := S.ker.nrzG_ne_one
  have hfix : (e : G) * (if NrR s t then nrzG Ψ else 1) * (e : G)⁻¹ =
      if NrR s t then nrzG Ψ else 1 := by
    split_ifs
    · exact hz
    · simp
  rw [hfix] at hcs
  by_cases h1 : NrR (nrAct S e s) (nrAct S e t) <;> by_cases h2 : NrR s t
  · exact ⟨fun _ => h2, fun _ => h1⟩
  · exfalso
    rw [if_pos h1, if_neg h2] at hcs
    exact hz1 hcs.symm
  · exfalso
    rw [if_neg h1, if_pos h2] at hcs
    exact hz1 hcs
  · exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩

end CFSG.OddStandard.SmallF3.Omega
