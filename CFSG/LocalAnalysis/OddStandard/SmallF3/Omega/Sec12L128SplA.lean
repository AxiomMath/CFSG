module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L127A5
public import Certificates.Data.A5

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

abbrev Sec128A5 : Type := ↥(alternatingGroup (Fin 5))

theorem sec128_A5_central {a : Sec128A5} (h : ∀ x : Sec128A5, a * x = x * a) : a = 1 :=
  sec127_center_alt5 (X := (⊤ : Subgroup Sec128A5)) ⟨Subgroup.topEquiv⟩ (u := a) trivial
    (fun x _ => h x)

theorem sec128_A5_ne_one : ∃ a : Sec128A5, a ≠ 1 := by
  by_contra h
  push Not at h
  have h1 : Nat.card Sec128A5 = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun a b => (h a).trans (h b).symm⟩, ⟨1⟩⟩
  rw [sec127_card_alt5_type] at h1
  omega

theorem sec128_normal_prod (N : Subgroup (Sec128A5 × Sec128A5)) [hN : N.Normal] (hne : N ≠ ⊥) :
    (∀ a : Sec128A5, (a, (1 : Sec128A5)) ∈ N) ∨ (∀ b : Sec128A5, ((1 : Sec128A5), b) ∈ N) := by
  obtain ⟨⟨a, b⟩, hn, hn1⟩ : ∃ p ∈ N, p ≠ 1 := by
    by_contra h
    push Not at h
    exact hne ((Subgroup.eq_bot_iff_forall N).mpr h)
  by_cases ha : a = 1
  · right
    subst ha
    have hb : b ≠ 1 := fun hb => hn1 (by rw [hb]; rfl)
    obtain ⟨x, hx⟩ : ∃ x : Sec128A5, b * x ≠ x * b := by
      by_contra h
      push Not at h
      exact hb (sec128_A5_central h)
    let K : Subgroup Sec128A5 := N.comap (MonoidHom.inr Sec128A5 Sec128A5)
    have hKn : K.Normal := hN.comap _
    have hmem : x * b * x⁻¹ * b⁻¹ ∈ K := by
      have h1 : ((1 : Sec128A5), x) * (1, b) * ((1 : Sec128A5), x)⁻¹ ∈ N := hN.conj_mem (1, b) hn _
      have h2 := N.mul_mem h1 (N.inv_mem hn)
      have h3 : ((1 : Sec128A5), x) * (1, b) * ((1 : Sec128A5), x)⁻¹ * (1, b)⁻¹ =
          ((1 : Sec128A5), x * b * x⁻¹ * b⁻¹) := by
        ext <;> simp
      rw [h3] at h2
      exact h2
    have hne1 : x * b * x⁻¹ * b⁻¹ ≠ 1 := by
      intro h
      apply hx
      calc b * x = (x * b * x⁻¹ * b⁻¹) * (b * x) := by rw [h, one_mul]
        _ = x * b := by group
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with hK | hK
    · exact absurd (Subgroup.mem_bot.mp (hK ▸ hmem)) hne1
    · intro y
      have : y ∈ K := hK ▸ Subgroup.mem_top y
      exact this
  · left
    obtain ⟨x, hx⟩ : ∃ x : Sec128A5, a * x ≠ x * a := by
      by_contra h
      push Not at h
      exact ha (sec128_A5_central h)
    let K : Subgroup Sec128A5 := N.comap (MonoidHom.inl Sec128A5 Sec128A5)
    have hKn : K.Normal := hN.comap _
    have hmem : x * a * x⁻¹ * a⁻¹ ∈ K := by
      have h1 : (x, (1 : Sec128A5)) * (a, b) * (x, (1 : Sec128A5))⁻¹ ∈ N := hN.conj_mem (a, b) hn _
      have h2 := N.mul_mem h1 (N.inv_mem hn)
      have h3 : (x, (1 : Sec128A5)) * (a, b) * (x, (1 : Sec128A5))⁻¹ * (a, b)⁻¹ =
          (x * a * x⁻¹ * a⁻¹, (1 : Sec128A5)) := by
        ext <;> simp
      rw [h3] at h2
      exact h2
    have hne1 : x * a * x⁻¹ * a⁻¹ ≠ 1 := by
      intro h
      apply hx
      calc a * x = (x * a * x⁻¹ * a⁻¹) * (a * x) := by rw [h, one_mul]
        _ = x * a := by group
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with hK | hK
    · exact absurd (Subgroup.mem_bot.mp (hK ▸ hmem)) hne1
    · intro y
      have : y ∈ K := hK ▸ Subgroup.mem_top y
      exact this

@[expose] def sec128N1 : Subgroup (Sec128A5 × Sec128A5) := (MonoidHom.snd Sec128A5 Sec128A5).ker

@[expose] def sec128N2 : Subgroup (Sec128A5 × Sec128A5) := (MonoidHom.fst Sec128A5 Sec128A5).ker

theorem sec128_mem_N1 {p : Sec128A5 × Sec128A5} : p ∈ sec128N1 ↔ p.2 = 1 := by
  unfold sec128N1
  rw [MonoidHom.mem_ker]
  rfl

theorem sec128_mem_N2 {p : Sec128A5 × Sec128A5} : p ∈ sec128N2 ↔ p.1 = 1 := by
  unfold sec128N2
  rw [MonoidHom.mem_ker]
  rfl

instance : sec128N1.Normal := by unfold sec128N1; infer_instance

instance : sec128N2.Normal := by unfold sec128N2; infer_instance

theorem sec128_card_N1 : Nat.card sec128N1 = 60 := by
  rw [← sec127_card_alt5_type]
  exact Nat.card_congr
    { toFun := fun p => (p : Sec128A5 × Sec128A5).1
      invFun := fun a => ⟨(a, 1), sec128_mem_N1.mpr rfl⟩
      left_inv := fun p => Subtype.ext (Prod.ext rfl (sec128_mem_N1.mp p.2).symm)
      right_inv := fun a => rfl }

theorem sec128_card_N2 : Nat.card sec128N2 = 60 := by
  rw [← sec127_card_alt5_type]
  exact Nat.card_congr
    { toFun := fun p => (p : Sec128A5 × Sec128A5).2
      invFun := fun a => ⟨(1, a), sec128_mem_N2.mpr rfl⟩
      left_inv := fun p => Subtype.ext (Prod.ext (sec128_mem_N2.mp p.2).symm rfl)
      right_inv := fun a => rfl }

theorem sec128_N1_ne_N2 : sec128N1 ≠ sec128N2 := by
  intro h
  obtain ⟨a, ha⟩ := sec128_A5_ne_one
  have h1 : (a, (1 : Sec128A5)) ∈ sec128N1 := sec128_mem_N1.mpr rfl
  rw [h] at h1
  exact ha (sec128_mem_N2.mp h1)

theorem sec128_normal_sixty (N : Subgroup (Sec128A5 × Sec128A5)) [hN : N.Normal]
    (hc : Nat.card N = 60) : N = sec128N1 ∨ N = sec128N2 := by
  have hne : N ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hc
    omega
  rcases sec128_normal_prod N hne with h | h
  · left
    refine (Subgroup.eq_of_le_of_card_ge (H := sec128N1) (K := N) ?_ ?_).symm
    · intro p hp
      have : p = (p.1, (1 : Sec128A5)) := Prod.ext rfl (sec128_mem_N1.mp hp)
      rw [this]
      exact h _
    · rw [hc, sec128_card_N1]
  · right
    refine (Subgroup.eq_of_le_of_card_ge (H := sec128N2) (K := N) ?_ ?_).symm
    · intro p hp
      have : p = ((1 : Sec128A5), p.2) := Prod.ext (sec128_mem_N2.mp hp) rfl
      rw [this]
      exact h _
    · rw [hc, sec128_card_N2]

theorem sec128_aut_dich (κ : Sec128A5 × Sec128A5 →* Sec128A5 × Sec128A5) (hκ : Function.Injective κ)
    (D : Subgroup (Sec128A5 × Sec128A5)) (hD1 : ∀ a : Sec128A5, ∃ b : Sec128A5, (a, b) ∈ D)
    (hD2 : ∀ b : Sec128A5, ∃ a : Sec128A5, (a, b) ∈ D) (hfix : ∀ d ∈ D, κ d = d) :
    (∀ p, κ p = p) ∨ ((∀ a : Sec128A5, (κ (a, 1)).1 = 1) ∧ (∀ b : Sec128A5, (κ (1, b)).2 = 1)) := by
  have hsurj : Function.Surjective κ := Finite.injective_iff_surjective.mp hκ
  have hK : ∀ N : Subgroup (Sec128A5 × Sec128A5), N.Normal → Nat.card N = 60 →
      N = sec128N1 ∨ N = sec128N2 := fun N hN hc => sec128_normal_sixty N hc
  have hm1 : (sec128N1.map κ) = sec128N1 ∨ (sec128N1.map κ) = sec128N2 :=
    hK _ (Subgroup.Normal.map inferInstance κ hsurj)
      (by rw [Subgroup.card_map_of_injective hκ]; exact sec128_card_N1)
  have hm2 : (sec128N2.map κ) = sec128N1 ∨ (sec128N2.map κ) = sec128N2 :=
    hK _ (Subgroup.Normal.map inferInstance κ hsurj)
      (by rw [Subgroup.card_map_of_injective hκ]; exact sec128_card_N2)
  have hin1 : ∀ a : Sec128A5, κ (a, 1) ∈ sec128N1.map κ := fun a =>
    Subgroup.mem_map_of_mem κ (sec128_mem_N1.mpr rfl)
  have hin2 : ∀ b : Sec128A5, κ (1, b) ∈ sec128N2.map κ := fun b =>
    Subgroup.mem_map_of_mem κ (sec128_mem_N2.mpr rfl)
  rcases hm1 with h1 | h1 <;> rcases hm2 with h2 | h2
  · exact absurd (Subgroup.map_injective hκ (h1.trans h2.symm)) (sec128_N1_ne_N2)
  · left
    have e1 : ∀ a : Sec128A5, (κ (a, 1)).2 = 1 := fun a => sec128_mem_N1.mp (h1 ▸ hin1 a)
    have e2 : ∀ b : Sec128A5, (κ (1, b)).1 = 1 := fun b => sec128_mem_N2.mp (h2 ▸ hin2 b)
    have hfa : ∀ a : Sec128A5, κ (a, 1) = (a, 1) := by
      intro a
      obtain ⟨b0, hb0⟩ := hD1 a
      have h3 := hfix _ hb0
      have h4 : (a, b0) = (a, (1 : Sec128A5)) * ((1 : Sec128A5), b0) := by ext <;> simp
      rw [h4, map_mul] at h3
      have h5 := congrArg Prod.fst h3
      simp only [Prod.fst_mul, e2, mul_one] at h5
      exact Prod.ext h5 (e1 a)
    have hfb : ∀ b : Sec128A5, κ (1, b) = (1, b) := by
      intro b
      obtain ⟨a0, ha0⟩ := hD2 b
      have h3 := hfix _ ha0
      have h4 : (a0, b) = (a0, (1 : Sec128A5)) * ((1 : Sec128A5), b) := by ext <;> simp
      rw [h4, map_mul, hfa] at h3
      exact mul_left_cancel h3
    intro p
    have h4 : p = (p.1, (1 : Sec128A5)) * ((1 : Sec128A5), p.2) := by ext <;> simp
    rw [h4, map_mul, hfa, hfb]
  · right
    exact ⟨fun a => sec128_mem_N2.mp (h1 ▸ hin1 a), fun b => sec128_mem_N1.mp (h2 ▸ hin2 b)⟩
  · exact absurd (Subgroup.map_injective hκ (h1.trans h2.symm)) (sec128_N1_ne_N2)

theorem sec128_proj2_onto {D : Subgroup (Sec128A5 × Sec128A5)} (hD : Nonempty (↥D ≃* Sec128A5))
    (hne : ∃ d ∈ D, d.2 ≠ 1) : ∀ b : Sec128A5, ∃ a : Sec128A5, (a, b) ∈ D := by
  obtain ⟨e⟩ := hD
  haveI : IsSimpleGroup ↥D := e.isSimpleGroup
  let f : ↥D →* Sec128A5 := (MonoidHom.snd Sec128A5 Sec128A5).comp D.subtype
  have hinj : Function.Injective f := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff f).mp h
    · exfalso
      obtain ⟨d, hd, hd2⟩ := hne
      have : (⟨d, hd⟩ : ↥D) ∈ f.ker := by rw [h]; trivial
      exact hd2 (MonoidHom.mem_ker.mp this)
  have hsurj : Function.Surjective f := (Finite.injective_iff_surjective_of_equiv e.toEquiv).mp hinj
  intro b
  obtain ⟨⟨d, hd⟩, hdb⟩ := hsurj b
  refine ⟨d.1, ?_⟩
  have : d = (d.1, b) := Prod.ext rfl hdb
  rw [← this]
  exact hd

theorem sec128_proj1_onto {D : Subgroup (Sec128A5 × Sec128A5)} (hD : Nonempty (↥D ≃* Sec128A5))
    (hne : ∃ d ∈ D, d.1 ≠ 1) : ∀ a : Sec128A5, ∃ b : Sec128A5, (a, b) ∈ D := by
  obtain ⟨e⟩ := hD
  haveI : IsSimpleGroup ↥D := e.isSimpleGroup
  let f : ↥D →* Sec128A5 := (MonoidHom.fst Sec128A5 Sec128A5).comp D.subtype
  have hinj : Function.Injective f := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff f).mp h
    · exfalso
      obtain ⟨d, hd, hd2⟩ := hne
      have : (⟨d, hd⟩ : ↥D) ∈ f.ker := by rw [h]; trivial
      exact hd2 (MonoidHom.mem_ker.mp this)
  have hsurj : Function.Surjective f := (Finite.injective_iff_surjective_of_equiv e.toEquiv).mp hinj
  intro a
  obtain ⟨⟨d, hd⟩, hda⟩ := hsurj a
  refine ⟨d.2, ?_⟩
  have : d = (a, d.2) := Prod.ext hda rfl
  rw [← this]
  exact hd

end CFSG.OddStandard.SmallF3.Omega
