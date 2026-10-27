module

public import CFSG.GH74.Uniqueness.SU.SU9Cfg
public import CFSG.GH74.GLS.C3.Layer3.Basic
public import CFSG.GH74.Uniqueness.SU.SU7Claim

public section

namespace CFSG.GH74.Uniqueness.SU.SU9

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU5 CFSG.GH74.Uniqueness.SU.SU7
  CFSG

namespace L196

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {U M V : Subgroup G} {x z : G}
  {A B R : Subgroup G}

theorem not_isConj_z (hc : Ctx19 S U M V x z A B R)
    (hTM' : ∀ m ∈ M, ∀ t ∈ Tsub S U, m * t * m⁻¹ ∈ Tsub S U) {a : G} (ha : a ∈ A)
    (haU : a ∉ U) : ¬ IsConj z a := by
  intro hza
  have hE : IsPGroup 2 A := IsPGroup.of_card (n := 4) (by rw [Cfg.card_A hc]; norm_num)
  have hcomm : ∀ e ∈ A, e * a = a * e := fun e he => Cfg.A_comm hc e he a ha
  obtain ⟨g', hg'a, hg'S⟩ := Cfg.exists_conj_into_S hc hE hcomm hza
  have hA₂S : conjSub g' A ≤ (S : Subgroup G) := by
    intro y hy
    rw [mem_conjSub] at hy
    have := hg'S _ hy
    have e : g' * (g'⁻¹ * y * g') * g'⁻¹ = y := by group
    rwa [e] at this
  have hA₂E : IsE 4 (conjSub g' A) :=
    ⟨isElemAbelian_conjSub (Cfg.isE_A hc).1, by rw [card_conjSub, Cfg.card_A hc]; norm_num⟩
  have hJ := Cfg.j2 hc
  have hA₂T : conjSub g' A ≤ Tsub S U := by
    intro s hs
    by_contra hsT
    have hs1 : s ≠ 1 := fun h => hsT (h ▸ (Tsub S U).one_mem)
    have hsc := isElemAbelian_iff.1 hA₂E.1
    have hs2 : s ^ 2 = 1 := hsc.2 s hs
    have h4 := hJ.le4 s (hA₂S hs) hsT hs2 (conjSub g' A) (fun y hy => ⟨hA₂S hy, ?_⟩) hA₂E.1
    · rw [hA₂E.2] at h4
      norm_num at h4
    · exact mem_centralizer_singleton_iff.2 (hsc.1 y hy s hs)
  have hnorm : ∃ g'' : G, g'' ∈ normalizer (A : Set G) ∧ g'' * a * g''⁻¹ = z := by
    rcases Cfg.unique_E16 hc hA₂T hA₂E with h | h
    · exact ⟨g', Cfg.mem_normalizer_of_conjSub_eq h, hg'a⟩
    · refine ⟨x * g', Cfg.mem_normalizer_of_conjSub_eq ?_, ?_⟩
      · rw [conjSub_mul, h, Cfg.conjSub_x_B hc]
      · calc x * g' * a * (x * g')⁻¹ = x * (g' * a * g'⁻¹) * x⁻¹ := by group
          _ = z := by rw [hg'a]; exact Cfg.x_comm_z hc
  obtain ⟨g'', hg''N, hg''a⟩ := hnorm
  have hg''M : g'' ∈ M := by
    have hle : normalizer (A : Set G) ≤ M :=
      Claim.normalizer_le_M_of_isE hc.hyp (Cfg.A_le_S hc) (Cfg.isE_A hc) (by norm_num)
        (F := A) (fun y hy => ⟨mem_centralizer_iff.2 fun w hw =>
          (Cfg.A_comm hc w hw y hy), Cfg.A_le_S hc hy⟩) (Cfg.isE_A hc) (by norm_num)
    exact hle hg''N
  have haeq : a = g''⁻¹ * z * g''⁻¹⁻¹ := by
    rw [← hg''a]; group
  apply haU
  rw [haeq]
  exact Cfg.U_normal_M hc hTM' g''⁻¹ (M.inv_mem hg''M) z (hc.c19.z_mem)

theorem isConj_cases (h191 : Lemma191Stmt) (hc : Ctx19 S U M V x z A B R)
    (h194M : pPrimeCore 2 ↥M = ⊥) {a s : G} (ha : a ∈ A) (haU : a ∉ U)
    (hs : s ∈ (S : Subgroup G)) (hs2 : orderOf s = 2) : IsConj z s ∨ IsConj a s := by
  have hs1 : s ≠ 1 := fun h => by rw [h, orderOf_one] at hs2; omega
  have hss : s * s = 1 := by rw [← pow_two]; exact pow_orderOf_eq_one s ▸ by rw [hs2]
  by_cases hsT : s ∈ Tsub S U
  · by_cases hsU : s ∈ U
    · exact Or.inl (Cfg.isConj_z_of_mem_U hc hsU hs1)
    · obtain ⟨m, hm, hma⟩ := Cfg.exists_M_conj hc h194M ha haU hsT hsU hss
      exact Or.inr (isConj_iff.2 ⟨m, hma⟩)
  · exact Or.inl (Cfg.isConj_z_of_not_T h191 hc hs hsT hs2)

theorem lemma196_a (h191 : Lemma191Stmt) (hc : Ctx19 S U M V x z A B R)
    (h194M : pPrimeCore 2 ↥M = ⊥) (hTM' : ∀ m ∈ M, ∀ t ∈ Tsub S U, m * t * m⁻¹ ∈ Tsub S U)
    {a : G} (ha : a ∈ A) (haU : a ∉ U) :
    (∀ g : G, orderOf g = 2 → IsConj z g ∨ IsConj a g) ∧ ¬ IsConj z a := by
  refine ⟨fun g hg => ?_, not_isConj_z hc hTM' ha haU⟩
  obtain ⟨c, hcS⟩ := GLS.Layer3.exists_conj_mem_sylow_two S hg
  have hs2 : orderOf (c * g * c⁻¹) = 2 := by rw [Cfg.orderOf_conj', hg]
  have hconj : IsConj g (c * g * c⁻¹) := isConj_iff.2 ⟨c, rfl⟩
  rcases isConj_cases h191 hc h194M ha haU hcS hs2 with h | h
  · exact Or.inl (h.trans hconj.symm)
  · exact Or.inr (h.trans hconj.symm)

theorem lemma196_b (h191 : Lemma191Stmt) (hc : Ctx19 S U M V x z A B R)
    (h194M : pPrimeCore 2 ↥M = ⊥) (hTM' : ∀ m ∈ M, ∀ t ∈ Tsub S U, m * t * m⁻¹ ∈ Tsub S U)
    {a : G} (ha : a ∈ A) (haU : a ∉ U) :
    ∀ g ∈ (S : Subgroup G), IsConj a g ↔ ((g ∈ A ∨ g ∈ B) ∧ g ∉ U) := by
  intro g hgS
  have hnz := not_isConj_z hc hTM' ha haU
  constructor
  · intro hag
    have hgo : orderOf g = 2 := by
      obtain ⟨c, hcg⟩ := isConj_iff.1 hag
      rw [← hcg, Cfg.orderOf_conj']
      have ha1 : a ≠ 1 := fun h => haU (h ▸ U.one_mem)
      exact orderOf_eq_prime (by rw [pow_two]; exact Cfg.A_sq hc a ha) ha1
    have hg1 : g ≠ 1 := fun h => by rw [h, orderOf_one] at hgo; omega
    by_cases hgT : g ∈ Tsub S U
    · by_cases hgU : g ∈ U
      · exact absurd ((Cfg.isConj_z_of_mem_U hc hgU hg1).trans hag.symm |>.symm) (by
          intro h; exact hnz h.symm)
      · exact ⟨hc.c19.invol g hgT hgo, hgU⟩
    · exact absurd (((Cfg.isConj_z_of_not_T h191 hc hgS hgT hgo).trans hag.symm).symm) (by
        intro h; exact hnz h.symm)
  · rintro ⟨hgAB, hgU⟩
    have hgT : g ∈ Tsub S U := by
      rcases hgAB with h | h
      · exact hc.c19.A_le h
      · exact hc.c19.B_le h
    have hgg : g * g = 1 := by
      rcases hgAB with h | h
      · exact Cfg.A_sq hc g h
      · exact Cfg.B_sq hc g h
    obtain ⟨m, -, hma⟩ := Cfg.exists_M_conj hc h194M ha haU hgT hgU hgg
    exact isConj_iff.2 ⟨m, hma⟩

end L196

end CFSG.GH74.Uniqueness.SU.SU9
