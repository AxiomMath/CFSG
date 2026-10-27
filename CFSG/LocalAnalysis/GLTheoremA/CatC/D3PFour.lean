module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3PGroup

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace D3P

open CFSG.Open

variable {G : Type*} [Group G]

def fourSubgroup (a b : G) (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) : Subgroup G where
  carrier := {h | h = 1 ∨ h = a ∨ h = b ∨ h = a * b}
  one_mem' := Or.inl rfl
  mul_mem' := by
    have e1 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
    have e2 : b * (a * b) = a := by rw [← mul_assoc, ← hab, mul_assoc, hb, mul_one]
    have e3 : (a * b) * a = b := by rw [mul_assoc, ← hab, ← mul_assoc, ha, one_mul]
    have e4 : (a * b) * b = a := by rw [mul_assoc, hb, mul_one]
    have e5 : (a * b) * (a * b) = 1 := by rw [← mul_assoc, e3, hb]
    intro u v hu hv
    have hba : b * a = a * b := hab.symm
    rcases hu with hu | hu | hu | hu <;> rcases hv with hv | hv | hv | hv <;> rw [hu, hv] <;>
      simp only [Set.mem_setOf_eq, one_mul, mul_one, ha, hb, e1, e2, e3, e4, e5, hba, true_or,
        or_true, eq_self_iff_true]
  inv_mem' := by
    intro u hu
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
    have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
    rcases hu with hu | hu | hu | hu
    · exact Or.inl (by rw [hu]; simp)
    · exact Or.inr (Or.inl (by rw [hu, hai]))
    · exact Or.inr (Or.inr (Or.inl (by rw [hu, hbi])))
    · refine Or.inr (Or.inr (Or.inr ?_))
      rw [hu, mul_inv_rev, hai, hbi, hab]

theorem min_invariant_four [Finite G] {E H : Subgroup G} (hE : IsElemAbelian 3 E)
    (hnorm : E ≤ Subgroup.normalizer (H : Set G))
    (hmin : ∀ H' : Subgroup G, H' ≠ ⊥ → H' ≤ H → E ≤ Subgroup.normalizer (H' : Set G) → H' = H)
    (hex : ∀ x ∈ H, x * x = 1 ∧ ∀ y ∈ H, x * y = y * x)
    {b : G} (hb : b ∈ E) (hbc : b ∉ Subgroup.centralizer (H : Set G)) {x : G} (hx : x ∈ H)
    (hx1 : x ≠ 1) :
    b * x * b⁻¹ ≠ x ∧ b * x * b⁻¹ ≠ 1 ∧ b * (b * x * b⁻¹) * b⁻¹ = x * (b * x * b⁻¹) ∧
      b * (x * (b * x * b⁻¹)) * b⁻¹ = x ∧
      ∀ h ∈ H, h = 1 ∨ h = x ∨ h = b * x * b⁻¹ ∨ h = x * (b * x * b⁻¹) := by
  have hfpf := min_invariant_fpf hE hnorm hmin hb hbc
  have h3b : b ^ 3 = 1 := hE.2 b hb
  have h3b' : b * b * b = 1 := by rw [← pow_three']; exact h3b
  have hx1H : b * x * b⁻¹ ∈ H := conj_mem_of_normalizer (hnorm hb) hx
  have hx2H : b * (b * x * b⁻¹) * b⁻¹ ∈ H := conj_mem_of_normalizer (hnorm hb) hx1H
  have hne1 : b * x * b⁻¹ ≠ x := fun h =>
    hx1 (hfpf x hx (by calc b * x = b * x * b⁻¹ * b := by group
                          _ = x * b := by rw [h]))
  have hne2 : b * x * b⁻¹ ≠ 1 := fun h => hx1 (by
    calc x = b⁻¹ * (b * x * b⁻¹) * b := by group
      _ = 1 := by rw [h]; group)
  have hnormx := min_invariant_norm hE hnorm hmin hex hb hbc hx
  have hx2 : b * (b * x * b⁻¹) * b⁻¹ = x * (b * x * b⁻¹) :=
    third_of_prod_eq_one hex hx hx1H hx2H hnormx
  have hx0 : b * (b * (b * x * b⁻¹) * b⁻¹) * b⁻¹ = x := by
    have : b * (b * (b * x * b⁻¹) * b⁻¹) * b⁻¹ = (b * b * b) * x * (b * b * b)⁻¹ := by group
    rw [this, h3b']; group
  have hx3 : b * (x * (b * x * b⁻¹)) * b⁻¹ = x := by rw [← hx2]; exact hx0
  refine ⟨hne1, hne2, hx2, hx3, ?_⟩
  have hxx : x * x = 1 := (hex x hx).1
  have hx1x1 : (b * x * b⁻¹) * (b * x * b⁻¹) = 1 := (hex _ hx1H).1
  have hcomm : x * (b * x * b⁻¹) = (b * x * b⁻¹) * x := (hex x hx).2 _ hx1H
  set W : Subgroup G := fourSubgroup x (b * x * b⁻¹) hxx hx1x1 hcomm with hW
  have hWH : W ≤ H := by
    intro w hw
    rcases hw with hw | hw | hw | hw <;> rw [hw]
    · exact H.one_mem
    · exact hx
    · exact hx1H
    · exact H.mul_mem hx hx1H
  have hWne : W ≠ ⊥ := by
    intro h
    have : x ∈ W := Or.inr (Or.inl rfl)
    rw [h, Subgroup.mem_bot] at this
    exact hx1 this
  have hWx : x ∈ W := Or.inr (Or.inl rfl)
  have hWx1 : b * x * b⁻¹ ∈ W := Or.inr (Or.inr (Or.inl rfl))
  have hWx2 : x * (b * x * b⁻¹) ∈ W := Or.inr (Or.inr (Or.inr rfl))
  have hWnorm : E ≤ Subgroup.normalizer (W : Set G) := by
    refine le_normalizer_of_forward E W fun e he w hw => ?_
    have hbx : b⁻¹ * x * b = x * (b * x * b⁻¹) := by
      calc b⁻¹ * x * b = b⁻¹ * (b * (x * (b * x * b⁻¹)) * b⁻¹) * b := by rw [hx3]
        _ = x * (b * x * b⁻¹) := by group
    have hbx1 : b⁻¹ * (b * x * b⁻¹) * b = x := by group
    have key : e * x * e⁻¹ ∈ W ∧ e * (b * x * b⁻¹) * e⁻¹ ∈ W := by
      rcases min_invariant_conj_cases hE hnorm hmin hex hb hbc he with h | h | h
      · rw [h x hx, h _ hx1H]; exact ⟨hWx, hWx1⟩
      · rw [h x hx, h _ hx1H, hx2]; exact ⟨hWx1, hWx2⟩
      · rw [h x hx, h _ hx1H, hbx, hbx1]; exact ⟨hWx2, hWx⟩
    rcases hw with hw | hw | hw | hw <;> rw [hw]
    · simpa using W.one_mem
    · exact key.1
    · exact key.2
    · have : e * (x * (b * x * b⁻¹)) * e⁻¹ = (e * x * e⁻¹) * (e * (b * x * b⁻¹) * e⁻¹) := by group
      rw [this]; exact W.mul_mem key.1 key.2
  have hWeq := hmin W hWne hWH hWnorm
  intro h hh
  have : h ∈ W := by rw [hWeq]; exact hh
  exact this

theorem min_invariant_card [Finite G] {E H : Subgroup G} (hE : IsElemAbelian 3 E)
    (hnorm : E ≤ Subgroup.normalizer (H : Set G))
    (hmin : ∀ H' : Subgroup G, H' ≠ ⊥ → H' ≤ H → E ≤ Subgroup.normalizer (H' : Set G) → H' = H)
    (hex : ∀ x ∈ H, x * x = 1 ∧ ∀ y ∈ H, x * y = y * x)
    {b : G} (hb : b ∈ E) (hbc : b ∉ Subgroup.centralizer (H : Set G)) {x : G} (hx : x ∈ H)
    (hx1 : x ≠ 1) :
    Nat.card E = 3 * Nat.card (E ⊓ Subgroup.centralizer (H : Set G) : Subgroup G) := by
  obtain ⟨h1, h2, h3, h4, hH⟩ := min_invariant_four hE hnorm hmin hex hb hbc hx hx1
  have hx1H : b * x * b⁻¹ ∈ H := conj_mem_of_normalizer (hnorm hb) hx
  have hbx : b⁻¹ * x * b = x * (b * x * b⁻¹) := by
    calc b⁻¹ * x * b = b⁻¹ * (b * (x * (b * x * b⁻¹)) * b⁻¹) * b := by rw [h4]
      _ = x * (b * x * b⁻¹) := by group
  letI : MulAction ↥E G := MulAction.compHom G
    ((ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom.comp E.subtype)
  have hsmul : ∀ (e : ↥E) (y : G), e • y = (e : G) * y * (e : G)⁻¹ := fun e y => by
    show ConjAct.toConjAct (e : G) • y = _
    simp [ConjAct.smul_def]
  have hstab : MulAction.stabilizer ↥E x =
      (E ⊓ Subgroup.centralizer (H : Set G) : Subgroup G).subgroupOf E := by
    ext e
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf, hsmul]
    constructor
    · intro hfix
      refine ⟨e.2, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
      have hbe : (e : G) * b = b * (e : G) := comm_of_elemAbelian hE e.2 hb
      have hfix1 : (e : G) * (b * x * b⁻¹) * (e : G)⁻¹ = b * x * b⁻¹ := by
        calc (e : G) * (b * x * b⁻¹) * (e : G)⁻¹
            = (e * b) * x * (e * b)⁻¹ * 1 := by group
          _ = (b * e) * x * (b * e)⁻¹ := by rw [hbe]; group
          _ = b * ((e : G) * x * (e : G)⁻¹) * b⁻¹ := by group
          _ = b * x * b⁻¹ := by rw [hfix]
      have hcom : ∀ z : G, (e : G) * z * (e : G)⁻¹ = z → z * (e : G) = (e : G) * z := by
        intro z hz
        calc z * (e : G) = ((e : G) * z * (e : G)⁻¹) * (e : G) := by rw [hz]
          _ = (e : G) * z := by group
      rcases hH y hy with rfl | rfl | rfl | rfl
      · simp
      · exact hcom _ hfix
      · exact hcom _ hfix1
      · refine hcom _ ?_
        calc (e : G) * (x * (b * x * b⁻¹)) * (e : G)⁻¹
            = ((e : G) * x * (e : G)⁻¹) * ((e : G) * (b * x * b⁻¹) * (e : G)⁻¹) := by group
          _ = x * (b * x * b⁻¹) := by rw [hfix, hfix1]
    · rintro ⟨-, hc⟩
      have := Subgroup.mem_centralizer_iff.1 hc x hx
      calc (e : G) * x * (e : G)⁻¹ = x * (e : G) * (e : G)⁻¹ := by rw [this]
        _ = x := by group
  have horb : MulAction.orbit ↥E x = {x, b * x * b⁻¹, x * (b * x * b⁻¹)} := by
    ext y
    rw [MulAction.mem_orbit_iff]
    simp only [hsmul, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨e, rfl⟩
      rcases min_invariant_conj_cases hE hnorm hmin hex hb hbc e.2 with h | h | h
      · exact Or.inl (h x hx)
      · exact Or.inr (Or.inl (h x hx))
      · exact Or.inr (Or.inr (by rw [h x hx, hbx]))
    · rintro (rfl | rfl | rfl)
      · exact ⟨1, by simp⟩
      · exact ⟨⟨b, hb⟩, rfl⟩
      · exact ⟨⟨b⁻¹, E.inv_mem hb⟩, by simp [hbx]⟩
  have hx1x2 : x * (b * x * b⁻¹) ≠ x := by
    intro h
    apply h2
    calc b * x * b⁻¹ = x⁻¹ * (x * (b * x * b⁻¹)) := by group
      _ = x⁻¹ * x := by rw [h]
      _ = 1 := by group
  have hx0x2 : x * (b * x * b⁻¹) ≠ b * x * b⁻¹ := by
    intro h
    apply hx1
    calc x = (x * (b * x * b⁻¹)) * (b * x * b⁻¹)⁻¹ := by group
      _ = (b * x * b⁻¹) * (b * x * b⁻¹)⁻¹ := by rw [h]
      _ = 1 := by group
  have horbcard : (MulAction.orbit ↥E x).ncard = 3 := by
    rw [horb]
    exact Set.ncard_eq_three.2 ⟨x, b * x * b⁻¹, x * (b * x * b⁻¹), h1.symm, hx1x2.symm,
      hx0x2.symm, rfl⟩
  have hidx := MulAction.index_stabilizer ↥E x
  have hmul := Subgroup.index_mul_card (MulAction.stabilizer ↥E x)
  rw [hidx, horbcard, hstab] at hmul
  rw [← hmul]
  congr 1
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : (E ⊓ Subgroup.centralizer (H : Set G) : Subgroup G) ≤ E)).toEquiv

theorem exists_fourgroup [Finite G] (E T : Subgroup G) (hE : IsElemAbelian 3 E) (hT2 : IsPGroup 2 T)
    (hT : T ≠ ⊥) (hnorm : E ≤ Subgroup.normalizer (T : Set G))
    (hfix : ∀ x ∈ T, (∀ e ∈ E, e * x = x * e) → x = 1) :
    ∃ H : Subgroup G, H ≤ T ∧ H ≠ ⊥ ∧ E ≤ Subgroup.normalizer (H : Set G) ∧
      (∀ x ∈ H, x * x = 1 ∧ ∀ y ∈ H, x * y = y * x) ∧
      (∃ b ∈ E, b ∉ Subgroup.centralizer (H : Set G)) ∧
      (∀ b ∈ E, b ∉ Subgroup.centralizer (H : Set G) → ∀ x ∈ H, b * x = x * b → x = 1) ∧
      (∀ b ∈ E, b ∉ Subgroup.centralizer (H : Set G) → ∀ x ∈ H, x ≠ 1 →
        Nat.card E = 3 * Nat.card (E ⊓ Subgroup.centralizer (H : Set G) : Subgroup G) ∧
        b * x * b⁻¹ ≠ x ∧ b * x * b⁻¹ ≠ 1 ∧ b * (b * x * b⁻¹) * b⁻¹ = x * (b * x * b⁻¹) ∧
        b * (x * (b * x * b⁻¹)) * b⁻¹ = x ∧
        ∀ h ∈ H, h = 1 ∨ h = x ∨ h = b * x * b⁻¹ ∨ h = x * (b * x * b⁻¹)) := by
  obtain ⟨H, hH, hHT, hHnorm, hmin⟩ := exists_min_invariant E T hT hnorm
  have hH2 : IsPGroup 2 H := hT2.of_injective (Subgroup.inclusion hHT) (Subgroup.inclusion_injective hHT)
  have hex := min_invariant_elemAbelian hH2 hH hHnorm hmin
  have hexists : ∃ b ∈ E, b ∉ Subgroup.centralizer (H : Set G) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hH
    have : (x : G) = 1 := hfix x (hHT x.2) fun e he => by
      have := Subgroup.mem_centralizer_iff.1 (hcon e he) x x.2
      exact this.symm
    exact hx (Subtype.ext this)
  refine ⟨H, hHT, hH, hHnorm, hex, hexists, fun b hb hbc => min_invariant_fpf hE hHnorm hmin hb hbc,
    fun b hb hbc x hx hx1 => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := min_invariant_four hE hHnorm hmin hex hb hbc hx hx1
  exact ⟨min_invariant_card hE hHnorm hmin hex hb hbc hx hx1, h1, h2, h3, h4, h5⟩

end D3P

end CFSG.LocalAnalysis.GLTheoremA
