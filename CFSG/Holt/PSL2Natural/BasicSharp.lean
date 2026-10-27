module

public import CFSG.Holt.ThreePoint
public import CFSG.Holt.Basic

public section

namespace CFSG.Holt

open MulAction

structure IsSharplyThreeTransitive (G Ω : Type*) [Group G] [MulAction G Ω] : Prop where
  exists_smul_eq : ∀ {a b c a' b' c' : Ω}, a ≠ b → a ≠ c → b ≠ c → a' ≠ b' → a' ≠ c' →
    b' ≠ c' → ∃ g : G, g • a = a' ∧ g • b = b' ∧ g • c = c'
  eq_one_of_smul_eq : ∀ {g : G} {a b c : Ω}, a ≠ b → a ≠ c → b ≠ c → g • a = a → g • b = b →
    g • c = c → g = 1

private theorem exists_ne_ne_of_three_le_card {Ω : Type*} [Finite Ω] (h3 : 3 ≤ Nat.card Ω)
    (a b : Ω) : ∃ c : Ω, c ≠ a ∧ c ≠ b :=
  ENat.exists_ne_ne_of_three_le (by rw [ENat.card_eq_coe_natCard]; exact_mod_cast h3) a b

private theorem card_ne_ne {Ω : Type*} [Finite Ω] {a b : Ω} (hab : a ≠ b) :
    Nat.card {x : Ω // x ≠ a ∧ x ≠ b} = Nat.card Ω - 2 := by
  classical
  have := Fintype.ofFinite Ω
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have h := Fintype.card_subtype_compl (fun x : Ω => x = a ∨ x = b)
  rw [Fintype.card_subtype_eq_or_eq_of_ne hab] at h
  rw [← h]
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun x => by simp [not_or]))

private theorem card_ne {Ω : Type*} [Finite Ω] (a : Ω) :
    Nat.card {x : Ω // x ≠ a} = Nat.card Ω - 1 := by
  classical
  have := Fintype.ofFinite Ω
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Set.card_ne_eq a

@[expose] def unipotentRadical (G : Type*) [Group G] {Ω : Type*} [MulAction G Ω] (a : Ω) :
    Subgroup G :=
  Subgroup.closure {g : G | orderOf g = 2 ∧ g • a = a}

namespace IsSharplyThreeTransitive

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω] (hS : IsSharplyThreeTransitive G Ω)
include hS

theorem isMultiplyPretransitive : IsMultiplyPretransitive G Ω 3 :=
  isMultiplyPretransitive_three_iff.mpr hS.exists_smul_eq

theorem existsUnique_smul_eq {a b c a' b' c' : Ω} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha'b' : a' ≠ b') (ha'c' : a' ≠ c') (hb'c' : b' ≠ c') :
    ∃! g : G, g • a = a' ∧ g • b = b' ∧ g • c = c' := by
  obtain ⟨g, hga, hgb, hgc⟩ := hS.exists_smul_eq hab hac hbc ha'b' ha'c' hb'c'
  refine ⟨g, ⟨hga, hgb, hgc⟩, fun h ⟨hha, hhb, hhc⟩ => ?_⟩
  have key : g⁻¹ * h = 1 := hS.eq_one_of_smul_eq hab hac hbc
    (by rw [mul_smul, hha, ← hga, inv_smul_smul]) (by rw [mul_smul, hhb, ← hgb, inv_smul_smul])
    (by rw [mul_smul, hhc, ← hgc, inv_smul_smul])
  exact (inv_mul_eq_one.mp key).symm

theorem stabilizer_inf_inf_eq_bot {a b c : Ω} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    stabilizer G a ⊓ stabilizer G b ⊓ stabilizer G c = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨⟨ha, hb⟩, hc⟩ := hg
  exact (Subgroup.mem_bot).mpr (hS.eq_one_of_smul_eq hab hac hbc ha hb hc)

theorem existsUnique_stabilizer_inf_smul_eq {a b c c' : Ω} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (hac' : a ≠ c') (hbc' : b ≠ c') :
    ∃! h : ↥(stabilizer G a ⊓ stabilizer G b), h • c = c' := by
  obtain ⟨g, ⟨hga, hgb, hgc⟩, hu⟩ := hS.existsUnique_smul_eq hab hac hbc hab hac' hbc'
  refine ⟨⟨g, hga, hgb⟩, hgc, fun h hh => Subtype.ext ?_⟩
  exact hu h ⟨h.2.1, h.2.2, hh⟩

theorem isPretransitive [Finite Ω] (h3 : 3 ≤ Nat.card Ω) : IsPretransitive G Ω :=
  have := hS.isMultiplyPretransitive
  isPretransitive_of_isMultiplyPretransitive_three h3

theorem existsUnique_fixed [Finite Ω] (hodd : Odd (Nat.card Ω)) {g : G} (hg : orderOf g = 2) :
    ∃! a : Ω, g • a = a := by
  have hP := isPGroup_zpowers_of_orderOf_eq_two hg
  obtain ⟨a, ha⟩ := fixSet_nonempty_of_odd hodd hP
  rw [fixSet_zpowers, mem_fixedBy] at ha
  refine ⟨a, ha, fun b hb => ?_⟩
  by_contra hba
  have hodd' := odd_card_fixSet_of_odd hodd hP
  rw [fixSet_zpowers] at hodd'
  have : Nontrivial (fixedBy Ω g) :=
    ⟨⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hba (congrArg Subtype.val h).symm⟩⟩
  have h2 := Finite.one_lt_card (α := fixedBy Ω g)
  obtain ⟨c, hca, hcb⟩ := exists_ne_ne_of_three_le_card (Ω := fixedBy Ω g)
    (by obtain ⟨k, hk⟩ := hodd'; omega) ⟨a, ha⟩ ⟨b, hb⟩
  have h1 : g = 1 := hS.eq_one_of_smul_eq (Ne.symm hba)
    (fun h => hca (Subtype.ext h.symm)) (fun h => hcb (Subtype.ext h.symm)) ha hb c.2
  rw [h1, orderOf_one] at hg
  exact absurd hg (by decide)

theorem eq_of_smul_eq_of_sq_eq_one {s t : G} (hs : s ^ 2 = 1) (ht : t ^ 2 = 1) {a b c : Ω}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hsa : s • a = a) (hta : t • a = a)
    (hsb : s • b = c) (htb : t • b = c) : s = t := by
  have hsc : s • c = b := by rw [← hsb, ← mul_smul, ← pow_two, hs, one_smul]
  have htc : t • c = b := by rw [← htb, ← mul_smul, ← pow_two, ht, one_smul]
  have key : s * t = 1 := hS.eq_one_of_smul_eq hab hac hbc (by rw [mul_smul, hta, hsa])
    (by rw [mul_smul, htb, hsc]) (by rw [mul_smul, htc, hsb])
  rw [mul_eq_one_iff_eq_inv] at key
  rw [key]
  exact inv_eq_of_mul_eq_one_right (by rw [← pow_two, ht])

theorem card_stabilizer_inf [Finite Ω] (h3 : 3 ≤ Nat.card Ω) {a b : Ω} (hab : a ≠ b) :
    Nat.card ↥(stabilizer G a ⊓ stabilizer G b) = Nat.card Ω - 2 := by
  obtain ⟨c, hca, hcb⟩ := exists_ne_ne_of_three_le_card h3 a b
  rw [← card_ne_ne hab]
  refine Nat.card_eq_of_bijective
    (fun h => ⟨h • c, fun e => hca (smul_left_cancel (h : G) (e.trans h.2.1.symm)),
      fun e => hcb (smul_left_cancel (h : G) (e.trans h.2.2.symm))⟩) ⟨fun h h' e => ?_, ?_⟩
  · obtain ⟨w, -, hu⟩ := hS.existsUnique_stabilizer_inf_smul_eq hab (Ne.symm hca) (Ne.symm hcb)
      (a := a) (b := b) (c := c) (c' := h • c) (fun e => hca (smul_left_cancel (h : G)
        (e.symm.trans h.2.1.symm))) (fun e => hcb (smul_left_cancel (h : G)
        (e.symm.trans h.2.2.symm)))
    exact (hu h rfl).trans (hu h' (congrArg Subtype.val e).symm).symm
  · rintro ⟨x, hxa, hxb⟩
    obtain ⟨h, hh, -⟩ := hS.existsUnique_stabilizer_inf_smul_eq hab (Ne.symm hca) (Ne.symm hcb)
      (Ne.symm hxa) (Ne.symm hxb)
    exact ⟨h, Subtype.ext hh⟩

theorem exists_regular_subgroup [Finite Ω] (h3 : 3 ≤ Nat.card Ω)
    (hU : ∃ (a₀ : Ω) (U : Subgroup G), (∀ u ∈ U, u • a₀ = a₀ ∧ u ^ 2 = 1) ∧
      ∀ b c, b ≠ a₀ → c ≠ a₀ → ∃ u ∈ U, u • b = c) (a : Ω) :
    ∃ U : Subgroup G, (∀ u ∈ U, u • a = a ∧ u ^ 2 = 1) ∧
      ∀ b c, b ≠ a → c ≠ a → ∃ u ∈ U, u • b = c := by
  obtain ⟨a₀, U, hU1, hU2⟩ := hU
  have := hS.isPretransitive h3
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G a₀ a
  refine ⟨U.map (MulAut.conj g).toMonoidHom, ?_, fun b c hb hc => ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    refine ⟨?_, ?_⟩
    · change (g * u * g⁻¹) • a = a
      rw [← hg, mul_smul, mul_smul, inv_smul_smul, (hU1 u hu).1]
    · change (g * u * g⁻¹) ^ 2 = 1
      rw [conj_pow, (hU1 u hu).2, mul_one, mul_inv_cancel]
  · have hb' : g⁻¹ • b ≠ a₀ := fun h => hb (by rw [← hg, ← h, smul_inv_smul])
    have hc' : g⁻¹ • c ≠ a₀ := fun h => hc (by rw [← hg, ← h, smul_inv_smul])
    obtain ⟨u, hu, huc⟩ := hU2 _ _ hb' hc'
    refine ⟨g * u * g⁻¹, ⟨u, hu, rfl⟩, ?_⟩
    rw [mul_smul, mul_smul, huc, smul_inv_smul]

theorem mem_unipotentRadical_iff [Finite Ω] (hodd : Odd (Nat.card Ω)) (h3 : 3 ≤ Nat.card Ω)
    (hU : ∃ (a₀ : Ω) (U : Subgroup G), (∀ u ∈ U, u • a₀ = a₀ ∧ u ^ 2 = 1) ∧
      ∀ b c, b ≠ a₀ → c ≠ a₀ → ∃ u ∈ U, u • b = c) {a : Ω} {g : G} :
    g ∈ unipotentRadical G a ↔ g • a = a ∧ g ^ 2 = 1 := by
  obtain ⟨U, hU1, hU2⟩ := hS.exists_regular_subgroup h3 hU a
  have key : ∀ g : G, g • a = a → g ^ 2 = 1 → g ∈ U := by
    intro g hga hg2
    by_cases hg1 : g = 1
    · rw [hg1]
      exact U.one_mem
    obtain ⟨x, -, hxu⟩ := hS.existsUnique_fixed hodd (orderOf_eq_prime hg2 hg1)
    obtain ⟨b, hba, -⟩ := exists_ne_ne_of_three_le_card h3 a a
    have hgb : g • b ≠ b := fun h => hba ((hxu b h).trans (hxu a hga).symm)
    have hgba : g • b ≠ a := fun h => hba (smul_left_cancel g (h.trans hga.symm))
    obtain ⟨u, hu, hub⟩ := hU2 b (g • b) hba hgba
    rw [← hS.eq_of_smul_eq_of_sq_eq_one (hU1 u hu).2 hg2 (Ne.symm hba) (Ne.symm hgba)
      (Ne.symm hgb) (hU1 u hu).1 hga hub rfl]
    exact hu
  have hUeq : unipotentRadical G a = U := by
    refine le_antisymm ((Subgroup.closure_le U).mpr ?_) fun u hu => ?_
    · rintro g ⟨hgo, hga⟩
      exact key g hga (hgo ▸ pow_orderOf_eq_one g)
    · by_cases hu1 : u = 1
      · rw [hu1]
        exact Subgroup.one_mem _
      · exact Subgroup.subset_closure ⟨orderOf_eq_prime (hU1 u hu).2 hu1, (hU1 u hu).1⟩
  rw [hUeq]
  exact ⟨hU1 g, fun h => key g h.1 h.2⟩

omit hS in
theorem mul_comm_of_mem_unipotentRadical {a : Ω}
    (hmem : ∀ g : G, g ∈ unipotentRadical G a ↔ g • a = a ∧ g ^ 2 = 1) {u v : G}
    (hu : u ∈ unipotentRadical G a) (hv : v ∈ unipotentRadical G a) : u * v = v * u := by
  have huv := ((hmem _).mp (mul_mem hu hv)).2
  have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right (by rw [← pow_two, ((hmem u).mp hu).2])
  have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right (by rw [← pow_two, ((hmem v).mp hv).2])
  calc u * v = (u * v)⁻¹ := (inv_eq_of_mul_eq_one_right (by rw [← pow_two, huv])).symm
    _ = v * u := by rw [mul_inv_rev, hu', hv']

omit hS in
theorem isMulCommutative_unipotentRadical {a : Ω}
    (hmem : ∀ g : G, g ∈ unipotentRadical G a ↔ g • a = a ∧ g ^ 2 = 1) :
    IsMulCommutative (unipotentRadical G a) :=
  ⟨⟨fun u v => Subtype.ext (mul_comm_of_mem_unipotentRadical hmem u.2 v.2)⟩⟩

theorem existsUnique_unipotentRadical_smul_eq [Finite Ω] (hodd : Odd (Nat.card Ω)) {a b c : Ω}
    (hmem : ∀ g : G, g ∈ unipotentRadical G a ↔ g • a = a ∧ g ^ 2 = 1) (hb : b ≠ a)
    (hc : c ≠ a) : ∃! u : ↥(unipotentRadical G a), u • b = c := by
  have triv : ∀ w : G, w • a = a → w ^ 2 = 1 → w • b = b → w = 1 := by
    intro w hwa hw2 hwb
    by_contra hw1
    obtain ⟨x, -, hxu⟩ := hS.existsUnique_fixed hodd (orderOf_eq_prime hw2 hw1)
    exact hb ((hxu b hwb).trans (hxu a hwa).symm)
  by_cases hbc : b = c
  · subst hbc
    refine ⟨1, one_smul _ _, fun v hv => Subtype.ext ?_⟩
    obtain ⟨hva, hv2⟩ := (hmem v).mp v.2
    exact triv v hva hv2 hv
  · obtain ⟨g, hga, hgb, hgc⟩ := hS.exists_smul_eq (Ne.symm hb) (Ne.symm hc) hbc (Ne.symm hc)
      (Ne.symm hb) (Ne.symm hbc)
    have hg2 : g ^ 2 = 1 := hS.eq_one_of_smul_eq (Ne.symm hb) (Ne.symm hc) hbc
      (by rw [pow_two, mul_smul, hga, hga]) (by rw [pow_two, mul_smul, hgb, hgc])
      (by rw [pow_two, mul_smul, hgc, hgb])
    refine ⟨⟨g, (hmem g).mpr ⟨hga, hg2⟩⟩, hgb, fun v hv => Subtype.ext ?_⟩
    obtain ⟨hva, hv2⟩ := (hmem v).mp v.2
    exact hS.eq_of_smul_eq_of_sq_eq_one hv2 hg2 (Ne.symm hb) (Ne.symm hc) hbc hva hga hv hgb

theorem card_unipotentRadical [Finite Ω] (hodd : Odd (Nat.card Ω)) (h3 : 3 ≤ Nat.card Ω)
    {a : Ω} (hmem : ∀ g : G, g ∈ unipotentRadical G a ↔ g • a = a ∧ g ^ 2 = 1) :
    Nat.card ↥(unipotentRadical G a) = Nat.card Ω - 1 := by
  obtain ⟨b, hba, -⟩ := exists_ne_ne_of_three_le_card h3 a a
  rw [← card_ne a]
  have hne : ∀ u : ↥(unipotentRadical G a), u • b ≠ a := fun u e =>
    hba (smul_left_cancel (u : G) (e.trans ((hmem u).mp u.2).1.symm))
  refine Nat.card_eq_of_bijective (fun u => ⟨u • b, hne u⟩) ⟨fun u v e => ?_, fun x => ?_⟩
  · obtain ⟨w, -, hw⟩ := hS.existsUnique_unipotentRadical_smul_eq hodd hmem hba (hne u)
    exact (hw u rfl).trans (hw v (congrArg Subtype.val e).symm).symm
  · obtain ⟨u, hu, -⟩ := hS.existsUnique_unipotentRadical_smul_eq hodd hmem hba x.2
    exact ⟨u, Subtype.ext hu⟩

theorem of_equivariant {H Δ : Type*} [Group H] [MulAction H Δ] (φ : G ≃* H) (ψ : Ω ≃ Δ)
    (hψ : ∀ g p, ψ (g • p) = φ g • ψ p) : IsSharplyThreeTransitive H Δ := by
  have key : ∀ (h : H) (x : Δ), h • x = ψ (φ.symm h • ψ.symm x) := fun h x => by
    rw [hψ, MulEquiv.apply_symm_apply, Equiv.apply_symm_apply]
  have inj : ∀ {x y : Δ}, x ≠ y → ψ.symm x ≠ ψ.symm y := fun h e => h (ψ.symm.injective e)
  refine ⟨fun hab hac hbc ha'b' ha'c' hb'c' => ?_, fun {h a b c} hab hac hbc ha hb hc => ?_⟩
  · obtain ⟨g, hga, hgb, hgc⟩ :=
      hS.exists_smul_eq (inj hab) (inj hac) (inj hbc) (inj ha'b') (inj ha'c') (inj hb'c')
    refine ⟨φ g, ?_, ?_, ?_⟩ <;>
      rw [key, MulEquiv.symm_apply_apply] <;> simp only [hga, hgb, hgc, Equiv.apply_symm_apply]
  · have fix : ∀ {x : Δ}, h • x = x → φ.symm h • ψ.symm x = ψ.symm x := fun {x} hx => by
      apply ψ.injective
      rw [Equiv.apply_symm_apply, ← key, hx]
    have h1 := hS.eq_one_of_smul_eq (inj hab) (inj hac) (inj hbc) (fix ha) (fix hb) (fix hc)
    rw [← φ.apply_symm_apply h, h1, map_one]

end IsSharplyThreeTransitive

end CFSG.Holt
