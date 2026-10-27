module

public import CFSG.Assembly.Defs

public section

namespace CFSG.GroupTheory.SevenInvolutionWreathLaw

open CFSG.Assembly

variable {K : Type*} [Group K]

@[expose] def InvolutionProductLaw (K : Type*) [Group K] : Prop :=
  ∀ z u v : K, orderOf z = 2 → orderOf u = 2 → orderOf v = 2 →
    u ∈ Subgroup.centralizer {z} → v ∈ Subgroup.centralizer {z} → u ≠ v → u ≠ z → v ≠ z →
      (u * v = v * u → u * v = z) ∧ (u * v ≠ v * u → (u * v) ^ 2 = z)

theorem mul_self_of_orderOf_eq_two {g : K} (hg : orderOf g = 2) : g * g = 1 := by
  rw [← sq, ← hg, pow_orderOf_eq_one]

theorem ne_one_of_orderOf_eq_two {g : K} (hg : orderOf g = 2) : g ≠ 1 := by
  rintro rfl
  rw [orderOf_one] at hg
  exact absurd hg (by norm_num)

theorem inv_eq_self_of_involution {g : K} (hg : orderOf g = 2) : g⁻¹ = g :=
  inv_eq_of_mul_eq_one_right (mul_self_of_orderOf_eq_two hg)

theorem adj_iff_ne_and_commute {a b : {g : K // orderOf g = 2}} :
    (involutionGraph K).Adj a b ↔ a ≠ b ∧ (a : K) * b = b * a := by
  rw [involutionGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨h, h' | h'⟩
    · exact ⟨h, h'⟩
    · exact ⟨h, h'.symm⟩
  · rintro ⟨h, h'⟩
    exact ⟨h, Or.inl h'⟩

theorem coe_ne_of_adj {a b : {g : K // orderOf g = 2}} (h : (involutionGraph K).Adj a b) :
    (a : K) ≠ b := fun h' => (adj_iff_ne_and_commute.mp h).1 (Subtype.ext h')

theorem commute_of_adj {a b : {g : K // orderOf g = 2}} (h : (involutionGraph K).Adj a b) :
    (a : K) * b = b * a :=
  (adj_iff_ne_and_commute.mp h).2

theorem mem_centralizer_of_adj {z u : {g : K // orderOf g = 2}}
    (h : (involutionGraph K).Adj z u) : (u : K) ∈ Subgroup.centralizer {(z : K)} :=
  Subgroup.mem_centralizer_singleton_iff.mpr (commute_of_adj h).symm

theorem not_commute_of_not_adj {a b : {g : K // orderOf g = 2}} (hab : a ≠ b)
    (h : ¬ (involutionGraph K).Adj a b) : (a : K) * b ≠ b * a :=
  fun h' => h (adj_iff_ne_and_commute.mpr ⟨hab, h'⟩)

theorem law_at {hlaw : InvolutionProductLaw K} {z u v : {g : K // orderOf g = 2}}
    (hzu : (involutionGraph K).Adj z u) (hzv : (involutionGraph K).Adj z v) (huv : u ≠ v) :
    ((u : K) * v = v * u → (u : K) * v = z) ∧ ((u : K) * v ≠ v * u → ((u : K) * v) ^ 2 = z) :=
  hlaw z u v z.2 u.2 v.2 (mem_centralizer_of_adj hzu) (mem_centralizer_of_adj hzv)
    (fun h => huv (Subtype.ext h)) (coe_ne_of_adj hzu).symm (coe_ne_of_adj hzv).symm

theorem exists_neighbor_partner (hlaw : InvolutionProductLaw K) (z u : {g : K // orderOf g = 2})
    (hzu : (involutionGraph K).Adj z u) :
    ∃ u' : {g : K // orderOf g = 2}, (u' : K) = z * u ∧ (involutionGraph K).Adj z u' ∧
      (involutionGraph K).Adj u u' ∧
      ∀ v, (involutionGraph K).Adj z v → (involutionGraph K).Adj u v → v = u' := by
  have hz := mul_self_of_orderOf_eq_two z.2
  have hu := mul_self_of_orderOf_eq_two u.2
  have hcomm := commute_of_adj hzu
  have hne := coe_ne_of_adj hzu
  have hord : orderOf ((z : K) * u) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ ?_
    · calc ((z : K) * u) ^ 2 = z * (u * z) * u := by rw [sq]; group
        _ = z * (z * u) * u := by rw [← hcomm]
        _ = (z * z) * (u * u) := by group
        _ = 1 := by rw [hz, hu, one_mul]
    · intro h
      apply hne
      calc (z : K) = z * (u * u) := by rw [hu, mul_one]
        _ = (z * u) * u := by group
        _ = u := by rw [h, one_mul]
  refine ⟨⟨(z : K) * u, hord⟩, rfl, ?_, ?_, ?_⟩
  · refine adj_iff_ne_and_commute.mpr ⟨fun h => ?_, ?_⟩
    · have h' : (z : K) = z * u := congrArg Subtype.val h
      exact ne_one_of_orderOf_eq_two u.2 (by
        calc (u : K) = (z : K)⁻¹ * (z * u) := by group
          _ = 1 := by rw [← h', inv_mul_cancel])
    · change (z : K) * (z * u) = z * u * z
      rw [mul_assoc, ← hcomm]
  · refine adj_iff_ne_and_commute.mpr ⟨fun h => ?_, ?_⟩
    · have h' : (u : K) = z * u := congrArg Subtype.val h
      exact ne_one_of_orderOf_eq_two z.2 (by
        calc (z : K) = (z * u) * (u : K)⁻¹ := by group
          _ = 1 := by rw [← h', mul_inv_cancel])
    · change (u : K) * (z * u) = z * u * u
      rw [← mul_assoc, ← hcomm]
  · intro v hzv huv
    have hne' : u ≠ v := (adj_iff_ne_and_commute.mp huv).1
    have h1 := (law_at (hlaw := hlaw) hzu hzv hne').1 (commute_of_adj huv)
    apply Subtype.ext
    change (v : K) = z * u
    calc (v : K) = (u * u) * v := by rw [hu, one_mul]
      _ = u * (u * v) := by group
      _ = u * z := by rw [h1]
      _ = z * u := hcomm.symm

theorem exists_kleinFour_of_triangle (hlaw : InvolutionProductLaw K)
    (a b c : {g : K // orderOf g = 2}) (hab : (involutionGraph K).Adj a b)
    (hbc : (involutionGraph K).Adj b c) (hac : (involutionGraph K).Adj a c) :
    ∃ V : Subgroup K, IsKleinFour V ∧ (V : Set K) \ {1} = {(a : K), (b : K), (c : K)} := by
  have ha := mul_self_of_orderOf_eq_two a.2
  have hb := mul_self_of_orderOf_eq_two b.2
  have hc := mul_self_of_orderOf_eq_two c.2
  have hab' := (adj_iff_ne_and_commute.mp hab).1
  have hbc' := (adj_iff_ne_and_commute.mp hbc).1
  have hac' := (adj_iff_ne_and_commute.mp hac).1
  have hbc_a : (b : K) * c = a := (law_at (hlaw := hlaw) hab hac hbc').1 (commute_of_adj hbc)
  have hcb_a : (c : K) * b = a := by rw [← commute_of_adj hbc, hbc_a]
  have hac_b : (a : K) * c = b :=
    (law_at (hlaw := hlaw) hab.symm hbc hac').1 (commute_of_adj hac)
  have hca_b : (c : K) * a = b := by rw [← commute_of_adj hac, hac_b]
  have hab_c : (a : K) * b = c :=
    (law_at (hlaw := hlaw) hac.symm hbc.symm hab').1 (commute_of_adj hab)
  have hba_c : (b : K) * a = c := by rw [← commute_of_adj hab, hab_c]
  let V : Subgroup K :=
    { carrier := {1, (a : K), (b : K), (c : K)}
      mul_mem' := by
        rintro x y (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;>
          simp [ha, hb, hc, hbc_a, hcb_a, hac_b, hca_b, hab_c, hba_c]
      one_mem' := Or.inl rfl
      inv_mem' := by
        rintro x (rfl | rfl | rfl | rfl)
        · simp
        · rw [inv_eq_self_of_involution a.2]
          exact Or.inr (Or.inl rfl)
        · rw [inv_eq_self_of_involution b.2]
          exact Or.inr (Or.inr (Or.inl rfl))
        · rw [inv_eq_self_of_involution c.2]
          exact Or.inr (Or.inr (Or.inr rfl)) }
  have hVset : (V : Set K) = {1, (a : K), (b : K), (c : K)} := rfl
  have ha1 := ne_one_of_orderOf_eq_two a.2
  have hb1 := ne_one_of_orderOf_eq_two b.2
  have hc1 := ne_one_of_orderOf_eq_two c.2
  have habK : (a : K) ≠ b := fun h => hab' (Subtype.ext h)
  have hbcK : (b : K) ≠ c := fun h => hbc' (Subtype.ext h)
  have hacK : (a : K) ≠ c := fun h => hac' (Subtype.ext h)
  refine ⟨V, ⟨?_, ?_⟩, ?_⟩
  · change Nat.card (V : Set K) = 4
    rw [Nat.card_coe_set_eq, hVset, Set.ncard_eq_four]
    exact ⟨1, a, b, c, ha1.symm, hb1.symm, hc1.symm, habK, hacK, hbcK, rfl⟩
  · have : Nontrivial V := ⟨⟨1, ⟨a, Or.inr (Or.inl rfl)⟩, fun h =>
      ha1 (congrArg Subtype.val h).symm⟩⟩
    refine (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr fun g hg => ?_
    have hg' : (g : K) ≠ 1 := fun h => hg (Subtype.ext h)
    rw [← Subgroup.orderOf_coe]
    rcases g.2 with h | h | h | h
    · exact absurd h hg'
    · rw [h]
      exact a.2
    · rw [h]
      exact b.2
    · rw [h]
      exact c.2
  · rw [hVset]
    ext g
    simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h | h | h | h, h1⟩
      · exact absurd h h1
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rintro (rfl | rfl | rfl)
      · exact ⟨Or.inr (Or.inl rfl), ha1⟩
      · exact ⟨Or.inr (Or.inr (Or.inl rfl)), hb1⟩
      · exact ⟨Or.inr (Or.inr (Or.inr rfl)), hc1⟩

theorem not_exists_induced_square (hlaw : InvolutionProductLaw K) :
    ¬ ∃ a b c d : {g : K // orderOf g = 2}, [a, b, c, d].Nodup ∧
      (involutionGraph K).Adj a b ∧ (involutionGraph K).Adj b c ∧
      (involutionGraph K).Adj c d ∧ (involutionGraph K).Adj d a ∧
      ¬ (involutionGraph K).Adj a c ∧ ¬ (involutionGraph K).Adj b d := by
  rintro ⟨a, b, c, d, hnd, hab, hbc, hcd, hda, hac, hbd⟩
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨-, hac', -⟩, ⟨-, hbd'⟩, -⟩ := hnd
  have hnc := not_commute_of_not_adj hac' hac
  have h1 := (law_at (hlaw := hlaw) hab.symm hbc hac').2 hnc
  have h2 := (law_at (hlaw := hlaw) hda hcd.symm hac').2 hnc
  exact hbd' (Subtype.ext (h1.symm.trans h2))

theorem eq_of_pentagon_relations {a u b v c : K} (ha : a * a = 1) (hu : u * u = 1)
    (hb : b * b = 1) (hc : c * c = 1) (hau : a * u = u * a) (hvc : v * c = c * v)
    (hca : c * a = a * c) (h1 : (a * b) ^ 2 = u) (h2 : (b * c) ^ 2 = v) (h3 : (u * c) ^ 2 = a)
    (h4 : (u * v) ^ 2 = b) : a = b := by
  rw [sq] at h1 h2 h3 h4
  have hA : b * a * b = a * u := by
    calc b * a * b = (a * a) * (b * a * b) := by rw [ha, one_mul]
      _ = a * ((a * b) * (a * b)) := by group
      _ = a * u := by rw [h1]
  have hcb : (c * b) * (c * b) = v := by
    calc (c * b) * (c * b) = c * ((b * c) * (b * c)) * c⁻¹ := by group
      _ = c * v * c⁻¹ := by rw [h2]
      _ = v := by rw [← hvc, mul_inv_cancel_right]
  have hB : b * c * b = c * v := by
    calc b * c * b = (c * c) * (b * c * b) := by rw [hc, one_mul]
      _ = c * ((c * b) * (c * b)) := by group
      _ = c * v := by rw [hcb]
  have hcu : (c * u) * (c * u) = a := by
    calc (c * u) * (c * u) = c * ((u * c) * (u * c)) * c⁻¹ := by group
      _ = c * a * c⁻¹ := by rw [h3]
      _ = a := by rw [hca, mul_inv_cancel_right]
  have hC : u * c = c * u * a := by
    calc u * c = c⁻¹ * ((c * u) * (c * u)) * u⁻¹ := by group
      _ = c⁻¹ * a * u⁻¹ := by rw [hcu]
      _ = c * (a * u) := by
        rw [inv_eq_of_mul_eq_one_right hc, inv_eq_of_mul_eq_one_right hu, mul_assoc]
      _ = c * u * a := by rw [hau, mul_assoc]
  have hD : b * (a * c) * b = c * u * v := by
    calc b * (a * c) * b = b * a * (b * b) * c * b := by rw [hb, mul_one, mul_assoc b a c]
      _ = (b * a * b) * (b * c * b) := by group
      _ = a * (u * c) * v := by rw [hA, hB]; group
      _ = a * (c * u * a) * v := by rw [hC]
      _ = (a * c) * u * a * v := by group
      _ = (c * a) * u * a * v := by rw [hca]
      _ = c * (a * u) * a * v := by group
      _ = c * (u * a) * a * v := by rw [hau]
      _ = c * u * (a * a) * v := by group
      _ = c * u * v := by rw [ha, mul_one]
  have hE : (c * u * v) * (c * u * v) = a * b := by
    calc (c * u * v) * (c * u * v) = c * u * (v * c) * u * v := by group
      _ = c * u * (c * v) * u * v := by rw [hvc]
      _ = c * (u * c) * (v * u * v) := by group
      _ = c * (c * u * a) * (v * u * v) := by rw [hC]
      _ = (c * c) * (u * a) * (v * u * v) := by group
      _ = (u * a) * (v * u * v) := by rw [hc, one_mul]
      _ = (a * u) * (v * u * v) := by rw [hau]
      _ = a * ((u * v) * (u * v)) := by group
      _ = a * b := by rw [h4]
  have hac2 : (a * c) * (a * c) = 1 := by
    calc (a * c) * (a * c) = a * (c * a) * c := by group
      _ = a * (a * c) * c := by rw [hca]
      _ = (a * a) * (c * c) := by group
      _ = 1 := by rw [ha, hc, one_mul]
  have hF : (b * (a * c) * b) * (b * (a * c) * b) = 1 := by
    calc (b * (a * c) * b) * (b * (a * c) * b) = b * (a * c) * (b * b) * (a * c) * b := by
          group
      _ = b * ((a * c) * (a * c)) * b := by rw [hb, mul_one]; group
      _ = b * b := by rw [hac2, mul_one]
      _ = 1 := hb
  rw [hD, hE] at hF
  rw [eq_inv_of_mul_eq_one_left hF, inv_eq_of_mul_eq_one_right hb]

theorem not_exists_induced_pentagon (hlaw : InvolutionProductLaw K) :
    ¬ ∃ a b c d e : {g : K // orderOf g = 2}, [a, b, c, d, e].Nodup ∧
      (involutionGraph K).Adj a b ∧ (involutionGraph K).Adj b c ∧
      (involutionGraph K).Adj c d ∧ (involutionGraph K).Adj d e ∧
      (involutionGraph K).Adj e a ∧ ¬ (involutionGraph K).Adj a c ∧
      ¬ (involutionGraph K).Adj a d ∧ ¬ (involutionGraph K).Adj b d ∧
      ¬ (involutionGraph K).Adj b e ∧ ¬ (involutionGraph K).Adj c e := by
  rintro ⟨a, b, c, d, e, hnd, hab, hbc, hcd, hde, hea, hac, had, hbd, hbe, hce⟩
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨-, hac', had', -⟩, ⟨-, hbd', hbe'⟩, ⟨-, hce'⟩, -⟩ := hnd
  have h1 := (law_at (hlaw := hlaw) hab.symm hbc hac').2 (not_commute_of_not_adj hac' hac)
  have h2 := (law_at (hlaw := hlaw) hcd.symm hde hce').2 (not_commute_of_not_adj hce' hce)
  have h3 := (law_at (hlaw := hlaw) hab hea.symm hbe').2 (not_commute_of_not_adj hbe' hbe)
  have h4 := (law_at (hlaw := hlaw) hbc.symm hcd hbd').2 (not_commute_of_not_adj hbd' hbd)
  have hac'' : a ≠ c := hac'
  exact hac'' (Subtype.ext (eq_of_pentagon_relations (mul_self_of_orderOf_eq_two a.2)
    (mul_self_of_orderOf_eq_two b.2) (mul_self_of_orderOf_eq_two c.2)
    (mul_self_of_orderOf_eq_two e.2) (commute_of_adj hab) (commute_of_adj hde)
    (commute_of_adj hea) h1 h2 h3 h4))

theorem ncard_neighborSet_eq_six (z : {g : K // orderOf g = 2})
    (hcount : {g : K | g ∈ Subgroup.centralizer {(z : K)} ∧ orderOf g = 2}.ncard = 7) :
    ((involutionGraph K).neighborSet z).ncard = 6 := by
  have himage : Subtype.val '' (involutionGraph K).neighborSet z =
      {g : K | g ∈ Subgroup.centralizer {(z : K)} ∧ orderOf g = 2} \ {(z : K)} := by
    ext g
    simp only [Set.mem_image, SimpleGraph.mem_neighborSet, Set.mem_sdiff, Set.mem_ofPred_eq,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨u, hzu, rfl⟩
      exact ⟨⟨mem_centralizer_of_adj hzu, u.2⟩, (coe_ne_of_adj hzu).symm⟩
    · rintro ⟨⟨hg, hg2⟩, hgz⟩
      refine ⟨⟨g, hg2⟩, adj_iff_ne_and_commute.mpr ⟨fun h => hgz ?_, ?_⟩, rfl⟩
      · exact (congrArg Subtype.val h).symm
      · exact (Subgroup.mem_centralizer_singleton_iff.mp hg).symm
  have hzmem : (z : K) ∈ {g : K | g ∈ Subgroup.centralizer {(z : K)} ∧ orderOf g = 2} :=
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, z.2⟩
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective, himage,
    Set.ncard_sdiff_singleton_of_mem hzmem, hcount]

end CFSG.GroupTheory.SevenInvolutionWreathLaw
