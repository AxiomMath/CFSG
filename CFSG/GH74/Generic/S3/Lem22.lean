module

public import CFSG.GH74.Generic.S3.Lem23

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.ABGLocalTools Subgroup
open scoped MatrixGroups

section Lemma22

variable {G : Type} [Group G] {V : Subgroup G} {w v v₁ : G}

theorem mem_V_iff (hs : Count23Setup V w) (hv : v ∈ Vsharp V) (hv₁ : v₁ ∈ Vsharp V) (hne : v ≠ v₁)
    (a : G) : a ∈ V ↔ a = 1 ∨ a = v ∨ a = v₁ ∨ a = v * v₁ := by
  constructor
  · intro ha
    have hVc : (V : Set G).ncard = 4 := by
      have h : Nat.card ↥V = (V : Set G).ncard := Nat.card_coe_set_eq (V : Set G)
      rw [← h, hs.card_V]
    have hfin : (V : Set G).Finite := Set.finite_of_ncard_ne_zero (by rw [hVc]; norm_num)
    have hv1 : v ≠ 1 := hv.2
    have hv₁1 : v₁ ≠ 1 := hv₁.2
    have hvv₁ : v * v₁ ≠ 1 := by
      intro h
      apply hne
      have h2 : v₁ * v₁ = 1 := hs.V_sq v₁ hv₁.1
      calc v = v * (v₁ * v₁) := by rw [h2, mul_one]
        _ = (v * v₁) * v₁ := by rw [mul_assoc]
        _ = v₁ := by rw [h, one_mul]
    have hS : ({1, v, v₁, v * v₁} : Set G) ⊆ (V : Set G) := by
      intro x hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact V.one_mem
      · exact hv.1
      · exact hv₁.1
      · exact V.mul_mem hv.1 hv₁.1
    have hScard : ({1, v, v₁, v * v₁} : Set G).ncard = 4 := by
      have e1 : (1 : G) ≠ v := hv1.symm
      have e2 : (1 : G) ≠ v₁ := hv₁1.symm
      have e3 : (1 : G) ≠ v * v₁ := hvv₁.symm
      have e5 : v ≠ v * v₁ := fun h => hv₁1 (by
        calc v₁ = v⁻¹ * (v * v₁) := by group
          _ = v⁻¹ * v := by rw [← h]
          _ = 1 := by group)
      have e6 : v₁ ≠ v * v₁ := fun h => hv1 (by
        calc v = (v * v₁) * v₁⁻¹ := by group
          _ = v₁ * v₁⁻¹ := by rw [← h]
          _ = 1 := by group)
      rw [Set.ncard_insert_of_notMem (by simp [e1, e2, e3]),
        Set.ncard_insert_of_notMem (by simp [hne, e5]), Set.ncard_pair e6]
    have heq := Set.eq_of_subset_of_ncard_le hS (by rw [hVc, hScard]) hfin
    have : a ∈ ({1, v, v₁, v * v₁} : Set G) := by rw [heq]; exact ha
    simpa [or_assoc] using this
  · rintro (rfl | rfl | rfl | rfl)
    · exact V.one_mem
    · exact hv.1
    · exact hv₁.1
    · exact V.mul_mem hv.1 hv₁.1




@[expose] def NormV (V : Subgroup G) (n : G) : Prop := ∀ a ∈ V, n * a * n⁻¹ ∈ V

theorem NormV.one : NormV V 1 := fun a ha => by simpa using ha

theorem NormV.mul {m n : G} (hm : NormV V m) (hn : NormV V n) : NormV V (m * n) := by
  intro a ha
  have := hm _ (hn a ha)
  have e : m * (n * a * n⁻¹) * m⁻¹ = m * n * a * (m * n)⁻¹ := by group
  rwa [e] at this

theorem NormV.inv [Finite G] {n : G} (h : NormV V n) : NormV V n⁻¹ := by
  intro a ha
  let f : ↥V → ↥V := fun b => ⟨n * b * n⁻¹, h b b.2⟩
  have hinj : Function.Injective f := by
    intro b c hbc
    have h1 : n * (b : G) * n⁻¹ = n * (c : G) * n⁻¹ := congrArg Subtype.val hbc
    exact Subtype.ext (by simpa using h1)
  obtain ⟨b, hb⟩ := Finite.surjective_of_injective hinj ⟨a, ha⟩
  have hb' : n * (b : G) * n⁻¹ = a := congrArg Subtype.val hb
  have : n⁻¹ * a * n⁻¹⁻¹ = b := by rw [← hb']; group
  rw [this]
  exact b.2

theorem V_comm_winv (hs : Count23Setup V w) {a : G} (ha : a ∈ V) : a * w⁻¹ = w⁻¹ * a := by
  have hc : a * w = w * a := hs.w_comm a ha
  have hinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hs.w_sq
  rw [hinv]; exact hc

theorem Wset_sq (hs : Count23Setup V w) {x : G} (hx : x ∈ Wset V w) : x * x = 1 := by
  have h1 : w * x ∈ V := hx
  have h2 : w * x * (w * x) = 1 := hs.V_sq _ h1
  have hc' : (w * x) * w⁻¹ = w⁻¹ * (w * x) := V_comm_winv hs h1
  have hinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hs.w_sq
  calc x * x = (w⁻¹ * (w * x)) * (w⁻¹ * (w * x)) := by group
    _ = w⁻¹ * ((w * x) * w⁻¹) * (w * x) := by group
    _ = w⁻¹ * (w⁻¹ * (w * x)) * (w * x) := by rw [hc']
    _ = (w⁻¹ * w⁻¹) * ((w * x) * (w * x)) := by group
    _ = 1 := by rw [h2, mul_one, hinv, hs.w_sq]

theorem Wset_mul_Wset (hs : Count23Setup V w) {x y : G} (hx : x ∈ Wset V w) (hy : y ∈ Wset V w) :
    x * y ∈ V := by
  have h1 : w * x ∈ V := hx
  have h2 : w * y ∈ V := hy
  have hc : (w * x) * w = w * (w * x) := hs.w_comm _ h1
  have hw2 : w * w = 1 := hs.w_sq
  have hc' : (w * x) * w⁻¹ = w⁻¹ * (w * x) := by
    have hinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
    rw [hinv]; exact hc
  have e : x * y = (w * x) * (w * y) := by
    calc x * y = w⁻¹ * (w * x) * (w⁻¹ * (w * y)) := by group
      _ = w⁻¹ * ((w * x) * w⁻¹) * (w * y) := by group
      _ = w⁻¹ * (w⁻¹ * (w * x)) * (w * y) := by rw [hc']
      _ = (w⁻¹ * w⁻¹) * (w * x) * (w * y) := by group
      _ = (w * x) * (w * y) := by
          have hinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
          rw [hinv, hw2, one_mul]
  rw [e]
  exact V.mul_mem h1 h2

variable {g h : G}

theorem normV_of_cycle (hs : Count23Setup V w) (hv : v ∈ Vsharp V) (hv₁ : v₁ ∈ Vsharp V)
    (hne : v ≠ v₁) {g : G} (hg_v : g * v * g⁻¹ = v * v₁) (hg_v₁ : g * v₁ * g⁻¹ = v) :
    NormV V g := by
  have hv2 : v * v = 1 := hs.V_sq v hv.1
  have hvv₁ : v * v₁ = v₁ * v := hs.V_comm v hv.1 v₁ hv₁.1
  have hVmem := mem_V_iff hs hv hv₁ hne
  intro a ha
  rcases (hVmem a).1 ha with rfl | rfl | rfl | rfl
  · simp
  · rw [hg_v]; exact V.mul_mem hv.1 hv₁.1
  · rw [hg_v₁]; exact hv.1
  · have : g * (v * v₁) * g⁻¹ = v₁ := by
      calc g * (v * v₁) * g⁻¹ = (g * v * g⁻¹) * (g * v₁ * g⁻¹) := by group
        _ = (v * v₁) * v := by rw [hg_v, hg_v₁]
        _ = (v * v) * v₁ := by
            calc (v * v₁) * v = v * (v₁ * v) := by rw [mul_assoc]
              _ = v * (v * v₁) := by rw [hvv₁]
              _ = (v * v) * v₁ := by rw [mul_assoc]
        _ = v₁ := by rw [hv2, one_mul]
    rw [this]; exact hv₁.1


theorem lemma22_elem [Finite G] (hs : Count23Setup V w) (hv : v ∈ Vsharp V) (hv₁ : v₁ ∈ Vsharp V)
    (hne : v ≠ v₁) (hg_v : g * v * g⁻¹ = v * v₁) (hg_v₁ : g * v₁ * g⁻¹ = v)
    (hg_wv : g * (w * v) = (w * v) * g) (hh_v : h * v * h⁻¹ = v * v₁)
    (hh_v₁ : h * v₁ * h⁻¹ = v) (hh_w : h * w = w * h) (hnc : ¬ IsConj v w) :
    (∀ x ∈ Wset V w, ∃ n : G, NormV V n ∧ NormV V n⁻¹ ∧ n * w * n⁻¹ = x) ∧
      (∀ a ∈ V, ¬ IsConj w a) ∧
      (∀ n : G, (∀ x, (x ∈ V ∨ x ∈ Wset V w) → (n * x * n⁻¹ ∈ V ∨ n * x * n⁻¹ ∈ Wset V w)) →
        NormV V n) := by
  have hv2 : v * v = 1 := hs.V_sq v hv.1
  have hv₁2 : v₁ * v₁ = 1 := hs.V_sq v₁ hv₁.1
  have hw2 : w * w = 1 := hs.w_sq
  have hvv₁ : v * v₁ = v₁ * v := hs.V_comm v hv.1 v₁ hv₁.1
  have hVmem := mem_V_iff hs hv hv₁ hne
  have hgwv' : g * (w * v) * g⁻¹ = w * v := by
    rw [hg_wv, mul_assoc, mul_inv_cancel, mul_one]
  have hgw : g * w * g⁻¹ = w * v₁ := by
    calc g * w * g⁻¹ = g * ((w * v) * v) * g⁻¹ := by rw [mul_assoc w v v, hv2, mul_one]
      _ = (g * (w * v) * g⁻¹) * (g * v * g⁻¹) := by group
      _ = (w * v) * (v * v₁) := by rw [hgwv', hg_v]
      _ = w * v₁ := by
          calc (w * v) * (v * v₁) = w * (v * v) * v₁ := by group
            _ = w * v₁ := by rw [hv2, mul_one]
  have hgwv₁ : g * (w * v₁) * g⁻¹ = w * (v * v₁) := by
    calc g * (w * v₁) * g⁻¹ = (g * w * g⁻¹) * (g * v₁ * g⁻¹) := by group
      _ = (w * v₁) * v := by rw [hgw, hg_v₁]
      _ = w * (v₁ * v) := by rw [mul_assoc]
      _ = w * (v * v₁) := by rw [hvv₁]
  have hhw : h * w * h⁻¹ = w := by
    rw [hh_w, mul_assoc, mul_inv_cancel, mul_one]
  have hhg : (h * g) * w * (h * g)⁻¹ = w * v := by
    calc (h * g) * w * (h * g)⁻¹ = h * (g * w * g⁻¹) * h⁻¹ := by group
      _ = h * (w * v₁) * h⁻¹ := by rw [hgw]
      _ = (h * w * h⁻¹) * (h * v₁ * h⁻¹) := by group
      _ = w * v := by rw [hhw, hh_v₁]
  have hggw : (g * g) * w * (g * g)⁻¹ = w * (v * v₁) := by
    calc (g * g) * w * (g * g)⁻¹ = g * (g * w * g⁻¹) * g⁻¹ := by group
      _ = g * (w * v₁) * g⁻¹ := by rw [hgw]
      _ = w * (v * v₁) := hgwv₁
  have hgV : NormV V g := normV_of_cycle hs hv hv₁ hne hg_v hg_v₁
  have hhV : NormV V h := normV_of_cycle hs hv hv₁ hne hh_v hh_v₁
  have hconj : ∀ x ∈ Wset V w, ∃ n : G, NormV V n ∧ NormV V n⁻¹ ∧ n * w * n⁻¹ = x := by
    intro x hx
    have hxa : w * x ∈ V := hx
    have hxe : x = w * (w * x) := by
      calc x = (w * w) * x := by rw [hw2, one_mul]
        _ = w * (w * x) := by rw [mul_assoc]
    rcases (hVmem _).1 hxa with h1 | h1 | h1 | h1
    · refine ⟨1, NormV.one, by simpa using (NormV.one : NormV V 1), ?_⟩
      rw [hxe, h1]; simp
    · refine ⟨h * g, hhV.mul hgV, (hhV.mul hgV).inv, ?_⟩
      rw [hhg, hxe, h1]
    · refine ⟨g, hgV, hgV.inv, ?_⟩
      rw [hgw, hxe, h1]
    · refine ⟨g * g, hgV.mul hgV, (hgV.mul hgV).inv, ?_⟩
      rw [hggw, hxe, h1]
  have hnotconj : ∀ a ∈ V, ¬ IsConj w a := by
    intro a ha hc
    have hw1 : w ≠ 1 := by
      intro h1
      exact hs.w_notin (h1 ▸ V.one_mem)
    rcases (hVmem a).1 ha with h1 | h1 | h1 | h1
    · rw [h1] at hc
      exact hw1 (isConj_one_left.1 hc)
    · rw [h1] at hc
      exact hnc hc.symm
    · rw [h1] at hc
      apply hnc
      have h₁ : IsConj v₁ v := isConj_iff.2 ⟨h, hh_v₁⟩
      exact (hc.trans h₁).symm
    · rw [h1] at hc
      apply hnc
      have h₁ : IsConj v (v * v₁) := isConj_iff.2 ⟨g, hg_v⟩
      exact (hc.trans h₁.symm).symm
  refine ⟨hconj, hnotconj, ?_⟩
  intro n hn a ha
  have hwW : w ∈ Wset V w := by
    show w * w ∈ V
    rw [hw2]; exact V.one_mem
  have hnw : n * w * n⁻¹ ∈ Wset V w := by
    rcases hn w (Or.inr hwW) with h1 | h1
    · exact absurd (isConj_iff.2 ⟨n, rfl⟩ : IsConj w (n * w * n⁻¹)) (hnotconj _ h1)
    · exact h1
  have hwaW : w * a ∈ Wset V w := by
    show w * (w * a) ∈ V
    rw [← mul_assoc, hw2, one_mul]; exact ha
  have hnwa : n * (w * a) * n⁻¹ ∈ Wset V w := by
    rcases hn (w * a) (Or.inr hwaW) with h1 | h1
    · exfalso
      obtain ⟨m, -, -, hm⟩ := hconj (w * a) hwaW
      have hc1 : IsConj w (w * a) := isConj_iff.2 ⟨m, hm⟩
      have hc2 : IsConj w (n * (w * a) * n⁻¹) :=
        hc1.trans (isConj_iff.2 ⟨n, rfl⟩)
      exact hnotconj _ h1 hc2
    · exact h1
  have e : n * a * n⁻¹ = (n * (w * a) * n⁻¹) * (n * w * n⁻¹) := by
    have hc : a * w = w * a := hs.w_comm a ha
    have ea : a = (w * a) * w := by
      calc a = (w * w) * a := by rw [hw2, one_mul]
        _ = w * (w * a) := by rw [mul_assoc]
        _ = w * (a * w) := by rw [hc]
        _ = (w * a) * w := by rw [mul_assoc]
    conv_lhs => rw [ea]
    group
  rw [e]
  exact Wset_mul_Wset hs hnwa hnw

end Lemma22


section OddCentralizer

variable {G : Type} [Group G]

theorem isPGroup_zpowers_of_involution {a : G} (ha2 : a * a = 1) :
    IsPGroup 2 ↥(Subgroup.zpowers a) := by
  by_cases ha1 : a = 1
  · subst ha1
    exact IsPGroup.of_card (n := 0) (by simp)
  · refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime (by rw [sq]; exact ha2) ha1

theorem isPGroup_closure_of_commuting {a b : G} (ha2 : a * a = 1) (hb2 : b * b = 1)
    (hab : a * b = b * a) : IsPGroup 2 ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) := by
  refine IsPGroup.to_sup_of_normal_right' (isPGroup_zpowers_of_involution ha2)
    (isPGroup_zpowers_of_involution hb2) ?_
  rw [Subgroup.zpowers_le]
  apply Subgroup.centralizer_le_normalizer _
  rw [mem_centralizer_iff]
  intro x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  exact ((show Commute a b from hab).zpow_right k).symm.eq

theorem noCommInv_of_sylow [Finite G] {D Q : Subgroup G} (hQ : IsSylowOf 2 Q D) (hrk : NoCommInv Q) :
    NoCommInv D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro a ha b hb ha2 hb2 hab
  have hA := isPGroup_closure_of_commuting ha2 hb2 hab
  have hAD : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤ D :=
    sup_le ((Subgroup.zpowers_le).2 ha) ((Subgroup.zpowers_le).2 hb)
  obtain ⟨S, hS, hAS⟩ := exists_isSylowOf_ge hAD hA
  obtain ⟨k, -, hk⟩ := hQ.exists_mem_conj hS
  have haS : a ∈ S := hAS (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
  have hbS : b ∈ S := hAS (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))
  have haQ : k⁻¹ * a * k ∈ Q := (hk a).1 haS
  have hbQ : k⁻¹ * b * k ∈ Q := (hk b).1 hbS
  have ha2' : (k⁻¹ * a * k) * (k⁻¹ * a * k) = 1 := by
    calc (k⁻¹ * a * k) * (k⁻¹ * a * k) = k⁻¹ * (a * a) * k := by group
      _ = 1 := by rw [ha2]; group
  have hb2' : (k⁻¹ * b * k) * (k⁻¹ * b * k) = 1 := by
    calc (k⁻¹ * b * k) * (k⁻¹ * b * k) = k⁻¹ * (b * b) * k := by group
      _ = 1 := by rw [hb2]; group
  have hab' : (k⁻¹ * a * k) * (k⁻¹ * b * k) = (k⁻¹ * b * k) * (k⁻¹ * a * k) := by
    calc (k⁻¹ * a * k) * (k⁻¹ * b * k) = k⁻¹ * (a * b) * k := by group
      _ = k⁻¹ * (b * a) * k := by rw [hab]
      _ = (k⁻¹ * b * k) * (k⁻¹ * a * k) := by group
  rcases hrk _ haQ _ hbQ ha2' hb2' hab' with h | h | h
  · left
    have : a = k * (k⁻¹ * a * k) * k⁻¹ := by group
    rw [this, h]; group
  · right; left
    have : b = k * (k⁻¹ * b * k) * k⁻¹ := by group
    rw [this, h]; group
  · right; right
    have : a = k * (k⁻¹ * a * k) * k⁻¹ := by group
    have h' : b = k * (k⁻¹ * b * k) * k⁻¹ := by group
    rw [this, h', h]

end OddCentralizer


section OddCentralizer2

variable {G : Type} [Group G]

theorem card_inf_centralizer_modEq [Finite G] {D : Subgroup G} {a : G} (ha2 : a * a = 1)
    (haD : ∀ d ∈ D, a * d * a⁻¹ ∈ D) :
    Nat.card ↥(D ⊓ centralizer ({a} : Set G)) ≡ Nat.card ↥D [MOD 2] := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype ↥D := Fintype.ofFinite _
  let f : Function.End ↥D := fun d => ⟨a * d * a⁻¹, haD d d.2⟩
  have hf : f ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    funext d
    apply Subtype.ext
    show a * (a * (d : G) * a⁻¹) * a⁻¹ = d
    calc a * (a * (d : G) * a⁻¹) * a⁻¹ = (a * a) * (d : G) * (a * a)⁻¹ := by group
      _ = d := by rw [ha2]; group
  have h := Equiv.Perm.card_fixedPoints_modEq hf
  let e : ↥(D ⊓ centralizer ({a} : Set G)) ≃ ↑f.fixedPoints :=
    { toFun := fun g => ⟨⟨g, g.2.1⟩, Subtype.ext (by
        have h1 := mem_centralizer_singleton_iff.1 g.2.2
        show a * (g : G) * a⁻¹ = g
        rw [← h1]; group)⟩
      invFun := fun d => ⟨d.1, d.1.2, by
        apply mem_centralizer_singleton_iff.2
        have h1 : a * (d.1 : G) * a⁻¹ = d.1 := congrArg Subtype.val d.2
        calc (d.1 : G) * a = (a * (d.1 : G) * a⁻¹) * a := by rw [h1]
          _ = a * (d.1 : G) := by group⟩
      left_inv := fun g => rfl
      right_inv := fun d => rfl }
  have h2 : Nat.card ↥(D ⊓ centralizer ({a} : Set G)) = Fintype.card f.fixedPoints := by
    rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  rw [h2, Nat.card_eq_fintype_card]
  exact h.symm

end OddCentralizer2


section OddCentralizer3

variable {G : Type} [Group G]

theorem odd_card_inf_centralizer [Finite G] {Iw Ivw : Subgroup G} {w v : G}
    (hw2 : w * w = 1) (hv2 : v * v = 1) (hwv : w * v = v * w) (hw1 : w ≠ 1) (hv1 : v ≠ 1)
    (hwne : w ≠ v) (hIw : ∀ i ∈ Iw, i * w = w * i) (hIvw : ∀ i ∈ Ivw, i * (w * v) = (w * v) * i)
    (hvIw : v ∈ Iw) (hvIvw : v ∈ Ivw)
    (hrk : NoCommInv (centralizer ({w} : Set G) ⊓ centralizer (Iw : Set G)))
    (hrk' : NoCommInv (centralizer ({w * v} : Set G) ⊓ centralizer (Ivw : Set G))) :
    Odd (Nat.card ↥(centralizer (Iw : Set G) ⊓ centralizer (Ivw : Set G))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hwIw : ∀ i ∈ Iw, w * i * w⁻¹ = i := by
    intro i hi
    rw [← hIw i hi]; group
  have hwIvw : ∀ i ∈ Ivw, w * i * w⁻¹ = v⁻¹ * i * v := by
    intro i hi
    have hj : v⁻¹ * i * v ∈ Ivw := Ivw.mul_mem (Ivw.mul_mem (Ivw.inv_mem hvIvw) hi) hvIvw
    have h1 := hIvw _ hj
    calc w * i * w⁻¹ = ((w * v) * (v⁻¹ * i * v)) * (w * v)⁻¹ := by group
      _ = (v⁻¹ * i * v * (w * v)) * (w * v)⁻¹ := by rw [← h1]
      _ = v⁻¹ * i * v := by group
  have hN_w_Iw : w ∈ normalizer (Iw : Set G) :=
    mem_normalizer_of_conj (fun i hi => by rw [hwIw i hi]; exact hi)
      (fun i hi => by
        have e : w⁻¹ * i * w = w * i * w⁻¹ := by rw [hwinv]
        rw [e, hwIw i hi]; exact hi)
  have hN_w_Ivw : w ∈ normalizer (Ivw : Set G) :=
    mem_normalizer_of_conj
      (fun i hi => by
        rw [hwIvw i hi]
        exact Ivw.mul_mem (Ivw.mul_mem (Ivw.inv_mem hvIvw) hi) hvIvw)
      (fun i hi => by
        have e : w⁻¹ * i * w = w * i * w⁻¹ := by rw [hwinv]
        rw [e, hwIvw i hi]
        exact Ivw.mul_mem (Ivw.mul_mem (Ivw.inv_mem hvIvw) hi) hvIvw)
  have hN_v_Iw : v ∈ normalizer (Iw : Set G) := by
    rw [mem_normalizer_iff]
    intro i
    constructor
    · intro hi; exact Iw.mul_mem (Iw.mul_mem hvIw hi) (Iw.inv_mem hvIw)
    · intro hi
      have := Iw.mul_mem (Iw.mul_mem (Iw.inv_mem hvIw) hi) hvIw
      have e : v⁻¹ * (v * i * v⁻¹) * v = i := by group
      rwa [e] at this
  have hN_v_Ivw : v ∈ normalizer (Ivw : Set G) := by
    rw [mem_normalizer_iff]
    intro i
    constructor
    · intro hi; exact Ivw.mul_mem (Ivw.mul_mem hvIvw hi) (Ivw.inv_mem hvIvw)
    · intro hi
      have := Ivw.mul_mem (Ivw.mul_mem (Ivw.inv_mem hvIvw) hi) hvIvw
      have e : v⁻¹ * (v * i * v⁻¹) * v = i := by group
      rwa [e] at this
  set D : Subgroup G := centralizer (Iw : Set G) ⊓ centralizer (Ivw : Set G) with hD
  have hwD : ∀ d ∈ D, w * d * w⁻¹ ∈ D := fun d hd =>
    ⟨conj_mem_centralizer_of_mem_normalizer hN_w_Iw hd.1,
      conj_mem_centralizer_of_mem_normalizer hN_w_Ivw hd.2⟩
  have hvD : ∀ d ∈ D, v * d * v⁻¹ ∈ D := fun d hd =>
    ⟨conj_mem_centralizer_of_mem_normalizer hN_v_Iw hd.1,
      conj_mem_centralizer_of_mem_normalizer hN_v_Ivw hd.2⟩
  set D₁ : Subgroup G := D ⊓ centralizer ({w} : Set G) with hD₁
  have hvD₁ : ∀ d ∈ D₁, v * d * v⁻¹ ∈ D₁ := by
    intro d hd
    refine ⟨hvD d hd.1, ?_⟩
    apply mem_centralizer_singleton_iff.2
    have hdw : d * w = w * d := mem_centralizer_singleton_iff.1 hd.2
    have hvw : v * w = w * v := hwv.symm
    calc v * d * v⁻¹ * w = v * d * (v⁻¹ * w) := by rw [mul_assoc]
      _ = v * d * (w * v⁻¹) := by
          congr 1
          calc v⁻¹ * w = v⁻¹ * (w * v) * v⁻¹ := by group
            _ = v⁻¹ * (v * w) * v⁻¹ := by rw [hwv]
            _ = w * v⁻¹ := by group
      _ = v * (d * w) * v⁻¹ := by group
      _ = v * (w * d) * v⁻¹ := by rw [hdw]
      _ = (v * w) * d * v⁻¹ := by group
      _ = (w * v) * d * v⁻¹ := by rw [hvw]
      _ = w * (v * d * v⁻¹) := by group
  set D₂ : Subgroup G := D₁ ⊓ centralizer ({v} : Set G) with hD₂
  have h1 := card_inf_centralizer_modEq hw2 hwD
  have h2 := card_inf_centralizer_modEq hv2 hvD₁
  by_contra hodd
  have hev : 2 ∣ Nat.card ↥D := by
    rcases Nat.even_or_odd (Nat.card ↥D) with h | h
    · exact even_iff_two_dvd.1 h
    · exact absurd h hodd
  have hev2 : 2 ∣ Nat.card ↥D₂ := by
    have e1 : Nat.card ↥D₁ ≡ Nat.card ↥D [MOD 2] := h1
    have e2 : Nat.card ↥D₂ ≡ Nat.card ↥D₁ [MOD 2] := h2
    exact (Nat.modEq_zero_iff_dvd).1 ((e2.trans e1).trans ((Nat.modEq_zero_iff_dvd).2 hev))
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 hev2
  have hu0 : orderOf (u : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hu
  have hu1 : (u : G) ≠ 1 := fun h => by
    rw [h, orderOf_one] at hu0; omega
  have hu2 : (u : G) * (u : G) = 1 := by
    have := pow_orderOf_eq_one (u : G)
    rwa [hu0, pow_two] at this
  have huD₂ : (u : G) ∈ D₂ := u.2
  have huw : (u : G) * w = w * (u : G) := mem_centralizer_singleton_iff.1 huD₂.1.2
  have huv : (u : G) * v = v * (u : G) := mem_centralizer_singleton_iff.1 huD₂.2
  have huIw : (u : G) ∈ centralizer (Iw : Set G) := huD₂.1.1.1
  have huIvw : (u : G) ∈ centralizer (Ivw : Set G) := huD₂.1.1.2
  have huw' : (u : G) = w := by
    have hwm : w ∈ centralizer ({w} : Set G) ⊓ centralizer (Iw : Set G) :=
      ⟨mem_centralizer_singleton_iff.2 rfl, mem_centralizer_iff.2 fun i hi => (hIw i hi)⟩
    have hum : (u : G) ∈ centralizer ({w} : Set G) ⊓ centralizer (Iw : Set G) :=
      ⟨mem_centralizer_singleton_iff.2 huw, huIw⟩
    rcases hrk _ hum _ hwm hu2 hw2 huw with h | h | h
    · exact absurd h hu1
    · exact absurd h hw1
    · exact h
  have hwv2 : (w * v) * (w * v) = 1 := by
    calc (w * v) * (w * v) = w * (v * w) * v := by group
      _ = w * (w * v) * v := by rw [← hwv]
      _ = (w * w) * (v * v) := by group
      _ = 1 := by rw [hw2, hv2, one_mul]
  have hwv1 : w * v ≠ 1 := by
    intro h
    apply hwne
    have : w = v⁻¹ := mul_eq_one_iff_eq_inv.1 h
    rw [this, hvinv]
  have huwv' : (u : G) = w * v := by
    have hwm : w * v ∈ centralizer ({w * v} : Set G) ⊓ centralizer (Ivw : Set G) :=
      ⟨mem_centralizer_singleton_iff.2 rfl, mem_centralizer_iff.2 fun i hi => (hIvw i hi)⟩
    have hum : (u : G) ∈ centralizer ({w * v} : Set G) ⊓ centralizer (Ivw : Set G) := by
      refine ⟨mem_centralizer_singleton_iff.2 ?_, huIvw⟩
      calc (u : G) * (w * v) = (u * w) * v := by rw [mul_assoc]
        _ = (w * u) * v := by rw [huw]
        _ = w * (u * v) := by rw [mul_assoc]
        _ = w * (v * u) := by rw [huv]
        _ = (w * v) * u := by rw [mul_assoc]
    have hcomm : (u : G) * (w * v) = (w * v) * u := mem_centralizer_singleton_iff.1 hum.1
    rcases hrk' _ hum _ hwm hu2 hwv2 hcomm with h | h | h
    · exact absurd h hu1
    · exact absurd h hwv1
    · exact h
  apply hv1
  have : w = w * v := huw'.symm.trans huwv'
  calc v = w⁻¹ * (w * v) := by group
    _ = w⁻¹ * w := by rw [← this]
    _ = 1 := by group

end OddCentralizer3

section FourGroup

variable {G : Type} [Group G]

theorem ncard_fourSet {v v₁ : G} (hv1 : v ≠ 1) (hv₁1 : v₁ ≠ 1) (hne : v ≠ v₁) (hvv₁ : v * v₁ ≠ 1) :
    ({1, v, v₁, v * v₁} : Set G).ncard = 4 := by
  have e1 : (1 : G) ≠ v := hv1.symm
  have e2 : (1 : G) ≠ v₁ := hv₁1.symm
  have e3 : (1 : G) ≠ v * v₁ := hvv₁.symm
  have e5 : v ≠ v * v₁ := fun h => hv₁1 (by
    calc v₁ = v⁻¹ * (v * v₁) := by group
      _ = v⁻¹ * v := by rw [← h]
      _ = 1 := by group)
  have e6 : v₁ ≠ v * v₁ := fun h => hv1 (by
    calc v = (v * v₁) * v₁⁻¹ := by group
      _ = v₁ * v₁⁻¹ := by rw [← h]
      _ = 1 := by group)
  rw [Set.ncard_insert_of_notMem (by simp [e1, e2, e3]),
    Set.ncard_insert_of_notMem (by simp [hne, e5]), Set.ncard_pair e6]

theorem exists_count23Setup {v v₁ w : G} (hv2 : v * v = 1) (hv₁2 : v₁ * v₁ = 1)
    (hvv₁ : v * v₁ = v₁ * v) (hv1 : v ≠ 1) (hv₁1 : v₁ ≠ 1) (hne : v ≠ v₁) (hw2 : w * w = 1)
    (hvw : v * w = w * v) (hv₁w : v₁ * w = w * v₁)
    (hw : w ≠ 1 ∧ w ≠ v ∧ w ≠ v₁ ∧ w ≠ v * v₁) :
    ∃ V : Subgroup G, Count23Setup V w ∧ v ∈ Vsharp V ∧ v₁ ∈ Vsharp V ∧
      ∀ a, a ∈ V ↔ (a = 1 ∨ a = v ∨ a = v₁ ∨ a = v * v₁) := by
  have hvv₁1 : v * v₁ ≠ 1 := by
    intro h
    apply hne
    calc v = v * (v₁ * v₁) := by rw [hv₁2, mul_one]
      _ = (v * v₁) * v₁ := by rw [mul_assoc]
      _ = v₁ := by rw [h, one_mul]
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hv₁inv : v₁⁻¹ = v₁ := inv_eq_of_mul_eq_one_right hv₁2
  have f1 : v * (v * v₁) = v₁ := by
    calc v * (v * v₁) = (v * v) * v₁ := by rw [mul_assoc]
      _ = v₁ := by rw [hv2, one_mul]
  have f2 : v₁ * (v * v₁) = v := by
    calc v₁ * (v * v₁) = (v₁ * v) * v₁ := by rw [mul_assoc]
      _ = (v * v₁) * v₁ := by rw [← hvv₁]
      _ = v * (v₁ * v₁) := by rw [mul_assoc]
      _ = v := by rw [hv₁2, mul_one]
  have f3 : (v * v₁) * v = v₁ := by
    calc (v * v₁) * v = v * (v₁ * v) := by rw [mul_assoc]
      _ = v * (v * v₁) := by rw [hvv₁]
      _ = v₁ := f1
  have f4 : (v * v₁) * v₁ = v := by
    calc (v * v₁) * v₁ = v * (v₁ * v₁) := by rw [mul_assoc]
      _ = v := by rw [hv₁2, mul_one]
  have f5 : (v * v₁) * (v * v₁) = 1 := by
    calc (v * v₁) * (v * v₁) = ((v * v₁) * v) * v₁ := (mul_assoc _ _ _).symm
      _ = v₁ * v₁ := by rw [f3]
      _ = 1 := hv₁2
  let V : Subgroup G :=
    { carrier := {a | a = 1 ∨ a = v ∨ a = v₁ ∨ a = v * v₁}
      mul_mem' := by
        intro a b ha hb
        rcases ha with ha | ha | ha | ha <;> rcases hb with hb | hb | hb | hb <;> rw [ha, hb] <;>
          simp [hv2, hv₁2, f1, f2, f3, f4, f5, hvv₁.symm]
      one_mem' := Or.inl rfl
      inv_mem' := by
        intro a ha
        rcases ha with ha | ha | ha | ha
        · left; rw [ha]; simp
        · right; left; rw [ha, hvinv]
        · right; right; left; rw [ha, hv₁inv]
        · right; right; right
          rw [ha, mul_inv_rev, hvinv, hv₁inv, hvv₁.symm] }
  have hmem : ∀ a, a ∈ V ↔ (a = 1 ∨ a = v ∨ a = v₁ ∨ a = v * v₁) := fun a => Iff.rfl
  have hvV : v ∈ V := (hmem v).2 (Or.inr (Or.inl rfl))
  have hv₁V : v₁ ∈ V := (hmem v₁).2 (Or.inr (Or.inr (Or.inl rfl)))
  refine ⟨V, ⟨?_, ?_, ?_, hw2, ?_, ?_⟩, ⟨hvV, hv1⟩, ⟨hv₁V, hv₁1⟩, hmem⟩
  · have hcard : (V : Set G).ncard = 4 := by
      have : (V : Set G) = ({1, v, v₁, v * v₁} : Set G) := by
        ext a
        simp [hmem]
      rw [this]
      exact ncard_fourSet hv1 hv₁1 hne hvv₁1
    have h : Nat.card ↥V = (V : Set G).ncard := Nat.card_coe_set_eq (V : Set G)
    rw [h, hcard]
  · intro a ha b hb
    rcases (hmem a).1 ha with h | h | h | h <;> rcases (hmem b).1 hb with h' | h' | h' | h' <;>
      rw [h, h'] <;> simp [f1, f2, f3, f4, hvv₁.symm]
  · intro a ha
    rcases (hmem a).1 ha with h | h | h | h <;> rw [h] <;> simp [hv2, hv₁2, f5]
  · intro a ha
    rcases (hmem a).1 ha with h | h | h | h
    · rw [h]; simp
    · rw [h]; exact hvw
    · rw [h]; exact hv₁w
    · rw [h]
      calc v * v₁ * w = v * (v₁ * w) := by rw [mul_assoc]
        _ = v * (w * v₁) := by rw [hv₁w]
        _ = (v * w) * v₁ := by rw [mul_assoc]
        _ = (w * v) * v₁ := by rw [hvw]
        _ = w * (v * v₁) := by rw [mul_assoc]
  · intro hwV
    rcases (hmem w).1 hwV with h | h | h | h
    · exact hw.1 h
    · exact hw.2.1 h
    · exact hw.2.2.1 h
    · exact hw.2.2.2 h

end FourGroup

section CyclicRank

variable {G : Type} [Group G]

theorem noCommInv_of_cyclic [Finite G] {Q : Subgroup G} (hQ : IsCyclic ↥Q) : NoCommInv Q := by
  intro a ha b hb ha2 hb2 _
  by_cases ha1 : a = 1
  · exact Or.inl ha1
  by_cases hb1 : b = 1
  · exact Or.inr (Or.inl hb1)
  exact Or.inr (Or.inr (eq_of_involutions_of_cyclic hQ ha hb ha1 hb1 ha2 hb2))

end CyclicRank

end CFSG.GH74.Generic.S3
