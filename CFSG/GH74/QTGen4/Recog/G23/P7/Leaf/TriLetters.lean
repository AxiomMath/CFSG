module

public import CFSG.GH74.QTGen4.Recog.G23.P7.LeafWrappers
public import CFSG.GH74.QTGen4.Recog.G23.P7.TriData
public import CFSG.GH74.QTGen4.Recog.G23.P7.Assembly

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable

namespace TriLettersAux

section Words

variable {X : Type*} [Group X]

theorem satWords_append {m : ℕ} {A B : List (List (Fin m × Bool))} {ρ : Fin m → X}
    (hA : SatWords A ρ) (hB : SatWords B ρ) : SatWords (A ++ B) ρ := by
  intro r hr
  rcases List.mem_append.mp hr with h | h
  · exact hA r h
  · exact hB r h

theorem satWords_relK_of (x : Fin 6 → X) (h0 : x 0 ^ 3 = 1) (h1 : x 1 ^ 3 = 1)
    (h2 : (x 1)⁻¹ * (x 0)⁻¹ * x 1 * (x 0)⁻¹ * (x 1)⁻¹ * x 0 = 1) (h3 : x 2 ^ 3 = 1)
    (h4 : x 3 ^ 3 = 1) (h5 : (x 3)⁻¹ * (x 2)⁻¹ * x 3 * (x 2)⁻¹ * (x 3)⁻¹ * x 2 = 1)
    (h6 : x 0 * x 1 * x 0 * x 1 * (x 3)⁻¹ * (x 2)⁻¹ * (x 3)⁻¹ * (x 2)⁻¹ = 1)
    (h7 : (x 0)⁻¹ * (x 2)⁻¹ * x 0 * x 2 = 1) (h8 : (x 0)⁻¹ * (x 3)⁻¹ * x 0 * x 3 = 1)
    (h9 : (x 1)⁻¹ * (x 2)⁻¹ * x 1 * x 2 = 1) (h10 : (x 1)⁻¹ * (x 3)⁻¹ * x 1 * x 3 = 1) :
    SatWords relK x := by
  intro r hr
  simp only [relK, g23WordsH, List.take, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [FreeGroup.lift_mk, pow_three', mul_assoc] using h0
  · simpa [FreeGroup.lift_mk, pow_three', mul_assoc] using h1
  · simpa [FreeGroup.lift_mk, mul_assoc] using h2
  · simpa [FreeGroup.lift_mk, pow_three', mul_assoc] using h3
  · simpa [FreeGroup.lift_mk, pow_three', mul_assoc] using h4
  · simpa [FreeGroup.lift_mk, mul_assoc] using h5
  · simpa [FreeGroup.lift_mk, mul_assoc] using h6
  · simpa [FreeGroup.lift_mk, mul_assoc] using h7
  · simpa [FreeGroup.lift_mk, mul_assoc] using h8
  · simpa [FreeGroup.lift_mk, mul_assoc] using h9
  · simpa [FreeGroup.lift_mk, mul_assoc] using h10

theorem satWords_relK_vec (a b c d p q : X) (h0 : a ^ 3 = 1) (h1 : b ^ 3 = 1)
    (h2 : b⁻¹ * a⁻¹ * b * a⁻¹ * b⁻¹ * a = 1) (h3 : c ^ 3 = 1) (h4 : d ^ 3 = 1)
    (h5 : d⁻¹ * c⁻¹ * d * c⁻¹ * d⁻¹ * c = 1)
    (h6 : a * b * a * b * d⁻¹ * c⁻¹ * d⁻¹ * c⁻¹ = 1)
    (h7 : a⁻¹ * c⁻¹ * a * c = 1) (h8 : a⁻¹ * d⁻¹ * a * d = 1)
    (h9 : b⁻¹ * c⁻¹ * b * c = 1) (h10 : b⁻¹ * d⁻¹ * b * d = 1) :
    SatWords relK ![a, b, c, d, p, q] :=
  satWords_relK_of _ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10

theorem satWords_vertexPart {ρ : Fin 6 → X} {k₁ k₂ : Fin 6}
    (h₁ : SatWords (vertexRels1 k₁) (ρ ∘ v1Map)) (h₂ : SatWords (vertexRels2 k₂) (ρ ∘ v2Map)) :
    SatWords (vertexPart k₁ k₂) ρ := by
  unfold vertexPart
  refine satWords_append ?_ ?_
  · intro r hr
    obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
    rw [lift_mk_mapWord]
    exact h₁ r' hr'
  · intro r hr
    obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
    rw [lift_mk_mapWord]
    exact h₂ r' hr'

theorem satWords_vertexPart_zero_of_model {p : Fin 6 × Fin 6} (hp : p ∈ modelPairs) {ρ : Fin 6 → X}
    (h : SatWords (vertexPart p.1 p.2) ρ) :
    SatWords (vertexPart 0 0) (flipLetters (modelFlip p) ρ) := by
  intro r hr
  have hmem : flipWord (modelFlip p) r ∈ vertexPart p.1 p.2 := by
    rw [vertexPart_model p hp]
    exact List.mem_map_of_mem hr
  have h' := h _ hmem
  rwa [lift_mk_flipWord] at h'

theorem relator_inv_of_inv {t x y : X} (ht : t * t = 1) (hx : t * x * t = x⁻¹)
    (hy : t * y * t = y⁻¹) (h : y⁻¹ * x⁻¹ * y * x⁻¹ * y⁻¹ * x = 1) :
    y * x * y⁻¹ * x * y * x⁻¹ = 1 := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hx' : t * x * t⁻¹ = x⁻¹ := by rw [hti]; exact hx
  have hy' : t * y * t⁻¹ = y⁻¹ := by rw [hti]; exact hy
  have h1 := congrArg (MulAut.conj t) h
  simp only [map_mul, map_inv, map_one, MulAut.conj_apply, hx', hy', inv_inv] at h1
  exact h1

theorem commute_of_rel {x y : X} (h : x⁻¹ * y⁻¹ * x * y = 1) : Commute x y := by
  have h' : (y * x)⁻¹ * (x * y) = 1 := by
    calc (y * x)⁻¹ * (x * y) = x⁻¹ * y⁻¹ * x * y := by group
      _ = 1 := h
  exact (inv_mul_eq_one.mp h').symm

theorem inv_mul_mul_inv_of_comm {x y : X} (h : x * y = y * x) : x⁻¹ * y * x * y⁻¹ = 1 := by
  calc x⁻¹ * y * x * y⁻¹ = x⁻¹ * (y * x) * y⁻¹ := by group
    _ = x⁻¹ * (x * y) * y⁻¹ := by rw [h]
    _ = 1 := by group

theorem mul_inv_mul_inv_of_comm {x y : X} (h : x * y = y * x) : x * y⁻¹ * x⁻¹ * y = 1 := by
  calc x * y⁻¹ * x⁻¹ * y = x * (y⁻¹ * x⁻¹) * y := by group
    _ = x * (x * y)⁻¹ * y := by group
    _ = x * (y * x)⁻¹ * y := by rw [h]
    _ = 1 := by group

end Words

section Groups

variable {G : Type} [Group G]

theorem relators_of_letters {e : Fin 6 → G} (R : SatisfiesWords g23WordsH e) :
    e 0 ^ 3 = 1 ∧ e 1 ^ 3 = 1 ∧ (e 1)⁻¹ * (e 0)⁻¹ * e 1 * (e 0)⁻¹ * (e 1)⁻¹ * e 0 = 1 ∧
    e 2 ^ 3 = 1 ∧ e 3 ^ 3 = 1 ∧ (e 3)⁻¹ * (e 2)⁻¹ * e 3 * (e 2)⁻¹ * (e 3)⁻¹ * e 2 = 1 ∧
    e 0 * e 1 * e 0 * e 1 * (e 3)⁻¹ * (e 2)⁻¹ * (e 3)⁻¹ * (e 2)⁻¹ = 1 ∧
    (e 0)⁻¹ * (e 2)⁻¹ * e 0 * e 2 = 1 ∧ (e 0)⁻¹ * (e 3)⁻¹ * e 0 * e 3 = 1 ∧
    (e 1)⁻¹ * (e 2)⁻¹ * e 1 * e 2 = 1 ∧ (e 1)⁻¹ * (e 3)⁻¹ * e 1 * e 3 = 1 ∧
    e 4 * e 4 = 1 ∧ e 4 * e 0 * e 4 * e 0 = 1 ∧ e 4 * e 1 * e 4 * e 1 = 1 ∧
    e 4 * e 2 * e 4 * e 2 = 1 ∧ e 4 * e 3 * e 4 * e 3 = 1 := by
  have key : ∀ r ∈ g23WordsH, FreeGroup.lift e (FreeGroup.mk r) = 1 := R
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := key [(0, true), (0, true), (0, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, pow_three', mul_assoc] using this
  · have := key [(1, true), (1, true), (1, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, pow_three', mul_assoc] using this
  · have := key [(1, false), (0, false), (1, true), (0, false), (1, false), (0, true)]
      (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using this
  · have := key [(2, true), (2, true), (2, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, pow_three', mul_assoc] using this
  · have := key [(3, true), (3, true), (3, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, pow_three', mul_assoc] using this
  · have := key [(3, false), (2, false), (3, true), (2, false), (3, false), (2, true)]
      (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using this
  · have := key [(0, true), (1, true), (0, true), (1, true), (3, false), (2, false),
      (3, false), (2, false)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using this
  · have := key [(0, false), (2, false), (0, true), (2, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using this
  · have := key [(0, false), (3, false), (0, true), (3, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using this
  · have := key [(1, false), (2, false), (1, true), (2, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using this
  · have := key [(1, false), (3, false), (1, true), (3, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using this
  · have := key [(4, true), (4, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using this
  · have := key [(4, true), (0, true), (4, true), (0, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using this
  · have := key [(4, true), (1, true), (4, true), (1, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using this
  · have := key [(4, true), (2, true), (4, true), (2, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using this
  · have := key [(4, true), (3, true), (4, true), (3, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using this

theorem mem_closure_of_sign {S : Set G} {x y : G} (h : y = x ∨ y = x⁻¹)
    (hx : x ∈ Subgroup.closure S) : y ∈ Subgroup.closure S := by
  rcases h with rfl | rfl
  · exact hx
  · exact Subgroup.inv_mem _ hx

theorem sign_rev {a a' : G} (h : a' = a ∨ a' = a⁻¹) : a = a' ∨ a = a'⁻¹ := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (inv_inv _).symm

theorem closure_four_congr {a b c d a' b' c' d' : G}
    (ha : a' = a ∨ a' = a⁻¹) (hb : b' = b ∨ b' = b⁻¹) (hc : c' = c ∨ c' = c⁻¹)
    (hd : d' = d ∨ d' = d⁻¹) :
    Subgroup.closure ({a', b', c', d'} : Set G) = Subgroup.closure ({a, b, c, d} : Set G) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact mem_closure_of_sign ha (Subgroup.subset_closure (by simp))
    · exact mem_closure_of_sign hb (Subgroup.subset_closure (by simp))
    · exact mem_closure_of_sign hc (Subgroup.subset_closure (by simp))
    · exact mem_closure_of_sign hd (Subgroup.subset_closure (by simp))
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact mem_closure_of_sign (sign_rev ha) (Subgroup.subset_closure (by simp))
    · exact mem_closure_of_sign (sign_rev hb) (Subgroup.subset_closure (by simp))
    · exact mem_closure_of_sign (sign_rev hc) (Subgroup.subset_closure (by simp))
    · exact mem_closure_of_sign (sign_rev hd) (Subgroup.subset_closure (by simp))

theorem closure_four_eq_sup {H H₁ H₂ : Subgroup G} {e : Fin 6 → G} (hlet : HLetters H H₁ H₂ e) :
    Subgroup.closure ({e 0, e 1, e 2, e 3} : Set G) = H₁ ⊔ H₂ := by
  rw [← hlet.gen₁, ← hlet.gen₂, ← Subgroup.closure_union]
  congr 1
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
  tauto

theorem closure_four_eq_sup_of_sign {H H₁ H₂ : Subgroup G} {e : Fin 6 → G}
    (hlet : HLetters H H₁ H₂ e) {x : Fin 6 → G} (h0 : x 0 = e 0 ∨ x 0 = (e 0)⁻¹)
    (h1 : x 1 = e 1 ∨ x 1 = (e 1)⁻¹) (h2 : x 2 = e 2 ∨ x 2 = (e 2)⁻¹)
    (h3 : x 3 = e 3 ∨ x 3 = (e 3)⁻¹) :
    Subgroup.closure ({x 0, x 1, x 2, x 3} : Set G) = H₁ ⊔ H₂ :=
  (closure_four_congr h0 h1 h2 h3).trans (closure_four_eq_sup hlet)

theorem eq_one_of_mem_of_card_eq_three [Finite G] {A B : Subgroup G} (hA : Nat.card A = 3)
    (hB : Nat.card B = 3) (hAB : A ≠ B) {x : G} (hxA : x ∈ A) (hxB : x ∈ B) : x = 1 := by
  by_contra hx
  have hd : orderOf x ∣ 3 := by
    have h := orderOf_dvd_natCard (⟨x, hxA⟩ : A)
    rw [Subgroup.orderOf_mk, hA] at h
    exact h
  have h3 : orderOf x = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx
    · exact h
  have hzA : Subgroup.zpowers x = A :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxA)
      (le_of_eq (by rw [Nat.card_zpowers, h3, hA]))
  have hzB : Subgroup.zpowers x = B :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxB)
      (le_of_eq (by rw [Nat.card_zpowers, h3, hB]))
  exact hAB (hzA.symm.trans hzB)

theorem exists_ne_one_of_card_eq_three [Finite G] {A : Subgroup G} (hA : Nat.card A = 3) :
    ∃ x ∈ A, x ≠ 1 := by
  haveI : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by rw [hA]; norm_num)
  obtain ⟨x, hx⟩ := exists_ne (1 : A)
  exact ⟨x, x.2, fun h => hx (Subtype.ext h)⟩

theorem card_mul_le_card_sup [Finite G] {A B : Subgroup G} (h : A ⊓ B = ⊥) :
    Nat.card A * Nat.card B ≤ Nat.card ↥(A ⊔ B) := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun p : ↥A × ↥B => (⟨(p.1 : G) * (p.2 : G), mul_mem (Subgroup.mem_sup_left p.1.2)
      (Subgroup.mem_sup_right p.2.2)⟩ : ↥(A ⊔ B))) ?_
  rintro ⟨a, b⟩ ⟨a', b'⟩ hab
  have h1 : (a : G) * (b : G) = (a' : G) * (b' : G) := congrArg Subtype.val hab
  have h2 : (a' : G)⁻¹ * (a : G) = (b' : G) * (b : G)⁻¹ := by
    calc (a' : G)⁻¹ * (a : G) = (a' : G)⁻¹ * ((a : G) * (b : G)) * (b : G)⁻¹ := by group
      _ = (a' : G)⁻¹ * ((a' : G) * (b' : G)) * (b : G)⁻¹ := by rw [h1]
      _ = (b' : G) * (b : G)⁻¹ := by group
  have hmem : (a' : G)⁻¹ * (a : G) ∈ A ⊓ B := by
    refine ⟨A.mul_mem (A.inv_mem a'.2) a.2, ?_⟩
    rw [h2]
    exact B.mul_mem b'.2 (B.inv_mem b.2)
  rw [h, Subgroup.mem_bot] at hmem
  have hb : (b' : G) * (b : G)⁻¹ = 1 := h2.symm.trans hmem
  have ha : (a : G) = (a' : G) := (inv_mul_eq_one.mp hmem).symm
  have hb' : (b : G) = (b' : G) := (mul_inv_eq_one.mp hb).symm
  exact Prod.ext (Subtype.ext ha) (Subtype.ext hb')

theorem orderOf_eq_three_of_ne_one {x : G} (h3 : x ^ 3 = 1) (hx : x ≠ 1) : orderOf x = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime h3 hx

theorem ne_one_of_card_pair [Finite G] {x y : G} (hy : y ^ 3 = 1)
    (h : Nat.card (Subgroup.closure ({x, y} : Set G)) = 9) : x ≠ 1 := by
  intro hx
  subst hx
  have hle : Subgroup.closure ({1, y} : Set G) ≤ Subgroup.zpowers y := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  have h3 : orderOf y ≤ 3 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_iff_pow_eq_one.mpr hy)
  have hc := Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers, h] at hc
  omega

end Groups

end TriLettersAux

open TriLettersAux

theorem leafTriLetters [G23Leaf LeafVertexLetters] [G23Leaf LeafTriClassify]
    : LeafTriLetters := by
  intro G _ _ T H H₁ H₂ M e M₁ M₂ Pb Np Nm W h hF hO hL h5
  have hone : G23One H H₁ H₂ := h.ctx.one
  have hlet : HLetters H H₁ H₂ e := h.lets
  have hv₁ := hL.v₁
  have hv₂ := hL.v₂
  have hms := h5.mstruct
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩ :=
    relators_of_letters hlet.rels
  have cm02 : Commute (e 0) (e 2) := commute_of_rel r7
  have cm03 : Commute (e 0) (e 3) := commute_of_rel r8
  have cm12 : Commute (e 1) (e 2) := commute_of_rel r9
  have cm13 : Commute (e 1) (e 3) := commute_of_rel r10
  have hzcd : zOf e = (e 2 * e 3) ^ 2 := by
    have h' : (e 0 * e 1) ^ 2 * ((e 2 * e 3) ^ 2)⁻¹ = 1 := by
      calc (e 0 * e 1) ^ 2 * ((e 2 * e 3) ^ 2)⁻¹
          = e 0 * e 1 * e 0 * e 1 * (e 3)⁻¹ * (e 2)⁻¹ * (e 3)⁻¹ * (e 2)⁻¹ := by
            simp only [sq, mul_inv_rev]; group
        _ = 1 := r6
    exact mul_inv_eq_one.mp h'
  have hz1 : Commute (e 1) (zOf e) := by
    rw [hzcd]
    exact (cm12.mul_right cm13).pow_right 2
  have hz3 : Commute (e 3) (zOf e) := by
    show Commute (e 3) ((e 0 * e 1) ^ 2)
    exact (cm03.symm.mul_right cm13.symm).pow_right 2
  have hz_ba : (e 1 * e 0) ^ 2 = zOf e := by
    have h1 : (e 1 * e 0) ^ 2 = e 1 * zOf e * (e 1)⁻¹ := by
      show (e 1 * e 0) ^ 2 = e 1 * (e 0 * e 1) ^ 2 * (e 1)⁻¹
      simp only [sq]
      group
    rw [h1, hz1.eq]
    group
  have hz_dc : (e 3 * e 2) ^ 2 = zOf e := by
    have h1 : (e 3 * e 2) ^ 2 = e 3 * (e 2 * e 3) ^ 2 * (e 3)⁻¹ := by
      simp only [sq]; group
    rw [h1, ← hzcd, hz3.eq]
    group
  have hzH₁ : zOf e ∈ H₁ := by
    rw [← hlet.gen₁]
    exact pow_mem (mul_mem (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))) 2
  have hzH₂ : zOf e ∈ H₂ := by
    rw [hzcd, ← hlet.gen₂]
    exact pow_mem (mul_mem (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))) 2
  have hz_sq : zOf e ^ 2 = 1 := by
    have hdvd := orderOf_dvd_natCard (⟨zOf e, hzH₁, hzH₂⟩ : ↥(H₁ ⊓ H₂))
    rw [hone.card_inf] at hdvd
    have h2 : (⟨zOf e, hzH₁, hzH₂⟩ : ↥(H₁ ⊓ H₂)) ^ 2 = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp hdvd
    simpa using congrArg Subtype.val h2
  have he0 : e 0 ≠ 1 := ne_one_of_card_pair r3 hF.card_P
  have he2 : e 2 ≠ 1 := ne_one_of_card_pair r0 (by rw [Set.pair_comm]; exact hF.card_P)
  have hs0 : orderOf (e 0) = 3 := orderOf_eq_three_of_ne_one r0 he0
  have hs2 : orderOf (e 2) = 3 := orderOf_eq_three_of_ne_one r3 he2
  have he2H₂ : e 2 ∈ H₂ := by
    rw [← hlet.gen₂]; exact Subgroup.subset_closure (by simp)
  have he3H₂ : e 3 ∈ H₂ := by
    rw [← hlet.gen₂]; exact Subgroup.subset_closure (by simp)
  have he0H₁ : e 0 ∈ H₁ := by
    rw [← hlet.gen₁]; exact Subgroup.subset_closure (by simp)
  have he1H₁ : e 1 ∈ H₁ := by
    rw [← hlet.gen₁]; exact Subgroup.subset_closure (by simp)
  have he0M₁ : e 0 ∈ M₁ := by
    have h' : e 0 ∈ M₁ ⊓ H := by
      rw [hv₁.inf_H]; exact Subgroup.mem_zpowers _
    exact h'.1
  have he2M₂ : e 2 ∈ M₂ := by
    have h' : e 2 ∈ M₂ ⊓ H := by
      rw [hv₂.inf_H]; exact Subgroup.mem_zpowers _
    exact h'.1
  have hH₂C : H₂ ≤ Subgroup.centralizer {e 0} := hv₁.compl.right_le
  have hH₁C : H₁ ≤ Subgroup.centralizer {e 2} := hv₂.compl.right_le
  obtain ⟨w₁, hw₁L, hw₁ne⟩ := exists_ne_one_of_card_eq_three h5.card_ℓ₁
  obtain ⟨w₂, hw₂L, hw₂ne⟩ := exists_ne_one_of_card_eq_three h5.card_ℓ₂
  have hw₁W : w₁ ∈ W := hw₁L.1
  have hw₂W : w₂ ∈ W := hw₂L.1
  have hw₂notM₁ : w₂ ∉ M₁ ⊓ Subgroup.centralizer (M₁ : Set G) := fun hmem =>
    hw₂ne (eq_one_of_mem_of_card_eq_three h5.card_ℓ₁ h5.card_ℓ₂ h5.ℓ_ne ⟨hw₂W, hmem⟩ hw₂L)
  have hw₁notM₂ : w₁ ∉ M₂ ⊓ Subgroup.centralizer (M₂ : Set G) := fun hmem =>
    hw₁ne (eq_one_of_mem_of_card_eq_three h5.card_ℓ₁ h5.card_ℓ₂ h5.ℓ_ne hw₁L ⟨hw₁W, hmem⟩)
  have hvh₁ : VertexHyp (e 0) (e 2) (e 3) (zOf e) M₁ W w₁ w₂ :=
    { a3 := r3
      b3 := r4
      rel := r5
      z_def := hzcd
      card_L := by rw [hlet.gen₂]; exact card_H₂_of_G23One hone
      M_norm := fun m hm => ⟨hv₁.compl.conj_mem _ (hH₂C he2H₂) m hm,
        hv₁.compl.conj_mem _ (hH₂C he3H₂) m hm⟩
      M_L := by rw [hlet.gen₂]; exact hv₁.compl.disjoint
      sigma_mem := he0M₁
      sigma_ord := hs0
      sigma_cent := fun g hg => by
        rw [hlet.gen₂] at hg
        exact Subgroup.mem_centralizer_singleton_iff.mp
          (sup_le hv₁.compl.left_le hv₁.compl.right_le hg)
      card_M := hms.card₁
      exp3 := hms.exp₁
      comm_le := hms.comm₁
      nonab := hms.nonab₁
      card_Z := hms.card_Z₁
      z_inv := hms.zinv₁
      W_le := h5.W_le₁
      card_W := h5.card_W
      W_inv := h5.W_inv
      w₁_mem := hw₁L
      w₁_ne := hw₁ne
      w₂_mem := hw₂W
      w₂_not := hw₂notM₁ }
  have hvh₂ : VertexHyp (e 2) (e 0) (e 1) (zOf e) M₂ W w₂ w₁ :=
    { a3 := r0
      b3 := r1
      rel := r2
      z_def := rfl
      card_L := by rw [hlet.gen₁]; exact card_H₁_of_G23One hone
      M_norm := fun m hm => ⟨hv₂.compl.conj_mem _ (hH₁C he0H₁) m hm,
        hv₂.compl.conj_mem _ (hH₁C he1H₁) m hm⟩
      M_L := by rw [hlet.gen₁]; exact hv₂.compl.disjoint
      sigma_mem := he2M₂
      sigma_ord := hs2
      sigma_cent := fun g hg => by
        rw [hlet.gen₁] at hg
        exact Subgroup.mem_centralizer_singleton_iff.mp
          (sup_le hv₂.compl.left_le hv₂.compl.right_le hg)
      card_M := hms.card₂
      exp3 := hms.exp₂
      comm_le := hms.comm₂
      nonab := hms.nonab₂
      card_Z := hms.card_Z₂
      z_inv := hms.zinv₂
      W_le := h5.W_le₂
      card_W := h5.card_W
      W_inv := h5.W_inv
      w₁_mem := hw₂L
      w₁_ne := hw₂ne
      w₂_mem := hw₁W
      w₂_not := hw₁notM₂ }
  obtain ⟨k₁, hA₁, -, hC₁⟩ := exists_vertexLetters hvh₁
  obtain ⟨k₂, -, hB₂, -⟩ := exists_vertexLetters hvh₂
  set f : Fin 6 → G := ![e 0, e 1, e 2, e 3, w₁, w₂] with hf
  have hc1 : f ∘ v1Map = ![e 0, e 2, e 3, w₁, w₂] := by
    funext i; fin_cases i <;> rfl
  have hc2 : f ∘ v2Map = ![e 2, e 0, e 1, w₂, w₁] := by
    funext i; fin_cases i <;> rfl
  have hvp : SatWords (vertexPart k₁ k₂) f :=
    satWords_vertexPart (by rw [hc1]; exact hA₁) (by rw [hc2]; exact hB₂)
  have hK : SatWords relK f :=
    satWords_relK_vec (e 0) (e 1) (e 2) (e 3) w₁ w₂ r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
  rcases modelPair_or_collapse k₁ k₂ with hm | hcol
  · have hsat0 := satWords_vertexPart_zero_of_model hm hvp
    simp only [modelPairs, List.mem_cons, List.mem_singleton, Prod.mk.injEq,
      List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    ·
      exact ⟨f, satWords_append hK hvp,
        closure_four_eq_sup_of_sign hlet (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)⟩
    ·
      have hx : flipLetters (modelFlip (1, 1)) f = ![e 0, e 1, e 2, e 3, w₁, w₂⁻¹] := by
        funext i; fin_cases i <;> first | rfl | simp [flipLetters, modelFlip, hf]
      rw [hx] at hsat0
      refine ⟨![e 0, e 1, e 2, e 3, w₁, w₂⁻¹], ?_, ?_⟩
      · exact satWords_append
          (satWords_relK_vec (e 0) (e 1) (e 2) (e 3) w₁ w₂⁻¹ r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10)
          hsat0
      · exact closure_four_eq_sup_of_sign hlet (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
          (Or.inl rfl)
    ·
      have hx : flipLetters (modelFlip (2, 3)) f = ![e 0, e 1, (e 2)⁻¹, (e 3)⁻¹, w₁, w₂] := by
        funext i; fin_cases i <;> first | rfl | simp [flipLetters, modelFlip, hf]
      rw [hx] at hsat0
      have h3' : ((e 2)⁻¹) ^ 3 = 1 := by rw [inv_pow, r3, inv_one]
      have h4' : ((e 3)⁻¹) ^ 3 = 1 := by rw [inv_pow, r4, inv_one]
      have hR5 : e 3 * e 2 * (e 3)⁻¹ * e 2 * e 3 * (e 2)⁻¹ = 1 :=
        relator_inv_of_inv r11 (eq_inv_of_mul_eq_one_left r14)
          (eq_inv_of_mul_eq_one_left r15) r5
      have h5' : ((e 3)⁻¹)⁻¹ * ((e 2)⁻¹)⁻¹ * (e 3)⁻¹ * ((e 2)⁻¹)⁻¹ * ((e 3)⁻¹)⁻¹ * (e 2)⁻¹
          = 1 := by
        simpa only [inv_inv] using hR5
      have h6' : e 0 * e 1 * e 0 * e 1 * ((e 3)⁻¹)⁻¹ * ((e 2)⁻¹)⁻¹ * ((e 3)⁻¹)⁻¹
          * ((e 2)⁻¹)⁻¹ = 1 := by
        calc _ = (e 0 * e 1) ^ 2 * (e 3 * e 2) ^ 2 := by simp only [sq]; group
          _ = 1 := by
            rw [hz_dc]
            show zOf e * zOf e = 1
            rw [← sq, hz_sq]
      have h7' : (e 0)⁻¹ * ((e 2)⁻¹)⁻¹ * e 0 * (e 2)⁻¹ = 1 := by
        simpa only [inv_inv] using inv_mul_mul_inv_of_comm cm02
      have h8' : (e 0)⁻¹ * ((e 3)⁻¹)⁻¹ * e 0 * (e 3)⁻¹ = 1 := by
        simpa only [inv_inv] using inv_mul_mul_inv_of_comm cm03
      have h9' : (e 1)⁻¹ * ((e 2)⁻¹)⁻¹ * e 1 * (e 2)⁻¹ = 1 := by
        simpa only [inv_inv] using inv_mul_mul_inv_of_comm cm12
      have h10' : (e 1)⁻¹ * ((e 3)⁻¹)⁻¹ * e 1 * (e 3)⁻¹ = 1 := by
        simpa only [inv_inv] using inv_mul_mul_inv_of_comm cm13
      refine ⟨![e 0, e 1, (e 2)⁻¹, (e 3)⁻¹, w₁, w₂], ?_, ?_⟩
      · exact satWords_append
          (satWords_relK_vec (e 0) (e 1) (e 2)⁻¹ (e 3)⁻¹ w₁ w₂ r0 r1 r2 h3' h4' h5' h6' h7'
            h8' h9' h10') hsat0
      · exact closure_four_eq_sup_of_sign hlet (Or.inl rfl) (Or.inl rfl) (Or.inr rfl)
          (Or.inr rfl)
    ·
      have hx : flipLetters (modelFlip (3, 2)) f = ![(e 0)⁻¹, (e 1)⁻¹, e 2, e 3, w₁, w₂] := by
        funext i; fin_cases i <;> first | rfl | simp [flipLetters, modelFlip, hf]
      rw [hx] at hsat0
      have h0' : ((e 0)⁻¹) ^ 3 = 1 := by rw [inv_pow, r0, inv_one]
      have h1' : ((e 1)⁻¹) ^ 3 = 1 := by rw [inv_pow, r1, inv_one]
      have h2' : ((e 1)⁻¹)⁻¹ * ((e 0)⁻¹)⁻¹ * (e 1)⁻¹ * ((e 0)⁻¹)⁻¹ * ((e 1)⁻¹)⁻¹ * (e 0)⁻¹
          = 1 := by
        simpa only [inv_inv] using relator_inv_of_inv r11 (eq_inv_of_mul_eq_one_left r12)
          (eq_inv_of_mul_eq_one_left r13) r2
      have h6' : (e 0)⁻¹ * (e 1)⁻¹ * (e 0)⁻¹ * (e 1)⁻¹ * (e 3)⁻¹ * (e 2)⁻¹ * (e 3)⁻¹
          * (e 2)⁻¹ = 1 := by
        calc _ = ((e 1 * e 0) ^ 2)⁻¹ * ((e 2 * e 3) ^ 2)⁻¹ := by
              simp only [sq, mul_inv_rev]; group
          _ = (zOf e)⁻¹ * (zOf e)⁻¹ := by rw [hz_ba, ← hzcd]
          _ = 1 := by rw [← mul_inv_rev, ← sq, hz_sq, inv_one]
      have h7' : ((e 0)⁻¹)⁻¹ * (e 2)⁻¹ * (e 0)⁻¹ * e 2 = 1 := by
        simpa only [inv_inv] using mul_inv_mul_inv_of_comm cm02
      have h8' : ((e 0)⁻¹)⁻¹ * (e 3)⁻¹ * (e 0)⁻¹ * e 3 = 1 := by
        simpa only [inv_inv] using mul_inv_mul_inv_of_comm cm03
      have h9' : ((e 1)⁻¹)⁻¹ * (e 2)⁻¹ * (e 1)⁻¹ * e 2 = 1 := by
        simpa only [inv_inv] using mul_inv_mul_inv_of_comm cm12
      have h10' : ((e 1)⁻¹)⁻¹ * (e 3)⁻¹ * (e 1)⁻¹ * e 3 = 1 := by
        simpa only [inv_inv] using mul_inv_mul_inv_of_comm cm13
      refine ⟨![(e 0)⁻¹, (e 1)⁻¹, e 2, e 3, w₁, w₂], ?_, ?_⟩
      · exact satWords_append
          (satWords_relK_vec ((e 0)⁻¹) ((e 1)⁻¹) (e 2) (e 3) w₁ w₂ h0' h1' h2' r3 r4 r5 h6' h7'
            h8' h9' h10') hsat0
      · exact closure_four_eq_sup_of_sign hlet (Or.inr rfl) (Or.inr rfl) (Or.inl rfl)
          (Or.inl rfl)
  ·
    exfalso
    have hsatc : SatWords (cfgWords k₁ k₂) f := satWords_append hK hvp
    have hbound : Nat.card (Subgroup.closure (Set.range f)) ≤ 288 := by
      exact card_closure_le_of_words hcol f hsatc
    have hsub : M₁ ⊔ H₂ ≤ Subgroup.closure (Set.range f) := by
      rw [← hlet.gen₂, ← hC₁]
      apply Subgroup.closure_mono
      rintro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨4, rfl⟩
      · exact ⟨5, rfl⟩
    have hbig := card_mul_le_card_sup (A := M₁) (B := H₂) hv₁.compl.disjoint
    rw [hms.card₁, card_H₂_of_G23One hone] at hbig
    have hle := Subgroup.card_le_of_le hsub
    omega

end CFSG.GH74.QTGen4.Recog.G23.P7
