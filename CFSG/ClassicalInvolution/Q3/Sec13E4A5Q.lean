module

public import CFSG.ClassicalInvolution.Q3.Sec13E4A5Pts

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.QuasithinUnique

namespace A5Q

section Pure

variable {M : Type*} [Group M]

theorem zmod_two_val_one : (1 : ZMod 2).val = 1 := rfl

theorem pow_val_add_of_mul_self {u : M} (hu : u * u = 1) (x y : ZMod 2) :
    u ^ (x + y).val = u ^ x.val * u ^ y.val := by
  have h2 : u ^ 2 = 1 := by rw [pow_two]; exact hu
  rw [ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ h2]

theorem mul_five_comm {a b : Fin 5 → M} (hab : ∀ i j, Commute (b i) (a j)) :
    a 0 * b 0 * (a 1 * b 1) * (a 2 * b 2) * (a 3 * b 3) * (a 4 * b 4) =
      a 0 * a 1 * a 2 * a 3 * a 4 * (b 0 * b 1 * b 2 * b 3 * b 4) := by
  have h1 : a 0 * b 0 * (a 1 * b 1) = a 0 * a 1 * (b 0 * b 1) :=
    (hab 0 1).mul_mul_mul_comm _ _
  have c2 : Commute (b 0 * b 1) (a 2) := (hab 0 2).mul_left (hab 1 2)
  have h2 : a 0 * a 1 * (b 0 * b 1) * (a 2 * b 2) = a 0 * a 1 * a 2 * (b 0 * b 1 * b 2) :=
    c2.mul_mul_mul_comm _ _
  have c3 : Commute (b 0 * b 1 * b 2) (a 3) := ((hab 0 3).mul_left (hab 1 3)).mul_left (hab 2 3)
  have h3 : a 0 * a 1 * a 2 * (b 0 * b 1 * b 2) * (a 3 * b 3) =
      a 0 * a 1 * a 2 * a 3 * (b 0 * b 1 * b 2 * b 3) :=
    c3.mul_mul_mul_comm _ _
  have c4 : Commute (b 0 * b 1 * b 2 * b 3) (a 4) :=
    (((hab 0 4).mul_left (hab 1 4)).mul_left (hab 2 4)).mul_left (hab 3 4)
  have h4 : a 0 * a 1 * a 2 * a 3 * (b 0 * b 1 * b 2 * b 3) * (a 4 * b 4) =
      a 0 * a 1 * a 2 * a 3 * a 4 * (b 0 * b 1 * b 2 * b 3 * b 4) :=
    c4.mul_mul_mul_comm _ _
  rw [h1, h2, h3, h4]

theorem prod_perm_five {p : Fin 5 → M} (hp : ∀ i j, Commute (p i) (p j))
    (σ : Equiv.Perm (Fin 5)) :
    p (σ 0) * p (σ 1) * p (σ 2) * p (σ 3) * p (σ 4) = p 0 * p 1 * p 2 * p 3 * p 4 := by
  classical
  have hc : (Set.range p).Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact hp i j
  letI : CommGroup (Subgroup.closure (Set.range p)) := Subgroup.closureCommGroupOfComm hc
  let q : Fin 5 → Subgroup.closure (Set.range p) :=
    fun i => ⟨p i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have h1 : ∏ i, q (σ i) = ∏ i, q i := Equiv.prod_comp σ q
  simp only [Fin.prod_univ_five] at h1
  exact congrArg Subtype.val h1

theorem eq_zero_or_one_of_prod_eq_one {w : Fin 5 → M} (hsq : ∀ i, w i * w i = 1)
    (hc : ∀ i j, Commute (w i) (w j)) (h1 : ∀ i, w i ≠ 1)
    (hne : ∀ i j, i ≠ j → w i ≠ w j) (hprod : w 0 * w 1 * w 2 * w 3 * w 4 = 1)
    (x : Fin 5 → ZMod 2)
    (hx : w 0 ^ (x 0).val * w 1 ^ (x 1).val * w 2 ^ (x 2).val * w 3 ^ (x 3).val *
      w 4 ^ (x 4).val = 1) : x = 0 ∨ x = fun _ => 1 := by
  classical
  have hc' : (Set.range w).Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact hc i j
  letI : CommGroup (Subgroup.closure (Set.range w)) := Subgroup.closureCommGroupOfComm hc'
  let u : Fin 5 → Subgroup.closure (Set.range w) :=
    fun i => ⟨w i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hu1 : ∀ i, u i ≠ 1 := fun i h => h1 i (congrArg Subtype.val h)
  have hune : ∀ i j, i ≠ j → u i ≠ u j := fun i j hij h => hne i j hij (congrArg Subtype.val h)
  have hu_inv : ∀ i, (u i)⁻¹ = u i := fun i =>
    inv_eq_of_mul_eq_one_right (Subtype.ext (hsq i))
  have hprodu : ∏ i, u i = 1 := by
    rw [Fin.prod_univ_five]; exact Subtype.ext hprod
  have hz : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  have hpow : ∀ i, u i ^ (x i).val = if x i = 1 then u i else 1 := by
    intro i
    rcases hz (x i) with h | h <;> simp [h, zmod_two_val_one]
  have hxu : ∏ i, u i ^ (x i).val = 1 := by
    rw [Fin.prod_univ_five]
    exact Subtype.ext hx
  set S : Finset (Fin 5) := Finset.univ.filter (fun i => x i = 1) with hS
  have hxS : ∏ i, u i ^ (x i).val = ∏ i ∈ S, u i := by
    rw [hS, Finset.prod_filter]
    exact Finset.prod_congr rfl (fun i _ => hpow i)
  have hP : ∏ i ∈ S, u i = 1 := by rw [← hxS]; exact hxu
  have key : ∀ T : Finset (Fin 5), ∏ i ∈ T, u i = 1 → T.card ≠ 1 ∧ T.card ≠ 2 := by
    intro T hT
    constructor
    · intro hc1
      obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc1
      rw [Finset.prod_singleton] at hT
      exact hu1 a hT
    · intro hc2
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hc2
      rw [Finset.prod_pair hab] at hT
      have : u a = u b := by
        have := eq_inv_of_mul_eq_one_left hT
        rw [this, hu_inv]
      exact hune a b hab this
  have hcomp : ∏ i ∈ Sᶜ, u i = 1 := by
    have := Finset.prod_mul_prod_compl S u
    rw [hP, one_mul, hprodu] at this
    exact this
  have h1S := key S hP
  have h2S := key Sᶜ hcomp
  have hcard : S.card + Sᶜ.card = 5 := by
    have := Finset.card_add_card_compl S
    simpa using this
  have hS5 : S.card ≤ 5 := by omega
  have hcases : S.card = 0 ∨ S.card = 5 := by omega
  rcases hcases with h0 | h5
  · left
    have hSe : S = ∅ := Finset.card_eq_zero.mp h0
    funext i
    have : ¬ x i = 1 := by
      intro hxi
      have : i ∈ S := by simp [hS, hxi]
      rw [hSe] at this
      simp at this
    rcases hz (x i) with h | h
    · simpa using h
    · exact absurd h this
  · right
    have hSu : S = Finset.univ := Finset.eq_univ_of_card S (by simpa using h5)
    funext i
    have : i ∈ S := by rw [hSu]; exact Finset.mem_univ i
    simpa [hS] using this

theorem conj_prod_five {w : Fin 5 → M} (hc : ∀ i j, Commute (w i) (w j))
    (σ : Equiv.Perm (Fin 5)) (φ : M →* M) (hφ : ∀ i, φ (w i) = w (σ i)) (x : Fin 5 → ZMod 2) :
    φ (w 0 ^ (x 0).val * w 1 ^ (x 1).val * w 2 ^ (x 2).val * w 3 ^ (x 3).val *
      w 4 ^ (x 4).val) =
      w 0 ^ (x (σ.symm 0)).val * w 1 ^ (x (σ.symm 1)).val * w 2 ^ (x (σ.symm 2)).val *
        w 3 ^ (x (σ.symm 3)).val * w 4 ^ (x (σ.symm 4)).val := by
  simp only [map_mul, map_pow, hφ]
  have := prod_perm_five (p := fun j => w j ^ (x (σ.symm j)).val)
    (fun i j => (hc i j).pow_pow _ _) σ
  simpa using this

theorem mem_closure_pair_iff {x y : M} (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y = y * x)
    (g : M) : g ∈ Subgroup.closure ({x, y} : Set M) ↔ g = 1 ∨ g = x ∨ g = y ∨ g = x * y := by
  have hyx : y * x = x * y := hxy.symm
  have e1 : x * (x * y) = y := by rw [← mul_assoc, hx, one_mul]
  have e2 : x * y * x = y := by rw [mul_assoc, hyx, e1]
  have e3 : x * y * y = x := by rw [mul_assoc, hy, mul_one]
  have e4 : y * (x * y) = x := by rw [hxy, ← mul_assoc, hy, one_mul]
  have e5 : x * y * (x * y) = 1 := by rw [mul_assoc, e4, hx]
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with rfl | hg
      · exact Or.inr (Or.inl rfl)
      · rw [Set.mem_singleton_iff] at hg
        exact Or.inr (Or.inr (Or.inl hg))
    | one => exact Or.inl rfl
    | mul g₁ g₂ _ _ h1 h2 =>
      rcases h1 with h1 | h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 | h2 <;> rw [h1, h2] <;>
        simp [hx, hy, hyx, e1, e2, e3, e4, e5]
    | inv g _ h =>
      rcases h with h | h | h | h <;> rw [h] <;> simp [hxi, hyi, hyx]
  · rintro (h | h | h | h) <;> rw [h]
    · exact one_mem _
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

theorem card_closure_pair {x y : M} (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y = y * x)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hne : x ≠ y) :
    Nat.card (Subgroup.closure ({x, y} : Set M)) = 4 := by
  classical
  have hset : ((Subgroup.closure ({x, y} : Set M) : Subgroup M) : Set M) =
      ↑({1, x, y, x * y} : Finset M) := by
    ext g
    simp only [SetLike.mem_coe, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    exact mem_closure_pair_iff hx hy hxy g
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hn1 : (1 : M) ≠ x * y := by
    intro h
    apply hne
    have := eq_inv_of_mul_eq_one_right h.symm
    rw [this, hxi]
  have hn2 : x ≠ x * y := by
    intro h
    apply hy1
    have : x * 1 = x * y := by rw [mul_one]; exact h
    exact (mul_left_cancel this).symm
  have hn3 : y ≠ x * y := by
    intro h
    apply hx1
    have : 1 * y = x * y := by rw [one_mul]; exact h
    exact (mul_right_cancel this).symm
  have hcard : Nat.card (Subgroup.closure ({x, y} : Set M)) =
      ((Subgroup.closure ({x, y} : Set M) : Subgroup M) : Set M).ncard :=
    Nat.card_coe_set_eq _
  rw [hcard, hset, Set.ncard_coe_finset]
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hn3]
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hne, hn2⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hx1.symm, hy1.symm, hn1⟩

theorem eq_closure_pair_of_card [Finite M] {H : Subgroup M} (hH : Nat.card H = 4) {x y : M}
    (hxH : x ∈ H) (hyH : y ∈ H) (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y = y * x)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hne : x ≠ y) : H = Subgroup.closure ({x, y} : Set M) := by
  symm
  refine Subgroup.eq_of_le_of_card_ge ((Subgroup.closure_le _).mpr ?_) ?_
  · rintro g (rfl | hg)
    · exact hxH
    · rw [Set.mem_singleton_iff] at hg
      rw [hg]; exact hyH
  · rw [hH, card_closure_pair hx hy hxy hx1 hy1 hne]

theorem klein_lift {z i j i' j' : M}
    (hz2 : z * z = 1)
    (hzi : i * z = z * i) (hzj : j * z = z * j) (hzi' : i' * z = z * i')
    (hii : i * i = z) (hjj : j * j = z) (hii' : i' * i' = z) (hjj' : j' * j' = z)
    (hij : j * i = z * (i * j)) (hij' : j' * i' = z * (i' * j'))
    (hci : i' * i = i * i') (hcj : j' * i = i * j') (hdi : i' * j = j * i')
    (hdj : j' * j = j * j') :
    (i * j') * (i * j') = 1 ∧ (j * (i' * j')) * (j * (i' * j')) = 1 ∧
      (i * j') * (j * (i' * j')) = (j * (i' * j')) * (i * j') := by
  have hwi : i' * j' * i = i * (i' * j') := by
    calc i' * j' * i = i' * (j' * i) := mul_assoc _ _ _
      _ = i' * (i * j') := by rw [hcj]
      _ = i' * i * j' := (mul_assoc _ _ _).symm
      _ = i * i' * j' := by rw [hci]
      _ = i * (i' * j') := mul_assoc _ _ _
  have hwj : i' * j' * j = j * (i' * j') := by
    calc i' * j' * j = i' * (j' * j) := mul_assoc _ _ _
      _ = i' * (j * j') := by rw [hdj]
      _ = i' * j * j' := (mul_assoc _ _ _).symm
      _ = j * i' * j' := by rw [hdi]
      _ = j * (i' * j') := mul_assoc _ _ _
  have hww : (i' * j') * (i' * j') = z := by
    calc (i' * j') * (i' * j') = i' * (j' * i') * j' := by group
      _ = i' * (z * (i' * j')) * j' := by rw [hij']
      _ = (i' * z) * (i' * j') * j' := by group
      _ = (z * i') * (i' * j') * j' := by rw [hzi']
      _ = z * (i' * i') * (j' * j') := by group
      _ = z * z * z := by rw [hii', hjj']
      _ = z := by rw [hz2, one_mul]
  have e1 : (i * j') * (i * j') = 1 := by
    calc (i * j') * (i * j') = i * (j' * i) * j' := by group
      _ = i * (i * j') * j' := by rw [hcj]
      _ = (i * i) * (j' * j') := by group
      _ = z * z := by rw [hii, hjj']
      _ = 1 := hz2
  have e2 : (j * (i' * j')) * (j * (i' * j')) = 1 := by
    calc (j * (i' * j')) * (j * (i' * j')) = j * ((i' * j') * j) * (i' * j') := by group
      _ = j * (j * (i' * j')) * (i' * j') := by rw [hwj]
      _ = (j * j) * ((i' * j') * (i' * j')) := by group
      _ = z * z := by rw [hjj, hww]
      _ = 1 := hz2
  have hjw : j' * (i' * j') = i' := by
    calc j' * (i' * j') = (j' * i') * j' := (mul_assoc _ _ _).symm
      _ = (z * (i' * j')) * j' := by rw [hij']
      _ = z * (i' * (j' * j')) := by group
      _ = z * (i' * z) := by rw [hjj']
      _ = z * (z * i') := by rw [hzi']
      _ = (z * z) * i' := (mul_assoc _ _ _).symm
      _ = i' := by rw [hz2, one_mul]
  have hwj' : (i' * j') * j' = i' * z := by
    calc (i' * j') * j' = i' * (j' * j') := mul_assoc _ _ _
      _ = i' * z := by rw [hjj']
  have hzij : (i * j) * z = z * (i * j) := by
    calc (i * j) * z = i * (j * z) := mul_assoc _ _ _
      _ = i * (z * j) := by rw [hzj]
      _ = (i * z) * j := (mul_assoc _ _ _).symm
      _ = (z * i) * j := by rw [hzi]
      _ = z * (i * j) := mul_assoc _ _ _
  refine ⟨e1, e2, ?_⟩
  have l : (i * j') * (j * (i' * j')) = (i * j) * i' := by
    calc (i * j') * (j * (i' * j')) = i * (j' * j) * (i' * j') := by group
      _ = i * (j * j') * (i' * j') := by rw [hdj]
      _ = (i * j) * (j' * (i' * j')) := by group
      _ = (i * j) * i' := by rw [hjw]
  have r : (j * (i' * j')) * (i * j') = (i * j) * i' := by
    calc (j * (i' * j')) * (i * j') = j * ((i' * j') * i) * j' := by group
      _ = j * (i * (i' * j')) * j' := by rw [hwi]
      _ = (j * i) * ((i' * j') * j') := by group
      _ = (j * i) * (i' * z) := by rw [hwj']
      _ = (z * (i * j)) * (z * i') := by rw [hij, hzi']
      _ = z * ((i * j) * z) * i' := by group
      _ = z * (z * (i * j)) * i' := by rw [hzij]
      _ = (z * z) * (i * j) * i' := by group
      _ = (i * j) * i' := by rw [hz2, one_mul]
  rw [l, r]

end Pure

section Central

open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

theorem commutator_eq_of_central {Γ : Type*} [Group Γ] {v₁ v₂ : Γ}
    (h₁ : ∀ x, v₁ * x = x * v₁) (h₂ : ∀ x, v₂ * x = x * v₂) (a b : Γ) :
    ⁅v₁ * a, v₂ * b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  have c1 : ∀ w, v₁ * w * v₁⁻¹ = w := fun w => by
    rw [h₁ w, mul_assoc, mul_inv_cancel, mul_one]
  have c2 : ∀ w, v₂ * w * v₂⁻¹ = w := fun w => by
    rw [h₂ w, mul_assoc, mul_inv_cancel, mul_one]
  calc v₁ * a * (v₂ * b) * (v₁ * a)⁻¹ * (v₂ * b)⁻¹
      = v₁ * (a * v₂ * b * a⁻¹) * v₁⁻¹ * b⁻¹ * v₂⁻¹ := by group
    _ = (a * v₂ * b * a⁻¹) * b⁻¹ * v₂⁻¹ := by rw [c1]
    _ = (v₂ * a * b * a⁻¹) * b⁻¹ * v₂⁻¹ := by rw [← h₂ a]
    _ = v₂ * (a * b * a⁻¹ * b⁻¹) * v₂⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := c2 _


theorem le_of_central_quotient {B Q X : Subgroup G} [B.Normal] (hBQ : B ≤ Q)
    (hQ2 : IsPGroup 2 Q)
    (hcent : ∀ g : G, ∀ q ∈ Q, QuotientGroup.mk' B g * QuotientGroup.mk' B q =
        QuotientGroup.mk' B q * QuotientGroup.mk' B g)
    (hperf : (⊤ : Subgroup G) ≤ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆)
    (S : Sylow 2 G) (hXS : X ≤ (S : Subgroup G)) (hXQ : Q ⊓ X ≤ B)
    (hQX : Q ⊔ X = (S : Subgroup G)) : Q ≤ B := by
  classical
  have hπ : Function.Surjective (QuotientGroup.mk' B) := QuotientGroup.mk'_surjective B
  set π : G →* G ⧸ B := QuotientGroup.mk' B with hπdef
  set V : Subgroup (G ⧸ B) := Q.map π with hV
  have hVc : ∀ v ∈ V, ∀ g : G ⧸ B, v * g = g * v := by
    intro v hv g
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hv
    obtain ⟨g, rfl⟩ := hπ g
    exact (hcent g q hq).symm
  haveI hVn : V.Normal := ⟨fun n hn g => by
    rw [← hVc n hn g, mul_assoc, mul_inv_cancel, mul_one]
    exact hn⟩
  haveI hVc' : IsMulCommutative V := ⟨⟨fun a b => Subtype.ext (hVc a.1 a.2 b.1)⟩⟩
  have hV2 : IsPGroup 2 V := hQ2.map π
  let P' : Sylow 2 (G ⧸ B) := S.mapSurjective hπ
  have hP' : (P' : Subgroup (G ⧸ B)) = (S : Subgroup G).map π := Sylow.coe_mapSurjective hπ S
  have hle : X.map π ≤ (P' : Subgroup (G ⧸ B)) := by
    rw [hP']; exact Subgroup.map_mono hXS
  have hinf : V ⊓ X.map π = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyV, hyX⟩
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hyV
    obtain ⟨x, hx, hxq⟩ := Subgroup.mem_map.mp hyX
    have h1 : x⁻¹ * q ∈ B := (QuotientGroup.eq).mp hxq
    have hxQ : x ∈ Q := by
      have : x⁻¹ ∈ Q := by
        have h2 : x⁻¹ * q * q⁻¹ ∈ Q := Q.mul_mem (hBQ h1) (Q.inv_mem hq)
        simpa using h2
      simpa using Q.inv_mem this
    have hxB : x ∈ B := hXQ ⟨hxQ, hx⟩
    have : π x = 1 := (QuotientGroup.eq_one_iff x).mpr hxB
    rw [Subgroup.mem_bot, ← hxq]
    exact this
  have hsup : V ⊔ X.map π = (P' : Subgroup (G ⧸ B)) := by
    rw [hP', hV, ← Subgroup.map_sup, hQX]
  obtain ⟨H', hH1, hH2⟩ := (CFSG.Quasithin.gaschutz hV2 P').mpr ⟨X.map π, hle, hinf, hsup⟩
  have hcomm : ∀ g₁ g₂ : G ⧸ B, ⁅g₁, g₂⁆ ∈ H' := by
    intro g₁ g₂
    have h1 : g₁ ∈ V ⊔ H' := by rw [hH2]; trivial
    have h2 : g₂ ∈ V ⊔ H' := by rw [hH2]; trivial
    obtain ⟨v₁, hv₁, a, ha, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp h1
    obtain ⟨v₂, hv₂, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp h2
    rw [commutator_eq_of_central (hVc v₁ hv₁) (hVc v₂ hv₂), commutatorElement_def]
    exact H'.mul_mem (H'.mul_mem (H'.mul_mem ha hb) (H'.inv_mem ha)) (H'.inv_mem hb)
  have hle' : (⊤ : Subgroup (G ⧸ B)) ≤ ⁅(⊤ : Subgroup (G ⧸ B)), ⊤⁆ := by
    have := Subgroup.map_mono (f := π) hperf
    rwa [Subgroup.map_commutator, Subgroup.map_top_of_surjective π hπ] at this
  have hH'top : H' = ⊤ :=
    top_le_iff.mp (hle'.trans (Subgroup.commutator_le.mpr fun g₁ _ g₂ _ => hcomm g₁ g₂))
  rw [hH'top, inf_top_eq] at hH1
  have := (Subgroup.map_eq_bot_iff _).mp hH1
  rwa [QuotientGroup.ker_mk'] at this

end Central

theorem alternatingGroup_five_pow_eq_one :
    ∀ g : alternatingGroup (Fin 5), g ^ 2 = 1 ∨ g ^ 3 = 1 ∨ g ^ 5 = 1 := by
  decide +kernel

theorem mem_normalizer_of_conjSub_eq {Γ : Type*} [Group Γ] {K : Subgroup Γ} {t : Γ}
    (h : conjSub t K = K) : t ∈ Subgroup.normalizer (K : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 : conjSub t⁻¹ K = K := by
    conv_lhs => rw [← h]
    exact conjSub_inv_conjSub t K
  have h2 : x ∈ conjSub t⁻¹ K ↔ x ∈ K := by rw [h1]
  rw [mem_conjSub_iff, inv_inv] at h2
  exact h2.symm

theorem uniqueInvolution_comm {Γ : Type*} [Group Γ] {K : Subgroup Γ} {z : Γ}
    (hz : IsUniqueInvolution K z) {u : Γ} (hu : u ∈ K) : u * z = z * u :=
  mul_inv_eq_iff_eq_mul.mp (hz.conj_eq (conjSub_eq_self_of_mem hu))

theorem mem_sup_pCore_iff {Γ : Type} [Group Γ] [Finite Γ] (K : Subgroup Γ) (x : Γ) :
    x ∈ K ⊔ pCore 2 Γ ↔ QuotientGroup.mk' (pCore 2 Γ) x ∈ bar K := by
  rw [← comap_bar K]
  exact Iff.rfl

end A5Q

variable {G : Type} [Group G] [Finite G]

namespace E4Hyp

section Members

variable {Ω : Set (Subgroup G)} {W : Subgroup G} (h : E4Hyp Ω W)
include h

theorem member_inf_pCore_cases {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) {k : G} (hk : k ∈ K) (hkQ : k ∈ pCore 2 G) :
    k = 1 ∨ k = z := by
  have hcard := h.card_inf_pCore_le hK
  have hmem : k ∈ K ⊓ pCore 2 G := ⟨hk, hkQ⟩
  have hdvd : orderOf k ∣ Nat.card ↥(K ⊓ pCore 2 G) := by
    have := orderOf_dvd_natCard (⟨k, hmem⟩ : ↥(K ⊓ pCore 2 G))
    rwa [Subgroup.orderOf_mk] at this
  have hpos : 0 < Nat.card ↥(K ⊓ pCore 2 G) := Nat.card_pos
  have hle : orderOf k ∣ 2 := by
    have : Nat.card ↥(K ⊓ pCore 2 G) = 1 ∨ Nat.card ↥(K ⊓ pCore 2 G) = 2 := by omega
    rcases this with h1 | h1 <;> rw [h1] at hdvd
    · exact hdvd.trans (one_dvd 2)
    · exact hdvd
  have hk2 : k * k = 1 := by
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp hle
  exact hz.unique k hk hk2

theorem member_sq_cases {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z)
    {k : G} (hk : k ∈ K) : k * k = 1 ∨ k * k = z := by
  have hQn : (pCore 2 G).Normal := CFSG.pCore_normal
  have hsq := (h.isElemAbelian_bar hK).2 (QuotientGroup.mk' (pCore 2 G) k)
    (Subgroup.mem_map_of_mem _ hk)
  have hkk : k * k ∈ pCore 2 G := by
    rw [pow_two, ← map_mul] at hsq
    exact (QuotientGroup.eq_one_iff _).mp hsq
  exact h.member_inf_pCore_cases hK hz (K.mul_mem hk hk) hkk

theorem member_comm_cases {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z)
    {k k' : G} (hk : k ∈ K) (hk' : k' ∈ K) :
    k * k' * k⁻¹ * k'⁻¹ = 1 ∨ k * k' * k⁻¹ * k'⁻¹ = z := by
  have hQn : (pCore 2 G).Normal := CFSG.pCore_normal
  have hc := (h.isElemAbelian_bar hK).1.is_comm.comm
    ⟨QuotientGroup.mk' (pCore 2 G) k, Subgroup.mem_map_of_mem _ hk⟩
    ⟨QuotientGroup.mk' (pCore 2 G) k', Subgroup.mem_map_of_mem _ hk'⟩
  have hc' : QuotientGroup.mk' (pCore 2 G) k * QuotientGroup.mk' (pCore 2 G) k' =
      QuotientGroup.mk' (pCore 2 G) k' * QuotientGroup.mk' (pCore 2 G) k :=
    congrArg Subtype.val hc
  have hQ : k * k' * k⁻¹ * k'⁻¹ ∈ pCore 2 G := by
    refine (QuotientGroup.eq_one_iff _).mp ?_
    show QuotientGroup.mk' (pCore 2 G) (k * k' * k⁻¹ * k'⁻¹) = 1
    simp only [map_mul, map_inv]
    rw [hc']
    group
  exact h.member_inf_pCore_cases hK hz
    (K.mul_mem (K.mul_mem (K.mul_mem hk hk') (K.inv_mem hk)) (K.inv_mem hk')) hQ

theorem member_sq_eq {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z)
    {i j : G} (hi : i ∈ K) (hj : j ∈ K) (hij : i * j ≠ j * i) : i * i = z := by
  rcases h.member_sq_cases hK hz hi with h1 | h1
  · exfalso
    apply hij
    rcases hz.unique i hi h1 with rfl | rfl
    · rw [one_mul, mul_one]
    · exact (A5Q.uniqueInvolution_comm hz hj).symm
  · exact h1

theorem member_comm_eq {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z)
    {i j : G} (hi : i ∈ K) (hj : j ∈ K) (hij : i * j ≠ j * i) : j * i = z * (i * j) := by
  rcases h.member_comm_cases hK hz hi hj with h1 | h1
  · exfalso
    apply hij
    calc i * j = (i * j * i⁻¹ * j⁻¹) * (j * i) := by group
      _ = j * i := by rw [h1, one_mul]
  · have h2 : i * j = z * (j * i) := by
      calc i * j = (i * j * i⁻¹ * j⁻¹) * (j * i) := by group
        _ = z * (j * i) := by rw [h1]
    calc j * i = z * z * (j * i) := by rw [hz.sq, one_mul]
      _ = z * (z * (j * i)) := mul_assoc z z _
      _ = z * (i * j) := by rw [← h2]

theorem member_bar_gen {K : Subgroup G} (hK : K ∈ Ω) {i j : G} (hi : i ∈ K) (hj : j ∈ K)
    (hij : i * j ≠ j * i) :
    QuotientGroup.mk' (pCore 2 G) i ≠ 1 ∧ QuotientGroup.mk' (pCore 2 G) j ≠ 1 ∧
    QuotientGroup.mk' (pCore 2 G) i ≠ QuotientGroup.mk' (pCore 2 G) j ∧
    QuotientGroup.mk' (pCore 2 G) i * QuotientGroup.mk' (pCore 2 G) i = 1 ∧
    QuotientGroup.mk' (pCore 2 G) j * QuotientGroup.mk' (pCore 2 G) j = 1 ∧
    QuotientGroup.mk' (pCore 2 G) i * QuotientGroup.mk' (pCore 2 G) j =
      QuotientGroup.mk' (pCore 2 G) j * QuotientGroup.mk' (pCore 2 G) i ∧
    bar K = Subgroup.closure
      ({QuotientGroup.mk' (pCore 2 G) i, QuotientGroup.mk' (pCore 2 G) j} :
        Set (G ⧸ pCore 2 G)) := by
  have hQn : (pCore 2 G).Normal := CFSG.pCore_normal
  obtain ⟨z, hz⟩ := h.exists_uniqueInvolution hK
  have hzc : ∀ u ∈ K, u * z = z * u := fun u hu => A5Q.uniqueInvolution_comm hz hu
  have hi1 : QuotientGroup.mk' (pCore 2 G) i ≠ 1 := by
    intro h1
    have hiQ : i ∈ pCore 2 G := (QuotientGroup.eq_one_iff i).mp h1
    apply hij
    rcases h.member_inf_pCore_cases hK hz hi hiQ with rfl | rfl
    · rw [one_mul, mul_one]
    · exact (hzc j hj).symm
  have hj1 : QuotientGroup.mk' (pCore 2 G) j ≠ 1 := by
    intro h1
    have hjQ : j ∈ pCore 2 G := (QuotientGroup.eq_one_iff j).mp h1
    apply hij
    rcases h.member_inf_pCore_cases hK hz hj hjQ with rfl | rfl
    · rw [one_mul, mul_one]
    · exact hzc i hi
  have hne : QuotientGroup.mk' (pCore 2 G) i ≠ QuotientGroup.mk' (pCore 2 G) j := by
    intro h1
    have h2 : i⁻¹ * j ∈ pCore 2 G := QuotientGroup.eq.mp h1
    have h3 : i⁻¹ * j ∈ K := K.mul_mem (K.inv_mem hi) hj
    apply hij
    rcases h.member_inf_pCore_cases hK hz h3 h2 with h4 | h4
    · rw [← inv_mul_eq_one.mp h4]
    · have h5 : j = i * z := by rw [← h4]; group
      rw [h5, mul_assoc i z i, ← hzc i hi]
  have hsq : ∀ x ∈ K, QuotientGroup.mk' (pCore 2 G) x * QuotientGroup.mk' (pCore 2 G) x = 1 := by
    intro x hx
    have := (h.isElemAbelian_bar hK).2 (QuotientGroup.mk' (pCore 2 G) x)
      (Subgroup.mem_map_of_mem _ hx)
    rwa [pow_two] at this
  have hcomm : QuotientGroup.mk' (pCore 2 G) i * QuotientGroup.mk' (pCore 2 G) j =
      QuotientGroup.mk' (pCore 2 G) j * QuotientGroup.mk' (pCore 2 G) i :=
    congrArg Subtype.val ((h.isElemAbelian_bar hK).1.is_comm.comm
      ⟨QuotientGroup.mk' (pCore 2 G) i, Subgroup.mem_map_of_mem _ hi⟩
      ⟨QuotientGroup.mk' (pCore 2 G) j, Subgroup.mem_map_of_mem _ hj⟩)
  exact ⟨hi1, hj1, hne, hsq i hi, hsq j hj, hcomm,
    A5Q.eq_closure_pair_of_card (h.card_bar hK) (Subgroup.mem_map_of_mem _ hi)
      (Subgroup.mem_map_of_mem _ hj) (hsq i hi) (hsq j hj) hcomm hi1 hj1 hne⟩

theorem conj_cases_of_normalizes_sup {K J : Subgroup G} (hp : Paired Ω K J) {g : G}
    (hg : conjSub g (K ⊔ pCore 2 G) ≤ K ⊔ pCore 2 G) :
    (conjSub g K = K ∧ conjSub g J = J) ∨ (conjSub g K = J ∧ conjSub g J = K) := by
  have hKle : conjSub g K ≤ K ⊔ pCore 2 G := (conjSub_mono le_sup_left).trans hg
  have hJle : conjSub g J ≤ K ⊔ pCore 2 G := (conjSub_mono (h.le_sup_pCore hp)).trans hg
  have hK' : conjSub g K ∈ Ω := h.thmD.hyp.conjInvariant g K hp.1
  have hJ' : conjSub g J ∈ Ω := h.thmD.hyp.conjInvariant g J hp.2.1
  have hne : conjSub g K ≠ conjSub g J := fun he => hp.2.2.1 (conjSub_injective g he)
  rcases h.eq_or_eq_of_le_sup hp hK' hKle with h1 | h1 <;>
    rcases h.eq_or_eq_of_le_sup hp hJ' hJle with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hne

end Members

variable {Ω : Set (Subgroup G)} {W : Subgroup G} (h : E4Hyp Ω W)
  (a : G ⧸ pCore 2 G ≃* alternatingGroup (Fin 5))

@[expose] noncomputable def beta : Multiplicative (Fin 5 → ZMod 2) →* G where
  toFun f := h.w a 0 ^ (f.toAdd 0).val * h.w a 1 ^ (f.toAdd 1).val * h.w a 2 ^ (f.toAdd 2).val *
    h.w a 3 ^ (f.toAdd 3).val * h.w a 4 ^ (f.toAdd 4).val
  map_one' := by
    simp
  map_mul' f g := by
    simp only [toAdd_mul, Pi.add_apply]
    rw [A5Q.pow_val_add_of_mul_self (h.w_mul_self a 0),
      A5Q.pow_val_add_of_mul_self (h.w_mul_self a 1),
      A5Q.pow_val_add_of_mul_self (h.w_mul_self a 2),
      A5Q.pow_val_add_of_mul_self (h.w_mul_self a 3),
      A5Q.pow_val_add_of_mul_self (h.w_mul_self a 4)]
    exact A5Q.mul_five_comm (a := fun i => h.w a i ^ (f.toAdd i).val)
      (b := fun i => h.w a i ^ (g.toAdd i).val)
      fun i j => (show Commute (h.w a i) (h.w a j) from h.w_comm a i j).pow_pow _ _

include h a

theorem exists_sylow_eq_sup_pCore {K : Subgroup G} (hK : K ∈ Ω) :
    ∃ S : Sylow 2 G, (S : Subgroup G) = K ⊔ pCore 2 G := by
  have hQn : (pCore 2 G).Normal := CFSG.pCore_normal
  have hP2 : IsPGroup 2 ↥(K ⊔ pCore 2 G) :=
    IsPGroup.to_sup_of_normal_right' (h.isPGroup hK) (CFSG.pCore_isPGroup (p := 2) (G := G))
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hcardA : Nat.card (G ⧸ pCore 2 G) = 60 := by
    rw [Nat.card_congr a.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  have hidx : (K ⊔ pCore 2 G).index = 15 := by
    rw [← comap_bar K, Subgroup.index_comap_of_surjective (bar K) (QuotientGroup.mk'_surjective _)]
    have h1 : (bar K).index * Nat.card (bar K) = Nat.card (G ⧸ pCore 2 G) :=
      Subgroup.index_mul_card (bar K)
    rw [h.card_bar hK, hcardA] at h1
    omega
  exact ⟨hP2.toSylow (by rw [hidx]; decide), rfl⟩

theorem beta_single (γ : Fin 5) :
    h.beta a (Multiplicative.ofAdd (Pi.single γ 1)) = h.w a γ := by
  show h.w a 0 ^ ((Pi.single γ (1 : ZMod 2) : Fin 5 → ZMod 2) 0).val *
    h.w a 1 ^ ((Pi.single γ (1 : ZMod 2) : Fin 5 → ZMod 2) 1).val *
    h.w a 2 ^ ((Pi.single γ (1 : ZMod 2) : Fin 5 → ZMod 2) 2).val *
    h.w a 3 ^ ((Pi.single γ (1 : ZMod 2) : Fin 5 → ZMod 2) 3).val *
    h.w a 4 ^ ((Pi.single γ (1 : ZMod 2) : Fin 5 → ZMod 2) 4).val = h.w a γ
  fin_cases γ <;> simp [Pi.single_apply, A5Q.zmod_two_val_one]

theorem beta_eq_one_iff (f : Multiplicative (Fin 5 → ZMod 2)) :
    h.beta a f = 1 ↔ (f.toAdd = 0 ∨ f.toAdd = fun _ => 1) := by
  constructor
  · intro hf
    exact A5Q.eq_zero_or_one_of_prod_eq_one (w := h.w a) (h.w_mul_self a)
      (fun i j => h.w_comm a i j) (h.w_ne_one a) (fun i j hij => h.w_ne a i j hij) (h.prod_w a)
      f.toAdd hf
  · rintro (h0 | h1)
    · have : f = 1 := Multiplicative.toAdd.injective (by rw [h0]; rfl)
      rw [this, map_one]
    · show h.w a 0 ^ (f.toAdd 0).val * h.w a 1 ^ (f.toAdd 1).val * h.w a 2 ^ (f.toAdd 2).val *
        h.w a 3 ^ (f.toAdd 3).val * h.w a 4 ^ (f.toAdd 4).val = 1
      rw [h1]
      simpa [A5Q.zmod_two_val_one] using h.prod_w a

theorem conj_beta (g : G) (f : Multiplicative (Fin 5 → ZMod 2)) :
    g * h.beta a f * g⁻¹ =
      h.beta a (Multiplicative.ofAdd (fun γ => f.toAdd ((sig a g).symm γ))) :=
  A5Q.conj_prod_five (w := h.w a) (fun i j => h.w_comm a i j) (sig a g)
    (MulAut.conj g).toMonoidHom (fun i => h.conj_w a g i) f.toAdd

theorem range_beta_le : (h.beta a).range ≤ pCore 2 G := by
  rintro _ ⟨f, rfl⟩
  have hw := h.w_mem_pCore a
  exact (pCore 2 G).mul_mem ((pCore 2 G).mul_mem ((pCore 2 G).mul_mem
    ((pCore 2 G).mul_mem ((pCore 2 G).pow_mem (hw 0) _) ((pCore 2 G).pow_mem (hw 1) _))
    ((pCore 2 G).pow_mem (hw 2) _)) ((pCore 2 G).pow_mem (hw 3) _)) ((pCore 2 G).pow_mem (hw 4) _)

theorem exists_three {K : Subgroup G} (hK : K ∈ Ω) :
    ∃ y : G, y ^ 3 = 1 ∧ conjSub y K = K ∧ ⁅K, Subgroup.zpowers y⁆ = K := by
  classical
  have hQn : (pCore 2 G).Normal := CFSG.pCore_normal
  obtain ⟨z, hz⟩ := h.exists_uniqueInvolution hK
  obtain ⟨i, hi, j, hj, hij⟩ := h.nonabelian hK
  obtain ⟨hi1, hj1, hne, hi2, hj2, hcomm, hbar⟩ := h.member_bar_gen hK hi hj hij
  set π : G →* G ⧸ pCore 2 G := QuotientGroup.mk' (pCore 2 G) with hπ
  obtain ⟨ib, hib⟩ : ∃ x : G ⧸ pCore 2 G, π i = x := ⟨_, rfl⟩
  obtain ⟨jb, hjb⟩ : ∃ x : G ⧸ pCore 2 G, π j = x := ⟨_, rfl⟩
  rw [hib] at hi1 hne hi2 hcomm hbar
  rw [hjb] at hj1 hne hj2 hcomm hbar
  have hu1 : a ib ≠ 1 := fun h1 => hi1 (a.map_eq_one_iff.mp h1)
  have hv1 : a jb ≠ 1 := fun h1 => hj1 (a.map_eq_one_iff.mp h1)
  have huv : a ib ≠ a jb := fun h1 => hne (a.injective h1)
  have hu2 : a ib * a ib = 1 := by rw [← map_mul, hi2, map_one]
  have hv2 : a jb * a jb = 1 := by rw [← map_mul, hj2, map_one]
  have huv' : a ib * a jb = a jb * a ib := by rw [← map_mul, ← map_mul, hcomm]
  obtain ⟨c, hc1, hc2⟩ := A5.exists_cycle (a ib) (a jb) hu1 hv1 huv hu2 hv2 huv'
  obtain ⟨c', hc'⟩ : ∃ x : G ⧸ pCore 2 G, a.symm c = x := ⟨_, rfl⟩
  have hac' : a c' = c := by rw [← hc']; exact a.apply_symm_apply c
  have hc'1 : c' * ib * c'⁻¹ = jb := by
    apply a.injective
    simp only [map_mul, map_inv, hac']
    exact hc1
  have hc'2 : c' * jb * c'⁻¹ = ib * jb := by
    apply a.injective
    simp only [map_mul, map_inv, hac']
    exact hc2
  have hiinv : ib⁻¹ = ib := inv_eq_of_mul_eq_one_right hi2
  have hjinv : jb⁻¹ = jb := inv_eq_of_mul_eq_one_right hj2
  have hc3 : c' ^ 3 = 1 := by
    have hpow : ∀ k : ℕ, c ^ k = 1 → c' ^ k = 1 := fun k hk => by
      apply a.injective
      rw [map_pow, hac', map_one]
      exact hk
    rcases A5Q.alternatingGroup_five_pow_eq_one c with h2 | h3 | h5
    · exfalso
      have e2 : c' * c' = 1 := by rw [← pow_two]; exact hpow 2 h2
      have : ib = ib * jb := by
        calc ib = (c' * c') * ib * (c' * c')⁻¹ := by rw [e2]; simp
          _ = c' * (c' * ib * c'⁻¹) * c'⁻¹ := by group
          _ = c' * jb * c'⁻¹ := by rw [hc'1]
          _ = ib * jb := hc'2
      exact hj1 (by simpa using this)
    · exact hpow 3 h3
    · exfalso
      have e5 := hpow 5 h5
      have e3 : c' ^ 3 * ib * (c' ^ 3)⁻¹ = ib := by
        calc c' ^ 3 * ib * (c' ^ 3)⁻¹ = c' * (c' * (c' * ib * c'⁻¹) * c'⁻¹) * c'⁻¹ := by
              rw [pow_three']; group
          _ = c' * (c' * jb * c'⁻¹) * c'⁻¹ := by rw [hc'1]
          _ = c' * (ib * jb) * c'⁻¹ := by rw [hc'2]
          _ = (c' * ib * c'⁻¹) * (c' * jb * c'⁻¹) := by group
          _ = jb * (ib * jb) := by rw [hc'1, hc'2]
          _ = ib * (jb * jb) := by rw [← mul_assoc, ← hcomm, mul_assoc]
          _ = ib := by rw [hj2, mul_one]
      have e6 : (c' ^ 3) ^ 2 = c' := by
        calc (c' ^ 3) ^ 2 = c' ^ 6 := (pow_mul c' 3 2).symm.trans rfl
          _ = c' * c' ^ 5 := pow_succ' c' 5
          _ = c' := by rw [e5, mul_one]
      have hcm : Commute (c' ^ 3) ib := mul_inv_eq_iff_eq_mul.mp e3
      have hcm2 : Commute c' ib := by
        have := hcm.pow_left 2
        rwa [e6] at this
      apply hne
      rw [← hc'1]
      have := hcm2.eq
      rw [this]
      group
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective c'
  have hπg : π g = c' := hg
  have hg3 : g ^ 3 ∈ pCore 2 G := by
    refine (QuotientGroup.eq_one_iff _).mp ?_
    show π (g ^ 3) = 1
    rw [map_pow, hπg, hc3]
  obtain ⟨m, hm⟩ : ∃ m : ℕ, orderOf (g ^ 3) = 2 ^ m := by
    obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp (CFSG.pCore_isPGroup (p := 2) (G := G)))
      ⟨g ^ 3, hg3⟩
    rw [Subgroup.orderOf_mk] at hm
    exact ⟨m, hm⟩
  set n := orderOf (g ^ 3) with hn
  have hnn : (n * n) % 3 = 1 := by
    rw [hm, ← mul_pow]
    norm_num [Nat.pow_mod]
  set y : G := g ^ (n * n) with hy
  have hy3 : y ^ 3 = 1 := by
    have h1 : (g ^ 3) ^ n = 1 := pow_orderOf_eq_one _
    calc y ^ 3 = (g ^ 3) ^ (n * n) := by rw [hy, ← pow_mul, ← pow_mul, mul_comm]
      _ = ((g ^ 3) ^ n) ^ n := by rw [pow_mul]
      _ = 1 := by rw [h1, one_pow]
  have hπy : π y = c' := by
    rw [hy, map_pow, hπg, pow_eq_pow_mod _ hc3, hnn, pow_one]
  have hbarc : ∀ s ∈ bar K, c' * s * c'⁻¹ ∈ bar K := by
    intro s hs
    rw [hbar] at hs ⊢
    have hib' : ib ∈ Subgroup.closure ({ib, jb} : Set (G ⧸ pCore 2 G)) :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    have hjb' : jb ∈ Subgroup.closure ({ib, jb} : Set (G ⧸ pCore 2 G)) :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    rcases (A5Q.mem_closure_pair_iff hi2 hj2 hcomm s).mp hs with h1 | h1 | h1 | h1 <;> rw [h1]
    · simp
    · rw [hc'1]; exact hjb'
    · rw [hc'2]; exact Subgroup.mul_mem _ hib' hjb'
    · have : c' * (ib * jb) * c'⁻¹ = ib := by
        calc c' * (ib * jb) * c'⁻¹ = (c' * ib * c'⁻¹) * (c' * jb * c'⁻¹) := by group
          _ = jb * (ib * jb) := by rw [hc'1, hc'2]
          _ = ib * (jb * jb) := by rw [← mul_assoc, ← hcomm, mul_assoc]
          _ = ib := by rw [hj2, mul_one]
      rw [this]; exact hib'
  have hnorm : conjSub y (K ⊔ pCore 2 G) ≤ K ⊔ pCore 2 G := by
    intro x hx
    rw [mem_conjSub_iff, A5Q.mem_sup_pCore_iff] at hx
    rw [A5Q.mem_sup_pCore_iff]
    have e : QuotientGroup.mk' (pCore 2 G) x =
        c' * QuotientGroup.mk' (pCore 2 G) (y⁻¹ * x * y) * c'⁻¹ := by
      show π x = c' * π (y⁻¹ * x * y) * c'⁻¹
      rw [map_mul, map_mul, map_inv, hπy]
      group
    rw [e]
    exact hbarc _ hx
  obtain ⟨J, hp⟩ := h.exists_partner hK
  have hyK : conjSub y K = K := by
    rcases h.conj_cases_of_normalizes_sup hp hnorm with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact h1
    · exfalso
      have e : conjSub (y * y * y) K = J := by
        rw [conjSub_mul, conjSub_mul, h1, h2, h1]
      have e1 : y * y * y = 1 := (pow_three' y).symm.trans hy3
      rw [e1, conjSub_one] at e
      exact hp.2.2.1 e
  refine ⟨y, hy3, hyK, ?_⟩
  have hyN : y ∈ Subgroup.normalizer (K : Set G) := A5Q.mem_normalizer_of_conjSub_eq hyK
  have hXK : ⁅K, Subgroup.zpowers y⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro k hk e he
    have heN : e ∈ Subgroup.normalizer (K : Set G) := (Subgroup.zpowers_le.mpr hyN) he
    rw [commutatorElement_def]
    have h1 : e * k⁻¹ * e⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp heN k⁻¹).mp (K.inv_mem hk)
    have h2 : k * e * k⁻¹ * e⁻¹ = k * (e * k⁻¹ * e⁻¹) := by group
    rw [h2]
    exact K.mul_mem hk h1
  refine le_antisymm hXK ?_
  set X := ⁅K, Subgroup.zpowers y⁆ with hX
  have hyz : y ∈ Subgroup.zpowers y := Subgroup.mem_zpowers y
  have hXi : i * y * i⁻¹ * y⁻¹ ∈ X := Subgroup.commutator_mem_commutator hi hyz
  have hXj : j * y * j⁻¹ * y⁻¹ ∈ X := Subgroup.commutator_mem_commutator hj hyz
  have hπi : π (i * y * i⁻¹ * y⁻¹) = ib * jb := by
    simp only [map_mul, map_inv, hπy, hib, hiinv]
    calc ib * c' * ib * c'⁻¹ = ib * (c' * ib * c'⁻¹) := by group
      _ = ib * jb := by rw [hc'1]
  have hπj : π (j * y * j⁻¹ * y⁻¹) = ib := by
    simp only [map_mul, map_inv, hπy, hjb, hjinv]
    calc jb * c' * jb * c'⁻¹ = jb * (c' * jb * c'⁻¹) := by group
      _ = jb * (ib * jb) := by rw [hc'2]
      _ = ib * (jb * jb) := by rw [← mul_assoc, ← hcomm, mul_assoc]
      _ = ib := by rw [hj2, mul_one]
  have hbX : bar K ≤ X.map π := by
    rw [hbar, Subgroup.closure_le]
    have h1 : ib ∈ X.map π := ⟨_, hXj, hπj⟩
    have h2 : ib * jb ∈ X.map π := ⟨_, hXi, hπi⟩
    intro s hs
    rcases hs with rfl | hs
    · exact h1
    · rw [Set.mem_singleton_iff] at hs
      rw [hs]
      have := (X.map π).mul_mem ((X.map π).inv_mem h1) h2
      simpa using this
  have hzX : z ∈ X := by
    have hx0K := hXK hXi
    have hx0 : i * y * i⁻¹ * y⁻¹ ≠ 1 := by
      intro h1
      have h2 : π (i * y * i⁻¹ * y⁻¹) = 1 := by rw [h1, map_one]
      rw [hπi] at h2
      apply hne
      rw [eq_inv_of_mul_eq_one_left h2, hjinv]
    rcases h.member_sq_cases hK hz hx0K with h1 | h1
    · rcases hz.unique _ hx0K h1 with h2 | h2
      · exact absurd h2 hx0
      · rw [← h2]; exact hXi
    · rw [← h1]; exact X.mul_mem hXi hXi
  intro k hk
  obtain ⟨x, hxX, hxk⟩ := hbX (Subgroup.mem_map_of_mem _ hk)
  have h1 : x⁻¹ * k ∈ pCore 2 G := QuotientGroup.eq.mp hxk
  have h2 : x⁻¹ * k ∈ K := K.mul_mem (K.inv_mem (hXK hxX)) hk
  rcases h.member_inf_pCore_cases hK hz h2 h1 with h3 | h3
  · have : k = x := (inv_mul_eq_one.mp h3).symm
    rw [this]; exact hxX
  · have : k = x * z := by rw [← h3]; group
    rw [this]; exact X.mul_mem hxX hzX

theorem range_beta_eq : (h.beta a).range = pCore 2 G := by
  classical
  have hQn : (pCore 2 G).Normal := CFSG.pCore_normal
  refine le_antisymm (h.range_beta_le a) ?_
  haveI hBn : (h.beta a).range.Normal :=
    ⟨fun n hn g => by
      obtain ⟨f, rfl⟩ := hn
      exact ⟨_, (h.conj_beta a g f).symm⟩⟩
  have hwB : ∀ δ : Fin 5, h.w a δ ∈ (h.beta a).range := fun δ => ⟨_, h.beta_single a δ⟩
  have hzB : ∀ {L : Subgroup G}, L ∈ Ω → ∀ {z' : G}, IsUniqueInvolution L z' →
      z' ∈ (h.beta a).range := by
    intro L hL z' hz'
    obtain ⟨γ, hγ, -⟩ := h.existsUnique_over a hL
    rw [← h.w_eq a hL hγ hz']
    exact hwB γ
  have hmem : ∀ L ∈ Ω, ∀ q ∈ pCore 2 G, ∀ k ∈ L,
      QuotientGroup.mk' (h.beta a).range q * QuotientGroup.mk' (h.beta a).range k =
        QuotientGroup.mk' (h.beta a).range k * QuotientGroup.mk' (h.beta a).range q := by
    intro L hL q hq k hk
    obtain ⟨zL, hzL⟩ := h.exists_uniqueInvolution hL
    obtain ⟨J, hp⟩ := h.exists_partner hL
    obtain ⟨zJ, hzJ⟩ := h.exists_uniqueInvolution hp.2.1
    have hzJL : zL = zJ := h.inv_eq hp hzL hzJ
    have hqn : conjSub q (L ⊔ pCore 2 G) ≤ L ⊔ pCore 2 G := by
      intro x hx
      rw [mem_conjSub_iff, A5Q.mem_sup_pCore_iff] at hx
      rw [A5Q.mem_sup_pCore_iff]
      have hq1 : QuotientGroup.mk' (pCore 2 G) q = 1 := (QuotientGroup.eq_one_iff q).mpr hq
      have e : QuotientGroup.mk' (pCore 2 G) x = QuotientGroup.mk' (pCore 2 G) (q⁻¹ * x * q) := by
        simp [map_mul, map_inv, hq1]
      rw [e]
      exact hx
    obtain ⟨q', hq'Q, hq'B, hq'N⟩ : ∃ q' ∈ pCore 2 G, q'⁻¹ * q ∈ (h.beta a).range ∧
        conjSub q' L = L := by
      rcases h.conj_cases_of_normalizes_sup hp hqn with ⟨h1, -⟩ | ⟨h1, h2⟩
      · exact ⟨q, hq, by rw [inv_mul_cancel]; exact one_mem _, h1⟩
      · obtain ⟨γ, hγ, -⟩ := h.existsUnique_over a hL
        obtain ⟨δ, hδ⟩ := exists_ne γ
        obtain ⟨M, hM, hMδ, hMz⟩ := h.w_spec a δ
        have hwγ : h.w a γ = zL := h.w_eq a hL hγ hzL
        have hML : M ≠ L := by
          rintro rfl
          exact h.w_ne a δ γ hδ ((hMz.eq hzL).trans hwγ.symm)
        have hMJ : M ≠ J := by
          rintro rfl
          exact h.w_ne a δ γ hδ ((hMz.eq hzJ).trans (hzJL.symm.trans hwγ.symm))
        have hs : conjSub (h.w a δ) L = J := h.swap hp hM hML hMJ hMz
        refine ⟨q * h.w a δ, (pCore 2 G).mul_mem hq (h.w_mem_pCore a δ), ?_, ?_⟩
        · have e : (q * h.w a δ)⁻¹ * q = (h.w a δ)⁻¹ := by group
          rw [e]
          exact inv_mem (hwB δ)
        · rw [conjSub_mul, hs, h2]
    have hq'norm : q' ∈ Subgroup.normalizer (L : Set G) := A5Q.mem_normalizer_of_conjSub_eq hq'N
    have hcj := h.conj_eq_or_of_mem_pCore hL hzL hq'Q hq'norm k hk
    have hπz : QuotientGroup.mk' (h.beta a).range zL = 1 :=
      (QuotientGroup.eq_one_iff zL).mpr (hzB hL hzL)
    have h1 : QuotientGroup.mk' (h.beta a).range q' * QuotientGroup.mk' (h.beta a).range k =
        QuotientGroup.mk' (h.beta a).range k * QuotientGroup.mk' (h.beta a).range q' := by
      rcases hcj with h2 | h2
      · have := congrArg (QuotientGroup.mk' (h.beta a).range) h2
        simp only [map_mul, map_inv] at this
        exact mul_inv_eq_iff_eq_mul.mp this
      · have := congrArg (QuotientGroup.mk' (h.beta a).range) h2
        simp only [map_mul, map_inv, hπz, mul_one] at this
        exact mul_inv_eq_iff_eq_mul.mp this
    have hqq : QuotientGroup.mk' (h.beta a).range q = QuotientGroup.mk' (h.beta a).range q' :=
      (QuotientGroup.eq.mpr hq'B).symm
    rw [hqq]
    exact h1
  have hcent : ∀ g : G, ∀ q ∈ pCore 2 G,
      QuotientGroup.mk' (h.beta a).range g * QuotientGroup.mk' (h.beta a).range q =
        QuotientGroup.mk' (h.beta a).range q * QuotientGroup.mk' (h.beta a).range g := by
    intro g q hq
    let C : Subgroup G := (Subgroup.centralizer
      ({QuotientGroup.mk' (h.beta a).range q} : Set (G ⧸ (h.beta a).range))).comap
        (QuotientGroup.mk' (h.beta a).range)
    have hC : pSpan Ω ≤ C := by
      refine pSpan_le fun L hL k hk => ?_
      show QuotientGroup.mk' (h.beta a).range k ∈ Subgroup.centralizer _
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      rw [Set.mem_singleton_iff] at hu
      rw [hu]
      exact hmem L hL q hq k hk
    have hg : g ∈ C := hC (by rw [h.thmD.gen]; trivial)
    exact (Subgroup.mem_centralizer_iff.mp hg (QuotientGroup.mk' (h.beta a).range q)
      (Set.mem_singleton _)).symm
  have hperf : (⊤ : Subgroup G) ≤ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ := by
    refine h.thmD.gen.symm.le.trans (pSpan_le fun L hL => ?_)
    obtain ⟨y, -, -, hy⟩ := h.exists_three a hL
    rw [← hy]
    exact Subgroup.commutator_mono le_top le_top
  obtain ⟨K, J0, hp0⟩ := h.exists_paired
  have hK : K ∈ Ω := hp0.1
  obtain ⟨S, hS⟩ := h.exists_sylow_eq_sup_pCore a hK
  obtain ⟨z, hz⟩ := h.exists_uniqueInvolution hK
  have hXQ : pCore 2 G ⊓ K ≤ (h.beta a).range := by
    rintro x ⟨hxQ, hxK⟩
    rcases h.member_inf_pCore_cases hK hz hxK hxQ with rfl | rfl
    · exact one_mem _
    · exact hzB hK hz
  exact A5Q.le_of_central_quotient (B := (h.beta a).range) (Q := pCore 2 G) (X := K)
    (h.range_beta_le a) (CFSG.pCore_isPGroup (p := 2) (G := G)) hcent hperf S
    (by rw [hS]; exact le_sup_left) hXQ (by rw [hS, sup_comm])

theorem card_pCore : Nat.card (pCore 2 G) = 16 := by
  rw [← h.range_beta_eq a]
  have h1 : Nat.card (h.beta a).range * Nat.card (h.beta a).ker =
      Nat.card (Multiplicative (Fin 5 → ZMod 2)) := by
    rw [← Subgroup.index_ker]
    exact Subgroup.index_mul_card _
  have hV : Nat.card (Multiplicative (Fin 5 → ZMod 2)) = 32 := by
    rw [Nat.card_eq_fintype_card]
    simp [Fintype.card_pi]
  have hker : Nat.card (h.beta a).ker = 2 := by
    have hset : ((h.beta a).ker : Set (Multiplicative (Fin 5 → ZMod 2))) =
        {1, Multiplicative.ofAdd (fun _ => (1 : ZMod 2))} := by
      ext f
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_insert_iff, Set.mem_singleton_iff]
      rw [h.beta_eq_one_iff a f]
      constructor
      · rintro (h0 | h1)
        · left; exact Multiplicative.toAdd.injective (by rw [h0]; rfl)
        · right; exact Multiplicative.toAdd.injective (by rw [h1]; rfl)
      · rintro (h0 | h1)
        · left; rw [h0]; rfl
        · right; rw [h1]; rfl
    have hcard : Nat.card (h.beta a).ker =
        ((h.beta a).ker : Set (Multiplicative (Fin 5 → ZMod 2))).ncard :=
      Nat.card_coe_set_eq _
    rw [hcard, hset]
    apply Set.ncard_pair
    intro h1
    have := congrArg (fun x : Multiplicative (Fin 5 → ZMod 2) => Multiplicative.toAdd x 0) h1
    simp at this
  rw [hV, hker] at h1
  omega

theorem exists_complement : ∃ H : Subgroup G, (pCore 2 G).IsComplement' H := by
  classical
  have hQn : (pCore 2 G).Normal := CFSG.pCore_normal
  haveI hQc : IsMulCommutative (pCore 2 G) := by
    refine ⟨⟨fun x y => ?_⟩⟩
    have hx : x.1 ∈ (h.beta a).range := by rw [h.range_beta_eq a]; exact x.2
    have hy : y.1 ∈ (h.beta a).range := by rw [h.range_beta_eq a]; exact y.2
    obtain ⟨f, hf⟩ := hx
    obtain ⟨g, hg⟩ := hy
    apply Subtype.ext
    show x.1 * y.1 = y.1 * x.1
    rw [← hf, ← hg, ← map_mul, ← map_mul, mul_comm]
  obtain ⟨K, J, hp⟩ := h.exists_paired
  have hK : K ∈ Ω := hp.1
  obtain ⟨z, hz⟩ := h.exists_uniqueInvolution hp.1
  obtain ⟨z', hz'⟩ := h.exists_uniqueInvolution hp.2.1
  have hzz : z = z' := h.inv_eq hp hz hz'
  subst hzz
  obtain ⟨L, hL, hLK, hLJ⟩ := h.exists_third hp
  obtain ⟨t, ht⟩ := h.exists_uniqueInvolution hL
  have hs : conjSub t K = J := h.swap hp hL hLK hLJ ht
  have htQ : t ∈ pCore 2 G := h.mem_pCore hL ht
  have htz : t * z * t⁻¹ = z := by
    have h1 := hz.conj t
    rw [hs] at h1
    exact (hz'.eq h1).symm
  obtain ⟨i, hi, j, hj, hij⟩ := h.nonabelian hp.1
  obtain ⟨hi1, hj1, hne, hi2, hj2, hcomm, hbar⟩ := h.member_bar_gen hK hi hj hij
  set π : G →* G ⧸ pCore 2 G := QuotientGroup.mk' (pCore 2 G) with hπ
  have hπt : π t = 1 := (QuotientGroup.eq_one_iff t).mpr htQ
  obtain ⟨ib, hib⟩ : ∃ x : G ⧸ pCore 2 G, π i = x := ⟨_, rfl⟩
  obtain ⟨jb, hjb⟩ : ∃ x : G ⧸ pCore 2 G, π j = x := ⟨_, rfl⟩
  rw [hib] at hi1 hne hi2 hcomm hbar
  rw [hjb] at hj1 hne hj2 hcomm hbar
  obtain ⟨i', hi'⟩ : ∃ x : G, x = t * i * t⁻¹ := ⟨_, rfl⟩
  obtain ⟨j', hj'⟩ : ∃ x : G, x = t * j * t⁻¹ := ⟨_, rfl⟩
  have hi'J : i' ∈ J := by rw [hi', ← hs]; exact conj_mem_conjSub hi
  have hj'J : j' ∈ J := by rw [hj', ← hs]; exact conj_mem_conjSub hj
  have hπi' : π i' = ib := by
    rw [hi', map_mul, map_mul, map_inv, hπt, one_mul, inv_one, mul_one, hib]
  have hπj' : π j' = jb := by
    rw [hj', map_mul, map_mul, map_inv, hπt, one_mul, inv_one, mul_one, hjb]
  have hz2 : z * z = 1 := hz.sq
  have hzi : i * z = z * i := A5Q.uniqueInvolution_comm hz hi
  have hzj : j * z = z * j := A5Q.uniqueInvolution_comm hz hj
  have hzi' : i' * z = z * i' := A5Q.uniqueInvolution_comm hz' hi'J
  have hii : i * i = z := h.member_sq_eq hK hz hi hj hij
  have hjj : j * j = z := h.member_sq_eq hK hz hj hi (Ne.symm hij)
  have hrel : j * i = z * (i * j) := h.member_comm_eq hK hz hi hj hij
  have hii' : i' * i' = z := by
    calc i' * i' = t * (i * i) * t⁻¹ := by rw [hi']; group
      _ = z := by rw [hii, htz]
  have hjj' : j' * j' = z := by
    calc j' * j' = t * (j * j) * t⁻¹ := by rw [hj']; group
      _ = z := by rw [hjj, htz]
  have hrel' : j' * i' = z * (i' * j') := by
    calc j' * i' = t * (j * i) * t⁻¹ := by rw [hi', hj']; group
      _ = t * (z * (i * j)) * t⁻¹ := by rw [hrel]
      _ = (t * z * t⁻¹) * (t * i * t⁻¹ * (t * j * t⁻¹)) := by group
      _ = z * (i' * j') := by rw [htz, hi', hj']
  have hci : i' * i = i * i' := (hp.2.2.2 i hi i' hi'J).symm
  have hcj : j' * i = i * j' := (hp.2.2.2 i hi j' hj'J).symm
  have hdi : i' * j = j * i' := (hp.2.2.2 j hj i' hi'J).symm
  have hdj : j' * j = j * j' := (hp.2.2.2 j hj j' hj'J).symm
  obtain ⟨e1, e2, e3⟩ := A5Q.klein_lift hz2 hzi hzj hzi' hii hjj hii' hjj' hrel hrel' hci hcj
    hdi hdj
  set X : Subgroup G := Subgroup.closure ({i * j', j * (i' * j')} : Set G) with hX
  have hx₁X : i * j' ∈ X := Subgroup.subset_closure (Set.mem_insert _ _)
  have hx₂X : j * (i' * j') ∈ X :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hJle : J ≤ K ⊔ pCore 2 G := h.le_sup_pCore hp
  have hXS : X ≤ K ⊔ pCore 2 G := by
    rw [hX, Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | hg
    · exact (K ⊔ pCore 2 G).mul_mem (Subgroup.mem_sup_left hi) (hJle hj'J)
    · rw [Set.mem_singleton_iff] at hg
      rw [hg]
      exact (K ⊔ pCore 2 G).mul_mem (Subgroup.mem_sup_left hj)
        ((K ⊔ pCore 2 G).mul_mem (hJle hi'J) (hJle hj'J))
  have hπx₁ : π (i * j') = ib * jb := by rw [map_mul, hπj', hib]
  have hπx₂ : π (j * (i' * j')) = ib := by
    rw [map_mul, map_mul, hπi', hπj', hjb]
    calc jb * (ib * jb) = ib * (jb * jb) := by rw [← mul_assoc, ← hcomm, mul_assoc]
      _ = ib := by rw [hj2, mul_one]
  have hπx₁₂ : π (i * j' * (j * (i' * j'))) = jb := by
    rw [map_mul, hπx₁, hπx₂]
    calc ib * jb * ib = ib * (jb * ib) := mul_assoc _ _ _
      _ = (ib * ib) * jb := by rw [← hcomm, ← mul_assoc]
      _ = jb := by rw [hi2, one_mul]
  have hinf : pCore 2 G ⊓ X = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgQ, hgX⟩
    have hmem := (A5Q.mem_closure_pair_iff e1 e2 e3 g).mp hgX
    rw [Subgroup.mem_bot]
    have hπg : π g = 1 := (QuotientGroup.eq_one_iff g).mpr hgQ
    rcases hmem with h1 | h1 | h1 | h1
    · exact h1
    · exfalso
      rw [h1, hπx₁] at hπg
      apply hne
      rw [eq_inv_of_mul_eq_one_left hπg]
      exact inv_eq_of_mul_eq_one_right hj2
    · exfalso
      rw [h1, hπx₂] at hπg
      exact hi1 hπg
    · exfalso
      rw [h1, hπx₁₂] at hπg
      exact hj1 hπg
  have hsup : pCore 2 G ⊔ X = K ⊔ pCore 2 G := by
    apply le_antisymm
    · exact sup_le le_sup_right hXS
    · refine sup_le ?_ le_sup_left
      intro k hk
      have hk' : π k ∈ Subgroup.closure ({ib, jb} : Set (G ⧸ pCore 2 G)) := by
        rw [← hbar]
        exact Subgroup.mem_map_of_mem _ hk
      have hbX : Subgroup.closure ({ib, jb} : Set (G ⧸ pCore 2 G)) ≤ X.map π := by
        rw [Subgroup.closure_le]
        intro s hs
        rcases hs with rfl | hs
        · exact ⟨_, hx₂X, hπx₂⟩
        · rw [Set.mem_singleton_iff] at hs
          rw [hs]
          exact ⟨_, X.mul_mem hx₁X hx₂X, hπx₁₂⟩
      obtain ⟨x, hxX, hxk⟩ := hbX hk'
      have h1 : x⁻¹ * k ∈ pCore 2 G := QuotientGroup.eq.mp hxk
      have h2 : k = x * (x⁻¹ * k) := by group
      rw [h2]
      exact (pCore 2 G ⊔ X).mul_mem (Subgroup.mem_sup_right hxX) (Subgroup.mem_sup_left h1)
  obtain ⟨S, hS⟩ := h.exists_sylow_eq_sup_pCore a hK
  obtain ⟨H, hH1, hH2⟩ := (CFSG.Quasithin.gaschutz (CFSG.pCore_isPGroup (p := 2) (G := G))
    S).mpr ⟨X, by rw [hS]; exact hXS, hinf, by rw [hS, hsup]⟩
  refine ⟨H, Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hH1) ?_⟩
  rw [← Subgroup.normal_mul, hH2, Subgroup.coe_top]

end E4Hyp

end CFSG.ClassicalInvolution.Q3.Sec13
