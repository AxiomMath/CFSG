module

public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverRoots

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearCover

open Subgroup
open scoped commutatorElement

section Identities

variable {G : Type*} [Group G]

theorem exists_fin_ne_four {n : ℕ} (hn : 5 ≤ n) (i j k l : Fin n) :
    ∃ m : Fin n, m ≠ i ∧ m ≠ j ∧ m ≠ k ∧ m ≠ l := by
  classical
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ {i, j, k, l} := fun m _ => by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases hi : m = i
    · exact Or.inl hi
    by_cases hj : m = j
    · exact Or.inr (Or.inl hj)
    by_cases hk : m = k
    · exact Or.inr (Or.inr (Or.inl hk))
    exact Or.inr (Or.inr (Or.inr (h m hi hj hk)))
  have h4 := (Finset.card_le_card hsub).trans Finset.card_le_four
  rw [Finset.card_univ, Fintype.card_fin] at h4
  omega

theorem conj_commutatorElement_eq (g p q : G) :
    g * ⁅p, q⁆ * g⁻¹ = ⁅g * p * g⁻¹, g * q * g⁻¹⁆ := by
  simp only [commutatorElement_def]
  group

theorem commutatorElement_commutatorElement_right_of_commute {a b c : G} (hac : a * c = c * a) :
    ⁅a, ⁅b, c⁆⁆ = ⁅a, b⁆ * ⁅b, c⁆ * ⁅a, b⁆⁻¹ * ⁅⁅a, b⁆, c⁆ * ⁅b, c⁆⁻¹ := by
  have h1 : c⁻¹ * a⁻¹ * c = a⁻¹ := by
    rw [← mul_inv_rev, hac, mul_inv_rev, inv_mul_cancel_right]
  have h2 : a⁻¹ * c * a = c := by
    rw [mul_assoc, ← hac, inv_mul_cancel_left]
  calc ⁅a, ⁅b, c⁆⁆ = a * b * c * b⁻¹ * (c⁻¹ * a⁻¹ * c) * b * c⁻¹ * b⁻¹ := by
        simp only [commutatorElement_def]
        group
    _ = a * b * (a⁻¹ * c * a) * b⁻¹ * a⁻¹ * b * c⁻¹ * b⁻¹ := by rw [h1, h2]
    _ = ⁅a, b⁆ * ⁅b, c⁆ * ⁅a, b⁆⁻¹ * ⁅⁅a, b⁆, c⁆ * ⁅b, c⁆⁻¹ := by
        simp only [commutatorElement_def]
        group

end Identities

section Counting

variable {E : Type*} [Group E]

theorem card_closure_insert_le [Finite E] {X : Set E} {y : E} (hy : y * y = 1)
    (hnorm : ∀ g ∈ X, y * g * y⁻¹ ∈ closure X) :
    Nat.card (closure (insert y X)) ≤ 2 * Nat.card (closure X) := by
  set H := closure X
  have hyH : ∀ h ∈ H, y * h * y⁻¹ ∈ H := by
    intro h hh
    induction hh using closure_induction with
    | mem g hg => exact hnorm g hg
    | one => rw [mul_one, mul_inv_cancel]; exact H.one_mem
    | mul a b _ _ ha hb =>
      rw [show y * (a * b) * y⁻¹ = y * a * y⁻¹ * (y * b * y⁻¹) by group]
      exact H.mul_mem ha hb
    | inv a _ ha =>
      rw [show y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ by group]
      exact H.inv_mem ha
  let L : Subgroup E :=
    { carrier := {g | g ∈ H ∨ y * g ∈ H}
      one_mem' := Or.inl H.one_mem
      mul_mem' := by
        rintro g g' (hg | hg) (hg' | hg')
        · exact Or.inl (H.mul_mem hg hg')
        · right
          rw [show y * (g * g') = y * g * y⁻¹ * (y * g') by group]
          exact H.mul_mem (hyH g hg) hg'
        · right
          rw [← mul_assoc]
          exact H.mul_mem hg hg'
        · left
          have h := H.mul_mem (hyH _ hg) hg'
          rwa [show y * (y * g) * y⁻¹ * (y * g') = y * y * (g * g') by group, hy,
            one_mul] at h
      inv_mem' := by
        rintro g (hg | hg)
        · exact Or.inl (H.inv_mem hg)
        · right
          have h := hyH _ (H.inv_mem hg)
          rwa [show y * (y * g)⁻¹ * y⁻¹ = y * g⁻¹ * (y * y)⁻¹ by group, hy, inv_one,
            mul_one] at h }
  have hle : closure (insert y X) ≤ L := by
    rw [closure_le]
    rintro g (rfl | hg)
    · exact Or.inr (by rw [hy]; exact H.one_mem)
    · exact Or.inl (subset_closure hg)
  let f : H ⊕ H → L := fun s => match s with
    | Sum.inl h => ⟨h, Or.inl h.2⟩
    | Sum.inr h => ⟨y * h, Or.inr (by rw [← mul_assoc, hy, one_mul]; exact h.2)⟩
  have hf : Function.Surjective f := by
    rintro ⟨g, hg | hg⟩
    · exact ⟨Sum.inl ⟨g, hg⟩, rfl⟩
    · refine ⟨Sum.inr ⟨y * g, hg⟩, Subtype.ext ?_⟩
      change y * (y * g) = g
      rw [← mul_assoc, hy, one_mul]
  calc Nat.card (closure (insert y X)) ≤ Nat.card L := Subgroup.card_le_of_le hle
    _ ≤ Nat.card (H ⊕ H) := Nat.card_le_card_of_surjective f hf
    _ = 2 * Nat.card H := by rw [Nat.card_sum, two_mul]

theorem card_closure_le_of_roots [Finite E] {n : ℕ} (y : Fin n → Fin n → E)
    (hy2 : ∀ i j, i < j → y i j * y i j = 1)
    (hyc : ∀ i j k l, i < j → k < l → j ≠ k → i ≠ l → y i j * y k l = y k l * y i j)
    (hy3 : ∀ i j l, i < j → j < l → ⁅y i j, y j l⁆ = y i l) :
    Nat.card (closure {g | ∃ i j, i < j ∧ y i j = g}) ≤ 2 ^ (n * (n - 1) / 2) := by
  classical
  set f : Fin n × Fin n → E := fun r => y r.1 r.2
  have key : ∀ T : Finset (Fin n × Fin n), (∀ r ∈ T, r.1 < r.2) →
      (∀ i j l, (i, j) ∈ T → (j, l) ∈ T → (i, l) ∈ T) →
      Nat.card (closure (f '' (T : Set (Fin n × Fin n)))) ≤ 2 ^ T.card := by
    intro T
    induction T using Finset.induction_on_min_value (fun r : Fin n × Fin n => r.2) with
    | empty =>
      intro _ _
      simp
    | insert a s has hmin ih =>
      intro hpos hcl
      obtain ⟨i₀, j₀⟩ := a
      have ha : i₀ < j₀ := hpos _ (Finset.mem_insert_self _ _)
      have hpos_s : ∀ r ∈ s, r.1 < r.2 := fun r hr => hpos r (Finset.mem_insert_of_mem hr)
      have hcl_s : ∀ i j l, (i, j) ∈ s → (j, l) ∈ s → (i, l) ∈ s := by
        intro i j l hij hjl
        rcases Finset.mem_insert.mp (hcl i j l (Finset.mem_insert_of_mem hij)
          (Finset.mem_insert_of_mem hjl)) with h | h
        · have h1 : j₀ ≤ j := hmin _ hij
          have h2 : j < l := hpos_s _ hjl
          rw [Prod.mk.injEq] at h
          exact absurd (h.2 ▸ h2) (not_lt.mpr h1)
        · exact h
      have ih' := ih hpos_s hcl_s
      rw [Finset.coe_insert, Set.image_insert_eq, Finset.card_insert_of_notMem has, pow_succ']
      refine (card_closure_insert_le (hy2 i₀ j₀ ha) ?_).trans ?_
      · rintro _ ⟨⟨i, j⟩, hr, rfl⟩
        have hij : i < j := hpos_s _ hr
        have hj : j₀ ≤ j := hmin _ hr
        by_cases hi : i = j₀
        · rw [hi] at hr hij
          have hmem : (i₀, j) ∈ s := by
            rcases Finset.mem_insert.mp (hcl i₀ j₀ j (Finset.mem_insert_self _ _)
              (Finset.mem_insert_of_mem hr)) with h | h
            · rw [Prod.mk.injEq] at h
              exact absurd h.2 hij.ne'
            · exact h
          change y i₀ j₀ * y i j * (y i₀ j₀)⁻¹ ∈ _
          rw [hi, show y i₀ j₀ * y j₀ j * (y i₀ j₀)⁻¹ = ⁅y i₀ j₀, y j₀ j⁆ * y j₀ j by
            simp only [commutatorElement_def]; group, hy3 i₀ j₀ j ha hij]
          exact mul_mem (subset_closure ⟨_, hmem, rfl⟩) (subset_closure ⟨_, hr, rfl⟩)
        · change y i₀ j₀ * y i j * (y i₀ j₀)⁻¹ ∈ _
          rw [hyc i₀ j₀ i j ha hij (Ne.symm hi) (ha.trans_le hj).ne, mul_inv_cancel_right]
          exact subset_closure ⟨_, hr, rfl⟩
      · exact Nat.mul_le_mul_left 2 ih'
  set T : Finset (Fin n × Fin n) := Finset.univ.filter fun r => r.1 < r.2 with hTdef
  have hT := key T (fun r hr => (Finset.mem_filter.mp hr).2) (fun i j l hij hjl =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp hij).2.trans (Finset.mem_filter.mp hjl).2⟩)
  have hset : f '' (T : Set (Fin n × Fin n)) = {g | ∃ i j, i < j ∧ y i j = g} := by
    ext g
    constructor
    · rintro ⟨⟨i, j⟩, hr, rfl⟩
      exact ⟨i, j, (Finset.mem_filter.mp (Finset.mem_coe.mp hr)).2, rfl⟩
    · rintro ⟨i, j, hij, rfl⟩
      exact ⟨(i, j), Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩), rfl⟩
  rw [hset, hTdef, Fintype.card_product_filter_lt, Fintype.card_fin, Nat.choose_two_right] at hT
  exact hT

end Counting

structure TypeARoots (G : Type*) [Group G] (n : ℕ) where
  x : Fin n → Fin n → G
  mul_self : ∀ i j, i ≠ j → x i j * x i j = 1
  comm : ∀ i j k l, i ≠ j → k ≠ l → j ≠ k → i ≠ l → x i j * x k l = x k l * x i j
  commutator : ∀ i j l, i ≠ j → j ≠ l → i ≠ l → ⁅x i j, x j l⁆ = x i l

namespace TypeARoots

variable {G E : Type*} [Group G] [Group E] {n : ℕ} (R : TypeARoots G n) (η : E →* G)
  (hker : ∀ z, η z = 1 → z ∈ center E) (hη : Function.Surjective η)

include hker hη

theorem lift_mul_comm (hn : 5 ≤ n) {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k)
    (hil : i ≠ l) {a c : E} (ha : η a = R.x i j) (hc : η c = R.x k l) : a * c = c * a := by
  obtain ⟨m, hmi, hmj, hmk, hml⟩ := exists_fin_ne_four hn i j k l
  obtain ⟨p, hp⟩ := hη (R.x k m)
  obtain ⟨q, hq⟩ := hη (R.x m l)
  have h1 : η (a * p * a⁻¹) = η p := by
    rw [map_mul, map_mul, map_inv, ha, hp, R.comm i j k m hij hmk.symm hjk hmi.symm,
      mul_inv_cancel_right]
  have h2 : η (a * q * a⁻¹) = η q := by
    rw [map_mul, map_mul, map_inv, ha, hq, R.comm i j m l hij hml hmj.symm hil,
      mul_inv_cancel_right]
  have h3 : a * ⁅p, q⁆ = ⁅p, q⁆ * a := by
    have h := conj_commutatorElement_eq a p q
    rw [HeisenbergRoots.commutatorElement_eq_of_map_eq η hker h1 h2] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  have hz : ⁅p, q⁆⁻¹ * c ∈ center E := hker _ (by
    rw [map_mul, map_inv, map_commutatorElement, hp, hq, R.commutator k m l hmk.symm hml hkl,
      hc, inv_mul_cancel])
  calc a * c = a * ⁅p, q⁆ * (⁅p, q⁆⁻¹ * c) := by group
    _ = ⁅p, q⁆ * (a * (⁅p, q⁆⁻¹ * c)) := by rw [h3, mul_assoc]
    _ = ⁅p, q⁆ * ((⁅p, q⁆⁻¹ * c) * a) := by rw [mem_center_iff.mp hz a]
    _ = c * a := by group

theorem commutatorElement_lift_mul_self (hn : 5 ≤ n) {i j k : Fin n} (hik : i ≠ k) (hkj : k ≠ j)
    (hij : i ≠ j) {p q : E} (hp : η p = R.x i k) (hq : η q = R.x k j) :
    ⁅p, q⁆ * ⁅p, q⁆ = 1 := by
  have hp2 : p * p ∈ center E := hker _ (by rw [map_mul, hp, R.mul_self i k hik])
  have hq2 : q * q ∈ center E := hker _ (by rw [map_mul, hq, R.mul_self k j hkj])
  have h := (commutatorElement_commutatorElement_eq_sq (mem_center_iff.mp hp2 q).symm
    (mem_center_iff.mp hq2 p).symm).1
  have hpq : η ⁅p, q⁆ = R.x i j := by
    rw [map_commutatorElement, hp, hq, R.commutator i k j hik hkj hij]
  have hc := R.lift_mul_comm η hker hη hn hij hik hij.symm hik hpq hp
  rw [commutatorElement_eq_one_iff_mul_comm.mpr hc, eq_comm, sq] at h
  exact h

theorem commutatorElement_lift_eq (hn : 5 ≤ n) {i j k l : Fin n} (hij : i ≠ j) (hik : i ≠ k)
    (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) {a b a' c : E}
    (ha : η a = R.x i k) (hb : η b = R.x k j) (ha' : η a' = R.x i l) (hc : η c = R.x l j) :
    ⁅a, b⁆ = ⁅a', c⁆ := by
  obtain ⟨b₀, hb₀⟩ := hη (R.x k l)
  have hu : η ⁅a, b₀⁆ = R.x i l := by
    rw [map_commutatorElement, ha, hb₀, R.commutator i k l hik hkl hil]
  have hv : η ⁅b₀, c⁆ = R.x k j := by
    rw [map_commutatorElement, hb₀, hc, R.commutator k l j hkl hjl.symm hjk.symm]
  have hX : η ⁅⁅a, b₀⁆, c⁆ = R.x i j := by
    rw [map_commutatorElement, hu, hc, R.commutator i l j hil hjl.symm hij]
  have hac : a * c = c * a := R.lift_mul_comm η hker hη hn hik hjl.symm hkl hij ha hc
  have huv : ⁅a, b₀⁆ * ⁅b₀, c⁆ = ⁅b₀, c⁆ * ⁅a, b₀⁆ :=
    R.lift_mul_comm η hker hη hn hil hjk.symm hkl.symm hij hu hv
  have hXv : ⁅⁅a, b₀⁆, c⁆ * ⁅b₀, c⁆ = ⁅b₀, c⁆ * ⁅⁅a, b₀⁆, c⁆ :=
    R.lift_mul_comm η hker hη hn hij hjk.symm hjk hij hX hv
  have hY : ⁅a, ⁅b₀, c⁆⁆ = ⁅⁅a, b₀⁆, c⁆ := by
    rw [commutatorElement_commutatorElement_right_of_commute hac, huv, mul_inv_cancel_right,
      ← hXv, mul_inv_cancel_right]
  calc ⁅a, b⁆ = ⁅a, ⁅b₀, c⁆⁆ :=
        HeisenbergRoots.commutatorElement_eq_of_map_eq η hker rfl (by rw [hb, hv])
    _ = ⁅⁅a, b₀⁆, c⁆ := hY
    _ = ⁅a', c⁆ := HeisenbergRoots.commutatorElement_eq_of_map_eq η hker (by rw [hu, ha']) rfl

omit hker hη

theorem ker_eq_bot (hn : 5 ≤ n) (S : Subgroup G) (hSyl : ∃ P : Sylow 2 G, (P : Subgroup G) = S)
    (hS : S ≤ closure {g | ∃ i j, i < j ∧ R.x i j = g})
    (hcard : 2 ^ (n * (n - 1) / 2) ≤ Nat.card S) [Finite E] [Group.IsPerfect E]
    (hη : Function.Surjective η) (hC : η.ker ≤ center E) (h2 : IsPGroup 2 η.ker) :
    η.ker = ⊥ := by
  classical
  have hker : ∀ z, η z = 1 → z ∈ center E := fun z hz => hC hz
  have comm_eq : ∀ {a a' b b' : E}, η a = η a' → η b = η b' → ⁅a, b⁆ = ⁅a', b'⁆ :=
    fun ha hb => HeisenbergRoots.commutatorElement_eq_of_map_eq η hker ha hb
  choose e he using fun i j => hη (R.x i j)
  choose t ht using fun i j : Fin n => Fin.exists_ne_and_ne_of_two_lt i j (by omega)
  obtain ⟨y, hydef⟩ : ∃ y : Fin n → Fin n → E, ∀ i j, y i j = ⁅e i (t i j), e (t i j) j⁆ :=
    ⟨_, fun _ _ => rfl⟩
  have hy : ∀ i j, i ≠ j → η (y i j) = R.x i j := fun i j hij => by
    rw [hydef, map_commutatorElement, he, he, R.commutator i (t i j) j (ht i j).1.symm (ht i j).2
      hij]
  have hy_eq : ∀ i j k, i ≠ j → i ≠ k → k ≠ j → ∀ a b, η a = R.x i k → η b = R.x k j →
      y i j = ⁅a, b⁆ := by
    intro i j k hij hik hkj a b ha hb
    rw [hydef]
    by_cases hk : t i j = k
    · exact comm_eq (by rw [he, ha, hk]) (by rw [he, hb, hk])
    · exact R.commutatorElement_lift_eq η hker hη hn hij (ht i j).1.symm hik (ht i j).2.symm
        hkj.symm hk (he _ _) (he _ _) ha hb
  have hy2 : ∀ i j, i ≠ j → y i j * y i j = 1 := fun i j hij => by
    rw [hydef]
    exact R.commutatorElement_lift_mul_self η hker hη hn (ht i j).1.symm (ht i j).2 hij
      (he _ _) (he _ _)
  have hcount := card_closure_le_of_roots y (fun i j h => hy2 i j h.ne)
    (fun i j k l hij hkl hjk hil =>
      R.lift_mul_comm η hker hη hn hij.ne hkl.ne hjk hil (hy i j hij.ne) (hy k l hkl.ne))
    (fun i j l hij hjl =>
      (hy_eq i l j (hij.trans hjl).ne hij.ne hjl.ne _ _ (hy i j hij.ne) (hy j l hjl.ne)).symm)
  set P₀ := closure {g | ∃ i j, i < j ∧ y i j = g}
  have hmap : P₀.map η = closure {g | ∃ i j, i < j ∧ R.x i j = g} := by
    rw [MonoidHom.map_closure]
    congr 1
    ext g
    constructor
    · rintro ⟨_, ⟨i, j, hij, rfl⟩, rfl⟩
      exact ⟨i, j, hij, (hy i j hij.ne).symm⟩
    · rintro ⟨i, j, hij, rfl⟩
      exact ⟨y i j, ⟨i, j, hij, rfl⟩, hy i j hij.ne⟩
  have hSP : S ≤ P₀.map η := hmap ▸ hS
  have : Finite (P₀.map η) := Finite.of_surjective _ (η.subgroupMap_surjective P₀)
  have hbij : Function.Bijective (η.subgroupMap P₀) := by
    refine (η.subgroupMap_surjective P₀).bijective_of_nat_card_le ?_
    calc Nat.card P₀ ≤ 2 ^ (n * (n - 1) / 2) := hcount
      _ ≤ Nat.card S := hcard
      _ ≤ Nat.card (P₀.map η) := Subgroup.card_le_of_le hSP
  have hinj : ∀ z ∈ P₀, η z = 1 → z = 1 := by
    intro z hz hz1
    have h : η.subgroupMap P₀ ⟨z, hz⟩ = η.subgroupMap P₀ 1 :=
      Subtype.ext (by rw [map_one]; exact hz1)
    exact congrArg Subtype.val (hbij.1 h)
  obtain ⟨SG, hSG⟩ := hSyl
  obtain ⟨P, hP, hzP⟩ := exists_sylow_map_eq_twoPart_le η hη hC SG
  have hlift : ∀ g ∈ (P : Subgroup E), ∃ p ∈ P₀, η p = η g := fun g hg => by
    have h1 : η g ∈ (P : Subgroup E).map η := mem_map_of_mem η hg
    rw [hP, hSG] at h1
    obtain ⟨p, hp, hpg⟩ := mem_map.mp (hSP h1)
    exact ⟨p, hp, hpg⟩
  have hPP : ⁅(P : Subgroup E), (P : Subgroup E)⁆ ≤ P₀ := by
    rw [commutator_le]
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨p₁, hp₁, h₁⟩ := hlift g₁ hg₁
    obtain ⟨p₂, hp₂, h₂⟩ := hlift g₂ hg₂
    rw [comm_eq h₁.symm h₂.symm, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hp₁ hp₂) (inv_mem hp₁)) (inv_mem hp₂)
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨k, hk⟩ := h2 ⟨z, hz⟩
  have hk' : z ^ 2 ^ k = 1 := congrArg Subtype.val hk
  exact mem_bot.mpr (hinj z (hPP (hzP z hz ⟨k, hk'⟩)) hz)

end TypeARoots

end LinearCover

end CFSG.LocalAnalysis.ComponentInitial
