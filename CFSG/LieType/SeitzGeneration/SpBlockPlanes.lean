module

public import CFSG.RankThree.PartOne.CTP.SeitzSpClosure

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.Assembly.LowTwoRank CFSG.RankThree.Classical CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.KCSpFull
open CFSG.Open
open CFSG.ClassicalInvolution.Models.SymplecticPairs (par par_par sgn form form_single_right
  form_eq_zero_of_supp ParClosed form_antisymm longBlock isSupp_longBlock coords mem_coords
  coords_subset_compl suppGroup suppGroup_mono commute_suppGroup_compl longBlock_injective
  IsSupp mem_suppGroup)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups

variable {r : ℕ} {K : Type} [Field K]

@[expose] def planeOf : Fin r ⊕ Fin r → Fin r := Sum.elim id id

@[simp] theorem planeOf_inl (i : Fin r) : planeOf (Sum.inl i : Fin r ⊕ Fin r) = i := rfl

@[simp] theorem planeOf_inr (i : Fin r) : planeOf (Sum.inr i : Fin r ⊕ Fin r) = i := rfl

@[simp] theorem planeOf_par (c : Fin r ⊕ Fin r) : planeOf (par c) = planeOf c := by
  cases c <;> rfl

@[expose] def planeSub (S : Set (Fin r)) : Submodule K (Fin r ⊕ Fin r → K) where
  carrier := {v | ∀ c, planeOf c ∉ S → v c = 0}
  add_mem' := fun {u v} hu hv c hc => by
    simp only [Pi.add_apply, hu c hc, hv c hc, add_zero]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun a v hv c hc => by simp only [Pi.smul_apply, hv c hc, smul_zero]

theorem planeSub_mono {S T : Set (Fin r)} (h : S ⊆ T) : planeSub (K := K) S ≤ planeSub T :=
  fun _ hv c hc => hv c fun hS => hc (h hS)

theorem spForm_eq_zero_of_disjoint {S T : Set (Fin r)} (hST : Disjoint S T)
    {u v : Fin r ⊕ Fin r → K} (hu : u ∈ planeSub S) (hv : v ∈ planeSub T) :
    spForm r K u v = 0 := by
  have hX : ParClosed {c : Fin r ⊕ Fin r | planeOf c ∉ S} := fun c hc => by
    simpa using hc
  rw [spForm_apply]
  exact form_eq_zero_of_supp hX (fun c hc => hu c hc) (fun c hc => by
    by_contra h0
    have hcS : planeOf c ∈ S := by simpa using hc
    exact hST.le_bot ⟨hcS, by by_contra hT; exact h0 (hv c hT)⟩)

theorem nondegenerate_planeSub (S : Set (Fin r)) :
    ((spForm r K).restrict (planeSub S)).Nondegenerate := by
  have hex : ∀ v ∈ planeSub S, v ≠ 0 → ∃ w ∈ planeSub S, spForm r K v w ≠ 0 := by
    intro v hv hv0
    obtain ⟨c, hc⟩ : ∃ c, v c ≠ 0 := by
      by_contra h
      push Not at h
      exact hv0 (funext h)
    have hcS : planeOf c ∈ S := by
      by_contra h
      exact hc (hv c h)
    refine ⟨Pi.single (par c) 1, fun d hd => ?_, ?_⟩
    · have : d ≠ par c := fun h => hd (by rw [h]; simpa using hcS)
      simp [this]
    · rw [spForm_apply]
      change form v (Pi.single (par c) 1) ≠ 0
      rw [form_single_right]
      simp only [par_par]
      rcases c with i | i <;> simp [sgn, hc]
  constructor
  · intro x hx
    by_contra hx0
    obtain ⟨w, hw, hw0⟩ := hex x x.2 (fun h => hx0 (Subtype.ext h))
    exact hw0 (hx ⟨w, hw⟩)
  · intro x hx
    by_contra hx0
    obtain ⟨w, hw, hw0⟩ := hex x x.2 (fun h => hx0 (Subtype.ext h))
    refine hw0 ?_
    have := hx ⟨w, hw⟩
    change spForm r K (w : Fin r ⊕ Fin r → K) x = 0 at this
    rw [spForm_apply] at this ⊢
    change form (x : Fin r ⊕ Fin r → K) w = 0
    rw [form_antisymm]
    change form w x = 0 at this
    rw [this, neg_zero]

theorem closure_centralizers_of_blocks {E : Subgroup (StatedSp r K)} {k₀ k₁ l : Fin r}
    (hk : k₀ ≠ k₁) (hl₀ : l ≠ k₀) (hl₁ : l ≠ k₁) {a b : StatedSp r K} (ha : a ∈ E) (hb : b ∈ E)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hfa : ∀ v ∈ planeSub (K := K) {i | i ≠ k₀}, spEnd a v = v)
    (hfb : ∀ v ∈ planeSub (K := K) {i | i ≠ k₁}, spEnd b v = v) :
    Subgroup.closure {g : StatedSp r K | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g} = ⊤ := by
  set H : Subgroup (StatedSp r K) :=
    Subgroup.closure {g : StatedSp r K | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g} with hH
  have hC₀ : ∀ v ∈ planeSub (K := K) {i | i ≠ k₀}, TransCenter H v := fun v hv t =>
    Subgroup.subset_closure ⟨a, ha, ha1, commute_spTransvection (hfa v hv) t⟩
  have hC₁ : ∀ v ∈ planeSub (K := K) {i | i ≠ k₁}, TransCenter H v := fun v hv t =>
    Subgroup.subset_closure ⟨b, hb, hb1, commute_spTransvection (hfb v hv) t⟩
  let S : Fin 3 → Set (Fin r) := ![{k₀}, {k₁}, {i | i ≠ k₀ ∧ i ≠ k₁}]
  let Vs : Fin 3 → Submodule K (Fin r ⊕ Fin r → K) := fun i => planeSub (S i)
  have hdisj : ∀ i j : Fin 3, i ≠ j → Disjoint (S i) (S j) := by
    intro i j hij
    rw [Set.disjoint_left]
    fin_cases i <;> fin_cases j <;> simp only [S] <;>
      first
        | exact absurd rfl hij
        | (intro x hx hx'; simp_all)
  have hsubset0 : planeSub (K := K) {k₀} ≤ planeSub {i | i ≠ k₁} :=
    planeSub_mono fun x hx => by simp only [Set.mem_singleton_iff] at hx; simp [hx, hk]
  have hsubset1 : planeSub (K := K) {k₁} ≤ planeSub {i | i ≠ k₀} :=
    planeSub_mono fun x hx => by simp only [Set.mem_singleton_iff] at hx; simp [hx, hk.symm]
  have hsubset2a : planeSub (K := K) {i | i ≠ k₀ ∧ i ≠ k₁} ≤ planeSub {i | i ≠ k₀} :=
    planeSub_mono fun x hx => hx.1
  have hsubset2b : planeSub (K := K) {i | i ≠ k₀ ∧ i ≠ k₁} ≤ planeSub {i | i ≠ k₁} :=
    planeSub_mono fun x hx => hx.2
  have hmix : ∀ y₁ ∈ planeSub (K := K) {k₀}, ∀ y₂ ∈ planeSub (K := K) {k₁}, y₂ ≠ 0 →
      TransCenter H (y₁ + y₂) := by
    intro y₁ hy₁ y₂ hy₂ hy₂0
    set u : Fin r ⊕ Fin r → K := Pi.single (Sum.inl l) 1 with hu
    set w : Fin r ⊕ Fin r → K := Pi.single (Sum.inr l) 1 with hw
    have hul : u ∈ planeSub (K := K) {l} := fun c hc => by
      have : c ≠ Sum.inl l := fun h => hc (by simp [h])
      simp [hu, this]
    have hwl : w ∈ planeSub (K := K) {l} := fun c hc => by
      have : c ≠ Sum.inr l := fun h => hc (by simp [h])
      simp [hw, this]
    have huw : spForm r K u w ≠ 0 := by
      rw [spForm_apply]
      change form u (Pi.single (Sum.inr l) 1) ≠ 0
      rw [form_single_right]
      simp [hu, sgn]
    have h01 : spForm r K y₁ y₂ = 0 := spForm_eq_zero_of_disjoint (by simpa using hk) hy₁ hy₂
    have h1w : spForm r K y₁ w = 0 :=
      spForm_eq_zero_of_disjoint (by simpa using hl₀.symm) hy₁ hwl
    have hu2 : spForm r K u y₂ = 0 :=
      spForm_eq_zero_of_disjoint (by simpa using hl₁) hul hy₂
    have hx : y₁ + u ∈ planeSub (K := K) {i | i ≠ k₁} :=
      Submodule.add_mem _ (hsubset0 hy₁) (planeSub_mono (fun x hx => by
        simp only [Set.mem_singleton_iff] at hx; simp [hx, hl₁]) hul)
    have hy : y₂ + w ∈ planeSub (K := K) {i | i ≠ k₀} :=
      Submodule.add_mem _ (hsubset1 hy₂) (planeSub_mono (fun x hx => by
        simp only [Set.mem_singleton_iff] at hx; simp [hx, hl₀]) hwl)
    have hB : spForm r K (y₁ + u) (y₂ + w) ≠ 0 := by
      simp only [map_add, LinearMap.add_apply, h01, h1w, hu2, zero_add]
      exact huw
    have hsum : TransCenter H ((y₁ + u) + (y₂ + w)) := (hC₁ _ hx).add (hC₀ _ hy) hB
    have hYmem : y₂ + u + w ∈ planeSub (K := K) {i | i ≠ k₀} :=
      Submodule.add_mem _ (Submodule.add_mem _ (hsubset1 hy₂) (planeSub_mono (fun x hx => by
        simp only [Set.mem_singleton_iff] at hx; simp [hx, hl₀]) hul))
        (planeSub_mono (fun x hx => by
          simp only [Set.mem_singleton_iff] at hx; simp [hx, hl₀]) hwl)
    have hY0 : y₂ + u + w ≠ 0 := by
      intro h0
      have := congrFun h0 (Sum.inl l)
      have h2 : y₂ (Sum.inl l) = 0 := hy₂ _ (by simpa using hl₁)
      simp [hu, hw, h2] at this
    obtain ⟨g, hgH, hgY, hgfix⟩ := exists_mem_fixing_eq (U := planeSub {i | i ≠ k₀})
      (nondegenerate_planeSub _) hC₀ hYmem (hsubset1 hy₂) hY0 hy₂0
    have hg1 : spEnd g y₁ = y₁ := hgfix y₁ fun c hc =>
      spForm_eq_zero_of_disjoint (by
        rw [Set.disjoint_left]; intro x hx hx'; simp_all) hy₁ hc
    have hmap := hsum.map hgH
    have heq : spEnd g ((y₁ + u) + (y₂ + w)) = y₁ + y₂ := by
      have : (y₁ + u) + (y₂ + w) = y₁ + (y₂ + u + w) := by abel
      rw [this, map_add, hg1, hgY]
    rwa [heq] at hmap
  have hspan : ⨆ i, Vs i = ⊤ := by
    rw [eq_top_iff]
    intro v _
    let v₀ : Fin r ⊕ Fin r → K := fun c => if planeOf c = k₀ then v c else 0
    let v₁ : Fin r ⊕ Fin r → K := fun c => if planeOf c = k₁ then v c else 0
    let v₂ : Fin r ⊕ Fin r → K := fun c => if planeOf c ≠ k₀ ∧ planeOf c ≠ k₁ then v c else 0
    have hv : v = v₀ + v₁ + v₂ := by
      funext c
      simp only [Pi.add_apply, v₀, v₁, v₂]
      by_cases h0 : planeOf c = k₀
      · have h1 : planeOf c ≠ k₁ := fun h => hk (h0.symm.trans h)
        simp [h0, hk]
      · by_cases h1 : planeOf c = k₁
        · simp [h1, hk.symm]
        · simp [h0, h1]
    have m0 : v₀ ∈ Vs 0 := fun c hc => by
      have : ¬ planeOf c = k₀ := fun h => hc (by simp [S, h])
      simp [v₀, this]
    have m1 : v₁ ∈ Vs 1 := fun c hc => by
      have : ¬ planeOf c = k₁ := fun h => hc (by simp [S, h])
      simp [v₁, this]
    have m2 : v₂ ∈ Vs 2 := fun c hc => by
      have : ¬ (planeOf c ≠ k₀ ∧ planeOf c ≠ k₁) := fun h => hc (by simpa [S] using h)
      simp [v₂, this]
    rw [hv]
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.mem_iSup_of_mem 0 m0)
      (Submodule.mem_iSup_of_mem 1 m1)) (Submodule.mem_iSup_of_mem 2 m2)
  have hall : ∀ v, TransCenter H v := by
    refine transCenter_of_pairs (Vs := Vs) hspan
      (fun i j hij u hu v hv => spForm_eq_zero_of_disjoint (hdisj i j hij) hu hv)
      (fun i => nondegenerate_planeSub _) ?_ ?_
    · intro i c hc
      fin_cases i
      · exact hC₁ c (hsubset0 hc)
      · exact hC₀ c (hsubset1 hc)
      · exact hC₀ c (hsubset2a hc)
    · intro i j hij y hy y' hy' hy0 hy'0
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hmix y hy y' hy' hy'0
      · exact hC₁ _ (Submodule.add_mem _ (hsubset0 hy) (hsubset2b hy'))
      · rw [add_comm]
        exact hmix y' hy' y hy hy0
      · exact absurd rfl hij
      · exact hC₀ _ (Submodule.add_mem _ (hsubset1 hy) (hsubset2a hy'))
      · exact hC₁ _ (Submodule.add_mem _ (hsubset2b hy) (hsubset0 hy'))
      · exact hC₀ _ (Submodule.add_mem _ (hsubset2a hy) (hsubset1 hy'))
      · exact absurd rfl hij
  exact eq_top_of_transCenter hall

section Planes

theorem mulVec_eq_self_of_isSupp {S : Set (Fin r ⊕ Fin r)}
    {M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} (hM : IsSupp S M) {v : Fin r ⊕ Fin r → K}
    (hv : ∀ c ∈ S, v c = 0) : M *ᵥ v = v := by
  have h : M *ᵥ v = (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v := by
    funext c
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases ht : t ∈ S
    · rw [hv t ht, mul_zero, mul_zero]
    · rw [hM c t (fun h => ht h.2)]
  rw [h, Matrix.one_mulVec]

theorem spEnd_longBlock_of_mem (k : Fin r) (A : SL(2, K)) {v : Fin r ⊕ Fin r → K}
    (hv : v ∈ planeSub (K := K) {i | i ≠ k}) : spEnd (longBlock K r k A) v = v := by
  change mat r K (longBlock K r k A) *ᵥ v = v
  refine mulVec_eq_self_of_isSupp (isSupp_longBlock k A) fun c hc => hv c ?_
  rcases mem_coords.1 hc with rfl | rfl <;> simp

theorem commute_longBlock {k₀ k₁ : Fin r} (hk : k₀ ≠ k₁) (A B : SL(2, K)) :
    Commute (longBlock K r k₀ A) (longBlock K r k₁ B) :=
  commute_suppGroup_compl (S := coords k₀) (isSupp_longBlock k₀ A)
    (suppGroup_mono (coords_subset_compl hk.symm) (isSupp_longBlock k₁ B))

theorem eq_one_of_isSupp_disjoint {S T : Set (Fin r ⊕ Fin r)} (hST : Disjoint S T)
    {x : StatedSp r K} (hS : IsSupp S (mat r K x)) (hT : IsSupp T (mat r K x)) : x = 1 := by
  apply mat_injective
  rw [map_one]
  ext c t
  by_cases h : c ∈ S ∧ t ∈ S
  · exact hT c t fun h' => Set.disjoint_left.1 hST h.1 h'.1
  · exact hS c t h

theorem isElemAbelian_closure_of_comm {G : Type*} [Group G] {p : ℕ} {S : Set G}
    (hc : ∀ x ∈ S, ∀ y ∈ S, Commute x y) (hp : ∀ x ∈ S, x ^ p = 1) :
    IsElemAbelian p (Subgroup.closure S) := by
  have hcomm : IsMulCommutative (Subgroup.closure S) :=
    Subgroup.isMulCommutative_closure fun x hx y hy _ => hc x hx y hy
  refine ⟨hcomm, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hp x hx
  | one => exact one_pow p
  | mul x y hx hy ihx ihy =>
    have hxy : Commute x y := by
      have := hcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
      exact congrArg Subtype.val this
    rw [hxy.mul_pow, ihx, ihy, one_mul]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

theorem card_closure_pair' {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {a b : G}
    (hab : Commute a b) (ha : orderOf a = p) (hb : orderOf b = p)
    (hind : b ∉ Subgroup.zpowers a) : Nat.card ↥(Subgroup.closure ({a, b} : Set G)) = p ^ 2 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hcomm : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers b, Commute x y := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact hab.zpow_zpow m n
  have hcb : Nat.card ↥(Subgroup.zpowers b) = p := by rw [Nat.card_zpowers, hb]
  have hca : Nat.card ↥(Subgroup.zpowers a) = p := by rw [Nat.card_zpowers, ha]
  have hinf : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
    have : Fact (Nat.card ↥(Subgroup.zpowers b)).Prime := ⟨by rw [hcb]; exact hp⟩
    have h := Subgroup.eq_bot_or_eq_top_of_prime_card
      ((Subgroup.zpowers a ⊓ Subgroup.zpowers b).subgroupOf (Subgroup.zpowers b))
    rcases h with h | h
    · rw [Subgroup.subgroupOf_eq_bot] at h
      have h' := disjoint_iff.1 h
      rwa [inf_assoc, inf_idem] at h'
    · exfalso
      apply hind
      have hbb : (⟨b, Subgroup.mem_zpowers b⟩ : ↥(Subgroup.zpowers b)) ∈
          (Subgroup.zpowers a ⊓ Subgroup.zpowers b).subgroupOf (Subgroup.zpowers b) := by
        rw [h]; exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.1 hbb).1
  let φ : Subgroup.zpowers a × Subgroup.zpowers b →* G :=
    MonoidHom.noncommCoprod (Subgroup.zpowers a).subtype (Subgroup.zpowers b).subtype
      fun x y => hcomm x x.2 y y.2
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, y⟩ hxy
    have hxy' : (x : G) * y = 1 := hxy
    have hx : (x : G) = (y : G)⁻¹ := eq_inv_of_mul_eq_one_left hxy'
    have hmem : (x : G) ∈ Subgroup.zpowers a ⊓ Subgroup.zpowers b :=
      ⟨x.2, by rw [hx]; exact (Subgroup.zpowers b).inv_mem y.2⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    have hy : (y : G) = 1 := inv_eq_one.1 (hx.symm.trans hmem)
    exact Prod.ext (Subtype.ext hmem) (Subtype.ext hy)
  have hrange : φ.range = Subgroup.closure ({a, b} : Set G) := by
    have h1 : φ.range = (Subgroup.zpowers a).subtype.range ⊔ (Subgroup.zpowers b).subtype.range :=
      MonoidHom.noncommCoprod_range _ _ _
    rw [h1, Subgroup.range_subtype, Subgroup.range_subtype, Set.insert_eq,
      Subgroup.closure_union, ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure]
  rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Nat.card_prod, hca, hcb,
    sq]

theorem exists_block_plane (hr : 3 ≤ r) {p : ℕ} (hp : p.Prime) (A : SL(2, K)) (hA : orderOf A = p) :
    ∃ E : Subgroup (StatedSp r K), IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      Subgroup.closure {g : StatedSp r K | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g} = ⊤ := by
  let k₀ : Fin r := ⟨0, by omega⟩
  let k₁ : Fin r := ⟨1, by omega⟩
  let l : Fin r := ⟨2, by omega⟩
  have hk : k₀ ≠ k₁ := fun h => by simpa [k₀, k₁] using congrArg Fin.val h
  have hl₀ : l ≠ k₀ := fun h => by simpa [l, k₀] using congrArg Fin.val h
  have hl₁ : l ≠ k₁ := fun h => by simpa [l, k₁] using congrArg Fin.val h
  set a : StatedSp r K := longBlock K r k₀ A with ha
  set b : StatedSp r K := longBlock K r k₁ A with hb
  have hA1 : A ≠ 1 := fun h => by
    rw [h, orderOf_one] at hA
    exact hp.one_lt.ne hA
  have ha1 : a ≠ 1 := fun h => hA1 (longBlock_injective k₀ (by rw [map_one]; exact h))
  have hb1 : b ≠ 1 := fun h => hA1 (longBlock_injective k₁ (by rw [map_one]; exact h))
  have hab : Commute a b := commute_longBlock hk A A
  have hao : orderOf a = p := by
    rw [ha, orderOf_injective (longBlock K r k₀) (longBlock_injective k₀) A, hA]
  have hbo : orderOf b = p := by
    rw [hb, orderOf_injective (longBlock K r k₁) (longBlock_injective k₁) A, hA]
  have hind : b ∉ Subgroup.zpowers a := by
    intro hmem
    have hdisj : Disjoint (coords k₀) (coords k₁) := Set.disjoint_left.2 fun c h0 h1 => by
      rcases mem_coords.1 h0 with rfl | rfl <;> rcases mem_coords.1 h1 with h | h <;>
        first | exact hk (Sum.inl_injective h) | exact hk (Sum.inr_injective h) | cases h
    have h0 : b ∈ suppGroup (K := K) (coords k₀) := by
      have : Subgroup.zpowers a ≤ suppGroup (coords k₀) :=
        Subgroup.zpowers_le.2 (isSupp_longBlock k₀ A)
      exact this hmem
    exact hb1 (eq_one_of_isSupp_disjoint hdisj h0 (isSupp_longBlock k₁ A))
  refine ⟨Subgroup.closure {a, b}, ?_, card_closure_pair' hp hab hao hbo hind, ?_⟩
  · refine isElemAbelian_closure_of_comm ?_ ?_
    · intro x hx y hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
        first | exact Commute.refl _ | exact hab | exact hab.symm
    · intro x hx
      rcases hx with rfl | rfl
      · rw [← hao]
        exact pow_orderOf_eq_one _
      · rw [← hbo]
        exact pow_orderOf_eq_one _
  · refine closure_centralizers_of_blocks hk hl₀ hl₁ (Subgroup.subset_closure (Or.inl rfl))
      (Subgroup.subset_closure (Or.inr rfl)) ha1 hb1 ?_ ?_
    · intro v hv
      exact spEnd_longBlock_of_mem k₀ A hv
    · intro v hv
      exact spEnd_longBlock_of_mem k₁ A hv

end Planes

end CFSG.LieType.SeitzGeneration
