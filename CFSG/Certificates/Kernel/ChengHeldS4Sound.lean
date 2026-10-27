module

public import Certificates.Data.Kernel.ChengHeldS4K
public import CFSG.Certificates.Kernel.ChengHeldAutSound
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelSimple

public section

namespace CFSG.KC.ChengHeldP

open CFSG.OddStandard.ChengHeldData CFSG.OddStandard.ChengHeldData.RegModel
open CFSG.OddStandard.ChengHeld.Model
open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.ChengHeldS2 Subgroup
open scoped commutatorElement

section Group

variable {H : Type} [Group H]

theorem cmE_mul_right (a b c : H) : ⁅a, b * c⁆ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := by
  simp only [commutatorElement_def]
  group

theorem cmE_mul_left (a b c : H) : ⁅a * b, c⁆ = a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆ := by
  simp only [commutatorElement_def]
  group

theorem conj_mem_closure {Y : Set H} (h : ∀ x : H, ∀ y ∈ Y, x * y * x⁻¹ ∈ closure Y) (x : H) :
    ∀ k ∈ closure Y, x * k * x⁻¹ ∈ closure Y := by
  intro k hk
  induction hk using Subgroup.closure_induction with
  | mem y hy => exact h x y hy
  | one => simp
  | mul a b _ _ iha ihb =>
    have e : x * (a * b) * x⁻¹ = x * a * x⁻¹ * (x * b * x⁻¹) := by group
    rw [e]
    exact mul_mem iha ihb
  | inv a _ iha =>
    have e : x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem iha

theorem comm_le_of_normal {X : Set H} {K : Subgroup H} (hconj : ∀ k ∈ K, ∀ h : H, h * k * h⁻¹ ∈ K)
    (hX : ∀ x ∈ X, ∀ y ∈ X, ⁅x, y⁆ ∈ K) : ⁅closure X, closure X⁆ ≤ K := by
  have h1 : ∀ x ∈ X, ∀ b ∈ closure X, ⁅x, b⁆ ∈ K := by
    intro x hx b hb
    induction hb using Subgroup.closure_induction with
    | mem y hy => exact hX x hx y hy
    | one => simp
    | mul b₁ b₂ _ _ ih₁ ih₂ =>
      rw [cmE_mul_right]
      exact mul_mem ih₁ (hconj _ ih₂ b₁)
    | inv b _ ih =>
      have e : ⁅x, b⁻¹⁆ = (b⁻¹ * ⁅x, b⁆ * b)⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      refine inv_mem ?_
      have := hconj _ ih b⁻¹
      simpa using this
  refine Subgroup.commutator_le.2 fun a ha => ?_
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact fun b hb => h1 x hx b hb
  | one => intro b _; simp
  | mul a₁ a₂ _ _ ih₁ ih₂ =>
    intro b hb
    rw [cmE_mul_left]
    exact mul_mem (hconj _ (ih₂ b hb) a₁) (ih₁ b hb)
  | inv a _ ih =>
    intro b hb
    have e : ⁅a⁻¹, b⁆ = (a⁻¹ * ⁅a, b⁆ * a)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    refine inv_mem ?_
    have := hconj _ (ih b hb) a⁻¹
    simpa using this

theorem cent_closure_iff {S : Set H} (a : H) :
    (∀ b ∈ closure S, a * b = b * a) ↔ ∀ s ∈ S, a * s = s * a := by
  refine ⟨fun h s hs => h s (subset_closure hs), fun h b hb => ?_⟩
  induction hb using Subgroup.closure_induction with
  | mem s hs => exact h s hs
  | one => simp
  | mul x y _ _ hx hy => exact (Commute.mul_right (a := a) hx hy).eq
  | inv x _ hx => exact (Commute.inv_right (a := a) hx).eq

theorem abelian_closure_iff {S : Set H} :
    (∀ a ∈ closure S, ∀ b ∈ closure S, a * b = b * a) ↔ ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
  refine ⟨fun h x hx y hy => h x (subset_closure hx) y (subset_closure hy), fun h a ha b hb => ?_⟩
  have hS : ∀ s ∈ S, ∀ c ∈ closure S, s * c = c * s := fun s hs =>
    (cent_closure_iff s).2 (h s hs)
  have hb' : ∀ s ∈ S, b * s = s * b := fun s hs => (hS s hs b hb).symm
  exact ((cent_closure_iff b).2 hb' a ha).symm

theorem orderOf_two_pow_iff (x : H) (k : ℕ) :
    (x ^ 2 ^ (k + 1) = 1 ∧ x ^ 2 ^ k ≠ 1) ↔ orderOf x = 2 ^ (k + 1) := by
  constructor
  · rintro ⟨h1, h2⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime_pow h2 h1
  · intro h
    refine ⟨h ▸ pow_orderOf_eq_one x, pow_ne_one_of_lt_orderOf (by positivity) ?_⟩
    rw [h, pow_succ]
    have : 0 < 2 ^ k := by positivity
    omega

end Group

variable {M : RegModel} {H : Type} [Group H] {n : ℕ} {m : ℕ → ℕ → ℕ} {inv g : ℕ → ℕ}

theorem arr_eq_of_set (R : Rep M H) {A B : Array Bool} (hA : A.size = M.N) (hB : B.size = M.N)
    (h : R.set A = R.set B) : A = B := by
  refine Array.ext (by rw [hA, hB]) fun i hi _ => ?_
  obtain ⟨x, rfl⟩ := R.pt_surj _ (hA ▸ hi)
  have e := Set.ext_iff.1 h x
  simp only [Rep.mem_set] at e
  rw [← getElem!_pos A _ hi, ← getElem!_pos B _ (by rw [hB, ← hA]; exact hi)]
  exact Bool.eq_iff_iff.2 e

theorem arr_eq_of_get {A B : Array Bool} (hA : A.size = n) (hB : B.size = n)
    (h : ∀ i < n, A[i]! = B[i]!) : A = B := by
  refine Array.ext (by rw [hA, hB]) fun i hi hi' => ?_
  have := h i (hA ▸ hi)
  rwa [getElem!_pos A _ hi, getElem!_pos B _ hi'] at this

theorem clW_lt {gs : List ℕ} {K : ℕ} (h : clW n m gs K = true) : ∀ y ∈ gs, y < n := by
  unfold clW at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  exact fun y hy => by simpa [Nat.blt_eq] using h.1 y hy

theorem cgK_pt (R : Rep M H) (hm : ∀ a b, M.m a b = m a b) {gs : List ℕ}
    (hgs : ∀ y ∈ gs, y < M.N) (x : H) :
    cgK m gs (R.pt x) = true ↔ ∀ s : H, R.pt s ∈ gs → x * s = s * x := by
  unfold cgK
  rw [List.all_eq_true]
  constructor
  · intro h s hs
    have := h _ hs
    rw [beq_iff_eq, ← hm, ← hm, ← R.pt_mul, ← R.pt_mul] at this
    exact R.pt_inj this
  · intro h y hy
    obtain ⟨s, rfl⟩ := R.pt_surj y (hgs y hy)
    rw [beq_iff_eq, ← hm, ← hm, ← R.pt_mul, ← R.pt_mul, h s hy]

theorem top_closure (R : Rep M H) (hT : TreeSpec M) (hg : ∀ j < 7, M.gpt[j]! < M.N) :
    closure {h : H | R.pt h ∈ [M.g 0, M.g 1, M.g 2, M.g 3, M.g 4, M.g 5, M.g 6]} = ⊤ := by
  set S := {h : H | R.pt h ∈ [M.g 0, M.g 1, M.g 2, M.g 3, M.g 4, M.g 5, M.g 6]}
  have hgen : ∀ l < 7, M.gpt[l]! ∈ [M.g 0, M.g 1, M.g 2, M.g 3, M.g 4, M.g 5, M.g 6] := by
    intro l hl
    interval_cases l <;> simp [RegModel.g]
  have key : ∀ i, i < M.N → ∀ h : H, R.pt h = M.order[i]! → h ∈ closure S := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi h hh
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rw [hT.order_zero, ← R.pt_one] at hh
        rw [R.pt_inj hh]
        exact one_mem _
      · obtain ⟨p, hp, -, hl, he⟩ := hT.step i hpos hi
        obtain ⟨a, ha⟩ := R.pt_surj _ (hg _ hl)
        obtain ⟨b, hb⟩ := R.pt_surj _ (hT.order_lt p (by omega))
        have e : h = a * b := R.pt_inj (by rw [hh, he, R.pt_mul, ha, hb])
        rw [e]
        exact mul_mem (subset_closure (show R.pt a ∈ _ from ha ▸ hgen _ hl))
          (ih p hp (by omega) b hb)
  refine eq_top_iff.2 fun h _ => ?_
  let f : Fin M.N → Fin M.N := fun i => ⟨M.order[i.1]!, hT.order_lt i.1 i.2⟩
  have hf : Function.Injective f := fun i j hij =>
    Fin.ext (hT.order_inj i.1 j.1 i.2 j.2 (congrArg Fin.val hij))
  obtain ⟨i, hi⟩ := (Finite.injective_iff_surjective.1 hf) ⟨R.pt h, R.pt_lt h⟩
  exact key i.1 i.2 h (congrArg Fin.val hi).symm

theorem center_get (R : Rep M H) (hT : TreeSpec M) (hN : M.N = n) (hm : ∀ a b, M.m a b = m a b)
    (hg : ∀ j, M.g j = g j) (hglt : ∀ j < 7, g j < n) (a : ℕ) :
    M.center[a]! = (decide (a < n) && cgK m [g 0, g 1, g 2, g 3, g 4, g 5, g 6] a) := by
  have hg' : ∀ j < 7, M.gpt[j]! < M.N := fun j hj => by
    rw [hN]
    have := hglt j hj
    rwa [← hg] at this
  have hgs : ∀ y ∈ [g 0, g 1, g 2, g 3, g 4, g 5, g 6], y < M.N := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rw [hN]
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hglt _ (by norm_num)
  by_cases ha : a < n
  · obtain ⟨x, rfl⟩ := R.pt_surj a (hN ▸ ha)
    rw [decide_eq_true ha, Bool.true_and, Bool.eq_iff_iff]
    have e1 : M.center[R.pt x]! = true ↔ x ∈ Subgroup.center H := by
      have := Set.ext_iff.1 R.set_center x
      rwa [Rep.mem_set] at this
    rw [e1, cgK_pt R hm hgs, Subgroup.mem_center_iff]
    have htop := top_closure R hT hg'
    simp only [hg] at htop
    constructor
    · intro h s _
      exact (h s).symm
    · intro h b
      have := (cent_closure_iff (S := {h : H | R.pt h ∈ [g 0, g 1, g 2, g 3, g 4, g 5, g 6]})
        x).2 (fun s hs => h s hs) b (by rw [htop]; exact mem_top b)
      exact this.symm
  · rw [getElem!_neg _ _ (by rw [R.center_size, hN]; exact ha), decide_eq_false ha,
      Bool.false_and]
    rfl

theorem cent_closure_get (R : Rep M H) (hN : M.N = n) (hm : ∀ a b, M.m a b = m a b)
    {gs : List ℕ} (hgs : ∀ y ∈ gs, y < n) (a : ℕ) :
    (M.cent (M.closure gs))[a]! = (decide (a < n) && cgK m gs a) := by
  have hgs' : ∀ y ∈ gs, y < M.N := fun y hy => hN ▸ hgs y hy
  by_cases ha : a < n
  · obtain ⟨x, rfl⟩ := R.pt_surj a (hN ▸ ha)
    rw [decide_eq_true ha, Bool.true_and, Bool.eq_iff_iff]
    have e1 := Set.ext_iff.1 (R.set_cent (R.closure_size hgs')) x
    rw [Rep.mem_set] at e1
    rw [e1, cgK_pt R hm hgs', R.set_closure hgs']
    simp only [Set.mem_setOf_eq, SetLike.mem_coe]
    exact cent_closure_iff (S := {h : H | R.pt h ∈ gs}) x
  · rw [getElem!_neg _ _ (by rw [Rep.cent_size, hN]; exact ha), decide_eq_false ha,
      Bool.false_and]
    rfl

theorem isAbelian_closure (R : Rep M H) (hN : M.N = n) (hm : ∀ a b, M.m a b = m a b)
    {gs : List ℕ} (hgs : ∀ y ∈ gs, y < n) :
    M.isAbelian (M.closure gs) = gs.all fun x => gs.all fun y => m x y == m y x := by
  have hgs' : ∀ y ∈ gs, y < M.N := fun y hy => hN ▸ hgs y hy
  rw [Bool.eq_iff_iff, R.isAbelian_iff (R.closure_size hgs'), R.set_closure hgs']
  simp only [SetLike.mem_coe]
  rw [abelian_closure_iff, List.all_eq_true]
  constructor
  · intro h y hy
    obtain ⟨x, rfl⟩ := R.pt_surj y (hgs' y hy)
    exact (cgK_pt R hm hgs' x).2 fun s hs => h x hy s hs
  · intro h x hx y hy
    exact (cgK_pt R hm hgs' x).1 (h _ hx) y hy

theorem pt_cmE (R : Rep M H) (hm : ∀ a b, M.m a b = m a b) (hinv : ∀ a, M.inv[a]! = inv a)
    (x y : H) : R.pt ⁅x, y⁆ = cmM m inv (R.pt x) (R.pt y) := by
  rw [commutatorElement_def, R.pt_mul, R.pt_mul, R.pt_mul, R.pt_inv, R.pt_inv, hm, hm, hm, hinv,
    hinv]
  rfl

theorem commSub_eq_of (R : Rep M H) (hN : M.N = n) (hm : ∀ a b, M.m a b = m a b)
    (hinv : ∀ a, M.inv[a]! = inv a) (hn : 0 < n) (hmlt : ∀ x y, x < n → y < n → m x y < n)
    {A : Array Bool} (hA : A.size = n) {gs ds : List ℕ} (hgs : ∀ y ∈ gs, y < n)
    (hAs : R.set A = (closure {h : H | R.pt h ∈ gs} : Set H)) {Af : ℕ → Bool}
    (hAf : ∀ i, A[i]! = Af i) {ps : List (ℕ × ℕ)} {K : ℕ} (hcl : clW n m ds K = true)
    (hd : derW n m inv gs ds Af ps K = true) : M.commSub A A = M.closure ds := by
  have hds := clW_lt hcl
  have hds' : ∀ y ∈ ds, y < M.N := fun y hy => hN ▸ hds y hy
  have hA' : A.size = M.N := hA.trans hN.symm
  obtain ⟨-, gD⟩ := closure_bit hN hm hn hmlt hcl
  unfold derW at hd
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hd
  obtain ⟨⟨⟨hnorm, hgen⟩, hpair⟩, hmap⟩ := hd
  set KA := closure {h : H | R.pt h ∈ gs}
  set KD := closure {h : H | R.pt h ∈ ds}
  have memD : ∀ h : H, h ∈ KD ↔ bitW n (clIterK n m ds K) (R.pt h) = true := by
    intro h
    have := Set.ext_iff.1 (R.set_closure hds') h
    rw [Rep.mem_set, gD] at this
    exact this.symm
  refine arr_eq_of_set R (R.commSub_size hA' hA') (R.closure_size hds') ?_
  have hS : {c : H | ∃ a ∈ R.set A, ∃ b ∈ R.set A, c = a⁻¹ * b⁻¹ * a * b} =
      {c | ∃ g₁ ∈ KA, ∃ g₂ ∈ KA, ⁅g₁, g₂⁆ = c} := by
    rw [hAs]
    ext c
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, by simp [commutatorElement_def]⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, by simp [commutatorElement_def]⟩
  rw [R.set_commSub hA' hA', R.set_closure hds', hS, ← Subgroup.commutator_def]
  congr 1
  refine le_antisymm (comm_le_of_normal ?_ ?_) ?_
  · refine fun k hk h => conj_mem_closure (fun x y hy => ?_) h k hk
    rw [memD, R.pt_mul, R.pt_mul, R.pt_inv, hm, hm, hinv]
    exact hnorm (R.pt x) (List.mem_range.2 (hN ▸ R.pt_lt x)) (R.pt y) hy
  · intro x hx y hy
    rw [memD, pt_cmE R hm hinv]
    exact hgen _ hx _ hy
  · refine (Subgroup.closure_le _).2 fun y hy => ?_
    have hy' : R.pt y ∈ ps.map fun p => cmM m inv p.1 p.2 := by
      rw [hmap]
      exact hy
    obtain ⟨p, hp, hpy⟩ := List.mem_map.1 hy'
    have hp2 := hpair p hp
    rw [← hAf, ← hAf] at hp2
    have hlt : ∀ i, A[i]! = true → i < M.N := fun i hi => by
      by_contra hc
      rw [getElem!_neg A i (by rw [hA']; exact hc)] at hi
      exact Bool.false_ne_true hi
    obtain ⟨a, ha⟩ := R.pt_surj _ (hlt _ hp2.1)
    obtain ⟨b, hb⟩ := R.pt_surj _ (hlt _ hp2.2)
    have haK : a ∈ KA := by
      have : a ∈ R.set A := by rw [Rep.mem_set, ha]; exact hp2.1
      rw [hAs] at this
      exact this
    have hbK : b ∈ KA := by
      have : b ∈ R.set A := by rw [Rep.mem_set, hb]; exact hp2.2
      rw [hAs] at this
      exact this
    have e : y = ⁅a, b⁆ := R.pt_inj (by rw [pt_cmE R hm hinv, ha, hb, hpy])
    rw [e]
    exact commutator_mem_commutator haK hbK

theorem o2K_iff (R : Rep M H) (hm : ∀ a b, M.m a b = m a b) (x : H) (k : ℕ) :
    o2K m (R.pt x) k = true ↔ orderOf x = 2 ^ (k + 1) := by
  have hp : ∀ j, (pwK m (R.pt x) j == 0) = true ↔ x ^ j = 1 := fun j => by
    rw [← pw_eq hm, ← R.pt_pow, beq_iff_eq, ← R.pt_one, R.pt_inj.eq_iff]
  unfold o2K
  rw [Bool.and_eq_true, hp, Bool.not_eq_true', ← Bool.not_eq_true, hp, orderOf_two_pow_iff]

theorem ord_beq4 (R : Rep M H) (hN : M.N = n) (hm : ∀ a b, M.m a b = m a b) {a : ℕ}
    (ha : a < n) : (M.ord a == 4) = o2K m a 1 := by
  obtain ⟨x, rfl⟩ := R.pt_surj a (hN ▸ ha)
  rw [Bool.eq_iff_iff, beq_iff_eq, R.ord_eq, o2K_iff R hm]
  norm_num

theorem ord_bne8 (R : Rep M H) (hN : M.N = n) (hm : ∀ a b, M.m a b = m a b) {a : ℕ}
    (ha : a < n) : (M.ord a != 8) = !o2K m a 2 := by
  obtain ⟨x, rfl⟩ := R.pt_surj a (hN ▸ ha)
  rw [bne, R.ord_eq]
  congr 1
  rw [Bool.eq_iff_iff, beq_iff_eq, o2K_iff R hm]
  norm_num

theorem filter_ord4 (R : Rep M H) (hN : M.N = n) (hm : ∀ a b, M.m a b = m a b) (f : ℕ → Bool) :
    (elemsK n f).filter (fun a => M.ord a == 4) = (elemsK n f).filter fun a => o2K m a 1 :=
  List.filter_congr fun a ha =>
    ord_beq4 R hN hm (List.mem_range.1 (List.mem_filter.1 ha).1)

theorem all_ord8 (R : Rep M H) (hN : M.N = n) (hm : ∀ a b, M.m a b = m a b) (f : ℕ → Bool) :
    (elemsK n f).all (fun a => M.ord a != 8) = (elemsK n f).all fun a => !o2K m a 2 :=
  all_congr' fun a ha => ord_bne8 R hN hm (List.mem_range.1 (List.mem_filter.1 ha).1)

theorem bInter_get (A B : Array Bool) (i : ℕ) : (bInter A B)[i]! = (A[i]! && B[i]!) := by
  unfold bInter
  by_cases hi : i < A.size
  · rw [getElem!_pos _ _ (by simpa using hi), Array.getElem_map, Array.getElem_range]
  · rw [getElem!_neg _ _ (by simpa using hi), getElem!_neg A i hi]
    rfl

theorem bInter_size' (A B : Array Bool) : (bInter A B).size = A.size := by
  simp [bInter]

theorem bUnion_get {A B : Array Bool} (h : B.size = A.size) (i : ℕ) :
    (bUnion A B)[i]! = (A[i]! || B[i]!) := by
  unfold bUnion
  by_cases hi : i < A.size
  · rw [getElem!_pos _ _ (by simpa using hi), Array.getElem_map, Array.getElem_range]
  · rw [getElem!_neg _ _ (by simpa using hi), getElem!_neg A i hi,
      getElem!_neg B i (by rw [h]; exact hi)]
    rfl

theorem bUnion_size' (A B : Array Bool) : (bUnion A B).size = A.size := by
  simp [bUnion]

theorem replicate_get (i : ℕ) : (Array.replicate n true)[i]! = decide (i < n) := by
  by_cases hi : i < n
  · rw [getElem!_pos _ _ (by simpa using hi), Array.getElem_replicate, decide_eq_true hi]
  · rw [getElem!_neg _ _ (by simpa using hi), decide_eq_false hi]
    rfl

theorem struct4OK_of {α K : ℕ} {ws : List ℕ} {ps qs : List (ℕ × ℕ)} (R : Rep (mkReg α) H)
    (hT : TreeSpec (mkReg α)) (hN : (mkReg α).N = n) (hm : ∀ a b, (mkReg α).m a b = m a b)
    (hinv : ∀ a, (mkReg α).inv[a]! = inv a) (hg : ∀ j, (mkReg α).g j = g j) (hn : 0 < n)
    (hmlt : ∀ x y, x < n → y < n → m x y < n) (hglt : ∀ j < 7, g j < n)
    (hea : (mkReg α).eaCounts = [55, 143, 29, 0, 0, 0])
    (hcl : (clW n m [g 0] K && clW n m [g 0, g 1, g 2] K &&
      clW n m [g 0, g 1, g 2, g 3, g 4] K && clW n m [g 0, g 1, g 2, g 5, g 6] K &&
      clW n m [pwK m (g 0) 2, g 1, m (g 0) (g 2)] K && clW n m ws K &&
      clW n m [g 0, g 1, m (g 0) (g 2)] K && clW n m [pwK m (g 0) 2] K) = true)
    (hd : derW n m inv [g 0, g 1, g 2, g 3, g 4, g 5, g 6] [g 0, g 1, g 2]
      (fun a => decide (a < n)) ps K = true)
    (hW : (List.range n).all (fun a => cgK m [pwK m (g 0) 2, g 1, m (g 0) (g 2)] a ==
      bitW n (clIterK n m ws K) a) = true)
    (hq : α ≠ 0 → derW n m inv ws [pwK m (g 0) 2] (bitW n (clIterK n m ws K)) qs K = true)
    (hr : s4RestW n m inv g α K ws = true) : struct4OK α = true := by
  set M := mkReg α with hM
  simp only [Bool.and_eq_true] at hcl
  obtain ⟨⟨⟨⟨⟨⟨⟨cZ, cD⟩, cR1⟩, cR2⟩, cV⟩, cW⟩, cZ3⟩, cQ⟩ := hcl
  obtain ⟨sZ, gZ⟩ := closure_bit hN hm hn hmlt cZ
  obtain ⟨sD, gD⟩ := closure_bit hN hm hn hmlt cD
  obtain ⟨sR1, gR1⟩ := closure_bit hN hm hn hmlt cR1
  obtain ⟨sR2, gR2⟩ := closure_bit hN hm hn hmlt cR2
  obtain ⟨sV, gV⟩ := closure_bit hN hm hn hmlt cV
  obtain ⟨sW, gW⟩ := closure_bit hN hm hn hmlt cW
  obtain ⟨sZ3, gZ3⟩ := closure_bit hN hm hn hmlt cZ3
  have hN' : M.N = n := hN
  have g7 : ∀ y ∈ [g 0, g 1, g 2, g 3, g 4, g 5, g 6], y < n := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hglt _ (by norm_num)
  have hg' : ∀ j < 7, M.gpt[j]! < M.N := fun j hj => by
    rw [hN']
    have := hglt j hj
    rwa [← hg] at this
  have sC : M.center.size = n := by rw [R.center_size, hN']
  have gC := center_get R hT hN hm hg hglt
  have gCR1 := cent_closure_get R hN hm (clW_lt cR1)
  have gCR2 := cent_closure_get R hN hm (clW_lt cR2)
  have gCV := cent_closure_get R hN hm (clW_lt cV)
  have gCW := cent_closure_get R hN hm (clW_lt cW)
  have sCe : ∀ B : Array Bool, (M.cent B).size = n := fun B => by rw [Rep.cent_size, hN']
  have hWeq : M.cent (M.closure [pwK m (g 0) 2, g 1, m (g 0) (g 2)]) = M.closure ws := by
    refine arr_eq_of_get (sCe _) sW fun i hi => ?_
    rw [gCV, gW, decide_eq_true hi, Bool.true_and]
    have := (List.all_eq_true.1 hW) i (List.mem_range.2 hi)
    exact beq_iff_eq.1 this
  have htop : R.set (Array.replicate n true) =
      (closure {h : H | R.pt h ∈ [g 0, g 1, g 2, g 3, g 4, g 5, g 6]} : Set H) := by
    have e := top_closure R hT hg'
    simp only [hg] at e
    rw [e]
    ext h
    rw [Rep.mem_set, replicate_get, decide_eq_true (hN' ▸ R.pt_lt h)]
    simp
  have hCT : M.commSub (Array.replicate n true) (Array.replicate n true) =
      M.closure [g 0, g 1, g 2] :=
    commSub_eq_of R hN hm hinv hn hmlt (by simp) g7 htop (fun i => replicate_get i) cD hd
  have ht4 : (M.ord (g 0) == 4) = o2K m (g 0) 1 := ord_beq4 R hN hm (hglt 0 (by norm_num))
  rw [← hr]
  have bR12 := beq_bitmap (A := bInter (M.closure [g 0, g 1, g 2, g 3, g 4])
      (M.closure [g 0, g 1, g 2, g 5, g 6])) ((bInter_size' _ _).trans sR1) sD
    (fun i => by rw [bInter_get, gR1, gR2]) gD
  have bR1 := beq_bitmap (A := bInter (M.closure [g 0, g 1, g 2, g 3, g 4])
      (M.cent (M.closure [g 0, g 1, g 2, g 3, g 4]))) ((bInter_size' _ _).trans sR1) sZ
    (fun i => by rw [bInter_get, gR1, gCR1]) gZ
  have bR2 := beq_bitmap (A := bInter (M.closure [g 0, g 1, g 2, g 5, g 6])
      (M.cent (M.closure [g 0, g 1, g 2, g 5, g 6]))) ((bInter_size' _ _).trans sR2) sZ
    (fun i => by rw [bInter_get, gR2, gCR2]) gZ
  have bWZ := beq_bitmap (A := bInter (M.closure ws) (M.cent (M.closure ws)))
    ((bInter_size' _ _).trans sW) sZ3 (fun i => by rw [bInter_get, gW, gCW]) gZ3
  have bC := beq_bitmap sC sZ gC gZ
  have eU := elems_eq (B := bUnion (M.closure [g 0, g 1, g 2, g 3, g 4])
      (M.closure [g 0, g 1, g 2, g 5, g 6])) ((bUnion_size' _ _).trans sR1)
    (fun i => by rw [bUnion_get (sR2.trans sR1.symm), gR1, gR2])
  by_cases hα : α = 0
  · subst hα
    unfold struct4OK s4RestW
    simp only [← hM]
    simp only [hN', hm, hinv, hg, pw_eq hm, hWeq, hCT, hea, ht4, beq_self_eq_true, Bool.and_true,
      Bool.true_and, Bool.true_or, card_eq sZ gZ, card_eq sD gD, card_eq sR1 gR1, card_eq sR2 gR2,
      card_eq sV gV, card_eq sW gW, bR12, bR1, bR2, bC, RegModel.invols, RegModel.ord4,
      RegModel.isElemAb, RegModel.cm, isAbelian_closure R hN hm (clW_lt cV),
      isAbelian_closure R hN hm (clW_lt cW), elems_eq sR1 gR1, elems_eq sR2 gR2, elems_eq sV gV,
      elems_eq sW gW, elems_eq (Array.size_replicate ..) replicate_get, eU, filter_ord4 R hN hm,
      all_ord8 R hN hm, gZ, gV]
  · obtain ⟨sQ, gQ⟩ := closure_bit hN hm hn hmlt cQ
    have hWs : R.set (M.closure ws) = (closure {h : H | R.pt h ∈ ws} : Set H) :=
      R.set_closure fun y hy => hN' ▸ clW_lt cW y hy
    have hWW : M.commSub (M.closure ws) (M.closure ws) = M.closure [pwK m (g 0) 2] :=
      commSub_eq_of R hN hm hinv hn hmlt sW (clW_lt cW) hWs gW cQ (hq hα)
    have h0 : (α == 0) = false := by simpa using hα
    unfold struct4OK s4RestW
    simp only [← hM]
    simp only [hN', hm, hinv, hg, pw_eq hm, hWeq, hCT, hWW, hea, ht4, h0, beq_self_eq_true,
      Bool.and_true, Bool.true_and, Bool.false_or, card_eq sZ gZ, card_eq sD gD, card_eq sR1 gR1,
      card_eq sR2 gR2, card_eq sV gV, card_eq sW gW, bR12, bR1, bR2, bC, bWZ, RegModel.invols,
      RegModel.ord4, RegModel.isElemAb, RegModel.cm, isAbelian_closure R hN hm (clW_lt cV),
      isAbelian_closure R hN hm (clW_lt cW), elems_eq sR1 gR1, elems_eq sR2 gR2, elems_eq sV gV,
      elems_eq sW gW, elems_eq (Array.size_replicate ..) replicate_get, eU, filter_ord4 R hN hm,
      all_ord8 R hN hm, gZ, gV]

end CFSG.KC.ChengHeldP

end
