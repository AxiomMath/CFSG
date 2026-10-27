module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.DataLocalTabs
public import Certificates.Certificate25121

public section

namespace CFSG.EvenSporadicStandard.J4Std.DataLocal

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

attribute [local irreducible] invs commMasks prodTab fixList fixLists tabL

section Main


theorem Tab_sup (hM : MatFacts) {B : Subgroup J} (hB : B ≤ P0) {y : J} (hy : y * y = 1)
    (hc : ∀ b ∈ B, b * y = y * b) {ty : List ℕ} (hty : Acts y ty) :
    Tab (B ⊔ Subgroup.zpowers y) = Tab B ∪ {t | ∃ s ∈ Tab B, t = compT ty s} := by
  ext t
  constructor
  · rintro ⟨x, hx, hxt⟩
    obtain ⟨u, hu, hxu | hxu⟩ := (mem_sup_zpowers_iff (G := J) (B := B) (y := y) hy hc).1 hx
    · rw [hxu] at hxt
      exact Or.inl ⟨u, hu, hxt⟩
    · rw [hxu] at hxt
      obtain ⟨s, -, hus⟩ := table_of_mem hM u (hB hu)
      exact Or.inr ⟨s, ⟨u, hu, hus⟩, hxt.unique hM (hty.mul hus)⟩
  · rintro (⟨b, hb, hbt⟩ | ⟨s, ⟨b, hb, hbs⟩, rfl⟩)
    · exact ⟨b, Subgroup.mem_sup_left hb, hbt⟩
    · exact ⟨y * b, Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
        (Subgroup.mem_sup_left hb), hty.mul hbs⟩

theorem exists_mask (hFam : chkFam = true) (hM : MatFacts) {A : Subgroup J} (hA : A ≤ P0)
    (hsq : ∀ a ∈ A, a * a = 1) (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    ∀ S : Finset J, (∀ s ∈ S, s ∈ A) →
      ∃ m, FamMem m ∧ Tab (Subgroup.closure (S : Set J)) = elems m := by
  classical
  have hT : chkTabs = true := (chkFam_spec hFam).1
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨0, famMem_zero, by rw [Finset.coe_empty, Subgroup.closure_empty, Tab_bot hM, elems_zero]⟩
  | insert y S hyS ih =>
    intro hS
    have hS' : ∀ s ∈ S, s ∈ A := fun s hs => hS s (Finset.mem_insert_of_mem hs)
    obtain ⟨m, hm, hTm⟩ := ih hS'
    have hyA : y ∈ A := hS y (Finset.mem_insert_self y S)
    have hBA : Subgroup.closure (S : Set J) ≤ A :=
      (Subgroup.closure_le A).2 fun s hs => hS' s (by simpa using hs)
    have hcl : Subgroup.closure ((insert y S : Finset J) : Set J) =
        Subgroup.closure (S : Set J) ⊔ Subgroup.zpowers y := by
      rw [Finset.coe_insert, Set.insert_eq, Subgroup.closure_union, sup_comm,
        Subgroup.zpowers_eq_closure]
    obtain ⟨ty, hty_mem, hty⟩ := table_of_mem hM y (hA hyA)
    have hysq : compT ty ty = idT := by
      have h2 := hty.mul hty
      rw [hsq y hyA] at h2
      exact h2.unique hM Acts.one
    have hyc : ∀ b ∈ Subgroup.closure (S : Set J), b * y = y * b := fun b hb =>
      hcomm b (hBA hb) y hyA
    rw [hcl, Tab_sup hM (hBA.trans hA) (hsq y hyA) hyc hty, hTm]
    by_cases hmem : ty ∈ elems m
    · refine ⟨m, hm, Set.union_eq_self_of_subset_right ?_⟩
      rintro t ⟨s, hs, rfl⟩
      rw [← hTm] at hs hmem ⊢
      obtain ⟨b, hb, hbs⟩ := hs
      obtain ⟨b₀, hb₀, hb₀t⟩ := hmem
      exact ⟨b₀ * b, Subgroup.mul_mem _ hb₀ hb, hb₀t.mul hbs⟩
    · have hty_inv : ty ∈ invs :=
        mem_invs.2 ⟨hty_mem, hysq, fun h => hmem (h ▸ idT_mem_elems m)⟩
      obtain ⟨i, hiN, hi⟩ := exists_inv hty_inv
      have hbit : m.testBit i = false := by
        by_contra hb
        exact hmem (Or.inr ⟨i, hiN, by simpa using hb, hi⟩)
      have hm_lt : m >>> nInv = 0 := famMem_shift hFam hm
      have hcm : ∀ j, m.testBit j = true → (commMasks.getD i 0).testBit j = true := by
        intro j hj
        have hjN : j < nInv := lt_nInv_of_testBit hm_lt hj
        rw [commMasks_testBit hT hiN hjN]
        have hjt : inv j ∈ elems m := Or.inr ⟨j, hjN, hj, rfl⟩
        rw [← hTm] at hjt
        obtain ⟨b, hb, hbj⟩ := hjt
        have h1 := hty.mul hbj
        have h2 := hbj.mul hty
        rw [hyc b hb] at h2
        have h3 := h1.unique hM h2
        rw [commutes, hi, h3]
        exact beq_self_eq_true _
      have hic : i ∈ cands m := mem_cands.2 ⟨hiN, hbit, hcm⟩
      exact ⟨ext m i, famMem_ext hFam hm hic, by rw [elems_ext hT hic, hi]⟩

theorem exists_mask_of_elAb (hFam : chkFam = true) (hM : MatFacts) {A : Subgroup J}
    (hA : A ≤ P0) (hsq : ∀ a ∈ A, a * a = 1) (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    ∃ m, FamMem m ∧ Tab A = elems m := by
  classical
  obtain ⟨m, hm, hT⟩ := exists_mask hFam hM hA hsq hcomm (Set.toFinite (A : Set J)).toFinset
    (fun s hs => by simpa using hs)
  refine ⟨m, hm, ?_⟩
  have : Subgroup.closure (((Set.toFinite (A : Set J)).toFinset : Finset J) : Set J) = A := by
    rw [Set.Finite.coe_toFinset, Subgroup.closure_eq]
  rwa [this] at hT

theorem mem_Eg_of_acts_idT (hM : MatFacts) (hF : J4Facts) {a : J} (ha : a ∈ P0)
    (h : Acts a idT) : a ∈ Eg uJ 11 := by
  refine centralizer_Hj hM hF a (P0_le_Hj ha) fun y hy => ?_
  obtain ⟨c, hc, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 hy
  have := h.2 c hc
  rw [actT_idT hc] at this
  calc a * eta uJ 11 c = (a * eta uJ 11 c * a⁻¹) * a := by group
    _ = eta uJ 11 c * a := by rw [this]

theorem card_le_tab_mul (hM : MatFacts) (hF : J4Facts) {A : Subgroup J} (hA : A ≤ P0) :
    Nat.card A ≤ Nat.card (Tab A) * Nat.card ↥(Eg uJ 11 ⊓ A) := by
  classical
  have hfin : (Tab A).Finite :=
    (List.finite_toSet tabL).subset fun t ht => Tab_sub_tabL hM hA ht
  have : Finite (Tab A) := hfin.to_subtype
  choose r hrA hrt using fun t : Tab A => t.2
  let tb : A → Tab A := fun a =>
    ⟨(table_of_mem hM a (hA a.2)).choose, a, a.2, (table_of_mem hM a (hA a.2)).choose_spec.2⟩
  have htb : ∀ a : A, Acts (a : J) (tb a).1 := fun a =>
    (table_of_mem hM a (hA a.2)).choose_spec.2
  have hx : ∀ a : A, (r (tb a))⁻¹ * (a : J) ∈ Eg uJ 11 ⊓ A := by
    intro a
    refine ⟨?_, A.mul_mem (A.inv_mem (hrA _)) a.2⟩
    refine centralizer_Hj hM hF _ (Hj.mul_mem (Hj.inv_mem (P0_le_Hj (hA (hrA _))))
      (P0_le_Hj (hA a.2))) fun y hy => ?_
    obtain ⟨c, hc, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 hy
    have h1 := (htb a).2 c hc
    have h2 := (hrt (tb a)).2 c hc
    have h3 : (a : J) * eta uJ 11 c * (a : J)⁻¹ = r (tb a) * eta uJ 11 c * (r (tb a))⁻¹ := by
      rw [h1, h2]
    calc (r (tb a))⁻¹ * (a : J) * eta uJ 11 c
        = (r (tb a))⁻¹ * ((a : J) * eta uJ 11 c * (a : J)⁻¹) * (a : J) := by group
      _ = (r (tb a))⁻¹ * (r (tb a) * eta uJ 11 c * (r (tb a))⁻¹) * (a : J) := by rw [h3]
      _ = eta uJ 11 c * ((r (tb a))⁻¹ * (a : J)) := by group
  let φ : A → Tab A × ↥(Eg uJ 11 ⊓ A) := fun a => (tb a, ⟨_, hx a⟩)
  have hφ : Function.Injective φ := by
    intro a a' h
    have h1 : tb a = tb a' := congrArg Prod.fst h
    have h2 : (r (tb a))⁻¹ * (a : J) = (r (tb a'))⁻¹ * (a' : J) := congrArg (fun p => (p.2 : J)) h
    rw [h1] at h2
    exact Subtype.ext (mul_left_cancel (a := (r (tb a'))⁻¹) h2)
  calc Nat.card A ≤ Nat.card (Tab A × ↥(Eg uJ 11 ⊓ A)) := Nat.card_le_card_of_injective φ hφ
    _ = Nat.card (Tab A) * Nat.card ↥(Eg uJ 11 ⊓ A) := Nat.card_prod _ _

theorem card_inf_le_fixCnt (hFam : chkFam = true) (hM : MatFacts) {A : Subgroup J} {m : ℕ}
    (hm : FamMem m) (hm0 : m ≠ 0) (hTm : Tab A = elems m)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    Nat.card ↥(Eg uJ 11 ⊓ A) ≤ fixCnt m := by
  classical
  obtain ⟨i, bs, hbs⟩ : ∃ i bs, bitIdx m = i :: bs := by
    cases h : bitIdx m with
    | nil => exact absurd h (bitIdx_ne_nil (famMem_shift hFam hm) hm0)
    | cons i bs => exact ⟨i, bs, rfl⟩
  have hi_mem : i ∈ bitIdx m := by rw [hbs]; simp
  have hiN : i < nInv := (mem_bitIdx.1 hi_mem).1
  let L : List ℕ := (fixList i).filter fun c => bs.all fun j => actT (inv j) c == c
  have hL : fixCnt m = L.length := by
    unfold fixCnt
    rw [hbs]
    simp only [fixCntFrom, fixLists_getD hiN, L]
  have key : ∀ y : ↥(Eg uJ 11 ⊓ A), ∃ c, c < 2 ^ 11 ∧ (y : J) = eta uJ 11 c ∧ c ∈ L := by
    intro y
    obtain ⟨c, hc, hyc⟩ := (mem_Eg_iff (elem_uJ hM)).1 y.2.1
    have hfix : ∀ j ∈ bitIdx m, actT (inv j) c = c := by
      intro j hj
      obtain ⟨hjN, hjb⟩ := mem_bitIdx.1 hj
      have hjt : inv j ∈ Tab A := hTm ▸ (Or.inr ⟨j, hjN, hjb, rfl⟩ : inv j ∈ elems m)
      obtain ⟨a, ha, hat⟩ := hjt
      have h1 : a * (y : J) * a⁻¹ = y := by rw [hcomm a ha y y.2.2]; group
      have h2 := hat.2 c hc
      rw [← hyc, h1, hyc] at h2
      exact (eta_inj hM _ (actT_lt hat.1 c) _ hc h2.symm)
    refine ⟨c, hc, hyc, ?_⟩
    simp only [L, List.mem_filter, List.all_eq_true, beq_iff_eq, mem_fixList]
    refine ⟨⟨by omega, hfix i hi_mem⟩, fun j hj => hfix j ?_⟩
    rw [hbs]
    exact List.mem_cons_of_mem _ hj
  choose f hf1 hf2 hf3 using key
  let g : ↥(Eg uJ 11 ⊓ A) → {c : ℕ // c ∈ L} := fun y => ⟨f y, hf3 y⟩
  have hg : Function.Injective g := by
    intro y z h
    have h' : f y = f z := congrArg Subtype.val h
    apply Subtype.ext
    rw [hf2 y, hf2 z, h']
  calc Nat.card ↥(Eg uJ 11 ⊓ A) ≤ Nat.card {c : ℕ // c ∈ L} := Nat.card_le_card_of_injective g hg
    _ ≤ L.length := natCard_mem_le L
    _ = fixCnt m := hL.symm

theorem card_le_of_mask (hFam : chkFam = true) (hM : MatFacts) (hF : J4Facts) {A : Subgroup J}
    (hA : A ≤ P0) (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {m : ℕ} (hm : FamMem m)
    (hm0 : m ≠ 0) (hTm : Tab A = elems m) : Nat.card A ≤ 1024 := by
  have h1 := card_le_tab_mul hM hF hA
  have h2 : Nat.card (Tab A) ≤ (bitIdx m).length + 1 := by
    rw [Nat.card_coe_set_eq, hTm]
    exact ncard_elems_le m
  have h3 := card_inf_le_fixCnt hFam hM hm hm0 hTm hcomm
  have h4 := famMem_boundOK hFam hm
  simp only [boundOK, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, hm0, false_or] at h4
  calc Nat.card A ≤ Nat.card (Tab A) * Nat.card ↥(Eg uJ 11 ⊓ A) := h1
    _ ≤ ((bitIdx m).length + 1) * fixCnt m := Nat.mul_le_mul h2 h3
    _ = fixCnt m * ((bitIdx m).length + 1) := Nat.mul_comm _ _
    _ ≤ 1024 := h4

theorem unique_J (hF : J4Facts) {A : Subgroup J} (hA : A ≤ P0)
    (hsq : ∀ a ∈ A, a * a = 1) (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hcard : 2 ^ 11 ≤ Nat.card A) : A = Eg uJ 11 := by
  have hM := hF.mat
  have hFam : chkFam = true := Certificates.certificate25121
  by_cases hAE : A ≤ Eg uJ 11
  · exact Subgroup.eq_of_le_of_card_ge hAE (by rw [card_Eg_uJ hM]; exact hcard)
  · exfalso
    obtain ⟨m, hm, hTm⟩ := exists_mask_of_elAb hFam hM hA hsq hcomm
    have hm0 : m ≠ 0 := by
      rintro rfl
      apply hAE
      intro a ha
      obtain ⟨t, -, hat⟩ := table_of_mem hM a (hA ha)
      have ht : t ∈ Tab A := ⟨a, ha, hat⟩
      rw [hTm, elems_zero] at ht
      rw [Set.mem_singleton_iff] at ht
      subst ht
      exact mem_Eg_of_acts_idT hM hF (hA ha) hat
    have := card_le_of_mask hFam hM hF hA hcomm hm hm0 hTm
    omega

end Main

end CFSG.EvenSporadicStandard.J4Std.DataLocal
