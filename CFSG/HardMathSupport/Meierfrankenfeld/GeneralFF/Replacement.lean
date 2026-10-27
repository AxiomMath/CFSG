module

public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.OffenderBasic
public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.CommLemmas

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF

open CFSG.RankThree.FFModules

namespace Replacement

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V} {A B : Subgroup G} {U W X : Submodule (ZMod 2) V}
variable {a b : G} {u : V}

theorem mem_commOn_of (ha : a ∈ A) (hu : u ∈ U) : ρ a u - u ∈ commOn ρ A U :=
  Submodule.subset_span ⟨a, ha, u, hu, rfl⟩

theorem commOn_le_iff : commOn ρ A U ≤ W ↔ ∀ a ∈ A, ∀ u ∈ U, ρ a u - u ∈ W := by
  refine ⟨fun h a ha u hu => h (mem_commOn_of ha hu), fun h => ?_⟩
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨a, ha, u, hu, rfl⟩
  exact h a ha u hu

theorem commOn_le (hU : IsInvariant ρ A U) : commOn ρ A U ≤ U :=
  commOn_le_iff.mpr fun a ha u hu => U.sub_mem (hU a ha u hu) hu

theorem commOn_bot : commOn ρ A ⊥ = ⊥ := by
  refine le_bot_iff.mp (commOn_le_iff.mpr fun a ha u hu => ?_)
  rw [Submodule.mem_bot] at hu
  simp [hu]

theorem isInvariant_of_comm_le (hU : W ≤ U) (hc : commOn ρ A U ≤ W) : IsInvariant ρ A W := by
  intro a ha w hw
  have : ρ a w - w ∈ W := hc (mem_commOn_of ha (hU hw))
  simpa using W.add_mem this hw

theorem fixOn_eq (ρ : Representation (ZMod 2) G V) (A : Subgroup G) (U : Submodule (ZMod 2) V) :
    fixOn ρ A U = U ⊓ fixSub ρ A := rfl

theorem comm_apply (hE : IsElemAbelianOn ρ A U) (hU : IsInvariant ρ A U) {a b : G} (ha : a ∈ A)
    (hb : b ∈ A) {u : V} (hu : u ∈ U) : ρ a (ρ b u) = ρ b (ρ a u) := by
  have hw : ρ b (ρ a u) ∈ U := hU b hb _ (hU a ha u hu)
  have h := (hE a ha b hb).1 _ hw
  have e : ρ (a * b * a⁻¹ * b⁻¹) (ρ b (ρ a u)) = ρ a (ρ b u) := by
    rw [← Module.End.mul_apply (ρ b), ← map_mul, ← Module.End.mul_apply (ρ (a * b * a⁻¹ * b⁻¹)),
      ← map_mul, ← Module.End.mul_apply (ρ a), ← map_mul]
    congr 2
    group
  rw [← e, h]

theorem sq_apply (hE : IsElemAbelianOn ρ A U) {a : G} (ha : a ∈ A) {u : V} (hu : u ∈ U) :
    ρ a (ρ a u) = u := by
  rw [← Module.End.mul_apply, ← map_mul]
  exact (hE a ha a ha).2 u hu

def genSpan (S : Finset (Module.End (ZMod 2) V)) (W : Submodule (ZMod 2) V) :
    Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2) {x | ∃ s ∈ S, ∃ w ∈ W, x = s w}

theorem genSpan_le_iff {S : Finset (Module.End (ZMod 2) V)} {W Z : Submodule (ZMod 2) V} :
    genSpan S W ≤ Z ↔ ∀ s ∈ S, ∀ w ∈ W, s w ∈ Z := by
  refine ⟨fun h s hs w hw => h (Submodule.subset_span ⟨s, hs, w, hw, rfl⟩), fun h => ?_⟩
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨s, hs, w, hw, rfl⟩
  exact h s hs w hw

theorem mem_genSpan {S : Finset (Module.End (ZMod 2) V)} {W : Submodule (ZMod 2) V}
    {s : Module.End (ZMod 2) V} (hs : s ∈ S) {w : V} (hw : w ∈ W) : s w ∈ genSpan S W :=
  Submodule.subset_span ⟨s, hs, w, hw, rfl⟩

theorem nil_aux (U : Submodule (ZMod 2) V) [DecidableEq (Module.End (ZMod 2) V)] :
    ∀ S : Finset (Module.End (ZMod 2) V),
      (∀ s ∈ S, ∀ t ∈ S, ∀ u ∈ U, s (t u) = t (s u)) →
      (∀ s ∈ S, ∀ u ∈ U, s (s u) = 0) → (∀ s ∈ S, ∀ u ∈ U, s u ∈ U) →
      ∀ W1 W2 : Submodule (ZMod 2) V, W2 ≤ U → W1 ≤ W2 →
        (∀ s ∈ S, ∀ w ∈ W1, s w ∈ W1) → (∀ s ∈ S, ∀ w ∈ W2, s w ∈ W2) →
        W2 ≤ W1 ⊔ genSpan S W2 → W2 ≤ W1 := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _ _ _ W1 W2 _ _ _ _ h
    have : genSpan ∅ W2 = ⊥ := by
      rw [eq_bot_iff, genSpan_le_iff]; simp
    simpa [this] using h
  | insert t S ht ih =>
    intro hcomm hsq hinv W1 W2 hW2U hW12 hW1inv hW2inv hle
    have hcommS : ∀ s ∈ S, ∀ t ∈ S, ∀ u ∈ U, s (t u) = t (s u) := fun s hs t' ht' =>
      hcomm s (Finset.mem_insert_of_mem hs) t' (Finset.mem_insert_of_mem ht')
    have hsqS : ∀ s ∈ S, ∀ u ∈ U, s (s u) = 0 := fun s hs =>
      hsq s (Finset.mem_insert_of_mem hs)
    have hinvS : ∀ s ∈ S, ∀ u ∈ U, s u ∈ U := fun s hs =>
      hinv s (Finset.mem_insert_of_mem hs)
    have htS : t ∈ insert t S := Finset.mem_insert_self t S
    set T : Submodule (ZMod 2) V := W2.map t with hT
    have hTU : T ≤ U := by
      rintro _ ⟨w, hw, rfl⟩
      exact hinv t htS w (hW2U hw)
    have hTW2 : T ≤ W2 := by
      rintro _ ⟨w, hw, rfl⟩
      exact hW2inv t htS w hw
    have h1 : ∀ x ∈ genSpan (insert t S) W2, t x ∈ genSpan S T := by
      have : genSpan (insert t S) W2 ≤ (genSpan S T).comap t := by
        rw [genSpan_le_iff]
        intro s hs w hw
        rcases Finset.mem_insert.mp hs with rfl | hs
        · simp only [Submodule.mem_comap]
          rw [hsq s htS w (hW2U hw)]
          exact Submodule.zero_mem _
        · simp only [Submodule.mem_comap]
          rw [hcomm t htS s (Finset.mem_insert_of_mem hs) w (hW2U hw)]
          exact mem_genSpan hs ⟨w, hw, rfl⟩
      exact fun x hx => this hx
    have hTle : T ≤ W1.map t ⊔ genSpan S T := by
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨w1, hw1, d, hd, hwd⟩ := Submodule.mem_sup.mp (hle hw)
      rw [← hwd, map_add]
      exact Submodule.add_mem_sup ⟨w1, hw1, rfl⟩ (h1 d hd)
    have hT1 : T ≤ W1.map t := by
      refine ih hcommS hsqS hinvS (W1.map t) T hTU (Submodule.map_mono hW12) ?_ ?_ hTle
      · rintro s hs _ ⟨w, hw, rfl⟩
        refine ⟨s w, hW1inv s (Finset.mem_insert_of_mem hs) w hw, ?_⟩
        exact hcomm t htS s (Finset.mem_insert_of_mem hs) w (hW2U (hW12 hw))
      · rintro s hs _ ⟨w, hw, rfl⟩
        refine ⟨s w, hW2inv s (Finset.mem_insert_of_mem hs) w hw, ?_⟩
        exact hcomm t htS s (Finset.mem_insert_of_mem hs) w (hW2U hw)
    have hT2 : T ≤ W1 := hT1.trans (by
      rintro _ ⟨w, hw, rfl⟩
      exact hW1inv t htS w hw)
    have hgen : genSpan (insert t S) W2 ≤ W1 ⊔ genSpan S W2 := by
      rw [genSpan_le_iff]
      intro s hs w hw
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact Submodule.mem_sup_left (hT2 ⟨w, hw, rfl⟩)
      · exact Submodule.mem_sup_right (mem_genSpan hs hw)
    refine ih hcommS hsqS hinvS W1 W2 hW2U hW12
      (fun s hs => hW1inv s (Finset.mem_insert_of_mem hs))
      (fun s hs => hW2inv s (Finset.mem_insert_of_mem hs)) ?_
    calc W2 ≤ W1 ⊔ genSpan (insert t S) W2 := hle
      _ ≤ W1 ⊔ (W1 ⊔ genSpan S W2) := sup_le_sup_left hgen _
      _ = W1 ⊔ genSpan S W2 := by rw [← sup_assoc, sup_idem]

variable [Finite V]

theorem le_of_le_sup_commOn (hE : IsElemAbelianOn ρ A U) (hU : IsInvariant ρ A U)
    {W1 W2 : Submodule (ZMod 2) V} (hW2 : W2 ≤ U) (h12 : W1 ≤ W2) (hW1 : IsInvariant ρ A W1)
    (hW2i : IsInvariant ρ A W2) (h : W2 ≤ W1 ⊔ commOn ρ A W2) : W2 ≤ W1 := by
  classical
  have hfin : Finite (Module.End (ZMod 2) V) :=
    Finite.of_injective (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  let S : Finset (Module.End (ZMod 2) V) :=
    (Set.toFinite {s : Module.End (ZMod 2) V | ∃ a ∈ A, s = ρ a - 1}).toFinset
  have hS : ∀ s, s ∈ S ↔ ∃ a ∈ A, s = ρ a - 1 := fun s => by simp [S]
  have hcomm : ∀ s ∈ S, ∀ t ∈ S, ∀ u ∈ U, s (t u) = t (s u) := by
    intro s hs t ht u hu
    obtain ⟨a, ha, rfl⟩ := (hS s).mp hs
    obtain ⟨b, hb, rfl⟩ := (hS t).mp ht
    have hau := hU a ha u hu
    have hbu := hU b hb u hu
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
    rw [comm_apply hE hU ha hb hu]
    abel
  have hsq : ∀ s ∈ S, ∀ u ∈ U, s (s u) = 0 := by
    intro s hs u hu
    obtain ⟨a, ha, rfl⟩ := (hS s).mp hs
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
    rw [sq_apply hE ha hu]
    have h3 : ∀ w : V, w + w = 0 := fun w => by
      rw [← two_smul (ZMod 2)]; simp [show (2 : ZMod 2) = 0 from rfl]
    calc u - ρ a u - (ρ a u - u) = (u + u) - (ρ a u + ρ a u) := by abel
      _ = 0 := by rw [h3, h3, sub_zero]
  have hinv : ∀ s ∈ S, ∀ u ∈ U, s u ∈ U := by
    intro s hs u hu
    obtain ⟨a, ha, rfl⟩ := (hS s).mp hs
    simpa using U.sub_mem (hU a ha u hu) hu
  refine nil_aux U S hcomm hsq hinv W1 W2 hW2 h12 ?_ ?_ ?_
  · intro s hs w hw
    obtain ⟨a, ha, rfl⟩ := (hS s).mp hs
    simpa using W1.sub_mem (hW1 a ha w hw) hw
  · intro s hs w hw
    obtain ⟨a, ha, rfl⟩ := (hS s).mp hs
    simpa using W2.sub_mem (hW2i a ha w hw) hw
  · refine h.trans (sup_le_sup_left ?_ _)
    refine commOn_le_iff.mpr fun a ha u hu => ?_
    have := mem_genSpan (S := S) (W := W2) ((hS _).mpr ⟨a, ha, rfl⟩) hu
    simpa using this

theorem eq_of_le_of_card_le (h : W ≤ U) (hc : Nat.card U ≤ Nat.card W) : W = U := by
  have hb := (Submodule.inclusion_injective h).bijective_of_nat_card_le hc
  refine le_antisymm h fun u hu => ?_
  obtain ⟨⟨w, hw⟩, hwu⟩ := hb.2 ⟨u, hu⟩
  have : w = u := congrArg Subtype.val hwu
  exact this ▸ hw

theorem card_pos' (W : Submodule (ZMod 2) V) : 0 < Nat.card W := Nat.card_pos

def Best (ρ : Representation (ZMod 2) G V) (A : Subgroup G) (U : Submodule (ZMod 2) V) : Prop :=
  ∀ B : Subgroup G, B ≤ A → Nat.card B * Nat.card (fixOn ρ B U) ≤
    Nat.card A * Nat.card (fixOn ρ A U)

theorem Best.finite (h : Best ρ A U) : Finite A := by
  have h1 := h ⊥ bot_le
  have : fixOn ρ ⊥ U = U := by
    rw [fixOn_eq, fixSub_bot, inf_top_eq]
  rw [this, Subgroup.card_bot, one_mul] at h1
  have hpos : 0 < Nat.card U := Nat.card_pos
  have : Nat.card A ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    omega
  exact Nat.finite_of_card_ne_zero this

theorem Best.mono (h : Best ρ A U) (hW : W ≤ U) : Best ρ A W :=
  weight_le_restrict h hW

def Concl (ρ : Representation (ZMod 2) G V) (A : Subgroup G) (U : Submodule (ZMod 2) V) : Prop :=
  Nat.card (cenOn ρ A (commOn ρ A U)) * Nat.card (fixOn ρ (cenOn ρ A (commOn ρ A U)) U) =
      Nat.card A * Nat.card (fixOn ρ A U) ∧
    fixOn ρ (cenOn ρ A (commOn ρ A U)) U = commOn ρ A U ⊔ fixOn ρ A U

theorem commOn_sup_fixOn_le (hU : IsInvariant ρ A U) :
    commOn ρ A U ⊔ fixOn ρ A U ≤ fixOn ρ (cenOn ρ A (commOn ρ A U)) U := by
  refine sup_le ?_ (fixOn_anti_left (cenOn_le ρ A _))
  intro x hx
  exact ⟨commOn_le hU hx, fun a ha => ha.2 x hx⟩

theorem concl_of_star (hU : IsInvariant ρ A U) (hB : Best ρ A U)
    (hs : Nat.card A * Nat.card (fixOn ρ A U) ≤
      Nat.card (cenOn ρ A (commOn ρ A U)) * Nat.card ↥(commOn ρ A U ⊔ fixOn ρ A U)) :
    Concl ρ A U := by
  have := hB.finite
  have hK := commOn_sup_fixOn_le hU
  have h1 := hB _ (cenOn_le ρ A (commOn ρ A U))
  have hfin : Finite (cenOn ρ A (commOn ρ A U)) := Finite.of_injective
    (Subgroup.inclusion (cenOn_le ρ A (commOn ρ A U))) (Subgroup.inclusion_injective _)
  unfold Concl
  generalize cenOn ρ A (commOn ρ A U) = A' at *
  have h2 := Nat.mul_le_mul_left (Nat.card A') (card_le_of_le_submodule hK)
  have hpos : 0 < Nat.card A' := Nat.card_pos
  have e1 : Nat.card A' * Nat.card (fixOn ρ A' U) = Nat.card A * Nat.card (fixOn ρ A U) := by
    omega
  refine ⟨e1, ?_⟩
  symm
  refine eq_of_le_of_card_le hK ?_
  refine Nat.le_of_mul_le_mul_left (c := Nat.card A') ?_ hpos
  omega

theorem cenOn_bot : cenOn ρ A ⊥ = A := by
  ext g
  simp only [mem_cenOn, Submodule.mem_bot, forall_eq]
  simp only [map_zero, and_true]

theorem concl_of_comm_bot (h : commOn ρ A U = ⊥) : Concl ρ A U := by
  unfold Concl
  rw [h, cenOn_bot, bot_sup_eq]
  exact ⟨rfl, rfl⟩

theorem cen_iff_of_cyclic (hE : IsElemAbelianOn ρ A U) (hU : IsInvariant ρ A U) {v : V}
    (hv : v ∈ U)
    (hXv : commOn ρ A U ≤ Submodule.span (ZMod 2) {w | ∃ a ∈ A, w = ρ a v - v})
    {x : G} (hx : x ∈ A) :
    x ∈ cenOn ρ A (commOn ρ A U) ↔ ρ x v - v ∈ fixSub ρ A := by
  constructor
  · intro h a ha
    have h1 : ρ x (ρ a v - v) = ρ a v - v := h.2 _ (mem_commOn_of ha hv)
    rw [map_sub] at h1
    have h2 := sub_eq_iff_eq_add.mp h1
    rw [map_sub, comm_apply hE hU ha hx hv, h2]
    abel
  · intro h
    refine ⟨hx, fun w hw => ?_⟩
    have hle : Submodule.span (ZMod 2) {w | ∃ a ∈ A, w = ρ a v - v} ≤
        LinearMap.ker (ρ x - 1) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨a, ha, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply]
      have e2 : ρ a (ρ x v - v) = ρ x v - v := h a ha
      rw [map_sub] at e2
      have e3 := sub_eq_iff_eq_add.mp e2
      rw [map_sub, comm_apply hE hU hx ha hv, e3]
      abel
    have := hle (hXv hw)
    simpa [sub_eq_zero] using this

theorem card_comap_subtype (X F : Submodule (ZMod 2) V) :
    Nat.card (F.comap X.subtype) = Nat.card ↥(X ⊓ F) :=
  Nat.card_congr
    { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
      invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem star_of_cyclic [Finite A] (hE : IsElemAbelianOn ρ A U) (hU : IsInvariant ρ A U) {v : V}
    (hv : v ∈ U)
    (hXv : commOn ρ A U ≤ Submodule.span (ZMod 2) {w | ∃ a ∈ A, w = ρ a v - v}) :
    Nat.card A * Nat.card (fixOn ρ A U) ≤
      Nat.card (cenOn ρ A (commOn ρ A U)) * Nat.card ↥(commOn ρ A U ⊔ fixOn ρ A U) := by
  set X := commOn ρ A U with hX
  set F := fixSub ρ A with hF
  set A' := cenOn ρ A X with hA'
  have hA'le : A' ≤ A := cenOn_le ρ A X
  have hkey : ∀ {x : G}, x ∈ A → (x ∈ A' ↔ ρ x v - v ∈ F) := fun hx =>
    cen_iff_of_cyclic hE hU hv hXv hx
  let D' : Submodule (ZMod 2) ↥X := F.comap X.subtype
  let H : Subgroup ↥A := A'.subgroupOf A
  have hmem : ∀ a : ↥A, ρ a v - v ∈ X := fun a => mem_commOn_of a.2 hv
  let f : ↥A → (↥X ⧸ D') := fun a => D'.mkQ ⟨ρ a v - v, hmem a⟩
  have hfeq : ∀ a b : ↥A, f a = f b ↔ ρ a v - ρ b v ∈ F := by
    intro a b
    simp only [f, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    simp only [D', Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub]
    rw [show ρ a v - v - (ρ b v - v) = ρ a v - ρ b v by abel]
  have hH : ∀ a b : ↥A, a⁻¹ * b ∈ H ↔ ρ a v - ρ b v ∈ F := by
    intro a b
    have hab : ((a⁻¹ * b : ↥A) : G) ∈ A := (a⁻¹ * b : ↥A).2
    have hmul : ∀ x : G, ρ x⁻¹ (ρ x v) = v := fun x => by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    have e : ρ ((a⁻¹ * b : ↥A) : G) v - v = ρ (a : G)⁻¹ (ρ b v - ρ a v) := by
      rw [map_sub, hmul]
      simp [map_mul]
    have hFa : ∀ z, ρ (a : G)⁻¹ z ∈ F ↔ z ∈ F := by
      intro z
      constructor
      · intro hz
        have h1 : ρ (a : G) (ρ (a : G)⁻¹ z) = z := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
        rw [← h1, hz _ a.2]
        exact hz
      · intro hz
        rw [hz _ (A.inv_mem a.2)]
        exact hz
    rw [Subgroup.mem_subgroupOf, hkey hab, e, hFa, ← neg_sub, F.neg_mem_iff]
  let g : ↥A ⧸ H → (↥X ⧸ D') := Quotient.lift f (fun a b hab => by
    rw [hfeq]
    exact (hH a b).mp (QuotientGroup.leftRel_apply.mp hab))
  have hg : Function.Injective g := by
    intro p q
    induction p using Quotient.inductionOn with | _ a =>
    induction q using Quotient.inductionOn with | _ b =>
    intro hpq
    exact (QuotientGroup.eq (a := a) (b := b)).mpr ((hH a b).mpr ((hfeq a b).mp hpq))
  have hfinQ : Finite (↥X ⧸ D') := Finite.of_surjective D'.mkQ D'.mkQ_surjective
  have hidx : H.index ≤ Nat.card (↥X ⧸ D') := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_le_card_of_injective g hg
  have hAcard : Nat.card A = Nat.card A' * H.index := by
    rw [← Subgroup.card_mul_index H]
    congr 1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA'le).toEquiv
  have hXcard := Submodule.card_eq_card_quotient_mul_card (R := ZMod 2) (M := ↥X) D'
  have hD' : Nat.card D' = Nat.card ↥(X ⊓ F) := card_comap_subtype X F
  have hXC : X ⊓ fixOn ρ A U = X ⊓ F := by
    ext x
    simp only [fixOn_eq, Submodule.mem_inf, hF]
    exact ⟨fun ⟨hx, _, h⟩ => ⟨hx, h⟩, fun ⟨hx, h⟩ => ⟨hx, commOn_le hU hx, h⟩⟩
  have hmod := card_inf_mul_card_sup X (fixOn ρ A U)
  rw [hXC] at hmod
  have hdpos : 0 < Nat.card ↥(X ⊓ F) := Nat.card_pos
  have hs : Nat.card ↥(X ⊔ fixOn ρ A U) = Nat.card (↥X ⧸ D') * Nat.card (fixOn ρ A U) := by
    refine Nat.eq_of_mul_eq_mul_left hdpos ?_
    calc Nat.card ↥(X ⊓ F) * Nat.card ↥(X ⊔ fixOn ρ A U)
        = Nat.card ↥X * Nat.card (fixOn ρ A U) := hmod
      _ = Nat.card ↥(X ⊓ F) * (Nat.card (↥X ⧸ D') * Nat.card (fixOn ρ A U)) := by
        rw [hXcard, hD']; ring
  rw [hAcard, hs]
  calc Nat.card A' * H.index * Nat.card (fixOn ρ A U)
      ≤ Nat.card A' * Nat.card (↥X ⧸ D') * Nat.card (fixOn ρ A U) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hidx)
    _ = Nat.card A' * (Nat.card (↥X ⧸ D') * Nat.card (fixOn ρ A U)) := by ring

omit [Finite V] in
theorem card_sup_mul_card_inf_of_normalizes {K L : Subgroup G}
    (hn : ∀ x ∈ L, ∀ n ∈ K, x * n * x⁻¹ ∈ K) :
    Nat.card ↥(L ⊔ K) * Nat.card ↥(K ⊓ L) = Nat.card K * Nat.card L := by
  have hL : L ≤ Subgroup.normalizer K := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hn x hx h hh, fun hh => ?_⟩
    have := hn x⁻¹ (L.inv_mem hx) _ hh
    simpa [mul_assoc] using this
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hL
  have h1 := Subgroup.relIndex_sup_right (L.subgroupOf (L ⊔ K)) (K.subgroupOf (L ⊔ K))
  rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self,
    Subgroup.relIndex_top_right, Subgroup.relIndex_subgroupOf le_sup_left] at h1
  have h2 := Subgroup.relIndex_mul_card (H := K) (K := L ⊔ K)
  have h3 := Subgroup.relIndex_mul_card (H := K) (K := L)
  have h4 : K ⊓ (L ⊔ K) = K := inf_eq_left.mpr le_sup_right
  rw [h4] at h2
  have h5 : K.relIndex (L ⊔ K) = K.relIndex L := by
    rw [← h1]; rfl
  rw [h5] at h2
  rw [← h2, ← h3]
  ring

omit [Finite V] in
theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

omit [Finite V] in
theorem hyperplane_of_functional (f : Module.Dual (ZMod 2) V) :
    ∀ c ∈ U, c ∉ U ⊓ LinearMap.ker f →
      U ≤ (U ⊓ LinearMap.ker f) ⊔ Submodule.span (ZMod 2) {c} := by
  intro c hc hcn y hy
  have hfc : f c = 1 := by
    rcases zmod_two_cases (f c) with h | h
    · exact absurd ⟨hc, h⟩ hcn
    · exact h
  have h1 : y - f y • c ∈ U ⊓ LinearMap.ker f := by
    refine ⟨U.sub_mem hy (U.smul_mem _ hc), ?_⟩
    show f (y - f y • c) = 0
    rw [map_sub, map_smul, hfc, smul_eq_mul, mul_one]
    exact sub_eq_zero_of_eq rfl
  have h2 : f y • c ∈ Submodule.span (ZMod 2) {c} := Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self c)
  have := Submodule.add_mem_sup h1 h2
  simpa using this

omit [Finite V] in
theorem two_hyperplanes (hXU : X ≤ U) {v : V} (hv : v ∈ U) (hvX : v ∉ X)
    (hcod : ¬ U ≤ X ⊔ Submodule.span (ZMod 2) {v}) :
    ∃ H1 H2 : Submodule (ZMod 2) V, X ≤ H1 ∧ H1 ≤ U ∧ X ≤ H2 ∧ H2 ≤ U ∧
      (∀ c ∈ U, c ∉ H1 → U ≤ H1 ⊔ Submodule.span (ZMod 2) {c}) ∧
      (∀ c ∈ U, c ∉ H2 → U ≤ H2 ⊔ Submodule.span (ZMod 2) {c}) ∧
      (∃ x ∈ H1, x ∉ H2) ∧ (∃ x ∈ H2, x ∉ H1) := by
  obtain ⟨u, huU, hu⟩ := IsConcreteLE.not_le_iff_exists.mp hcod
  have hvu : v ∉ X ⊔ Submodule.span (ZMod 2) {u} := by
    intro h
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp h
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rcases zmod_two_cases a with rfl | rfl
    · simp at hxy
      exact hvX (hxy ▸ hx)
    · simp at hxy
      apply hu
      have : u = v - x := by rw [← hxy]; abel
      rw [this]
      exact Submodule.sub_mem _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self v))
        (Submodule.mem_sup_left hx)
  obtain ⟨f1, hf1u, hf1⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hu inferInstance
  obtain ⟨f2, hf2v, hf2⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hvu inferInstance
  have hz1 : ∀ x ∈ X ⊔ Submodule.span (ZMod 2) {v}, f1 x = 0 := fun x hx => by
    have : f1 x ∈ (X ⊔ Submodule.span (ZMod 2) {v}).map f1 := ⟨x, hx, rfl⟩
    rw [hf1] at this
    simpa using this
  have hz2 : ∀ x ∈ X ⊔ Submodule.span (ZMod 2) {u}, f2 x = 0 := fun x hx => by
    have : f2 x ∈ (X ⊔ Submodule.span (ZMod 2) {u}).map f2 := ⟨x, hx, rfl⟩
    rw [hf2] at this
    simpa using this
  refine ⟨U ⊓ LinearMap.ker f1, U ⊓ LinearMap.ker f2, ?_, inf_le_left, ?_, inf_le_left,
    hyperplane_of_functional f1, hyperplane_of_functional f2, ⟨v, ⟨hv, ?_⟩, ?_⟩, ⟨u, ⟨huU, ?_⟩, ?_⟩⟩
  · exact fun x hx => ⟨hXU hx, hz1 x (Submodule.mem_sup_left hx)⟩
  · exact fun x hx => ⟨hXU hx, hz2 x (Submodule.mem_sup_left hx)⟩
  · exact hz1 v (Submodule.mem_sup_right (Submodule.mem_span_singleton_self v))
  · exact fun h => hf2v h.2
  · exact hz2 u (Submodule.mem_sup_right (Submodule.mem_span_singleton_self u))
  · exact fun h => hf1u h.2

theorem star_of_sub {H : Submodule (ZMod 2) V} (hHU : H ≤ U) (hHinv : IsInvariant ρ A H)
    (hXH : commOn ρ A U = commOn ρ A H) (hc : Concl ρ A H) :
    Nat.card A * Nat.card (fixOn ρ A U) ≤
      Nat.card (cenOn ρ A (commOn ρ A U)) * Nat.card ↥(commOn ρ A U ⊔ fixOn ρ A U) := by
  obtain ⟨hc1, hc2⟩ := hc
  rw [← hXH] at hc1 hc2
  set X := commOn ρ A U with hX
  set C := cenOn ρ A X with hC
  have hXle : X ≤ H := by rw [hXH]; exact commOn_le hHinv
  set F := fixSub ρ A with hF
  have hZ : X ⊓ fixOn ρ A U = X ⊓ fixOn ρ A H := by
    ext x
    simp only [fixOn_eq, Submodule.mem_inf]
    exact ⟨fun ⟨hx, _, h⟩ => ⟨hx, hXle hx, h⟩, fun ⟨hx, _, h⟩ => ⟨hx, hHU (hXle hx), h⟩⟩
  have m1 := card_inf_mul_card_sup X (fixOn ρ A U)
  have m2 := card_inf_mul_card_sup X (fixOn ρ A H)
  rw [hc2] at hc1
  rw [hZ] at m1
  have hZpos : 0 < Nat.card ↥(X ⊓ fixOn ρ A H) := Nat.card_pos
  have hHpos : 0 < Nat.card (fixOn ρ A H) := Nat.card_pos
  have key : Nat.card C * Nat.card ↥(X ⊔ fixOn ρ A U) = Nat.card A * Nat.card (fixOn ρ A U) := by
    refine Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hZpos hHpos) ?_
    calc Nat.card ↥(X ⊓ fixOn ρ A H) * Nat.card (fixOn ρ A H) *
          (Nat.card C * Nat.card ↥(X ⊔ fixOn ρ A U))
        = Nat.card C * (Nat.card ↥(X ⊓ fixOn ρ A H) * Nat.card ↥(X ⊔ fixOn ρ A U)) *
            Nat.card (fixOn ρ A H) := by ring
      _ = Nat.card C * (Nat.card ↥X * Nat.card (fixOn ρ A U)) * Nat.card (fixOn ρ A H) := by
          rw [m1]
      _ = Nat.card C * Nat.card (fixOn ρ A H) * (Nat.card ↥X * Nat.card (fixOn ρ A U)) := by ring
      _ = Nat.card C * (Nat.card ↥(X ⊓ fixOn ρ A H) * Nat.card ↥(X ⊔ fixOn ρ A H)) *
            Nat.card (fixOn ρ A U) := by rw [m2]; ring
      _ = Nat.card ↥(X ⊓ fixOn ρ A H) * (Nat.card C * Nat.card ↥(X ⊔ fixOn ρ A H)) *
            Nat.card (fixOn ρ A U) := by ring
      _ = Nat.card ↥(X ⊓ fixOn ρ A H) * (Nat.card A * Nat.card (fixOn ρ A H)) *
            Nat.card (fixOn ρ A U) := by rw [hc1]
      _ = _ := by ring
  exact key.ge

theorem cenOn_normalizes (hW : IsInvariant ρ A W) :
    ∀ x ∈ A, ∀ n ∈ cenOn ρ A W, x * n * x⁻¹ ∈ cenOn ρ A W := by
  intro x hx n hn
  refine ⟨A.mul_mem (A.mul_mem hx hn.1) (A.inv_mem hx), fun w hw => ?_⟩
  have hw' : ρ x⁻¹ w ∈ W := hW x⁻¹ (A.inv_mem hx) w hw
  have e1 : ρ x (ρ x⁻¹ w) = w := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hn.2 _ hw', e1]

theorem fix_le_of_ne {H : Submodule (ZMod 2) V} (hHU : H ≤ U)
    (hyp : ∀ c ∈ U, c ∉ H → U ≤ H ⊔ Submodule.span (ZMod 2) {c})
    (hne : commOn ρ A U ≠ commOn ρ A H) : fixOn ρ A U ≤ H := by
  intro c hc
  by_contra hcH
  refine hne (le_antisymm ?_ (commOn_mono_right hHU))
  refine commOn_le_iff.mpr fun a ha u hu => ?_
  obtain ⟨h, hh, y, hy, rfl⟩ := Submodule.mem_sup.mp (hyp c hc.1 hcH hu)
  obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.mp hy
  rw [map_add, map_smul, hc.2 a ha]
  have : ρ a h + k • c - (h + k • c) = ρ a h - h := by abel
  rw [this]
  exact mem_commOn_of ha hh

theorem comm_le_sup_of_two {H1 H2 : Submodule (ZMod 2) V} (h1U : H1 ≤ U)
    (hyp2 : ∀ c ∈ U, c ∉ H2 → U ≤ H2 ⊔ Submodule.span (ZMod 2) {c})
    (hw : ∃ x ∈ H1, x ∉ H2) : commOn ρ A U ≤ commOn ρ A H1 ⊔ commOn ρ A H2 := by
  obtain ⟨x, hx1, hx2⟩ := hw
  refine commOn_le_iff.mpr fun a ha u hu => ?_
  obtain ⟨h2, hh2, y, hy, rfl⟩ := Submodule.mem_sup.mp (hyp2 x (h1U hx1) hx2 hu)
  have hy1 : y ∈ H1 := by
    obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.mp hy
    exact H1.smul_mem _ hx1
  have : ρ a (h2 + y) - (h2 + y) = (ρ a y - y) + (ρ a h2 - h2) := by
    rw [map_add]; abel
  rw [this]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (mem_commOn_of ha hy1))
    (Submodule.mem_sup_right (mem_commOn_of ha hh2))

theorem piece {H : Submodule (ZMod 2) V} (hB : Best ρ A U) (hHU : H ≤ U)
    (hfix : fixOn ρ A U ≤ H) (hc : Concl ρ A H) :
    Nat.card (cenOn ρ A (commOn ρ A H)) * Nat.card (fixOn ρ (cenOn ρ A (commOn ρ A H)) U) =
        Nat.card A * Nat.card (fixOn ρ A U) ∧
      fixOn ρ (cenOn ρ A (commOn ρ A H)) U = commOn ρ A H ⊔ fixOn ρ A U := by
  have := hB.finite
  obtain ⟨hc1, hc2⟩ := hc
  have hfeq : fixOn ρ A H = fixOn ρ A U := by
    refine le_antisymm (inf_le_inf_right _ hHU) ?_
    intro x hx
    exact ⟨hfix hx, hx.2⟩
  rw [hfeq] at hc1 hc2
  have hle : fixOn ρ (cenOn ρ A (commOn ρ A H)) H ≤ fixOn ρ (cenOn ρ A (commOn ρ A H)) U :=
    inf_le_inf_right _ hHU
  have hbest := hB _ (cenOn_le ρ A (commOn ρ A H))
  have hfin : Finite (cenOn ρ A (commOn ρ A H)) := Finite.of_injective
    (Subgroup.inclusion (cenOn_le ρ A (commOn ρ A H))) (Subgroup.inclusion_injective _)
  have hpos : 0 < Nat.card (cenOn ρ A (commOn ρ A H)) := Nat.card_pos
  have hcard : Nat.card (fixOn ρ (cenOn ρ A (commOn ρ A H)) U) ≤
      Nat.card (fixOn ρ (cenOn ρ A (commOn ρ A H)) H) := by
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    omega
  have heq := eq_of_le_of_card_le hle hcard
  rw [← heq]
  exact ⟨hc1, hc2⟩

theorem star_of_two (hB : Best ρ A U) {H1 H2 : Submodule (ZMod 2) V}
    (h1U : H1 ≤ U) (h2U : H2 ≤ U)
    (hX1 : commOn ρ A U ≤ H1) (hX2 : commOn ρ A U ≤ H2)
    (hyp1 : ∀ c ∈ U, c ∉ H1 → U ≤ H1 ⊔ Submodule.span (ZMod 2) {c})
    (hyp2 : ∀ c ∈ U, c ∉ H2 → U ≤ H2 ⊔ Submodule.span (ZMod 2) {c})
    (hw : ∃ x ∈ H1, x ∉ H2)
    (hne1 : commOn ρ A U ≠ commOn ρ A H1) (hne2 : commOn ρ A U ≠ commOn ρ A H2)
    (hc1 : Concl ρ A H1) (hc2 : Concl ρ A H2) :
    Nat.card A * Nat.card (fixOn ρ A U) ≤
      Nat.card (cenOn ρ A (commOn ρ A U)) * Nat.card ↥(commOn ρ A U ⊔ fixOn ρ A U) := by
  have hAfin := hB.finite
  set X := commOn ρ A U with hX
  set X1 := commOn ρ A H1 with hX1def
  set X2 := commOn ρ A H2 with hX2def
  set CU := fixOn ρ A U with hCU
  have hX1le : X1 ≤ X := commOn_mono_right h1U
  have hX2le : X2 ≤ X := commOn_mono_right h2U
  have hH1inv : IsInvariant ρ A H1 := isInvariant_of_comm_le h1U hX1
  have hH2inv : IsInvariant ρ A H2 := isInvariant_of_comm_le h2U hX2
  have hf1 : CU ≤ H1 := fix_le_of_ne h1U hyp1 hne1
  have hf2 : CU ≤ H2 := fix_le_of_ne h2U hyp2 hne2
  obtain ⟨hm1, hP1⟩ := piece hB h1U hf1 hc1
  obtain ⟨hm2, hP2⟩ := piece hB h2U hf2 hc2
  set C1 := cenOn ρ A X1 with hC1
  set C2 := cenOn ρ A X2 with hC2
  set P1 := fixOn ρ C1 U with hP1def
  set P2 := fixOn ρ C2 U with hP2def
  have hXsup : X ≤ X1 ⊔ X2 := comm_le_sup_of_two h1U hyp2 hw
  set As := cenOn ρ A X with hAs
  have hAs1 : As ≤ C1 := cenOn_anti_right hX1le
  have hAs2 : As ≤ C2 := cenOn_anti_right hX2le
  have hC12 : C1 ⊓ C2 = As := by
    refine le_antisymm (fun g hg => ?_) (le_inf hAs1 hAs2)
    refine ⟨hg.1.1, fun x hx => ?_⟩
    obtain ⟨x1, hx1, x2, hx2, rfl⟩ := Submodule.mem_sup.mp (hXsup hx)
    rw [map_add, hg.1.2 x1 hx1, hg.2.2 x2 hx2]
  have hprod := card_sup_mul_card_inf_of_normalizes (K := C1) (L := C2)
    (fun x hx n hn => cenOn_normalizes (isInvariant_of_comm_le (commOn_le hH1inv) le_rfl) x (cenOn_le ρ A _ hx) n hn)
  rw [hC12] at hprod
  have hBle : C2 ⊔ C1 ≤ A := sup_le (cenOn_le ρ A _) (cenOn_le ρ A _)
  have hbest := hB _ hBle
  have hfixB : fixOn ρ (C2 ⊔ C1) U = P1 ⊓ P2 := by
    ext x
    simp only [fixOn_eq, fixSub_sup, Submodule.mem_inf, hP1def, hP2def]
    tauto
  rw [hfixB] at hbest
  have hPP := card_inf_mul_card_sup P1 P2
  have hQle : P1 ⊔ P2 ≤ X ⊔ CU := by
    rw [hP1, hP2]
    exact sup_le (sup_le_sup_right hX1le _) (sup_le_sup_right hX2le _)
  have hQle2 : Nat.card ↥(P1 ⊔ P2) ≤ Nat.card ↥(X ⊔ CU) := card_le_of_le_submodule hQle
  have hmpos : 0 < Nat.card A * Nat.card CU := Nat.mul_pos Nat.card_pos Nat.card_pos
  have hmm : (Nat.card A * Nat.card CU) * (Nat.card A * Nat.card CU) ≤
      (Nat.card As * Nat.card ↥(P1 ⊔ P2)) * (Nat.card A * Nat.card CU) := by
    calc (Nat.card A * Nat.card CU) * (Nat.card A * Nat.card CU)
        = (Nat.card C1 * Nat.card P1) * (Nat.card C2 * Nat.card P2) := by rw [hm1, hm2]
      _ = (Nat.card ↥(C2 ⊔ C1) * Nat.card As) * (Nat.card ↥(P1 ⊓ P2) * Nat.card ↥(P1 ⊔ P2)) := by
          rw [hprod, hPP]; ring
      _ = (Nat.card As * Nat.card ↥(P1 ⊔ P2)) *
            (Nat.card ↥(C2 ⊔ C1) * Nat.card ↥(P1 ⊓ P2)) := by ring
      _ ≤ (Nat.card As * Nat.card ↥(P1 ⊔ P2)) * (Nat.card A * Nat.card CU) :=
          Nat.mul_le_mul_left _ hbest
  have h1 := Nat.le_of_mul_le_mul_right hmm hmpos
  exact h1.trans (Nat.mul_le_mul_left _ hQle2)

theorem finrank_lt_of_not_mem {H : Submodule (ZMod 2) V} (hHU : H ≤ U) {x : V} (hx : x ∈ U)
    (hxH : x ∉ H) : Module.finrank (ZMod 2) H < Module.finrank (ZMod 2) U :=
  Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hHU fun h => hxH (h ▸ hx))

theorem main_aux {U₀ : Submodule (ZMod 2) V} (hE : IsElemAbelianOn ρ A U₀) :
    ∀ n : ℕ, ∀ U : Submodule (ZMod 2) V, Module.finrank (ZMod 2) U = n → U ≤ U₀ →
      IsInvariant ρ A U → Best ρ A U → Concl ρ A U := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro U hn hUU₀ hU hB
  have hEU : IsElemAbelianOn ρ A U := fun a ha b hb =>
    ⟨fun u hu => (hE a ha b hb).1 u (hUU₀ hu), fun u hu => (hE a ha b hb).2 u (hUU₀ hu)⟩
  have hfinA := hB.finite
  by_cases hX0 : commOn ρ A U = ⊥
  · exact concl_of_comm_bot hX0
  have hXU : commOn ρ A U ≤ U := commOn_le hU
  have hXinv : IsInvariant ρ A (commOn ρ A U) := isInvariant_of_comm_le hXU le_rfl
  have hXne : commOn ρ A U ≠ U := by
    intro h
    apply hX0
    have hc : commOn ρ A (commOn ρ A U) = commOn ρ A U := by rw [h]; exact h
    have := le_of_le_sup_commOn (U := U) hEU hU (W1 := ⊥) (W2 := commOn ρ A U) hXU bot_le
      (fun a _ w hw => by rw [Submodule.mem_bot] at hw; simp [hw]) hXinv
      (by rw [hc, bot_sup_eq])
    exact le_bot_iff.mp this
  obtain ⟨v, hvU, hvX⟩ : ∃ v ∈ U, v ∉ commOn ρ A U := by
    by_contra hcon
    push Not at hcon
    exact hXne (le_antisymm hXU fun v hv => hcon v hv)
  by_cases hcod : ∀ v ∈ U, v ∉ commOn ρ A U →
      U ≤ commOn ρ A U ⊔ Submodule.span (ZMod 2) {v}
  ·
    set Y : Submodule (ZMod 2) V := Submodule.span (ZMod 2) {w | ∃ a ∈ A, w = ρ a v - v} with hY
    have hYX : Y ≤ commOn ρ A U := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨a, ha, rfl⟩
      exact mem_commOn_of ha hvU
    have hYinv : IsInvariant ρ A Y := by
      intro a ha y hy
      have : Y ≤ Y.comap (ρ a) := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨b, hb, rfl⟩
        simp only [SetLike.mem_coe, Submodule.mem_comap]
        rw [map_sub, ← Module.End.mul_apply, ← map_mul]
        have h1 : ρ (a * b) v - ρ a v ∈ Y := by
          have := Y.sub_mem (Submodule.subset_span ⟨a * b, A.mul_mem ha hb, rfl⟩)
            (Submodule.subset_span ⟨a, ha, rfl⟩ : ρ a v - v ∈ Y)
          simpa using this
        simpa using h1
      exact this hy
    have hXle : commOn ρ A U ≤ Y ⊔ commOn ρ A (commOn ρ A U) := by
      refine commOn_le_iff.mpr fun a ha u hu => ?_
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp (hcod v hvU hvX hu)
      obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.mp hy
      have : ρ a (x + k • v) - (x + k • v) = (ρ a x - x) + k • (ρ a v - v) := by
        rw [map_add, map_smul, smul_sub]; abel
      rw [this, add_comm]
      exact Submodule.add_mem _
        (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)))
        (Submodule.mem_sup_right (mem_commOn_of ha hx))
    have hXY := le_of_le_sup_commOn (U := U) hEU hU (W1 := Y) (W2 := commOn ρ A U) hXU hYX
      hYinv hXinv hXle
    exact concl_of_star hU hB (star_of_cyclic hEU hU hvU hXY)
  · push Not at hcod
    obtain ⟨v', hv'U, hv'X, hcod'⟩ := hcod
    obtain ⟨H1, H2, hXH1, hH1U, hXH2, hH2U, hyp1, hyp2, hw12, hw21⟩ :=
      two_hyperplanes hXU hv'U hv'X hcod'
    have hH1inv : IsInvariant ρ A H1 := isInvariant_of_comm_le hH1U hXH1
    have hH2inv : IsInvariant ρ A H2 := isInvariant_of_comm_le hH2U hXH2
    obtain ⟨x1, hx1, hx1'⟩ := hw12
    obtain ⟨x2, hx2, hx2'⟩ := hw21
    have hconcl1 : Concl ρ A H1 :=
      ih _ (hn ▸ finrank_lt_of_not_mem hH1U (hH2U hx2) hx2') H1 rfl (hH1U.trans hUU₀) hH1inv (hB.mono hH1U)
    have hconcl2 : Concl ρ A H2 :=
      ih _ (hn ▸ finrank_lt_of_not_mem hH2U (hH1U hx1) hx1') H2 rfl (hH2U.trans hUU₀) hH2inv (hB.mono hH2U)
    by_cases hX1 : commOn ρ A U = commOn ρ A H1
    · exact concl_of_star hU hB (star_of_sub hH1U hH1inv hX1 hconcl1)
    by_cases hX2 : commOn ρ A U = commOn ρ A H2
    · exact concl_of_star hU hB (star_of_sub hH2U hH2inv hX2 hconcl2)
    exact concl_of_star hU hB (star_of_two hB hH1U hH2U hXH1 hXH2 hyp1 hyp2 ⟨x1, hx1, hx1'⟩
      hX1 hX2 hconcl1 hconcl2)

theorem concl_top (hE : IsElemAbelianOn ρ A ⊤) (hB : Best ρ A ⊤) : Concl ρ A ⊤ :=
  main_aux hE _ ⊤ rfl le_rfl (fun _ _ _ _ => Submodule.mem_top) hB

theorem concl_on (hE : IsElemAbelianOn ρ A U) (hU : IsInvariant ρ A U) (hB : Best ρ A U) :
    Concl ρ A U :=
  main_aux hE _ U rfl le_rfl hU hB
end Replacement

open Replacement

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem timmesfeld_replacement_on (ρ : Representation (ZMod 2) G V) (A : Subgroup G)
    (U : Submodule (ZMod 2) V) (hU : IsInvariant ρ A U) (hb : IsBestOffenderOn ρ A U) :
    let A' : Subgroup G := cenOn ρ A (commOn ρ A U)
    cenOn ρ A' U = cenOn ρ A U ∧
    Nat.card A' * Nat.card (fixOn ρ A' U) = Nat.card A * Nat.card (fixOn ρ A U) ∧
    fixOn ρ A' U = commOn ρ A U ⊔ fixOn ρ A U ∧
    IsBestOffenderOn ρ A' U ∧
    (commOn ρ A U ≠ ⊥ → commOn ρ A' U ≠ ⊥) ∧
    (∀ a ∈ A, ∀ w ∈ commOn ρ A' U, ρ a w = w) := by
  intro A'
  obtain ⟨hE, hbest⟩ := hb
  obtain ⟨hc1, hc2⟩ := concl_on hE hU hbest
  have hA'le : A' ≤ A := cenOn_le ρ A _
  have hXU : commOn ρ A U ≤ U := commOn_le hU
  have hcen : cenOn ρ A' U = cenOn ρ A U := by
    ext g
    simp only [mem_cenOn]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, fun w hw => h.2 w (hXU hw)⟩, h.2⟩⟩
  refine ⟨hcen, hc1, hc2, ⟨fun a ha b hb => hE a (hA'le ha) b (hA'le hb), fun B hB => ?_⟩, ?_, ?_⟩
  · rw [hc1]
    exact hbest B (hB.trans hA'le)
  · intro hX0 hcontra
    have hfixU : fixOn ρ A' U = U := by
      refine le_antisymm inf_le_left fun x hx => ⟨hx, fun a ha => ?_⟩
      have : ρ a x - x ∈ commOn ρ A' U := mem_commOn_of ha hx
      rw [hcontra, Submodule.mem_bot, sub_eq_zero] at this
      exact this
    have hUeq : U = commOn ρ A U ⊔ fixOn ρ A U := by
      rw [← hc2]; exact hfixU.symm
    have hle : commOn ρ A U ≤ commOn ρ A (commOn ρ A U) := by
      refine commOn_le_iff.mpr fun a ha u hu => ?_
      have hu' : u ∈ commOn ρ A U ⊔ fixOn ρ A U := by rw [← hUeq]; exact hu
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hu'
      have : ρ a (x + y) - (x + y) = ρ a x - x := by
        rw [map_add, hy.2 a ha]; abel
      rw [this]
      exact mem_commOn_of ha hx
    have hXinv : IsInvariant ρ A (commOn ρ A U) := isInvariant_of_comm_le hXU le_rfl
    have := le_of_le_sup_commOn (U := U) hE hU (W1 := ⊥) (W2 := commOn ρ A U) hXU bot_le
      (fun a _ w hw => by rw [Submodule.mem_bot] at hw; simp [hw]) hXinv
      (hle.trans le_sup_right)
    exact hX0 (le_bot_iff.mp this)
  · intro a ha w hw
    have hle : commOn ρ A' U ≤ fixSub ρ A := by
      refine commOn_le_iff.mpr fun b hb u hu c hc => ?_
      have h1 : ρ b (ρ c u - u) = ρ c u - u := hb.2 _ (mem_commOn_of hc hu)
      rw [map_sub] at h1
      have h2 := sub_eq_iff_eq_add.mp h1
      have h3 := comm_apply hE hU hc (hA'le hb) hu
      rw [map_sub, h3, h2]
      abel
    exact hle hw a ha

theorem timmesfeld_replacement (ρ : Representation (ZMod 2) G V) (A : Subgroup G)
    (hb : IsBestOffenderOn ρ A ⊤) :
    let A' : Subgroup G := cenOn ρ A (commOn ρ A ⊤)
    cenOn ρ A' ⊤ = cenOn ρ A ⊤ ∧
    Nat.card A' * Nat.card (fixSub ρ A') = Nat.card A * Nat.card (fixSub ρ A) ∧
    fixSub ρ A' = commOn ρ A ⊤ ⊔ fixSub ρ A ∧
    IsBestOffenderOn ρ A' ⊤ ∧
    (commOn ρ A ⊤ ≠ ⊥ → commOn ρ A' ⊤ ≠ ⊥) ∧
    (∀ a ∈ A, ∀ w ∈ commOn ρ A' ⊤, ρ a w = w) := by
  intro A'
  have hfix : ∀ B : Subgroup G, fixOn ρ B ⊤ = fixSub ρ B := fun B => top_inf_eq _
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
    timmesfeld_replacement_on ρ A ⊤ (fun _ _ _ _ => Submodule.mem_top) hb
  rw [hfix, hfix] at h2
  rw [hfix, hfix] at h3
  exact ⟨h1, h2, h3, h4, h5, h6⟩
