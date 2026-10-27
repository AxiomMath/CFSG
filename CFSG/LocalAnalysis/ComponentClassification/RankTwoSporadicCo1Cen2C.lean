module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1Cen2CTests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1Root
public import CFSG.Sporadic.Co1Block.TwoCCent

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Co1

open Subgroup CFSG.Open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block

theorem forall₂_range_of_getD {L : List Native.Rows} {f : ℕ → GL24}
    (h : ∀ l < L.length, MRep (L.getD l Native.one) (f l)) :
    List.Forall₂ MRep L ((List.range L.length).map f) := by
  rw [List.forall₂_iff_get]
  refine ⟨by simp, fun i h₁ h₂ => ?_⟩
  have := h i h₁
  rw [List.getD_eq_getElem _ _ h₁] at this
  simpa using this

@[expose] noncomputable def co1Cen2CBaseG : List GL24 :=
  A₁ :: A₂ :: cG :: (List.range twoCQRows.length).map twoCQg

theorem rep_co1Cen2CBase :
    List.Forall₂ MRep co1Cen2CBase co1Cen2CBaseG :=
  .cons rep_A₁ (.cons rep_A₂ (.cons rep_iotaC (forall₂_range_of_getD qRep_twoC)))

theorem co1Cen2CBaseG_mem :
    ∀ g ∈ co1Cen2CBaseG, g ∈ GA := by
  intro g hg
  rcases List.mem_cons.mp hg with h | hg
  · rw [h]; exact A₁_mem
  rcases List.mem_cons.mp hg with h | hg
  · rw [h]; exact A₂_mem
  rcases List.mem_cons.mp hg with h | hg
  · rw [h]; exact iotaC_mem_GA
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hg
  have hmem : twoCQg l ∈ twoCQ := by
    rw [twoCQ_eq]
    exact Subgroup.subset_closure ⟨l, by simpa [twoCQRows_length] using hl, rfl⟩
  exact (Subgroup.mem_inf.mp (twoCQ_le hmem)).1

theorem mem_twoCQ_of_comm
    {b : ℕ → GL24}
    (hb : ∀ i < twoCRoots.length, b i ∈ qSub twoCQg twoCQRows.length ∧
      MRep (twoCRoots.getD i Native.one) (b i))
    {g : GL24} (hg : g ∈ GA ⊓ Subgroup.centralizer {cG})
    (hq : ∀ i < twoCRoots.length, g * b i = b i * g) : g ∈ twoCQ := by
  have hT := card_mul_card_towerStab_brayE_le rep_iotaC twoC_cent_check twoC_q_check
    (fun i hi => (hb i hi).2)
  have hE : brayE cG twoCD1 twoCBray = GA ⊓ Subgroup.centralizer {cG} := twoCE_eq
  rw [twoC_tower_prod, hE, card_cent_cG] at hT
  set T := towerStab (GA ⊓ Subgroup.centralizer {cG}) b twoCRoots.length
  have hT2 : Nat.card T ≤ 2048 := by omega
  have hQT : twoCQ ≤ T := fun q hqQ =>
    mem_towerStab_of_lt (twoCQ_le hqQ) _ fun i hi => twoCQ_comm hqQ (hb i hi).1
  have hTQ : twoCQ = T := Subgroup.eq_of_le_of_card_ge hQT (by rw [card_twoCQ]; exact hT2)
  rw [hTQ]
  exact mem_towerStab_of_lt hg _ hq

theorem exists_of_forall₂ {α β : Type*} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) {a : α} (ha : a ∈ l₁) : ∃ b ∈ l₂, R a b := by
  induction h with
  | nil => exact absurd ha List.not_mem_nil
  | @cons x y xs ys hxy _ ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨y, List.mem_cons_self, hxy⟩
    · obtain ⟨b, hb, hab⟩ := ih ha
      exact ⟨b, List.mem_cons_of_mem _ hb, hab⟩

theorem eq_one_or_eq_cG_of_scan
    {S : List Native.Rows}
    {SG : List GL24} (hS : List.Forall₂ MRep S SG)
    (hscan : co1QcScanOK (CFSG.Sporadic.Co1.TwoBNative.gtBFS twoCQRows.toArray 2048).pts
      iotaCRows S = true)
    {g : GL24} (hgQ : g ∈ twoCQ) (hgS : ∀ s ∈ SG, g * s = s * g) : g = 1 ∨ g = cG := by
  simp only [co1QcScanOK, Bool.and_eq_true, Array.all_eq_true', List.all_eq_true] at hscan
  obtain ⟨hSvalid, hpts⟩ := hscan
  obtain ⟨f, hf, -, heq⟩ := CFSG.Sporadic.Co1Block.prodTree_closure_eq valHom valHom_injective
    (qCheck_parts twoC_q_check).1 twoCQg (qRep_arr qRep_twoC)
  have hgset : g ∈ (Subgroup.closure (twoCQg '' {l | l < twoCQRows.toArray.size}) :
      Set GL24) := by
    rw [← qSub_eq]
    exact hgQ
  rw [heq] at hgset
  obtain ⟨i, hi, rfl⟩ := hgset
  set pts := (CFSG.Sporadic.Co1.TwoBNative.gtBFS twoCQRows.toArray 2048).pts
  have hi' : i < pts.size := hi
  have hrep : MRep pts[i] (f i) := by
    have := hf i hi'
    rw [getElem!_pos pts i hi'] at this
    exact this.symm
  have hr := hpts pts[i] (Array.getElem_mem hi')
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, Bool.not_eq_true'] at hr
  obtain ⟨hvalid, (h1 | hc) | ⟨s, hs, hsc⟩⟩ := hr
  · rw [h1] at hrep
    exact Or.inl (hrep.eq MRep.one)
  · rw [hc] at hrep
    exact Or.inr (hrep.eq rep_iotaC)
  · exfalso
    obtain ⟨sG, hsG, hssG⟩ := exists_of_forall₂ hS hs
    have hsv := hSvalid s hs
    have h1 := hrep.mul hssG
    have h2 := hssG.mul hrep
    rw [hgS sG hsG] at h1
    have heq' : Native.mul pts[i] s = Native.mul s pts[i] :=
      CFSG.Sporadic.Co1.Module.rowsMatrix_injective_of_valid
        (CFSG.Sporadic.Co1.Module.TwoB.validRows_mulRows hvalid hsv)
        (CFSG.Sporadic.Co1.Module.TwoB.validRows_mulRows hsv hvalid) (h1.trans h2.symm)
    simp only [commR, heq', beq_self_eq_true] at hsc
    exact absurd hsc (by decide)

theorem cG_ne_one :
    cG ≠ 1 := by
  intro h
  have h2 := orderOf_cC
  have : cC = 1 := Subtype.ext h
  rw [this, orderOf_one] at h2
  exact absurd h2 (by decide)

theorem co1_pWitness_cG
    {glob : List (List ℕ)} {s₁ s₂ : List ℕ} {d₁ d₂ : List (List ℕ)} {zh₁ zh₂ : ℕ × ℕ}
    {dec₁ dec₂ : List (List ℕ)} {rd : List (List ℕ)} {re : List ℕ}
    (h : co1Cen2CCheck glob s₁ s₂ d₁ d₂ zh₁ zh₂ dec₁ dec₂ rd re = true) {E : Subgroup GL24}
    (hEG : E ≤ GA) (hE : IsElemAbelian 2 E) (hE4 : 4 ≤ Nat.card E) (hcE : cG ∈ E) :
    PWitness GA E := by
  simp only [co1Cen2CCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hG, hP₁⟩, hP₂⟩, hw⟩, hscan⟩ := h
  obtain ⟨br, hbr⟩ := exists_roots qRep_twoC twoC_q_check
  have htg : List.Forall₂ MRep twoCRoots ((List.range twoCRoots.length).map br) :=
    forall₂_range_of_getD fun i hi => (hbr i hi).2
  have hrep := dag_rep rep_co1Cen2CBase (glob.map Native.decWord) hG
  have hS := List.rel_append (RootWitness.forall₂_entries hrep s₁)
    (RootWitness.forall₂_entries hrep s₂)
  refine RootWitness.pWitness rep_co1Cen2CBase co1Cen2CBaseG_mem hG rep_iotaC cG_ne_one hP₁ hP₂
    (Z := {1, cG}) (fun b hb h₁ h₂ => ?_) hEG hE hcE ?_
  · have hc := RootWitness.comm_of_words rep_co1Cen2CBase hG htg hw h₁ h₂
    have hbQ := mem_twoCQ_of_comm hbr hb fun i hi =>
      hc (br i) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    have hall : ∀ s ∈ (s₁.map (entryG (dagG co1Cen2CBaseG (glob.map Native.decWord))) ++
        s₂.map (entryG (dagG co1Cen2CBaseG (glob.map Native.decWord)))), b * s = s * b :=
      fun s hs => (List.mem_append.mp hs).elim (h₁ s) (h₂ s)
    rcases eq_one_or_eq_cG_of_scan hS hscan hbQ hall with h | h
    · exact Or.inl h
    · exact Or.inr h
  · intro hsub
    have hle : Nat.card E ≤ 2 := by
      have hE' : Nat.card E = (E : Set GL24).ncard := (Nat.card_coe_set_eq _).symm
      rw [hE']
      calc (E : Set GL24).ncard ≤ ({1, cG} : Set GL24).ncard :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ ({cG} : Set GL24).ncard + 1 := Set.ncard_insert_le 1 {cG}
        _ = 2 := by rw [Set.ncard_singleton]
    omega

end CFSG.ComponentClassification.RankTwoSporadic.Co1
