module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneOddDerivation

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

section ListProd

variable {G ι : Type*} [Group G]

theorem list_prod_map_mul_of_commute (l : List ι) (f g : ι → G)
    (h : ∀ a ∈ l, ∀ b ∈ l, Commute (g a) (f b)) :
    (l.map fun i => f i * g i).prod = (l.map f).prod * (l.map g).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [ih fun x hx y hy => h x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)]
    have hc : Commute (g a) (l.map f).prod :=
      Commute.list_prod_right _ _ fun x hx => by
        obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
        exact h a List.mem_cons_self b (List.mem_cons_of_mem _ hb)
    rw [mul_assoc, ← mul_assoc (g a), hc.eq, mul_assoc, mul_assoc]

theorem list_sum_apply {α M : Type*} [AddMonoid M] (L : List (α → M)) (x : α) :
    L.sum x = (L.map fun f => f x).sum := by
  induction L with
  | nil => rfl
  | cons f L ih => simp [ih]

end ListProd

section RootProd

variable {τ : Tag} {K : Type} [Field K]

variable (τ K) in
@[expose] noncomputable def rootProd (l : List (Fin τ.rank → ℤ)) (c : (Fin τ.rank → ℤ) → K) :
    ModGL τ K :=
  (l.map fun β => pinnedX τ K β (c β)).prod


theorem rootProd_nil (c : (Fin τ.rank → ℤ) → K) : rootProd τ K [] c = 1 := rfl

theorem rootProd_cons (β : Fin τ.rank → ℤ) (l : List (Fin τ.rank → ℤ))
    (c : (Fin τ.rank → ℤ) → K) :
    rootProd τ K (β :: l) c = pinnedX τ K β (c β) * rootProd τ K l c := by
  simp [rootProd]

theorem rootProd_append (l l' : List (Fin τ.rank → ℤ)) (c : (Fin τ.rank → ℤ) → K) :
    rootProd τ K (l ++ l') c = rootProd τ K l c * rootProd τ K l' c := by
  simp [rootProd]

theorem rootProd_congr {l : List (Fin τ.rank → ℤ)} {c d : (Fin τ.rank → ℤ) → K}
    (h : ∀ β ∈ l, c β = d β) : rootProd τ K l c = rootProd τ K l d := by
  simp only [rootProd]
  congr 1
  exact List.map_congr_left fun β hβ => by rw [h β hβ]

theorem rootProd_zero (l : List (Fin τ.rank → ℤ)) : rootProd τ K l 0 = 1 := by
  simp [rootProd, pinnedX_zero]

@[expose] def RootCommFamily (τ : Tag) (K : Type) [Field K] (l : List (Fin τ.rank → ℤ)) : Prop :=
  ∀ β ∈ l, ∀ β' ∈ l, ∀ s t : K, Commute (pinnedX τ K β s) (pinnedX τ K β' t)

theorem RootCommFamily.commute_rootProd {l : List (Fin τ.rank → ℤ)} (hl : RootCommFamily τ K l)
    {β : Fin τ.rank → ℤ} (hβ : β ∈ l) (s : K) (c : (Fin τ.rank → ℤ) → K) :
    Commute (pinnedX τ K β s) (rootProd τ K l c) :=
  Commute.list_prod_right _ _ fun x hx => by
    obtain ⟨β', hβ', rfl⟩ := List.mem_map.1 hx
    exact hl β hβ β' hβ' s _

theorem RootCommFamily.of_sublist {l l' : List (Fin τ.rank → ℤ)} (hl : RootCommFamily τ K l)
    (h : ∀ β ∈ l', β ∈ l) : RootCommFamily τ K l' :=
  fun β hβ β' hβ' s t => hl β (h β hβ) β' (h β' hβ') s t

theorem rootProd_add {l : List (Fin τ.rank → ℤ)} (hl : RootCommFamily τ K l)
    (c d : (Fin τ.rank → ℤ) → K) :
    rootProd τ K l (c + d) = rootProd τ K l c * rootProd τ K l d := by
  simp only [rootProd, Pi.add_apply, pinnedX_add]
  exact list_prod_map_mul_of_commute l _ _ fun a ha b hb => hl a ha b hb _ _

theorem rootProd_list_sum {l : List (Fin τ.rank → ℤ)} (hl : RootCommFamily τ K l)
    (L : List ((Fin τ.rank → ℤ) → K)) :
    rootProd τ K l L.sum = (L.map (rootProd τ K l)).prod := by
  induction L with
  | nil => exact rootProd_zero l
  | cons c L ih => rw [List.sum_cons, rootProd_add hl, ih, List.map_cons, List.prod_cons]

theorem rootProd_ite_mem (l M : List (Fin τ.rank → ℤ)) (c : (Fin τ.rank → ℤ) → K) :
    rootProd τ K l (fun ρ => if ρ ∈ M then c ρ else 0) = rootProd τ K (l.filter (· ∈ M)) c := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases ha : a ∈ M
    · rw [List.filter_cons_of_pos (by simpa using ha), rootProd_cons, rootProd_cons, ih,
        ite_eq_left ha]
    · rw [List.filter_cons_of_neg (by simpa using ha), rootProd_cons, ih, ite_eq_right ha,
        pinnedX_zero, one_mul]

theorem rootProd_perm {l l' : List (Fin τ.rank → ℤ)} (hl : RootCommFamily τ K l) (h : l.Perm l')
    (c : (Fin τ.rank → ℤ) → K) : rootProd τ K l c = rootProd τ K l' c := by
  simp only [rootProd]
  refine (h.map _).prod_eq' ?_
  refine List.Pairwise.map _ (fun a b hab => hab) ?_
  exact List.pairwise_of_forall_mem_list fun a ha b hb => hl a ha b hb _ _

theorem rootProd_single {l : List (Fin τ.rank → ℤ)} (hnd : l.Nodup) {ρ : Fin τ.rank → ℤ}
    (hρ : ρ ∈ l) (s : K) : rootProd τ K l (Pi.single ρ s) = pinnedX τ K ρ s := by
  induction l with
  | nil => simp at hρ
  | cons a l ih =>
    rw [List.nodup_cons] at hnd
    rw [rootProd_cons]
    by_cases ha : a = ρ
    · subst ha
      rw [Pi.single_eq_same, ← mul_one (pinnedX τ K a s)]
      congr 1
      calc rootProd τ K l (Pi.single a s) = rootProd τ K l 0 :=
            rootProd_congr fun β hβ => by
              rw [Pi.zero_apply]
              exact Pi.single_eq_of_ne (fun h : β = a => hnd.1 (h ▸ hβ)) _
        _ = 1 := rootProd_zero l
    · rw [Pi.single_eq_of_ne ha, pinnedX_zero, one_mul]
      exact ih hnd.2 ((List.mem_cons.1 hρ).resolve_left (Ne.symm ha))

theorem list_sum_single_apply {l : List (Fin τ.rank → ℤ)} (hnd : l.Nodup)
    {ρ : Fin τ.rank → ℤ} (hρ : ρ ∈ l) (c : (Fin τ.rank → ℤ) → K) :
    (l.map fun β => (Pi.single β (c β) : (Fin τ.rank → ℤ) → K) ρ).sum = c ρ := by
  induction l with
  | nil => simp at hρ
  | cons a l ih =>
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.sum_cons]
    by_cases ha : a = ρ
    · subst ha
      rw [Pi.single_eq_same]
      have h0 : (l.map fun β => (Pi.single β (c β) : (Fin τ.rank → ℤ) → K) a).sum = 0 :=
        List.sum_eq_zero fun x hx => by
          obtain ⟨β, hβ, rfl⟩ := List.mem_map.1 hx
          exact Pi.single_eq_of_ne (fun h : a = β => hnd.1 (h ▸ hβ)) _
      rw [h0, add_zero]
    · rw [Pi.single_eq_of_ne (Ne.symm ha), zero_add]
      exact ih hnd.2 ((List.mem_cons.1 hρ).resolve_left (Ne.symm ha))

theorem rootProd_injective {l : List (Fin τ.rank → ℤ)} (hnd : l.Nodup)
    (hpos : ∀ β ∈ l, IsRoot τ β ∧ 0 < height β) {c d : (Fin τ.rank → ℤ) → K}
    (h : rootProd τ K l c = rootProd τ K l d) : ∀ β ∈ l, c β = d β :=
  pinnedX_list_prod_injective l hnd hpos c d h

theorem conj_rootProd_of_mem_torusGroup {h : ModGL τ K} (hh : h ∈ torusGroup τ K)
    {l : List (Fin τ.rank → ℤ)} (hl : ∀ β ∈ l, IsRoot τ β) (c : (Fin τ.rank → ℤ) → K) :
    h * rootProd τ K l c * h⁻¹ = rootProd τ K l (fun β => torusRootChar h β * c β) := by
  induction l with
  | nil => simp [rootProd]
  | cons a l ih =>
    rw [rootProd_cons, rootProd_cons, ← conj_pinnedX_of_mem_torusGroup hh
      (hl a List.mem_cons_self) (c a), ← ih fun β hβ => hl β (List.mem_cons_of_mem _ hβ)]
    group

@[expose] noncomputable def conjCoeff (α : Fin τ.rank → ℤ) (t : K) (l : List (Fin τ.rank → ℤ))
    (c : (Fin τ.rank → ℤ) → K) : (Fin τ.rank → ℤ) → K := by
  classical
  exact (l.map fun β => Pi.single β (c β) +
    if α ≠ β ∧ IsRoot τ (α + β) then Pi.single (α + β) (t * c β) else 0).sum

theorem conj_rootProd (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (h2 : (2 : K) = 0)
    {l : List (Fin τ.rank → ℤ)} (hnd : l.Nodup) (hlr : ∀ β ∈ l, IsRoot τ β)
    (hl : RootCommFamily τ K l) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hαl : ∀ β ∈ l, α ≠ -β ∧ (IsRoot τ (α + β) → α + β ∈ l)) (t : K)
    (c : (Fin τ.rank → ℤ) → K) :
    pinnedX τ K α t * rootProd τ K l c * (pinnedX τ K α t)⁻¹ =
      rootProd τ K l (conjCoeff α t l c) := by
  classical
  have hfac : ∀ β ∈ l, pinnedX τ K α t * pinnedX τ K β (c β) * (pinnedX τ K α t)⁻¹ =
      rootProd τ K l (Pi.single β (c β) +
        if α ≠ β ∧ IsRoot τ (α + β) then Pi.single (α + β) (t * c β) else 0) := by
    intro β hβ
    rw [rootProd_add hl, rootProd_single hnd hβ]
    by_cases hc : α ≠ β ∧ IsRoot τ (α + β)
    · rw [ite_eq_left hc, rootProd_single hnd ((hαl β hβ).2 hc.2)]
      have hcomm := CFSG.SeitzReduction.commutatorElement_pinnedX_of_oddDerivLaced h2
        (CFSG.SeitzReduction.oddDerivLacedCheck_of_simplyLaced hτ) hα (hlr β hβ) hc.1
        (hαl β hβ).1 hc.2 t (c β)
      rw [commutatorElement_def] at hcomm
      have hc2 : Commute (pinnedX τ K β (c β)) (pinnedX τ K (α + β) (t * c β)) :=
        hl β hβ _ ((hαl β hβ).2 hc.2) _ _
      rw [hc2.eq, ← hcomm]
      group
    · rw [ite_eq_right hc, rootProd_zero, mul_one]
      by_cases hab : α = β
      · subst hab
        rw [pinnedX_neg, ← pinnedX_add, ← pinnedX_add]
        congr 1
        ring
      · have hnr : ¬IsRoot τ (α + β) := fun hr => hc ⟨hab, hr⟩
        have hcm := CFSG.SeitzReduction.commute_pinnedX_of_oddDeriv hα (hlr β hβ) (hαl β hβ).1
          hnr t (c β)
        rw [hcm.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hconj : pinnedX τ K α t * rootProd τ K l c * (pinnedX τ K α t)⁻¹ =
      (l.map fun β => pinnedX τ K α t * pinnedX τ K β (c β) * (pinnedX τ K α t)⁻¹).prod := by
    have := map_list_prod (MulAut.conj (pinnedX τ K α t))
      (l.map fun β => pinnedX τ K β (c β))
    simpa [rootProd, List.map_map, Function.comp_def] using this
  rw [hconj, List.map_congr_left hfac, conjCoeff, rootProd_list_sum hl, List.map_map]
  rfl

theorem conjCoeff_apply_of_forall {l : List (Fin τ.rank → ℤ)} (hnd : l.Nodup)
    {α : Fin τ.rank → ℤ} (t : K) (c : (Fin τ.rank → ℤ) → K) {ρ : Fin τ.rank → ℤ} (hρ : ρ ∈ l)
    (h : ∀ β ∈ l, α + β = ρ → c β = 0) : conjCoeff α t l c ρ = c ρ := by
  classical
  rw [conjCoeff, list_sum_apply, List.map_map]
  have e : ∀ β ∈ l, ((fun f : (Fin τ.rank → ℤ) → K => f ρ) ∘ fun β => Pi.single β (c β) +
      if α ≠ β ∧ IsRoot τ (α + β) then Pi.single (α + β) (t * c β) else 0) β =
      (Pi.single β (c β) : (Fin τ.rank → ℤ) → K) ρ := by
    intro β hβ
    simp only [Function.comp_apply, Pi.add_apply]
    split_ifs with hc
    · by_cases he : α + β = ρ
      · simp [h β hβ he]
      · rw [Pi.single_eq_of_ne (Ne.symm he), add_zero]
    · rw [Pi.zero_apply, add_zero]
  rw [List.map_congr_left e]
  exact list_sum_single_apply hnd hρ c

theorem mem_and_eq_of_rootProd_eq {L M : List (Fin τ.rank → ℤ)} (hLnd : L.Nodup)
    (hLr : ∀ β ∈ L, IsRoot τ β) (hL : RootCommFamily τ K L) (hMnd : M.Nodup)
    (hMpos : ∀ ρ ∈ M, IsRoot τ ρ ∧ 0 < height ρ) (hM : RootCommFamily τ K M)
    {c d : (Fin τ.rank → ℤ) → K} (h : rootProd τ K L c = rootProd τ K M d)
    {β : Fin τ.rank → ℤ} (hβL : β ∈ L) (hcβ : c β ≠ 0) : β ∈ M ∧ d β = c β := by
  classical
  set Lp := L.filter fun β => decide (0 < height β) with hLp
  set Ln := L.filter fun β => !decide (0 < height β) with hLn
  have hperm : L.Perm (Lp ++ Ln) := (List.filter_append_perm _ L).symm
  have hsplit : rootProd τ K L c = rootProd τ K Lp c * rootProd τ K Ln c := by
    rw [rootProd_perm hL hperm, rootProd_append]
  have hLpL : ∀ x ∈ Lp, x ∈ L := fun x hx => List.mem_of_mem_filter hx
  have hLnL : ∀ x ∈ Ln, x ∈ L := fun x hx => List.mem_of_mem_filter hx
  have hneg : ∀ x ∈ Ln, IsRoot τ x ∧ height x < 0 := by
    intro x hx
    have hx' := List.mem_filter.1 hx
    refine ⟨hLr x hx'.1, ?_⟩
    rcases IsRoot.height_pos_or_neg (hLr x hx'.1) with hp | hn
    · simp [hp] at hx'
    · exact hn
  have hXU : rootProd τ K Ln c ∈ negUnipotent τ K := by
    refine list_prod_mem fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact pinnedX_mem_rootSpan (S := {α | IsRoot τ α ∧ height α < 0}) (hneg x hx) _
  have hposU : ∀ (l : List (Fin τ.rank → ℤ)), (∀ x ∈ l, IsRoot τ x ∧ 0 < height x) →
      ∀ e : (Fin τ.rank → ℤ) → K, rootProd τ K l e ∈ posUnipotent τ K := by
    intro l hl e
    refine list_prod_mem fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact pinnedX_mem_rootSpan (S := {α | IsRoot τ α ∧ 0 < height α}) (hl x hx) _
  have hLppos : ∀ x ∈ Lp, IsRoot τ x ∧ 0 < height x := by
    intro x hx
    have hx' := List.mem_filter.1 hx
    exact ⟨hLr x hx'.1, by simpa using hx'.2⟩
  have hXB : rootProd τ K Ln c ∈ borelGroup τ K := by
    have e : rootProd τ K Ln c = (rootProd τ K Lp c)⁻¹ * rootProd τ K M d := by
      rw [← h, hsplit, inv_mul_cancel_left]
    rw [e]
    exact Subgroup.mem_sup_right (mul_mem (inv_mem (hposU Lp hLppos c)) (hposU M hMpos d))
  have hX1 : rootProd τ K Ln c = 1 := by
    have hm : rootProd τ K Ln c ∈ borelGroup τ K ⊓ negUnipotent τ K := Subgroup.mem_inf.2 ⟨hXB, hXU⟩
    rwa [borelGroup_inf_negUnipotent, Subgroup.mem_bot] at hm
  have hc0 : ∀ x ∈ Ln, c x = 0 := by
    have := CFSG.LieType.Ree.pinnedX_list_prod_injective_neg Ln (hLnd.filter _) hneg c 0
      (by rw [show (Ln.map fun α => pinnedX τ K α (c α)).prod = rootProd τ K Ln c from rfl, hX1]
          exact (rootProd_zero Ln).symm)
    simpa using this
  have hβp : β ∈ Lp := by
    rcases List.mem_append.1 (hperm.subset hβL) with hp | hn
    · exact hp
    · exact absurd (hc0 β hn) hcβ
  have hEq : rootProd τ K Lp c = rootProd τ K M d := by rw [← h, hsplit, hX1, mul_one]
  set M' := M.filter fun ρ => !decide (ρ ∈ Lp) with hM'
  set N := Lp ++ M' with hN
  have hM'M : ∀ x ∈ M', x ∈ M := fun x hx => List.mem_of_mem_filter hx
  have hNnd : N.Nodup := by
    refine List.nodup_append.2 ⟨hLnd.filter _, hMnd.filter _, fun a ha b hb hab => ?_⟩
    subst hab
    have := (List.mem_filter.1 hb).2
    simp [ha] at this
  have hNpos : ∀ x ∈ N, IsRoot τ x ∧ 0 < height x := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hLppos x hx
    · exact hMpos x (hM'M x hx)
  have hc' : rootProd τ K N (fun ρ => if ρ ∈ Lp then c ρ else 0) = rootProd τ K Lp c := by
    rw [rootProd_append, rootProd_ite_mem, rootProd_ite_mem]
    have e1 : Lp.filter (· ∈ Lp) = Lp := List.filter_eq_self.2 fun a ha => by simpa using ha
    have e2 : M'.filter (· ∈ Lp) = [] := List.filter_eq_nil_iff.2 fun a ha => by
      have := (List.mem_filter.1 ha).2
      simpa using this
    rw [e1, e2, rootProd_nil, mul_one]
  have hd' : rootProd τ K N (fun ρ => if ρ ∈ M then d ρ else 0) = rootProd τ K M d := by
    rw [rootProd_ite_mem, List.filter_append]
    have e2 : M'.filter (· ∈ M) = M' := List.filter_eq_self.2 fun a ha => by simpa using hM'M a ha
    rw [e2]
    refine (rootProd_perm (hM.of_sublist fun x hx => ?_) ?_ d)
    · rcases List.mem_append.1 hx with hx | hx
      · exact by simpa using (List.mem_filter.1 hx).2
      · exact hM'M x hx
    · have hnd1 : (Lp.filter (· ∈ M) ++ M').Nodup := by
        refine List.nodup_append.2 ⟨(hLnd.filter _).filter _, hMnd.filter _, ?_⟩
        intro a ha b hb hab
        subst hab
        have h1 : a ∈ Lp := List.mem_of_mem_filter ha
        have h2 := (List.mem_filter.1 hb).2
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h2
        exact h2 h1
      rw [List.perm_ext_iff_of_nodup hnd1 hMnd]
      intro a
      constructor
      · intro ha
        rcases List.mem_append.1 ha with ha | ha
        · exact of_decide_eq_true (List.mem_filter.1 ha).2
        · exact hM'M a ha
      · intro ha
        by_cases hp : a ∈ Lp
        · exact List.mem_append_left _ (List.mem_filter.2 ⟨hp, decide_eq_true ha⟩)
        · refine List.mem_append_right _ (List.mem_filter.2 ⟨ha, ?_⟩)
          simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
          exact hp
  have hinj := rootProd_injective hNnd hNpos (hc'.trans (hEq.trans hd'.symm)) β
    (List.mem_append_left _ hβp)
  simp only [ite_eq_left hβp] at hinj
  by_cases hβM : β ∈ M
  · rw [ite_eq_left hβM] at hinj
    exact ⟨hβM, hinj.symm⟩
  · rw [ite_eq_right hβM] at hinj
    exact absurd hinj hcβ

end RootProd

end CFSG.SeitzReduction.E6Pilot
