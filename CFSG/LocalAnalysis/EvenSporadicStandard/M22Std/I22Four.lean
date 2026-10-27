module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.I22Check
public import CFSG.Sporadic.Recognition.M22MultiplierInputs

public section

namespace CFSG.EvenSporadicStandard.M22Std

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Bridge.TwoGen
  CFSG.Sporadic.Recognition.M22Multiplier CFSG.Sporadic.Recognition.CoverRecipe
  CFSG.LieType.Multipliers CFSG.QuasithinUnique.Ch1.M22Cover
open CFSG.Monster.B CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Co2 (rep_compA rep_idA eqA_iff eq_of_eqA)
open CFSG.Sporadic.Bridge.TwoGen.Native (relCheck wordTab letterTab)
open CFSG.Sporadic.Schreier.Tits (getElem!_ofFn_of_lt)

@[expose] def i22fParse (s : String) : Table :=
  (((s.splitOn " ").filterMap String.toNat?).map UInt32.ofNat).toArray

@[expose] def i22fAlphaText : String := include_str "I22FourAlpha.txt"

@[expose] def i22fBetaText : String := include_str "I22FourBeta.txt"

@[expose] def i22fN : ℕ := 32256

@[expose] def i22fAlpha (_ : Unit := ()) : Table := i22fParse i22fAlphaText

@[expose] def i22fBeta (_ : Unit := ()) : Table := i22fParse i22fBetaText

@[expose] def i22fPermOK (n : ℕ) (P R : Table) : Bool :=
  allIn 0 n (fun i => decide (ap P i < n) && decide (ap R i < n)) && invOK n P R && invOK n R P

@[expose] def i22fProd (n : ℕ) (gen : ℕ → Table) (w : List ℕ) : Table :=
  w.foldr (fun l T => compT n (gen l) T) (idT n)

@[expose] def i22fVertexTabs (n : ℕ) (tA tB : Table) : Array Table :=
  let gen : ℕ → Table := fun l => if l = 0 then tA else tB
  let tx : Array Table := Array.ofFn (n := 3) fun i => i22fProd n gen (covData.xwOf i)
  Array.ofFn (n := covData.nV) fun v => i22fProd n (fun l => tx[l % 3]!) (covData.words[v]!)

@[expose] def i22fIsInv (ea : Array (Array ℕ)) (v : ℕ) : Bool :=
  !eqA 22 ea[v]! (idA 22) && eqA 22 (compA 22 ea[v]! ea[v]!) (idA 22)

@[expose] def i22fPartner (n : ℕ) (ea : Array (Array ℕ)) (tv : Array Table) (v w : ℕ) : Bool :=
  w != v && eqA 22 (compA 22 ea[v]! ea[w]!) (compA 22 ea[w]! ea[v]!) &&
    compT n tv[v]! tv[w]! == compT n tv[w]! tv[v]!

@[expose] def i22fCount (n : ℕ) (tA tB : Table) : Bool :=
  let tv := i22fVertexTabs n tA tB
  let ea := covData.elaTab
  let invs := (List.range covData.nV).filter (i22fIsInv ea)
  decide ((invs.filter fun v => 14 ≤ (invs.filter (i22fPartner n ea tv v)).length).length ≤ 14)

@[expose] def i22fCheckT (n : ℕ) (α β : Table) : Bool :=
  let αi := invT n α
  let βi := invT n β
  i22fPermOK n α αi && i22fPermOK n β βi &&
    relCheck n α αi β βi ((coverWords m22Rels m22CommWord).map natWord) &&
    i22fCount n (wordTab n α αi β βi (natWord m22SurjA)) (wordTab n α αi β βi (natWord m22SurjB))

@[expose] def i22fCheck (_ : Unit := ()) : Bool :=
  decide (covData.nV = 128) && goodCheck covData covData.elaTab &&
    i22fCheckT i22fN (i22fAlpha ()) (i22fBeta ())

section Sound

variable {n : ℕ}

theorem i22fPermOK_spec {P R : Table} (h : i22fPermOK n P R = true) :
    ∀ i < n, ap P i < n ∧ ap R i < n ∧ ap R (ap P i) = i ∧ ap P (ap R i) = i := by
  unfold i22fPermOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  intro i hi
  have a := allIn_eq_true.1 h1 i (Nat.zero_le _) hi
  have b := allIn_eq_true.1 h2 i (Nat.zero_le _) hi
  have c := allIn_eq_true.1 h3 i (Nat.zero_le _) hi
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at a b c
  exact ⟨a.1, a.2, b, c⟩

theorem i22fPermOK_invOK {P R : Table} (h : i22fPermOK n P R = true) : invOK n P R = true := by
  unfold i22fPermOK at h
  simp only [Bool.and_eq_true] at h
  exact h.1.2

@[expose] noncomputable def i22fTabPerm (n : ℕ) (P R : Table) (h : i22fPermOK n P R = true) :
    Equiv.Perm (Fin n) where
  toFun i := ⟨ap P i, (i22fPermOK_spec h i i.2).1⟩
  invFun i := ⟨ap R i, (i22fPermOK_spec h i i.2).2.1⟩
  left_inv i := Fin.ext (i22fPermOK_spec h i i.2).2.2.1
  right_inv i := Fin.ext (i22fPermOK_spec h i i.2).2.2.2

theorem rep_i22fTabPerm {P R : Table} (h : i22fPermOK n P R = true) :
    Rep n P (i22fTabPerm n P R h) := by
  intro i hi
  rw [idx_of_lt _ hi]
  rfl

theorem i22f_exists_rho {x y : Equiv.Perm (Fin n)} {α αi β βi : Table} (hn : n < 2 ^ 32)
    (hx : Rep n α x) (hxi : Rep n αi x⁻¹) (hy : Rep n β y) (hyi : Rep n βi y⁻¹)
    (h : relCheck n α αi β βi ((coverWords m22Rels m22CommWord).map natWord) = true) :
    ∃ ρ : M22Cover →* Equiv.Perm (Fin n), ∀ w : FreeGroup (Fin 2),
      ρ (PresentedGroup.mk _ w) = FreeGroup.lift (fun i : Fin 2 => img2 x y i.val) w := by
  have hrel := wordProd_eq_one_of_relCheck hn hx hxi hy hyi h
  have hr : ∀ r ∈ coverRelators (wordSet m22Rels) m22CommW,
      FreeGroup.lift (fun i : Fin 2 => img2 x y i.val) r = 1 := by
    intro r hr
    have h1 : r ∈ wordSet (coverWords m22Rels m22CommWord) := by
      rw [← coverRelators_wordSet]
      exact hr
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 h1
    rw [lift_mk_eq_wordProd]
    exact hrel _ (List.mem_map_of_mem hv)
  exact ⟨PresentedGroup.toGroup hr, fun w => rfl⟩

@[expose] noncomputable def i22fAP : M22Cover := PresentedGroup.mk _ (FreeGroup.mk m22SurjA)

@[expose] noncomputable def i22fBP : M22Cover := PresentedGroup.mk _ (FreeGroup.mk m22SurjB)

@[expose] noncomputable def i22fxP (i : Fin 3) : M22Cover :=
  ((covData.xwOf i).map fun l => if l = 0 then i22fAP else i22fBP).prod

@[expose] noncomputable def i22fsig (v : ℕ) : M22Cover :=
  ((covData.words[v]!).map fun l => i22fxP (fo l)).prod

@[expose] def i22fInv (v : ℕ) : Prop := v < covData.nV ∧ i22el v ≠ 1 ∧ i22el v * i22el v = 1

@[expose] def i22fCom (v w : ℕ) : Prop := i22el v * i22el w = i22el w * i22el v

theorem rep_i22fProd {gen : ℕ → Table} {g : ℕ → Equiv.Perm (Fin n)} (hn : n < 2 ^ 32)
    (hgen : ∀ l, Rep n (gen l) (g l)) (w : List ℕ) :
    Rep n (i22fProd n gen w) ((w.map g).prod) := by
  induction w with
  | nil => exact Rep.idT hn
  | cons l w ih =>
    have e : i22fProd n gen (l :: w) = compT n (gen l) (i22fProd n gen w) := rfl
    rw [e, List.map_cons, List.prod_cons]
    exact Rep.compT (hgen l) ih

theorem i22f_tab_eq {T T' : Table} {g h : Equiv.Perm (Fin n)} (hT : Rep n T g) (hT' : Rep n T' h)
    (hs : T.size = n) (hs' : T'.size = n) (e : g = h) : T = T' := by
  refine Array.ext (hs.trans hs'.symm) fun i hi1 hi2 => ?_
  have hin : i < n := hs ▸ hi1
  have h1 := hT i hin
  have h2 := hT' i hin
  rw [e] at h1
  have h3 : (T[i]!).toNat = (T'[i]!).toNat := by
    have := h1.trans h2.symm
    exact this
  have h4 : T[i]! = T'[i]! := UInt32.toNat_inj.1 h3
  rwa [getElem!_pos T i hi1, getElem!_pos T' i hi2] at h4

theorem i22fCount_sound {tA tB : Table} {g : ℕ → Equiv.Perm (Fin n)}
    (hg : ∀ v < covData.nV, Rep n ((i22fVertexTabs n tA tB)[v]!) (g v))
    (h : i22fCount n tA tB = true) (T : Finset ℕ) (hT : T.card = 15)
    (hinv : ∀ v ∈ T, i22fInv v)
    (hcom : ∀ v ∈ T, ∀ w ∈ T, v ≠ w → i22fCom v w ∧ g v * g w = g w * g v) : False := by
  unfold i22fCount at h
  simp only [decide_eq_true_eq] at h
  set tv := i22fVertexTabs n tA tB with htv
  set ea := covData.elaTab with hea
  set invs := (List.range covData.nV).filter (i22fIsInv ea) with hinvs
  have hx : ∀ i, Co2.Rep 22 (covData.xa i) (covData.x i) := fun i => covData.xa_rep i
  have hrep : ∀ v, v < covData.nV → Co2.Rep 22 ea[v]! (i22el v) := fun v hv =>
    covData.rep_el hx hv
  have hmem : ∀ v ∈ T, v ∈ invs := by
    intro v hv
    obtain ⟨hvlt, hne, hsq⟩ := hinv v hv
    rw [hinvs, List.mem_filter]
    refine ⟨List.mem_range.2 hvlt, ?_⟩
    have h1 : eqA 22 ea[v]! (idA 22) = false := by
      rw [Bool.eq_false_iff]
      intro hc
      exact hne ((eqA_iff (hrep v hvlt) rep_idA).1 hc)
    have h2 : eqA 22 (compA 22 ea[v]! ea[v]!) (idA 22) = true :=
      (eqA_iff (rep_compA (hrep v hvlt) (hrep v hvlt)) rep_idA).2 hsq
    simp [i22fIsInv, h1, h2]
  have hdeg : ∀ v ∈ T, 14 ≤ (invs.filter (i22fPartner n ea tv v)).length := by
    intro v hv
    have hvlt := (hinv v hv).1
    have hsub : T.erase v ⊆ (invs.filter (i22fPartner n ea tv v)).toFinset := by
      intro w hw
      rw [Finset.mem_erase] at hw
      obtain ⟨hwv, hw⟩ := hw
      have hwlt := (hinv w hw).1
      rw [List.mem_toFinset, List.mem_filter]
      refine ⟨hmem w hw, ?_⟩
      obtain ⟨hc1, hc2⟩ := hcom v hv w hw (Ne.symm hwv)
      have e1 : (w != v) = true := by simpa using hwv
      have e2 : eqA 22 (compA 22 ea[v]! ea[w]!) (compA 22 ea[w]! ea[v]!) = true :=
        (eqA_iff (rep_compA (hrep v hvlt) (hrep w hwlt))
          (rep_compA (hrep w hwlt) (hrep v hvlt))).2 hc1
      have e3 : (compT n tv[v]! tv[w]! == compT n tv[w]! tv[v]!) = true := by
        have r1 := Rep.compT (hg v hvlt) (hg w hwlt)
        have r2 := Rep.compT (hg w hwlt) (hg v hvlt)
        have := i22f_tab_eq r1 r2 (by simp [compT]) (by simp [compT]) hc2
        rw [this]
        exact beq_self_eq_true _
      simp [i22fPartner, e1, e2, e3]
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hv, hT] at this
    exact this.trans (List.toFinset_card_le _)
  have hsubT : T ⊆ (invs.filter fun v => 14 ≤ (invs.filter (i22fPartner n ea tv v)).length).toFinset := by
    intro v hv
    rw [List.mem_toFinset, List.mem_filter]
    exact ⟨hmem v hv, by simpa using hdeg v hv⟩
  have h1 := Finset.card_le_card hsubT
  rw [hT] at h1
  have h2 := h1.trans (List.toFinset_card_le _)
  omega

theorem i22fCheckT_sound (hn : n < 2 ^ 32) {α β : Table} (h : i22fCheckT n α β = true) :
    ∃ ρ : M22Cover →* Equiv.Perm (Fin n), ∀ T : Finset ℕ, T.card = 15 → (∀ v ∈ T, i22fInv v) →
      (∀ v ∈ T, ∀ w ∈ T, v ≠ w → i22fCom v w ∧
        ρ (i22fsig v) * ρ (i22fsig w) = ρ (i22fsig w) * ρ (i22fsig v)) → False := by
  unfold i22fCheckT at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hpa, hpb⟩, hrel⟩, hcount⟩ := h
  set αi := invT n α with hαi
  set βi := invT n β with hβi
  set x := i22fTabPerm n α αi hpa with hxdef
  set y := i22fTabPerm n β βi hpb with hydef
  have hx : Rep n α x := rep_i22fTabPerm hpa
  have hxi : Rep n αi x⁻¹ := hx.inv_of_invOK (i22fPermOK_invOK hpa)
  have hy : Rep n β y := rep_i22fTabPerm hpb
  have hyi : Rep n βi y⁻¹ := hy.inv_of_invOK (i22fPermOK_invOK hpb)
  obtain ⟨ρ, hρ⟩ := i22f_exists_rho hn hx hxi hy hyi hrel
  refine ⟨ρ, fun T hT hinv hcom => ?_⟩
  set tA := wordTab n α αi β βi (natWord m22SurjA) with htA
  set tB := wordTab n α αi β βi (natWord m22SurjB) with htB
  have hAP : Rep n tA (ρ i22fAP) := by
    rw [i22fAP, hρ, lift_mk_eq_wordProd]
    exact rep_wordTab hn hx hxi hy hyi _
  have hBP : Rep n tB (ρ i22fBP) := by
    rw [i22fBP, hρ, lift_mk_eq_wordProd]
    exact rep_wordTab hn hx hxi hy hyi _
  set gen : ℕ → Table := fun l => if l = 0 then tA else tB with hgen
  have hgenRep : ∀ l, Rep n (gen l) (if l = 0 then ρ i22fAP else ρ i22fBP) := by
    intro l
    by_cases hl : l = 0
    · simp only [hgen, hl, if_true]
      exact hAP
    · simp only [hgen, hl, if_false]
      exact hBP
  have hρAB : ∀ l : ℕ, ρ (if l = 0 then i22fAP else i22fBP) =
      if l = 0 then ρ i22fAP else ρ i22fBP := by
    intro l
    split_ifs <;> rfl
  have htx : ∀ i : Fin 3, Rep n (i22fProd n gen (covData.xwOf i)) (ρ (i22fxP i)) := by
    intro i
    have h1 := rep_i22fProd hn hgenRep (covData.xwOf i)
    have h2 : ρ (i22fxP i) = (((covData.xwOf i).map fun l =>
        if l = 0 then ρ i22fAP else ρ i22fBP)).prod := by
      unfold i22fxP
      rw [map_list_prod, List.map_map]
      congr 1
      exact List.map_congr_left fun l _ => hρAB l
    rw [h2]
    exact h1
  have hvert : ∀ v < covData.nV, Rep n ((i22fVertexTabs n tA tB)[v]!) (ρ (i22fsig v)) := by
    intro v hv
    set tx : Array Table := Array.ofFn (n := 3) fun i => i22fProd n gen (covData.xwOf i) with htxdef
    have htxget : ∀ l : ℕ, tx[l % 3]! = i22fProd n gen (covData.xwOf (fo l)) := by
      intro l
      rw [htxdef]
      exact getElem!_ofFn_of_lt _ (Nat.mod_lt l (by norm_num))
    have hgen2 : ∀ l : ℕ, Rep n ((fun l => tx[l % 3]!) l) (ρ (i22fxP (fo l))) := by
      intro l
      show Rep n (tx[l % 3]!) _
      rw [htxget]
      exact htx (fo l)
    have h1 := rep_i22fProd hn hgen2 (covData.words[v]!)
    have e : (i22fVertexTabs n tA tB)[v]! =
        i22fProd n (fun l => tx[l % 3]!) (covData.words[v]!) := by
      unfold i22fVertexTabs
      exact getElem!_ofFn_of_lt _ hv
    rw [e]
    have h2 : ρ (i22fsig v) = (((covData.words[v]!).map fun l => ρ (i22fxP (fo l)))).prod := by
      unfold i22fsig
      rw [map_list_prod, List.map_map]
      rfl
    rw [h2]
    exact h1
  exact i22fCount_sound hvert hcount T hT hinv hcom

end Sound

theorem i22fCheck_sound (h : i22fCheck () = true) :
    (covData.nV = 128 ∧ covData.tab.Good covData.x) ∧
    ∃ ρ : M22Cover →* Equiv.Perm (Fin i22fN), ∀ T : Finset ℕ, T.card = 15 →
      (∀ v ∈ T, i22fInv v) →
      (∀ v ∈ T, ∀ w ∈ T, v ≠ w → i22fCom v w ∧
        ρ (i22fsig v) * ρ (i22fsig w) = ρ (i22fsig w) * ρ (i22fsig v)) → False := by
  unfold i22fCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hnV, hgood⟩, hT⟩ := h
  exact ⟨⟨hnV, (goodCheck_sound hgood).1⟩, i22fCheckT_sound (by norm_num [i22fN]) hT⟩

end CFSG.EvenSporadicStandard.M22Std
