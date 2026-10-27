module

public import CFSG.GF2Type.Smith1979W3.Cert690.Check
public import CFSG.GF2Type.Smith1979W3.Cert690.Dict

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3.Cert690

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62

theorem omega0_false_eq_codeSubgroup_a8Gens {E : List ℕ} (h : EnumCert a8Gens E)
    (hlen : E.length = 20160) : Ω₀ false = codeSubgroup a8Gens := by
  have hgen : a8Gens = (omegaWords false).map wordC := omegaWords_code_false.symm
  have hle : codeSubgroup a8Gens ≤ Ω₀ false := by
    rw [hgen]
    exact codeSubgroup_map_wordC_le_omega _ (omegaWords_letters false) (omegaWords_even false)
  have hcard : Nat.card (codeSubgroup a8Gens) = Nat.card (Ω₀ false) := by
    rw [h.natCard, hlen, natCard_Ω₀]
    rfl
  exact (eq_of_le_of_natCard hle hcard).symm

theorem a8Data_witMap : (a8Data ()).witMap = witMapOf (a8Data ()).wits :=
  by simp only [a8Data]

theorem a8Data_theta : (a8Data ()).theta = repThetas (a8Data ()).reps :=
  by simp only [a8Data]

theorem a8Data_root : (a8Data ()).root = repRoot (a8Data ()).innTabs (a8Data ()).theta :=
  by simp only [a8Data]

theorem a8Data_innTabs : (a8Data ()).innTabs = innTabs () :=
  by simp only [a8Data]

theorem a8Data_qmulFlat : (a8Data ()).qmulFlat = qmulFlat () :=
  by simp only [a8Data]

theorem a8Data_involutions : (a8Data ()).involutions = invsOf (a8Data ()).elems :=
  by simp only [a8Data]

theorem pglSquareData_pgl : (pglSquareData ()).pgl = pglData () :=
  by simp only [pglSquareData]

theorem pglSquareData_witMap :
    (pglSquareData ()).witMap = witMapOf (pglSquareData ()).wits :=
  by simp only [pglSquareData]

theorem pglSquareData_theta :
    (pglSquareData ()).theta = repThetas (pglSquareData ()).reps :=
  by simp only [pglSquareData]

theorem pglSquareData_root :
    (pglSquareData ()).root = repRoot (pglSquareData ()).innTabs (pglSquareData ()).theta :=
  by simp only [pglSquareData]

theorem pglSquareData_innTabs : (pglSquareData ()).innTabs = innTabs () :=
  by simp only [pglSquareData]

theorem pglSquareData_qmulFlat : (pglSquareData ()).qmulFlat = qmulFlat () :=
  by simp only [pglSquareData]

theorem ncard_image_filter {α β : Type*} {L : List α} (hL : L.Nodup) {F : α → β}
    (hF : ∀ a ∈ L, ∀ a' ∈ L, F a = F a' → a = a') (P : α → Bool) :
    (F '' {a | a ∈ L ∧ P a = true}).ncard = (L.filter P).length := by
  classical
  have hinj : Set.InjOn F {a | a ∈ L ∧ P a = true} :=
    fun a ha a' ha' h => hF a ha.1 a' ha'.1 h
  rw [hinj.ncard_image]
  have hset : {a | a ∈ L ∧ P a = true} = ((L.filter P).toFinset : Set α) := by
    ext a
    simp
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup (hL.filter P)]

private theorem witMap_insert_get? {m : Std.HashMap ℕ SqWit} {k a : ℕ} {v w : SqWit}
    (h : (m.insert k v).get? a = some w) : (w = v ∧ a = k) ∨ m.get? a = some w := by
  rw [Std.HashMap.get?_insert] at h
  by_cases hk : (k == a) = true
  · rw [if_pos hk] at h
    exact Or.inl ⟨(Option.some.inj h).symm, (beq_iff_eq.mp hk).symm⟩
  · rw [if_neg hk] at h
    exact Or.inr h

private theorem witMapOf_list_get? (data : List (Option SqWit)) (m : Std.HashMap ℕ SqWit)
    {g : ℕ} {w : SqWit} :
    (data.foldl (fun (m : Std.HashMap ℕ SqWit) o => match o with
        | some w => m.insert w.g w
        | none => m) m).get? g = some w →
      m.get? g = some w ∨ (w.g = g ∧ some w ∈ data) := by
  induction data generalizing m with
  | nil => intro h; exact Or.inl h
  | cons a l ih =>
    intro h
    cases a with
    | none =>
      rcases ih m (by simpa using h) with h0 | ⟨hg, hmem⟩
      · exact Or.inl h0
      · exact Or.inr ⟨hg, List.mem_cons_of_mem _ hmem⟩
    | some w0 =>
      have h2 : (l.foldl (fun (m : Std.HashMap ℕ SqWit) o => match o with
          | some w => m.insert w.g w
          | none => m) (m.insert w0.g w0)).get? g = some w := by
        rw [List.foldl_cons] at h
        simpa using h
      rcases ih (m.insert w0.g w0) h2 with h0 | ⟨hg, hmem⟩
      · rcases witMap_insert_get? h0 with ⟨hw, hk⟩ | h0
        · subst hw
          subst hk
          exact Or.inr ⟨rfl, List.mem_cons_self⟩
        · exact Or.inl h0
      · exact Or.inr ⟨hg, List.mem_cons_of_mem _ hmem⟩

theorem witMapOf_get?_eq_some {data : Array (Option SqWit)} {g : ℕ} {w : SqWit}
    (h : (witMapOf data).get? g = some w) : w.g = g ∧ some w ∈ data := by
  have h' : (data.toList.foldl (fun (m : Std.HashMap ℕ SqWit) o => match o with
      | some w => m.insert w.g w
      | none => m) {}).get? g = some w := by
    rw [Array.foldl_toList]
    exact h
  rcases witMapOf_list_get? data.toList {} h' with h0 | ⟨hg, hmem⟩
  · simp at h0
  · exact ⟨hg, Array.mem_toList_iff.mp hmem⟩

theorem witOK_spec {E : Array ℕ} {invMap : Std.HashMap ℕ ℕ} {reps : Array ℕ}
    {theta : Array (Array ℕ)} {invs : Array ℕ} {wits : Array (Option SqWit)}
    (h : witOK E invMap reps theta invs wits = true) {w : SqWit} (hw : some w ∈ wits) :
    w.g ∈ invs ∧ w.k ∈ E ∧ w.repIdx < reps.size ∧ w.repIdx < theta.size ∧
      Code.mul w.k (invMap.getD w.k 0) = Code.one ∧ w.psi = liftTab w.k 0 ∧
      w.tp = compTab (compTab w.psi theta[w.repIdx]!) (invTab w.psi) ∧
      w.itp = invTab w.tp ∧
      Code.mul (Code.mul w.k reps[w.repIdx]!) (invMap.getD w.k 0) = w.g := by
  simp only [witOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hsize, hall⟩ := h
  obtain ⟨j, hj, hjw⟩ := Array.mem_iff_getElem.mp hw
  have hjw' : wits[j]! = some w := by
    rw [getElem!_pos wits j hj]
    exact hjw
  have hj2 : j < invs.size := hsize ▸ hj
  have hspec := List.all_eq_true.mp hall j (List.mem_range.mpr hj2)
  simp only [hjw', Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hspec
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hga, hEk⟩, hrep⟩, hthe⟩, hkmul⟩, hpsi⟩, htp⟩, hitp⟩, hkrep⟩ := hspec
  refine ⟨?_, Array.contains_iff_mem.mp hEk, hrep, hthe, hkmul, hpsi, htp, hitp, hkrep⟩
  rw [hga, getElem!_pos invs j hj2]
  exact Array.getElem_mem hj2

theorem rootsOK_spec {IT : Array (Array ℕ)} {theta : Array (Array ℕ)}
    (h : rootsOK IT theta = true) {i : ℕ} (hi : i < theta.size) (e : ℕ) :
    e ∈ innRoots IT (compTab theta[i]! theta[i]!) ↔
      e = (repRoot IT theta)[i]! ∨ e = qmulN (repRoot IT theta)[i]! z0N := by
  have hspec : ((innRoots IT (compTab theta[i]! theta[i]!)).length == 2 &&
      (innRoots IT (compTab theta[i]! theta[i]!)).contains (repRoot IT theta)[i]! &&
      (innRoots IT (compTab theta[i]! theta[i]!)).filter
        (fun e => e != (repRoot IT theta)[i]!) ==
          [qmulN (repRoot IT theta)[i]! z0N]) = true := by
    have h1 := Array.all_eq_true.mp (by simpa only [rootsOK] using h) i (by simpa using hi)
    simpa using h1
  simp only [Bool.and_eq_true, beq_iff_eq] at hspec
  obtain ⟨⟨hlen, hcont⟩, hfil⟩ := hspec
  have hrmem : (repRoot IT theta)[i]! ∈ innRoots IT (compTab theta[i]! theta[i]!) :=
    List.contains_iff_mem.mp hcont
  constructor
  · intro he
    by_cases hre : e = (repRoot IT theta)[i]!
    · exact Or.inl hre
    · refine Or.inr ?_
      have hne : (e != (repRoot IT theta)[i]!) = true := bne_iff_ne.mpr hre
      have hmem : e ∈ (innRoots IT (compTab theta[i]! theta[i]!)).filter
          (fun e => e != (repRoot IT theta)[i]!) := List.mem_filter.mpr ⟨he, hne⟩
      rw [hfil] at hmem
      exact List.mem_singleton.mp hmem
  · rintro (rfl | rfl)
    · exact hrmem
    · have hmem : qmulN (repRoot IT theta)[i]! z0N ∈
          (innRoots IT (compTab theta[i]! theta[i]!)).filter
            (fun e => e != (repRoot IT theta)[i]!) := by
        rw [hfil]
        exact List.mem_singleton_self _
      exact (List.mem_filter.mp hmem).1

theorem isInvCode_iff {x : ℕ} :
    isInvCode x = true ↔ x ≠ Code.one ∧ Code.mul x x = Code.one := by
  simp only [isInvCode, Bool.and_eq_true, bne_iff_ne, beq_iff_eq]

theorem mem_involutions_iff_of_pglInvolutionsOK {D : PGLData}
    (h : pglInvolutionsOK D = true) {x : ℕ} :
    x ∈ D.involutions ↔ x ∈ D.elems ∧ isInvCode x = true := by
  simp only [pglInvolutionsOK, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  constructor
  · intro hx
    have hxE : x ∈ D.elems :=
      Array.contains_iff_mem.mp (Array.all_eq_true_iff_forall_mem.mp h2 x hx)
    have hxc : D.involutions.contains x = true := Array.contains_eq_true_of_mem hx
    have h1x := Array.all_eq_true_iff_forall_mem.mp h1 x hxE
    rw [beq_iff_eq] at h1x
    exact ⟨hxE, by rw [h1x]; exact hxc⟩
  · rintro ⟨hxE, hxinv⟩
    have h1x := Array.all_eq_true_iff_forall_mem.mp h1 x hxE
    rw [beq_iff_eq] at h1x
    exact Array.contains_iff_mem.mp (by rw [← h1x]; exact hxinv)

theorem mem_outers_iff_of_pglOutersOK {D : PGLData} (h : pglOutersOK D = true) {x : ℕ} :
    x ∈ D.outers ↔ x ∈ D.elems ∧ isInvCode x = true ∧ x ∉ D.elems0 := by
  simp only [pglOutersOK, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  constructor
  · intro hx
    have hxE : x ∈ D.elems :=
      Array.contains_iff_mem.mp (Array.all_eq_true_iff_forall_mem.mp h2 x hx)
    have h1x := Array.all_eq_true_iff_forall_mem.mp h1 x hxE
    rw [beq_iff_eq] at h1x
    have hxc : D.outers.contains x = true := Array.contains_eq_true_of_mem hx
    have hboth : (isInvCode x && !(D.elems0.contains x)) = true := by
      rw [h1x]; exact hxc
    obtain ⟨hi, hnot⟩ := Bool.and_eq_true_iff.mp hboth
    have hnot' : D.elems0.contains x = false := by simpa using hnot
    refine ⟨hxE, hi, ?_⟩
    intro hx0
    rw [Array.contains_eq_true_of_mem hx0] at hnot'
    simp at hnot'
  · rintro ⟨hxE, hi, hx0⟩
    have h1x := Array.all_eq_true_iff_forall_mem.mp h1 x hxE
    rw [beq_iff_eq] at h1x
    have hboth : (isInvCode x && !(D.elems0.contains x)) = true := by
      rw [hi]
      cases hc : D.elems0.contains x with
      | false => rfl
      | true => exact absurd (Array.contains_iff_mem.mp hc) hx0
    have hxc : D.outers.contains x = true := by
      rw [← h1x]; exact hboth
    exact Array.contains_iff_mem.mp hxc

theorem mem_involutions_iff_of_a8InvolutionsOK {D : A8Data} (h : a8InvolutionsOK D = true)
    {x : ℕ} : x ∈ D.involutions ↔ x ∈ D.elems ∧ isInvCode x = true := by
  simp only [a8InvolutionsOK, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  constructor
  · intro hx
    have hxE : x ∈ D.elems :=
      Array.contains_iff_mem.mp (Array.all_eq_true_iff_forall_mem.mp h2 x hx)
    have hxc : D.involutions.contains x = true := Array.contains_eq_true_of_mem hx
    have h1x := Array.all_eq_true_iff_forall_mem.mp h1 x hxE
    rw [beq_iff_eq] at h1x
    exact ⟨hxE, by rw [h1x]; exact hxc⟩
  · rintro ⟨hxE, hxinv⟩
    have h1x := Array.all_eq_true_iff_forall_mem.mp h1 x hxE
    rw [beq_iff_eq] at h1x
    exact Array.contains_iff_mem.mp (by rw [← h1x]; exact hxinv)

theorem nodup_one_append_invsOf {E : Array ℕ} (hE : E.toList.Nodup) :
    (#[Code.one] ++ invsOf E).toList.Nodup := by
  have h1 : (#[Code.one] ++ invsOf E).toList =
      Code.one :: (E.toList.filter fun x => isInvCode x) := by
    simp [invsOf]
  rw [h1]
  refine List.nodup_cons.mpr ⟨?_, hE.filter _⟩
  intro hx
  have hx' := (List.mem_filter.mp hx).2
  simp only [isInvCode, Bool.and_eq_true, bne_iff_ne] at hx'
  exact hx'.1 rfl

theorem pglS1Of_spec {D : PGLSquareData} (h : pglS1Of D = true) :
    pglInvolutionsOK D.pgl = true ∧ D.reps.size = 2 ∧
      (∀ r ∈ D.reps, r ∈ D.pgl.elems ∧ isInvCode r = true) ∧ D.reps[0]! ∈ D.pgl.elems0 ∧
      D.reps[1]! ∉ D.pgl.elems0 ∧ (∀ o ∈ D.wits, o.isSome = true) ∧
      witOK D.pgl.elems D.pgl.invMap D.reps D.theta D.pgl.involutions D.wits = true := by
  simp only [pglS1Of, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, _⟩, _⟩, h8⟩, h9⟩ := h
  have h5' : D.pgl.elems0.contains (D.reps[1]!) = false := by simpa using h5
  refine ⟨h1, h2, ?_, Array.contains_iff_mem.mp h4, ?_, ?_, h9⟩
  · intro r hr
    obtain ⟨hr1, hr2⟩ := Bool.and_eq_true_iff.mp (Array.all_eq_true_iff_forall_mem.mp h3 r hr)
    exact ⟨Array.contains_iff_mem.mp hr1, hr2⟩
  · intro hx
    rw [Array.contains_eq_true_of_mem hx] at h5'
    simp at h5'
  · intro o ho
    exact Array.all_eq_true_iff_forall_mem.mp h8 o ho

theorem pglS2Of_spec {D : PGLSquareData} (h : pglS2Of D = true) :
    (∀ t ∈ D.theta, isHomTabWith D.qmulFlat t = true) ∧ rootsOK D.innTabs D.theta = true := by
  simp only [pglS2Of, Bool.and_eq_true] at h
  exact ⟨Array.all_eq_true_iff_forall_mem.mp h.1, h.2⟩

theorem pglS3Of_spec {D : PGLSquareData} (h : pglS3Of D = true) :
    (∀ g ∈ D.pgl.involutions, ∀ f < 64, isHomTabWith D.qmulFlat (liftTab g f) = true) ∧
      ∀ w : SqWit, some w ∈ D.wits → isHomTabWith D.qmulFlat w.psi = true := by
  simp only [pglS3Of, Bool.and_eq_true] at h
  obtain ⟨⟨⟨_, _⟩, h3⟩, h4⟩ := h
  refine ⟨?_, ?_⟩
  · intro g hg f hf
    exact List.all_eq_true.mp (Array.all_eq_true_iff_forall_mem.mp h3 g hg) f
      (List.mem_range.mpr hf)
  · intro w hw
    exact Array.all_eq_true_iff_forall_mem.mp h4 (some w) hw

theorem a8S1Of_spec {D : A8Data} (h : a8S1Of D = true) :
    enumOK a8Gens D.elems D.par = true ∧ D.elems.size = 20160 := by
  simp only [a8S1Of, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, _⟩, _⟩, h4⟩, _⟩ := h
  exact ⟨h1, h4⟩

theorem a8S2Of_spec {D : A8Data} (h : a8S2Of D = true) :
    a8InvolutionsOK D = true ∧ D.reps.size = 2 ∧
      (∀ r ∈ D.reps, r ∈ D.elems ∧ isInvCode r = true) ∧ (∀ o ∈ D.wits, o.isSome = true) ∧
      witOK D.elems D.invMap D.reps D.theta D.involutions D.wits = true := by
  simp only [a8S2Of, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, _⟩, _⟩, _⟩, _⟩, _⟩, h9⟩, h10⟩ := h
  refine ⟨h1, h2, ?_, ?_, h10⟩
  · intro r hr
    obtain ⟨hr1, hr2⟩ := Bool.and_eq_true_iff.mp (Array.all_eq_true_iff_forall_mem.mp h3 r hr)
    exact ⟨Array.contains_iff_mem.mp hr1, hr2⟩
  · intro o ho
    exact Array.all_eq_true_iff_forall_mem.mp h9 o ho

theorem a8S3Of_spec {D : A8Data} (h : a8S3Of D = true) :
    (∀ t ∈ D.theta, isHomTabWith D.qmulFlat t = true) ∧ rootsOK D.innTabs D.theta = true := by
  simp only [a8S3Of, Bool.and_eq_true] at h
  exact ⟨Array.all_eq_true_iff_forall_mem.mp h.1, h.2⟩

theorem a8S4Of_spec {D : A8Data} (h : a8S4Of D = true) :
    (∀ g ∈ #[Code.one] ++ D.involutions, ∀ f < 64,
        isHomTabWith D.qmulFlat (liftTab g f) = true) ∧
      ∀ w : SqWit, some w ∈ D.wits → isHomTabWith D.qmulFlat w.psi = true := by
  simp only [a8S4Of, Bool.and_eq_true] at h
  obtain ⟨⟨⟨_, _⟩, h3⟩, h4⟩ := h
  refine ⟨?_, ?_⟩
  · intro g hg f hf
    exact List.all_eq_true.mp (Array.all_eq_true_iff_forall_mem.mp h3 g hg) f
      (List.mem_range.mpr hf)
  · intro w hw
    exact Array.all_eq_true_iff_forall_mem.mp h4 (some w) hw

@[expose] def pglCand (D : PGLSquareData) (b : Bool × Bool) (w : SqWit) (u f : ℕ) :
    Option ℕ :=
  candVal D.innTabs (liftTab u f) w.psi w.tp w.itp (sOf D.root b.1 b.2 w.repIdx)

private theorem length_filter_filterMap_some {α : Type*} (l : List α) (g : α → Option ℕ)
    (v : ℕ) :
    ((l.filterMap g).filter (fun x => x == v)).length =
      (l.filter (fun x => g x == some v)).length := by
  rw [← List.countP_eq_length_filter, ← List.count_eq_countP, List.count_filterMap,
    List.countP_eq_length_filter]

theorem pglS4Of_spec {D : PGLSquareData} (h : pglS4Of D = true) :
    pglOutersOK D.pgl = true ∧ rootsOK D.innTabs D.theta = true ∧
      witOK D.pgl.elems D.pgl.invMap D.reps D.theta D.pgl.involutions D.wits = true ∧
      ∀ b : Bool × Bool, ∀ u ∈ D.pgl.outers, ∃ w : SqWit, D.witMap.get? u = some w ∧ w.g = u ∧
        (∀ f < 64, (pglCand D b w u f).isSome = true) ∧
        ((((List.range 64).filter fun f => pglCand D b w u f == some 0).length = 8 ∧
            ((List.range 64).filter fun f => pglCand D b w u f == some z0N).length = 0) ∨
          (((List.range 64).filter fun f => pglCand D b w u f == some 0).length = 0 ∧
            ((List.range 64).filter fun f => pglCand D b w u f == some z0N).length = 8)) ∧
        (∀ f < 64, ∀ v, pglCand D b w u f = some v → (v = 0 ∨ v = z0N) →
          ((List.range 128).filter fun x => (liftTab u f)[x]! == x).length = 8 ∧
          (∀ x < 128, (liftTab u f)[x]! = x → qmulN x x = 0) ∧
          ∀ w0 ∈ D.pgl.elems0, w0 ≠ Code.one → Code.mul w0 w0 = Code.one →
            Code.mul w0 u = Code.mul u w0 →
            ∃ x < 128, (liftTab u f)[x]! = x ∧ Code.act w0 (x / 2) ≠ x / 2) ∧
        ∀ f₁ < 64, ∀ f₂ < 64, liftTab u f₁ = liftTab u f₂ → f₁ = f₂ := by
  simp only [pglS4Of, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, ?_⟩
  intro b u hu
  have hb : b ∈ certBits := by
    rcases b with ⟨b1, b2⟩
    cases b1 <;> cases b2 <;> simp [certBits]
  have hu' := Array.all_eq_true_iff_forall_mem.mp (List.all_eq_true.mp h4 b hb) u hu
  rcases Option.eq_none_or_eq_some (D.witMap.get? u) with ho | ⟨w, hw⟩
  · rw [ho] at hu'
    simp at hu'
  · rw [hw] at hu'
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true_iff] at hu'
    obtain ⟨⟨⟨⟨hgu, hexist⟩, hsigma1⟩, hsigma2⟩, hdistinct⟩ := hu'
    have hsv : ∀ f < 64,
        ((List.range 64).map fun f => candVal D.innTabs (liftTab u f) w.psi w.tp w.itp
          (sOf D.root b.1 b.2 w.repIdx))[f]! = pglCand D b w u f := by
      intro f hf
      rw [getElem!_eq_getElem_of_lt (by simp; exact hf)]
      simp [pglCand, List.getElem_map, List.getElem_range, hf]
    have htabs : ∀ f < 64,
        ((List.range 64).map fun f => liftTab u f).toArray[f]! = liftTab u f := by
      intro f hf
      rw [List.getElem!_toArray, getElem!_eq_getElem_of_lt (by simp; exact hf)]
      simp [List.getElem_map, List.getElem_range, hf]
    have hexist' : ∀ f < 64, (pglCand D b w u f).isSome = true := by
      intro f hf
      have hmem : pglCand D b w u f ∈ List.map (fun f => candVal D.innTabs (liftTab u f)
          w.psi w.tp w.itp (sOf D.root b.1 b.2 w.repIdx)) (List.range 64) :=
        List.mem_map.mpr ⟨f, List.mem_range.mpr hf, rfl⟩
      exact List.all_eq_true.mp hexist _ hmem
    have hcnt : ∀ v : ℕ,
        ((List.range 64).filter fun f => pglCand D b w u f == some v).length =
          ((((List.range 64).map fun f => pglCand D b w u f).filterMap fun o => o).filter
            fun x => x == v).length := by
      intro v
      have hmap : ((List.range 64).map fun f => pglCand D b w u f).filterMap (fun o => o) =
          (List.range 64).filterMap fun f => pglCand D b w u f := by
        rw [List.filterMap_map]
        rfl
      rw [hmap]
      exact (length_filter_filterMap_some _ _ v).symm
    have hsigma1' : (((List.range 64).filter fun f => pglCand D b w u f == some 0).length = 8 ∧
          ((List.range 64).filter fun f => pglCand D b w u f == some z0N).length = 0) ∨
        (((List.range 64).filter fun f => pglCand D b w u f == some 0).length = 0 ∧
          ((List.range 64).filter fun f => pglCand D b w u f == some z0N).length = 8) := by
      rcases hsigma1 with ⟨h0, hz⟩ | ⟨h0, hz⟩
      · left
        exact ⟨by rw [hcnt 0]; exact h0, by rw [hcnt z0N]; exact hz⟩
      · right
        exact ⟨by rw [hcnt 0]; exact h0, by rw [hcnt z0N]; exact hz⟩
    have hsigma2' : ∀ f < 64, ∀ v, pglCand D b w u f = some v → (v = 0 ∨ v = z0N) →
        ((List.range 128).filter fun x => (liftTab u f)[x]! == x).length = 8 ∧
          (∀ x < 128, (liftTab u f)[x]! = x → qmulN x x = 0) ∧
          ∀ w0 ∈ D.pgl.elems0, w0 ≠ Code.one → Code.mul w0 w0 = Code.one →
            Code.mul w0 u = Code.mul u w0 →
            ∃ x < 128, (liftTab u f)[x]! = x ∧ Code.act w0 (x / 2) ≠ x / 2 := by
      intro f hf v hv hvn
      have hs2 := List.all_eq_true.mp hsigma2 f (List.mem_range.mpr hf)
      simp only [hsv f hf, hv, htabs f hf] at hs2
      rw [if_pos hvn] at hs2
      simp only [Bool.and_eq_true, beq_iff_eq] at hs2
      obtain ⟨⟨hlen, hall⟩, hw0⟩ := hs2
      refine ⟨hlen, ?_, ?_⟩
      · intro x hx hfix
        have hxmem : x ∈ (List.range 128).filter
            (fun y => (liftTab u f)[y]! == y) :=
          List.mem_filter.mpr ⟨List.mem_range.mpr hx, beq_iff_eq.mpr hfix⟩
        have := List.all_eq_true.mp hall x hxmem
        simpa using this
      · intro w0 hw0E hw0ne hw0inv hw0comm
        have hw0mem : w0 ∈ D.pgl.elems0.filter (fun w0 =>
            w0 != Code.one && Code.mul w0 w0 == Code.one &&
              Code.mul w0 u == Code.mul u w0) := by
          rw [Array.mem_filter]
          refine ⟨hw0E, ?_⟩
          simp only [Bool.and_eq_true_iff]
          exact ⟨⟨bne_iff_ne.mpr hw0ne, beq_iff_eq.mpr hw0inv⟩,
            beq_iff_eq.mpr hw0comm⟩
        obtain ⟨x, hxmem, hxne⟩ :=
          List.any_eq_true.mp (Array.all_eq_true_iff_forall_mem.mp hw0 w0 hw0mem)
        exact ⟨x, List.mem_range.mp (List.mem_filter.mp hxmem).1,
          beq_iff_eq.mp (List.mem_filter.mp hxmem).2, bne_iff_ne.mp hxne⟩
    have hdist : ∀ f1 < 64, ∀ f2 < 64, f1 ≤ f2 ∨ liftTab u f1 ≠ liftTab u f2 := by
      intro f1 h1 f2 h2
      rw [distinctTabs] at hdistinct
      have hh1 := Array.all_eq_true.mp hdistinct f1 (by simpa using h1)
      have hh2 := Array.all_eq_true.mp hh1 f2 (by simpa using h2)
      simpa [Bool.or_eq_true_iff, bne_iff_ne, decide_eq_true_eq, htabs f1 h1, htabs f2 h2]
        using hh2
    have hinj : ∀ f1 < 64, ∀ f2 < 64, liftTab u f1 = liftTab u f2 → f1 = f2 := by
      intro f1 h1 f2 h2 heq
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · rcases hdist f2 (by omega) f1 (by omega) with hle | hne'
        · omega
        · exact hne' heq.symm
      · rcases hdist f1 (by omega) f2 (by omega) with hle | hne'
        · omega
        · exact hne' heq
    exact ⟨w, hw, hgu, hexist', hsigma1', hsigma2', hinj⟩

@[expose] def a0Pairs (gens : Array ℕ) : List (ℕ × ℕ) :=
  gens.toList.flatMap fun g =>
    ((List.range 64).filter fun f => (liftTab g f)[a0N]! == a0N).map fun f => (g, f)

theorem mem_a0Pairs {gens : Array ℕ} {g f : ℕ} :
    (g, f) ∈ a0Pairs gens ↔ g ∈ gens ∧ f < 64 ∧ (liftTab g f)[a0N]! = a0N := by
  rw [a0Pairs]
  simp only [List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
    Array.mem_toList_iff, Prod.mk.injEq, beq_iff_eq]
  constructor
  · rintro ⟨g', hg', f', ⟨hf, hpred⟩, hgg, hff⟩
    rw [← hgg, ← hff]
    exact ⟨hg', hf, hpred⟩
  · rintro ⟨hg, hf, hpred⟩
    exact ⟨g, hg, f, ⟨hf, hpred⟩, rfl, rfl⟩

theorem nodup_a0Pairs {gens : Array ℕ} (h : gens.toList.Nodup) : (a0Pairs gens).Nodup := by
  rw [a0Pairs, List.nodup_flatMap]
  refine ⟨fun g _ => ?_, h.imp ?_⟩
  · refine List.Nodup.map ?_ (List.nodup_range.filter _)
    intro f1 f2 heq
    exact (Prod.mk.injEq ..).mp heq |>.2
  · intro g1 g2 hne
    simp only [Function.onFun, List.disjoint_left]
    rintro ⟨g, f⟩ hx hy
    simp only [List.mem_map, List.mem_filter] at hx hy
    obtain ⟨f1, _, hx'⟩ := hx
    obtain ⟨f2, _, hy'⟩ := hy
    have h1 : g1 = g := (Prod.mk.injEq ..).mp hx' |>.1
    have h2 : g2 = g := (Prod.mk.injEq ..).mp hy' |>.1
    exact hne (h1.trans h2.symm)

@[expose] def a8Cand (D : A8Data) (b : Bool × Bool) (p : ℕ × ℕ) : Option ℕ :=
  if p.1 == Code.one then candValOne D.innTabs (liftTab p.1 p.2)
  else
    match D.witMap.get? p.1 with
    | some w =>
      if w.g == p.1 then
        candVal D.innTabs (liftTab p.1 p.2) w.psi w.tp w.itp (sOf D.root b.1 b.2 w.repIdx)
      else none
    | none => none

private theorem foldl_push_filter (l : List ℕ) (p : ℕ → Bool) (F : ℕ → Option ℕ)
    (acc : Array (Option ℕ)) :
    (l.foldl (fun acc f => if p f then acc.push (F f) else acc) acc).toList =
      acc.toList ++ (l.filter p).map F := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons]
    by_cases h : p a = true
    · rw [if_pos h, ih, List.filter_cons, if_pos h, Array.toList_push]
      simp [List.append_assoc]
    · rw [if_neg h, ih, List.filter_cons, if_neg h]

private theorem foldl_foldl_push (l : List ℕ) (F : ℕ → ℕ → Option ℕ)
    (acc : Array (Option ℕ)) :
    (l.foldl (fun acc g => (List.range 64).foldl (fun acc f =>
        if (liftTab g f)[a0N]! == a0N then acc.push (F g f) else acc) acc) acc).toList =
      acc.toList ++ l.flatMap (fun g => ((List.range 64).filter fun f =>
        (liftTab g f)[a0N]! == a0N).map fun f => F g f) := by
  induction l generalizing acc with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih, List.flatMap_cons, foldl_push_filter]
    simp [List.append_assoc]

private theorem foldl_foldl_push_array (gens : Array ℕ) (F : ℕ → ℕ → Option ℕ) :
    gens.foldl (fun acc g => (List.range 64).foldl (fun acc f =>
        if (liftTab g f)[a0N]! == a0N then acc.push (F g f) else acc) acc) #[] =
      ((a0Pairs gens).map fun p => F p.1 p.2).toArray := by
  apply Array.toList_inj.mp
  rw [← Array.foldl_toList, foldl_foldl_push, a0Pairs]
  simp only [List.toList_toArray, List.map_flatMap, List.nil_append, List.map_map,
    Function.comp_def]

theorem a8S5Of_spec {D : A8Data} (h : a8S5Of D = true) :
    a8InvolutionsOK D = true ∧ rootsOK D.innTabs D.theta = true ∧
      witOK D.elems D.invMap D.reps D.theta D.involutions D.wits = true ∧
      ∀ b : Bool × Bool,
        (∀ p ∈ a0Pairs (#[Code.one] ++ D.involutions), (a8Cand D b p).isSome = true) ∧
        ((a0Pairs (#[Code.one] ++ D.involutions)).filter
            fun p => a8Cand D b p == some a0N).length = 120 ∧
        ((a0Pairs (#[Code.one] ++ D.involutions)).filter
            fun p => a8Cand D b p == some z0N).length ∈ ({72, 336, 408, 672} : Finset ℕ) := by
  simp only [a8S5Of, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, ?_⟩
  intro b
  have hb : b ∈ certBits := by
    rcases b with ⟨b1, b2⟩
    cases b1 <;> cases b2 <;> simp [certBits]
  have hb' := List.all_eq_true.mp h4 b hb
  rw [foldl_foldl_push_array] at hb'
  simp only [Bool.and_eq_true] at hb'
  obtain ⟨⟨⟨hexist, _⟩, hna⟩, hnz⟩ := hb'
  have hna' : (((((a0Pairs (#[Code.one] ++ D.involutions)).map
      fun p => a8Cand D b p).toArray.toList.filterMap fun o => o).filter
      (fun x => x == a0N)).length) = 120 := beq_iff_eq.mp hna
  have hexist' : ∀ p ∈ a0Pairs (#[Code.one] ++ D.involutions), (a8Cand D b p).isSome = true := by
    intro p hp
    have hmem : a8Cand D b p ∈ ((a0Pairs (#[Code.one] ++ D.involutions)).map
        fun p => a8Cand D b p).toArray := by
      rw [← Array.mem_toList_iff, List.toList_toArray]
      exact List.mem_map_of_mem hp
    exact Array.all_eq_true_iff_forall_mem.mp hexist _ hmem
  have hcount : ∀ v : ℕ,
      ((a0Pairs (#[Code.one] ++ D.involutions)).filter
          fun p => a8Cand D b p == some v).length =
        ((((a0Pairs (#[Code.one] ++ D.involutions)).map
            fun p => a8Cand D b p).toArray.toList.filterMap
          fun o => o).filter (fun x => x == v)).length := by
    intro v
    simp only [List.toList_toArray]
    rw [← length_filter_filterMap_some (a0Pairs (#[Code.one] ++ D.involutions))
      (fun p => a8Cand D b p) v, List.filterMap_map]
    rfl
  refine ⟨hexist', ?_, ?_⟩
  · rw [hcount a0N]
    exact hna'
  · rw [hcount z0N]
    have hmem : ((((a0Pairs (#[Code.one] ++ D.involutions)).map
        fun p => a8Cand D b p).toArray.toList.filterMap
        fun o => o).filter (fun x => x == z0N)).length ∈ [72, 336, 408, 672] :=
      List.contains_iff_mem.mp hnz
    simpa using hmem

end CFSG.GF2Type.Smith1979W3.Cert690

end
