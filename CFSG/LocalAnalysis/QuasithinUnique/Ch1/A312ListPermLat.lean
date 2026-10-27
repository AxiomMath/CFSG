module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermEnc

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

open CFSG.QuasithinUnique.Unc25K1.Six

abbrev CommWord : Type := List ℕ × List ℕ × List ℕ × List ℕ

section Words

@[expose] def evalW {R : Type*} [Mul R] [One R] (gens : List R) : List ℕ → R
  | [] => 1
  | i :: w => gens.getD i 1 * evalW gens w

variable {G : Type*} [Group G] {R : Type} [Mul R] [One R] {enc : G → R}

theorem enc_evalW (h : IsEnc enc) (gens : List G) (w : List ℕ) :
    enc (evalW gens w) = evalW (gens.map enc) w := by
  induction w with
  | nil => simpa [evalW] using h.map_one
  | cons i w ih =>
    simp only [evalW]
    rw [h.map_mul, ih]
    congr 1
    by_cases hi : i < gens.length
    · rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (by simpa using hi),
        List.getElem_map]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simpa using hi),
        h.map_one]

theorem evalW_mem_closure (gens : List G) (w : List ℕ) :
    evalW gens w ∈ Subgroup.closure {g | g ∈ gens} := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons i w ih =>
    simp only [evalW]
    refine Subgroup.mul_mem _ ?_ ih
    by_cases hi : i < gens.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact Subgroup.subset_closure (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]
      exact Subgroup.one_mem _

end Words

section Pure

variable {G : Type*} [Group G] [Finite G]

theorem mem_of_forall_zpowers (T M : Subgroup G) (𝓛 : Subgroup G → Prop) (hT : 𝓛 T)
    (hjoin : ∀ A B, 𝓛 A → 𝓛 B → 𝓛 (A ⊔ B))
    (hx : ∀ x ∈ M, 𝓛 (T ⊔ Subgroup.zpowers x)) {Y : Subgroup G} (hTY : T ≤ Y) (hYM : Y ≤ M) :
    𝓛 Y := by
  classical
  have key : ∀ l : List G, (∀ x ∈ l, x ∈ M) → 𝓛 (T ⊔ Subgroup.closure {g | g ∈ l}) := by
    intro l
    induction l with
    | nil =>
      intro _
      have : (Subgroup.closure {g : G | g ∈ ([] : List G)}) = ⊥ := by
        rw [← Subgroup.closure_empty]
        congr 1
        ext g
        simp
      rw [this, sup_bot_eq]
      exact hT
    | cons x l ih =>
      intro hl
      have h1 := ih (fun y hy => hl y (List.mem_cons_of_mem _ hy))
      have h2 := hx x (hl x List.mem_cons_self)
      have hset : {g : G | g ∈ x :: l} = {x} ∪ {g | g ∈ l} := by
        ext g
        simp [List.mem_cons]
      have : T ⊔ Subgroup.closure {g | g ∈ x :: l} =
          (T ⊔ Subgroup.zpowers x) ⊔ (T ⊔ Subgroup.closure {g | g ∈ l}) := by
        rw [hset, Subgroup.closure_union, Subgroup.zpowers_eq_closure]
        ac_rfl
      rw [this]
      exact hjoin _ _ h2 h1
  let l : List G := (Set.toFinite (Y : Set G)).toFinset.toList
  have hl : ∀ x ∈ l, x ∈ M := fun x hx => hYM (by simpa [l] using hx)
  have hY : T ⊔ Subgroup.closure {g | g ∈ l} = Y := by
    apply le_antisymm
    · refine sup_le hTY ?_
      rw [Subgroup.closure_le]
      intro g hg
      simpa [l] using hg
    · intro y hy
      exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simpa [l] using hy))
  rw [← hY]
  exact key l hl

end Pure

section Certificate

variable {G : Type} [Group G] {R : Type} [Mul R] [One R] [DecidableEq R] [Hashable R]
  (enc : G → R)

@[expose] def elts (depth : ℕ) (gens : List G) : Std.HashSet R := bfsSet (gens.map enc) depth

def eqCert (EB : Std.HashSet R) (A B : List G) (ws : List (List ℕ)) : Bool :=
  A.all (fun g => EB.contains (enc g)) && decide (ws.length = B.length) &&
    (B.zip ws).all fun p => evalW (A.map enc) p.2 == enc p.1

variable {enc}

theorem closure_eq_of_eqCert [Finite G] (h : IsEnc enc) {depth : ℕ} {A B : List G}
    {ws : List (List ℕ)} (hB : closedH (B.map enc) (elts enc depth B) = true)
    (hc : eqCert enc (elts enc depth B) A B ws = true) :
    Subgroup.closure {g | g ∈ A} = Subgroup.closure {g | g ∈ B} := by
  simp only [eqCert, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hA, hlen⟩, hw⟩ := hc
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro g hg
    have := Std.HashSet.contains_iff_mem.mp (hA g hg)
    exact (mem_closure_iff_H h B depth hB g).mpr this
  · rw [Subgroup.closure_le]
    intro g hg
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
    have hk' : k < ws.length := by omega
    have hmem : (B[k], ws[k]) ∈ B.zip ws :=
      List.mem_iff_getElem.mpr ⟨k, by simp [List.length_zip]; omega, by simp⟩
    have := hw _ hmem
    simp only [beq_iff_eq] at this
    have hg : B[k] = evalW A ws[k] := h.inj (by rw [enc_evalW h, ← this])
    rw [hg]
    exact evalW_mem_closure A _

end Certificate

structure LatCert (G : Type) where
  depth : ℕ
  mGens : List G
  tGens : List G
  lat : List (List G)
  reps : List (G × ℕ × List (List ℕ))
  joins : List (ℕ × ℕ × ℕ × List (List ℕ))
  sizes : List ℕ
  msize : ℕ

section Check

variable {G : Type} [Group G] {R : Type} [Mul R] [One R] [DecidableEq R] [Hashable R]
  (enc : G → R)

@[expose] def LatCert.members (c : LatCert G) : List (List G × Std.HashSet R) :=
  (c.tGens :: c.lat).map fun L => (L, elts enc c.depth L)

def LatCert.closedOK (c : LatCert G) : Bool :=
  closedH (c.mGens.map enc) (elts enc c.depth c.mGens) &&
    (c.members enc).all fun p => closedH (p.1.map enc) p.2

def LatCert.coverOK (c : LatCert G) : Bool :=
  let ET := elts enc c.depth c.tGens
  let DC : Std.HashSet R := Std.HashSet.ofList (c.reps.flatMap fun r =>
    ET.toList.flatMap fun d => ET.toList.map fun e => d * enc r.1 * e)
  (elts enc c.depth c.mGens).toList.all fun x => DC.contains x

def LatCert.repsOK (c : LatCert G) : Bool :=
  let mem := c.members enc
  c.reps.all fun r =>
    match mem[r.2.1]? with
    | some p => eqCert enc p.2 (c.tGens ++ [r.1]) p.1 r.2.2
    | none => false

def LatCert.joinsOK (c : LatCert G) : Bool :=
  let mem := c.members enc
  (List.range mem.length).all (fun a => (List.range mem.length).all fun b =>
      c.joins.any fun j => j.1 == a && j.2.1 == b) &&
    c.joins.all fun j =>
      match mem[j.1]?, mem[j.2.1]?, mem[j.2.2.1]? with
      | some pa, some pb, some pc => eqCert enc pc.2 (pa.1 ++ pb.1) pc.1 j.2.2.2
      | _, _, _ => false

def LatCert.sizesOK (c : LatCert G) : Bool :=
  (c.members enc).map (fun p => p.2.size) == c.sizes &&
    (elts enc c.depth c.mGens).size == c.msize

def LatCert.tleOK (c : LatCert G) : Bool :=
  c.tGens.all fun g => (elts enc c.depth c.mGens).contains (enc g)

@[expose] def LatCert.check (c : LatCert G) : Bool :=
  c.closedOK enc && c.coverOK enc && c.repsOK enc && c.joinsOK enc && c.sizesOK enc &&
    c.tleOK enc

variable {enc}

section Sound

variable [Finite G]

omit [Group G] [Finite G] in
theorem LatCert.members_closed (c : LatCert G) (hc : c.closedOK enc = true) :
    ∀ L ∈ c.tGens :: c.lat, closedH (L.map enc) (elts enc c.depth L) = true := by
  simp only [LatCert.closedOK, Bool.and_eq_true, List.all_eq_true, LatCert.members,
    List.mem_map] at hc
  intro L hL
  exact hc.2 (L, elts enc c.depth L) ⟨L, hL, rfl⟩

theorem LatCert.mem_elts_of_mem_closure (h : IsEnc enc) (c : LatCert G)
    (hc : c.closedOK enc = true) (x : G) (hx : x ∈ Subgroup.closure {g | g ∈ c.mGens}) :
    enc x ∈ elts enc c.depth c.mGens := by
  simp only [LatCert.closedOK, Bool.and_eq_true] at hc
  exact (mem_closure_iff_H h c.mGens c.depth hc.1 x).mp hx

theorem LatCert.rep_mem (h : IsEnc enc) (c : LatCert G) (hcl : c.closedOK enc = true)
    (hc : c.repsOK enc = true) :
    ∀ r ∈ c.reps, ∃ L ∈ c.tGens :: c.lat,
      Subgroup.closure {g | g ∈ c.tGens ++ [r.1]} = Subgroup.closure {g | g ∈ L} := by
  intro r hr
  simp only [LatCert.repsOK, List.all_eq_true] at hc
  have h1 := hc r hr
  cases hmem : (c.members enc)[r.2.1]? with
  | none => simp [hmem] at h1
  | some p =>
    rw [hmem] at h1
    simp only at h1
    obtain ⟨L, hL, hpL⟩ : ∃ L ∈ c.tGens :: c.lat, p = (L, elts enc c.depth L) := by
      have : p ∈ c.members enc := List.mem_of_getElem? hmem
      obtain ⟨L, hL, hpL⟩ := List.mem_map.mp this
      exact ⟨L, hL, hpL.symm⟩
    subst hpL
    refine ⟨L, hL, ?_⟩
    exact closure_eq_of_eqCert h (c.members_closed hcl L hL) h1

theorem LatCert.join_mem (h : IsEnc enc) (c : LatCert G) (hcl : c.closedOK enc = true)
    (hc : c.joinsOK enc = true) :
    ∀ L₁ ∈ c.tGens :: c.lat, ∀ L₂ ∈ c.tGens :: c.lat, ∃ L ∈ c.tGens :: c.lat,
      Subgroup.closure {g | g ∈ L₁} ⊔ Subgroup.closure {g | g ∈ L₂} =
        Subgroup.closure {g | g ∈ L} := by
  intro L₁ hL₁ L₂ hL₂
  simp only [LatCert.joinsOK, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    List.mem_range, Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨hall, hjoin⟩ := hc
  have hlen : (c.members enc).length = (c.tGens :: c.lat).length := by simp [LatCert.members]
  obtain ⟨a, ha, hLa⟩ := List.mem_iff_getElem.mp hL₁
  obtain ⟨b, hb, hLb⟩ := List.mem_iff_getElem.mp hL₂
  obtain ⟨j, hj, hja, hjb⟩ := hall a (by rw [hlen]; exact ha) b (by rw [hlen]; exact hb)
  have h1 := hjoin j hj
  have hLa' : (c.tGens :: c.lat)[a]? = some L₁ := by rw [List.getElem?_eq_getElem ha, hLa]
  have hLb' : (c.tGens :: c.lat)[b]? = some L₂ := by rw [List.getElem?_eq_getElem hb, hLb]
  have hma : (c.members enc)[j.1]? = some (L₁, elts enc c.depth L₁) := by
    rw [hja]
    simp only [LatCert.members, List.getElem?_map, hLa', Option.map_some]
  have hmb : (c.members enc)[j.2.1]? = some (L₂, elts enc c.depth L₂) := by
    rw [hjb]
    simp only [LatCert.members, List.getElem?_map, hLb', Option.map_some]
  rw [hma, hmb] at h1
  cases hmc : (c.members enc)[j.2.2.1]? with
  | none => simp [hmc] at h1
  | some p =>
    rw [hmc] at h1
    simp only at h1
    obtain ⟨L, hL, hpL⟩ : ∃ L ∈ c.tGens :: c.lat, p = (L, elts enc c.depth L) := by
      have : p ∈ c.members enc := List.mem_of_getElem? hmc
      obtain ⟨L, hL, hpL⟩ := List.mem_map.mp this
      exact ⟨L, hL, hpL.symm⟩
    subst hpL
    refine ⟨L, hL, ?_⟩
    have := closure_eq_of_eqCert h (c.members_closed hcl L hL) h1
    rw [← this]
    have hset : {g : G | g ∈ L₁ ++ L₂} = {g | g ∈ L₁} ∪ {g | g ∈ L₂} := by
      ext g
      simp
    rw [hset, Subgroup.closure_union]

theorem LatCert.cover_mem (h : IsEnc enc) (c : LatCert G) (hcl : c.closedOK enc = true)
    (hcov : c.coverOK enc = true) (x : G) (hx : x ∈ Subgroup.closure {g | g ∈ c.mGens}) :
    ∃ r ∈ c.reps, ∃ d ∈ Subgroup.closure {g | g ∈ c.tGens},
      ∃ e ∈ Subgroup.closure {g | g ∈ c.tGens}, x = d * r.1 * e := by
  have hxE := c.mem_elts_of_mem_closure h hcl x hx
  simp only [LatCert.coverOK, List.all_eq_true] at hcov
  have h1 := hcov (enc x) (Std.HashSet.mem_toList.mpr hxE)
  have h2 := Std.HashSet.contains_iff_mem.mp h1
  simp only [Std.HashSet.mem_ofList, List.contains_iff_exists_mem_beq, List.mem_flatMap,
    List.mem_map, beq_iff_eq] at h2
  obtain ⟨_, ⟨r, hr, d', hd', e', he', rfl⟩, hxeq⟩ := h2
  obtain ⟨d, hd, rfl⟩ := bfsSet_sound h c.tGens c.depth d' (Std.HashSet.mem_toList.mp hd')
  obtain ⟨e, he, rfl⟩ := bfsSet_sound h c.tGens c.depth e' (Std.HashSet.mem_toList.mp he')
  refine ⟨r, hr, d, hd, e, he, h.inj ?_⟩
  rw [h.map_mul, h.map_mul]
  exact hxeq

theorem LatCert.overgroups (h : IsEnc enc) (c : LatCert G) (hc : c.check enc = true)
    (Y : Subgroup G) (hTY : Subgroup.closure {g | g ∈ c.tGens} ≤ Y)
    (hYM : Y ≤ Subgroup.closure {g | g ∈ c.mGens}) :
    ∃ L ∈ c.tGens :: c.lat, Y = Subgroup.closure {g | g ∈ L} := by
  simp only [LatCert.check, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨hcl, hcov⟩, hreps⟩, hjoins⟩, -⟩, -⟩ := hc
  let 𝓛 : Subgroup G → Prop := fun A => ∃ L ∈ c.tGens :: c.lat, A = Subgroup.closure {g | g ∈ L}
  have hT : 𝓛 (Subgroup.closure {g | g ∈ c.tGens}) := ⟨c.tGens, List.mem_cons_self, rfl⟩
  have hjoin : ∀ A B, 𝓛 A → 𝓛 B → 𝓛 (A ⊔ B) := by
    rintro A B ⟨L₁, h₁, rfl⟩ ⟨L₂, h₂, rfl⟩
    obtain ⟨L, hL, he⟩ := c.join_mem h hcl hjoins L₁ h₁ L₂ h₂
    exact ⟨L, hL, he⟩
  have hx : ∀ x ∈ Subgroup.closure {g | g ∈ c.mGens},
      𝓛 (Subgroup.closure {g | g ∈ c.tGens} ⊔ Subgroup.zpowers x) := by
    intro x hxM
    obtain ⟨r, hr, d, hd, e, he, rfl⟩ := c.cover_mem h hcl hcov x hxM
    have heq : Subgroup.closure {g | g ∈ c.tGens} ⊔ Subgroup.zpowers (d * r.1 * e) =
        Subgroup.closure {g | g ∈ c.tGens} ⊔ Subgroup.zpowers r.1 := by
      apply le_antisymm
      · refine sup_le le_sup_left ?_
        rw [Subgroup.zpowers_le]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hd)
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))) (Subgroup.mem_sup_left he)
      · refine sup_le le_sup_left ?_
        rw [Subgroup.zpowers_le]
        have hmem : d⁻¹ * (d * r.1 * e) * e⁻¹ ∈
            Subgroup.closure {g | g ∈ c.tGens} ⊔ Subgroup.zpowers (d * r.1 * e) :=
          Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left hd))
            (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))
            (Subgroup.inv_mem _ (Subgroup.mem_sup_left he))
        have hr' : d⁻¹ * (d * r.1 * e) * e⁻¹ = r.1 := by group
        rwa [hr'] at hmem
    have hset : {g : G | g ∈ c.tGens ++ [r.1]} = {g | g ∈ c.tGens} ∪ {r.1} := by
      ext g
      simp only [Set.mem_ofPred_eq, List.mem_append, List.mem_singleton, Set.mem_union,
        Set.mem_singleton_iff]
    have hcl' : Subgroup.closure {g | g ∈ c.tGens ++ [r.1]} =
        Subgroup.closure {g | g ∈ c.tGens} ⊔ Subgroup.zpowers r.1 := by
      rw [hset, Subgroup.closure_union, Subgroup.zpowers_eq_closure]
    obtain ⟨L, hL, hLe⟩ := c.rep_mem h hcl hreps r hr
    exact ⟨L, hL, by rw [heq, ← hcl', hLe]⟩
  exact mem_of_forall_zpowers _ _ 𝓛 hT hjoin hx hTY hYM

omit [Group G] [Finite G] in
theorem LatCert.card_member' (c : LatCert G) (hc : c.sizesOK enc = true) :
    ∀ L ∈ c.tGens :: c.lat, (elts enc c.depth L).size ∈ c.sizes := by
  simp only [LatCert.sizesOK, Bool.and_eq_true, beq_iff_eq] at hc
  intro L hL
  rw [← hc.1]
  exact List.mem_map.mpr ⟨(L, elts enc c.depth L), List.mem_map.mpr ⟨L, hL, rfl⟩, rfl⟩

theorem LatCert.card_member (h : IsEnc enc) (c : LatCert G) (hcl : c.closedOK enc = true)
    (hc : c.sizesOK enc = true) :
    ∀ L ∈ c.tGens :: c.lat, Nat.card (Subgroup.closure {g | g ∈ L}) ∈ c.sizes := by
  intro L hL
  rw [card_closure_of_closedH h L c.depth (c.members_closed hcl L hL)]
  exact c.card_member' hc L hL

theorem LatCert.card_m (h : IsEnc enc) (c : LatCert G) (hcl : c.closedOK enc = true)
    (hc : c.sizesOK enc = true) : Nat.card (Subgroup.closure {g | g ∈ c.mGens}) = c.msize := by
  simp only [LatCert.closedOK, Bool.and_eq_true] at hcl
  simp only [LatCert.sizesOK, Bool.and_eq_true, beq_iff_eq] at hc
  rw [card_closure_of_closedH h c.mGens c.depth hcl.1]
  exact hc.2

theorem LatCert.t_le_m (h : IsEnc enc) (c : LatCert G) (hcl : c.closedOK enc = true)
    (hc : c.tleOK enc = true) :
    Subgroup.closure {g | g ∈ c.tGens} ≤ Subgroup.closure {g | g ∈ c.mGens} := by
  simp only [LatCert.closedOK, Bool.and_eq_true] at hcl
  simp only [LatCert.tleOK, List.all_eq_true] at hc
  rw [Subgroup.closure_le]
  intro g hg
  exact (mem_closure_iff_H h c.mGens c.depth hcl.1 g).mpr (Std.HashSet.contains_iff_mem.mp (hc g hg))

omit [Group G] [Finite G] in
theorem LatCert.closedOK_of_check {c : LatCert G} (hc : c.check enc = true) :
    c.closedOK enc = true := by
  simp only [LatCert.check, Bool.and_eq_true] at hc
  exact hc.1.1.1.1.1

omit [Group G] [Finite G] in
theorem LatCert.sizesOK_of_check {c : LatCert G} (hc : c.check enc = true) :
    c.sizesOK enc = true := by
  simp only [LatCert.check, Bool.and_eq_true] at hc
  exact hc.1.2

theorem LatCert.overgroup_cases (h : IsEnc enc) (c : LatCert G) (hc : c.check enc = true)
    (Y : Subgroup ↥(Subgroup.closure {g | g ∈ c.mGens}))
    (hY : (Subgroup.closure {g | g ∈ c.tGens}).subgroupOf (Subgroup.closure {g | g ∈ c.mGens}) ≤
      Y) :
    ∃ L ∈ c.tGens :: c.lat, Subgroup.closure {g | g ∈ L} ≤ Subgroup.closure {g | g ∈ c.mGens} ∧
      Y = (Subgroup.closure {g | g ∈ L}).subgroupOf (Subgroup.closure {g | g ∈ c.mGens}) ∧
      Nat.card (Subgroup.closure {g | g ∈ L}) ∈ c.sizes := by
  simp only [LatCert.check, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨hcl, hcov⟩, hreps⟩, hjoins⟩, hsz⟩, htle⟩ := hc
  have hc' : c.check enc = true := by
    simp only [LatCert.check, Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨hcl, hcov⟩, hreps⟩, hjoins⟩, hsz⟩, htle⟩
  have hTM := c.t_le_m h hcl htle
  let Y' : Subgroup G := Y.map (Subgroup.closure {g | g ∈ c.mGens}).subtype
  have hTY' : Subgroup.closure {g | g ∈ c.tGens} ≤ Y' := by
    intro t ht
    exact ⟨⟨t, hTM ht⟩, hY (Subgroup.mem_subgroupOf.mpr ht), rfl⟩
  have hY'M : Y' ≤ Subgroup.closure {g | g ∈ c.mGens} := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  obtain ⟨L, hL, hYL⟩ := c.overgroups h hc' Y' hTY' hY'M
  refine ⟨L, hL, hYL ▸ hY'M, ?_, c.card_member h hcl hsz L hL⟩
  rw [← hYL]
  exact (Subgroup.comap_map_eq_self_of_injective
    (Subgroup.closure {g | g ∈ c.mGens}).subtype_injective Y).symm

theorem LatCert.card_member_idx (h : IsEnc enc) (c : LatCert G) (hcl : c.closedOK enc = true)
    (hc : c.sizesOK enc = true) (j : ℕ) (hj : j < (c.tGens :: c.lat).length) :
    Nat.card (Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[j]}) = c.sizes.getD j 0 := by
  have hmem : (c.tGens :: c.lat)[j] ∈ c.tGens :: c.lat := List.getElem_mem hj
  rw [card_closure_of_closedH h _ c.depth (c.members_closed hcl _ hmem)]
  simp only [LatCert.sizesOK, Bool.and_eq_true, beq_iff_eq] at hc
  have hjm : j < (c.members enc).length := by simpa [LatCert.members] using hj
  have h2 : (c.members enc)[j]'hjm =
      ((c.tGens :: c.lat)[j], elts enc c.depth ((c.tGens :: c.lat)[j])) := by
    simp only [LatCert.members, List.getElem_map]
  have h3 : ((c.members enc).map (fun p => p.2.size)).getD j 0 =
      (elts enc c.depth ((c.tGens :: c.lat)[j])).size := by
    rw [List.getD_eq_getElem _ _ (by simpa using hjm), List.getElem_map, h2]
  rw [← hc.1, h3]
  rfl

theorem LatCert.card_t (h : IsEnc enc) (c : LatCert G) (hcl : c.closedOK enc = true)
    (hc : c.sizesOK enc = true) :
    Nat.card (Subgroup.closure {g | g ∈ c.tGens}) = c.sizes.headD 0 := by
  rw [card_closure_of_closedH h c.tGens c.depth (c.members_closed hcl c.tGens List.mem_cons_self)]
  simp only [LatCert.sizesOK, Bool.and_eq_true, beq_iff_eq] at hc
  rw [← hc.1]
  simp [LatCert.members, elts]

theorem LatCert.overgroup_cases_idx (h : IsEnc enc) (c : LatCert G) (hc : c.check enc = true)
    (Y : Subgroup ↥(Subgroup.closure {g | g ∈ c.mGens}))
    (hY : (Subgroup.closure {g | g ∈ c.tGens}).subgroupOf (Subgroup.closure {g | g ∈ c.mGens}) ≤
      Y) :
    ∃ (j : ℕ) (hj : j < (c.tGens :: c.lat).length),
      Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[j]} ≤ Subgroup.closure {g | g ∈ c.mGens} ∧
      Y = (Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[j]}).subgroupOf
        (Subgroup.closure {g | g ∈ c.mGens}) ∧
      Nat.card (Subgroup.closure {g | g ∈ (c.tGens :: c.lat)[j]}) = c.sizes.getD j 0 := by
  obtain ⟨L, hL, hLM, hYL, -⟩ := c.overgroup_cases h hc Y hY
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hL
  exact ⟨j, hj, hLM, hYL, c.card_member_idx h (c.closedOK_of_check hc) (c.sizesOK_of_check hc) j hj⟩

end Sound

end Check

end CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
