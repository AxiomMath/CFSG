module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaFor

public section

namespace CFSG.EvenSporadicStandard.Fin76b.Beta

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.EvenSporadicStandard.HypOne

theorem hom_of_cayley {D M ι : Type*} [Group D] [Group M] (gg : ι → D) (φ : ι → M)
    (hgen : closure (Set.range gg) = ⊤) (F : D → M) (h1 : F 1 = 1)
    (hcay : ∀ x l, F (x * gg l) = F x * φ l) : ∀ x y, F (x * y) = F x * F y := by
  have key : ∀ y ∈ closure (Set.range gg), ∀ x, F (x * y) = F x * F y := by
    intro y hy
    induction hy using Subgroup.closure_induction_right with
    | one => intro x; simp [h1]
    | mul_right y _ g hg ih =>
      obtain ⟨l, rfl⟩ := hg
      intro x
      rw [← mul_assoc, hcay, hcay, ih, mul_assoc]
    | mul_inv_cancel y _ g hg ih =>
      obtain ⟨l, rfl⟩ := hg
      intro x
      have h2 : ∀ z, F (z * (gg l)⁻¹) = F z * (φ l)⁻¹ := fun z => by
        have := hcay (z * (gg l)⁻¹) l
        rw [inv_mul_cancel_right] at this
        rw [this]
        group
      rw [← mul_assoc, h2, h2, ih, mul_assoc]
  intro x y
  exact key y (hgen ▸ mem_top y) x

theorem idxTH_spec {n : ℕ} {L : Array Table} {idx : Std.HashMap UInt64 ℕ} {x : Table}
    (h : idxTH n L idx x < L.size) :
    idxTH n L idx x < L.size ∧ tblEq n x L[idxTH n L idx x]! = true := by
  refine ⟨h, ?_⟩
  cases hx : idx[hkey n x]? with
  | none => simp [idxTH, hx] at h
  | some i =>
    by_cases hc : (i < L.size && tblEq n x L[i]!) = true
    · simp only [idxTH, hx, hc, ite_true]
      exact (Bool.and_eq_true_iff.1 hc).2
    · simp [idxTH, hx, hc] at h

theorem tblEq_symm' {n : ℕ} {S T : Table} (h : tblEq n S T = true) : tblEq n T S = true :=
  tblEq_iff.2 fun i hi => ((tblEq_iff.1 h) i hi).symm

theorem piGens_even : ∀ l < 2, ∃ σ ∈ alternatingGroup (Fin 6), Rep 6 piGens[l]! σ := by
  intro l hl
  interval_cases l
  · refine ⟨Equiv.swap (0 : Fin 6) 1 * Equiv.swap 2 4, ?_, ?_⟩
    · rw [Equiv.Perm.mem_alternatingGroup]
      simp [Equiv.Perm.sign_mul]
    · intro i hi
      interval_cases i <;> decide
  · refine ⟨Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 3 * Equiv.swap 3 2 * Equiv.swap 4 5, ?_, ?_⟩
    · rw [Equiv.Perm.mem_alternatingGroup]
      simp [Equiv.Perm.sign_mul]
    · intro i hi
      interval_cases i <;> decide

theorem betaFor_of_check {n : ℕ} (hn : n < 2 ^ 32) {X : Subgroup (Equiv.Perm (Fin n))}
    {tT dT bT : Table} {pg : Array Table}
    (hpg : ∀ l < 2, ∃ σ ∈ alternatingGroup (Fin 6), Rep 6 pg[l]! σ)
    (hchk : betaHomCheck n tT dT bT pg = true)
    (htX : tp n tT ∈ X) (hdX : tp n dT ∈ X) (hbX : tp n bT ∈ X)
    (hcard : Nat.card ↥(X ⊓ centralizer ({tp n bT} : Set (Equiv.Perm (Fin n)))) = 1080) :
    tp n tT * tp n bT = tp n bT * tp n tT ∧ BetaFor ↥X ⟨tp n bT, hbX⟩ := by
  classical
  simp only [betaHomCheck, Bool.and_eq_true, beq_iff_eq] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩,
    h15⟩ := hchk
  set gens : Array Table := #[tT, dT] with hgens
  set E := mulClosureH n gens 1100 with hE
  set elts := E.1 with helts
  set img := treeImg pg E.2.1 E.2.2 elts.size with himg
  have hsz : elts.size = 1080 := h10
  rw [Array.all_eq_true'] at h1
  simp only [Bool.and_eq_true] at h1
  have hgA : ∀ x ∈ gens, permOK n x = true := fun x hx => (h1 x hx).1
  have hginv : ∀ x ∈ gens, invOK n x (invT n x) = true := fun x hx => (h1 x hx).2
  obtain ⟨hErep, hcov, hKcard⟩ := enum_spec hn hgA hginv h7 (closedOK_of_closedOKH h9) h8
  have htT : tT ∈ gens := by simp [hgens]
  have hdT : dT ∈ gens := by simp [hgens]
  have rt := rep_tp (hgA tT htT)
  have rd := rep_tp (hgA dT hdT)
  have rb := rep_tp h2
  have hgset : tp n '' {x | x ∈ gens} = {tp n tT, tp n dT} := by
    ext y
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp [hgens] at hx
      rcases hx with rfl | rfl <;> simp
    · rintro (rfl | rfl)
      · exact ⟨tT, htT, rfl⟩
      · exact ⟨dT, hdT, rfl⟩
  set K : Subgroup (Equiv.Perm (Fin n)) := closure (tp n '' {x | x ∈ gens}) with hK
  set β : Equiv.Perm (Fin n) := tp n bT with hβdef
  have htK : tp n tT ∈ K := subset_closure ⟨tT, htT, rfl⟩
  have hdK : tp n dT ∈ K := subset_closure ⟨dT, hdT, rfl⟩
  rw [Array.all_eq_true'] at h6
  have hcomm : ∀ x ∈ gens, β * tp n x = tp n x * β := fun x hx =>
    (commTT_iff rb (rep_tp (hgA x hx))).1 (h6 x hx)
  have hKle : K ≤ X ⊓ centralizer ({β} : Set (Equiv.Perm (Fin n))) := by
    rw [hK, closure_le]
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨?_, mem_centralizer_singleton_iff.2 (hcomm x hx).symm⟩
    simp [hgens] at hx
    rcases hx with rfl | rfl
    · exact htX
    · exact hdX
  have hKeq : K = X ⊓ centralizer ({β} : Set (Equiv.Perm (Fin n))) :=
    eq_of_le_of_card_ge hKle (by rw [hcard, hKcard, hsz])
  have hKcard' : Nat.card ↥K = 1080 := by rw [hKcard, hsz]
  let β' : ↥X := ⟨β, hbX⟩
  let Cc : Subgroup ↥X := centralizer ({β'} : Set ↥X)
  let ψ : ↥Cc →* Equiv.Perm (Fin n) := X.subtype.comp Cc.subtype
  have hψinj : Function.Injective ψ := X.subtype_injective.comp Cc.subtype_injective
  have hψK : ∀ c : ↥Cc, ψ c ∈ K := by
    intro c
    rw [hKeq]
    refine ⟨(c : ↥X).2, mem_centralizer_singleton_iff.2 ?_⟩
    have := mem_centralizer_singleton_iff.1 c.2
    exact congrArg Subtype.val this
  have hψsurj : ∀ y ∈ K, ∃ c : ↥Cc, ψ c = y := by
    intro y hy
    rw [hKeq] at hy
    obtain ⟨hyX, hyC⟩ := hy
    refine ⟨⟨⟨y, hyX⟩, mem_centralizer_singleton_iff.2 ?_⟩, rfl⟩
    exact Subtype.ext (mem_centralizer_singleton_iff.1 hyC)
  have hψrange : ψ.range = K := by
    ext y
    constructor
    · rintro ⟨c, rfl⟩
      exact hψK c
    · intro hy
      exact hψsurj y hy
  have hrepL : List.Forall₂ (Rep n) elts.toList (elts.toList.map (tablePerm n)) := by
    rw [List.forall₂_map_right_iff]
    apply List.forall₂_same.mpr
    intro T hT
    obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp hT)
    have := (hErep k hk).1
    rwa [getElem!_pos elts k hk] at this
  have hnodup := nodup_of_hkeysDistinct hrepL h8
  have huniq : ∀ a b, a < elts.size → b < elts.size → ∀ x : Equiv.Perm (Fin n), Rep n elts[a]! x →
      Rep n elts[b]! x → a = b := by
    intro a b ha hb x hax hbx
    have hl : (elts.toList.map (tablePerm n)).length = elts.size := by simp
    refine (hnodup.getElem_inj_iff (i := a) (j := b) (hi := by rw [hl]; exact ha)
      (hj := by rw [hl]; exact hb)).1 ?_
    simp only [List.getElem_map, Array.getElem_toList]
    rw [← getElem!_pos elts a ha, ← getElem!_pos elts b hb, tablePerm_eq hax, tablePerm_eq hbx]
  let idxOf : Equiv.Perm (Fin n) → ℕ := fun x =>
    if h : x ∈ K then Classical.choose (hcov x h) else 0
  have hidx : ∀ x ∈ K, idxOf x < elts.size ∧ Rep n elts[idxOf x]! x := by
    intro x hx
    simp only [idxOf, hx, dite_true]
    exact Classical.choose_spec (hcov x hx)
  have himgrep : ∀ k < elts.size, Rep 6 img[k]! (tp 6 img[k]!) := by
    intro k hk
    have h12a := h12
    rw [Array.all_eq_true'] at h12a
    exact rep_tp (h12a _ (getElem!_mem_array (by rw [h11]; exact hk)))
  have hpgrep : ∀ l < 2, Rep 6 pg[l]! (tp 6 pg[l]!) := by
    intro l hl
    have h4a := h4
    rw [Array.all_eq_true'] at h4a
    exact rep_tp (h4a _ (getElem!_mem_array (by rw [h3]; exact hl)))
  let gg : Fin 2 → Equiv.Perm (Fin n) := ![tp n tT, tp n dT]
  let φ : Fin 2 → Equiv.Perm (Fin 6) := fun l => tp 6 pg[(l : ℕ)]!
  have hgg_rep : ∀ l : Fin 2, Rep n gens[(l : ℕ)]! (gg l) := by
    intro l
    fin_cases l
    · exact rt
    · exact rd
  have hggK : ∀ l : Fin 2, gg l ∈ K := by
    intro l
    fin_cases l
    · exact htK
    · exact hdK
  let F : Equiv.Perm (Fin n) → Equiv.Perm (Fin 6) := fun x => tp 6 img[idxOf x]!
  have hcayP : ∀ x ∈ K, ∀ l : Fin 2, F (x * gg l) = F x * φ l := by
    intro x hx l
    obtain ⟨hk, hxk⟩ := hidx x hx
    have hxg : x * gg l ∈ K := mul_mem hx (hggK l)
    have h14a := h14
    rw [List.all_eq_true] at h14a
    have h14b := h14a (idxOf x) (List.mem_range.2 hk)
    rw [List.all_eq_true] at h14b
    have h14c := h14b l (List.mem_range.2 l.2)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h14c
    obtain ⟨hjlt, himgj⟩ := h14c
    obtain ⟨-, hjeq⟩ := idxTH_spec hjlt
    have hrepc : Rep n (compT n elts[idxOf x]! gens[(l : ℕ)]!) (x * gg l) :=
      Rep.compT hxk (hgg_rep l)
    have hrepj : Rep n elts[idxTH n elts (hashIndex n elts) (compT n elts[idxOf x]!
        gens[(l : ℕ)]!)]! (x * gg l) := rep_of_tblEq hrepc (tblEq_symm' hjeq)
    have hjk : idxOf (x * gg l) = idxTH n elts (hashIndex n elts) (compT n elts[idxOf x]!
        gens[(l : ℕ)]!) := huniq _ _ (hidx _ hxg).1 hjlt _ (hidx _ hxg).2 hrepj
    show tp 6 img[idxOf (x * gg l)]! = tp 6 img[idxOf x]! * φ l
    rw [hjk]
    have hrc : Rep 6 (compT 6 img[idxOf x]! pg[(l : ℕ)]!) (tp 6 img[idxOf x]! * φ l) :=
      Rep.compT (himgrep _ hk) (hpgrep l l.2)
    exact rep_unique (himgrep _ hjlt) (rep_of_tblEq hrc himgj)
  have hF1 : F 1 = 1 := by
    obtain ⟨hk, hrep⟩ := hidx 1 K.one_mem
    have h7a := h7
    simp only [mulTreeOK, Bool.and_eq_true, decide_eq_true_eq] at h7a
    have hr0 : Rep n elts[0]! (1 : Equiv.Perm (Fin n)) := rep_of_tblEq (Rep.idT hn) h7a.1.2
    have h0lt : 0 < elts.size := by omega
    have h0 : idxOf 1 = 0 := huniq _ _ hk h0lt 1 hrep hr0
    show tp 6 img[idxOf 1]! = 1
    rw [h0]
    exact rep_unique (himgrep 0 h0lt) (rep_of_tblEq (Rep.idT (by norm_num)) h13)
  have hFker : ∀ x ∈ K, F x = 1 ↔ (x = 1 ∨ x = β ∨ x = β * β) := by
    intro x hx
    obtain ⟨hk, hrep⟩ := hidx x hx
    have h15a := h15
    rw [List.all_eq_true] at h15a
    have hb := h15a _ (List.mem_range.2 hk)
    simp only [beq_iff_eq] at hb
    have hA : tblEq 6 img[idxOf x]! (idT 6) = true ↔ F x = 1 :=
      tblEq_idT_iff (by norm_num) (himgrep _ hk)
    have hB : tblEq n elts[idxOf x]! (idT n) = true ↔ x = 1 := tblEq_idT_iff hn hrep
    have hC : tblEq n elts[idxOf x]! bT = true ↔ x = β := tblEq_iff_eq hrep rb
    have hD : tblEq n elts[idxOf x]! (compT n bT bT) = true ↔ x = β * β :=
      tblEq_iff_eq hrep (Rep.compT rb rb)
    constructor
    · intro h
      have h' := hA.2 h
      rw [hb] at h'
      simp only [Bool.or_eq_true] at h'
      rcases h' with (h' | h') | h'
      · exact Or.inl (hB.1 h')
      · exact Or.inr (Or.inl (hC.1 h'))
      · exact Or.inr (Or.inr (hD.1 h'))
    · intro h
      apply hA.1
      rw [hb]
      simp only [Bool.or_eq_true]
      rcases h with h | h | h
      · exact Or.inl (Or.inl (hB.2 h))
      · exact Or.inl (Or.inr (hC.2 h))
      · exact Or.inr (hD.2 h)
  have hβC : β' ∈ Cc := mem_centralizer_singleton_iff.2 rfl
  obtain ⟨t', ht'⟩ := hψsurj _ htK
  obtain ⟨d', hd'⟩ := hψsurj _ hdK
  let gens' : Fin 2 → ↥Cc := ![t', d']
  have hψgens : ∀ l : Fin 2, ψ (gens' l) = gg l := by
    intro l
    fin_cases l
    · exact ht'
    · exact hd'
  have hgen' : closure (Set.range gens') = ⊤ := by
    apply Subgroup.map_injective hψinj
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, hψrange, ← Set.range_comp]
    have hr : Set.range (⇑ψ ∘ gens') = {tp n tT, tp n dT} := by
      ext y
      simp only [Set.mem_range, Function.comp_apply, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨l, rfl⟩
        rw [hψgens]
        fin_cases l
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨0, hψgens 0⟩
        · exact ⟨1, hψgens 1⟩
    rw [hr, hK, hgset]
  let Fc : ↥Cc → Equiv.Perm (Fin 6) := fun c => F (ψ c)
  have hFc1 : Fc 1 = 1 := by
    show F (ψ 1) = 1
    rw [map_one]
    exact hF1
  have hFcgen : ∀ c l, Fc (c * gens' l) = Fc c * φ l := by
    intro c l
    show F (ψ (c * gens' l)) = F (ψ c) * φ l
    rw [map_mul, hψgens]
    exact hcayP _ (hψK c) l
  have hFcmul := hom_of_cayley gens' φ hgen' Fc hFc1 hFcgen
  let π₀ : ↥Cc →* Equiv.Perm (Fin 6) :=
    { toFun := Fc
      map_one' := hFc1
      map_mul' := hFcmul }
  have hπ₀gen : ∀ l, π₀ (gens' l) = φ l := by
    intro l
    show Fc (gens' l) = φ l
    have := hFcgen 1 l
    rw [one_mul, hFc1, one_mul] at this
    exact this
  have hφalt : ∀ l : Fin 2, φ l ∈ alternatingGroup (Fin 6) := by
    intro l
    obtain ⟨σ, hσ, hrσ⟩ := hpg l l.2
    have : tp 6 pg[(l : ℕ)]! = σ := rep_unique (hpgrep l l.2) hrσ
    show tp 6 pg[(l : ℕ)]! ∈ alternatingGroup (Fin 6)
    rw [this]
    exact hσ
  have hAlt : ∀ c, π₀ c ∈ alternatingGroup (Fin 6) := by
    have hle : (⊤ : Subgroup ↥Cc) ≤ (alternatingGroup (Fin 6)).comap π₀ := by
      rw [← hgen', closure_le]
      rintro _ ⟨l, rfl⟩
      show π₀ (gens' l) ∈ alternatingGroup (Fin 6)
      rw [hπ₀gen]
      exact hφalt l
    intro c
    exact hle (mem_top c)
  let π : ↥Cc →* alternatingGroup (Fin 6) := π₀.codRestrict (alternatingGroup (Fin 6)) hAlt
  have hβ3 : orderOf β = 3 := (ordTest_iff_perm rb (by norm_num)).1 h5
  have hβ'3 : orderOf β' = 3 := by
    rw [← Subgroup.orderOf_coe β']
    exact hβ3
  have hker : ∀ x : ↥Cc, π x = 1 ↔ (x : ↥X) ∈ zpowers β' := by
    intro x
    have hx : ψ x ∈ K := hψK x
    have hπx : π x = 1 ↔ F (ψ x) = 1 := by
      rw [Subtype.ext_iff]
      rfl
    rw [hπx, hFker _ hx]
    constructor
    · rintro (h | h | h)
      · have : (x : ↥X) = 1 := Subtype.ext h
        rw [this]
        exact one_mem _
      · have : (x : ↥X) = β' := Subtype.ext h
        rw [this]
        exact mem_zpowers _
      · have : (x : ↥X) = β' ^ (2 : ℤ) := by
          apply Subtype.ext
          rw [zpow_two]
          exact h
        rw [this]
        exact zpow_mem (mem_zpowers _) _
    · intro hz
      obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hz
      have hj' : ψ x = β ^ j := by
        have := congrArg Subtype.val hj
        exact this.symm
      have hmod : β ^ j = β ^ (j % 3) := by
        have h := zpow_mod_orderOf β j
        rw [hβ3] at h
        simpa using h.symm
      have hjm : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
      rcases hjm with h | h | h
      · left
        rw [hj', hmod, h, zpow_zero]
      · right; left
        rw [hj', hmod, h, zpow_one]
      · right; right
        rw [hj', hmod, h, zpow_two]
  have hCcard : Nat.card ↥Cc = 1080 := by
    rw [← hKcard', ← hψrange]
    exact Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv
  let β'' : ↥Cc := ⟨β', hβC⟩
  have hβ''3 : orderOf β'' = 3 := by
    rw [← Subgroup.orderOf_coe β'']
    exact hβ'3
  have hkerEq : π.ker = zpowers β'' := by
    ext x
    rw [MonoidHom.mem_ker, hker x, mem_zpowers_iff, mem_zpowers_iff]
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, Subtype.ext (by simpa using hj)⟩
    · rintro ⟨j, hj⟩
      refine ⟨j, ?_⟩
      have := congrArg Subtype.val hj
      simp only [Subgroup.coe_zpow] at this
      exact this
  have hkercard : Nat.card π.ker = 3 := by rw [hkerEq, Nat.card_zpowers, hβ''3]
  have hrangecard : Nat.card π.range = 360 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange π).toEquiv, hCcard, hkercard] at h1
    omega
  have hAltcard : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup]
    simp [Nat.card_eq_fintype_card, Nat.factorial]
  have hrange : π.range = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [hrangecard, hAltcard])
  have hsurj : Function.Surjective π := MonoidHom.range_eq_top.1 hrange
  exact ⟨(hcomm tT htT).symm, BetaFor.of_hom hβ'3 π hsurj hker⟩

theorem betaHomCheck_permOK {n : ℕ} {tT dT bT : Table} {pg : Array Table}
    (hchk : betaHomCheck n tT dT bT pg = true) :
    permOK n tT = true ∧ permOK n dT = true ∧ permOK n bT = true := by
  simp only [betaHomCheck, Bool.and_eq_true, beq_iff_eq] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hchk
  rw [Array.all_eq_true'] at h1
  simp only [Bool.and_eq_true] at h1
  exact ⟨(h1 tT (by simp)).1, (h1 dT (by simp)).1, h2⟩


end CFSG.EvenSporadicStandard.Fin76b.Beta
