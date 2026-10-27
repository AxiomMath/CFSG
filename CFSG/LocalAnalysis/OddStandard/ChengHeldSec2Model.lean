module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec2Aux
public import Certificates.Data.ChengHeldSec2Facts
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModel

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.OddStandard.ChengHeldData CFSG.OddStandard.ChengHeld.Model
open CFSG.OddStandard.ChengHeld.M1b (evalE)

theorem chSec2_parts (h : chSec2OK = true) :
    (∀ α, α ≤ 1 → ∀ k, k ≤ 2 → twOK α k = true) ∧
      ∀ α, α ≤ 1 → sqVOK α = true ∧ eaCentOK α = true ∧ pairFixOK α = true ∧
        graphOK α = true ∧ notCentVOK α 0 = true ∧ notCentVOK α 2 = true ∧
        unitFixOK α = true := by
  have key : ∀ α, α ≤ 1 → (twM (mkReg α) α 0 = true ∧ twM (mkReg α) α 1 = true ∧
      twM (mkReg α) α 2 = true ∧ sqVM (mkReg α) = true ∧ eaCentM (mkReg α) = true ∧
      pairFixM (mkReg α) α = true ∧ graphM (mkReg α) α = true ∧
      notCentVM (mkReg α) α 0 = true ∧ notCentVM (mkReg α) α 2 = true ∧
      unitFixM (mkReg α) α = true) := by
    intro α hα
    simp only [chSec2OK, List.all_eq_true, List.mem_cons, List.mem_nil_iff, or_false,
      forall_eq_or_imp, forall_eq, Bool.and_eq_true, and_assoc] at h
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := h
    interval_cases α
    · exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩
    · exact ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9⟩
  refine ⟨fun α hα k hk => ?_, fun α hα => ?_⟩
  · obtain ⟨a0, a1, a2, -⟩ := key α hα
    interval_cases k
    exacts [a0, a1, a2]
  · obtain ⟨-, -, -, a3, a4, a5, a6, a7, a8, a9⟩ := key α hα
    exact ⟨a3, a4, a5, a6, a7, a8, a9⟩

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {α : ℕ}

omit [Finite G] in
theorem mem_zpowers_sub_iff {S : Subgroup G} {a x : ↥S} :
    x ∈ zpowers a ↔ (x : G) ∈ zpowers (a : G) := by
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by simp⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem Datum.conj_inv_mem_S (d : Datum A) {y : G} (hy : y ∈ d.X) :
    ∀ s ∈ d.S, y⁻¹ * s * y ∈ d.S := fun s hs => by
  simpa using d.conj_mem_S (d.X.inv_mem hy) hs

theorem Chart4.act_table (hα : α ≤ 1) (c : Chart4 d α) (k : Kind) {y : G}
    (hact : k.Act α c.t c.pi c.tau c.mu c.lam c.ze c.xi y) :
    ∀ e ∈ tableRels α (kind0 k),
      y⁻¹ * ((natFam c.fam e.1 : ↥d.S) : G) * y = ((evalE (natFam c.fam) e.2 : ↥d.S) : G) := by
  intro e he
  have hg : tableRels α (kind0 k) = actRels α (kind0 k) := by
    simp [tableRels, show α ≠ 2 by omega]
  rw [hg] at he
  have := rels_of_act α hα k (natFam c.famG) y hact e he
  rw [coe_evalE_natFam d.S c.fam]
  have hf : (fun j => ((c.fam j : ↥d.S) : G)) = c.famG := funext c.subtype_fam
  have hn : ∀ i, ((natFam c.fam i : ↥d.S) : G) = natFam c.famG i := fun i => by
    simp only [natFam]; exact c.subtype_fam _
  rw [hn, hf]
  exact this

theorem Chart4.aut_pt (hα : α ≤ 1) (c : Chart4 d α) (R : Rep (mkReg α) ↥d.S)
    (hR : ∀ j : Fin 7, R.pt (c.fam j) = (mkReg α).g j.val) (hT : TreeSpec (mkReg α)) (k : Kind)
    {y : G} (hy : y ∈ d.X) (hact : k.Act α c.t c.pi c.tau c.mu c.lam c.ze c.xi y)
    (s : ↥d.S) :
    (autArr (mkReg α) α (kind0 k))[R.pt s]! =
      R.pt ⟨y⁻¹ * (s : G) * y, d.conj_inv_mem_S hy s s.2⟩ := by
  have hy' := d.conj_inv_mem_S hy
  exact (autOK_rec R hT c.fam hR (by omega) (by cases k <;> decide)
    (AutAux.conjHom d.S y hy') (AutAux.actTable_conjHom c.fam hy' (c.act_table hα k hact))).2 s

theorem Chart4.aut_size (hα : α ≤ 1) (c : Chart4 d α) (R : Rep (mkReg α) ↥d.S)
    (hR : ∀ j : Fin 7, R.pt (c.fam j) = (mkReg α).g j.val) (hT : TreeSpec (mkReg α)) (k : Kind)
    {y : G} (hy : y ∈ d.X) (hact : k.Act α c.t c.pi c.tau c.mu c.lam c.ze c.xi y) :
    (autArr (mkReg α) α (kind0 k)).size = (mkReg α).N := by
  have hy' := d.conj_inv_mem_S hy
  exact (autOK_rec R hT c.fam hR (by omega) (by cases k <;> decide)
    (AutAux.conjHom d.S y hy') (AutAux.actTable_conjHom c.fam hy' (c.act_table hα k hact))).1

theorem Chart4.set_secZ (c : Chart4 d α) (R : Rep (mkReg α) ↥d.S)
    (hR : ∀ j : Fin 7, R.pt (c.fam j) = (mkReg α).g j.val) :
    R.set (secZ (mkReg α)) = (zpowers (c.fam 0) : Set ↥d.S) := by
  unfold secZ
  rw [show (mkReg α).g 0 = R.pt (c.fam 0) from (hR 0).symm]
  exact S4Aux.set_cl1 R _

theorem Chart4.set_secV (c : Chart4 d α) (R : Rep (mkReg α) ↥d.S)
    (hR : ∀ j : Fin 7, R.pt (c.fam j) = (mkReg α).g j.val) :
    R.set (secV (mkReg α)) = (sV c.fam : Set ↥d.S) := by
  unfold secV
  rw [show (mkReg α).g 0 = R.pt (c.fam 0) from (hR 0).symm,
    show (mkReg α).g 1 = R.pt (c.fam 1) from (hR 1).symm,
    show (mkReg α).g 2 = R.pt (c.fam 2) from (hR 2).symm, ← R.pt_pow, ← R.pt_mul]
  exact S4Aux.set_cl3 R _ _ _

theorem Chart4.size_secV (c : Chart4 d α) (R : Rep (mkReg α) ↥d.S)
    (hR : ∀ j : Fin 7, R.pt (c.fam j) = (mkReg α).g j.val) :
    (secV (mkReg α)).size = (mkReg α).N := by
  unfold secV
  rw [show (mkReg α).g 0 = R.pt (c.fam 0) from (hR 0).symm,
    show (mkReg α).g 1 = R.pt (c.fam 1) from (hR 1).symm,
    show (mkReg α).g 2 = R.pt (c.fam 2) from (hR 2).symm, ← R.pt_pow, ← R.pt_mul]
  exact S4Aux.size_cl3 R _ _ _

theorem Chart4.set_secW (c : Chart4 d α) (R : Rep (mkReg α) ↥d.S)
    (hR : ∀ j : Fin 7, R.pt (c.fam j) = (mkReg α).g j.val) :
    R.set ((mkReg α).cent (secV (mkReg α))) = (sW c.fam : Set ↥d.S) :=
  S4Aux.set_cent_of R (c.size_secV R hR) (c.set_secV R hR)

theorem Chart4.twist_fact (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A) (hP : chPresOK = true)
    (hS2 : chSec2OK = true) (k : Kind) {y : G} (hy : y ∈ d.X)
    (hact : k.Act α c.t c.pi c.tau c.mu c.lam c.ze c.xi y) {s₀ : G} (hs₀ : s₀ ∈ d.S)
    (hz : s₀ * (y⁻¹ * s₀ * y) ∈ zpowers c.t) :
    ∃ s ∈ d.S, s⁻¹ * s₀ * (y⁻¹ * s * y) ∈ zpowers c.t := by
  obtain ⟨R, hR⟩ := c.exists_rep hα h hP
  have hT := treeSpec_mkReg (α := α) (by omega) hP
  have hk : twOK α (kind0 k) = true := (chSec2_parts hS2).1 α hα _ (by cases k <;> decide)
  have ha := c.aut_pt hα R hR hT k hy hact
  have hZ := c.set_secZ R hR
  simp only [twOK, twM, List.all_eq_true, List.any_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true'] at hk
  set σ : ↥d.S → ↥d.S := fun u => ⟨y⁻¹ * (u : G) * y, d.conj_inv_mem_S hy u u.2⟩ with hσ
  have hcoe : ∀ u : ↥d.S, ((σ u : ↥d.S) : G) = y⁻¹ * (u : G) * y := fun u => rfl
  have ht0 : ((c.fam 0 : ↥d.S) : G) = c.t := rfl
  rcases hk (R.pt ⟨s₀, hs₀⟩) (R.pt_lt _) with h1 | ⟨p, hp, h2⟩
  · exfalso
    rw [ha, ← R.pt_mul] at h1
    have hmem : (⟨s₀, hs₀⟩ * σ ⟨s₀, hs₀⟩ : ↥d.S) ∈ R.set (secZ (mkReg α)) := by
      rw [hZ]
      exact mem_zpowers_sub_iff.2 (by rw [ht0]; simpa [hcoe] using hz)
    rw [Rep.mem_set, h1] at hmem
    exact Bool.false_ne_true hmem
  · obtain ⟨u, rfl⟩ := R.pt_surj p hp
    refine ⟨u, u.2, ?_⟩
    rw [ha u, ← R.pt_inv, ← R.pt_mul, ← R.pt_mul] at h2
    have hmem : (u⁻¹ * ⟨s₀, hs₀⟩ * σ u : ↥d.S) ∈ R.set (secZ (mkReg α)) := R.mem_set.2 h2
    rw [hZ] at hmem
    have := mem_zpowers_sub_iff.1 hmem
    rw [ht0] at this
    simpa [hcoe] using this

theorem Chart4.sq_V_fact (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A) (hP : chPresOK = true)
    (hS2 : chSec2OK = true) : ∀ v ∈ c.V, ∃ w ∈ c.W, w * w = v := by
  obtain ⟨R, hR⟩ := c.exists_rep hα h hP
  have hk : sqVOK α = true := ((chSec2_parts hS2).2 α hα).1
  have eV := c.set_secV R hR
  have eW := c.set_secW R hR
  have nV := c.size_secV R hR
  have nW := Rep.cent_size (M := mkReg α) (secV (mkReg α))
  simp only [sqVOK, sqVM, List.all_eq_true, List.any_eq_true, beq_iff_eq] at hk
  intro v hv
  rw [← SFacts4Aux.map_sV c] at hv
  obtain ⟨v', hv', rfl⟩ := hv
  have hpt : R.pt v' ∈ RegModel.elems (secV (mkReg α)) :=
    (R.mem_elems_iff_exists_pt nV).2 ⟨v', rfl, by rw [eV]; exact hv'⟩
  obtain ⟨pw, hpw, hmul⟩ := hk _ hpt
  obtain ⟨w', rfl, hw'⟩ := (R.mem_elems_iff_exists_pt nW).1 hpw
  rw [eW] at hw'
  refine ⟨(w' : G), ?_, ?_⟩
  · rw [← SFacts4Aux.map_sW c]
    exact ⟨w', hw', rfl⟩
  · have : R.pt (w' * w') = R.pt v' := by rw [R.pt_mul]; exact hmul
    exact congrArg Subtype.val (R.pt_inj this)

theorem Chart4.notCent_V_fact (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A)
    (hP : chPresOK = true) (hS2 : chSec2OK = true) (k : Kind) (hk : k ≠ Kind.graph) {y : G}
    (hy : y ∈ d.X) (hact : k.Act α c.t c.pi c.tau c.mu c.lam c.ze c.xi y) :
    ∀ s ∈ d.S, ∃ v ∈ c.V, y⁻¹ * (s⁻¹ * v * s) * y ≠ v := by
  obtain ⟨R, hR⟩ := c.exists_rep hα h hP
  have hT := treeSpec_mkReg (α := α) (by omega) hP
  have hk' : notCentVOK α (kind0 k) = true := by
    obtain ⟨-, -, -, -, h0, h2, -⟩ := (chSec2_parts hS2).2 α hα
    cases k
    · exact h0
    · exact absurd rfl hk
    · exact h2
  have ha := c.aut_pt hα R hR hT k hy hact
  have eV := c.set_secV R hR
  have nV := c.size_secV R hR
  simp only [notCentVOK, notCentVM, List.all_eq_true, List.any_eq_true, List.mem_range, bne_iff_ne,
    ne_eq] at hk'
  intro s hs
  obtain ⟨pv, hpv, hne⟩ := hk' (R.pt ⟨s, hs⟩) (R.pt_lt _)
  obtain ⟨v', rfl, hv'⟩ := (R.mem_elems_iff_exists_pt nV).1 hpv
  rw [eV] at hv'
  refine ⟨(v' : G), ?_, fun heq => hne ?_⟩
  · rw [← SFacts4Aux.map_sV c]
    exact ⟨v', hv', rfl⟩
  · rw [← R.pt_cj, ha]
    exact congrArg R.pt (Subtype.ext (by simpa using heq))

theorem Chart4.ea8_fact (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A) (hP : chPresOK = true)
    (hS2 : chSec2OK = true) {E : Subgroup G} (hE : E ≤ d.S)
    (hab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (h2 : ∀ a ∈ E, a * a = 1)
    (hcard : Nat.card E = 8) :
    E = c.V ∨ (Nat.card ↥(d.S ⊓ centralizer (E : Set G)) ≤ 16 ∧
      ∀ s ∈ d.S ⊓ centralizer (E : Set G), s ^ 4 = 1) := by
  obtain ⟨R, hR⟩ := c.exists_rep hα h hP
  have hk : eaCentOK α = true := ((chSec2_parts hS2).2 α hα).2.1
  have eV := c.set_secV R hR
  have nV := c.size_secV R hR
  set E' : Subgroup ↥d.S := E.subgroupOf d.S with hE'
  have hmemE' : ∀ s : ↥d.S, s ∈ E' ↔ (s : G) ∈ E := fun s => mem_subgroupOf
  have hE'ab : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := fun a ha b hb =>
    Subtype.ext (hab _ ((hmemE' a).1 ha) _ ((hmemE' b).1 hb))
  have hE'sq : ∀ a ∈ E', a * a = 1 := fun a ha => Subtype.ext (h2 _ ((hmemE' a).1 ha))
  have hE'card : Nat.card E' = 2 ^ 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv, hcard]
    norm_num
  obtain ⟨l, hl, hlE⟩ := R.eaL_complete 3 (by norm_num) E' hE'ab hE'sq hE'card
  have hl' : l ∈ secEA3 (mkReg α) := hl
  unfold eaCentOK eaCentM at hk
  rw [Array.all_eq_true'] at hk
  have hkl := hk l hl'
  have hBsz : (secBitmap (mkReg α) l).size = (mkReg α).N := by simp [secBitmap]
  have hB : R.set (secBitmap (mkReg α) l) = (E' : Set ↥d.S) := by
    ext s
    rw [R.mem_set]
    unfold secBitmap
    rw [Rep.getElem!_range_map_of_lt _ (R.pt_lt s)]
    rw [SetLike.mem_coe, hlE s]
    simp [Array.mem_toList_iff]
  have hEmap : E'.map d.S.subtype = E := Subgroup.map_subgroupOf_eq_of_le hE
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true] at hkl
  rcases hkl with hVeq | ⟨hc16, hexp⟩
  · left
    have : E' = sV c.fam := S4Aux.eq_of_bitmap R hB eV hVeq
    rw [← hEmap, this, SFacts4Aux.map_sV c]
  · right
    have hCset : R.set ((mkReg α).cent (secBitmap (mkReg α) l)) =
        (centralizer (E' : Set ↥d.S) : Set ↥d.S) := S4Aux.set_cent_of R hBsz hB
    have hCsz := Rep.cent_size (M := mkReg α) (secBitmap (mkReg α) l)
    have hCard : Nat.card (centralizer (E' : Set ↥d.S)) =
        RegModel.card ((mkReg α).cent (secBitmap (mkReg α) l)) :=
      (S4Aux.card_of R hCsz hCset).symm
    have hmapC : (centralizer (E' : Set ↥d.S)).map d.S.subtype = d.S ⊓ centralizer (E : Set G) := by
      rw [← top_inf_eq (centralizer (E' : Set ↥d.S)), SFacts4Aux.map_inf_centralizer,
        SFacts4Aux.map_top_subtype, hEmap]
    refine ⟨?_, ?_⟩
    · rw [← hmapC, SFacts4Aux.card_map, hCard]
      exact hc16
    · intro s hs
      have hs' : (⟨s, hs.1⟩ : ↥d.S) ∈ R.set ((mkReg α).cent (secBitmap (mkReg α) l)) := by
        rw [hCset]
        intro e he
        have := (mem_centralizer_iff.1 hs.2) (e : G) ((hmemE' e).1 he)
        exact Subtype.ext this
      have hpt := hexp (R.pt ⟨s, hs.1⟩) ((R.mem_elems_iff_exists_pt hCsz).2 ⟨_, rfl, hs'⟩)
      have : R.pt ((⟨s, hs.1⟩ : ↥d.S) ^ 4) = R.pt 1 := by rw [R.pt_pow, R.pt_one]; exact hpt
      have h4 := R.pt_inj this
      exact congrArg Subtype.val h4

theorem pair_aux (M : RegModel) {H : List ℕ} {Es : Finset ℕ} (hnd : H.Nodup)
    (hsub : ∀ x ∈ Es, x ∈ H) (hE : Es.card = 8) (hsq : ∀ x ∈ Es, M.m x x = 0)
    (hchk : (H.length < 8 || (H.length == 8 && H.any fun x => M.m x x != 0)) = true) : False := by
  have hle : Es.card ≤ H.toFinset.card :=
    Finset.card_le_card fun x hx => List.mem_toFinset.2 (hsub x hx)
  rw [List.toFinset_card_of_nodup hnd, hE] at hle
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq,
    List.any_eq_true, bne_iff_ne] at hchk
  rcases hchk with hlt | ⟨hlen, x, hx, hne⟩
  · omega
  · have heq : Es = H.toFinset := by
      refine Finset.eq_of_subset_of_card_le (fun x hx => List.mem_toFinset.2 (hsub x hx)) ?_
      rw [List.toFinset_card_of_nodup hnd, hlen, hE]
    have hxE : x ∈ Es := by rw [heq]; exact List.mem_toFinset.2 hx
    exact hne (hsq x hxE)

theorem graph_aux (M : RegModel) {Gl : List ℕ} {Es : Finset ℕ} (hnd : Gl.Nodup)
    (hsub : ∀ x ∈ Es, x ∈ Gl) (hE : 32 ≤ Es.card) (hcl : ∀ x ∈ Es, ∀ y ∈ Es, M.m x y ∈ Es)
    (hchk : (Gl.length < 32 || (Gl.length == 32 &&
      Gl.any fun x => Gl.any fun y => !(Gl.contains (M.m x y)))) = true) : False := by
  have hle : Es.card ≤ Gl.toFinset.card :=
    Finset.card_le_card fun x hx => List.mem_toFinset.2 (hsub x hx)
  rw [List.toFinset_card_of_nodup hnd] at hle
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq,
    List.any_eq_true, Bool.not_eq_true'] at hchk
  rcases hchk with hlt | ⟨hlen, x, hx, y, hy, hne⟩
  · omega
  · have heq : Es = Gl.toFinset := by
      refine Finset.eq_of_subset_of_card_le (fun x hx => List.mem_toFinset.2 (hsub x hx)) ?_
      rw [List.toFinset_card_of_nodup hnd]
      omega
    have hxE : x ∈ Es := by rw [heq]; exact List.mem_toFinset.2 hx
    have hyE : y ∈ Es := by rw [heq]; exact List.mem_toFinset.2 hy
    have hm := hcl x hxE y hyE
    rw [heq] at hm
    have := List.mem_toFinset.1 hm
    simp [this] at hne

theorem exists_points_finset {M : RegModel} {H : Type} [Group H] (R : Rep M H) (K : Subgroup H) :
    ∃ Es : Finset ℕ, Es.card = Nat.card K ∧ (∀ x, x ∈ Es ↔ ∃ k ∈ K, R.pt k = x) := by
  have := R.finite
  have hfin : (R.pt '' (K : Set H)).Finite := Set.toFinite _
  refine ⟨hfin.toFinset, ?_, fun x => ?_⟩
  · rw [← Set.ncard_eq_toFinset_card _ hfin, Set.ncard_image_of_injective _ R.pt_inj,
      ← Nat.card_coe_set_eq]
    rfl
  · simp [Set.Finite.mem_toFinset]

theorem Chart4.pairFix_fact (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A) (hP : chPresOK = true)
    (hS2 : chSec2OK = true) {y₁ y₂ : G} (hy₁ : y₁ ∈ d.X) (hy₂ : y₂ ∈ d.X)
    (h₁ : Kind.field.Act α c.t c.pi c.tau c.mu c.lam c.ze c.xi y₁)
    (h₂ : Kind.graph.Act α c.t c.pi c.tau c.mu c.lam c.ze c.xi y₂) {s₁ s₂ : G}
    (hs₁ : s₁ ∈ d.S) (hs₂ : s₂ ∈ d.S) {E : Subgroup G} (hE : E ≤ d.S)
    (h2 : ∀ a ∈ E, a * a = 1) (hcard : Nat.card E = 8) :
    ¬ ∀ e ∈ E, y₁⁻¹ * (s₁⁻¹ * e * s₁) * y₁ = e ∧ y₂⁻¹ * (s₂⁻¹ * e * s₂) * y₂ = e := by
  intro hfix
  obtain ⟨R, hR⟩ := c.exists_rep hα h hP
  have hT := treeSpec_mkReg (α := α) (by omega) hP
  have hk : pairFixOK α = true := ((chSec2_parts hS2).2 α hα).2.2.1
  have ha1 : ∀ s : ↥d.S, (autArr (mkReg α) α 0)[R.pt s]! =
      R.pt ⟨y₁⁻¹ * (s : G) * y₁, d.conj_inv_mem_S hy₁ s s.2⟩ :=
    c.aut_pt hα R hR hT Kind.field hy₁ h₁
  have ha2 : ∀ s : ↥d.S, (autArr (mkReg α) α 1)[R.pt s]! =
      R.pt ⟨y₂⁻¹ * (s : G) * y₂, d.conj_inv_mem_S hy₂ s s.2⟩ :=
    c.aut_pt hα R hR hT Kind.graph hy₂ h₂
  simp only [pairFixOK, pairFixM, List.all_eq_true, List.mem_range] at hk
  have hkk := hk (R.pt ⟨s₁, hs₁⟩) (R.pt_lt _) (R.pt ⟨s₂, hs₂⟩) (R.pt_lt _)
  unfold pairCase at hkk
  set E' : Subgroup ↥d.S := E.subgroupOf d.S with hE'
  have hmemE' : ∀ s : ↥d.S, s ∈ E' ↔ (s : G) ∈ E := fun s => mem_subgroupOf
  have hE'card : Nat.card E' = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv, hcard]
  obtain ⟨Es, hEs, hmem⟩ := exists_points_finset R E'
  refine pair_aux (mkReg α) (Es := Es) ?_ ?_ (hEs.trans hE'card) ?_ hkk
  · exact (List.nodup_range.filter _).filter _
  · intro x hx
    obtain ⟨e, he, rfl⟩ := (hmem x).1 hx
    unfold pairSet fixSet1
    rw [List.mem_filter, List.mem_filter, List.mem_range]
    obtain ⟨f1, f2⟩ := hfix (e : G) ((hmemE' e).1 he)
    simp only [beq_iff_eq]
    rw [← R.pt_cj, ← R.pt_cj, ha1, ha2]
    exact ⟨⟨R.pt_lt e, congrArg R.pt (Subtype.ext (by simpa using f1))⟩,
      congrArg R.pt (Subtype.ext (by simpa using f2))⟩
  · intro x hx
    obtain ⟨e, he, rfl⟩ := (hmem x).1 hx
    rw [← R.pt_mul, ← R.pt_one]
    exact congrArg R.pt (Subtype.ext (h2 _ ((hmemE' e).1 he)))

theorem Chart4.graph_fact (hα : α = 1) (c : Chart4 d α) (h : Hyp G A) (hP : chPresOK = true)
    (hS2 : chSec2OK = true) {y : G} (hy : y ∈ d.X)
    (hact : Kind.graph.Act α c.t c.pi c.tau c.mu c.lam c.ze c.xi y) {s : G} (hs : s ∈ c.W)
    {cc : G} (hcc : cc ∈ zpowers c.t) (W₁ : Subgroup G) (hW₁ : W₁ ≤ c.W)
    (hcard : 32 ≤ Nat.card W₁)
    (hsq : ∀ x ∈ W₁, (cc * s * (y⁻¹ * s * y)) * (y⁻¹ * (s⁻¹ * x * s) * y) * x ∈ c.V ∧
      (cc * s * (y⁻¹ * s * y)) * (y⁻¹ * (s⁻¹ * x * s) * y) * x ≠ 1) : False := by
  have hα1 : α ≤ 1 := by omega
  obtain ⟨R, hR⟩ := c.exists_rep hα1 h hP
  have hT := treeSpec_mkReg (α := α) (by omega) hP
  have hk : graphOK α = true := ((chSec2_parts hS2).2 α hα1).2.2.2.1
  have ha : ∀ u : ↥d.S, (autArr (mkReg α) α 1)[R.pt u]! =
      R.pt ⟨y⁻¹ * (u : G) * y, d.conj_inv_mem_S hy u u.2⟩ :=
    c.aut_pt hα1 R hR hT Kind.graph hy hact
  have eV := c.set_secV R hR
  have nV := c.size_secV R hR
  have eW := c.set_secW R hR
  have nW := Rep.cent_size (M := mkReg α) (secV (mkReg α))
  have hα0 : (α == 0) = false := by simp [hα]
  simp only [graphOK, graphM, hα0, Bool.false_or, List.all_eq_true, List.mem_range] at hk
  obtain ⟨s', hs'W, hs'⟩ : ∃ s' : ↥d.S, s' ∈ sW c.fam ∧ (s' : G) = s := by
    have := hs
    rw [← SFacts4Aux.map_sW c] at this
    obtain ⟨s', h1, h2⟩ := this
    exact ⟨s', h1, h2⟩
  have hccS : cc ∈ d.S := (zpowers_le.2 c.t_mem.2) hcc
  obtain ⟨n, hn4, hccn⟩ := c.exists_pow_t hcc
  set cc' : ↥d.S := ⟨cc, hccS⟩ with hcc'def
  have hcc' : cc' = (c.fam 0) ^ n := Subtype.ext (by rw [Subgroup.coe_pow]; exact hccn)
  have hptcc : R.pt cc' = (mkReg α).pw ((mkReg α).g 0) n := by rw [hcc', R.pt_pow, hR 0]; rfl
  have hspt : R.pt s' ∈ RegModel.elems ((mkReg α).cent (secV (mkReg α))) :=
    (R.mem_elems_iff_exists_pt nW).2 ⟨s', rfl, by rw [eW]; exact hs'W⟩
  have hcase := hk (R.pt s') hspt n hn4
  rw [← hptcc] at hcase
  unfold graphCase at hcase
  set σ : ↥d.S → ↥d.S := fun u => ⟨y⁻¹ * (u : G) * y, d.conj_inv_mem_S hy u u.2⟩ with hσ
  have hσc : ∀ u : ↥d.S, ((σ u : ↥d.S) : G) = y⁻¹ * (u : G) * y := fun u => rfl
  have hepoint : (mkReg α).m (R.pt cc') ((mkReg α).m (R.pt s') (autArr (mkReg α) α 1)[R.pt s']!) =
      R.pt (cc' * (s' * σ s')) := by rw [ha, ← R.pt_mul, ← R.pt_mul]
  rw [hepoint] at hcase
  have memV : ∀ u : ↥d.S, (u : G) ∈ c.V ↔ u ∈ sV c.fam := fun u => by
    rw [← SFacts4Aux.map_sV c]
    exact SFacts4Aux.coe_mem_map d.S _ u
  have memW : ∀ u : ↥d.S, (u : G) ∈ c.W ↔ u ∈ sW c.fam := fun u => by
    rw [← SFacts4Aux.map_sW c]
    exact SFacts4Aux.coe_mem_map d.S _ u
  have hsq1 := hsq 1 W₁.one_mem
  have he'coe : ((cc' * (s' * σ s') : ↥d.S) : G) = cc * s * (y⁻¹ * s * y) := by
    simp only [Subgroup.coe_mul, hσc, hs', mul_assoc]
    rfl
  have hsq1' : cc * s * (y⁻¹ * s * y) * (y⁻¹ * (s⁻¹ * 1 * s) * y) * 1 = cc * s * (y⁻¹ * s * y) := by
    group
  rw [hsq1'] at hsq1
  have hinV : inV1 (secV (mkReg α)) (R.pt (cc' * (s' * σ s'))) = true := by
    unfold inV1
    rw [Bool.and_eq_true, bne_iff_ne]
    refine ⟨R.mem_set.1 (by rw [eV]; exact (memV _).1 (by rw [he'coe]; exact hsq1.1)), ?_⟩
    intro h0
    apply hsq1.2
    rw [← he'coe]
    have := R.pt_inj (h0.trans R.pt_one.symm)
    rw [this]
    rfl
  dsimp only at hcase
  rw [hinV] at hcase
  simp only [Bool.not_true, Bool.false_or] at hcase
  obtain ⟨Es, hEs, hmem⟩ := exists_points_finset R (W₁.subgroupOf d.S)
  have hW₁S : W₁ ≤ d.S := hW₁.trans inf_le_left
  have hcardW₁ : Nat.card (W₁.subgroupOf d.S) = Nat.card W₁ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW₁S).toEquiv
  refine graph_aux (mkReg α) (Es := Es) ?_ ?_ (by omega) ?_ hcase
  · exact (Rep.elems_nodup _).filter _
  · intro x hx
    obtain ⟨w, hw, rfl⟩ := (hmem x).1 hx
    have hwW₁ : (w : G) ∈ W₁ := mem_subgroupOf.1 hw
    unfold graphSet
    rw [List.mem_filter]
    refine ⟨(R.mem_elems_iff_exists_pt nW).2 ⟨w, rfl, by rw [eW]; exact (memW w).1 (hW₁ hwW₁)⟩, ?_⟩
    have hs'w : ((⟨y⁻¹ * ((s'⁻¹ * w * s' : ↥d.S) : G) * y, d.conj_inv_mem_S hy _
        (s'⁻¹ * w * s').2⟩ : ↥d.S)) = σ (s'⁻¹ * w * s') := rfl
    have hpt : (mkReg α).m ((mkReg α).m (R.pt (cc' * (s' * σ s')))
        (autArr (mkReg α) α 1)[(mkReg α).cj (R.pt w) (R.pt s')]!) (R.pt w) =
        R.pt (cc' * (s' * σ s') * σ (s'⁻¹ * w * s') * w) := by
      rw [← R.pt_cj, ha, ← R.pt_mul, ← R.pt_mul]
    rw [hpt]
    have key := hsq (w : G) hwW₁
    have hcoe : ((cc' * (s' * σ s') * σ (s'⁻¹ * w * s') * w : ↥d.S) : G) =
        cc * s * (y⁻¹ * s * y) * (y⁻¹ * (s⁻¹ * (w : G) * s) * y) * w := by
      simp only [Subgroup.coe_mul, hσc, Subgroup.coe_inv, hs', mul_assoc]
      rfl
    unfold inV1
    rw [Bool.and_eq_true, bne_iff_ne]
    refine ⟨R.mem_set.1 (by rw [eV]; exact (memV _).1 (by rw [hcoe]; exact key.1)), ?_⟩
    intro h0
    apply key.2
    rw [← hcoe]
    have := R.pt_inj (h0.trans R.pt_one.symm)
    rw [this]
    rfl
  · intro x hx z hz
    obtain ⟨w₁, hw₁, rfl⟩ := (hmem x).1 hx
    obtain ⟨w₂, hw₂, rfl⟩ := (hmem z).1 hz
    exact (hmem _).2 ⟨w₁ * w₂, mul_mem hw₁ hw₂, R.pt_mul _ _⟩

theorem Chart4.unitary_fix_fact (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A)
    (hP : chPresOK = true) (hS2 : chSec2OK = true) {y : G} (hy : y ∈ d.X)
    (hact : Kind.unitary.Act α c.t c.pi c.tau c.mu c.lam c.ze c.xi y) :
    (∀ s ∈ d.S, (y⁻¹ * s * y = s ↔
      s ∈ closure ({d.q, c.mu * c.lam * c.xi * c.tau} : Set G))) ∨
    (∀ s ∈ d.S, (y⁻¹ * s * y = s ↔
      s ∈ closure ({d.q, c.mu * c.lam * c.xi * c.tau * c.t} : Set G))) := by
  obtain ⟨R, hR⟩ := c.exists_rep hα h hP
  have hT := treeSpec_mkReg (α := α) (by omega) hP
  have hk : unitFixOK α = true := ((chSec2_parts hS2).2 α hα).2.2.2.2.2.2
  have hy' := d.conj_inv_mem_S hy
  have ha : ∀ s : ↥d.S, (autArr (mkReg α) α 2)[R.pt s]! =
      R.pt (AutAux.conjHom d.S y hy' s) := c.aut_pt hα R hR hT Kind.unitary hy hact
  have hfix : R.set ((mkReg α).fixedPts (autArr (mkReg α) α 2)) =
      {u : ↥d.S | AutAux.conjHom d.S y hy' u = u} :=
    R.set_fixedPts (AutAux.conjHom d.S y hy') ha
  have hsz : (autArr (mkReg α) α 2).size = (mkReg α).N :=
    c.aut_size hα R hR hT Kind.unitary hy hact
  have e0 : (mkReg α).g 0 = R.pt (c.fam 0) := (hR 0).symm
  have e2 : (mkReg α).g 2 = R.pt (c.fam 2) := (hR 2).symm
  have e3 : (mkReg α).g 3 = R.pt (c.fam 3) := (hR 3).symm
  have e4 : (mkReg α).g 4 = R.pt (c.fam 4) := (hR 4).symm
  have e6 : (mkReg α).g 6 = R.pt (c.fam 6) := (hR 6).symm
  have hq : (mkReg α).pw ((mkReg α).g 0) 2 = R.pt (c.fam 0 ^ 2) := by rw [e0, R.pt_pow]
  have hm : (mkReg α).m ((mkReg α).m ((mkReg α).m ((mkReg α).g 3) ((mkReg α).g 4))
      ((mkReg α).g 6)) ((mkReg α).g 2) =
      R.pt (c.fam 3 * c.fam 4 * c.fam 6 * c.fam 2) := by
    rw [e3, e4, e6, e2, ← R.pt_mul, ← R.pt_mul, ← R.pt_mul]
  have hmt : (mkReg α).m ((mkReg α).m ((mkReg α).m ((mkReg α).m ((mkReg α).g 3) ((mkReg α).g 4))
      ((mkReg α).g 6)) ((mkReg α).g 2)) ((mkReg α).g 0) =
      R.pt (c.fam 3 * c.fam 4 * c.fam 6 * c.fam 2 * c.fam 0) := by
    rw [e3, e4, e6, e2, e0, ← R.pt_mul, ← R.pt_mul, ← R.pt_mul, ← R.pt_mul]
  have hcl : ∀ (a b : ↥d.S), R.set ((mkReg α).closure [R.pt a, R.pt b]) =
      (closure {a, b} : Set ↥d.S) := fun a b => by
    have h1 := autOK_set_closure R [a, b]
    have h2 : {h | h ∈ [a, b]} = ({a, b} : Set ↥d.S) := by ext; simp
    rw [h2] at h1
    simpa using h1
  have hmap : ∀ (a b : ↥d.S) (s : ↥d.S), (s : G) ∈ closure ({(a : G), (b : G)} : Set G) ↔
      s ∈ (closure {a, b} : Subgroup ↥d.S) := fun a b s => by
    have h1 : (closure ({a, b} : Set ↥d.S)).map d.S.subtype =
        closure ({(a : G), (b : G)} : Set G) := by
      rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton]
      rfl
    rw [← h1]
    exact SFacts4Aux.coe_mem_map d.S _ s
  unfold unitFixOK unitFixM at hk
  simp only [Bool.or_eq_true, beq_iff_eq] at hk
  have hq' : d.q = ((c.fam 0 ^ 2 : ↥d.S) : G) := by rw [c.q_eq]; rfl
  have hfi : ∀ s : ↥d.S, (y⁻¹ * (s : G) * y = s) ↔ AutAux.conjHom d.S y hy' s = s := fun s =>
    ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  rw [hmt, hq, hm] at hk
  have hm1 : c.mu * c.lam * c.xi * c.tau =
      ((c.fam 3 * c.fam 4 * c.fam 6 * c.fam 2 : ↥d.S) : G) := rfl
  have hm2 : c.mu * c.lam * c.xi * c.tau * c.t =
      ((c.fam 3 * c.fam 4 * c.fam 6 * c.fam 2 * c.fam 0 : ↥d.S) : G) := rfl
  rcases hk with hk | hk
  · left
    have hset : {u : ↥d.S | AutAux.conjHom d.S y hy' u = u} =
        (closure {c.fam 0 ^ 2, c.fam 3 * c.fam 4 * c.fam 6 * c.fam 2} : Set ↥d.S) := by
      rw [← hfix, hk, hcl]
    intro s hs
    rw [hq', hm1]
    exact (hfi ⟨s, hs⟩).trans ((Set.ext_iff.1 hset ⟨s, hs⟩).trans
      (hmap (c.fam 0 ^ 2) (c.fam 3 * c.fam 4 * c.fam 6 * c.fam 2) ⟨s, hs⟩).symm)
  · right
    have hset : {u : ↥d.S | AutAux.conjHom d.S y hy' u = u} =
        (closure {c.fam 0 ^ 2, c.fam 3 * c.fam 4 * c.fam 6 * c.fam 2 * c.fam 0} :
          Set ↥d.S) := by
      rw [← hfix, hk, hcl]
    intro s hs
    rw [hq', hm2]
    exact (hfi ⟨s, hs⟩).trans ((Set.ext_iff.1 hset ⟨s, hs⟩).trans
      (hmap (c.fam 0 ^ 2) (c.fam 3 * c.fam 4 * c.fam 6 * c.fam 2 * c.fam 0) ⟨s, hs⟩).symm)

end CFSG.OddStandard.ChengHeld
