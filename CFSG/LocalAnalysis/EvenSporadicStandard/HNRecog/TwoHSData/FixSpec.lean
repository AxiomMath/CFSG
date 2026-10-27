module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.FixCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.FixClass
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.WClassSpec
public import CFSG.Certificates.CosetTableShort
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9Iso
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.EvenSporadicStandard.TwoHS

local notation "𝒞" => CFSG.Sporadic.SmallOddCore.conjClass

theorem fixCount_spec {T : Table} {g : Equiv.Perm (Fin 1408)} (h : Rep 1408 T g) :
    fixCount T = (Finset.univ.filter fun p : Fin 1408 => g p = p).card := by
  unfold fixCount
  have key : ∀ (i : ℕ) (hi : i < 1408), ap T i = i ↔ g ⟨i, hi⟩ = ⟨i, hi⟩ := by
    intro i hi
    have h1 := h i hi
    rw [idx_of_lt g hi] at h1
    rw [h1, Fin.ext_iff]
    rfl
  refine Finset.card_bij (fun (i : ℕ) hi =>
    (⟨i, Finset.mem_range.1 (Finset.mem_filter.1 hi).1⟩ : Fin 1408)) ?_ ?_ ?_
  · intro i hi
    have hi' := Finset.mem_filter.1 hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (key i (Finset.mem_range.1 hi'.1)).1 hi'.2
  · intro i hi j hj hij
    exact congrArg Fin.val hij
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    refine ⟨q.val, ?_, rfl⟩
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 q.2, (key q.val q.2).2 hq⟩

@[expose] def ListConj (L : Array Table) (x : Equiv.Perm (Fin 1408)) : Prop :=
  ∀ k < L.size, ∃ g ∈ P1408, Rep 1408 L[k]! (g * x * g⁻¹)

theorem mem_conjClass_of_memT {L : Array Table} {x : Equiv.Perm (Fin 1408)} (hL : ListConj L x)
    {T : Table} {y : Equiv.Perm (Fin 1408)} (hy : Rep 1408 T y) (h : memT 1408 L T = true) :
    y ∈ 𝒞 P1408 x := by
  rw [memT, Array.any_eq_true'] at h
  obtain ⟨T', hT', hTT'⟩ := h
  obtain ⟨k, hk, hkT⟩ := Array.getElem_of_mem hT'
  have hkT' : L[k]! = T' := by rw [getElem!_pos L k hk, hkT]
  obtain ⟨g, hg, hrep⟩ := hL k hk
  have hTT'' : tblEq 1408 T L[k]! = true := by rw [hkT']; exact hTT'
  have hrepT := rep_of_tblEq hrep hTT''
  exact ⟨g, hg, rep_unique hy hrepT⟩

theorem fixTreesOK_spec {pg pgInv : Array Table} {gg : ℕ → Equiv.Perm (Fin 1408)}
    (hg : ∀ l < pg.size, Rep 1408 pg[l]! (gg l) ∧ Rep 1408 pgInv[l]! (gg l)⁻¹ ∧ gg l ∈ P1408)
    {tx : Table} {x : Equiv.Perm (Fin 1408)} (cs : List (List ℕ))
    (os : List (Array Table × Array ℕ × Array ℕ))
    (hc : ∀ c ∈ cs, ∃ cg ∈ P1408, Rep 1408 (conjTab c tx) (cg * x * cg⁻¹))
    (h : fixTreesOK pg pgInv tx cs os = true) :
    ∀ o ∈ os, ListConj o.1 x ∧ ∀ k < o.1.size, ap o.1[k]! 0 = 0 := by
  induction cs generalizing os with
  | nil =>
    cases os with
    | nil => intro o ho; exact absurd ho (by simp)
    | cons _ _ => simp [fixTreesOK] at h
  | cons c cs ih =>
    cases os with
    | nil => simp [fixTreesOK] at h
    | cons o₀ os =>
      simp only [fixTreesOK, Bool.and_eq_true] at h
      obtain ⟨⟨htree, hfix⟩, hrest⟩ := h
      intro o ho
      rcases List.mem_cons.1 ho with rfl | ho
      · obtain ⟨cg, hcg, hroot⟩ := hc c List.mem_cons_self
        have hconj := conjTreeOK_spec P1408 hg hroot htree
        refine ⟨fun k hk => ?_, fun k hk => ?_⟩
        · obtain ⟨c', hc', hrep⟩ := hconj k hk
          refine ⟨c' * cg, P1408.mul_mem hc' hcg, ?_⟩
          have e : c' * (cg * x * cg⁻¹) * c'⁻¹ = c' * cg * x * (c' * cg)⁻¹ := by group
          rw [e] at hrep
          exact hrep
        · have := Array.all_eq_true'.1 hfix (o.1[k]!) (getElem!_mem_array hk)
          exact beq_iff_eq.1 this
      · exact ih os (fun c' hc' => hc c' (List.mem_cons_of_mem _ hc')) hrest o ho

theorem p0_gens_spec (hgens : gensOK = true) {p0w : List (List ℕ)}
    (hw : p0w.all wordOK = true)
    (hinv : p0w.all (fun w => invOK 1408 (tabW w) (invT 1408 (tabW w))) = true) :
    ∀ l < (p0Tabs p0w).size, Rep 1408 (p0Tabs p0w)[l]! (tablePerm 1408 (p0Tabs p0w)[l]!) ∧
      Rep 1408 (p0Invs p0w)[l]! (tablePerm 1408 (p0Tabs p0w)[l]!)⁻¹ ∧
        tablePerm 1408 (p0Tabs p0w)[l]! ∈ P1408 := by
  intro l hl
  have hmem : (p0Tabs p0w)[l]! ∈ tabsW p0w := by
    have := getElem!_mem_array hl
    simpa [p0Tabs] using this
  obtain ⟨w, hwm, hwl⟩ := List.mem_map.1 hmem
  have hr : Rep 1408 (tabW w) (elemW w) :=
    rep_elemW_of_gensOK hgens (List.all_eq_true.1 hw w hwm)
  have hr' : Rep 1408 (p0Tabs p0w)[l]! (elemW w) := by rw [← hwl]; exact hr
  have htp : tablePerm 1408 (p0Tabs p0w)[l]! = elemW w := tablePerm_eq hr'
  have hinvr : Rep 1408 (invT 1408 (tabW w)) (elemW w)⁻¹ :=
    Rep.inv_of_invOK hr (List.all_eq_true.1 hinv w hwm)
  have hInvEntry : (p0Invs p0w)[l]! = invT 1408 (tabW w) := by
    rw [p0Invs, getElem!_pos _ l (by simpa [p0Tabs] using hl), Array.getElem_map,
      ← getElem!_pos (p0Tabs p0w) l hl, hwl]
  refine ⟨by rw [htp]; exact hr', by rw [htp, hInvEntry]; exact hinvr, by
    rw [htp]; exact elemW_mem w⟩

theorem rep_conjTab (hgens : gensOK = true) {c : List ℕ} (hc : wordOK c = true)
    (hinv : invOK 1408 (tabW c) (invT 1408 (tabW c)) = true) {tx : Table}
    {x : Equiv.Perm (Fin 1408)} (hx : Rep 1408 tx x) :
    Rep 1408 (conjTab c tx) (elemW c * x * (elemW c)⁻¹) := by
  have hr := rep_elemW_of_gensOK hgens hc
  exact rep_conjT hr (Rep.inv_of_invOK hr hinv) hx

theorem fixClassOK_spec (hP : Nat.card ↥P1408 = 177408000)
    (htrans : ∀ p : Fin 1408, ∃ g ∈ P1408, g p = 0) {cap : ℕ} {p0w : List (List ℕ)}
    {d : FixData} (h : fixClassOK cap p0w d = true) :
    Nat.card ↥(P1408 ⊓ centralizer ({elemW d.rep} : Set (Equiv.Perm (Fin 1408)))) =
        d.centOrder ∧
      closure (elemW '' {w | w ∈ d.cent}) =
        P1408 ⊓ centralizer ({elemW d.rep} : Set (Equiv.Perm (Fin 1408))) ∧
      ∀ L ∈ (fixClosures cap (p0Tabs p0w) (p0Invs p0w) (tabW d.rep) d.conjs).map (·.1),
        ListConj L (elemW d.rep) := by
  simp only [fixClassOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hgens, hrep⟩, hcent⟩, hconjs⟩, hp0w⟩, hp0inv⟩, hconjinv⟩, henum⟩, hcomm⟩,
    hfix0⟩, hfixc⟩, htrees⟩, hdist⟩, hsum⟩, heq⟩ := h
  set tx : Table := tabW d.rep with htx
  set x : Equiv.Perm (Fin 1408) := elemW d.rep with hxdef
  set cls := fixClosures cap (p0Tabs p0w) (p0Invs p0w) tx d.conjs with hcls
  have hrx : Rep 1408 tx x := rep_elemW_of_gensOK hgens hrep
  have hroots : ∀ c ∈ d.conjs, ∃ cg ∈ P1408, Rep 1408 (conjTab c tx) (cg * x * cg⁻¹) := fun c hc =>
    ⟨elemW c, elemW_mem c, rep_conjTab hgens (List.all_eq_true.1 hconjs c hc)
      (List.all_eq_true.1 hconjinv c hc) hrx⟩
  have htreesSpec := fixTreesOK_spec (gg := fun l => tablePerm 1408 (p0Tabs p0w)[l]!)
    (p0_gens_spec hgens hp0w hp0inv) d.conjs cls hroots htrees
  set Ts : List Table := cls.flatMap fun o => o.1.toList with hTs
  have hTsrep : ∀ T ∈ Ts, ∃ g ∈ P1408, Rep 1408 T (g * x * g⁻¹) ∧ ap T 0 = 0 := by
    intro T hT
    obtain ⟨o, ho, hTo⟩ := List.mem_flatMap.1 hT
    obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp hTo)
    obtain ⟨hlc, hf⟩ := htreesSpec o ho
    obtain ⟨g, hg, hrp⟩ := hlc k hk
    have hf' := hf k hk
    rw [getElem!_pos o.1 k hk] at hrp hf'
    exact ⟨g, hg, hrp, hf'⟩
  have hF : List.Forall₂ (Rep 1408) Ts (Ts.map (tablePerm 1408)) := by
    rw [List.forall₂_map_right_iff]
    apply List.forall₂_same.mpr
    intro T hT
    obtain ⟨g, -, hr, -⟩ := hTsrep T hT
    rw [tablePerm_eq hr]
    exact hr
  have hnodup : (Ts.map (tablePerm 1408)).Nodup := nodup_of_hkeysDistinct hF hdist
  have hlen : Ts.length = d.m := by
    rw [← hsum, hTs, List.length_flatMap]
    simp only [Array.length_toList]
  let M : Finset (Equiv.Perm (Fin 1408)) := (Ts.map (tablePerm 1408)).toFinset
  have hMcard : M.card = d.m := by
    rw [List.toFinset_card_of_nodup hnodup, List.length_map, hlen]
  have hM : ∀ y ∈ M, y ∈ 𝒞 P1408 x ∧ y 0 = 0 := by
    intro y hy
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hy)
    obtain ⟨g, hg, hr, hf⟩ := hTsrep T hT
    rw [tablePerm_eq hr]
    refine ⟨⟨g, hg, rfl⟩, ?_⟩
    have h1 := hr 0 (by norm_num)
    rw [hf, idx_of_lt _ (by norm_num)] at h1
    exact Fin.ext h1.symm
  have hcount := TwoHSData.card_centralizer_mul_le P1408 0 htrans (elemW_mem d.rep) M hM
  rw [hMcard, hP, ← fixCount_spec hrx, hfixc] at hcount
  obtain ⟨hKcard, hKenum⟩ := enumW_spec henum
  have hKle : closure (elemW '' {w | w ∈ d.cent}) ≤
      P1408 ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 1408))) := by
    rw [closure_le]
    rintro _ ⟨w, hw, rfl⟩
    refine Subgroup.mem_inf.2 ⟨elemW_mem w, mem_centralizer_iff.2 ?_⟩
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact ((commTT_iff (rep_elemW_of_gensOK hgens (List.all_eq_true.1 hcent w hw)) hrx).1
      (List.all_eq_true.1 hcomm w hw)).symm
  have hKC : d.centOrder ≤ Nat.card ↥(P1408 ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 1408)))) := by
    rw [← hKcard]
    exact Subgroup.card_le_of_le hKle
  have hfixpos : 0 < d.fix := by
    rw [← hfixc, fixCount_spec hrx]
    apply Finset.card_pos.2
    refine ⟨0, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
    have h1 := hrx 0 (by norm_num)
    rw [hfix0, idx_of_lt _ (by norm_num)] at h1
    exact Fin.ext h1.symm
  have hmpos : 0 < d.m := by
    rcases Nat.eq_zero_or_pos d.m with h0 | h0
    · rw [h0, mul_zero] at heq
      omega
    · exact h0
  have hle : Nat.card ↥(P1408 ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 1408)))) ≤ d.centOrder := by
    have h1 : Nat.card ↥(P1408 ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 1408)))) *
        (1408 * d.m) ≤ d.centOrder * (1408 * d.m) := by
      calc _ ≤ 177408000 * d.fix := hcount
        _ = d.centOrder * 1408 * d.m := heq.symm
        _ = d.centOrder * (1408 * d.m) := by ring
    exact Nat.le_of_mul_le_mul_right h1 (Nat.mul_pos (by norm_num) hmpos)
  have hcard : Nat.card ↥(P1408 ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 1408)))) =
      d.centOrder := le_antisymm hle hKC
  refine ⟨hcard, Subgroup.eq_of_le_of_card_ge hKle (by rw [hcard, hKcard]), ?_⟩
  intro L hL
  obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hL
  exact (htreesSpec o ho).1

end CFSG.EvenSporadicStandard.HNRecog
