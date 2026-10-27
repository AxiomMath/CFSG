module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.PermKit
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.SixData

public section

namespace CFSG.SectionRank.QTK.Insp443.PermKit

open Equiv CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Native
  CFSG.SectionRank.QTK.Insp443.PermKit.Native

variable {n : ℕ}

theorem countProducts_mono {f f' : Table → Bool} (h : ∀ T, f T = true → f' T = true) :
    ∀ (Tss : List (List Table)) (g : Table), countProducts n f Tss g ≤ countProducts n f' Tss g
  | [], g => by
    simp only [countProducts]
    by_cases hf : f g = true
    · rw [if_pos hf, if_pos (h g hf)]
    · rw [if_neg hf]
      exact Nat.zero_le _
  | T :: Ts, g => by
    simp only [countProducts]
    rw [foldl_add_eq_sum, foldl_add_eq_sum, zero_add, zero_add]
    exact List.sum_le_sum fun t _ => countProducts_mono h Ts (compT n g t)

theorem forall_of_tests_count (hn : n < 2 ^ 32) (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    {tests : List (Table → Bool)}
    (h : countProducts n (anyTest tests) (levelTables Q) (idT n) = 0)
    {t : Table → Bool} (ht : t ∈ tests) {P : Perm (Fin n) → Prop} [DecidablePred P]
    (htP : ∀ T g, Rep n T g → (t T = true ↔ P g)) : ∀ x : Q.originalSubgroup, ¬ P x := by
  have h0 : countProducts n t (levelTables Q) (idT n) = 0 := by
    have := countProducts_mono (n := n) (f := t) (f' := anyTest tests)
      (fun T hT => List.any_eq_true.mpr ⟨t, ht, hT⟩) (levelTables Q) (idT n)
    omega
  exact forall_of_countProducts_eq_zero hn Q hQ htP h0

theorem inSp_spanTabs {bs : List Table} {T : Table} :
    inSp n (spanTabs n bs) T = inSpanT n bs T := rfl

theorem conjIn_spanTabs {bs cs : List Table} {T : Table} :
    conjIn n bs (spanTabs n cs) T = conjSpanIn n bs cs T := rfl

theorem centTest_iff (hn : n < 2 ^ 32) {k l : ℕ} {u : Fin k → Perm (Fin n)}
    {w : Fin l → Perm (Fin n)} (hw : EBasis w) {us ws : List Table}
    (hus : List.Forall₂ (Rep n) us (List.ofFn u)) (hws : List.Forall₂ (Rep n) ws (List.ofFn w))
    {T : Table} {g : Perm (Fin n)} (hT : Rep n T g) :
    centTest n us ws T = true ↔ (∀ i, g * u i = u i * g) ∧ g ∉ eSub hw := by
  show (commAllT n us T && !(inSp n (spanTabs n ws) T)) = true ↔ _
  rw [Bool.and_eq_true, Bool.not_eq_true', inSp_spanTabs, commAllT_iff hus hT]
  refine and_congr Iff.rfl ?_
  rw [← Bool.not_eq_true, inSpanT_iff_mem hn hw hws hT]

@[expose] noncomputable def dB (n : ℕ) (ds : List (List Table)) (r : ℕ) :
    Fin (ds.getD r []).length → Perm (Fin n) :=
  permB n (ds.getD r [])

@[expose] def ConjInto {k l : ℕ} (g : Perm (Fin n)) (v : Fin k → Perm (Fin n))
    (w : Fin l → Perm (Fin n)) : Prop :=
  ∀ i, ∃ c, g * v i * g⁻¹ = eElt w c

theorem sixTest_iff (hn : n < 2 ^ 32) {l : ℕ} {w : Fin l → Perm (Fin n)} (hw : EBasis w)
    {ws : List Table} (hws : List.Forall₂ (Rep n) ws (List.ofFn w)) {ds : List (List Table)}
    (hds : ds.length = 6) (hdt : ∀ r < 6, tabsOK n (ds.getD r []) = true)
    {T : Table} {g : Perm (Fin n)} (hT : Rep n T g) :
    sixTest n ws ds T = true ↔ g ∈ eNorm hw ∧
      (¬ (∀ r < 6, ∃ s < 6, ConjInto g (dB n ds r) (dB n ds s)) ∨
        ((∀ r < 6, ConjInto g (dB n ds r) (dB n ds r)) ∧ g ∉ eSub hw)) := by
  have hget : ∀ s < 6, (ds.map (spanTabs n)).getD s [] = spanTabs n (ds.getD s []) := by
    intro s hs
    have hs' : s < ds.length := by rw [hds]; exact hs
    rw [List.getD_eq_getElem _ _ (by simpa using hs'), List.getD_eq_getElem _ _ hs',
      List.getElem_map]
  have hcj : ∀ r < 6, ∀ s < 6, conjIn n (ds.getD r []) ((ds.map (spanTabs n)).getD s []) T =
      true ↔ ConjInto g (dB n ds r) (dB n ds s) := by
    intro r hr s hs
    rw [hget s hs, conjIn_spanTabs]
    exact conjSpanIn_iff hn (forall₂_permB (hdt r hr)) (forall₂_permB (hdt s hs)) hT
  show (conjIn n ws (spanTabs n ws) T && (!((List.range 6).all fun r => (List.range 6).any fun s =>
      conjIn n (ds.getD r []) ((ds.map (spanTabs n)).getD s []) T) ||
      (((List.range 6).all fun r => conjIn n (ds.getD r []) ((ds.map (spanTabs n)).getD r []) T) &&
        !(inSp n (spanTabs n ws) T)))) = true ↔ _
  have hnorm : conjIn n ws (spanTabs n ws) T = normAll n ws T := rfl
  rw [Bool.and_eq_true, hnorm, normAll_iff hn hw hws hT]
  refine and_congr Iff.rfl ?_
  rw [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, Bool.not_eq_true', inSp_spanTabs,
    ← Bool.not_eq_true (inSpanT n ws T), inSpanT_iff_mem hn hw hws hT]
  refine or_congr ?_ (and_congr ?_ Iff.rfl)
  · rw [← Bool.not_eq_true, List.all_eq_true]
    refine not_congr ⟨fun h r hr => ?_, fun h r hr => ?_⟩
    · obtain ⟨s, hs, hsT⟩ := List.any_eq_true.mp (h r (List.mem_range.mpr hr))
      exact ⟨s, List.mem_range.mp hs, (hcj r hr s (List.mem_range.mp hs)).mp hsT⟩
    · obtain ⟨s, hs, hsT⟩ := h r (List.mem_range.mp hr)
      exact List.any_eq_true.mpr ⟨s, List.mem_range.mpr hs,
        (hcj r (List.mem_range.mp hr) s hs).mpr hsT⟩
  · rw [List.all_eq_true]
    exact ⟨fun h r hr => (hcj r hr r hr).mp (h r (List.mem_range.mpr hr)),
      fun h r hr => (hcj r (List.mem_range.mp hr) r (List.mem_range.mp hr)).mpr
        (h r (List.mem_range.mp hr))⟩

theorem mul_self_of_invoOK {T : Table} {g : Perm (Fin n)} (hT : Rep n T g)
    (h : invoOK n T = true) : g * g = 1 := by
  have h1 := idx_sq_of_invoOK hT h
  rw [← sq]
  refine Equiv.ext fun i => ?_
  have h2 := h1 i i.2
  rw [idx_of_lt _ i.2] at h2
  exact Fin.ext h2

theorem eSub_le_of_inSpan (hn : n < 2 ^ 32) {k l : ℕ} {v : Fin k → Perm (Fin n)}
    {w : Fin l → Perm (Fin n)} (hv : EBasis v) (hw : EBasis w) {bs ws : List Table}
    (hbs : List.Forall₂ (Rep n) bs (List.ofFn v)) (hws : List.Forall₂ (Rep n) ws (List.ofFn w))
    (h : ∀ b ∈ bs, inSpanT n ws b = true) : eSub hv ≤ eSub hw := by
  rw [eSub_eq_closure hv, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  obtain ⟨b, hb, hbi⟩ := exists_tab_of_mem hbs (List.mem_ofFn.mpr ⟨i, rfl⟩)
  exact (inSpanT_iff_mem hn hw hws hbi).mp (h b hb)

theorem map_conj_eq_of_conjInto {k l : ℕ} {v : Fin k → Perm (Fin n)}
    {w : Fin l → Perm (Fin n)} (hv : EBasis v) (hw : EBasis w) (hkl : k = l) {g : Perm (Fin n)}
    (h : ConjInto g v w) : (eSub hv).map (MulAut.conj g).toMonoidHom = eSub hw := by
  have hle : (eSub hv).map (MulAut.conj g).toMonoidHom ≤ eSub hw := by
    rw [eSub_eq_closure hv, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    obtain ⟨c, hc⟩ := h i
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hc]
    exact eElt_mem hw c
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, card_eSub, card_eSub, hkl]

theorem ebasis_permB (hn : n < 2 ^ 32) {bs : List Table} (h1 : tabsOK n bs = true)
    (h2 : ebasisOK n bs = true) : EBasis (permB n bs) :=
  ebasis_of_ebasisOK hn (forall₂_permB h1) h2

theorem getD_mem {ds : List (List Table)} {r : ℕ} (hr : r < ds.length) : ds.getD r [] ∈ ds := by
  rw [List.getD_eq_getElem _ _ hr]
  exact List.getElem_mem hr

theorem swap01_val (r : Fin 6) : ((Equiv.swap (0 : Fin 6) 1 r : Fin 6) : ℕ) = swap01 r := by
  fin_cases r <;> rfl

theorem finRotate_val (r : Fin 6) : ((finRotate 6 r : Fin 6) : ℕ) = ((r : ℕ) + 1) % 6 := by
  fin_cases r <;> rfl

theorem exists_sixData (hn : n < 2 ^ 32) {H : Subgroup (Perm (Fin n))} {ws : List Table}
    {ds : List (List Table)} {hs : List Table} {aT gT hT : Table}
    (hc : sixCheckE n ws ds hs aT gT hT = true) (hwb : EBasis (permB n ws))
    (hwH : ∀ i, permB n ws i ∈ H)
    (hnov : ∀ g ∈ H, ¬ (g ∈ eNorm hwb ∧
      (¬ (∀ r < 6, ∃ s < 6, ConjInto g (dB n ds r) (dB n ds s)) ∨
        ((∀ r < 6, ConjInto g (dB n ds r) (dB n ds r)) ∧ g ∉ eSub hwb))))
    (hgH : tabPerm n gT ∈ H) (hhH : tabPerm n hT ∈ H) :
    ∃ (hdb : ∀ r : Fin 6, EBasis (dB n ds r)) (hdH : ∀ (r : Fin 6) i, dB n ds r i ∈ H),
      SixData (eSub (liftB_basis hwH hwb)) fun r => eSub (liftB_basis (hdH r) (hdb r)) := by
  simp only [sixCheckE, Bool.and_eq_true, beq_iff_eq, and_assoc, Bool.not_eq_true'] at hc
  obtain ⟨hwt, -, hwl, hdl, hdall, hdist, -, -, -, -, htabs, -, -, -, -, hgW, hhW, hgD, hhD⟩ := hc
  have hws := forall₂_permB hwt
  rw [List.all_eq_true] at hdall
  have hdt : ∀ r : Fin 6, tabsOK n (ds.getD r []) = true := fun r =>
    (by simpa [and_assoc] using hdall _ (getD_mem (by rw [hdl]; exact r.2)) :
      tabsOK n (ds.getD r []) = true ∧ _).1
  have hdinfo : ∀ r : Fin 6, ebasisOK n (ds.getD r []) = true ∧ (ds.getD r []).length = 4 ∧
      ∀ b ∈ ds.getD r [], inSp n (spanTabs n ws) b = true := by
    intro r
    have := hdall _ (getD_mem (by rw [hdl]; exact r.2))
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at this
    exact ⟨this.1.1.2, this.1.2, this.2⟩
  have hdb : ∀ r : Fin 6, EBasis (dB n ds r) := fun r => ebasis_permB hn (hdt r) (hdinfo r).1
  have hds : ∀ r : Fin 6, List.Forall₂ (Rep n) (ds.getD r []) (List.ofFn (dB n ds r)) :=
    fun r => forall₂_permB (hdt r)
  have hdle : ∀ r : Fin 6, eSub (hdb r) ≤ eSub hwb := fun r =>
    eSub_le_of_inSpan hn (hdb r) hwb (hds r) hws fun b hb => (hdinfo r).2.2 b hb
  have hwH' : eSub hwb ≤ H := by
    rw [← eSub_liftB_map hwH hwb]
    exact Subgroup.map_subtype_le _
  have hdH : ∀ (r : Fin 6) i, dB n ds r i ∈ H := fun r i =>
    hwH' (hdle r (mem_eSub (hdb r) i))
  refine ⟨hdb, hdH, ?_⟩
  set W' := eSub (liftB_basis hwH hwb) with hW'
  set D' : Fin 6 → Subgroup H := fun r => eSub (liftB_basis (hdH r) (hdb r)) with hD'
  have hmapW : W'.map H.subtype = eSub hwb := eSub_liftB_map hwH hwb
  have hmapD : ∀ r, (D' r).map H.subtype = eSub (hdb r) := fun r => eSub_liftB_map (hdH r) (hdb r)
  have hconjmap : ∀ (g : H) (K : Subgroup H),
      (K.map (MulAut.conj g).toMonoidHom).map H.subtype =
        (K.map H.subtype).map (MulAut.conj (g : Perm (Fin n))).toMonoidHom := by
    intro g K
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hinjmap : ∀ K K' : Subgroup H, K.map H.subtype = K'.map H.subtype → K = K' :=
    fun K K' h => Subgroup.map_injective H.subtype_injective h
  have hconjD : ∀ (g : H) (r s : Fin 6), ConjInto (g : Perm (Fin n)) (dB n ds r) (dB n ds s) →
      (D' r).map (MulAut.conj g).toMonoidHom = D' s := by
    intro g r s h
    apply hinjmap
    rw [hconjmap, hmapD, hmapD]
    exact map_conj_eq_of_conjInto (hdb r) (hdb s)
      (by rw [(hdinfo r).2.1, (hdinfo s).2.1]) h
  have hconjD' : ∀ (g : H) (r s : Fin 6), (D' r).map (MulAut.conj g).toMonoidHom = D' s →
      ConjInto (g : Perm (Fin n)) (dB n ds r) (dB n ds s) := by
    intro g r s h i
    have h1 : (g : Perm (Fin n)) * dB n ds r i * (g : Perm (Fin n))⁻¹ ∈ eSub (hdb s) := by
      rw [← hmapD, ← h, hconjmap, hmapD]
      exact ⟨_, mem_eSub (hdb r) i, rfl⟩
    exact (mem_eSub_iff (hdb s) _).mp h1 |>.imp fun c hc => hc.symm
  have hnormW : ∀ g : H, g ∈ Subgroup.normalizer (W' : Set H) →
      (g : Perm (Fin n)) ∈ eNorm hwb := fun g hg =>
    (mem_normalizer_liftB_iff hwH hwb g).mp hg
  refine ⟨fun r s hrs => ?_, fun r => ?_, fun g hg r => ?_, fun g hg hfix => ?_,
    fun a ha b hb => ?_, ?_, ?_⟩
  ·
    by_contra hne
    have hrs' : eSub (hdb r) = eSub (hdb s) := by rw [← hmapD, ← hmapD, hrs]
    have h1 := List.all_eq_true.mp (List.all_eq_true.mp hdist r (List.mem_range.mpr r.2)) s
      (List.mem_range.mpr s.2)
    rw [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at h1
    rcases h1 with h1 | h1
    · exact hne (Fin.ext h1)
    · have h2 : spanEq n (ds.getD r []) (ds.getD s []) = true := by
        unfold spanEq
        rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
        refine ⟨fun b hb => ?_, fun b hb => ?_⟩
        · obtain ⟨x, hx, hbx⟩ := exists_rep_of_mem (hds r) hb
          obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
          rw [inSpanT_iff_mem hn (hdb s) (hds s) hbx, ← hrs']
          exact mem_eSub _ i
        · obtain ⟨x, hx, hbx⟩ := exists_rep_of_mem (hds s) hb
          obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
          rw [inSpanT_iff_mem hn (hdb r) (hds r) hbx, hrs']
          exact mem_eSub _ i
      rw [h1] at h2
      exact absurd h2 (by decide)
  ·
    intro x hx
    have : (x : Perm (Fin n)) ∈ eSub hwb := hdle r ((mem_eSub_liftB_iff (hdH r) (hdb r) x).mp hx)
    exact (mem_eSub_liftB_iff hwH hwb x).mpr this
  ·
    have hng := hnormW g hg
    have hall : ∀ r < 6, ∃ s < 6, ConjInto (g : Perm (Fin n)) (dB n ds r) (dB n ds s) := by
      by_contra hc'
      exact hnov g g.2 ⟨hng, Or.inl hc'⟩
    obtain ⟨s, hs, hrs⟩ := hall r r.2
    exact ⟨⟨s, hs⟩, hconjD g r ⟨s, hs⟩ hrs⟩
  ·
    have hng := hnormW g hg
    have hall : ∀ r < 6, ConjInto (g : Perm (Fin n)) (dB n ds r) (dB n ds r) := fun r hr =>
      hconjD' g ⟨r, hr⟩ ⟨r, hr⟩ (hfix ⟨r, hr⟩)
    have hmem : (g : Perm (Fin n)) ∈ eSub hwb := by
      by_contra hc'
      exact hnov g g.2 ⟨hng, Or.inr ⟨hall, hc'⟩⟩
    exact (mem_eSub_liftB_iff hwH hwb g).mpr hmem
  · exact eSub_comm _ a b ha hb
  ·
    simp only [tabsOK, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at htabs
    have hgT : Rep n gT (tabPerm n gT) := rep_tabPerm htabs.2.1
    let g : H := ⟨tabPerm n gT, hgH⟩
    have hgN : g ∈ Subgroup.normalizer (W' : Set H) := by
      rw [mem_normalizer_liftB_iff]
      exact (normAll_iff hn hwb hws hgT).mp hgW
    refine ⟨g, hgN, fun r => ?_⟩
    have h1 := List.all_eq_true.mp hgD r (List.mem_range.mpr r.2)
    have hsw : swap01 r < 6 := by rw [← swap01_val]; exact (Equiv.swap (0 : Fin 6) 1 r).2
    have hget : (ds.map (spanTabs n)).getD (swap01 r) [] = spanTabs n (ds.getD (swap01 r) []) := by
      have hs' : swap01 r < ds.length := by rw [hdl]; exact hsw
      rw [List.getD_eq_getElem _ _ (by simpa using hs'), List.getD_eq_getElem _ _ hs',
        List.getElem_map]
    rw [hget, conjIn_spanTabs] at h1
    have h2 := (conjSpanIn_iff hn (hds r) (forall₂_permB (hdt ⟨swap01 r, hsw⟩)) hgT).mp h1
    apply hconjD g r
    rw [swap01_val]
    exact h2
  ·
    simp only [tabsOK, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at htabs
    have hhT' : Rep n hT (tabPerm n hT) := rep_tabPerm htabs.2.2
    let g : H := ⟨tabPerm n hT, hhH⟩
    have hgN : g ∈ Subgroup.normalizer (W' : Set H) := by
      rw [mem_normalizer_liftB_iff]
      exact (normAll_iff hn hwb hws hhT').mp hhW
    refine ⟨g, hgN, fun r => ?_⟩
    have h1 := List.all_eq_true.mp hhD r (List.mem_range.mpr r.2)
    have hsw : ((r : ℕ) + 1) % 6 < 6 := Nat.mod_lt _ (by norm_num)
    have hget : (ds.map (spanTabs n)).getD (((r : ℕ) + 1) % 6) [] =
        spanTabs n (ds.getD (((r : ℕ) + 1) % 6) []) := by
      have hs' : ((r : ℕ) + 1) % 6 < ds.length := by rw [hdl]; exact hsw
      rw [List.getD_eq_getElem _ _ (by simpa using hs'), List.getD_eq_getElem _ _ hs',
        List.getElem_map]
    rw [hget, conjIn_spanTabs] at h1
    have h2 := (conjSpanIn_iff hn (hds r) (forall₂_permB (hdt ⟨_, hsw⟩)) hhT').mp h1
    apply hconjD g r
    rw [finRotate_val]
    exact h2

end CFSG.SectionRank.QTK.Insp443.PermKit

end
