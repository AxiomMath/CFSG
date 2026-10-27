module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.Sp6Five
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.FanoMap
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.E8Concl
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.FanoConcl

public section

namespace CFSG.SectionRank.QTK.Insp443.Sp6

open Equiv CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Schreier.Co3 CFSG.Quasithin.KGC31
  CFSG.Quasithin.KGC31.Native CFSG.SectionRank.QTK.Insp443.PermKit
  CFSG.SectionRank.QTK.Insp443.PermKit.Native CFSG.Quasithin.H13 CFSG.Quasithin.H13.Fano
  CFSG.Quasithin
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped Matrix

theorem invOK_of_tabOK {n : ℕ} {T R : Table} (h : tabOK n T R = true) : invOK n T R = true := by
  unfold tabOK at h
  unfold invOK
  rw [allIn_eq_true] at h ⊢
  intro i h1 h2
  have := h i h1 h2
  rw [Bool.and_eq_true] at this
  exact this.2

theorem mem_zpowers_of_prime {G : Type*} [Group G] {x y : G} {p : ℕ} [hp : Fact p.Prime]
    (hx : orderOf x = p) (hyx : y ∈ Subgroup.zpowers x) (hy1 : y ≠ 1) :
    x ∈ Subgroup.zpowers y := by
  have hle : Subgroup.zpowers y ≤ Subgroup.zpowers x := Subgroup.zpowers_le.mpr hyx
  have hdvd : orderOf y ∣ p := hx ▸ orderOf_dvd_of_mem_zpowers hyx
  have hy : orderOf y = p := by
    rcases (Nat.dvd_prime hp.out).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hy1
    · exact h1
  have hfin : Finite (Subgroup.zpowers x) := by
    have hpos : 0 < orderOf x := by rw [hx]; exact hp.out.pos
    exact Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers]; omega)
  have heq : Subgroup.zpowers y = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hx, hy])
  rw [heq]
  exact Subgroup.mem_zpowers x

theorem coe_statedSLEquiv (s : ↥(StatedSL 3 (ZMod 2))) :
    ((CFSG.RankThree.PartTwo.Sec4.statedSLEquiv 3 (ZMod 2) s :
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
        ((s : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  conv_rhs => rw [← (CFSG.RankThree.PartTwo.Sec4.statedSLEquiv 3 (ZMod 2)).symm_apply_apply s]
  rw [CFSG.RankThree.PartTwo.Sec4.coe_statedSLEquiv_symm]


theorem p7_facts (h : chkP7 () = true) :
    subOK 36 (cands7.getD 0 []) (cands7.getD 2 []) = true ∧
    subOK 36 (cands7.getD 1 []) (cands7.getD 4 []) = true ∧
    subOK 36 (cands7.getD 2 []) (cands7.getD 2 []) = true ∧
    subOK 36 (cands7.getD 3 []) (cands7.getD 2 []) = true ∧
    subOK 36 (cands7.getD 4 []) (cands7.getD 4 []) = true ∧
    subOK 36 (cands7.getD 5 []) (cands7.getD 4 []) = true ∧
    irrOK 36 7 x7T (invT 36 x7T) (cands7.getD 0 []) (cands7.getD 2 []) = true ∧
    irrOK 36 7 x7T (invT 36 x7T) (cands7.getD 1 []) (cands7.getD 4 []) = true ∧
    irrOK 36 7 x7T (invT 36 x7T) (cands7.getD 3 []) (cands7.getD 2 []) = true ∧
    irrOK 36 7 x7T (invT 36 x7T) (cands7.getD 5 []) (cands7.getD 4 []) = true ∧
    countProducts 36 (anyTest (tests7 (spanTabs 36 (cands7.getD 2 []))
      (spanTabs 36 (cands7.getD 4 [])) (spanTabs 36 (cands7.getD 0 []))
      (spanTabs 36 (cands7.getD 1 [])))) (levelTables co3Sp36Chain) (idT 36) = 0 := by
  rw [levelTables_eq_lv]
  simpa only [chkP7, Bool.and_eq_true, beq_iff_eq, and_assoc] using h

theorem rows2_even : ∀ i : Fin 6, ∑ p : FanoPoint, rowBit rows2 i (pmask p) = 0 := by decide

theorem rows4_even : ∀ i : Fin 6, ∑ p : FanoPoint, rowBit rows4 i (pmask p) = 0 := by decide

theorem rows2_ind : ∀ m < 64, (∀ q, 1 ≤ q → q < 8 → bsum rows2 m q = false) → m = 0 := by
  have h : ∀ m < 64, (∀ q < 8, 1 ≤ q → bsum rows2 m q = false) → m = 0 := by decide
  exact fun m hm hq => h m hm fun q h8 h1 => hq q h1 h8

theorem rows4_ind : ∀ m < 64, (∀ q, 1 ≤ q → q < 8 → bsum rows4 m q = false) → m = 0 := by
  have h : ∀ m < 64, (∀ q < 8, 1 ≤ q → bsum rows4 m q = false) → m = 0 := by decide
  exact fun m hm hq => h m hm fun q h8 h1 => hq q h1 h8

theorem permBk_mem {bs : List Table} (ht : tabsOK 36 bs = true) (hs : bs.all siftOK = true)
    {k : ℕ} (hk : bs.length = k) (i : Fin k) : permBk 36 k bs i ∈ co3X36 := by
  subst hk
  unfold tabsOK at ht
  rw [List.all_eq_true] at ht hs
  unfold permBk
  rw [List.getD_eq_getElem _ _ i.2]
  exact mem_of_siftOK (rep_tabPerm (ht _ (List.getElem_mem i.2))) (hs _ (List.getElem_mem i.2))

theorem cent_of_test' {tests : List (Table → Bool)}
    (hcnt : countProducts 36 (anyTest tests) (levelTables co3Sp36Chain) (idT 36) = 0)
    {k l : ℕ} {u : Fin k → Perm (Fin 36)} {w : Fin l → Perm (Fin 36)} (hw : EBasis w)
    {us ws : List Table} (hus : List.Forall₂ (Rep 36) us (List.ofFn u))
    (hws : List.Forall₂ (Rep 36) ws (List.ofFn w)) (ht : centTestS 36 us (spanTabs 36 ws) ∈ tests) :
    ∀ x : co3X36, ¬ ((∀ i, (x : Perm (Fin 36)) * u i = u i * x) ∧
      (x : Perm (Fin 36)) ∉ eSub hw) :=
  no_viol (P := fun g => (∀ i, g * u i = u i * g) ∧ g ∉ eSub hw) hcnt ht
    fun _ _ hT => centTest_iff hn36 hw hus hws hT

theorem fano_of_test {tests : List (Table → Bool)}
    (hcnt : countProducts 36 (anyTest tests) (levelTables co3Sp36Chain) (idT 36) = 0)
    {ws as : List Table} {rows : List ℕ} {k l : ℕ} {w : Fin k → Perm (Fin 36)}
    {a : Fin l → Perm (Fin 36)} (hw : EBasis w) (ha : EBasis a)
    (hws : List.Forall₂ (Rep 36) ws (List.ofFn w)) (has : List.Forall₂ (Rep 36) as (List.ofFn a))
    (ht : fanoTestS 36 ws (spanTabs 36 ws) as (spanTabs 36 as) rows ∈ tests) (x : co3X36)
    (hxW : (x : Perm (Fin 36)) ∈ eNorm hw) :
    (x : Perm (Fin 36)) ∈ eNorm ha ∧ ∃ T, Rep 36 T (x : Perm (Fin 36)) ∧
      fanoEqOK 36 ws (spanTabs 36 ws) as (spanTabs 36 as) rows T = true := by
  by_contra hne
  refine forall_of_tests_count' hn36 co3Sp36Chain valid hcnt ht
    (P := fun g => g ∈ eNorm hw ∧ ¬ (g ∈ eNorm ha ∧ ∃ T, Rep 36 T g ∧
      fanoEqOK 36 ws (spanTabs 36 ws) as (spanTabs 36 as) rows T = true)) ?_ x ⟨hxW, hne⟩
  rintro T g hT ⟨hgW, hgn⟩
  have h1 : conjIn 36 ws (spanTabs 36 ws) T = true := by
    have hnorm : conjIn 36 ws (spanTabs 36 ws) T = normAll 36 ws T := rfl
    rw [hnorm]
    exact (normAll_iff hn36 hw hws hT).mpr hgW
  show (conjIn 36 ws (spanTabs 36 ws) T && (!(conjIn 36 as (spanTabs 36 as) T) ||
    !(fanoEqOK 36 ws (spanTabs 36 ws) as (spanTabs 36 as) rows T))) = true
  rw [h1, Bool.true_and]
  cases hA : conjIn 36 as (spanTabs 36 as) T
  · rfl
  · cases hF : fanoEqOK 36 ws (spanTabs 36 ws) as (spanTabs 36 as) rows T
    · rfl
    · exfalso
      have hnorm : conjIn 36 as (spanTabs 36 as) T = normAll 36 as T := rfl
      exact hgn ⟨(normAll_iff hn36 ha has hT).mp (hnorm ▸ hA), T, hT, hF⟩

theorem conclK_fano {L V MK : Subgroup co3X36} (h : KConfig co3X36 L V MK)
    {ws as : List Table} {rows : List ℕ} (hwl : ws.length = 6) (hal : as.length = 3)
    (hsubW : subOK 36 ws ws = true) (hsubA : subOK 36 as ws = true)
    (hwS : ws.all siftOK = true) (haS : as.all siftOK = true)
    {tests : List (Table → Bool)}
    (hcnt : countProducts 36 (anyTest tests) (levelTables co3Sp36Chain) (idT 36) = 0)
    (hmCA : centTestS 36 as (spanTabs 36 ws) ∈ tests)
    (hmF : fanoTestS 36 ws (spanTabs 36 ws) as (spanTabs 36 as) rows ∈ tests)
    (hev : ∀ i : Fin 6, ∑ p : FanoPoint, rowBit rows i (pmask p) = 0) (hrl : rows.length = 6)
    (hind : ∀ m < 64, (∀ q, 1 ≤ q → q < 8 → bsum rows m q = false) → m = 0)
    (hwb : EBasis (permBk 36 6 ws)) (hwH : ∀ i, permBk 36 6 ws i ∈ co3X36)
    (hV : V = eSub (liftB_basis hwH hwb)) : ConclK co3X36 L V MK := by
  subst hV
  simp only [subOK, Bool.and_eq_true, List.all_eq_true] at hsubW hsubA
  obtain ⟨⟨⟨⟨⟨hwt, -⟩, -⟩, -⟩, -⟩, -⟩ := hsubW
  obtain ⟨⟨⟨⟨⟨hat, hae⟩, -⟩, -⟩, haW⟩, -⟩ := hsubA
  have hws := forall₂_permBk hwt hwl
  have has := forall₂_permBk hat hal
  have hab : EBasis (permBk 36 3 as) := ebasis_permBk hn36 hat hae hal
  have haH : ∀ i, permBk 36 3 as i ∈ co3X36 := permBk_mem hat haS hal
  have hAW0 : eSub hab ≤ eSub hwb := eSub_le_of_inSpan hn36 hab hwb has hws fun b hb => haW b hb
  have hAW : eSub (liftB_basis haH hab) ≤ eSub (liftB_basis hwH hwb) := fun z hz =>
    (mem_eSub_liftB_iff hwH hwb z).mpr (hAW0 ((mem_eSub_liftB_iff haH hab z).mp hz))
  have hCAt := cent_of_test' hcnt hwb has hws hmCA
  have hCA : Subgroup.centralizer (eSub (liftB_basis haH hab) : Set co3X36) ≤
      eSub (liftB_basis hwH hwb) := fun z hz => by
    rw [mem_centralizer_liftB_iff haH hab] at hz
    by_contra hzW
    exact hCAt z ⟨hz, fun hm => hzW ((mem_eSub_liftB_iff hwH hwb z).mpr hm)⟩
  have hW2 : IsPGroup 2 ↥(eSub (liftB_basis hwH hwb)) :=
    IsPGroup.of_card (n := 6) (by rw [card_eSub])
  have hC2 : IsPGroup 2 ↥(Subgroup.centralizer (eSub (liftB_basis haH hab) : Set co3X36)) :=
    hW2.to_le hCA
  have hLF : ∀ l ∈ L, l ∈ eNorm (liftB_basis haH hab) ∧ ∃ T, Rep 36 T (l : Perm (Fin 36)) ∧
      fanoEqOK 36 ws (spanTabs 36 ws) as (spanTabs 36 as) rows T = true := by
    intro l hl
    have hlW : (l : Perm (Fin 36)) ∈ eNorm hwb :=
      (mem_normalizer_liftB_iff hwH hwb l).mp (h.le_normalizer hl)
    obtain ⟨hlA, T, hT, hok⟩ := fano_of_test hcnt hwb hab hws has hmF l hlW
    exact ⟨(mem_normalizer_liftB_iff haH hab l).mpr hlA, T, hT, hok⟩
  have hLA : L ≤ eNorm (liftB_basis haH hab) := fun l hl => (hLF l hl).1
  let α₀ := E16.eNHom (liftB_basis haH hab) hLA
  have hθ : ∀ l : ↥L, α₀ l = 1 ↔
      (l : co3X36) ∈ Subgroup.centralizer (eSub (liftB_basis haH hab) : Set co3X36) :=
    fun l => E16.eNHom_eq_one_iff _ hLA l
  haveI : Group.IsPerfect ↥L := ⟨commutator_eq_top_of_perfect h.perfect⟩
  haveI : IsSimpleGroup ↥(StatedSL 3 (ZMod 2)) := E8.isSimpleGroup_statedSL3
  have hsurj₀ : Function.Surjective α₀ := by
    rw [← MonoidHom.range_eq_top]
    rcases CFSG.Quasithin.J4Fam.eq_bot_or_top_of_isPerfect
        (fun H hH => CFSG.Quasithin.J4Fam.solvable_of_ne_top_card168 E8.card_statedSL3 hH)
        (Group.IsPerfect.range α₀) with hb | ht
    · exfalso
      have hLC : L ≤ Subgroup.centralizer (eSub (liftB_basis haH hab) : Set co3X36) :=
        fun l hl => (hθ ⟨l, hl⟩).mp (by
          have : α₀ ⟨l, hl⟩ ∈ α₀.range := ⟨_, rfl⟩
          rwa [hb, Subgroup.mem_bot] at this)
      have hL1 : L = ⊥ := eq_bot_of_perfect_of_isPGroup h.perfect (hC2.to_le hLC)
      apply h.ne_bot
      rw [eq_bot_iff]
      exact h.le_pCoreOf.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hL1.le)
    · exact ht
  let α : ↥L →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    invTr.comp ((CFSG.RankThree.PartTwo.Sec4.statedSLEquiv 3 (ZMod 2)).toMonoidHom.comp α₀)
  have hα1 : ∀ l, α l = 1 ↔ α₀ l = 1 := fun l => by
    change invTr (CFSG.RankThree.PartTwo.Sec4.statedSLEquiv 3 (ZMod 2) (α₀ l)) = 1 ↔ _
    rw [← invTr.map_one, invTr_injective.eq_iff, ← map_one (CFSG.RankThree.PartTwo.Sec4.statedSLEquiv 3 (ZMod 2)),
      (CFSG.RankThree.PartTwo.Sec4.statedSLEquiv 3 (ZMod 2)).injective.eq_iff]
  have hsurj : Function.Surjective α :=
    invTr_surjective.comp ((CFSG.RankThree.PartTwo.Sec4.statedSLEquiv 3 (ZMod 2)).surjective.comp
      hsurj₀)
  have hker : CFSG.pCore 2 ↥L = α.ker := by
    rw [← Hex.pCoreOf_subgroupOf' L]
    ext l
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, hα1, hθ]
    constructor
    · intro hl
      exact Subgroup.centralizer_le hAW (h.pCoreOf_le hl)
    · intro hl
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        (inf_le_left : L ⊓ Subgroup.centralizer (eSub (liftB_basis haH hab) : Set co3X36) ≤ L)
        (fun m hm => mem_normalizer_inf (Subgroup.le_normalizer hm)
          (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer _ (hLA hm))) (hC2.to_le inf_le_right)
        ⟨l.2, hl⟩
  have hC : ∀ l : ↥L, α l = 1 →
      (l : co3X36) ∈ Subgroup.centralizer (eSub (liftB_basis hwH hwb) : Set co3X36) := by
    intro l hl
    have h1 := hCA ((hθ l).mp ((hα1 l).mp hl))
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact eSub_comm _ y l hy h1
  refine KConfig.conclK_of_fanoEquiv h α hsurj hker hC
    (fanoEquiv (liftB_basis hwH hwb) hev hrl hind) ?_
  intro l u u' hu
  obtain ⟨hlA, T, hT, hok⟩ := hLF l l.2
  have hlW : (l : co3X36) ∈ eNorm (liftB_basis hwH hwb) := h.le_normalizer l.2
  refine fanoEquiv_conj (liftB_basis hwH hwb) hev hrl hind (liftB_basis haH hab) hlW hlA ?_ ?_
    u u' hu
  · intro j q hq1 hq8
    have hws' : List.Forall₂ (Rep 36) ws
        (List.ofFn fun i => ((liftB (permBk 36 6 ws) hwH i : co3X36) : Perm (Fin 36))) := by
      rw [show (fun i => ((liftB (permBk 36 6 ws) hwH i : co3X36) : Perm (Fin 36))) =
        permBk 36 6 ws from funext fun i => coe_liftB _ hwH i]
      exact hws
    have has' : List.Forall₂ (Rep 36) as
        (List.ofFn fun i => ((liftB (permBk 36 3 as) haH i : co3X36) : Perm (Fin 36))) := by
      rw [show (fun i => ((liftB (permBk 36 3 as) haH i : co3X36) : Perm (Fin 36))) =
        permBk 36 3 as from funext fun i => coe_liftB _ haH i]
      exact has
    exact fano_entry_of_ok hn36 (liftB_basis hwH hwb) (liftB_basis haH hab) hws' has' hrl hT hlW
      hlA hok j hq1 hq8
  · change (((invTr (CFSG.RankThree.PartTwo.Sec4.statedSLEquiv 3 (ZMod 2) (α₀ l)))⁻¹ :
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = _
    rw [← map_inv invTr, coe_invTr, inv_inv, coe_statedSLEquiv, E16.eNHom_coe]

theorem forall₂_liftB {H : Subgroup (Perm (Fin 36))} {k : ℕ} {v : Fin k → Perm (Fin 36)}
    (hvH : ∀ i, v i ∈ H) {bs : List Table} (h : List.Forall₂ (Rep 36) bs (List.ofFn v)) :
    List.Forall₂ (Rep 36) bs (List.ofFn fun i => ((liftB v hvH i : H) : Perm (Fin 36))) := by
  rw [show (fun i => ((liftB v hvH i : H) : Perm (Fin 36))) = v from
    funext fun i => coe_liftB _ hvH i]
  exact h

theorem conclK_e64cand {L V MK : Subgroup co3X36} (h : KConfig co3X36 L V MK)
    {ws as : List Table} {rows : List ℕ} (hwl : ws.length = 6) (hal : as.length = 3)
    (hsubW : subOK 36 ws ws = true) (hsubA : subOK 36 as ws = true)
    (hwS : ws.all siftOK = true) (haS : as.all siftOK = true)
    {tests : List (Table → Bool)}
    (hcnt : countProducts 36 (anyTest tests) (levelTables co3Sp36Chain) (idT 36) = 0)
    (hmW : centTestS 36 ws (spanTabs 36 ws) ∈ tests)
    (hmCA : centTestS 36 as (spanTabs 36 ws) ∈ tests)
    (hmF : fanoTestS 36 ws (spanTabs 36 ws) as (spanTabs 36 as) rows ∈ tests)
    (hev : ∀ i : Fin 6, ∑ p : FanoPoint, rowBit rows i (pmask p) = 0) (hrl : rows.length = 6)
    (hind : ∀ m < 64, (∀ q, 1 ≤ q → q < 8 → bsum rows m q = false) → m = 0)
    {U : Subgroup co3X36}
    (hU : U.map co3X36.subtype = Subgroup.closure {g | g ∈ ws.map (tabPerm 36)})
    (hUV : U ≤ V) : ConclK co3X36 L V MK := by
  have hsub' := hsubW
  simp only [subOK, Bool.and_eq_true, List.all_eq_true] at hsub'
  obtain ⟨⟨⟨⟨⟨hwt, hwe⟩, -⟩, -⟩, -⟩, -⟩ := hsub'
  have hwb := ebasis_permBk hn36 hwt hwe hwl
  have hws := forall₂_permBk hwt hwl
  obtain ⟨hwH, rfl⟩ := eq_eSub_of_map_eq_closure' hwb (closure_map_tabPerm_k hwl hwb) hU
  have hC := cent_of_test' hcnt hwb hws hws hmW
  have hVU : V ≤ eSub (liftB_basis hwH hwb) := fun v hv => by
    have hvc : v ∈ Subgroup.centralizer (eSub (liftB_basis hwH hwb) : Set co3X36) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact congrArg Subtype.val (h.elemAbelian.1.is_comm.comm ⟨u, hUV hu⟩ ⟨v, hv⟩)
    rw [mem_centralizer_liftB_iff hwH hwb] at hvc
    by_contra hvW
    exact hC v ⟨hvc, fun hm => hvW ((mem_eSub_liftB_iff hwH hwb v).mpr hm)⟩
  exact conclK_fano h hwl hal hsubW hsubA hwS haS hcnt hmCA hmF hev hrl hind hwb hwH
    (le_antisymm hVU hUV)

theorem conclK_e8cand {L V MK : Subgroup co3X36} (h : KConfig co3X36 L V MK) {x : co3X36}
    (hxT : Rep 36 x7T (x : Perm (Fin 36)))
    (hxi : Rep 36 (invT 36 x7T) (x : Perm (Fin 36))⁻¹) (hxL : x ∈ L)
    {us ws as : List Table} {rows : List ℕ} (hul : us.length = 3) (hwl : ws.length = 6)
    (hal : as.length = 3) (hsubU : subOK 36 us ws = true) (hsubW : subOK 36 ws ws = true)
    (hsubA : subOK 36 as ws = true) (hirr : irrOK 36 7 x7T (invT 36 x7T) us ws = true)
    (hwS : ws.all siftOK = true) (haS : as.all siftOK = true)
    {tests : List (Table → Bool)}
    (hcnt : countProducts 36 (anyTest tests) (levelTables co3Sp36Chain) (idT 36) = 0)
    (hmU : centTestS 36 us (spanTabs 36 ws) ∈ tests)
    (hmCA : centTestS 36 as (spanTabs 36 ws) ∈ tests)
    (hmF : fanoTestS 36 ws (spanTabs 36 ws) as (spanTabs 36 as) rows ∈ tests)
    (hev : ∀ i : Fin 6, ∑ p : FanoPoint, rowBit rows i (pmask p) = 0) (hrl : rows.length = 6)
    (hind : ∀ m < 64, (∀ q, 1 ≤ q → q < 8 → bsum rows m q = false) → m = 0)
    {U : Subgroup co3X36}
    (hU : U.map co3X36.subtype = Subgroup.closure {g | g ∈ us.map (tabPerm 36)})
    (hUV : U ≤ V) : ConclK co3X36 L V MK := by
  have hsubU' := hsubU
  simp only [subOK, Bool.and_eq_true, List.all_eq_true] at hsubU'
  obtain ⟨⟨⟨⟨⟨hut, hue⟩, hwt⟩, hwe⟩, huW⟩, -⟩ := hsubU'
  have hub := ebasis_permBk hn36 hut hue hul
  have hwb := ebasis_permBk hn36 hwt hwe hwl
  have hwH := permBk_mem hwt hwS hwl
  have hus := forall₂_permBk hut hul
  have hws := forall₂_permBk hwt hwl
  obtain ⟨huH, rfl⟩ := eq_eSub_of_map_eq_closure' hub (closure_map_tabPerm_k hul hub) hU
  have hCU := cent_of_test' hcnt hwb hus hws hmU
  have hCUW : Subgroup.centralizer (eSub (liftB_basis huH hub) : Set co3X36) ≤
      eSub (liftB_basis hwH hwb) := fun z hz => by
    rw [mem_centralizer_liftB_iff huH hub] at hz
    by_contra hzW
    exact hCU z ⟨hz, fun hm => hzW ((mem_eSub_liftB_iff hwH hwb z).mpr hm)⟩
  have hVW : V ≤ eSub (liftB_basis hwH hwb) := fun v hv => hCUW (by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact congrArg Subtype.val (h.elemAbelian.1.is_comm.comm ⟨u, hUV hu⟩ ⟨v, hv⟩))
  rcases eq_or_eq_of_irrOK hn36 (liftB_basis huH hub) (liftB_basis hwH hwb)
      (forall₂_liftB huH hus) (forall₂_liftB hwH hws) hxT hxi hirr hUV hVW
      (h.le_normalizer hxL) with hV | hV
  · subst hV
    have hW2 : IsPGroup 2 ↥(eSub (liftB_basis hwH hwb)) :=
      IsPGroup.of_card (n := 6) (by rw [card_eSub])
    exact KConfig.conclK_of_e8 (liftB_basis huH hub) h (hW2.to_le hCUW)
  · exact conclK_fano h hwl hal hsubW hsubA hwS haS hcnt hmCA hmF hev hrl hind hwb hwH hV

theorem conclK_seven (hOrb : chkOrb () = true) (h7 : chkP7 () = true)
    {L V MK : Subgroup co3X36} (h : KConfig co3X36 L V MK) {x : co3X36}
    (hxT : Rep 36 x7T (x : Perm (Fin 36))) (hx : orderOf x = 7) {y t : co3X36} (hy : y ∈ L)
    (hyx : y ∈ Subgroup.zpowers x) (ht : t ∈ V) (hyt : y * t * y⁻¹ ≠ t) :
    ConclK co3X36 L V MK := by
  obtain ⟨htabs, -, -, -, -, -, hc7, -, hs7, -, ho7⟩ := orb_facts hOrb
  obtain ⟨ht2, hcomm⟩ := h.bad_facts hy ht hyt
  obtain ⟨cg, hcg, hU⟩ :=
    orbSub_mem_cands hn36 valid (by norm_num) hxT hx hc7 ho7 hyx ht2 hyt hcomm
  have hUV : orbSub y t ≤ V := orbSub_le (h.le_normalizer hy) ht
  have hy1 : y ≠ 1 := fun h1 => hyt (by rw [h1, one_mul, inv_one, mul_one])
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hxL : x ∈ L := (Subgroup.zpowers_le.mpr hy) (mem_zpowers_of_prime hx hyx hy1)
  simp only [tabsOK, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at htabs
  have hxi : Rep 36 (invT 36 x7T) (x : Perm (Fin 36))⁻¹ :=
    Rep.inv_of_invOK hxT (invOK_of_tabOK htabs.2)
  obtain ⟨k, hk, rfl⟩ := exists_index_of_mem_candPerms hcg
  obtain ⟨hs0, hs1, hs2, hs3, hs4, hs5, hi0, hi1, hi3, hi5, hcnt⟩ := p7_facts h7
  have hlen : cands7.length = 6 := rfl
  have hsift : ∀ k < 6, (cands7.getD k []).all siftOK = true := fun k hk =>
    List.all_eq_true.mp hs7 _ (getD_mem (by rw [hlen]; exact hk))
  have hk6 : k < 6 := by rwa [hlen] at hk
  interval_cases k
  · exact conclK_e8cand h hxT hxi hxL rfl rfl rfl hs0 hs2 hs0 hi0 (hsift 2 (by norm_num))
      (hsift 0 (by norm_num)) hcnt (by simp [tests7]) (by simp [tests7]) (by simp [tests7])
      rows2_even rfl rows2_ind hU hUV
  · exact conclK_e8cand h hxT hxi hxL rfl rfl rfl hs1 hs4 hs1 hi1 (hsift 4 (by norm_num))
      (hsift 1 (by norm_num)) hcnt (by simp [tests7]) (by simp [tests7]) (by simp [tests7])
      rows4_even rfl rows4_ind hU hUV
  · exact conclK_e64cand h rfl rfl hs2 hs0 (hsift 2 (by norm_num)) (hsift 0 (by norm_num)) hcnt
      (by simp [tests7]) (by simp [tests7]) (by simp [tests7]) rows2_even rfl rows2_ind hU hUV
  · exact conclK_e8cand h hxT hxi hxL rfl rfl rfl hs3 hs2 hs0 hi3 (hsift 2 (by norm_num))
      (hsift 0 (by norm_num)) hcnt (by simp [tests7]) (by simp [tests7]) (by simp [tests7])
      rows2_even rfl rows2_ind hU hUV
  · exact conclK_e64cand h rfl rfl hs4 hs1 (hsift 4 (by norm_num)) (hsift 1 (by norm_num)) hcnt
      (by simp [tests7]) (by simp [tests7]) (by simp [tests7]) rows4_even rfl rows4_ind hU hUV
  · exact conclK_e8cand h hxT hxi hxL rfl rfl rfl hs5 hs4 hs1 hi5 (hsift 4 (by norm_num))
      (hsift 1 (by norm_num)) hcnt (by simp [tests7]) (by simp [tests7]) (by simp [tests7])
      rows4_even rfl rows4_ind hU hUV

end CFSG.SectionRank.QTK.Insp443.Sp6

end
