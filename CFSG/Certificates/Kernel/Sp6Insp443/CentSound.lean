module

public import Certificates.Data.Kernel.Sp6Insp443.Cent
public import CFSG.Certificates.Kernel.SporSch.ChainKEnum
public import CFSG.Certificates.Kernel.SporSch.MOCChain
public import CFSG.Certificates.Kernel.SporSch.J1PtSound
public import CFSG.Sporadic.Schreier.Enumeration
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.PermKit
public import Certificates.Data.CFSGNative.Insp443.PermTests
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.Spor.RawCard
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.Hyp
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure38Facts
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Quasithin.Vol2.Ch4Sec1Lem415
public import CFSG.Quasithin.Vol2.Ch4Sec4Lem445
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.J1CountCheckInputs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.KS.Sp6I

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.SporSch.MOC CFSG.Certificates
  CFSG.Sporadic.Schreier CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Quasithin.KGC31
  CFSG.Quasithin.KGC31.Native CFSG.SectionRank.QTK.Insp443.PermKit
  CFSG.SectionRank.QTK.Insp443.PermKit.Native

variable {n w : Nat}

@[expose] def bitSel (x : Nat → Equiv.Perm (Fin n)) (mk j : Nat) : Equiv.Perm (Fin n) :=
  if Nat.land (Nat.shiftRight mk j) 1 = 0 then 1 else x j

@[expose] def mprod (x : Nat → Equiv.Perm (Fin n)) (mk c : Nat) : Equiv.Perm (Fin n) :=
  ((List.range c).map (bitSel x mk)).prod

theorem mprod_zero (x : Nat → Equiv.Perm (Fin n)) (mk : Nat) : mprod x mk 0 = 1 := by
  simp [mprod]

theorem mprod_succ (x : Nat → Equiv.Perm (Fin n)) (mk c : Nat) :
    mprod x mk (c + 1) = mprod x mk c * bitSel x mk c := by
  simp only [mprod, List.range_succ, List.map_append, List.prod_append, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one]

theorem mprod_conj (x : Nat → Equiv.Perm (Fin n)) (z : Equiv.Perm (Fin n)) (mk : Nat) :
    ∀ c, mprod (fun j => z⁻¹ * x j * z) mk c = z⁻¹ * mprod x mk c * z
  | 0 => by rw [mprod_zero, mprod_zero, mul_one, inv_mul_cancel]
  | c + 1 => by
    rw [mprod_succ, mprod_succ, mprod_conj x z mk c]
    unfold bitSel
    split_ifs
    · simp only [mul_one, mul_assoc]
    · simp only [mul_assoc, mul_inv_cancel_left]

theorem commute_mprod {g : Equiv.Perm (Fin n)} {x : Nat → Equiv.Perm (Fin n)} {c : Nat}
    (h : ∀ j < c, g * x j = x j * g) (mk : Nat) : g * mprod x mk c = mprod x mk c * g := by
  have hc : Commute g (mprod x mk c) := Commute.list_prod_right _ _ fun y hy => by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
    unfold bitSel
    split_ifs
    · exact Commute.one_right g
    · exact h j (List.mem_range.1 hj)
  exact hc

theorem shiftRight_succ_half (m j : Nat) :
    Nat.shiftRight m (j + 1) = Nat.shiftRight (m / 2) j := by
  change m >>> (j + 1) = (m / 2) >>> j
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, pow_succ']

theorem land_shiftRight_zero (m : Nat) : Nat.land (Nat.shiftRight m 0) 1 = m % 2 := by
  change (m >>> 0) &&& 1 = m % 2
  rw [Nat.shiftRight_zero, Nat.and_one_is_mod]

theorem maskProd_rep (hn : n < 2 ^ 32) : ∀ {Ts : List Table} {x : Nat → Equiv.Perm (Fin n)},
    (∀ j < Ts.length, Rep n (Ts.getD j #[]) (x j)) → ∀ m,
      Rep n (maskProd n Ts m) (mprod x m Ts.length)
  | [], x, _, m => by
    rw [List.length_nil, mprod_zero]
    exact Rep.idT hn
  | T :: Ts, x, hx, m => by
    have ih := maskProd_rep hn (Ts := Ts) (x := fun j => x (j + 1))
      (fun j hj => by simpa using hx (j + 1) (by rw [List.length_cons]; omega)) (m / 2)
    have e : mprod x m (Ts.length + 1) =
        bitSel x m 0 * mprod (fun j => x (j + 1)) (m / 2) Ts.length := by
      rw [mprod, List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map, mprod]
      congr 1
      congr 1
      apply List.map_congr_left
      intro j _
      simp only [Function.comp_apply, bitSel, Nat.succ_eq_add_one, shiftRight_succ_half]
    rw [maskProd, List.length_cons, e]
    refine Rep.compT ?_ ih
    unfold bitSel
    rw [land_shiftRight_zero]
    by_cases hm : m % 2 = 1
    · rw [if_pos hm, if_neg (by omega)]
      simpa using hx 0 (by simp)
    · rw [if_neg hm, if_pos (by omega)]
      exact Rep.idT hn

theorem inSp_of_mprod (hn : n < 2 ^ 32) {Ws : List Table} {x : Nat → Equiv.Perm (Fin n)}
    (hx : ∀ j < Ws.length, Rep n (Ws.getD j #[]) (x j)) {s : Nat} (hs : s < 2 ^ Ws.length)
    {T : Table} {g : Equiv.Perm (Fin n)} (hT : Rep n T g) (hg : mprod x s Ws.length = g) :
    inSp n (spanTabs n Ws) T = true := by
  unfold inSp spanTabs
  rw [List.any_eq_true]
  exact ⟨maskProd n Ws s, List.mem_map.mpr ⟨s, List.mem_range.mpr hs, rfl⟩,
    (tblEq_iff_eq (maskProd_rep hn hx s) hT).mpr hg⟩

theorem laneK_shr (nw P j : Nat) : laneK nw P j >>> nw = 0 := by
  have e : laneK nw P j = (P >>> (nw * j)) % 2 ^ nw := by
    change (P >>> (nw * j)) &&& (1 <<< nw - 1) = _
    rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod]
  rw [e, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos nw))]

theorem lenT_eq : ∀ Ts : List Table, lenT Ts = Ts.length
  | [] => rfl
  | _ :: Ts => by
    rw [List.length_cons, ← lenT_eq Ts]
    rfl

theorem rep_of_tabPK {p : Nat} {T : Table} {g : Equiv.Perm (Fin n)} (hp : PRep n w p g)
    (h : tabPK n w (mask w) p T = true) : Rep n T g := by
  unfold tabPK at h
  intro i hi
  rw [← Nat.eq_of_beq_eq_true (Orb.allN_iff.1 h i hi), idx_of_lt g hi, Equiv.Perm.smul_def]
  exact hp ⟨i, hi⟩

theorem tabsPK_spec {nw P : Nat} : ∀ {Ts : List Table} {j : Nat},
    tabsPK n w (mask w) nw P Ts j = true →
      ∀ i < Ts.length, tabPK n w (mask w) (laneK nw P (j + i)) (Ts.getD i #[]) = true
  | [], _, _, i, hi => absurd hi (by simp)
  | T :: Ts, j, h, i, hi => by
    have h' : strictB (laneK nw P j) (fun p => bAnd(CFSG.KS.Prim.canonK n w (mask w) nw p,
        bAnd(tabPK n w (mask w) p T, tabsPK n w (mask w) nw P Ts (Nat.succ j)))) = true := h
    rw [Orb.strictB_eq, Orb.bAnd_eq, Orb.bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h'
    rcases i with _ | i
    · simpa using h'.2.1
    · have hi' : i < Ts.length := by
        rw [List.length_cons] at hi
        omega
      have := tabsPK_spec h'.2.2 i hi'
      have e : Nat.succ j + i = j + (i + 1) := by omega
      rw [List.getD_cons_succ]
      rwa [e] at this

theorem commPK_iff (hn : n < 2 ^ 32) (hw : 0 < w) {P G : Nat} {u : Nat → Equiv.Perm (Fin n)}
    {g : Equiv.Perm (Fin n)} (hG : PRep n w G g) : ∀ c,
      (∀ j < c, PRep n w (laneK (n * w) P j) (u j)) →
        (commPK n w (mask w) (n * w) P c G = true ↔ ∀ j < c, g * u j = u j * g)
  | 0, _ => ⟨fun _ j hj => absurd hj (Nat.not_lt_zero j), fun _ => rfl⟩
  | c + 1, hu => by
    have e : commPK n w (mask w) (n * w) P (c + 1) G = strictB (laneK (n * w) P c) (fun v =>
        bAnd(Nat.beq (pcomp n w (mask w) G v) (pcomp n w (mask w) v G),
          commPK n w (mask w) (n * w) P c G)) := rfl
    rw [e, Orb.strictB_eq, Orb.bAnd_eq, Bool.and_eq_true,
      beq_pcomp_iff hn hw hG (hu c (by omega)) (hu c (by omega)) hG, decide_eq_true_iff,
      commPK_iff hn hw hG c (fun j hj => hu j (by omega))]
    constructor
    · rintro ⟨h1, h2⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact h2 j hj
      · exact h1
    · intro h
      exact ⟨h c (by omega), fun j hj => h j (by omega)⟩

theorem memPK_iff (hw : 0 < w) {S G : Nat} {y : Nat → Equiv.Perm (Fin n)}
    {g : Equiv.Perm (Fin n)} (hG : PRep n w G g) (sG : G >>> (n * w) = 0) : ∀ c,
      (∀ s < c, PRep n w (laneK (n * w) S s) (y s)) →
        (memPK (n * w) S c G = true ↔ ∃ s < c, y s = g)
  | 0, _ => ⟨fun h => absurd h Bool.false_ne_true, fun ⟨s, hs, _⟩ => absurd hs (Nat.not_lt_zero s)⟩
  | c + 1, hy => by
    have e : memPK (n * w) S (c + 1) G = bIf(Nat.beq (laneK (n * w) S c) G, true,
        memPK (n * w) S c G) := rfl
    have hyc := hy c (by omega)
    have hc : Nat.beq (laneK (n * w) S c) G = true ↔ y c = g := by
      rw [Nat.beq_eq]
      constructor
      · intro h
        rw [h] at hyc
        exact SporSch.MOC.prep_unique hyc hG
      · intro h
        refine PF.eq_of_fields hw (laneK_shr _ _ _) sG fun i hi => ?_
        rw [hyc ⟨i, hi⟩, hG ⟨i, hi⟩, h]
    rw [e, Orb.bIf_eq]
    by_cases hb : Nat.beq (laneK (n * w) S c) G = true
    · rw [if_pos hb]
      exact ⟨fun _ => ⟨c, by omega, hc.1 hb⟩, fun _ => rfl⟩
    · rw [if_neg hb, memPK_iff hw hG sG c (fun s hs => hy s (by omega))]
      constructor
      · rintro ⟨s, hs, hys⟩
        exact ⟨s, by omega, hys⟩
      · rintro ⟨s, hs, hys⟩
        by_cases hsc : s < c
        · exact ⟨s, hsc, hys⟩
        · have hsc' : s = c := by omega
          rw [hsc'] at hys
          exact absurd (hc.2 hys) hb

theorem maskPK_prep (hn : n < 2 ^ 32) {nw idn P mk : Nat} {x : Nat → Equiv.Perm (Fin n)}
    (hid : PRep n w idn 1) : ∀ c, (∀ j < c, PRep n w (laneK nw P j) (x j)) →
      PRep n w (maskPK n w (mask w) nw idn P mk c) (mprod x mk c)
  | 0, _ => by
    rw [mprod_zero]
    exact hid
  | c + 1, hx => by
    have e : maskPK n w (mask w) nw idn P mk (c + 1) =
        strictN (maskPK n w (mask w) nw idn P mk c) (fun q =>
          nIf(Nat.beq (Nat.land (Nat.shiftRight mk c) (nat_lit 1)) (nat_lit 0), q,
            pcomp n w (mask w) q (laneK nw P c))) := rfl
    have ih := maskPK_prep hn (mk := mk) hid c (fun j hj => hx j (by omega))
    rw [e, Orb.strictN_eq, Orb.nIf_eq, mprod_succ]
    unfold bitSel
    by_cases hb : Nat.land (Nat.shiftRight mk c) 1 = 0
    · rw [if_pos (by rw [hb]; rfl), if_pos hb, mul_one]
      exact ih
    · rw [if_neg (by rw [Nat.beq_eq]; exact hb), if_neg hb]
      exact prep_pcomp hn ih (hx c (by omega))

theorem conjPK_prep (hn : n < 2 ^ 32) {nw T P y yi c : Nat} {t : Nat → Equiv.Perm (Fin n)}
    {z : Equiv.Perm (Fin n)} (hy : PRep n w y z) (hyi : PRep n w yi z⁻¹)
    (h : conjPK n w (mask w) nw T P y yi c = true)
    (ht : ∀ j < c, PRep n w (laneK nw T j) (t j)) :
    ∀ j < c, PRep n w (laneK nw P j) (z⁻¹ * t j * z) := by
  intro j hj
  unfold conjPK at h
  rw [Nat.eq_of_beq_eq_true (Orb.allN_iff.1 h j hj)]
  exact prep_pcomp hn (prep_pcomp hn hyi (ht j hj)) hy

theorem spanPK_prep (hn : n < 2 ^ 32) {nw idn P S c : Nat} {x : Nat → Equiv.Perm (Fin n)}
    (hid : PRep n w idn 1) (h : spanPK n w (mask w) nw idn P S c = true)
    (hx : ∀ j < c, PRep n w (laneK nw P j) (x j)) :
    ∀ s < 2 ^ c, PRep n w (laneK nw S s) (mprod x s c) := by
  intro s hs
  unfold spanPK at h
  have hs' : s < Nat.shiftLeft 1 c := by
    change s < 1 <<< c
    rwa [Nat.one_shiftLeft]
  rw [Nat.eq_of_beq_eq_true (Orb.allN_iff.1 h s hs')]
  exact maskPK_prep hn hid c hx

theorem prep_inv_of_permOK {P Q : Nat} {g : Equiv.Perm (Fin n)}
    (h : permOK n w (mask w) (n * w) P Q = true) (hP : PRep n w P g) : PRep n w Q g⁻¹ := by
  obtain ⟨-, -, h3⟩ := Orb.permOK_facts h
  intro x
  have e := (h3 (g⁻¹ x) (g⁻¹ x).2).2
  have hgx : g (g⁻¹ x) = x := by simp
  rw [hP (g⁻¹ x), hgx] at e
  exact e

theorem wordNK_prep (hn : n < 2 ^ 32) {idn : Nat} {S SI : Nat → Nat}
    {gs : Nat → Equiv.Perm (Fin n)} {H : Subgroup (Equiv.Perm (Fin n))} (hid : PRep n w idn 1)
    (hS : ∀ j < 2, PRep n w (S j) (gs j)) (hSI : ∀ j < 2, PRep n w (SI j) (gs j)⁻¹)
    (hH : ∀ j < 2, gs j ∈ H) : ∀ wd : List Nat, lettersNK wd = true →
      ∃ x ∈ H, PRep n w (wordNK n w (mask w) idn S SI wd) x
  | [], _ => ⟨1, H.one_mem, hid⟩
  | l :: wd, h => by
    have h' : bAnd(Nat.blt l (nat_lit 4), lettersNK wd) = true := h
    rw [Orb.bAnd_eq, Bool.and_eq_true] at h'
    obtain ⟨x, hx, hpx⟩ := wordNK_prep hn hid hS hSI hH wd h'.2
    have e : wordNK n w (mask w) idn S SI (l :: wd) = strictN (wordNK n w (mask w) idn S SI wd)
        (fun q => pcomp n w (mask w) (nIf(Nat.blt l (nat_lit 2), S l, SI (Nat.sub l (nat_lit 2))))
          q) := rfl
    rw [e, Orb.strictN_eq, Orb.nIf_eq]
    by_cases hl : l < 2
    · rw [if_pos (by rw [Nat.blt_eq]; exact hl)]
      exact ⟨gs l * x, H.mul_mem (hH l hl) hx, prep_pcomp hn (hS l hl) hpx⟩
    · have hl4 : l < 4 := by
        have := h'.1
        rw [Nat.blt_eq] at this
        exact this
      rw [if_neg (by rw [Nat.blt_eq]; exact hl)]
      have hl2 : l - 2 < 2 := by omega
      exact ⟨(gs (l - 2))⁻¹ * x, H.mul_mem (H.inv_mem (hH (l - 2) hl2)) hx,
        prep_pcomp hn (hSI (l - 2) hl2) hpx⟩

theorem ite_true_false (d : Bool) : (if d = true then false else true) = !d := by
  cases d <;> rfl

theorem centTestS_false_of_cnt (hn : 1 ≤ n) (hn32 : n < 2 ^ 32) (hw : 0 < w)
    {gens : List (Equiv.Perm (Fin n))} {words : List (List Int)} {k : Nat}
    {bv : Vector (Fin n) k} (hbs : bv.toList.Nodup) {PS PSI LR TR TRI : Nat → Nat}
    {kS BP NS CH : Nat} (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH)
    {H : Subgroup (Equiv.Perm (Fin n))} {r : Equiv.Perm (Fin n)}
    (hC : centralizerIn H r ≤ (certificate hn gens words bv hbs).originalSubgroup)
    {idn : Nat} (hid : PRep n w idn 1) (sid : idn >>> (n * w) = 0)
    {C CI : Nat} {c : Equiv.Perm (Fin n)} (hc : PRep n w C c) (hci : PRep n w CI c⁻¹)
    (hcH : c ∈ H) {Us Ws : List Table} {UT WT UP WP SP uM a b : Nat}
    (hUT : tabsPK n w (mask w) (n * w) UT Us 0 = true)
    (hWT : tabsPK n w (mask w) (n * w) WT Ws 0 = true) (ha : lenT Us = a) (hb : lenT Ws = b)
    (hUi : allN a (fun j => permOK n w (mask w) (n * w) (laneK (n * w) UT j)
      (laneK (n * w) UT j)) = true)
    (hWi : allN b (fun j => permOK n w (mask w) (n * w) (laneK (n * w) WT j)
      (laneK (n * w) WT j)) = true)
    (hcu : conjPK n w (mask w) (n * w) UT UP C CI a = true)
    (hcw : conjPK n w (mask w) (n * w) WT WP C CI b = true)
    (hr : PRep n w (maskPK n w (mask w) (n * w) idn UP uM a) r)
    (hsp : spanPK n w (mask w) (n * w) idn WP SP b = true)
    (hcnt : centCntK n w (mask w) (n * w) LR TR k idn UP a SP b = 0)
    {g : Equiv.Perm (Fin n)} (hg : g ∈ H) {T : Table} (hT : Rep n T g) :
    centTestS n Us (spanTabs n Ws) T = false := by
  classical
  have hUl : Us.length = a := by rw [← ha, lenT_eq]
  have hWl : Ws.length = b := by rw [← hb, lenT_eq]
  have hu0 : ∀ j, ∃ v : Equiv.Perm (Fin n), j < a → PRep n w (laneK (n * w) UT j) v := by
    intro j
    by_cases hj : j < a
    · obtain ⟨v, hv⟩ := SporSch.MOC.exists_prep (Orb.allN_iff.1 hUi j hj)
      exact ⟨v, fun _ => hv⟩
    · exact ⟨1, fun h => absurd h hj⟩
  have hw0 : ∀ j, ∃ v : Equiv.Perm (Fin n), j < b → PRep n w (laneK (n * w) WT j) v := by
    intro j
    by_cases hj : j < b
    · obtain ⟨v, hv⟩ := SporSch.MOC.exists_prep (Orb.allN_iff.1 hWi j hj)
      exact ⟨v, fun _ => hv⟩
    · exact ⟨1, fun h => absurd h hj⟩
  choose u hu using hu0
  choose x hx using hw0
  have hUr : ∀ j < Us.length, Rep n (Us.getD j #[]) (u j) := fun j hj =>
    rep_of_tabPK (hu j (by omega)) (by simpa using tabsPK_spec hUT j hj)
  have hWr : ∀ j < Ws.length, Rep n (Ws.getD j #[]) (x j) := fun j hj =>
    rep_of_tabPK (hx j (by omega)) (by simpa using tabsPK_spec hWT j hj)
  have hup := conjPK_prep hn32 hc hci hcu hu
  have hwp := conjPK_prep hn32 hc hci hcw hx
  have hsP := spanPK_prep hn32 hid hsp hwp
  have hrr : r = mprod (fun j => c⁻¹ * u j * c) uM a := SporSch.MOC.prep_unique hr (maskPK_prep hn32 hid a hup)
  rw [← Bool.not_eq_true]
  intro hcent
  unfold centTestS at hcent
  rw [Bool.and_eq_true, Bool.not_eq_true'] at hcent
  obtain ⟨hcomm, hin⟩ := hcent
  have hgu : ∀ j < a, g * u j = u j * g := fun j hj => by
    have hj' : j < Us.length := by omega
    unfold commAllT at hcomm
    have hmem : Us.getD j #[] ∈ Us := by
      rw [List.getD_eq_getElem _ _ hj']
      exact List.getElem_mem _
    exact (commT2_iff hT (hUr j hj')).mp (List.all_eq_true.mp hcomm _ hmem)
  have hg'u : ∀ j < a, c⁻¹ * g * c * (c⁻¹ * u j * c) = c⁻¹ * u j * c * (c⁻¹ * g * c) :=
    fun j hj => by
      simp only [mul_assoc, mul_inv_cancel_left]
      rw [← mul_assoc g, hgu j hj, mul_assoc]
  have hgr : c⁻¹ * g * c * r = r * (c⁻¹ * g * c) := by
    rw [hrr]
    exact commute_mprod hg'u uM
  have hg'H : c⁻¹ * g * c ∈ H := H.mul_mem (H.mul_mem (H.inv_mem hcH) hg) hcH
  have hg'Q := hC (mem_centralizerIn.2 ⟨hg'H, hgr⟩)
  have hen := (mem_enumeration_iff _ (chainK_check hn hbs hQ).1 _).2 hg'Q
  rw [enumeration_trL hQ hn hbs] at hen
  let q : Equiv.Perm (Fin n) → Bool := fun y =>
    decide (∀ j < a, y * (c⁻¹ * u j * c) = c⁻¹ * u j * c * y) &&
      !decide (∃ s < 2 ^ b, mprod (fun j => c⁻¹ * x j * c) s b = y)
  have hp : ∀ P y, PRep n w P y → P >>> (n * w) = 0 →
      (fun G => bAnd(commPK n w (mask w) (n * w) UP a G,
        bIf(memPK (n * w) SP (Nat.shiftLeft (nat_lit 1) b) G, false, true))) P = q y := by
    intro P y hP sP
    have h1 : commPK n w (mask w) (n * w) UP a P =
        decide (∀ j < a, y * (c⁻¹ * u j * c) = c⁻¹ * u j * c * y) := by
      by_cases h : ∀ j < a, y * (c⁻¹ * u j * c) = c⁻¹ * u j * c * y
      · rw [decide_eq_true h]
        exact (commPK_iff hn32 hw hP a hup).2 h
      · rw [decide_eq_false h]
        exact Bool.eq_false_iff.2 fun h' => h ((commPK_iff hn32 hw hP a hup).1 h')
    have e2 : Nat.shiftLeft (nat_lit 1) b = 2 ^ b := Nat.one_shiftLeft b
    have h2 : memPK (n * w) SP (Nat.shiftLeft (nat_lit 1) b) P =
        decide (∃ s < 2 ^ b, mprod (fun j => c⁻¹ * x j * c) s b = y) := by
      rw [e2]
      by_cases h : ∃ s < 2 ^ b, mprod (fun j => c⁻¹ * x j * c) s b = y
      · rw [decide_eq_true h]
        exact (memPK_iff hw hP sP _ hsP).2 h
      · rw [decide_eq_false h]
        exact Bool.eq_false_iff.2 fun h' => h ((memPK_iff hw hP sP _ hsP).1 h')
    change bAnd(commPK n w (mask w) (n * w) UP a P,
      bIf(memPK (n * w) SP (Nat.shiftLeft (nat_lit 1) b) P, false, true)) = q y
    rw [Orb.bAnd_eq, Orb.bIf_eq, h1, h2, ite_true_false]
  have hcnt' : enumFrom n w (mask w) (n * w) LR TR (fun G => bAnd(commPK n w (mask w) (n * w) UP a G,
      bIf(memPK (n * w) SP (Nat.shiftLeft (nat_lit 1) b) G, false, true))) k (nat_lit 0) idn
      (nat_lit 0) = 0 := by
    have e : centCntK n w (mask w) (n * w) LR TR k idn UP a SP b = enumFrom n w (mask w) (n * w)
        LR TR (fun G => bAnd(commPK n w (mask w) (n * w) UP a G,
          bIf(memPK (n * w) SP (Nat.shiftLeft (nat_lit 1) b) G, false, true))) k (nat_lit 0) idn
        (nat_lit 0) := by
      unfold centCntK
      rw [Orb.strictN_eq, Orb.strictN_eq, Orb.strictN_eq, Orb.strictN_eq]
    rw [← e]
    exact hcnt
  rw [enumFrom_spec hQ hp k 0 (by omega) idn 1 0 hid sid, Nat.zero_add] at hcnt'
  have hq := List.countP_eq_zero.1 hcnt' (c⁻¹ * g * c) (by
    rw [List.mem_map]
    refine ⟨c⁻¹ * g * c, ?_, one_mul _⟩
    simpa only [Nat.zero_add] using hen)
  have hex : ∃ s < 2 ^ b, mprod (fun j => c⁻¹ * x j * c) s b = c⁻¹ * g * c := by
    by_contra hne
    apply hq
    simp only [q, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
    exact ⟨hg'u, hne⟩
  obtain ⟨s, hs, hs'⟩ := hex
  rw [mprod_conj, mul_right_cancel_iff, mul_left_cancel_iff] at hs'
  rw [inSp_of_mprod hn32 hWr (by rw [hWl]; exact hs) hT (by rw [hWl]; exact hs')] at hin
  exact Bool.false_ne_true hin.symm

end CFSG.KS.Sp6I

end
