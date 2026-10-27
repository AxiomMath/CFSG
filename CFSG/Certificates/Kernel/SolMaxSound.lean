module

public import Certificates.Data.Kernel.SolMaxK
public import Certificates.Data.SolMaxEightPerm
public import CFSG.Certificates.Kernel.Spor.PEnumSound
import CFSG.Certificates.Kernel.L34KSnd.Tab
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.SolMax

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KS.PEnum
open CFSG.PSL3Four.Native CFSG.ComponentClassification.SolMax.SixGen
  CFSG.ComponentClassification.SolMax.ThreeCent CFSG.ComponentClassification.SolMax.EightPerm
open CFSG.KLie.CT (andB orB notB)

abbrev Cn (p : Nat) : Prop := canonK 9 4 (mask 4) (9 * 4) p = true

theorem hsz : szOK 9 4 = true := by decide

theorem cn_pc {p q : Nat} (hp : Cn p) (hq : Cn q) : Cn (pc9 p q) := canonK_pcomp hp hq

theorem cn_e : Cn e9 := CFSG.KC.L34KSnd.canon_pidn hsz

theorem comp_u {p q : Nat} (hp : Cn p) (hq : Cn q) :
    comp 9 (unpack 9 4 p) (unpack 9 4 q) = unpack 9 4 (pc9 p q) :=
  CFSG.KC.L34KSnd.comp_unpack' hp hq

theorem id_u : idTab 9 = unpack 9 4 e9 := CFSG.KC.L34KSnd.idTab_unpack' hsz

theorem beq_u {p q : Nat} (hp : Cn p) (hq : Cn q) :
    (unpack 9 4 p == unpack 9 4 q) = Nat.beq p q :=
  CFSG.KC.L34KSnd.beq_unpack hp hq

theorem strictN_app (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem strictB_app (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem cntK_eq (f : Nat → Bool) : ∀ n, cntK f n = ((List.range n).filter fun i => !f i).length
  | 0 => rfl
  | n + 1 => by
    have e : cntK f (n + 1) = strictN (cntK f n) fun a =>
        Bool.rec (motive := fun _ => Nat) (Nat.succ a) a (f n) := rfl
    rw [e, strictN_app, cntK_eq f n, List.range_succ, List.filter_append, List.length_append]
    cases h : f n <;> simp [h]

theorem supp_u (p : Nat) : threeCentSupp (unpack 9 4 p) = suppK p := by
  unfold threeCentSupp countBelow suppK
  rw [cntK_eq]
  congr 1

theorem orB_eq (a b : Bool) : CFSG.KLie.CT.orB a b = (a || b) := by cases a <;> rfl

theorem andB_eq (a b : Bool) : CFSG.KLie.CT.andB a b = (a && b) := by cases a <;> rfl

theorem notB_eq (a : Bool) : CFSG.KLie.CT.notB a = !a := by cases a <;> rfl

theorem blt_eq (a b : Nat) : Nat.blt a b = decide (a < b) := by
  cases h : Nat.blt a b
  · have : ¬ a < b := fun h' => by rw [Nat.blt_eq.mpr h'] at h; exact Bool.false_ne_true h.symm
    simp [this]
  · simp [Nat.blt_eq.mp h]

theorem ble_eq (a b : Nat) : Nat.ble a b = decide (a ≤ b) := by
  cases h : Nat.ble a b
  · have : ¬ a ≤ b := fun h' => by rw [Nat.ble_eq.mpr h'] at h; exact Bool.false_ne_true h.symm
    simp [this]
  · simp [Nat.ble_eq.mp h]

theorem mem_rec {cnt : Nat} {T PL : Nat → Nat} {x : Tab} :
    x ∈ (penumRec 9 4 cnt T PL).tabs ↔ ∃ i < cnt, unpack 9 4 (T i) = x := by
  rw [penumRec_eq]
  simp only [Array.mem_ofFn]
  constructor
  · rintro ⟨⟨i, hi⟩, e⟩
    exact ⟨i, hi, e⟩
  · rintro ⟨i, hi, e⟩
    exact ⟨⟨i, hi⟩, e⟩

theorem all_rec {cnt : Nat} {T PL : Nat → Nat} {f : Tab → Bool}
    (h : ∀ i < cnt, f (unpack 9 4 (T i)) = true) : (penumRec 9 4 cnt T PL).tabs.all f = true := by
  rw [Array.all_eq_true_iff_forall_mem]
  intro x hx
  obtain ⟨i, hi, rfl⟩ := mem_rec.1 hx
  exact h i hi

theorem comm_of {c : Swaps × List Swaps × Nat} {k : Nat} {G : Nat → Nat} {U : Nat}
    (hg : GensOK 9 4 k G (gsOf c)) (hu : tabOf (permOf c.1) = unpack 9 4 U) (hU : Cn U)
    (hc : commK k G U = true) :
    ((gsOf c).all fun g => commutes g (tabOf (permOf c.1))) = true := by
  rw [Array.all_eq_true]
  intro j hj
  have hj' : j < k := hg.1 ▸ hj
  obtain ⟨e, cg⟩ := hg.2 j hj'
  rw [← getElem!_pos (gsOf c) j hj, e, hu]
  unfold commutes
  rw [comp_u cg hU, comp_u hU cg, beq_u (cn_pc cg hU) (cn_pc hU cg)]
  exact CFSG.KS.Raw.Orb.allN_iff.1 hc j hj'

theorem enum_of {c : Swaps × List Swaps × Nat} {k cnt : Nat}
    {G GI T PL POS SRT SRI : Nat → Nat} (hg : GensOK 9 4 k G (gsOf c))
    (hh : penumHdK (pidn 9 4) cnt c.2.2 T PL = true)
    (hp : ∀ i < cnt, penumPtK 9 4 (mask 4) (9 * 4) false G GI k cnt T PL POS SRT SRI i = true) :
    enumBFS 9 (gsOf c) c.2.2 = penumRec 9 4 cnt T PL ∧
      enumOK 9 (gsOf c) (penumRec 9 4 cnt T PL) = true :=
  penumK_left_sound hsz hg hh hp

theorem pt_canon {k cnt i : Nat} {G GI T PL POS SRT SRI : Nat → Nat}
    (h : penumPtK 9 4 (mask 4) (9 * 4) false G GI k cnt T PL POS SRT SRI i = true) : Cn (T i) := by
  unfold penumPtK at h
  rw [strictB_app] at h
  cases hc : canonK 9 4 (mask 4) (9 * 4) (T i)
  · rw [hc] at h
    exact absurd h Bool.false_ne_true
  · exact hc

theorem size_rec (cnt : Nat) (T PL : Nat → Nat) : (penumRec 9 4 cnt T PL).tabs.size = cnt := by
  rw [penumRec_eq, Array.size_ofFn]

theorem threeCase_of {c : Swaps × List Swaps × Nat} {k cnt : Nat}
    {G GI T PL POS SRT SRI : Nat → Nat} {U : Nat} (hg : GensOK 9 4 k G (gsOf c))
    (hh : penumHdK (pidn 9 4) cnt c.2.2 T PL = true)
    (hp : ∀ i < cnt, penumPtK 9 4 (mask 4) (9 * 4) false G GI k cnt T PL POS SRT SRI i = true)
    (hcnt : cnt = c.2.2) (hu : tabOf (permOf c.1) = unpack 9 4 U) (hU : Cn U)
    (hc : commK k G U = true) (hx : restXK cnt T = true) (hy : restYK cnt T = true) :
    threeCentCaseOK c = true := by
  have hT : ∀ i < cnt, Cn (T i) := fun i hi => pt_canon (hp i hi)
  have henum := enum_of hg hh hp
  change (((((gsOf c).all fun g => commutes g (tabOf (permOf c.1))) &&
      enumOK 9 (gsOf c) (enumBFS 9 (gsOf c) c.2.2) &&
      (enumBFS 9 (gsOf c) c.2.2).tabs.size == c.2.2) &&
      (enumBFS 9 (gsOf c) c.2.2).tabs.all (fun y =>
        comp 9 y y == idTab 9 || !(comp 9 (comp 9 y y) (comp 9 y y) == idTab 9) ||
          threeCentSupp y < 6 || threeCentSupp (comp 9 y y) < 6)) &&
      ((enumBFS 9 (gsOf c) c.2.2).tabs.filter fun a =>
        comp 9 a a == idTab 9 && !(a == idTab 9) && 6 ≤ threeCentSupp a).all (fun a =>
        ((enumBFS 9 (gsOf c) c.2.2).tabs.filter fun a =>
          comp 9 a a == idTab 9 && !(a == idTab 9) && 6 ≤ threeCentSupp a).all fun b =>
          a == b || !commutes a b || threeCentSupp (comp 9 a b) < 6)) = true
  have hs : ((penumRec 9 4 cnt T PL).tabs.size == c.2.2) = true := by
    rw [size_rec, hcnt]
    exact beq_self_eq_true _
  rw [henum.1, henum.2, comm_of hg hu hU hc, hs]
  simp only [Bool.true_and, Bool.and_eq_true]
  refine ⟨all_rec fun i hi => ?_, ?_⟩
  · have h := CFSG.KS.Raw.Orb.allN_iff.1 hx i hi
    rw [strictB_app, strictB_app] at h
    have cy := hT i hi
    rw [comp_u cy cy, comp_u (cn_pc cy cy) (cn_pc cy cy), id_u, beq_u (cn_pc cy cy) cn_e,
      beq_u (cn_pc (cn_pc cy cy) (cn_pc cy cy)) cn_e, supp_u, supp_u]
    simpa only [orB_eq, notB_eq, blt_eq, Bool.or_assoc] using h
  · rw [Array.all_eq_true_iff_forall_mem]
    intro a ha
    rw [Array.all_eq_true_iff_forall_mem]
    intro b hb
    rw [Array.mem_filter] at ha hb
    obtain ⟨ha, hba⟩ := ha
    obtain ⟨hb, hbb⟩ := hb
    obtain ⟨i, hi, rfl⟩ := mem_rec.1 ha
    obtain ⟨j, hj, rfl⟩ := mem_rec.1 hb
    have ci := hT i hi
    have cj := hT j hj
    have bigI : bigK (T i) = true := by
      unfold bigK
      rw [comp_u ci ci, id_u, beq_u (cn_pc ci ci) cn_e, beq_u ci cn_e, supp_u] at hba
      simpa only [andB_eq, notB_eq, ble_eq, Bool.and_assoc] using hba
    have bigJ : bigK (T j) = true := by
      unfold bigK
      rw [comp_u cj cj, id_u, beq_u (cn_pc cj cj) cn_e, beq_u cj cn_e, supp_u] at hbb
      simpa only [andB_eq, notB_eq, ble_eq, Bool.and_assoc] using hbb
    have h := CFSG.KS.Raw.Orb.allN_iff.1 hy i hi
    rw [strictB_app, bigI] at h
    simp only [orB_eq, notB_eq, Bool.not_true, Bool.false_or] at h
    have h2 := CFSG.KS.Raw.Orb.allN_iff.1 h j hj
    rw [strictB_app, bigJ] at h2
    unfold commutes
    rw [beq_u ci cj, comp_u ci cj, comp_u cj ci, beq_u (cn_pc ci cj) (cn_pc cj ci), supp_u]
    simpa only [orB_eq, notB_eq, Bool.not_true, Bool.false_or, blt_eq, Bool.or_assoc] using h2

theorem allN_congr {n : Nat} {f g : Nat → Bool} (h : ∀ i < n, f i = g i) :
    allN n f = allN n g := by
  rw [Bool.eq_iff_iff, CFSG.KS.Raw.Orb.allN_iff, CFSG.KS.Raw.Orb.allN_iff]
  exact forall_congr' fun i => imp_congr_right fun hi => by rw [h i hi]

theorem all_filter_rec {cnt : Nat} {T PL : Nat → Nat} (p q : Tab → Bool) :
    ((penumRec 9 4 cnt T PL).tabs.filter p).all q =
      allN cnt (fun i => !p (unpack 9 4 (T i)) || q (unpack 9 4 (T i))) := by
  rw [Bool.eq_iff_iff, Array.all_eq_true_iff_forall_mem, CFSG.KS.Raw.Orb.allN_iff]
  constructor
  · intro H i hi
    cases hp : p (unpack 9 4 (T i))
    · rfl
    · rw [Bool.not_true, Bool.false_or]
      exact H _ (Array.mem_filter.2 ⟨mem_rec.2 ⟨i, hi, rfl⟩, hp⟩)
  · intro H x hx
    rw [Array.mem_filter] at hx
    obtain ⟨hx, hp⟩ := hx
    obtain ⟨i, hi, rfl⟩ := mem_rec.1 hx
    have h := H i hi
    rw [hp, Bool.not_true, Bool.false_or] at h
    exact h

theorem adm_u {U w : Nat} (hU : Cn U) (hw : Cn w) :
    eightAdmissible (unpack 9 4 U) (unpack 9 4 w) = admK U w := by
  unfold eightAdmissible admK
  rw [comp_u hw hw, comp_u hw hU, id_u, beq_u (cn_pc hw hw) hU, beq_u (cn_pc hw hw) cn_e, supp_u,
    supp_u]
  simp only [orB_eq, andB_eq, ble_eq, Bool.and_assoc]

theorem link_u {U a b : Nat} (hU : Cn U) (ha : Cn a) (hb : Cn b) :
    eightLinked (unpack 9 4 U) (unpack 9 4 a) (unpack 9 4 b) = linkK U a b := by
  unfold eightLinked linkK commutes
  rw [comp_u ha hb, comp_u hb ha, id_u, beq_u (cn_pc ha hb) (cn_pc hb ha),
    beq_u (cn_pc ha hb) cn_e, beq_u (cn_pc ha hb) hU]
  simp only [andB_eq, notB_eq, Bool.and_assoc]

theorem eightCase_of {c : Swaps × List Swaps × Nat} {k cnt : Nat}
    {G GI T PL POS SRT SRI : Nat → Nat} {U : Nat} (hg : GensOK 9 4 k G (gsOf c))
    (hh : penumHdK (pidn 9 4) cnt c.2.2 T PL = true)
    (hp : ∀ i < cnt, penumPtK 9 4 (mask 4) (9 * 4) false G GI k cnt T PL POS SRT SRI i = true)
    (hcnt : cnt = c.2.2) (hu : tabOf (permOf c.1) = unpack 9 4 U) (hU : Cn U)
    (hc : commK k G U = true) (hz : restZK U cnt T = true) :
    eightPermCaseOK c = true := by
  have hT : ∀ i < cnt, Cn (T i) := fun i hi => pt_canon (hp i hi)
  have henum := enum_of hg hh hp
  change ((((gsOf c).all fun g => commutes g (tabOf (permOf c.1))) &&
      enumOK 9 (gsOf c) (enumBFS 9 (gsOf c) c.2.2) &&
      (enumBFS 9 (gsOf c) c.2.2).tabs.size == c.2.2) &&
      ((enumBFS 9 (gsOf c) c.2.2).tabs.filter (eightAdmissible (tabOf (permOf c.1)))).all
        (fun a => ((enumBFS 9 (gsOf c) c.2.2).tabs.filter
          (eightAdmissible (tabOf (permOf c.1)))).all fun b =>
          !eightLinked (tabOf (permOf c.1)) a b ||
          ((enumBFS 9 (gsOf c) c.2.2).tabs.filter
            (eightAdmissible (tabOf (permOf c.1)))).all fun c' =>
            !(eightLinked (tabOf (permOf c.1)) a c' && eightLinked (tabOf (permOf c.1)) b c') ||
            ((enumBFS 9 (gsOf c) c.2.2).tabs.filter
              (eightAdmissible (tabOf (permOf c.1)))).all fun d =>
              !(eightLinked (tabOf (permOf c.1)) a d && eightLinked (tabOf (permOf c.1)) b d &&
                eightLinked (tabOf (permOf c.1)) c' d))) = true
  have hs : ((penumRec 9 4 cnt T PL).tabs.size == c.2.2) = true := by
    rw [size_rec, hcnt]
    exact beq_self_eq_true _
  rw [henum.1, henum.2, comm_of hg hu hU hc, hs]
  simp only [Bool.true_and]
  rw [hu]
  simp only [all_filter_rec]
  unfold restZK at hz
  simp only [strictB_app, orB_eq, notB_eq, andB_eq] at hz
  refine Eq.trans ?_ hz
  apply allN_congr
  intro i hi
  rw [adm_u hU (hT i hi)]
  refine congrArg (fun t => (!admK U (T i)) || t) ?_
  apply allN_congr
  intro j hj
  rw [adm_u hU (hT j hj), link_u hU (hT i hi) (hT j hj)]
  refine congrArg (fun t => (!admK U (T j)) || ((!linkK U (T i) (T j)) || t)) ?_
  apply allN_congr
  intro l hl
  rw [adm_u hU (hT l hl), link_u hU (hT i hi) (hT l hl), link_u hU (hT j hj) (hT l hl)]
  refine congrArg (fun t => (!admK U (T l)) ||
    ((!(linkK U (T i) (T l) && linkK U (T j) (T l))) || t)) ?_
  apply allN_congr
  intro m hm
  rw [adm_u hU (hT m hm), link_u hU (hT i hi) (hT m hm), link_u hU (hT j hj) (hT m hm),
    link_u hU (hT l hl) (hT m hm), Bool.and_assoc]

end CFSG.KC.SolMax

end
