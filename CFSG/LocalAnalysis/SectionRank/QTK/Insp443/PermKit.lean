module

public import Certificates.Data.PermOrbKit
public import CFSG.Quasithin.Vol2.KGFactC31OrbSound
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.KConfig

public section

namespace CFSG.SectionRank.QTK.Insp443.PermKit

open Equiv CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Native
  CFSG.SectionRank.QTK.Insp443.PermKit.Native

variable {n : ℕ}

open scoped Classical in
@[expose] noncomputable def tabPerm (n : ℕ) (T : Table) : Perm (Fin n) :=
  if h : (∀ i < n, ap T i < n) ∧ ∀ i < n, ∀ j < n, ap T i = ap T j → i = j then
    Equiv.ofBijective (fun i : Fin n => (⟨ap T i, h.1 i i.2⟩ : Fin n))
      (Finite.injective_iff_bijective.1 fun i j hij =>
        Fin.ext (h.2 i i.2 j j.2 (Fin.mk.inj hij)))
  else 1

theorem rep_tabPerm {T R : Table} (h : tabOK n T R = true) : Rep n T (tabPerm n T) := by
  have h' := allIn_eq_true.1 h
  have hc : (∀ i < n, ap T i < n) ∧ ∀ i < n, ∀ j < n, ap T i = ap T j → i = j := by
    refine ⟨fun i hi => ?_, fun i hi j hj hij => ?_⟩
    · have h1 := h' i (Nat.zero_le _) hi
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
      exact h1.1
    · have h1 := h' i (Nat.zero_le _) hi
      have h2 := h' j (Nat.zero_le _) hj
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h1 h2
      rw [← h1.2, ← h2.2, hij]
  intro i hi
  rw [idx_of_lt _ hi, tabPerm, dif_pos hc]
  rfl

theorem commT2_iff {S T : Table} {g h : Perm (Fin n)} (hS : Rep n S g) (hT : Rep n T h) :
    commT2 n S T = true ↔ g * h = h * g :=
  tblEq_iff_eq (Rep.compT hS hT) (Rep.compT hT hS)

theorem commAllT_iff {k : ℕ} {v : Fin k → Perm (Fin n)} {bs : List Table}
    (hbs : List.Forall₂ (Rep n) bs (List.ofFn v)) {T : Table} {g : Perm (Fin n)}
    (hT : Rep n T g) : commAllT n bs T = true ↔ ∀ i, g * v i = v i * g := by
  unfold commAllT
  rw [List.all_eq_true]
  constructor
  · intro h i
    obtain ⟨b, hb, hbi⟩ := exists_tab_of_mem hbs (List.mem_ofFn.mpr ⟨i, rfl⟩)
    exact (commT2_iff hT hbi).mp (h b hb)
  · intro h b hb
    obtain ⟨x, hx, hbx⟩ := exists_rep_of_mem hbs hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact (commT2_iff hT hbx).mpr (h i)

theorem inSpanT_iff (hn : n < 2 ^ 32) {k : ℕ} {v : Fin k → Perm (Fin n)} {bs : List Table}
    (hbs : List.Forall₂ (Rep n) bs (List.ofFn v)) {T : Table} {g : Perm (Fin n)}
    (hT : Rep n T g) : inSpanT n bs T = true ↔ ∃ c, eElt v c = g :=
  mem_spanTabs_iff hn hbs (f := fun u => tblEq n u T) (P := fun u => u = g)
    fun _ _ hU => tblEq_iff_eq hU hT

theorem inSpanT_iff_mem (hn : n < 2 ^ 32) {k : ℕ} {v : Fin k → Perm (Fin n)} (hb : EBasis v)
    {bs : List Table} (hbs : List.Forall₂ (Rep n) bs (List.ofFn v)) {T : Table}
    {g : Perm (Fin n)} (hT : Rep n T g) : inSpanT n bs T = true ↔ g ∈ eSub hb := by
  rw [inSpanT_iff hn hbs hT, mem_eSub_iff]

theorem conjSpanIn_iff (hn : n < 2 ^ 32) {k l : ℕ} {v : Fin k → Perm (Fin n)}
    {w : Fin l → Perm (Fin n)} {bs cs : List Table} (hbs : List.Forall₂ (Rep n) bs (List.ofFn v))
    (hcs : List.Forall₂ (Rep n) cs (List.ofFn w)) {T : Table} {g : Perm (Fin n)}
    (hT : Rep n T g) :
    conjSpanIn n bs cs T = true ↔ ∀ i, ∃ c, g * v i * g⁻¹ = eElt w c := by
  have key : ∀ (b : Table) (x : Perm (Fin n)), Rep n b x →
      (((spanTabs n cs).any fun u => compEq n T b u) = true ↔ ∃ c, g * x = eElt w c * g) :=
    fun b x hb => mem_spanTabs_iff hn hcs (f := fun u => compEq n T b u)
      (P := fun u => g * x = u * g) fun U u hU => compEq_iff hT hb hU
  show (bs.all fun b => (spanTabs n cs).any fun u => compEq n T b u) = true ↔ _
  rw [List.all_eq_true]
  constructor
  · intro h i
    obtain ⟨b, hb, hbi⟩ := exists_tab_of_mem hbs (List.mem_ofFn.mpr ⟨i, rfl⟩)
    obtain ⟨c, hc⟩ := (key b (v i) hbi).mp (h b hb)
    exact ⟨c, by rw [hc, mul_inv_cancel_right]⟩
  · intro h b hb
    obtain ⟨x, hx, hbx⟩ := exists_rep_of_mem hbs hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    obtain ⟨c, hc⟩ := h i
    exact (key b (v i) hbx).mpr ⟨c, by rw [← hc, inv_mul_cancel_right]⟩

theorem spanEq_iff (hn : n < 2 ^ 32) {k l : ℕ} {v : Fin k → Perm (Fin n)}
    {w : Fin l → Perm (Fin n)} (hv : EBasis v) (hw : EBasis w) {bs cs : List Table}
    (hbs : List.Forall₂ (Rep n) bs (List.ofFn v)) (hcs : List.Forall₂ (Rep n) cs (List.ofFn w))
    (h : spanEq n bs cs = true) : eSub hv = eSub hw := by
  unfold spanEq at h
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  apply le_antisymm
  · rw [eSub_eq_closure hv, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨b, hb, hbi⟩ := exists_tab_of_mem hbs (List.mem_ofFn.mpr ⟨i, rfl⟩)
    exact (inSpanT_iff_mem hn hw hcs hbi).mp (h1 b hb)
  · rw [eSub_eq_closure hw, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨c, hc, hci⟩ := exists_tab_of_mem hcs (List.mem_ofFn.mpr ⟨i, rfl⟩)
    exact (inSpanT_iff_mem hn hv hbs hci).mp (h2 c hc)

section Count

variable (hn : n < 2 ^ 32) (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
include hn hQ

theorem exists_of_countProducts_ne_zero {f : Table → Bool} {P : Perm (Fin n) → Prop}
    [DecidablePred P] (hfP : ∀ T g, Rep n T g → (f T = true ↔ P g))
    (h : countProducts n f (levelTables Q) (idT n) ≠ 0) : ∃ x : Q.originalSubgroup, P x := by
  rw [← card_subtype_eq_countProducts hn Q hQ hfP] at h
  obtain ⟨⟨x, hx⟩⟩ := (Nat.card_ne_zero.mp h).1
  exact ⟨x, hx⟩

theorem forall_of_countProducts_eq_zero {f : Table → Bool} {P : Perm (Fin n) → Prop}
    [DecidablePred P] (hfP : ∀ T g, Rep n T g → (f T = true ↔ P g))
    (h : countProducts n f (levelTables Q) (idT n) = 0) : ∀ x : Q.originalSubgroup, ¬ P x := by
  rw [← card_subtype_eq_countProducts hn Q hQ hfP] at h
  intro x hx
  have : Nonempty {x : Q.originalSubgroup // P x} := ⟨⟨x, hx⟩⟩
  exact (Nat.card_pos (α := {x : Q.originalSubgroup // P x})).ne' h

theorem mem_of_count_tblEq {T : Table} {g : Perm (Fin n)} (hT : Rep n T g)
    (h : countProducts n (fun S => tblEq n S T) (levelTables Q) (idT n) ≠ 0) :
    g ∈ Q.originalSubgroup := by
  classical
  obtain ⟨x, hx⟩ := exists_of_countProducts_ne_zero hn Q hQ (P := fun x => x = g)
    (fun _ _ hS => tblEq_iff_eq hS hT) h
  rw [← hx]
  exact x.2

end Count

@[expose] def liftB {H : Subgroup (Perm (Fin n))} {k : ℕ} (v : Fin k → Perm (Fin n))
    (hv : ∀ i, v i ∈ H) : Fin k → H :=
  fun i => ⟨v i, hv i⟩

theorem coe_liftB {H : Subgroup (Perm (Fin n))} {k : ℕ} (v : Fin k → Perm (Fin n))
    (hv : ∀ i, v i ∈ H) (i : Fin k) : ((liftB v hv i : H) : Perm (Fin n)) = v i := rfl

theorem coe_eElt_liftB {H : Subgroup (Perm (Fin n))} {k : ℕ} (v : Fin k → Perm (Fin n))
    (hv : ∀ i, v i ∈ H) (c : Fin k → ZMod 2) :
    ((eElt (liftB v hv) c : H) : Perm (Fin n)) = eElt v c :=
  map_eElt H.subtype c

theorem liftB_basis {H : Subgroup (Perm (Fin n))} {k : ℕ} {v : Fin k → Perm (Fin n)}
    (hv : ∀ i, v i ∈ H) (hb : EBasis v) : EBasis (liftB v hv) where
  sq i := Subtype.ext (by simpa [liftB] using hb.sq i)
  comm i j := Subtype.ext (hb.comm i j).eq
  ne_one c hc := hb.ne_one c (by
    have h := congrArg Subtype.val hc
    rwa [coe_eElt_liftB] at h)

theorem eSub_liftB_map {H : Subgroup (Perm (Fin n))} {k : ℕ} {v : Fin k → Perm (Fin n)}
    (hv : ∀ i, v i ∈ H) (hb : EBasis v) : (eSub (liftB_basis hv hb)).map H.subtype = eSub hb := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := (mem_eSub_iff _ y).mp hy
    exact (mem_eSub_iff hb _).mpr ⟨c, (coe_eElt_liftB v hv c).symm⟩
  · intro hx
    obtain ⟨c, rfl⟩ := (mem_eSub_iff hb x).mp hx
    exact ⟨eElt (liftB v hv) c, eElt_mem _ c, coe_eElt_liftB v hv c⟩

theorem mem_eSub_liftB_iff {H : Subgroup (Perm (Fin n))} {k : ℕ} {v : Fin k → Perm (Fin n)}
    (hv : ∀ i, v i ∈ H) (hb : EBasis v) (x : H) :
    x ∈ eSub (liftB_basis hv hb) ↔ (x : Perm (Fin n)) ∈ eSub hb := by
  rw [← eSub_liftB_map hv hb]
  exact (Subgroup.mem_map_iff_mem (f := H.subtype) H.subtype_injective (x := x)).symm

theorem mem_centralizer_liftB_iff {H : Subgroup (Perm (Fin n))} {k : ℕ}
    {v : Fin k → Perm (Fin n)} (hv : ∀ i, v i ∈ H) (hb : EBasis v) (x : H) :
    x ∈ Subgroup.centralizer (eSub (liftB_basis hv hb) : Set H) ↔
      ∀ i, (x : Perm (Fin n)) * v i = v i * x := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h i
    have := h _ (mem_eSub (liftB_basis hv hb) i)
    exact (congrArg Subtype.val this).symm
  · intro h y hy
    rw [eSub_eq_closure] at hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact Subtype.ext (h i).symm
    | one => rw [one_mul, mul_one]
    | mul a b _ _ ha hb' => rw [mul_assoc, hb', ← mul_assoc, ha, mul_assoc]
    | inv a _ ha =>
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ha, mul_inv_cancel_right]

theorem mem_normalizer_liftB_iff {H : Subgroup (Perm (Fin n))} {k : ℕ}
    {v : Fin k → Perm (Fin n)} (hv : ∀ i, v i ∈ H) (hb : EBasis v) (x : H) :
    x ∈ Subgroup.normalizer (eSub (liftB_basis hv hb) : Set H) ↔
      (x : Perm (Fin n)) ∈ eNorm hb := by
  rw [Subgroup.mem_normalizer_iff, eNorm, Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    constructor
    · intro hy
      obtain ⟨c, rfl⟩ := (mem_eSub_iff hb y).mp hy
      have h1 := (h (eElt (liftB v hv) c)).mp (eElt_mem _ c)
      rw [mem_eSub_liftB_iff] at h1
      simpa [coe_eElt_liftB] using h1
    · intro hy
      have hyH : y ∈ H := by
        have : (x : Perm (Fin n)) * y * (x : Perm (Fin n))⁻¹ ∈ H := by
          obtain ⟨c, hc⟩ := (mem_eSub_iff hb _).mp hy
          rw [← hc]
          exact Subgroup.list_prod_mem _ fun z hz => by
            obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
            exact Subgroup.pow_mem _ (hv i) _
        have h2 := H.mul_mem (H.mul_mem (H.inv_mem x.2) this) x.2
        simpa [mul_assoc] using h2
      have h1 := (h ⟨y, hyH⟩).mpr (by rw [mem_eSub_liftB_iff]; simpa using hy)
      rw [mem_eSub_liftB_iff] at h1
      exact h1
  · intro h y
    rw [mem_eSub_liftB_iff, mem_eSub_liftB_iff]
    simpa using h (y : Perm (Fin n))



@[expose] noncomputable def permB (n : ℕ) (bs : List Table) : Fin bs.length → Perm (Fin n) :=
  fun i => tabPerm n bs[i]

theorem forall₂_permB {bs : List Table} (h : tabsOK n bs = true) :
    List.Forall₂ (Rep n) bs (List.ofFn (permB n bs)) := by
  rw [List.forall₂_iff_get]
  refine ⟨by simp, fun i h₁ h₂ => ?_⟩
  simp only [List.get_eq_getElem, List.getElem_ofFn, permB]
  unfold tabsOK at h
  rw [List.all_eq_true] at h
  exact rep_tabPerm (h _ (List.getElem_mem h₁))

theorem _root_.CFSG.SectionRank.QTK.Insp443.KConfig.bad_facts {K : Type} [Group K]
    {L V MK : Subgroup K} (h : KConfig K L V MK) {y t : K} (hy : y ∈ L) (ht : t ∈ V)
    (hyt : y * t * y⁻¹ ≠ t) :
    orderOf t = 2 ∧ ∀ j : ℕ, t * (y ^ j * t * y⁻¹ ^ j) = y ^ j * t * y⁻¹ ^ j * t := by
  refine ⟨orderOf_eq_prime ?_ fun h1 => hyt (by rw [h1, mul_one, mul_inv_cancel]), fun j => ?_⟩
  · exact h.elemAbelian.2 t ht
  · have hm : y ^ j * t * y⁻¹ ^ j ∈ V := by
      rw [inv_pow]
      exact (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ (h.le_normalizer hy) j) t).mp ht
    have := h.elemAbelian.1.is_comm.comm ⟨t, ht⟩ ⟨_, hm⟩
    simpa using congrArg Subtype.val this

@[expose] noncomputable def candPerms (n : ℕ) (cands : List (List Table)) :
    List (List (Perm (Fin n))) :=
  cands.map fun c => c.map (tabPerm n)

theorem forall₂_candPerms {cands : List (List Table)} (h : candsOK n cands = true) :
    List.Forall₂ (List.Forall₂ (Rep n)) cands (candPerms n cands) := by
  unfold candPerms
  rw [List.forall₂_map_right_iff]
  refine List.forall₂_same.2 fun c hc => ?_
  rw [List.forall₂_map_right_iff]
  refine List.forall₂_same.2 fun T hT => rep_tabPerm (R := invT n T) ?_
  unfold candsOK at h
  rw [List.all_eq_true] at h
  have := h c hc
  rw [List.all_eq_true] at this
  exact this T hT

theorem orbSub_mem_cands (hn : n < 2 ^ 32) {Q : RawSchreierDatum n} (hQ : ValidSchreier Q)
    {p : ℕ} (hp : 0 < p) {xT : Table} {x : Q.originalSubgroup}
    (hxT : Rep n xT (x : Perm (Fin n))) (hx : orderOf x = p) {cands : List (List Table)}
    (hok : candsOK n cands = true)
    (hchk : orbCheck n p (orderTables Q 2) (powTabs n xT p) cands = true)
    {y t : Q.originalSubgroup} (hyx : y ∈ Subgroup.zpowers x) (ht2 : orderOf t = 2)
    (hyt : y * t * y⁻¹ ≠ t)
    (hcomm : ∀ j : ℕ, t * (y ^ j * t * y⁻¹ ^ j) = y ^ j * t * y⁻¹ ^ j * t) :
    ∃ cg ∈ candPerms n cands,
      (orbSub y t).map Q.originalSubgroup.subtype = Subgroup.closure {g | g ∈ cg} := by
  obtain ⟨e, he, hey⟩ := exists_powTabs hn (H := Q.originalSubgroup) hxT hyx
  rw [hx] at he
  obtain ⟨T, hT, hTt⟩ := exists_orderTables hn Q hQ t.2 (by rw [Subgroup.orderOf_coe]; exact ht2)
  have hym : (y : Perm (Fin n)) ^ p = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hyx
    rw [← Subgroup.coe_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hx,
      pow_orderOf_eq_one, one_zpow, Subgroup.coe_one]
  have hmove : (y : Perm (Fin n)) * t * (y : Perm (Fin n))⁻¹ ≠ t := fun h' =>
    hyt (Subtype.ext (by simpa using h'))
  have hcomm' : ∀ j < p, (t : Perm (Fin n)) * ((y : Perm (Fin n)) ^ j * t *
      (y : Perm (Fin n))⁻¹ ^ j) = (y : Perm (Fin n)) ^ j * t * (y : Perm (Fin n))⁻¹ ^ j * t :=
    fun j _ => by simpa using congrArg Subtype.val (hcomm j)
  obtain ⟨cg, hcg, hcl⟩ := orbSub_eq_of_orbCheck hn hchk (forall₂_candPerms hok) he hT hey hTt
    hp hym hmove hcomm'
  exact ⟨cg, hcg, by rw [orbSub_map]; exact hcl⟩

end CFSG.SectionRank.QTK.Insp443.PermKit

end
