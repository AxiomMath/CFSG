module

public import Certificates.Data.CFSGNative.Insp443.L52Tests
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.PermFano
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.PermSix

public section

namespace CFSG.SectionRank.QTK.Insp443.PermKit

open Equiv CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Native
  CFSG.SectionRank.QTK.Insp443.PermKit.Native

variable {n : ℕ}

theorem rep_eq {T : Table} {g h : Perm (Fin n)} (hg : Rep n T g) (hh : Rep n T h) : g = h :=
  (tblEq_iff_eq hg hh).mp ((tblEq_iff_eq hg hg).mpr rfl)

theorem eSub_congr {G : Type*} [Group G] {k : ℕ} {v v' : Fin k → G} (hv : EBasis v)
    (hv' : EBasis v') (h : v = v') : eSub hv = eSub hv' := by
  subst h
  rfl

theorem forall₂_liftB {H : Subgroup (Perm (Fin n))} {k : ℕ} {v : Fin k → Perm (Fin n)}
    (hvH : ∀ i, v i ∈ H) {bs : List Table} (h : List.Forall₂ (Rep n) bs (List.ofFn v)) :
    List.Forall₂ (Rep n) bs (List.ofFn fun i => ((liftB v hvH i : H) : Perm (Fin n))) := by
  rw [show (fun i => ((liftB v hvH i : H) : Perm (Fin n))) = v from
    funext fun i => coe_liftB _ hvH i]
  exact h

theorem map_conj_liftB {H : Subgroup (Perm (Fin n))} {k : ℕ} {v w : Fin k → Perm (Fin n)}
    (hvH : ∀ i, v i ∈ H) (hv : EBasis v) (hwH : ∀ i, w i ∈ H) (hw : EBasis w) (g : H)
    (h : ConjInto (g : Perm (Fin n)) v w) :
    (eSub (liftB_basis hvH hv)).map (MulAut.conj g).toMonoidHom = eSub (liftB_basis hwH hw) := by
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_map, eSub_liftB_map hwH hw]
  have hc : H.subtype.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (g : Perm (Fin n))).toMonoidHom.comp H.subtype := by
    ext x
    simp [MulAut.conj_apply]
  rw [hc, ← Subgroup.map_map, eSub_liftB_map hvH hv]
  exact map_conj_eq_of_conjInto hv hw rfl h

variable (hn : n < 2 ^ 32) (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)

include hn hQ in
theorem card_eNorm_liftB {k : ℕ} {v : Fin k → Perm (Fin n)} (hvH : ∀ i, v i ∈ Q.originalSubgroup)
    (hv : EBasis v) {bs : List Table} (hbs : List.Forall₂ (Rep n) bs (List.ofFn v)) :
    Nat.card (eNorm (liftB_basis hvH hv)) =
      countProducts n (conjIn n bs (spanTabs n bs)) (levelTables Q) (idT n) := by
  classical
  have hf : ∀ T g, Rep n T g → (conjIn n bs (spanTabs n bs) T = true ↔ g ∈ eNorm hv) :=
    fun T g hT => normAll_iff hn hv hbs hT
  rw [← card_subtype_eq_countProducts hn Q hQ hf]
  exact Nat.card_congr ⟨fun x => ⟨x, (mem_normalizer_liftB_iff hvH hv x).mp x.2⟩,
    fun x => ⟨x, (mem_normalizer_liftB_iff hvH hv x).mpr x.2⟩, fun _ => rfl, fun _ => rfl⟩

variable {tests : List (Table → Bool)}
  (hcnt : countProducts n (anyTest tests) (levelTables Q) (idT n) = 0)
include hn hQ hcnt

theorem cent_of_scan {k l : ℕ} {u : Fin k → Perm (Fin n)} {w : Fin l → Perm (Fin n)}
    (hw : EBasis w) {us ws : List Table} (hus : List.Forall₂ (Rep n) us (List.ofFn u))
    (hws : List.Forall₂ (Rep n) ws (List.ofFn w)) (ht : centTestS n us (spanTabs n ws) ∈ tests)
    (x : Q.originalSubgroup) (hx : ∀ i, (x : Perm (Fin n)) * u i = u i * x) :
    (x : Perm (Fin n)) ∈ eSub hw := by
  by_contra hxw
  exact forall_of_tests_count' hn Q hQ hcnt ht
    (P := fun g => (∀ i, g * u i = u i * g) ∧ g ∉ eSub hw)
    (fun T g hT hP => (centTest_iff hn hw hus hws hT).mpr hP) x ⟨hx, hxw⟩

theorem cn_of_scan {k k' l : ℕ} {u : Fin k → Perm (Fin n)} {v : Fin k' → Perm (Fin n)}
    {w : Fin l → Perm (Fin n)} (hv : EBasis v) (hw : EBasis w) {us vs ws : List Table}
    (hus : List.Forall₂ (Rep n) us (List.ofFn u)) (hvs : List.Forall₂ (Rep n) vs (List.ofFn v))
    (hws : List.Forall₂ (Rep n) ws (List.ofFn w))
    (ht : cnTestS n us vs (spanTabs n vs) (spanTabs n ws) ∈ tests) (x : Q.originalSubgroup)
    (hx : ∀ i, (x : Perm (Fin n)) * u i = u i * x) (hxv : (x : Perm (Fin n)) ∈ eNorm hv) :
    (x : Perm (Fin n)) ∈ eSub hw := by
  by_contra hxw
  refine forall_of_tests_count' hn Q hQ hcnt ht
    (P := fun g => (∀ i, g * u i = u i * g) ∧ g ∈ eNorm hv ∧ g ∉ eSub hw) ?_ x ⟨hx, hxv, hxw⟩
  rintro T g hT ⟨hgu, hgv, hgw⟩
  have h1 : conjIn n vs (spanTabs n vs) T = true := by
    have hnorm : conjIn n vs (spanTabs n vs) T = normAll n vs T := rfl
    rw [hnorm]
    exact (normAll_iff hn hv hvs hT).mpr hgv
  have h2 : inSp n (spanTabs n ws) T = false := by
    rw [inSp_spanTabs, ← Bool.not_eq_true, inSpanT_iff_mem hn hw hws hT]
    exact hgw
  show (commAllT n us T && conjIn n vs (spanTabs n vs) T && !(inSp n (spanTabs n ws) T)) = true
  rw [(commAllT_iff hus hT).mpr hgu, h1, h2]
  rfl

theorem pow_of_scan {k : ℕ} {u : Fin k → Perm (Fin n)} {us : List Table}
    (hus : List.Forall₂ (Rep n) us (List.ofFn u)) {e : ℕ} (ht : c2TestS n us e ∈ tests)
    (x : Q.originalSubgroup) (hx : ∀ i, (x : Perm (Fin n)) * u i = u i * x) :
    (x : Perm (Fin n)) ^ e = 1 := by
  by_contra hxe
  refine forall_of_tests_count' hn Q hQ hcnt ht
    (P := fun g => (∀ i, g * u i = u i * g) ∧ g ^ e ≠ 1) ?_ x ⟨hx, hxe⟩
  rintro T g hT ⟨hgu, hge⟩
  have h1 : powFixW n [T] e = false := by
    rw [← Bool.not_eq_true, powFixW_iff perm_faithful (List.Forall₂.cons hT List.Forall₂.nil) e,
      List.prod_singleton]
    exact hge
  show (commAllT n us T && !(powFixW n [T] e)) = true
  rw [(commAllT_iff hus hT).mpr hgu, h1]
  rfl

theorem s_of_scan {k l m : ℕ} {u : Fin k → Perm (Fin n)} {z : Fin l → Perm (Fin n)}
    {w : Fin m → Perm (Fin n)} (hz : EBasis z) (hw : EBasis w) {us zs ws : List Table}
    (hus : List.Forall₂ (Rep n) us (List.ofFn u)) (hzs : List.Forall₂ (Rep n) zs (List.ofFn z))
    (hws : List.Forall₂ (Rep n) ws (List.ofFn w)) {cs : List (Table × Table)}
    {P : Perm (Fin n) → Prop} (hcs : ∀ ab ∈ cs, ∃ c, P c ∧ Rep n ab.1 c ∧ Rep n ab.2 c⁻¹)
    (ht : sTestS n us (spanTabs n zs) (spanTabs n ws) cs ∈ tests) (x : Q.originalSubgroup)
    (hx : ∀ i, (x : Perm (Fin n)) * u i = u i * x)
    (hxc : ∀ c, P c → (x : Perm (Fin n)) * (c * x * c⁻¹) = c * x * c⁻¹ * x) :
    (x : Perm (Fin n)) ∈ eSub hz ∨ (x : Perm (Fin n)) ∈ eSub hw := by
  by_contra hne
  rw [not_or] at hne
  refine forall_of_tests_count' hn Q hQ hcnt ht
    (P := fun g => (∀ i, g * u i = u i * g) ∧ g ∉ eSub hz ∧ g ∉ eSub hw ∧
      ∀ c, P c → g * (c * g * c⁻¹) = c * g * c⁻¹ * g) ?_ x ⟨hx, hne.1, hne.2, hxc⟩
  rintro T g hT ⟨hgu, hgz, hgw, hgc⟩
  have h1 : inSp n (spanTabs n zs) T = false := by
    rw [inSp_spanTabs, ← Bool.not_eq_true, inSpanT_iff_mem hn hz hzs hT]
    exact hgz
  have h2 : inSp n (spanTabs n ws) T = false := by
    rw [inSp_spanTabs, ← Bool.not_eq_true, inSpanT_iff_mem hn hw hws hT]
    exact hgw
  have h3 : (cs.all fun ab => commT2 n T (compT n (compT n ab.1 T) ab.2)) = true := by
    rw [List.all_eq_true]
    intro ab hab
    obtain ⟨c, hc, h1c, h2c⟩ := hcs ab hab
    exact (commT2_iff hT (Rep.compT (Rep.compT h1c hT) h2c)).mpr (hgc c hc)
  show (commAllT n us T && !(inSp n (spanTabs n zs) T) && !(inSp n (spanTabs n ws) T) &&
    cs.all fun ab => commT2 n T (compT n (compT n ab.1 T) ab.2)) = true
  rw [(commAllT_iff hus hT).mpr hgu, h1, h2, h3]
  rfl

theorem perm3_of_scan {l k : ℕ} {w : Fin l → Perm (Fin n)} (hw : EBasis w) {ws : List Table}
    (hws : List.Forall₂ (Rep n) ws (List.ofFn w)) {a : Fin 3 → Fin k → Perm (Fin n)}
    {as : List (List Table)} (has : ∀ i : Fin 3, List.Forall₂ (Rep n) (as.getD i []) (List.ofFn (a i)))
    (ht : perm3TestS n ws (spanTabs n ws) as (as.map (spanTabs n)) ∈ tests)
    (hal : as.length = 3) (x : Q.originalSubgroup) (hxw : (x : Perm (Fin n)) ∈ eNorm hw) :
    ∀ i : Fin 3, ∃ j : Fin 3, ConjInto (x : Perm (Fin n)) (a i) (a j) := by
  by_contra hne
  push Not at hne
  refine forall_of_tests_count' hn Q hQ hcnt ht
    (P := fun g => g ∈ eNorm hw ∧ ∃ i : Fin 3, ∀ j : Fin 3, ¬ ConjInto g (a i) (a j)) ?_ x
    ⟨hxw, hne⟩
  rintro T g hT ⟨hgw, i, hi⟩
  have h1 : conjIn n ws (spanTabs n ws) T = true := by
    have hnorm : conjIn n ws (spanTabs n ws) T = normAll n ws T := rfl
    rw [hnorm]
    exact (normAll_iff hn hw hws hT).mpr hgw
  have h2 : ((List.range 3).all fun i => (List.range 3).any fun j =>
      conjIn n (as.getD i []) ((as.map (spanTabs n)).getD j []) T) = false := by
    rw [← Bool.not_eq_true, List.all_eq_true]
    intro hall
    have h3 := hall i (List.mem_range.mpr i.2)
    rw [List.any_eq_true] at h3
    obtain ⟨j, hj, hjT⟩ := h3
    have hj3 : j < 3 := List.mem_range.mp hj
    have hspan : (as.map (spanTabs n)).getD j [] = spanTabs n (as.getD j []) := by
      rw [List.getD_eq_getElem _ _ (by rw [List.length_map, hal]; exact hj3),
        List.getD_eq_getElem _ _ (by rw [hal]; exact hj3), List.getElem_map]
    rw [hspan, conjIn_spanTabs, conjSpanIn_iff hn (has i) (has ⟨j, hj3⟩) hT] at hjT
    exact hi ⟨j, hj3⟩ hjT
  show (conjIn n ws (spanTabs n ws) T && !((List.range 3).all fun i => (List.range 3).any fun j =>
    conjIn n (as.getD i []) ((as.map (spanTabs n)).getD j []) T)) = true
  rw [h1, h2]
  rfl

end CFSG.SectionRank.QTK.Insp443.PermKit

end
