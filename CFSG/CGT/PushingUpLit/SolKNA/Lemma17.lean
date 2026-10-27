module

public import CFSG.RankThree.GF2n.Basic
public import CFSG.Timmesfeld.ARS.NaturalModule

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

set_option linter.unusedSectionVars false

open CFSG.Timmesfeld CFSG.Timmesfeld.RankOne CFSG.Timmesfeld.ARS.NaturalModule Matrix
open scoped MatrixGroups
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)
open CFSG.RankThree.GF2n (card_conjSubgroup conjSubgroup_eq_self_iff)

theorem commute_of_sq_mul' {G : Type*} [Group G] {a b : G} (h : (a * b) ^ 2 = a ^ 2 * b ^ 2) :
    a * b = b * a := by
  rw [sq, sq, sq] at h
  have h' : a * (b * a) * b = a * (a * b) * b := by simpa [mul_assoc] using h
  exact (mul_left_cancel (mul_right_cancel h')).symm

theorem sup_inf_centralizer_le {X : Type*} [Group X] {R : Subgroup X} {s : Finset (Subgroup X)}
    (hs : s.SupIndep id) (hn : ∀ W ∈ s, W.Normal) :
    s.sup id ⊓ Subgroup.centralizer (R : Set X) ≤
      s.sup (fun W => W ⊓ Subgroup.centralizer (R : Set X)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert W s' hW ih =>
    have hs' : s'.SupIndep id := hs.subset (Finset.subset_insert W s')
    have hn' : ∀ V ∈ s', V.Normal := fun V hV => hn V (Finset.mem_insert_of_mem hV)
    have hWn : W.Normal := hn W (Finset.mem_insert_self W s')
    have hdisj : Disjoint W (s'.sup id) :=
      hs (Finset.subset_insert W s') (Finset.mem_insert_self W s') hW
    have hsup : (s'.sup id).Normal := by
      refine Finset.sup_induction (p := fun U : Subgroup X => U.Normal) inferInstance
        (fun a ha b hb => by have := ha; have := hb; infer_instance) fun V hV => hn' V hV
    intro c hc
    rw [Finset.sup_insert, id] at hc
    obtain ⟨hcs, hcZ⟩ := Subgroup.mem_inf.mp hc
    obtain ⟨w, hw, c', hc', rfl⟩ := CFSG.RankThree.GF2n.exists_mul_of_mem_sup
      (by rw [Subgroup.normalizer_eq_top]; exact le_top) hcs
    have key : ∀ r ∈ R, r * w = w * r ∧ r * c' = c' * r := by
      intro r hr
      have h1 : r * (w * c') = (w * c') * r := Subgroup.mem_centralizer_iff.mp hcZ r hr
      have h2 : r * w * r⁻¹ ∈ W := hWn.conj_mem w hw r
      have h3 : r * c' * r⁻¹ ∈ s'.sup id := hsup.conj_mem c' hc' r
      have h4 : w⁻¹ * (r * w * r⁻¹) = c' * (r * c' * r⁻¹)⁻¹ := by
        have e : (r * w * r⁻¹) * (r * c' * r⁻¹) = w * c' := by
          calc (r * w * r⁻¹) * (r * c' * r⁻¹) = r * (w * c') * r⁻¹ := by group
            _ = w * c' := by rw [h1]; group
        calc w⁻¹ * (r * w * r⁻¹) = w⁻¹ * (r * w * r⁻¹) * (r * c' * r⁻¹) * (r * c' * r⁻¹)⁻¹ := by
              group
          _ = c' * (r * c' * r⁻¹)⁻¹ := by rw [mul_assoc w⁻¹, e]; group
      have h5 : w⁻¹ * (r * w * r⁻¹) ∈ W ⊓ s'.sup id :=
        Subgroup.mem_inf.mpr ⟨W.mul_mem (W.inv_mem hw) h2,
          h4 ▸ (s'.sup id).mul_mem hc' ((s'.sup id).inv_mem h3)⟩
      rw [disjoint_iff.mp hdisj, Subgroup.mem_bot] at h5
      have h6 : r * w * r⁻¹ = w := by
        have := congrArg (w * ·) h5
        simpa using this
      have h7 : r * c' * r⁻¹ = c' := by
        have h8 : c' * (r * c' * r⁻¹)⁻¹ = 1 := by rw [← h4, h5]
        have := mul_inv_eq_one.mp h8
        exact this.symm
      refine ⟨?_, ?_⟩
      · calc r * w = r * w * r⁻¹ * r := by group
          _ = w * r := by rw [h6]
      · calc r * c' = r * c' * r⁻¹ * r := by group
          _ = c' * r := by rw [h7]
    have hwZ : w ∈ Subgroup.centralizer (R : Set X) :=
      Subgroup.mem_centralizer_iff.mpr fun r hr => (key r hr).1
    have hc'Z : c' ∈ Subgroup.centralizer (R : Set X) :=
      Subgroup.mem_centralizer_iff.mpr fun r hr => (key r hr).2
    rw [Finset.sup_insert]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hw, hwZ⟩))
      (Subgroup.mem_sup_right ?_)
    exact ih hs' hn' (Subgroup.mem_inf.mpr ⟨hc', hc'Z⟩)


variable {X : Type} [Group X] [Finite X] {F : Type} [Field F] [Finite F] [CharP F 2]

structure Lemma17Psl (ψ : X →* SL(2, F)) (N R : Subgroup X) : Prop where
  normal : N.Normal
  surj : Function.Surjective ψ
  ker : ψ.ker = N
  img : R.map ψ = upperUnipotent F
  sq_N : ∀ n ∈ N, n * n = 1
  cent : ∀ n, n ∈ R ⊓ N ↔ n ∈ N ∧ ∀ r ∈ R, r * n = n * r
  norm : ∀ x : X, x ∈ Subgroup.normalizer ((R ⊓ N : Subgroup X) : Set X) →
    x ∈ Subgroup.normalizer (R : Set X)
  dec : ∃ s : Finset (Subgroup X), s.SupIndep id ∧ s.sup id = N ∧
    ∀ W ∈ s, W.Normal ∧ ∃ θ : (Fin 2 → F) → X, (∀ v v', θ (v + v') = θ v * θ v') ∧
      Function.Injective θ ∧ Set.range θ = W ∧ ∀ (x : X) (v : Fin 2 → F),
        θ ((ψ x : Matrix (Fin 2) (Fin 2) F) *ᵥ v) = x * θ v * x⁻¹

namespace Lemma17Psl

variable {ψ : X →* SL(2, F)} {N R : Subgroup X} (D : Lemma17Psl ψ N R)
include D

theorem mem_ker_iff (x : X) : ψ x = 1 ↔ x ∈ N := by
  rw [← D.ker, MonoidHom.mem_ker]

theorem exists_upper {a : X} (ha : a ∈ R) : ∃ s : F, ψ a = upperElt F s := by
  have : ψ a ∈ upperUnipotent F := by
    rw [← D.img]
    exact ⟨a, ha, rfl⟩
  exact (mem_upperUnipotent_iff F).mp this

theorem exists_mem_of_upper (s : F) : ∃ a ∈ R, ψ a = upperElt F s := by
  have : upperElt F s ∈ R.map ψ := by
    rw [D.img]
    exact (mem_upperUnipotent_iff F).mpr ⟨s, rfl⟩
  obtain ⟨a, ha, h⟩ := this
  exact ⟨a, ha, h⟩

theorem inv_mul_mem {a b : X} (ha : a ∈ R) (hb : b ∈ R) (h : ψ a = ψ b) :
    a⁻¹ * b ∈ R ⊓ N := by
  refine Subgroup.mem_inf.mpr ⟨R.mul_mem (R.inv_mem ha) hb, ?_⟩
  rw [← D.mem_ker_iff, map_mul, map_inv, h, inv_mul_cancel]

theorem cent_of_mem {l : X} (hl : l ∈ R ⊓ N) {r : X} (hr : r ∈ R) : r * l = l * r :=
  ((D.cent l).mp hl).2 r hr

theorem commute_of_eq {a b : X} (ha : a ∈ R) (hb : b ∈ R) (h : ψ a = ψ b) : a * b = b * a := by
  have hl := D.inv_mul_mem ha hb h
  have := D.cent_of_mem hl ha
  calc a * b = a * (a * (a⁻¹ * b)) := by group
    _ = a * ((a⁻¹ * b) * a) := by rw [this]
    _ = b * a := by group

theorem sq_eq {a b : X} (ha : a ∈ R) (hb : b ∈ R) (h : ψ a = ψ b) : a * a = b * b := by
  have hl := D.inv_mul_mem ha hb h
  have hc := D.cent_of_mem hl ha
  have hsq : (a⁻¹ * b) * (a⁻¹ * b) = 1 := D.sq_N _ (Subgroup.mem_inf.mp hl).2
  calc a * a = a * a * ((a⁻¹ * b) * (a⁻¹ * b)) := by rw [hsq, mul_one]
    _ = a * (a * (a⁻¹ * b)) * (a⁻¹ * b) := by group
    _ = a * ((a⁻¹ * b) * a) * (a⁻¹ * b) := by rw [hc]
    _ = b * b := by group


theorem comm_N {u v : X} (hu : u ∈ N) (hv : v ∈ N) : u * v = v * u := by
  have huv := D.sq_N (u * v) (N.mul_mem hu hv)
  have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right (D.sq_N u hu)
  have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right (D.sq_N v hv)
  calc u * v = (u * v)⁻¹ := (inv_eq_of_mul_eq_one_right huv).symm
    _ = v⁻¹ * u⁻¹ := mul_inv_rev u v
    _ = v * u := by rw [hu', hv']

theorem psi_conj_upper {c : Fˣ} {x : X} (hx : ψ x = diagElt c) {r : X} {t : F}
    (hr : ψ r = upperElt F t) : ψ (x * r * x⁻¹) = upperElt F ((c : F) ^ 2 * t) := by
  rw [map_mul, map_mul, map_inv, hx, hr, diagElt_mul_upperElt, mul_inv_cancel_right]

theorem conj_decomp {c : Fˣ} {x : X} (hx : ψ x = diagElt c) {r : X} (hr : r ∈ R) :
    ∃ r' ∈ R, ∃ n ∈ N, x * r * x⁻¹ = r' * n := by
  obtain ⟨t, ht⟩ := D.exists_upper hr
  obtain ⟨r', hr', hψr'⟩ := D.exists_mem_of_upper ((c : F) ^ 2 * t)
  refine ⟨r', hr', r'⁻¹ * (x * r * x⁻¹), ?_, by group⟩
  rw [← D.mem_ker_iff, map_mul, map_inv, hψr', D.psi_conj_upper hx ht, inv_mul_cancel]

theorem conj_mem_L {c : Fˣ} {x : X} (hx : ψ x = diagElt c) {l : X} (hl : l ∈ R ⊓ N) :
    x * l * x⁻¹ ∈ R ⊓ N := by
  obtain ⟨hlR, hlN⟩ := Subgroup.mem_inf.mp hl
  have hxN : x * l * x⁻¹ ∈ N := D.normal.conj_mem l hlN x
  have hx' : ψ x⁻¹ = diagElt c⁻¹ := by rw [map_inv, hx, diagElt_inv]
  refine (D.cent _).mpr ⟨hxN, fun r hr => ?_⟩
  obtain ⟨r', hr', n, hn, hrn⟩ := D.conj_decomp hx' hr
  rw [inv_inv] at hrn
  have e1 : r * (x * l * x⁻¹) = x * ((r' * n) * l) * x⁻¹ := by
    calc r * (x * l * x⁻¹) = x * (x⁻¹ * r * x) * l * x⁻¹ := by group
      _ = x * ((r' * n) * l) * x⁻¹ := by rw [hrn]; group
  have e2 : (x * l * x⁻¹) * r = x * (l * (r' * n)) * x⁻¹ := by
    calc (x * l * x⁻¹) * r = x * l * (x⁻¹ * r * x) * x⁻¹ := by group
      _ = x * (l * (r' * n)) * x⁻¹ := by rw [hrn]; group
  rw [e1, e2]
  congr 2
  calc r' * n * l = r' * (n * l) := by group
    _ = r' * (l * n) := by rw [D.comm_N hn hlN]
    _ = (r' * l) * n := by group
    _ = (l * r') * n := by rw [D.cent_of_mem hl hr']
    _ = l * (r' * n) := by group

theorem mem_normalizer_R {c : Fˣ} {x : X} (hx : ψ x = diagElt c) :
    x ∈ Subgroup.normalizer (R : Set X) := by
  have hle : conjSubgroup x (R ⊓ N) ≤ R ⊓ N := fun y hy => by
    have h1 := D.conj_mem_L hx (mem_conjSubgroup.mp hy)
    rwa [show x * (x⁻¹ * y * x) * x⁻¹ = y by group] at h1
  have heq : conjSubgroup x (R ⊓ N) = R ⊓ N :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup])
  exact D.norm x (conjSubgroup_eq_self_iff.mp heq)

theorem sq_formula {a₁ : X} (ha₁ : a₁ ∈ R) (ha₁ψ : ψ a₁ = upperElt F 1) {a : X} (ha : a ∈ R)
    {s : F} (hs : ψ a = upperElt F s) {c : Fˣ} (hc : (c : F) ^ 2 = s) {x : X}
    (hx : ψ x = diagElt c) : a * a = x * (a₁ * a₁) * x⁻¹ := by
  have h1 : x * a₁ * x⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (D.mem_normalizer_R hx) a₁).mp ha₁
  have h2 : ψ (x * a₁ * x⁻¹) = ψ a := by
    rw [D.psi_conj_upper hx ha₁ψ, hs, mul_one, hc]
  rw [D.sq_eq ha h1 h2.symm]
  group


theorem conj_theta {θ : (Fin 2 → F) → X}
    (hθ : ∀ (x : X) (v : Fin 2 → F),
      θ ((ψ x : Matrix (Fin 2) (Fin 2) F) *ᵥ v) = x * θ v * x⁻¹)
    {c : Fˣ} {x : X} (hx : ψ x = diagElt c) {v : Fin 2 → F} (hv : v 1 = 0) :
    x * θ v * x⁻¹ = θ ![(c : F) * v 0, 0] := by
  rw [← hθ, hx, diagElt_mulVec, hv, mul_zero]

theorem conj_add {c : X} (hc : c ∈ R ⊓ N) {l l' : Fˣ} (hμ : (l : F) + l' ≠ 0) {x y z : X}
    (hx : ψ x = diagElt l) (hy : ψ y = diagElt l')
    (hz : ψ z = diagElt (Units.mk0 ((l : F) + l') hμ)) :
    z * c * z⁻¹ = (x * c * x⁻¹) * (y * c * y⁻¹) := by
  obtain ⟨s, hs, hsN, hW⟩ := D.dec
  let G₀ : Subgroup X :=
    { carrier := {c | c ∈ R ⊓ N ∧ z * c * z⁻¹ = (x * c * x⁻¹) * (y * c * y⁻¹)}
      one_mem' := ⟨(R ⊓ N).one_mem, by group⟩
      mul_mem' := fun {c c'} hc hc' => by
        obtain ⟨hcN, hc1⟩ := hc
        obtain ⟨hc'N, hc'1⟩ := hc'
        refine ⟨(R ⊓ N).mul_mem hcN hc'N, ?_⟩
        have hxc := D.normal.conj_mem c (Subgroup.mem_inf.mp hcN).2
        have hyc := D.normal.conj_mem c (Subgroup.mem_inf.mp hcN).2
        have hxc' := D.normal.conj_mem c' (Subgroup.mem_inf.mp hc'N).2
        have hyc' := D.normal.conj_mem c' (Subgroup.mem_inf.mp hc'N).2
        have hcomm := D.comm_N (hyc y) (hxc' x)
        calc z * (c * c') * z⁻¹ = (z * c * z⁻¹) * (z * c' * z⁻¹) := by group
          _ = ((x * c * x⁻¹) * (y * c * y⁻¹)) * ((x * c' * x⁻¹) * (y * c' * y⁻¹)) := by
              rw [hc1, hc'1]
          _ = (x * c * x⁻¹) * ((y * c * y⁻¹) * (x * c' * x⁻¹)) * (y * c' * y⁻¹) := by group
          _ = (x * c * x⁻¹) * ((x * c' * x⁻¹) * (y * c * y⁻¹)) * (y * c' * y⁻¹) := by
              rw [hcomm]
          _ = (x * (c * c') * x⁻¹) * (y * (c * c') * y⁻¹) := by group
      inv_mem' := fun {c} hc => by
        obtain ⟨hcN, hc1⟩ := hc
        refine ⟨(R ⊓ N).inv_mem hcN, ?_⟩
        have hxc := D.normal.conj_mem c (Subgroup.mem_inf.mp hcN).2 x
        have hyc := D.normal.conj_mem c (Subgroup.mem_inf.mp hcN).2 y
        have hcomm := D.comm_N hxc hyc
        calc z * c⁻¹ * z⁻¹ = (z * c * z⁻¹)⁻¹ := by group
          _ = ((x * c * x⁻¹) * (y * c * y⁻¹))⁻¹ := by rw [hc1]
          _ = (y * c * y⁻¹)⁻¹ * (x * c * x⁻¹)⁻¹ := _root_.mul_inv_rev _ _
          _ = (x * c * x⁻¹)⁻¹ * (y * c * y⁻¹)⁻¹ := by
              rw [← _root_.mul_inv_rev, ← _root_.mul_inv_rev, hcomm]
          _ = (x * c⁻¹ * x⁻¹) * (y * c⁻¹ * y⁻¹) := by group }
  have hWG : ∀ W ∈ s, W ⊓ Subgroup.centralizer (R : Set X) ≤ G₀ := by
    intro W hWs d hd
    obtain ⟨hdW, hdZ⟩ := Subgroup.mem_inf.mp hd
    obtain ⟨hWn, θ, hθadd, hθinj, hθr, hθ⟩ := hW W hWs
    have hdN : d ∈ N := hsN ▸ (Finset.le_sup (f := id) hWs) hdW
    have hdR : d ∈ R ⊓ N := (D.cent d).mpr ⟨hdN, fun r hr =>
      Subgroup.mem_centralizer_iff.mp hdZ r hr⟩
    obtain ⟨v, rfl⟩ : d ∈ Set.range θ := hθr ▸ hdW
    have hv1 : v 1 = 0 := by
      refine (forall_upperElt_mulVec_eq_iff v).mp fun t => ?_
      obtain ⟨r, hr, hrt⟩ := D.exists_mem_of_upper t
      have h1 : r * θ v = θ v * r := Subgroup.mem_centralizer_iff.mp hdZ r hr
      have h2 : θ ((ψ r : Matrix (Fin 2) (Fin 2) F) *ᵥ v) = θ v := by
        rw [hθ, h1]
        group
      rw [← hrt]
      exact hθinj h2
    refine ⟨hdR, ?_⟩
    rw [D.conj_theta hθ hx hv1, D.conj_theta hθ hy hv1, D.conj_theta hθ hz hv1, ← hθadd]
    congr 1
    ext i
    fin_cases i <;> simp [add_mul]
  have hle : R ⊓ N ≤ G₀ := by
    intro d hd
    have hdZ : d ∈ Subgroup.centralizer (R : Set X) :=
      Subgroup.mem_centralizer_iff.mpr fun r hr => D.cent_of_mem hd hr
    have h1 := sup_inf_centralizer_le (R := R) hs (fun V hV => (hW V hV).1)
      (Subgroup.mem_inf.mpr ⟨hsN ▸ (Subgroup.mem_inf.mp hd).2, hdZ⟩)
    exact (Finset.sup_le hWG) h1
  exact (hle hc).2


theorem abelian : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
  intro a ha b hb
  obtain ⟨s, hs⟩ := D.exists_upper ha
  obtain ⟨t, ht⟩ := D.exists_upper hb
  by_cases hst : s = t
  · exact D.commute_of_eq ha hb (by rw [hs, ht, hst])
  by_cases hs0 : s = 0
  · have : a ∈ N := (D.mem_ker_iff a).mp (by rw [hs, hs0, upperElt_zero])
    exact (D.cent_of_mem (Subgroup.mem_inf.mpr ⟨ha, this⟩) hb).symm
  by_cases ht0 : t = 0
  · have : b ∈ N := (D.mem_ker_iff b).mp (by rw [ht, ht0, upperElt_zero])
    exact D.cent_of_mem (Subgroup.mem_inf.mpr ⟨hb, this⟩) ha
  have hst0 : s + t ≠ 0 := fun h => hst (by
    rw [eq_neg_of_add_eq_zero_left h, CharTwo.neg_eq])
  have hsq : ∀ u : F, ((frobeniusEquiv F 2).symm u) ^ 2 = u := fun u => by
    have := (frobeniusEquiv F 2).apply_symm_apply u
    rwa [frobeniusEquiv_apply] at this
  have hsqadd : ∀ u v : F, (frobeniusEquiv F 2).symm (u + v) =
      (frobeniusEquiv F 2).symm u + (frobeniusEquiv F 2).symm v := fun u v => map_add _ _ _
  have hne : ∀ u : F, u ≠ 0 → (frobeniusEquiv F 2).symm u ≠ 0 := fun u hu h => hu (by
    rw [← hsq u, h]
    ring)
  let l : Fˣ := Units.mk0 ((frobeniusEquiv F 2).symm s) (hne s hs0)
  let l' : Fˣ := Units.mk0 ((frobeniusEquiv F 2).symm t) (hne t ht0)
  have hμe : (l : F) + l' = (frobeniusEquiv F 2).symm (s + t) := by
    simp only [l, l', Units.val_mk0]
    rw [hsqadd]
  have hμ : (l : F) + l' ≠ 0 := by
    rw [hμe]
    exact hne _ hst0
  obtain ⟨x, hx⟩ := D.surj (diagElt l)
  obtain ⟨y, hy⟩ := D.surj (diagElt l')
  obtain ⟨z, hz⟩ := D.surj (diagElt (Units.mk0 ((l : F) + l') hμ))
  obtain ⟨a₁, ha₁, ha₁ψ⟩ := D.exists_mem_of_upper 1
  have hc₀ : a₁ * a₁ ∈ R ⊓ N := by
    refine Subgroup.mem_inf.mpr ⟨R.mul_mem ha₁ ha₁, ?_⟩
    rw [← D.mem_ker_iff, map_mul, ha₁ψ, upperElt_mul, CharTwo.add_self_eq_zero, upperElt_zero]
  have hab : a * b ∈ R := R.mul_mem ha hb
  have habψ : ψ (a * b) = upperElt F (s + t) := by rw [map_mul, hs, ht, upperElt_mul]
  have ea : a * a = x * (a₁ * a₁) * x⁻¹ :=
    D.sq_formula ha₁ ha₁ψ ha hs (by simp only [l, Units.val_mk0]; exact hsq s) hx
  have eb : b * b = y * (a₁ * a₁) * y⁻¹ :=
    D.sq_formula ha₁ ha₁ψ hb ht (by simp only [l', Units.val_mk0]; exact hsq t) hy
  have eab : (a * b) * (a * b) = z * (a₁ * a₁) * z⁻¹ :=
    D.sq_formula ha₁ ha₁ψ hab habψ (c := Units.mk0 ((l : F) + l') hμ)
      (by simp only [Units.val_mk0]; rw [hμe]; exact hsq _) hz
  have hadd := D.conj_add hc₀ hμ hx hy hz
  apply commute_of_sq_mul'
  rw [sq, sq, sq, eab, hadd, ea, eb]

end Lemma17Psl

end CFSG.CGT.PushingUpLit.SolKNA
