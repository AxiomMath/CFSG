module

public import CFSG.LocalAnalysis.GLTheoremA.S6.Prop65Aux
public import CFSG.LocalAnalysis.GLTheoremA.S12.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

section Step

variable {G : Type} [Group G] [Finite G]

theorem s265_inf_zpowers_bot {p : ℕ} (hp : p.Prime) {A : Subgroup G} {e : G}
    (hord : Nat.card (Subgroup.zpowers e) = p) (heA : e ∉ A) : A ⊓ Subgroup.zpowers e = ⊥ := by
  by_contra hne'
  have hdvd : Nat.card ↥(A ⊓ Subgroup.zpowers e) ∣ Nat.card ↥(Subgroup.zpowers e) :=
    Subgroup.card_dvd_of_le inf_le_right
  rw [hord] at hdvd
  rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
  · exact hne' (Subgroup.card_eq_one.1 h1)
  · have heq : A ⊓ Subgroup.zpowers e = Subgroup.zpowers e :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (le_of_eq (by rw [hord, h1]))
    have heA' : e ∈ A ⊓ Subgroup.zpowers e := by
      rw [heq]
      exact Subgroup.mem_zpowers e
    exact heA heA'.1

theorem s265_zpowers_le_normalizer {p : ℕ} {B A : Subgroup G} (hB : IsElemAbelian p B)
    (hAB : A ≤ B) {e : G} (heB : e ∈ B) :
    Subgroup.zpowers e ≤ Subgroup.normalizer (A : Set G) := by
  have hcomm : ∀ g ∈ B, ∀ d ∈ B, g * d = d * g := fun g hg d hd =>
    congrArg Subtype.val (hB.1.is_comm.comm (⟨g, hg⟩ : B) ⟨d, hd⟩)
  have hconj : ∀ h ∈ B, e * h * e⁻¹ = h := fun h hh => by
    rw [hcomm e heB h hh, mul_inv_cancel_right]
  rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [hconj h (hAB hh)]
    exact hh
  · intro hh
    have hB' : e * h * e⁻¹ ∈ B := hAB hh
    have hhB : h ∈ B := by
      have hh' : h = e⁻¹ * (e * h * e⁻¹) * e := by group
      rw [hh']
      exact B.mul_mem (B.mul_mem (B.inv_mem heB) hB') heB
    rw [hconj h hhB] at hh
    exact hh

theorem s265_card_sup {p n : ℕ} (hp : p.Prime) {B A : Subgroup G} (hB : IsElemAbelian p B)
    (hAB : A ≤ B) (hA : Nat.card A = p ^ n) {e : G} (heB : e ∈ B) (heA : e ∉ A)
    (hord : Nat.card (Subgroup.zpowers e) = p) :
    Nat.card ↥(A ⊔ Subgroup.zpowers e) = p ^ (n + 1) := by
  have hcardprod : Nat.card ↥(A ⊔ Subgroup.zpowers e) * Nat.card ↥(A ⊓ Subgroup.zpowers e) =
      Nat.card A * Nat.card ↥(Subgroup.zpowers e) :=
    card_sup_mul_card_inf_of_le_normalizer (s265_zpowers_le_normalizer hB hAB heB)
  rw [s265_inf_zpowers_bot hp hord heA, Subgroup.card_bot, hA, hord, mul_one] at hcardprod
  rw [hcardprod, pow_succ]

theorem s265_layer_sn (p : ℕ) (X : Subgroup G) : IsSubnormal (GLAPLayer p X) X :=
  IsSubnormal.step (sSup_le fun _ hK => hK.1)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (sSup_le fun _ hK => hK.1)).2
      (fun _ hg => P65.mem_normalizer_glaPLayer (Subgroup.le_normalizer hg)))
    (IsSubnormal.refl X)

theorem s265_stepB_gen {p : ℕ} (hp : p.Prime) {B A K L : Subgroup G} (hB : IsElemAbelian p B)
    (hAB : A ≤ B) (hAcard : Nat.card A = p ^ 2) (hK : K ≤ L ⊓ Subgroup.centralizer (A : Set G))
    (hKsn : IsSubnormal K (L ⊓ Subgroup.centralizer (A : Set G))) {e : G} (heB : e ∈ B)
    (heA : e ∉ A) (hne : GLAPLayer p (K ⊓ Subgroup.centralizer ({e} : Set G)) ≠ ⊥) :
    ∃ E : Subgroup G, IsE3 p B E ∧ A ≤ E ∧
      GLAPLayer p (L ⊓ Subgroup.centralizer (E : Set G)) ≠ ⊥ := by
  haveI := Fact.mk hp
  have hord : Nat.card (Subgroup.zpowers e) = p := by
    have he1 : e ≠ 1 := fun h => heA (h ▸ A.one_mem)
    rw [Nat.card_zpowers, orderOf_eq_prime (hB.2 e heB) he1]
  have hEcard := s265_card_sup hp hB hAB hAcard heB heA hord
  have hEab : IsElemAbelian p (A ⊔ Subgroup.zpowers e) :=
    isElemAbelian_mono hB (sup_le hAB (Subgroup.zpowers_le.2 heB))
  have hEB : A ⊔ Subgroup.zpowers e ≤ B := sup_le hAB (Subgroup.zpowers_le.2 heB)
  refine ⟨A ⊔ Subgroup.zpowers e, ⟨hEB, hEab, hEcard⟩, le_sup_left, ?_⟩
  have hcomm : ∀ g ∈ B, ∀ d ∈ B, g * d = d * g := fun g hg d hd =>
    congrArg Subtype.val (hB.1.is_comm.comm (⟨g, hg⟩ : B) ⟨d, hd⟩)
  have hKC : ∀ k ∈ K, ∀ d ∈ A, d * k = k * d := fun k hk d hd =>
    Subgroup.mem_centralizer_iff.1 (hK hk).2 d hd
  have hEC : ∀ k ∈ K ⊓ Subgroup.centralizer ({e} : Set G),
      A ⊔ Subgroup.zpowers e ≤ Subgroup.centralizer ({k} : Set G) := by
    intro k hk
    apply sup_le
    · intro d hd
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff.1 hy]
      exact (hKC k hk.1 d hd).symm
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff.1 hy]
      exact (Subgroup.mem_centralizer_iff.1 hk.2 e (Set.mem_singleton e)).symm
  have heE : e ∈ (A ⊔ Subgroup.zpowers e : Subgroup G) :=
    (le_sup_right : Subgroup.zpowers e ≤ A ⊔ Subgroup.zpowers e) (Subgroup.mem_zpowers e)
  have hKE : ∀ k ∈ K ⊓ Subgroup.centralizer ({e} : Set G),
      k ∈ Subgroup.centralizer ((A ⊔ Subgroup.zpowers e : Subgroup G) : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (Subgroup.mem_centralizer_iff.1 (hEC k hk hh) k (Set.mem_singleton k)).symm
  have hEq : K ⊓ (L ⊓ Subgroup.centralizer ((A ⊔ Subgroup.zpowers e : Subgroup G) : Set G)) =
      K ⊓ Subgroup.centralizer ({e} : Set G) := by
    apply le_antisymm
    · exact inf_le_inf_left K (le_trans inf_le_right
        (Subgroup.centralizer_le (Set.singleton_subset_iff.2 heE)))
    · intro k hk
      exact ⟨hk.1, (hK hk.1).1, hKE k hk⟩
  have hMsub : L ⊓ Subgroup.centralizer ((A ⊔ Subgroup.zpowers e : Subgroup G) : Set G) ≤
      L ⊓ Subgroup.centralizer (A : Set G) :=
    inf_le_inf_left L (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_left))
  have hsub : IsSubnormal (K ⊓ Subgroup.centralizer ({e} : Set G))
      (L ⊓ Subgroup.centralizer ((A ⊔ Subgroup.zpowers e : Subgroup G) : Set G)) := by
    have h1 := isSubnormal_inf hKsn (L ⊓ Subgroup.centralizer ((A ⊔ Subgroup.zpowers e : Subgroup G) : Set G))
    have h2 : (L ⊓ Subgroup.centralizer (A : Set G)) ⊓
        (L ⊓ Subgroup.centralizer ((A ⊔ Subgroup.zpowers e : Subgroup G) : Set G)) =
        L ⊓ Subgroup.centralizer ((A ⊔ Subgroup.zpowers e : Subgroup G) : Set G) :=
      inf_eq_right.2 hMsub
    rw [h2, hEq] at h1
    exact h1
  obtain ⟨Y, hY, hYne⟩ : ∃ Y : Subgroup G,
      GLAPComponent p (K ⊓ Subgroup.centralizer ({e} : Set G)) Y ∧ Y ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    apply hne
    unfold GLAPLayer
    exact sSup_eq_bot.2 fun Y hY => hcon Y hY
  have hYM : GLAPComponent p (L ⊓ Subgroup.centralizer ((A ⊔ Subgroup.zpowers e : Subgroup G) : Set G)) Y :=
    glaPComponent_of_isSubnormal' hp hsub hY
  intro hbot
  apply hYne
  have hle : Y ≤ GLAPLayer p (L ⊓ Subgroup.centralizer ((A ⊔ Subgroup.zpowers e : Subgroup G) : Set G)) :=
    le_sSup hYM
  rw [hbot] at hle
  exact le_bot_iff.1 hle

theorem dgrp_eq (b x : G) : Dgrp b x = Subgroup.zpowers x ⊔ Subgroup.zpowers b := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy
    · rw [hy]
      exact (le_sup_right : Subgroup.zpowers b ≤ Subgroup.zpowers x ⊔ Subgroup.zpowers b)
        (Subgroup.mem_zpowers b)
    · rw [hy]
      exact (le_sup_left : Subgroup.zpowers x ≤ Subgroup.zpowers x ⊔ Subgroup.zpowers b)
        (Subgroup.mem_zpowers x)
  · exact sup_le (Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp)))
      (Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp)))

theorem inf_cs_dgrp {L : Subgroup G} {x b : G} (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) :
    L ⊓ Subgroup.centralizer ((Dgrp b x : Subgroup G) : Set G) = L ⊓ cx b := by
  have hbD : b ∈ Dgrp b x := Subgroup.subset_closure (by simp)
  apply le_antisymm
  · intro l hl
    refine ⟨hl.1, ?_⟩
    refine Subgroup.mem_centralizer_iff.2 (fun y hy => ?_)
    rw [Set.mem_singleton_iff.1 hy]
    exact Subgroup.mem_centralizer_iff.1 hl.2 b hbD
  · intro l hl
    refine ⟨hl.1, ?_⟩
    have hDC : Dgrp b x ≤ Subgroup.centralizer ({l} : Set G) := by
      refine (Subgroup.closure_le _).2 ?_
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      refine Subgroup.mem_centralizer_iff.2 (fun h hh => ?_)
      rw [Set.mem_singleton_iff.1 hh]
      rcases hy with hy | hy
      · rw [hy]
        exact (Subgroup.mem_centralizer_iff.1 hl.2 b (Set.mem_singleton b)).symm
      · rw [hy]
        exact (Subgroup.mem_centralizer_iff.1 (hLx hl.1) x (Set.mem_singleton x)).symm
    refine Subgroup.mem_centralizer_iff.2 (fun y hy => ?_)
    exact (Subgroup.mem_centralizer_iff.1 (hDC hy) l (Set.mem_singleton l)).symm

theorem stepB_used {p : ℕ} (hp : p.Prime) {B S : Subgroup G} {x b e : G} (hB : IsElemAbelian p B)
    (hxB : x ∈ B) (hx1 : x ≠ 1) (hSx : S ≤ Subgroup.centralizer ({x} : Set G)) (hb : b ∈ B)
    (hbx : b ∉ Subgroup.zpowers x) (heB : e ∈ B) (heD : e ∉ Dgrp b x)
    (hne : GLAPLayer p (Ipart p S b ⊓ cx e) ≠ ⊥) :
    ∃ E : Subgroup G, E ≤ B ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧ Dgrp b x ≤ E ∧
      GLAPLayer p (S ⊓ cs E) ≠ ⊥ := by
  haveI := Fact.mk hp
  have hzx : Subgroup.zpowers x ≤ B := Subgroup.zpowers_le.2 hxB
  have hDB : Dgrp b x ≤ B := by
    rw [dgrp_eq]
    exact sup_le hzx (Subgroup.zpowers_le.2 hb)
  have hordx : Nat.card (Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hB.2 x hxB) hx1]
  have hordb : Nat.card (Subgroup.zpowers b) = p := by
    have hb1 : b ≠ 1 := fun h => hbx (h ▸ (Subgroup.zpowers x).one_mem)
    rw [Nat.card_zpowers, orderOf_eq_prime (hB.2 b hb) hb1]
  have hcard : Nat.card ↥(Dgrp b x) = p ^ 2 := by
    rw [dgrp_eq]
    exact s265_card_sup hp hB hzx (by rw [hordx, pow_one]) hb hbx hordb
  have hK : Ipart p S b ≤ S ⊓ Subgroup.centralizer ((Dgrp b x : Subgroup G) : Set G) := by
    rw [inf_cs_dgrp hSx]
    exact sSup_le fun _ hK => hK.1
  have hKsn : IsSubnormal (Ipart p S b) (S ⊓ Subgroup.centralizer ((Dgrp b x : Subgroup G) : Set G)) := by
    rw [inf_cs_dgrp hSx]
    exact s265_layer_sn p (S ⊓ cx b)
  obtain ⟨E, ⟨h1, h2, h3⟩, h4, h5⟩ := s265_stepB_gen hp hB hDB hcard hK hKsn heB heD hne
  exact ⟨E, h1, h2, h3, h4, h5⟩

theorem stepB_std {p : ℕ} (hp : p.Prime) {B S D K : Subgroup G} {x e : G} (hB : IsElemAbelian p B)
    (hStd : GLAStdSubPre p B x S D K) (heB : e ∈ B) (heD : e ∉ D)
    (hne : GLAPLayer p (K ⊓ cx e) ≠ ⊥) :
    ∃ E : Subgroup G, IsE3 p B E ∧ D ≤ E ∧ GLAPLayer p (S ⊓ cs E) ≠ ⊥ := by
  obtain ⟨hDB, -, hDcard, -, -, hKcomp, -⟩ := hStd
  exact s265_stepB_gen hp hB hDB hDcard hKcomp.1 hKcomp.2.1 heB heD hne

end Step

end CFSG.LocalAnalysis.GLTheoremA.S265

end
