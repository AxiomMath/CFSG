module

public import CFSG.CGT.PushingUpLit.SolKNA.BranchC3
public import CFSG.CGT.PushingUpLit.SolKNA.Lemma14
import CFSG.RankThree.GF2n.Tim78Frattini

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

set_option linter.unusedSectionVars false

open CFSG CFSG.CGT.Timmesfeld75 CFSG.CGT.PushingUpLit.SolKAb
open CFSG.RankThree.GF2n (inf_conjSubgroup_eq_bot_of_isTI conjSubgroup_eq_self_iff
  isTI_conjSubgroup conjSubgroup_eq_of_isTI exists_mul_of_mem_sup)
open CFSG.RankThree.GF2n.Tim77 (mem_normalizer_of_commute_of_isTI)
open CFSG.ComponentClassification.AschbacherTightEmbedding (rightConjugate rightConjugate_card
  mem_rightConjugate_iff rightConjugate_mul rightConjugate_eq_self_iff)
open CFSG.ComponentClassification.LiteratureLocal.TightCommuting (rightConjugate_mono)
open CFSG.Open (IsElemAbelian)

variable {G : Type} [Group G]

theorem commute_of_inf_eq_bot {A B : Subgroup G} (hAB : A ⊓ B = ⊥) {c t : G}
    (hc : c ∈ A ⊓ Subgroup.normalizer (B : Set G))
    (ht : t ∈ B ⊓ Subgroup.normalizer (A : Set G)) : c * t = t * c := by
  obtain ⟨hcA, hcB⟩ := hc
  obtain ⟨htB, htA⟩ := ht
  have h1 : c * t * c⁻¹ * t⁻¹ ∈ B :=
    B.mul_mem ((Subgroup.mem_normalizer_iff.mp hcB t).mp htB) (B.inv_mem htB)
  have h2 : c * t * c⁻¹ * t⁻¹ ∈ A := by
    have := (Subgroup.mem_normalizer_iff.mp htA c⁻¹).mp (A.inv_mem hcA)
    have e : c * t * c⁻¹ * t⁻¹ = c * (t * c⁻¹ * t⁻¹) := by group
    rw [e]
    exact A.mul_mem hcA this
  have h3 : c * t * c⁻¹ * t⁻¹ ∈ A ⊓ B := ⟨h2, h1⟩
  rw [hAB, Subgroup.mem_bot] at h3
  have h4 : c * t * c⁻¹ = t := mul_inv_eq_one.mp h3
  calc c * t = c * t * c⁻¹ * c := by group
    _ = t * c := by rw [h4]

theorem sup_inf_normalizer_eq {A B : Subgroup G}
    (hBA : B ≤ Subgroup.normalizer (A : Set G)) :
    (A ⊔ B) ⊓ Subgroup.normalizer (B : Set G) = (A ⊓ Subgroup.normalizer (B : Set G)) ⊔ B := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxS, hxN⟩ := hx
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hBA hxS
    have ha' : a ∈ Subgroup.normalizer (B : Set G) := by
      have e : a = (a * b) * b⁻¹ := by group
      rw [e]
      exact (Subgroup.normalizer (B : Set G)).mul_mem hxN
        ((Subgroup.normalizer (B : Set G)).inv_mem (Subgroup.le_normalizer hb))
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨ha, ha'⟩) (Subgroup.mem_sup_right hb)
  · exact sup_le (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
      (le_inf le_sup_right Subgroup.le_normalizer)

variable [Finite G]

theorem inf_rightConjugate_eq_bot {R : Subgroup G} {g : G} (hTI : IsTI R)
    (hg : g ∉ Subgroup.normalizer (R : Set G)) : R ⊓ rightConjugate R g = ⊥ := by
  have h : rightConjugate R g = conjSubgroup g⁻¹ R := rfl
  rw [h]
  refine inf_conjSubgroup_eq_bot_of_isTI hTI fun heq => hg ?_
  have := (Subgroup.normalizer (R : Set G)).inv_mem (conjSubgroup_eq_self_iff.mp heq)
  simpa using this

theorem inf_normalizer_rightConjugate_eq {R T : Subgroup G} {g : G} (hTI : IsTI R)
    (hg : g ∉ Subgroup.normalizer (R : Set G))
    (hT : T = rightConjugate R g ⊓ Subgroup.normalizer (R : Set G)) (hT0 : T ≠ ⊥) :
    R ⊓ Subgroup.normalizer (rightConjugate R g : Set G) =
      R ⊓ Subgroup.normalizer (T : Set G) := by
  have hinf := inf_rightConjugate_eq_bot hTI hg
  have hTI' : IsTI (rightConjugate R g) := isTI_conjSubgroup hTI g⁻¹
  ext c
  constructor
  · intro hc
    refine ⟨hc.1, ?_⟩
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun t ht => ?_)
    have ht' : t ∈ rightConjugate R g ⊓ Subgroup.normalizer (R : Set G) := by
      rw [← hT]
      exact ht
    exact (commute_of_inf_eq_bot hinf hc ht').symm
  · intro hc
    refine ⟨hc.1, ?_⟩
    obtain ⟨⟨t₀, ht₀⟩, ht₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hT0
    have ht₀' : t₀ ∈ rightConjugate R g ⊓ Subgroup.normalizer (R : Set G) := by
      rw [← hT]
      exact ht₀
    have hcomm : c * t₀ = t₀ * c := by
      have h1 : c * t₀ * c⁻¹ * t₀⁻¹ ∈ rightConjugate R g := by
        have h5 : c * t₀ * c⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hc.2 t₀).mp ht₀
        have h6 : c * t₀ * c⁻¹ ∈ rightConjugate R g := by
          rw [hT] at h5
          exact h5.1
        exact (rightConjugate R g).mul_mem h6 ((rightConjugate R g).inv_mem ht₀'.1)
      have h2 : c * t₀ * c⁻¹ * t₀⁻¹ ∈ R := by
        have h5 := (Subgroup.mem_normalizer_iff.mp ht₀'.2 c⁻¹).mp (R.inv_mem hc.1)
        have e : c * t₀ * c⁻¹ * t₀⁻¹ = c * (t₀ * c⁻¹ * t₀⁻¹) := by group
        rw [e]
        exact R.mul_mem hc.1 h5
      have h3 : c * t₀ * c⁻¹ * t₀⁻¹ ∈ R ⊓ rightConjugate R g := ⟨h2, h1⟩
      rw [hinf, Subgroup.mem_bot] at h3
      have h4 : c * t₀ * c⁻¹ = t₀ := mul_inv_eq_one.mp h3
      calc c * t₀ = c * t₀ * c⁻¹ * c := by group
        _ = t₀ * c := by rw [h4]
    exact mem_normalizer_of_commute_of_isTI hTI' ht₀'.1 (fun h => ht₀1 (Subtype.ext h)) hcomm

theorem inf_normalizer_L_eq {R T L : Subgroup G} {g : G} (hTI : IsTI R)
    (hg : g ∉ Subgroup.normalizer (R : Set G))
    (hT : T = rightConjugate R g ⊓ Subgroup.normalizer (R : Set G))
    (hL : L = R ⊓ Subgroup.normalizer (rightConjugate R g : Set G)) (hL0 : L ≠ ⊥) :
    rightConjugate R g ⊓ Subgroup.normalizer (L : Set G) = T := by
  have hinf := inf_rightConjugate_eq_bot hTI hg
  ext x
  constructor
  · intro hx
    obtain ⟨hxR', hxL⟩ := hx
    obtain ⟨⟨l₀, hl₀⟩, hl₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hL0
    have hl₀' : l₀ ∈ R ⊓ Subgroup.normalizer (rightConjugate R g : Set G) := by
      rw [← hL]
      exact hl₀
    have hcomm : x * l₀ = l₀ * x := by
      have h1 : x * l₀ * x⁻¹ * l₀⁻¹ ∈ R := by
        have h5 : x * l₀ * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hxL l₀).mp hl₀
        have h6 : x * l₀ * x⁻¹ ∈ R := by
          rw [hL] at h5
          exact h5.1
        exact R.mul_mem h6 (R.inv_mem hl₀'.1)
      have h2 : x * l₀ * x⁻¹ * l₀⁻¹ ∈ rightConjugate R g := by
        have h5 := (Subgroup.mem_normalizer_iff.mp hl₀'.2 x⁻¹).mp
          ((rightConjugate R g).inv_mem hxR')
        have e : x * l₀ * x⁻¹ * l₀⁻¹ = x * (l₀ * x⁻¹ * l₀⁻¹) := by group
        rw [e]
        exact (rightConjugate R g).mul_mem hxR' h5
      have h3 : x * l₀ * x⁻¹ * l₀⁻¹ ∈ R ⊓ rightConjugate R g := ⟨h1, h2⟩
      rw [hinf, Subgroup.mem_bot] at h3
      have h4 : x * l₀ * x⁻¹ = l₀ := mul_inv_eq_one.mp h3
      calc x * l₀ = x * l₀ * x⁻¹ * x := by group
        _ = l₀ * x := by rw [h4]
    have hxN : x ∈ Subgroup.normalizer (R : Set G) :=
      mem_normalizer_of_commute_of_isTI hTI hl₀'.1 (fun h => hl₀1 (Subtype.ext h)) hcomm
    rw [hT]
    exact ⟨hxR', hxN⟩
  · intro hx
    rw [hT] at hx
    refine ⟨hx.1, Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun l hl => ?_)⟩
    have hl' : l ∈ R ⊓ Subgroup.normalizer (rightConjugate R g : Set G) := by
      rw [← hL]
      exact hl
    exact commute_of_inf_eq_bot hinf hl' hx

theorem isTI_L {R T L : Subgroup G} {g : G} (hTI : IsTI R)
    (hg : g ∉ Subgroup.normalizer (R : Set G))
    (hT : T = rightConjugate R g ⊓ Subgroup.normalizer (R : Set G))
    (hL : L = R ⊓ Subgroup.normalizer (rightConjugate R g : Set G)) (hL0 : L ≠ ⊥) :
    ∀ x ∈ rightConjugate R g ⊔ L, L ⊓ rightConjugate L x ≠ ⊥ → rightConjugate L x = L := by
  intro x hx hne
  have hLR : L ≤ R := by rw [hL]; exact inf_le_left
  have hLN : L ≤ Subgroup.normalizer (rightConjugate R g : Set G) := by rw [hL]; exact inf_le_right
  obtain ⟨r', hr', l, hl, rfl⟩ := exists_mul_of_mem_sup hLN hx
  have hne' : R ⊓ rightConjugate R (r' * l) ≠ ⊥ := by
    intro hbot
    apply hne
    rw [eq_bot_iff]
    exact (inf_le_inf hLR (rightConjugate_mono _ hLR)).trans hbot.le
  have hxR : r' * l ∈ Subgroup.normalizer (R : Set G) :=
    (rightConjugate_eq_self_iff R (r' * l)).mp (conjSubgroup_eq_of_isTI hTI hne')
  have hr'N : r' ∈ Subgroup.normalizer (R : Set G) := by
    have e : r' = (r' * l) * l⁻¹ := by group
    rw [e]
    exact (Subgroup.normalizer (R : Set G)).mul_mem hxR
      ((Subgroup.normalizer (R : Set G)).inv_mem (Subgroup.le_normalizer (hLR hl)))
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := by
    rw [← inf_normalizer_L_eq hTI hg hT hL hL0]
    exact inf_le_right
  have hr'T : r' ∈ T := by
    rw [hT]
    exact ⟨hr', hr'N⟩
  have h1 : rightConjugate L r' = L := (rightConjugate_eq_self_iff L r').mpr (hTL hr'T)
  have h2 : rightConjugate L l = L :=
    (rightConjugate_eq_self_iff L l).mpr (Subgroup.le_normalizer hl)
  rw [← rightConjugate_mul, h1, h2]

theorem sq_mem_of_frattini_le {P K : Subgroup G} (hP : IsPGroup 2 P)
    (h : (frattini ↥P).map P.subtype ≤ K) {x : G} (hx : x ∈ P) : x * x ∈ K := by
  have := h (CFSG.RankThree.GF2n.Tim78.sq_mem_inSubgroup_frattini hP hx)
  rwa [sq] at this

theorem comm_mem_of_frattini_le {P K : Subgroup G} (hP : IsPGroup 2 P)
    (h : (frattini ↥P).map P.subtype ≤ K) {x y : G} (hx : x ∈ P) (hy : y ∈ P) :
    x * y * x⁻¹ * y⁻¹ ∈ K := by
  have := h (CFSG.RankThree.GF2n.Tim78.commutatorElement_mem_inSubgroup_frattini hP hx hy)
  rwa [commutatorElement_def] at this

theorem isCommSubgroup_of_isElemAbelian {A : Subgroup G} (h : IsElemAbelian 2 A) :
    IsCommSubgroup A := fun a ha b hb =>
  congrArg Subtype.val (h.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

section Certified


theorem revPair_of_bData {R T : Subgroup G} {g : G} (hR2 : IsPGroup 2 R) (hTI : IsTI R)
    (hg : g ∉ Subgroup.normalizer (R : Set G))
    (hT : T = rightConjugate R g ⊓ Subgroup.normalizer (R : Set G)) (hT0 : T ≠ ⊥)
    (hTnc : ¬ IsCyclic ↥T) (hNel : IsElemAbelian 2 (R ⊓ Subgroup.normalizer (T : Set G)))
    (hNT : Nonempty (↥(R ⊓ Subgroup.normalizer (T : Set G)) ≃* ↥T))
    (hlt : Nat.card ↥T < Nat.card ↥R) (hle : Nat.card ↥R ≤ Nat.card ↥T ^ 2)
    (hWn : R ≤ Subgroup.normalizer
      (((R ⊔ T) ⊓ Subgroup.normalizer (T : Set G) : Subgroup G) : Set G)) :
    RevPair R g := by
  obtain ⟨L, hLdef⟩ : ∃ L : Subgroup G, L = R ⊓ Subgroup.normalizer (T : Set G) := ⟨_, rfl⟩
  rw [← hLdef] at hNel hNT
  have hinf := inf_rightConjugate_eq_bot hTI hg
  have hLR' : L = R ⊓ Subgroup.normalizer (rightConjugate R g : Set G) :=
    hLdef.trans (inf_normalizer_rightConjugate_eq hTI hg hT hT0).symm
  have hcardL : Nat.card ↥L = Nat.card ↥T := Nat.card_congr hNT.some.toEquiv
  have hL0 : L ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcardL
    exact hT0 (Subgroup.eq_bot_of_card_eq T hcardL.symm)
  have hLR : L ≤ R := by rw [hLR']; exact inf_le_left
  have hLN : L ≤ Subgroup.normalizer (rightConjugate R g : Set G) := by
    rw [hLR']; exact inf_le_right
  have hTR : T ≤ Subgroup.normalizer (R : Set G) := by rw [hT]; exact inf_le_right
  have hL2 : IsPGroup 2 L := hR2.to_le hLR
  have hR'2 : IsPGroup 2 (rightConjugate R g) := hR2.map (MulAut.conj g⁻¹).toMonoidHom
  have hLc : IsCommSubgroup L := isCommSubgroup_of_isElemAbelian hNel
  have hLnc : ¬ IsCyclic ↥L := by
    intro hc
    obtain ⟨e⟩ := hNT
    exact hTnc (isCyclic_of_surjective e.toMonoidHom e.surjective)
  have hinfL : L ⊓ rightConjugate R g = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_right _ hLR).trans hinf.le)
  have hTL := inf_normalizer_L_eq hTI hg hT hLR' hL0
  have hγ : Nat.card ↥(rightConjugate R g ⊓ Subgroup.normalizer (L : Set G)) ≤ Nat.card ↥L := by
    rw [hTL, hcardL]
  have hR'card : Nat.card ↥(rightConjugate R g) = Nat.card ↥R := rightConjugate_card R g
  have hW : (R ⊔ T) ⊓ Subgroup.normalizer (T : Set G) = L ⊔ T := by
    rw [sup_inf_normalizer_eq hTR, hLdef]
  have hW' : (rightConjugate R g ⊔ L) ⊓ Subgroup.normalizer (L : Set G) = T ⊔ L := by
    rw [sup_inf_normalizer_eq hLN, hTL]
  have hnot : ∃ y ∈ rightConjugate R g,
      y ∉ rightConjugate R g ⊓ Subgroup.normalizer (L : Set G) := by
    by_contra hcon
    have hle' : rightConjugate R g ≤ rightConjugate R g ⊓ Subgroup.normalizer (L : Set G) :=
      fun y hy => by
        by_contra hy'
        exact hcon ⟨y, hy, hy'⟩
    have := Subgroup.card_le_of_le hle'
    rw [hTL, hR'card] at this
    omega
  have hel : ∀ t ∈ L, t * t = 1 := fun t ht => by
    have := hNel.2 t ht
    rwa [sq] at this
  have hTIL := isTI_L hTI hg hT hLR' hL0
  rcases lemma14 hR'2 hL2 hL0 hLN hinfL hLc hLnc hTIL hγ with h1 | B | ⟨W, A⟩
  · exfalso
    have hle' : rightConjugate R g ≤ rightConjugate R g ⊓ Subgroup.normalizer (L : Set G) :=
      le_inf le_rfl h1
    have := Subgroup.card_le_of_le hle'
    rw [hTL, hR'card] at this
    omega
  · refine ⟨?_, ?_, ?_⟩
    · rw [← hLR', ← hT]
      have hRn : R ≤ Subgroup.normalizer ((L ⊔ T : Subgroup G) : Set G) := by
        rw [hW] at hWn
        exact hWn
      have hR'n : rightConjugate R g ≤ Subgroup.normalizer ((L ⊔ T : Subgroup G) : Set G) := by
        have h2 := le_sup_left.trans B.normal
        rw [hW', sup_comm] at h2
        exact h2
      intro x hx
      exact (sup_le hRn hR'n) hx
    · rw [← hT]
      refine CFSG.ComponentClassification.Asc76X.frattini_map_le_of_sq hR'2 fun x hx => ?_
      have h2 := B.sq_mem_R hx
      rw [hTL] at h2
      rw [sq]
      exact h2
    · rw [← hT, ← hTL]
      intro n hn
      refine ⟨hn.1, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
      exact (B.N_central hel hnot hn hr).symm
  · exfalso
    have h1 := A.card_R
    have h2 := A.card_H
    rw [h2, hR'card, hcardL] at h1
    have hpos : 0 < Nat.card ↥T ^ 2 := pow_pos Nat.card_pos 2
    omega

theorem revPair_of_pair {R T : Subgroup G} {g : G} (hR2 : IsPGroup 2 R) (hTI : IsTI R)
    (hg : g ∉ Subgroup.normalizer (R : Set G))
    (hT : T = rightConjugate R g ⊓ Subgroup.normalizer (R : Set G)) (hT0 : T ≠ ⊥)
    (hTc : IsCommSubgroup T) (hTnc : ¬ IsCyclic ↥T)
    (hTIT : ∀ x ∈ R ⊔ T, T ⊓ rightConjugate T x ≠ ⊥ → rightConjugate T x = T)
    (hNel : IsElemAbelian 2 (R ⊓ Subgroup.normalizer (T : Set G)))
    (hNT : Nonempty (↥(R ⊓ Subgroup.normalizer (T : Set G)) ≃* ↥T))
    (hlt : Nat.card ↥T < Nat.card ↥R) (hle : Nat.card ↥R ≤ Nat.card ↥T ^ 2) :
    RevPair R g := by
  have hinf := inf_rightConjugate_eq_bot hTI hg
  have hR'2 : IsPGroup 2 (rightConjugate R g) := hR2.map (MulAut.conj g⁻¹).toMonoidHom
  have hTR' : T ≤ rightConjugate R g := by rw [hT]; exact inf_le_left
  have hT2 : IsPGroup 2 T := hR'2.to_le hTR'
  have hTR : T ≤ Subgroup.normalizer (R : Set G) := by rw [hT]; exact inf_le_right
  have hTRb : T ⊓ R = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxT, hxR⟩
    have : x ∈ R ⊓ rightConjugate R g := ⟨hxR, hTR' hxT⟩
    rwa [hinf] at this
  have hcardN : Nat.card ↥(R ⊓ Subgroup.normalizer (T : Set G)) = Nat.card ↥T :=
    Nat.card_congr hNT.some.toEquiv
  have hWn : R ≤ Subgroup.normalizer
      (((R ⊔ T) ⊓ Subgroup.normalizer (T : Set G) : Subgroup G) : Set G) := by
    rcases lemma14 hR2 hT2 hT0 hTR hTRb hTc hTnc hTIT hcardN.le with h1 | B | ⟨W, A⟩
    · exfalso
      have hle' : R ≤ R ⊓ Subgroup.normalizer (T : Set G) := le_inf le_rfl h1
      have := Subgroup.card_le_of_le hle'
      omega
    · exact le_sup_left.trans B.normal
    · exfalso
      have h1 := A.card_R
      have h2 := A.card_H
      rw [h2] at h1
      have hpos : 0 < Nat.card ↥T ^ 2 := pow_pos Nat.card_pos 2
      omega
  exact revPair_of_bData hR2 hTI hg hT hT0 hTnc hNel hNT hlt hle hWn

end Certified

theorem RevPair.lemma18_data {R T C : Subgroup G} {g : G} (hR2 : IsPGroup 2 R)
    (hrev : RevPair R g) (hT : T = rightConjugate R g ⊓ Subgroup.normalizer (R : Set G))
    (hC : R ⊓ Subgroup.normalizer (rightConjugate R g : Set G) = C) :
    R ⊔ conjSubgroup g⁻¹ R ≤ Subgroup.normalizer (((C ⊔ T : Subgroup G)) : Set G) ∧
      (∀ x ∈ conjSubgroup g⁻¹ R, x * x ∈ T) ∧
      (∀ x ∈ conjSubgroup g⁻¹ R, ∀ y ∈ conjSubgroup g⁻¹ R, x * y * x⁻¹ * y⁻¹ ∈ T) ∧
      (∀ t ∈ T, ∀ x ∈ conjSubgroup g⁻¹ R, t * x = x * t) := by
  have hR'2 : IsPGroup 2 (rightConjugate R g) := hR2.map (MulAut.conj g⁻¹).toMonoidHom
  have hF : (frattini ↥(rightConjugate R g)).map (rightConjugate R g).subtype ≤ T := by
    rw [hT]
    exact hrev.frattini_le
  refine ⟨fun x hx => ?_, fun x hx => sq_mem_of_frattini_le hR'2 hF hx,
    fun x hx y hy => comm_mem_of_frattini_le hR'2 hF hx hy, fun t ht x hx => ?_⟩
  · have := hrev.normal x hx
    rwa [hC, ← hT] at this
  · have h1 : t ∈ rightConjugate R g ⊓ Subgroup.normalizer (R : Set G) := by
      rw [← hT]
      exact ht
    exact (Subgroup.mem_centralizer_iff.mp (hrev.le_center h1).2 x hx).symm

end CFSG.CGT.PushingUpLit.SolKNA
