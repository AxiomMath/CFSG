module

public import CFSG.Open.LocalVocabulary
public import CFSG.LocalAnalysis.GL83PartI.I_23_1

import CFSG.GroupTheory.PGroup.ElemAbelianSq

public section

namespace CFSG.AltLocalClosure

open Equiv Equiv.Perm Subgroup Finset

theorem exists_isCycle_mem_of_sylow_le {n p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpn : p ≤ n)
    {B : Subgroup (alternatingGroup (Fin n))} (P : Sylow p (alternatingGroup (Fin n)))
    (hPB : (P : Subgroup _) ≤ B) :
    ∃ c ∈ B, (c : Equiv.Perm (Fin n)).IsCycle ∧ (c : Equiv.Perm (Fin n)).support.card = p := by
  classical
  have hp := Fact.out (p := p.Prime)
  have hp2le : 2 ≤ p := hp.two_le
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 2 := ⟨p - 2, by omega⟩
  let emb : Fin (m + 2) ↪ Fin n := Fin.castLEEmb hpn
  let c0 : Perm (Fin n) := (finRotate (m + 2)).extendDomain emb.toEquivRange
  have hc0cyc : c0.IsCycle := isCycle_finRotate.extendDomain emb.toEquivRange
  have hc0supp : c0.support.card = m + 2 := by
    change ((finRotate (m + 2)).extendDomain emb.toEquivRange).support.card = m + 2
    rw [support_extend_domain, Finset.card_map, support_finRotate, Finset.card_univ,
      Fintype.card_fin]
  have hc0alt : c0 ∈ alternatingGroup (Fin n) := by
    rw [mem_alternatingGroup, hc0cyc.sign, hc0supp,
      (hp.odd_of_ne_two hp2).neg_one_pow, neg_neg]
  let c0A : alternatingGroup (Fin n) := ⟨c0, hc0alt⟩
  let C : Subgroup (alternatingGroup (Fin n)) := Subgroup.zpowers c0A
  have hCcard : Nat.card C = m + 2 := by
    change Nat.card (Subgroup.zpowers c0A) = m + 2
    rw [Nat.card_zpowers]
    have hcoe : orderOf c0A = orderOf c0 := by
      rw [← Subgroup.orderOf_coe c0A]
    rw [hcoe, hc0cyc.orderOf, hc0supp]
  have hC : IsPGroup (m + 2) C := IsPGroup.of_card (n := 1) (by simpa using hCcard)
  obtain ⟨P', hle⟩ := hC.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (M := alternatingGroup (Fin n)) P' P
  let c : alternatingGroup (Fin n) := (MulAut.conj g) c0A
  have hc0P' : c0A ∈ (P' : Subgroup (alternatingGroup (Fin n))) :=
    hle (Subgroup.mem_zpowers c0A)
  have hcP : c ∈ (P : Subgroup (alternatingGroup (Fin n))) := by
    have hmem := Subgroup.smul_mem_pointwise_smul c0A (MulAut.conj g)
      (P' : Subgroup (alternatingGroup (Fin n))) hc0P'
    rw [← Sylow.coe_subgroup_smul (g := g) (P := P'), hg] at hmem
    exact hmem
  have hcB : c ∈ B := hPB hcP
  have hcval : (c : Perm (Fin n)) = (g : Perm (Fin n)) * c0 * (g : Perm (Fin n))⁻¹ := by
    simp [c, c0A, MulAut.conj_apply]
  refine ⟨c, hcB, ?_, ?_⟩
  · rw [hcval]
    exact hc0cyc.conj
  · rw [hcval, Equiv.Perm.card_support_conj, hc0supp]


theorem eq_one_of_sign_eq_one_of_card_support_le_two {α : Type*} [Fintype α] [DecidableEq α]
    {c : Perm α} (hc : Equiv.Perm.sign c = 1) (h2 : c.support.card ≤ 2) : c = 1 := by
  rcases (show c.support.card = 0 ∨ c.support.card = 1 ∨ c.support.card = 2 by omega)
    with h0 | h1 | h2
  · exact Equiv.Perm.card_support_eq_zero.mp h0
  · exact absurd h1 (Equiv.Perm.card_support_ne_one c)
  · exact absurd (Equiv.Perm.card_support_eq_two.mp h2).sign_eq (by rw [hc]; norm_num)

theorem three_le_card_support_of_ne_one {α : Type*} [Fintype α] [DecidableEq α]
    {c : Perm α} (hc : Equiv.Perm.sign c = 1) (hne : c ≠ 1) : 3 ≤ c.support.card := by
  by_contra h
  exact hne (eq_one_of_sign_eq_one_of_card_support_le_two hc (by omega))

theorem cyc3_support_subset {α : Type*} [Fintype α] [DecidableEq α] {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (GL83.cyc3 a b c).support ⊆ ({a, b, c} : Finset α) := by
  intro x hx
  by_contra hxabc
  have hxa : x ≠ a := fun h => hxabc (by simp [h])
  have hxb : x ≠ b := fun h => hxabc (by simp [h])
  have hxc : x ≠ c := fun h => hxabc (by simp [h])
  exact (Equiv.Perm.mem_support.mp hx) (GL83.cyc3_apply_of_ne hxa hxb hxc)

theorem cyc3_commute_of_fixes {α : Type*} [Fintype α] [DecidableEq α]
    {g : Perm α} {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : g a = a) (hb : g b = b) (hc : g c = c) :
    g * GL83.cyc3 a b c = GL83.cyc3 a b c * g := by
  have hsupp := cyc3_support_subset hab hac hbc
  have hdisj : Disjoint (GL83.cyc3 a b c).support g.support := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have hxabc := hsupp hx1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxabc
    rcases hxabc with rfl | rfl | rfl
    · exact (Equiv.Perm.mem_support.mp hx2) ha
    · exact (Equiv.Perm.mem_support.mp hx2) hb
    · exact (Equiv.Perm.mem_support.mp hx2) hc
  exact (Equiv.Perm.disjoint_iff_disjoint_support.mpr hdisj).commute.eq.symm

theorem altOn_support_compl_le_map {n : ℕ}
    {B : Subgroup (alternatingGroup (Fin n))} (c : alternatingGroup (Fin n))
    (hc : Subgroup.centralizer ({c} : Set _) ≤ B) :
    GL83.altOn (((c : Perm (Fin n)).supportᶜ : Finset (Fin n)) : Set (Fin n)) ≤
      B.map (alternatingGroup (Fin n)).subtype := by
  intro g hg
  let A := alternatingGroup (Fin n)
  have hgA : g ∈ A := (GL83.mem_altOn.mp hg).1
  have hfix : ∀ x, x ∉ (((c : Perm (Fin n)).supportᶜ : Finset (Fin n)) : Set (Fin n)) →
      g x = x := (GL83.mem_altOn.mp hg).2
  have hcomm : g * (c : Perm (Fin n)) = (c : Perm (Fin n)) * g := by
    have hsub : g.support ⊆ ((c : Perm (Fin n)).supportᶜ : Finset (Fin n)) := by
      intro x hx
      by_contra hxF
      exact (Equiv.Perm.mem_support.mp hx) (hfix x hxF)
    have hdisj : Disjoint g.support (c : Perm (Fin n)).support :=
      Finset.subset_compl_iff_disjoint_right.mp hsub
    exact (Equiv.Perm.disjoint_iff_disjoint_support.mpr hdisj).commute.eq
  have hcent : (⟨g, hgA⟩ : A) ∈ Subgroup.centralizer ({c} : Set A) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext hcomm
  exact Subgroup.mem_map_of_mem A.subtype (hc hcent)

theorem exists_cyc3_pair_of_six {n : ℕ} (a : Fin 6 → Fin n)
    (ha : Function.Injective a) :
    ∃ y1 y2 : alternatingGroup (Fin n),
      (y1 : Perm (Fin n)) = GL83.cyc3 (a 0) (a 1) (a 2) ∧
      (y2 : Perm (Fin n)) = GL83.cyc3 (a 3) (a 4) (a 5) ∧
      y1 * y2 = y2 * y1 ∧ y2 ∉ Subgroup.zpowers y1 := by
  classical
  let A := alternatingGroup (Fin n)
  have h01 : a 0 ≠ a 1 := ha.ne (by decide)
  have h02 : a 0 ≠ a 2 := ha.ne (by decide)
  have h12 : a 1 ≠ a 2 := ha.ne (by decide)
  have h34 : a 3 ≠ a 4 := ha.ne (by decide)
  have h35 : a 3 ≠ a 5 := ha.ne (by decide)
  have h45 : a 4 ≠ a 5 := ha.ne (by decide)
  let y1 : A := ⟨GL83.cyc3 (a 0) (a 1) (a 2),
    (GL83.isThreeCycle_cyc3 ⟨h01, h02, h12⟩).mem_alternatingGroup⟩
  let y2 : A := ⟨GL83.cyc3 (a 3) (a 4) (a 5),
    (GL83.isThreeCycle_cyc3 ⟨h34, h35, h45⟩).mem_alternatingGroup⟩
  have hy1perm : (y1 : Perm (Fin n)) = GL83.cyc3 (a 0) (a 1) (a 2) := rfl
  have hy2perm : (y2 : Perm (Fin n)) = GL83.cyc3 (a 3) (a 4) (a 5) := rfl
  let T1 : Finset (Fin n) := {a 0, a 1, a 2}
  let T2 : Finset (Fin n) := {a 3, a 4, a 5}
  have hy1supp : (y1 : Perm (Fin n)).support ⊆ T1 := by
    rw [hy1perm]
    change (GL83.cyc3 (a 0) (a 1) (a 2)).support ⊆ ({a 0, a 1, a 2} : Finset (Fin n))
    exact cyc3_support_subset h01 h02 h12
  have hy2supp : (y2 : Perm (Fin n)).support ⊆ T2 := by
    rw [hy2perm]
    change (GL83.cyc3 (a 3) (a 4) (a 5)).support ⊆ ({a 3, a 4, a 5} : Finset (Fin n))
    exact cyc3_support_subset h34 h35 h45
  have hT1img : T1 = Finset.image a ({0, 1, 2} : Finset (Fin 6)) := by
    ext x
    simp [T1]
  have hT2img : T2 = Finset.image a ({3, 4, 5} : Finset (Fin 6)) := by
    ext x
    simp [T2]
  have hT1T2 : Disjoint T1 T2 := by
    rw [hT1img, hT2img]
    exact (Finset.disjoint_image ha).mpr (by decide)
  have hdisj_supp : Disjoint (y1 : Perm (Fin n)).support (y2 : Perm (Fin n)).support := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact (Finset.disjoint_left.mp hT1T2) (hy1supp hx1) (hy2supp hx2)
  have hcommA : y1 * y2 = y2 * y1 :=
    Subtype.ext ((Equiv.Perm.disjoint_iff_disjoint_support.mpr hdisj_supp).commute.eq)
  have hy2not : y2 ∉ Subgroup.zpowers y1 := by
    intro hmem
    have hstab : Subgroup.zpowers y1 ≤ MulAction.stabilizer A (a 3) := by
      rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
      change (y1 : Perm (Fin n)) (a 3) = a 3
      rw [hy1perm]
      exact GL83.cyc3_apply_of_ne (ha.ne (by decide)) (ha.ne (by decide)) (ha.ne (by decide))
    have hfix : (y2 : Perm (Fin n)) (a 3) = a 3 := hstab hmem
    have hmove : (y2 : Perm (Fin n)) (a 3) = a 4 := by
      rw [hy2perm]
      exact GL83.cyc3_apply_left ⟨h34, h35, h45⟩
    exact (ha.ne (by decide : (3 : Fin 6) ≠ 4)) (hfix.symm.trans hmove)
  exact ⟨y1, y2, rfl, rfl, hcommA, hy2not⟩

theorem cyc3_pair_map_le_centralizer_altOn_compl {n : ℕ} {S : Finset (Fin n)}
    {a : Fin 6 → Fin n} (ha : Function.Injective a) (haS : ∀ i, a i ∈ S)
    {y1 y2 : alternatingGroup (Fin n)}
    (hy1 : (y1 : Perm (Fin n)) = GL83.cyc3 (a 0) (a 1) (a 2))
    (hy2 : (y2 : Perm (Fin n)) = GL83.cyc3 (a 3) (a 4) (a 5)) :
    (Subgroup.zpowers y1 ⊔ Subgroup.zpowers y2).map (alternatingGroup (Fin n)).subtype ≤
      Subgroup.centralizer (GL83.altOn (((Sᶜ : Finset (Fin n)) : Set (Fin n)))) := by
  have h01 : a 0 ≠ a 1 := ha.ne (by decide)
  have h02 : a 0 ≠ a 2 := ha.ne (by decide)
  have h12 : a 1 ≠ a 2 := ha.ne (by decide)
  have h34 : a 3 ≠ a 4 := ha.ne (by decide)
  have h35 : a 3 ≠ a 5 := ha.ne (by decide)
  have h45 : a 4 ≠ a 5 := ha.ne (by decide)
  rw [Subgroup.map_le_iff_le_comap]
  refine sup_le ?_ ?_
  · rw [Subgroup.zpowers_le, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro g hg
    have hfix : ∀ i, g (a i) = a i := fun i =>
      (GL83.mem_altOn.mp hg).2 (a i) (by simpa [Finset.mem_compl] using haS i)
    change g * (y1 : Perm (Fin n)) = (y1 : Perm (Fin n)) * g
    rw [hy1]
    exact cyc3_commute_of_fixes h01 h02 h12 (hfix 0) (hfix 1) (hfix 2)
  · rw [Subgroup.zpowers_le, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro g hg
    have hfix : ∀ i, g (a i) = a i := fun i =>
      (GL83.mem_altOn.mp hg).2 (a i) (by simpa [Finset.mem_compl] using haS i)
    change g * (y2 : Perm (Fin n)) = (y2 : Perm (Fin n)) * g
    rw [hy2]
    exact cyc3_commute_of_fixes h34 h35 h45 (hfix 3) (hfix 4) (hfix 5)

theorem exists_isElemAbelian_nine_le_centralizer_altOn_compl {n : ℕ}
    {S : Finset (Fin n)} (a : Fin 6 → Fin n) (ha : Function.Injective a)
    (haS : ∀ i, a i ∈ S) :
    ∃ R : Subgroup (alternatingGroup (Fin n)),
      CFSG.Open.IsElemAbelian 3 R ∧ Nat.card R = 9 ∧
      R.map (alternatingGroup (Fin n)).subtype ≤
        Subgroup.centralizer (GL83.altOn (((Sᶜ : Finset (Fin n)) : Set (Fin n)))) := by
  classical
  let A := alternatingGroup (Fin n)
  obtain ⟨y1, y2, hy1, hy2, hcomm, hnot⟩ := exists_cyc3_pair_of_six a ha
  have h01 : a 0 ≠ a 1 := ha.ne (by decide)
  have h02 : a 0 ≠ a 2 := ha.ne (by decide)
  have h12 : a 1 ≠ a 2 := ha.ne (by decide)
  have h34 : a 3 ≠ a 4 := ha.ne (by decide)
  have h35 : a 3 ≠ a 5 := ha.ne (by decide)
  have h45 : a 4 ≠ a 5 := ha.ne (by decide)
  have hy1ord : orderOf y1 = 3 := by
    rw [show orderOf y1 = orderOf (y1 : Perm (Fin n)) from (Subgroup.orderOf_coe y1).symm]
    rw [hy1]
    exact (GL83.isThreeCycle_cyc3 ⟨h01, h02, h12⟩).orderOf
  have hy2ord : orderOf y2 = 3 := by
    rw [show orderOf y2 = orderOf (y2 : Perm (Fin n)) from (Subgroup.orderOf_coe y2).symm]
    rw [hy2]
    exact (GL83.isThreeCycle_cyc3 ⟨h34, h35, h45⟩).orderOf
  have hXcard : Nat.card (Subgroup.zpowers y1) = 3 := by
    rw [Nat.card_zpowers, hy1ord]
  have hcomm_zpowers : ∀ x ∈ Subgroup.zpowers y1, x * y2 = y2 * x := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (Commute.zpow_left (show Commute y1 y2 from hcomm) k).eq
  obtain ⟨hEA, hRcard⟩ := CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute
    (r := 3) (X := Subgroup.zpowers y1) hXcard hy2ord hnot hcomm_zpowers
  exact ⟨Subgroup.zpowers y1 ⊔ Subgroup.zpowers y2, hEA, by simpa using hRcard,
    cyc3_pair_map_le_centralizer_altOn_compl ha haS hy1 hy2⟩

theorem altOn_le_map_of_normalizer_le {n : ℕ}
    {B : Subgroup (alternatingGroup (Fin n))} {S : Finset (Fin n)}
    {R : Subgroup (alternatingGroup (Fin n))}
    (hRB : R ≤ B) (hNR : Subgroup.normalizer (R : Set _) ≤ B)
    (hcent : R.map (alternatingGroup (Fin n)).subtype ≤
      Subgroup.centralizer (GL83.altOn (((Sᶜ : Finset (Fin n)) : Set (Fin n))))) :
    GL83.altOn (((Sᶜ : Finset (Fin n)) : Set (Fin n))) ≤
      B.map (alternatingGroup (Fin n)).subtype := by
  intro g hg
  let A := alternatingGroup (Fin n)
  have hgA : g ∈ A := (GL83.mem_altOn.mp hg).1
  let k : A := ⟨g, hgA⟩
  have hcentk : k ∈ Subgroup.centralizer (R : Set A) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hrc : A.subtype r ∈
        Subgroup.centralizer (GL83.altOn (((Sᶜ : Finset (Fin n)) : Set (Fin n)))) :=
      hcent (Subgroup.mem_map_of_mem A.subtype hr)
    have hcomm : g * (r : Perm (Fin n)) = (r : Perm (Fin n)) * g :=
      (Subgroup.mem_centralizer_iff.mp hrc) g hg
    exact Subtype.ext hcomm.symm
  have hkB : k ∈ B := hNR (Subgroup.centralizer_le_normalizer (R : Set A) hcentk)
  exact Subgroup.mem_map_of_mem A.subtype hkB

theorem eq_top_of_altOn_pair_le {n : ℕ}
    {B : Subgroup (alternatingGroup (Fin n))} {F T : Finset (Fin n)}
    (hF3 : 3 ≤ (F : Set (Fin n)).ncard) (hT3 : 3 ≤ (T : Set (Fin n)).ncard)
    (hcover : ((F ∪ T : Finset (Fin n)) : Set (Fin n)) = Set.univ)
    (hFT : ((F : Set (Fin n)) ∩ (T : Set (Fin n))).Nonempty)
    (hAF : GL83.altOn (F : Set (Fin n)) ≤ B.map (alternatingGroup (Fin n)).subtype)
    (hAT : GL83.altOn (T : Set (Fin n)) ≤ B.map (alternatingGroup (Fin n)).subtype) :
    B = ⊤ := by
  classical
  let A := alternatingGroup (Fin n)
  let S : Fin 2 → Set (Fin n) := fun i => if i = 0 then (F : Set (Fin n)) else (T : Set (Fin n))
  have hS3 : ∀ i, 3 ≤ (S i).ncard := by
    intro i
    fin_cases i
    · simpa [S] using hF3
    · simpa [S] using hT3
  have hcov : (⋃ i, S i) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    have hx : x ∈ (F : Set (Fin n)) ∪ (T : Set (Fin n)) := by
      rw [← Finset.coe_union, hcover]
      exact Set.mem_univ x
    rcases (Set.mem_union x (F : Set (Fin n)) (T : Set (Fin n))).mp hx with hxF | hxT
    · exact ⟨0, by simpa [S] using hxF⟩
    · exact ⟨1, by simpa [S] using hxT⟩
  have hconn : ∀ i j : Fin 2,
      Relation.ReflTransGen (fun a b => (S a ∩ S b).Nonempty) i j := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single (by simpa [S] using hFT)
    · refine Relation.ReflTransGen.single ?_
      simpa [S, Set.inter_comm] using hFT
    · exact Relation.ReflTransGen.refl
  haveI : Nonempty (Fin n) := by
    have hpos : 0 < (F : Set (Fin n)).ncard := by omega
    obtain ⟨x, -⟩ := (Set.ncard_pos (s := (F : Set (Fin n)))).mp hpos
    exact ⟨x⟩
  have hgen := GL83.iSup_altOn_eq_alternatingGroup (S := S) hS3 hcov hconn
  have hAll : alternatingGroup (Fin n) ≤ B.map A.subtype := by
    rw [← hgen]
    refine iSup_le ?_
    intro i
    fin_cases i
    · simpa [S] using hAF
    · simpa [S] using hAT
  have hNtop : B.map A.subtype = alternatingGroup (Fin n) :=
    le_antisymm (Subgroup.map_subtype_le B) hAll
  have htopmap : (⊤ : Subgroup A).map A.subtype = alternatingGroup (Fin n) := by
    rw [← Subgroup.subgroupOf_self (H := A)]
    exact Subgroup.map_subgroupOf_eq_of_le (le_refl A)
  have hmap : B.map A.subtype = (⊤ : Subgroup A).map A.subtype := by
    rw [hNtop, htopmap]
  exact Subgroup.map_injective A.subtype_injective hmap


theorem exists_six_points_complement {n : ℕ} {F : Finset (Fin n)} (hF : 7 ≤ F.card)
    (hn6 : 3 ≤ n - 6) :
    ∃ (S6 T : Finset (Fin n)) (a : Fin 6 → Fin n),
      S6 ⊆ F ∧ S6.card = 6 ∧ T = S6ᶜ ∧ Function.Injective a ∧
      (∀ i, a i ∈ S6) ∧ 3 ≤ (F : Set (Fin n)).ncard ∧
      3 ≤ (T : Set (Fin n)).ncard ∧
      ((F : Set (Fin n)) ∩ (T : Set (Fin n))).Nonempty ∧
      ((F ∪ T : Finset (Fin n)) : Set (Fin n)) = Set.univ := by
  classical
  obtain ⟨S6, hS6F, hS6card⟩ :=
    Finset.exists_subset_card_eq (s := F) (n := 6) (by omega : 6 ≤ F.card)
  let e : ↥S6 ≃ Fin 6 := Finset.equivFinOfCardEq hS6card
  let a : Fin 6 → Fin n := fun i => (e.symm i).val
  have haS6 : ∀ i, a i ∈ S6 := fun i => (e.symm i).2
  have ha_inj : Function.Injective a := by
    intro i j hij
    exact e.symm.injective (Subtype.ext hij)
  let T : Finset (Fin n) := S6ᶜ
  have hTcard : T.card = n - 6 := by
    change (S6ᶜ).card = n - 6
    rw [Finset.card_compl, hS6card, Fintype.card_fin]
  have hF3 : 3 ≤ (F : Set (Fin n)).ncard := by
    rw [Set.ncard_eq_toFinset_card']
    simpa using (by omega : 3 ≤ F.card)
  have hT3 : 3 ≤ (T : Set (Fin n)).ncard := by
    rw [Set.ncard_eq_toFinset_card']
    have hto : ((T : Set (Fin n)).toFinset) = T := by
      ext x
      simp
    rw [hto, hTcard]
    exact hn6
  have hFT : ((F : Set (Fin n)) ∩ (T : Set (Fin n))).Nonempty := by
    have hpos : 0 < (F \ S6).card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hS6F, hS6card]
      exact Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (by norm_num : 6 < 7) hF)
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
    refine ⟨x, ?_⟩
    rw [Set.mem_inter_iff]
    refine ⟨Finset.mem_coe.mpr (Finset.mem_sdiff.mp hx).1, ?_⟩
    apply Finset.mem_coe.mpr
    change x ∈ (S6ᶜ : Finset (Fin n))
    rw [Finset.mem_compl]
    exact (Finset.mem_sdiff.mp hx).2
  have hcover : ((F ∪ T : Finset (Fin n)) : Set (Fin n)) = Set.univ := by
    ext x
    rw [Finset.coe_union, Set.mem_union]
    constructor
    · intro _
      exact Set.mem_univ x
    · intro _
      by_cases hxF : x ∈ F
      · exact Or.inl hxF
      · refine Or.inr ?_
        change x ∈ (S6ᶜ : Finset (Fin n))
        rw [Finset.mem_compl]
        exact fun hxS6 => hxF (hS6F hxS6)
  exact ⟨S6, T, a, hS6F, hS6card, rfl, ha_inj, haS6, hF3, hT3, hFT, hcover⟩

theorem eq_top_of_centralizer_le_of_normalizer_le {n : ℕ}
    {B : Subgroup (alternatingGroup (Fin n))} (c : alternatingGroup (Fin n))
    (hc7 : 7 ≤ n - (c : Equiv.Perm (Fin n)).support.card)
    (hc : Subgroup.centralizer ({c} : Set _) ≤ B)
    (hR : ∀ R : Subgroup (alternatingGroup (Fin n)), R ≤ B → CFSG.Open.IsElemAbelian 3 R →
      Nat.card R = 9 → Subgroup.normalizer (R : Set _) ≤ B) :
    B = ⊤ := by
  classical
  let A := alternatingGroup (Fin n)
  let F : Finset (Fin n) := ((c : Perm (Fin n)).supportᶜ)
  have hFcard : 7 ≤ F.card := by
    change 7 ≤ ((c : Perm (Fin n)).supportᶜ).card
    rw [Finset.card_compl, Fintype.card_fin]
    exact hc7
  by_cases hc1 : c = 1
  · have htop : Subgroup.centralizer ({c} : Set A) = ⊤ := by
      rw [hc1]
      simp
    exact top_le_iff.mp (htop ▸ hc)
  · have hc1' : (c : Perm (Fin n)) ≠ 1 := fun h => hc1 (Subtype.ext h)
    have hsign : Equiv.Perm.sign (c : Perm (Fin n)) = 1 :=
      Equiv.Perm.mem_alternatingGroup.mp c.2
    have hsupp3 : 3 ≤ (c : Perm (Fin n)).support.card :=
      three_le_card_support_of_ne_one hsign hc1'
    have hAF := altOn_support_compl_le_map c hc
    have hsupple : (c : Perm (Fin n)).support.card ≤ n := by
      simpa using Finset.card_le_univ (c : Perm (Fin n)).support
    have hn6 : 3 ≤ n - 6 := by omega
    obtain ⟨S6, T, a, hS6F, hS6card, hT, ha_inj, haS6, hF3, hT3, hFT, hcover⟩ :=
      exists_six_points_complement hFcard hn6
    subst T
    obtain ⟨R, hEA, hRcard, hRcent⟩ :=
      exists_isElemAbelian_nine_le_centralizer_altOn_compl a ha_inj haS6
    have hc_altOn : (c : Perm (Fin n)) ∈
        GL83.altOn (((S6ᶜ : Finset (Fin n)) : Set (Fin n))) := by
      rw [GL83.mem_altOn]
      refine ⟨c.2, ?_⟩
      intro x hx
      have hxS6 : x ∈ S6 := by
        by_contra hxS6
        exact hx (by simp [Finset.mem_compl, hxS6])
      have hxF : x ∈ F := hS6F hxS6
      exact Equiv.Perm.notMem_support.mp (by simpa [F] using hxF)
    have hRleC : R ≤ Subgroup.centralizer ({c} : Set A) := by
      intro r hr
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hrc : A.subtype r ∈
          Subgroup.centralizer (GL83.altOn (((S6ᶜ : Finset (Fin n)) : Set (Fin n)))) :=
        hRcent (Subgroup.mem_map_of_mem A.subtype hr)
      have hcomm : (c : Perm (Fin n)) * (r : Perm (Fin n)) =
          (r : Perm (Fin n)) * (c : Perm (Fin n)) :=
        (Subgroup.mem_centralizer_iff.mp hrc) (c : Perm (Fin n)) hc_altOn
      exact Subtype.ext hcomm.symm
    have hRleB : R ≤ B := hRleC.trans hc
    have hNR : Subgroup.normalizer (R : Set A) ≤ B :=
      hR R hRleB hEA (by simpa using hRcard)
    have hAT : GL83.altOn (((S6ᶜ : Finset (Fin n)) : Set (Fin n))) ≤ B.map A.subtype :=
      altOn_le_map_of_normalizer_le (B := B) (S := S6) (R := R) hRleB hNR hRcent
    exact eq_top_of_altOn_pair_le hF3 hT3 hcover hFT hAF hAT

theorem exists_isElemAbelian_nine_le_centralizer {n : ℕ} (c : alternatingGroup (Fin n))
    (hc6 : 6 ≤ n - (c : Equiv.Perm (Fin n)).support.card) :
    ∃ R : Subgroup (alternatingGroup (Fin n)), R ≤ Subgroup.centralizer ({c} : Set _) ∧
      CFSG.Open.IsElemAbelian 3 R ∧ Nat.card R = 9 := by
  classical
  let A := alternatingGroup (Fin n)
  let F : Finset (Fin n) := ((c : Perm (Fin n)).supportᶜ)
  have hFcard : 6 ≤ F.card := by
    change 6 ≤ ((c : Perm (Fin n)).supportᶜ).card
    rw [Finset.card_compl, Fintype.card_fin]
    exact hc6
  obtain ⟨S6, hS6F, hS6card⟩ :=
    Finset.exists_subset_card_eq (s := F) (n := 6) hFcard
  let e : ↥S6 ≃ Fin 6 := Finset.equivFinOfCardEq hS6card
  let a : Fin 6 → Fin n := fun i => (e.symm i).val
  have haS6 : ∀ i, a i ∈ S6 := fun i => (e.symm i).2
  have ha_inj : Function.Injective a := by
    intro i j hij
    exact e.symm.injective (Subtype.ext hij)
  obtain ⟨R, hEA, hRcard, hRcent⟩ :=
    exists_isElemAbelian_nine_le_centralizer_altOn_compl a ha_inj haS6
  refine ⟨R, ?_, hEA, hRcard⟩
  have hc_altOn : (c : Perm (Fin n)) ∈
      GL83.altOn (((S6ᶜ : Finset (Fin n)) : Set (Fin n))) := by
    rw [GL83.mem_altOn]
    refine ⟨c.2, ?_⟩
    intro x hx
    have hxS6 : x ∈ S6 := by
      by_contra hxS6
      exact hx (by simp [Finset.mem_compl, hxS6])
    have hxF : x ∈ F := hS6F hxS6
    exact Equiv.Perm.notMem_support.mp (by simpa [F] using hxF)
  intro r hr
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hrc : A.subtype r ∈
      Subgroup.centralizer (GL83.altOn ((S6ᶜ : Finset (Fin n)) : Set (Fin n))) :=
    hRcent (Subgroup.mem_map_of_mem A.subtype hr)
  have hcomm : (c : Perm (Fin n)) * (r : Perm (Fin n)) =
      (r : Perm (Fin n)) * (c : Perm (Fin n)) :=
    (Subgroup.mem_centralizer_iff.mp hrc) (c : Perm (Fin n)) hc_altOn
  exact Subtype.ext hcomm.symm

theorem eq_top_of_sylow_le_of_normalizer_le {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p)
    {B : Subgroup (alternatingGroup (Fin (2 * p)))} (P : Sylow p (alternatingGroup (Fin (2 * p))))
    (hPB : (P : Subgroup _) ≤ B)
    (hp : ∀ R : Subgroup (alternatingGroup (Fin (2 * p))), R ≤ B → IsPGroup p R → R ≠ ⊥ →
      Subgroup.normalizer (R : Set _) ≤ B)
    (h3 : ∀ R : Subgroup (alternatingGroup (Fin (2 * p))), R ≤ B → CFSG.Open.IsElemAbelian 3 R →
      Nat.card R = 9 → Subgroup.normalizer (R : Set _) ≤ B) :
    B = ⊤ := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hpn : p ≤ 2 * p := by omega
  obtain ⟨c, hcB, hccyc, hccard⟩ := exists_isCycle_mem_of_sylow_le hp2 hpn P hPB
  let A := alternatingGroup (Fin (2 * p))
  let R : Subgroup A := Subgroup.zpowers c
  have hRcard : Nat.card R = p := by
    change Nat.card (Subgroup.zpowers c) = p
    rw [Nat.card_zpowers]
    have hcoe : orderOf c = orderOf (c : Perm (Fin (2 * p))) := (Subgroup.orderOf_coe c).symm
    rw [hcoe, hccyc.orderOf, hccard]
  have hRisP : IsPGroup p R := IsPGroup.of_card (n := 1) (by simpa using hRcard)
  have hc_ne : c ≠ 1 := by
    intro hc1
    have hzero : (c : Perm (Fin (2 * p))).support.card = 0 := by
      rw [hc1]
      simp
    rw [hccard] at hzero
    omega
  have hRne : R ≠ ⊥ := by
    intro hbot
    exact hc_ne (Subgroup.zpowers_eq_bot.mp (by simpa [R] using hbot))
  have hRleB : R ≤ B := by
    change Subgroup.zpowers c ≤ B
    exact Subgroup.zpowers_le.mpr hcB
  have hNR : Subgroup.normalizer (R : Set A) ≤ B := hp R hRleB hRisP hRne
  have hcentR : Subgroup.centralizer ((R : Subgroup A) : Set A) ≤ B :=
    (Subgroup.centralizer_le_normalizer (R : Set A)).trans hNR
  have heq : Subgroup.centralizer ((R : Subgroup A) : Set A) =
      Subgroup.centralizer ({c} : Set A) := by
    change Subgroup.centralizer ((Subgroup.zpowers c : Subgroup A) : Set A) =
      Subgroup.centralizer ({c} : Set A)
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [heq] at hcentR
  have hc7 : 7 ≤ 2 * p - (c : Perm (Fin (2 * p))).support.card := by
    rw [hccard]
    omega
  exact eq_top_of_centralizer_le_of_normalizer_le (n := 2 * p) c hc7 hcentR h3


end CFSG.AltLocalClosure
