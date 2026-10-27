module

public import CFSG.GroupTheory.ExtraspecialThreeFive
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K2LieAbstract
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K4143Reduce
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneFourteenTen
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactAutAlt
import CFSG.Adapters.StatedClassicalOrders
import CFSG.Adapters.StatedClassicalUnitaryOrders
import CFSG.RankThree.PartOne.N143.Inspect613Even

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup

theorem card_le_three_mul_card_inf_innAut_of_outPNice {Y : Type} [Group Y] [Finite Y]
    (h : CFSG.RankThree.PartOne.OutStructure.OutPNice 3 Y) {S : Subgroup (MulAut Y)}
    (hS : ∀ s ∈ S, s ^ 3 = 1) :
    Nat.card S ≤
      3 * Nat.card (S ⊓ CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.innAut Y :
        Subgroup (MulAut Y)) := by
  classical
  by_cases hSInn : S ≤ CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.innAut Y
  · have hinf : S ⊓ CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.innAut Y = S :=
      inf_eq_left.mpr hSInn
    rw [hinf]
    have hpos : 0 < Nat.card S := Nat.card_pos
    omega
  · obtain ⟨φ, hφS, hφI⟩ := Set.not_subset.mp hSInn
    have hφ3 : φ ^ 3 = 1 := hS φ hφS
    have hBNC : ∀ b ∈ S, ∃ n ∈ CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.innAut Y,
        ∃ c ∈ Subgroup.zpowers φ, b = n * c := by
      intro b hb
      obtain ⟨D, -, hInnD, hD3, m, hmD⟩ :=
        CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.exists_normal_of_outPNice h
          ⟨1, by rw [pow_one]; exact hφ3⟩ hφI (hS b hb)
      have hbφ : b * φ ^ m ∈ S := S.mul_mem hb (S.zpow_mem hφS m)
      have h3 : (b * φ ^ m) ^ 3 = 1 := hS _ hbφ
      have hInn : b * φ ^ m ∈
          CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.innAut Y :=
        hD3 _ hmD 1 (by simpa [h3] using (Subgroup.one_mem
          (CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.innAut Y)))
      refine ⟨b * φ ^ m, hInn, φ ^ (-m),
        (Subgroup.zpowers φ).zpow_mem (Subgroup.mem_zpowers φ) (-m), ?_⟩
      group
    have hC : IsCyclic (Subgroup.zpowers φ) := Subgroup.isCyclic_zpowers φ
    have hnormal : (CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.innAut Y).Normal :=
      CFSG.ComponentClassification.OuterAutomorphisms.inner_normal Y
    haveI := hnormal
    have hCN : Subgroup.zpowers φ ≤
        Subgroup.normalizer
          (CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.innAut Y : Set (MulAut Y)) :=
      Subgroup.le_normalizer_of_normal
    exact CFSG.GroupTheory.ExtraspecialThreeFive.card_le_three_mul_card_inf_of_pow_three
      (B := S) (N := CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.innAut Y)
      (C := Subgroup.zpowers φ) hS hC hCN hBNC

theorem isThreeOnePlusFour_map_of_injOn {A B : Type} [Group A] [Group B] (f : A →* B)
    {R : Subgroup A} (hinj : ∀ x ∈ R, f x = 1 → x = 1)
    (hR : CFSG.LocalAnalysis.RankThreeUC.S15.IsThreeOnePlusFour ↥R) :
    CFSG.LocalAnalysis.RankThreeUC.S15.IsThreeOnePlusFour ↥(R.map f) := by
  let fR : ↥R →* ↥(R.map f) := f.subgroupMap R
  have hfR : Function.Injective fR := by
    intro a b hab
    apply Subtype.ext
    have h1 : f ((a : A)⁻¹ * (b : A)) = 1 := by
      have h2 : f (a : A) = f (b : A) := congrArg Subtype.val hab
      rw [map_mul, map_inv, h2, inv_mul_cancel]
    have h2 : (a : A)⁻¹ * (b : A) ∈ R := R.mul_mem (R.inv_mem a.2) b.2
    exact inv_mul_eq_one.mp (hinj _ h2 h1)
  let e : ↥R ≃* ↥(R.map f) :=
    MulEquiv.ofBijective fR ⟨hfR, MonoidHom.subgroupMap_surjective f R⟩
  exact isThreeOnePlusFour_of_mulEquiv e hR

theorem le_of_map_conjNormal_le_innAut {X : Type} [Group X] {L : Subgroup X} [L.Normal]
    {R : Subgroup X}
    (hle : R.map (MulAut.conjNormal (H := L)) ≤
      CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.innAut ↥L)
    (hsup : ∀ x ∈ R, x ∈ L ⊔ Subgroup.centralizer (L : Set X) → x ∈ L) : R ≤ L := by
  intro x hx
  have hmem : MulAut.conjNormal (H := L) x ∈
      CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.innAut ↥L :=
    hle (Subgroup.mem_map_of_mem (MulAut.conjNormal (H := L)) hx)
  obtain ⟨l, hl⟩ := hmem
  have hc : (l : X)⁻¹ * x ∈ Subgroup.centralizer (L : Set X) :=
    CFSG.LocalAnalysis.RankThreeUC.S15.K4143K2.inv_mul_mem_centralizer_of_conj_eq hl
  apply hsup x hx
  have hxeq : x = (l : X) * ((l : X)⁻¹ * x) := by group
  rw [hxeq]
  exact mul_mem (Subgroup.mem_sup_left l.2) (Subgroup.mem_sup_right hc)

theorem card_le_three_mul_card_inf_of_outPNice {X : Type} [Group X] [Finite X]
    {L : Subgroup X} [L.Normal]
    (h : CFSG.RankThree.PartOne.OutStructure.OutPNice 3 ↥L) {R : Subgroup X}
    (hexp : ∀ x ∈ R, x ^ 3 = 1)
    (hinj : ∀ x ∈ R, x ∈ Subgroup.centralizer (L : Set X) → x = 1)
    (hsup : ∀ x ∈ R, x ∈ L ⊔ Subgroup.centralizer (L : Set X) → x ∈ L) :
    Nat.card R ≤ 3 * Nat.card (R ⊓ L : Subgroup X) := by
  classical
  let c : X →* MulAut ↥L := MulAut.conjNormal (H := L)
  have hcInj : Function.Injective (c.subgroupMap R) := by
    intro a b hab
    apply Subtype.ext
    have h1 : c ((a : X)⁻¹ * (b : X)) = 1 := by
      have h2 : c (a : X) = c (b : X) := congrArg Subtype.val hab
      rw [map_mul, map_inv, h2, inv_mul_cancel]
    have h2 : (a : X)⁻¹ * (b : X) ∈ Subgroup.centralizer (L : Set X) :=
      (CFSG.LocalAnalysis.RankThreeUC.S15.K4143K2.conjNormal_eq_one_iff_mem_centralizer L).mp h1
    have h3 : (a : X)⁻¹ * (b : X) ∈ R := R.mul_mem (R.inv_mem a.2) b.2
    exact inv_mul_eq_one.mp (hinj _ h3 h2)
  let eR : ↥R ≃* ↥(R.map c) :=
    MulEquiv.ofBijective (c.subgroupMap R) ⟨hcInj, MonoidHom.subgroupMap_surjective c R⟩
  have hcardMap : Nat.card (R.map c) = Nat.card R := (Nat.card_congr eR.toEquiv).symm
  have hS : ∀ s ∈ R.map c, s ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hexp x hx, map_one]
  have hA := card_le_three_mul_card_inf_innAut_of_outPNice h hS
  have hInt : (R.map c) ⊓ CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.innAut ↥L =
      (R ⊓ L).map c := by
    ext y
    constructor
    · rintro ⟨hyMap, hyInn⟩
      obtain ⟨x, hxR, rfl⟩ := Subgroup.mem_map.mp hyMap
      obtain ⟨l, hl⟩ := hyInn
      have hc : (l : X)⁻¹ * x ∈ Subgroup.centralizer (L : Set X) :=
        CFSG.LocalAnalysis.RankThreeUC.S15.K4143K2.inv_mul_mem_centralizer_of_conj_eq hl
      have hxSup : x ∈ L ⊔ Subgroup.centralizer (L : Set X) := by
        have hxeq : x = (l : X) * ((l : X)⁻¹ * x) := by group
        rw [hxeq]
        exact mul_mem (Subgroup.mem_sup_left l.2) (Subgroup.mem_sup_right hc)
      exact Subgroup.mem_map_of_mem c ⟨hxR, hsup x hxR hxSup⟩
    · rintro ⟨x, ⟨hxR, hxL⟩, rfl⟩
      refine ⟨Subgroup.mem_map_of_mem c hxR, ?_⟩
      refine ⟨⟨x, hxL⟩, ?_⟩
      exact (MulAut.conjNormal_val (H := L) (h := ⟨x, hxL⟩)).symm
  have hleMap : Nat.card ((R ⊓ L).map c) ≤ Nat.card (R ⊓ L : Subgroup X) :=
    Nat.le_of_dvd (Nat.card_pos (α := ↥(R ⊓ L)))
      (Subgroup.card_map_dvd (R ⊓ L) c)
  calc Nat.card R = Nat.card (R.map c) := hcardMap.symm
    _ ≤ 3 * Nat.card ((R.map c) ⊓
          CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.innAut ↥L :
            Subgroup (MulAut ↥L)) := hA
    _ = 3 * Nat.card ((R ⊓ L).map c) := by rw [hInt]
    _ ≤ 3 * Nat.card (R ⊓ L : Subgroup X) := Nat.mul_le_mul_left 3 hleMap

theorem three_le_pRank_of_outPNice {X : Type} [Group X] [Finite X] {L : Subgroup X} [L.Normal]
    (h : CFSG.RankThree.PartOne.OutStructure.OutPNice 3 ↥L)
    (hC : Subgroup.centralizer (L : Set X) = ⊥) {R : Subgroup X}
    (hR : CFSG.LocalAnalysis.RankThreeUC.S15.IsThreeOnePlusFour ↥R) :
    3 ≤ CFSG.Open.pRank 3 L := by
  obtain ⟨hcard, hexp, hZ, hcomm⟩ := hR
  have hexpR : ∀ x ∈ R, x ^ 3 = 1 := by
    intro x hx
    have hx3 := hexp ⟨x, hx⟩
    exact congrArg Subtype.val hx3
  have hinj : ∀ x ∈ R, x ∈ Subgroup.centralizer (L : Set X) → x = 1 := by
    intro x _ hx
    rw [hC] at hx
    exact Subgroup.mem_bot.mp hx
  have hsup : ∀ x ∈ R, x ∈ L ⊔ Subgroup.centralizer (L : Set X) → x ∈ L := by
    intro x _ hx
    rwa [hC, sup_bot_eq] at hx
  have hle := card_le_three_mul_card_inf_of_outPNice h hexpR hinj hsup
  obtain ⟨E, hE, hEea, hEcard⟩ :=
    CFSG.GroupTheory.ExtraspecialThreeFive.exists_elemAbelian_27_le_inf
      (R := R) (N := L) hcard hexp hZ hcomm hle
  exact CFSG.SectionRank.le_pRank (p := 3) (by norm_num) (hE.trans inf_le_right) hEea
    (by rw [hEcard]; norm_num)

theorem mem_innAut_of_pow_three_eq_one {S : Type} [Group S] {φ : MulAut S}
    (h3 : φ ^ 3 = 1)
    (h2 : ∃ k : ℕ,
      φ ^ (2 ^ k) ∈ CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.innAut S) :
    φ ∈ CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.innAut S := by
  obtain ⟨k, hk⟩ := h2
  have hdvd : orderOf φ ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hcop : Nat.Coprime (2 ^ k) (orderOf φ) :=
    (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)).coprime_dvd_right hdvd
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact pow_mem hk m

private theorem not_dvd_three_pow_five_mulAut_alt {n : ℕ}
    (hn : n = 5 ∨ n = 6 ∨ n = 8) :
    ¬ 3 ^ 5 ∣ Nat.card (MulAut (alternatingGroup (Fin n))) := by
  rintro hdvd
  rcases hn with rfl | rfl | rfl
  · rw [CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.card_mulAut_alternatingGroup_eq_factorial
      5 (by norm_num) (by norm_num)] at hdvd
    norm_num [Nat.factorial] at hdvd
  · have hdiv :=
      CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.card_mulAut_alternatingGroup_six_dvd_two_mul
    exact (by norm_num : ¬ 3 ^ 5 ∣ 2 * Nat.factorial 6) (hdvd.trans hdiv)
  · rw [CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.card_mulAut_alternatingGroup_eq_factorial
      8 (by norm_num) (by norm_num)] at hdvd
    norm_num [Nat.factorial] at hdvd

private theorem card_psl_two_seven {S : Type} [Group S]
    (h : CFSG.Open.StatedClassicalModel S .PSL 2 7 1) : Nat.card S = 168 := by
  rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl (by norm_num) h]
  norm_num

theorem false_of_le_mulAut_small {S : Type} [Group S] [Finite S]
    (hS : (∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 8) ∧
        Nonempty (S ≃* alternatingGroup (Fin n))) ∨
      ∃ d : TauCeti.ValidLieTypeIndex,
        ((∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q) ∨
          (∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .twistedA 2 q)) ∧
        Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group))
    {T : Subgroup (MulAut S)} (hcard : Nat.card T = 3 ^ 5)
    (hexp : ∀ t ∈ T, t ^ 3 = 1) : False := by
  classical
  rcases hS with ⟨n, hn, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
  · have hdvd : 3 ^ 5 ∣ Nat.card (MulAut S) := by
      rw [← hcard]
      exact Subgroup.card_subgroup_dvd_card T
    have hcardMul : Nat.card (MulAut S) =
        Nat.card (MulAut (alternatingGroup (Fin n))) :=
      Nat.card_congr (MulAut.congr e).toEquiv
    rw [hcardMul] at hdvd
    exact not_dvd_three_pow_five_mulAut_alt hn hdvd
  · obtain ⟨d1, hv⟩ := d
    have hlist : CFSG.LocalAnalysis.RankThreeUC.S15.IsOutTwoGroupList S := by
      rcases hd with ⟨q, hq, hd1⟩ | ⟨q, hq, hd1⟩
      · exact Or.inr (Or.inr ⟨⟨d1, hv⟩, Or.inr (Or.inr ⟨q, hq, hd1⟩), ⟨e⟩⟩)
      · exact Or.inr (Or.inr ⟨⟨d1, hv⟩, Or.inr (Or.inl ⟨q, hq, hd1⟩), ⟨e⟩⟩)
    have hTle : T ≤ CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.innAut S := by
      intro t ht
      have hout : ∃ k : ℕ, t ^ (2 ^ k) ∈
          CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.innAut S :=
        CFSG.LocalAnalysis.RankThreeUC.S15.KOut_holds S hlist t
      exact mem_innAut_of_pow_three_eq_one (hexp t ht) hout
    have hdvdInn : 3 ^ 5 ∣
        Nat.card (CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.innAut S) := by
      have h := Subgroup.card_dvd_of_le hTle
      rwa [hcard] at h
    have hdvdS : 3 ^ 5 ∣ Nat.card S :=
      hdvdInn.trans (Subgroup.card_range_dvd (MulAut.conj : S →* MulAut S))
    rcases hd with ⟨q, hq, hd1⟩ | ⟨q, hq, hd1⟩
    · simp only at hd1
      subst hd1
      have hm := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
      have hq' : q.p ^ q.exponent = 7 := by
        rw [← TauCeti.PrimePower.card_def]
        exact hq
      obtain ⟨hp7, he1⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 7)).mp hq'
      rw [hp7, he1] at hm
      have hcardS : Nat.card S = 168 := card_psl_two_seven hm
      rw [hcardS] at hdvdS
      exact (by norm_num : ¬ 3 ^ 5 ∣ 168) hdvdS
    · simp only at hd1
      subst hd1
      have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
      have hq' : q.p ^ q.exponent = 3 := by
        rw [← TauCeti.PrimePower.card_def]
        exact hq
      obtain ⟨hp3, he1⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 3)).mp hq'
      rw [hp3, he1] at hm
      have hcardS : Nat.card S = 6048 :=
        CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three hm
      rw [hcardS] at hdvdS
      exact (by norm_num : ¬ 3 ^ 5 ∣ 6048) hdvdS

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
