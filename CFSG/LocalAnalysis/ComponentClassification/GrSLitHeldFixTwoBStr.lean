module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixTwoBCheck
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixSylow
public import CFSG.Sporadic.SmallOddCore.HeLocal

public noncomputable section

namespace CFSG.ComponentClassification.GrSLit.HeldFix

open scoped commutatorElement
open CFSG Subgroup CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SuzOddCore CFSG.Sporadic.HeldB CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier

@[expose] def hfCW (w : List ℕ) : Equiv.Perm (Fin 8330) := (w.map heInnerCP1).prod

theorem hfCW_mem {w : List ℕ} (hw : ∀ j ∈ w, j < 9) : hfCW w ∈ heInnerGrp1 := by
  refine heInnerGrp1.list_prod_mem fun x hx => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  exact heInnerCP1_mem_grp1 (hw j hj)

theorem tabRep_hfCTab {w : List ℕ} (hw : ∀ j ∈ w, j < 9) : TabRep (hfCTab w) (hfCW w) :=
  tabRep_wordTabS tabRep_hfC1Tabs w fun j hj => by simpa [hfC1Tabs] using hw j hj

theorem heRho1_c {j : ℕ} (hj : j < 9) :
    heRho1 ⟨heInnerCP1 j, heInnerCP1_mem_grp1 hj⟩ = heInnerSigmaP1 j :=
  restrictHom_eq_of_agree heDelta1_injective heInnerGrp1_stab _ (heInnerCP1_agree hj)

theorem heRho1_word : ∀ (w : List ℕ) (hw : ∀ j ∈ w, j < 9),
    heRho1 ⟨hfCW w, hfCW_mem hw⟩ = (w.map heInnerSigmaP1).prod
  | [], _ => by
    have e : (⟨hfCW [], hfCW_mem (w := []) (by simp)⟩ : heInnerGrp1) = 1 :=
      Subtype.ext (by simp [hfCW])
    rw [e, map_one]
    simp
  | j :: w, hw => by
    have hj : j < 9 := hw j List.mem_cons_self
    have hw' : ∀ i ∈ w, i < 9 := fun i hi => hw i (List.mem_cons_of_mem _ hi)
    have e : (⟨hfCW (j :: w), hfCW_mem hw⟩ : heInnerGrp1) =
        ⟨heInnerCP1 j, heInnerCP1_mem_grp1 hj⟩ * ⟨hfCW w, hfCW_mem hw'⟩ :=
      Subtype.ext (by simp [hfCW])
    rw [e, map_mul, heRho1_word w hw', heRho1_c hj, List.map_cons, List.prod_cons]

theorem tabRep_hfCTab42 {w : List ℕ} (hw : ∀ j ∈ w, j < 9) :
    TabRep (hfCTab42 w) (heRho1 ⟨hfCW w, hfCW_mem hw⟩) := by
  rw [heRho1_word w hw]
  exact tabRep_wordTabS tabRep_heXTabs w fun j hj => by simpa [heXTabs] using hw j hj

theorem hfCW_rep (k : ℕ) (w : List ℕ) : hfCW (hfRep k w) = hfCW w ^ k := by
  induction k with
  | zero => simp [hfCW, hfRep]
  | succ k ih =>
    rw [pow_succ', ← ih]
    simp only [hfCW, hfRep, List.replicate_succ, List.flatten_cons, List.map_append,
      List.prod_append]

@[expose] def hfT1C : heInnerGrp1 := ⟨heT1P, heT1P_mem_grp1⟩

theorem hfT1C_mem_ker : hfT1C ∈ heRho1.ker := by
  rw [MonoidHom.mem_ker, heRho1, restrictHom_eq_one_iff]
  exact heT1P_fix

theorem hfT1C_sq' : hfT1C * hfT1C = 1 :=
  Subtype.ext (by
    show heT1P * heT1P = 1
    rw [← pow_two, ← orderOf_heT1P, pow_orderOf_eq_one])

theorem mem_ker_heRho1 {c : heInnerGrp1} (hc : c ∈ heRho1.ker) : c = 1 ∨ c = hfT1C := by
  have hT1 : hfT1C ≠ 1 := fun h' => heT1P_ne_one (congrArg Subtype.val h')
  have hle : zpowers hfT1C ≤ heRho1.ker := by rw [zpowers_le]; exact hfT1C_mem_ker
  have hcard : Nat.card (zpowers hfT1C) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hfT1C_sq') hT1
  have heq : zpowers hfT1C = heRho1.ker :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, card_heRho1_ker])
  rw [← heq] at hc
  exact mem_zpowers_of_involution hfT1C_sq' hc

theorem hfT1C_central (c : heInnerGrp1) : c * hfT1C = hfT1C * c := by
  apply Subtype.ext
  have := (mem_inf.1 (heInnerGrp1_le c.2)).2
  exact mem_centralizer_singleton_iff.1 this

theorem card_heRho1_range : Nat.card heRho1.range = 10752 := by
  rw [heRho1_range, heX_enumerates.card, Array.length_toList, he2_X.2.1]

theorem eq_top_of_map_heRho1 {K : Subgroup heInnerGrp1} (hK : hfT1C ∈ K)
    (hmap : heRho1.range ≤ K.map heRho1) : K = ⊤ := by
  rw [eq_top_iff]
  intro c _
  obtain ⟨d, hd, hdc⟩ := hmap ⟨c, rfl⟩
  have hker : d⁻¹ * c ∈ heRho1.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hdc, inv_mul_cancel]
  rcases mem_ker_heRho1 hker with h | h
  · rw [inv_mul_eq_one] at h
    rw [← h]
    exact hd
  · have : c = d * hfT1C := by rw [← h]; group
    rw [this]
    exact K.mul_mem hd hK

theorem range_le_map_of_enum {K : Subgroup heInnerGrp1} {gs : Array Tab}
    {f : ℕ → heInnerGrp1} (hgs : ∀ j < gs.size, TabRep gs[j]! (heRho1 (f j)))
    (hfK : ∀ j < gs.size, f j ∈ K) {E : Enum} (hE : enumOK 42 gs E = true)
    (hsize : E.tabs.size = 10752) : heRho1.range ≤ K.map heRho1 := by
  have henum := enumerates_closure (genGroup_hA hgs) (genGroup_hgens hgs) hE
  have hle : genGroup 42 gs (fun j => heRho1 (f j)) ≤ K.map heRho1 := by
    rw [genGroup, closure_le]
    rintro _ ⟨j, hj, rfl⟩
    exact ⟨f j, hfK j hj, rfl⟩
  have hle' : genGroup 42 gs (fun j => heRho1 (f j)) ≤ heRho1.range := by
    rw [genGroup, closure_le]
    rintro _ ⟨j, hj, rfl⟩
    exact ⟨f j, rfl⟩
  have heq : genGroup 42 gs (fun j => heRho1 (f j)) = heRho1.range :=
    Subgroup.eq_of_le_of_card_ge hle' (by
      rw [card_heRho1_range, henum.card, Array.length_toList, hsize])
  rw [← heq]
  exact hle

theorem hfQ_mem {i : ℕ} (hi : i < 2) : hfCW (hfQWords.getD i []) ∈ heInnerGrp1 :=
  hfCW_mem (hfTwoB_check.1 i hi)

theorem hfComm_mem {i : ℕ} (hi : i < 6) : hfCW (hfCommWords.getD i []) ∈ heInnerGrp1 :=
  hfCW_mem (hfTwoB_check.2.1 i hi)

@[expose] def hfCommC (i : ℕ) : heInnerGrp1 :=
  if hi : i < 3 then
    ⁅(⟨_, hfComm_mem (i := 2 * i) (by omega)⟩ : heInnerGrp1),
      ⟨_, hfComm_mem (i := 2 * i + 1) (by omega)⟩⁆
  else 1

theorem tabRep_hfCommTabs42 :
    ∀ i < hfCommTabs42.size, TabRep hfCommTabs42[i]! (heRho1 (hfCommC i)) := by
  intro i hi
  have hi3 : i < 3 := by simpa [hfCommTabs42] using hi
  rw [hfCommTabs42, getElem!_pos _ i (by simpa using hi3), Array.getElem_ofFn]
  simp only [hfCommC, hi3, ↓reduceDIte]
  rw [map_commutatorElement]
  have hx := tabRep_hfCTab42 (hfTwoB_check.2.1 (2 * i) (by omega))
  have hy := tabRep_hfCTab42 (hfTwoB_check.2.1 (2 * i + 1) (by omega))
  obtain ⟨hxi1, hxi2⟩ := hfTwoB_check.2.2.2.2.2.2.2.2.2.1 (2 * i) (by omega)
  obtain ⟨hyi1, hyi2⟩ := hfTwoB_check.2.2.2.2.2.2.2.2.2.1 (2 * i + 1) (by omega)
  exact hx.commTab hy (hx.inv hxi2 hxi1) (hy.inv hyi2 hyi1)

theorem perfect_heInnerGrp1 :
    ⁅(⊤ : Subgroup heInnerGrp1), (⊤ : Subgroup heInnerGrp1)⁆ = ⊤ := by
  apply eq_top_of_map_heRho1
  · have hq0 := hfQ_mem (i := 0) (by norm_num)
    have hq1 := hfQ_mem (i := 1) (by norm_num)
    have hc : ⁅(⟨_, hq0⟩ : heInnerGrp1), ⟨_, hq1⟩⁆ = hfT1C := by
      apply Subtype.ext
      have h0 := tabRep_hfCTab (hfTwoB_check.1 0 (by norm_num))
      have h1 := tabRep_hfCTab (hfTwoB_check.1 1 (by norm_num))
      have h0i := rep_inv_of_isInvA h0.2 hfTwoB_check.2.2.2.2.1
      have h1i := rep_inv_of_isInvA h1.2 hfTwoB_check.2.2.2.2.2.1
      have hrep := tabRep_comp_of_rep (rep_comp (rep_comp h0.2 h1.2) h0i) h1i
      have ht := tabRep_of_rep rep_heT1 hfSylow_check.2.1
      have := (hrep.eq_iff ht).1 hfTwoB_check.2.2.2.2.2.2.1
      simpa [commutatorElement_def, hfT1C] using this
    rw [← hc]
    exact commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  · exact range_le_map_of_enum tabRep_hfCommTabs42 (fun i hi => by
      have hi3 : i < 3 := by simpa [hfCommTabs42] using hi
      simp only [hfCommC, hi3, ↓reduceDIte]
      exact commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
      hfTwoB_check.2.2.2.2.2.2.2.2.2.2.1 hfTwoB_check.2.2.2.2.2.2.2.2.2.2.2.1

theorem perfect_centralizer_heT1P :
    ⁅centralizerIn heP heT1P, centralizerIn heP heT1P⁆ = centralizerIn heP heT1P := by
  rw [← heInnerGrp1_eq, ← Subgroup.map_subtype_commutator, _root_.commutator_def,
    perfect_heInnerGrp1, Subgroup.map_top, range_subtype]

theorem heT1P_sq : heT1P * heT1P = 1 := by
  rw [← pow_two, ← orderOf_heT1P, pow_orderOf_eq_one]

theorem eq_top_of_normal_of_enum {N : Subgroup heInnerGrp1} (hN : N.Normal) {gs : Array Tab}
    {f : ℕ → heInnerGrp1} (hgs : ∀ j < gs.size, TabRep gs[j]! (heRho1 (f j)))
    (hfN : ∀ j < gs.size, f j ∈ N) {E : Enum} (hE : enumOK 42 gs E = true)
    (hsize : E.tabs.size = 10752) : N = ⊤ := by
  have hmap := range_le_map_of_enum hgs hfN hE hsize
  have hq : ∀ c : heInnerGrp1, (QuotientGroup.mk' N) c = 1 ∨
      (QuotientGroup.mk' N) c = (QuotientGroup.mk' N) hfT1C := by
    intro c
    obtain ⟨d, hd, hdc⟩ := hmap ⟨c, rfl⟩
    have hker : d⁻¹ * c ∈ heRho1.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hdc, inv_mul_cancel]
    have hd1 : (QuotientGroup.mk' N) d = 1 := (QuotientGroup.eq_one_iff d).2 hd
    rcases mem_ker_heRho1 hker with h | h
    · left
      rw [inv_mul_eq_one] at h
      rw [← h, hd1]
    · right
      have e : c = d * hfT1C := by rw [← h]; group
      rw [e, map_mul, hd1, one_mul]
  have hcomm : ⁅(⊤ : Subgroup heInnerGrp1), (⊤ : Subgroup heInnerGrp1)⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement]
    rcases hq a with ha | ha <;> rcases hq b with hb | hb <;>
      simp [ha, hb, commutatorElement_def]
  rw [eq_top_iff, ← perfect_heInnerGrp1]
  exact hcomm

theorem mem_of_normal_of_dvd {N : Subgroup heInnerGrp1} (hN : N.Normal) {p : ℕ} [Fact p.Prime]
    (hp : p ∣ Nat.card N) (hpC : p ^ (Nat.card heInnerGrp1).factorization p = p)
    {w : heInnerGrp1} (hw : orderOf w = p) : w ∈ N := by
  obtain ⟨n, hn⟩ := exists_prime_orderOf_dvd_card' p hp
  have hS : Nat.card (zpowers (n : heInnerGrp1)) =
      p ^ (Nat.card (⊤ : Subgroup heInnerGrp1)).factorization p := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hn, Subgroup.card_top, hpC]
  have hT : Nat.card (zpowers w) = Nat.card (zpowers (n : heInnerGrp1)) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, Subgroup.orderOf_coe, hn, hw]
  obtain ⟨g, -, hg⟩ := exists_conj_eq_map_of_card le_top le_top hS hT
  have hwT : w ∈ zpowers w := mem_zpowers w
  rw [hg] at hwT
  obtain ⟨y, hy, rfl⟩ := hwT
  obtain ⟨k, rfl⟩ := hy
  exact hN.conj_mem _ (N.zpow_mem n.2 k) g

theorem card_heInnerGrp1_factorization_three :
    3 ^ (Nat.card heInnerGrp1).factorization 3 = 3 := by
  rw [card_heInnerGrp1, show (21504 : ℕ) = 3 * 7168 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self (by norm_num),
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  norm_num

theorem card_heInnerGrp1_factorization_seven :
    7 ^ (Nat.card heInnerGrp1).factorization 7 = 7 := by
  rw [card_heInnerGrp1, show (21504 : ℕ) = 7 * 3072 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self (by norm_num),
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  norm_num

theorem orderOf_hfCW {w : List ℕ} (hw : ∀ j ∈ w, j < 9) {p : ℕ} (hp : p.Prime)
    (hpow : hfCTab (hfRep p w) = idTab 8330) (hne : hfCTab w ≠ idTab 8330) :
    orderOf (hfCW w) = p := by
  have hrep : ∀ j ∈ hfRep p w, j < 9 := by
    intro j hj
    simp only [hfRep, List.mem_flatten, List.mem_replicate] at hj
    obtain ⟨l, ⟨-, rfl⟩, hjl⟩ := hj
    exact hw j hjl
  have h1 : hfCW w ^ p = 1 := by
    rw [← hfCW_rep]
    exact ((tabRep_hfCTab hrep).eq_iff TabRep.idTab).1 hpow
  have h2 : hfCW w ≠ 1 := fun h => hne (((tabRep_hfCTab hw).eq_iff TabRep.idTab).2 h)
  have := Fact.mk hp
  exact orderOf_eq_prime h1 h2

@[expose] def hfOrd7C (i : ℕ) : heInnerGrp1 :=
  if hi : i < 2 then ⟨_, hfCW_mem (hfTwoB_check.2.2.1 i hi)⟩ else 1

@[expose] def hfOrd3C (i : ℕ) : heInnerGrp1 :=
  if hi : i < 3 then ⟨_, hfCW_mem (hfTwoB_check.2.2.2.1 i hi)⟩ else 1

theorem tabRep_hfOrd7Tabs42 :
    ∀ i < hfOrd7Tabs42.size, TabRep hfOrd7Tabs42[i]! (heRho1 (hfOrd7C i)) := by
  intro i hi
  have hi2 : i < 2 := by simpa [hfOrd7Tabs42] using hi
  rw [hfOrd7Tabs42, getElem!_pos _ i (by simpa using hi2), Array.getElem_ofFn]
  simp only [hfOrd7C, hi2, ↓reduceDIte]
  exact tabRep_hfCTab42 (hfTwoB_check.2.2.1 i hi2)

theorem tabRep_hfOrd3Tabs42 :
    ∀ i < hfOrd3Tabs42.size, TabRep hfOrd3Tabs42[i]! (heRho1 (hfOrd3C i)) := by
  intro i hi
  have hi3 : i < 3 := by simpa [hfOrd3Tabs42] using hi
  rw [hfOrd3Tabs42, getElem!_pos _ i (by simpa using hi3), Array.getElem_ofFn]
  simp only [hfOrd3C, hi3, ↓reduceDIte]
  exact tabRep_hfCTab42 (hfTwoB_check.2.2.2.1 i hi3)

theorem orderOf_hfOrd7C {i : ℕ} (hi : i < 2) : orderOf (hfOrd7C i) = 7 := by
  simp only [hfOrd7C, hi, ↓reduceDIte, Subgroup.orderOf_mk]
  exact orderOf_hfCW (hfTwoB_check.2.2.1 i hi) (by norm_num)
    (hfTwoB_check.2.2.2.2.2.2.2.1 i hi).1 (hfTwoB_check.2.2.2.2.2.2.2.1 i hi).2

theorem orderOf_hfOrd3C {i : ℕ} (hi : i < 3) : orderOf (hfOrd3C i) = 3 := by
  simp only [hfOrd3C, hi, ↓reduceDIte, Subgroup.orderOf_mk]
  exact orderOf_hfCW (hfTwoB_check.2.2.2.1 i hi) (by norm_num)
    (hfTwoB_check.2.2.2.2.2.2.2.2.1 i hi).1 (hfTwoB_check.2.2.2.2.2.2.2.2.1 i hi).2

theorem isPGroup_of_normal_ne {N : Subgroup (Equiv.Perm (Fin 8330))}
    (hNC : N ≤ centralizerIn heP heT1P) (hN : (N.subgroupOf (centralizerIn heP heT1P)).Normal)
    (hne : N ≠ centralizerIn heP heT1P) : IsPGroup 2 N := by
  rw [← heInnerGrp1_eq] at hNC hN hne
  set N' := N.subgroupOf heInnerGrp1
  have hcard : Nat.card N' = Nat.card N := Nat.card_congr (subgroupOfEquivOfLe hNC).toEquiv
  have htop : N' ≠ ⊤ := by
    intro h
    apply hne
    apply le_antisymm hNC
    intro c hc
    have : (⟨c, hc⟩ : heInnerGrp1) ∈ N' := h ▸ mem_top _
    exact this
  have h7 : ¬ 7 ∣ Nat.card N := by
    intro h
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    rw [← hcard] at h
    exact htop (eq_top_of_normal_of_enum hN tabRep_hfOrd7Tabs42 (fun i hi =>
      mem_of_normal_of_dvd hN h card_heInnerGrp1_factorization_seven
        (orderOf_hfOrd7C (by simpa [hfOrd7Tabs42] using hi)))
      hfTwoB_check.2.2.2.2.2.2.2.2.2.2.2.2.1 hfTwoB_check.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
  have h3 : ¬ 3 ∣ Nat.card N := by
    intro h
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    rw [← hcard] at h
    exact htop (eq_top_of_normal_of_enum hN tabRep_hfOrd3Tabs42 (fun i hi =>
      mem_of_normal_of_dvd hN h card_heInnerGrp1_factorization_three
        (orderOf_hfOrd3C (by simpa [hfOrd3Tabs42] using hi)))
      hfTwoB_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hfTwoB_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
  have hdvd : Nat.card N ∣ 2 ^ 10 * 21 := by
    rw [show (2 : ℕ) ^ 10 * 21 = 21504 by norm_num, ← card_heInnerGrp1, ← hcard]
    exact Subgroup.card_subgroup_dvd_card N'
  have hcop : Nat.Coprime (Nat.card N) 21 := by
    rw [show (21 : ℕ) = 3 * 7 by norm_num]
    exact Nat.Coprime.mul_right ((Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd
      (by norm_num)).2 h3))) ((Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd
      (by norm_num)).2 h7)))
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (hcop.dvd_of_dvd_mul_right hdvd)
  exact IsPGroup.of_card hk

end CFSG.ComponentClassification.GrSLit.HeldFix
