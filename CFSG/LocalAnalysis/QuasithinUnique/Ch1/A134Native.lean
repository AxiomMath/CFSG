module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
public import CFSG.Quasithin.Background.A3Structure36AQuasi
public import CFSG.Milestones.CL_LIT_SQTK_simple_list

public section

namespace CFSG.QuasithinUnique.Vol2Native

open CFSG.Open CFSG.SectionRank
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

theorem three_le_pRank_of_commuting_subgroups {H : Type*} [Group H] [Finite H] {r : ℕ}
    (hr : r.Prime) {A B : Subgroup H} (hAB : ∀ u ∈ A, ∀ v ∈ B, u * v = v * u) {x y z : H}
    (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ B) (hxr : x ^ r = 1) (hyr : y ^ r = 1) (hzr : z ^ r = 1)
    (hxy : x * y = y * x) (hx1 : x ≠ 1) (hy1 : ∀ n : ℕ, x ^ n ≠ y)
    (hznc : ∃ w ∈ B, z * w ≠ w * z) : 3 ≤ CFSG.Open.pRank r (⊤ : Subgroup H) := by
  have : Fact r.Prime := ⟨hr⟩
  refine ClassicalEven.three_le_pRank_of_gens hxr hyr hzr hxy
    (show Commute x z from hAB x hx z hz) (show Commute y z from hAB y hy z hz) hx1 hy1 ?_
  intro n m h
  obtain ⟨w, hwB, hw⟩ := hznc
  have hzA : z ∈ A := h ▸ A.mul_mem (A.pow_mem hx n) (A.pow_mem hy m)
  exact hw (hAB z hzA w hwB)

theorem two_le_pRank_of_quotient_center {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (h : 2 ≤ CFSG.Open.pRank r (⊤ : Subgroup (L ⧸ Subgroup.center L))) :
    2 ≤ CFSG.Open.pRank r (⊤ : Subgroup L) := by
  have : Fact r.Prime := ⟨hr⟩
  by_cases hdvd : r ∣ Nat.card (Subgroup.center L)
  · have hrL : r ∣ Nat.card L := hdvd.trans (Subgroup.card_subgroup_dvd_card _)
    have := (perfect_cyclic_center_odd_elements (L := L) hr2 hrL).2 hdvd
    rwa [pRank_eq_open_pRank_top] at this
  · rw [pRank_quotient_eq (Subgroup.center L) hdvd] at h
    exact h

theorem exists_noncentral_pair {L : Type*} [Group L] [Finite L] [Group.IsPerfect L] {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2)
    (hZ : Nat.card (Subgroup.center L) = 1 ∨ Nat.card (Subgroup.center L) = 3)
    (h : 2 ≤ CFSG.Open.pRank r (⊤ : Subgroup (L ⧸ Subgroup.center L))) :
    ∃ a b : L, a ^ r = 1 ∧ b ^ r = 1 ∧ a * b = b * a ∧ a ∉ Subgroup.center L ∧
      ∀ n : ℕ, a ^ n ≠ b := by
  have h2 := two_le_pRank_of_quotient_center hr hr2 h
  obtain ⟨E, -, hE, hcard⟩ := exists_pRank hr.one_lt (⊤ : Subgroup L)
  have hr3 : 3 ≤ r := by
    have := hr.two_le
    omega
  have hEr : r ^ 2 ≤ Nat.card E := by
    rw [hcard]
    exact Nat.pow_le_pow_right hr.pos h2
  obtain ⟨a, haE, haZ⟩ : ∃ a ∈ E, a ∉ Subgroup.center L := by
    by_contra hcon
    push Not at hcon
    have h1 : Nat.card E ≤ Nat.card (Subgroup.center L) :=
      Subgroup.card_le_of_le fun x hx => hcon x hx
    have h9 : 9 ≤ r ^ 2 := by nlinarith
    rcases hZ with hZ | hZ <;> omega
  have hap : a ^ r = 1 := hE.2 a haE
  have hzp : Nat.card (Subgroup.zpowers a) ≤ r := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd hr.pos (orderOf_dvd_of_pow_eq_one hap)
  obtain ⟨b, hbE, hb⟩ : ∃ b ∈ E, b ∉ Subgroup.zpowers a := by
    by_contra hcon
    push Not at hcon
    have h1 : Nat.card E ≤ Nat.card (Subgroup.zpowers a) :=
      Subgroup.card_le_of_le fun x hx => hcon x hx
    nlinarith
  have hcomm := hE.1
  refine ⟨a, b, hap, hE.2 b hbE, ?_, haZ, fun n hn => hb ?_⟩
  · have := mul_comm' (⟨a, haE⟩ : E) ⟨b, hbE⟩
    exact congrArg Subtype.val this
  · rw [← hn]
    exact Subgroup.npow_mem_zpowers a n

theorem exists_odd_prime_dvd_card_of_quasisimple {L : Type*} [Group L] [Finite L]
    (hL : CFSG.IsQuasisimple L) : ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ Nat.card L := by
  by_contra hcon
  push Not at hcon
  have hpos : Nat.card L ≠ 0 := Nat.card_pos.ne'
  have hpow : Nat.card L = 2 ^ (Nat.card L).primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd hpos fun {d} hd hdvd => by
      by_contra hne
      exact hcon d hd hne hdvd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 L := IsPGroup.of_card hpow
  have hnil : Group.IsNilpotent L := hP.isNilpotent
  have hsolv : Group.IsSolvable L := inferInstance
  have hnt : Nontrivial L := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    obtain ⟨a, b, hab⟩ := hL.2.2
    have : Subsingleton (L ⧸ Subgroup.center L) :=
      Function.Surjective.subsingleton (QuotientGroup.mk'_surjective (Subgroup.center L))
    exact hab (Subsingleton.elim _ _)
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial L).ne (Group.isPerfect_def.mp hL.1)

theorem commute_of_components {H : Type*} [Group H] [Finite H] {L₁ L₂ : Subgroup H}
    (h₁ : CFSG.IsComponent L₁) (h₂ : CFSG.IsComponent L₂) (hne : L₁ ≠ L₂) :
    ∀ u ∈ L₁, ∀ v ∈ L₂, u * v = v * u := by
  rcases CFSG.LocalCores.distinct_components_commute h₁ h₂ with h | h
  · exact absurd h hne
  · intro u hu v hv
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hu) v hv).symm

theorem not_mem_center_map {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {a : X}
    (ha : a ∉ Subgroup.center X) : e a ∉ Subgroup.center Y := by
  intro h
  apply ha
  rw [Subgroup.mem_center_iff] at h ⊢
  intro g
  apply e.injective
  rw [map_mul, map_mul]
  exact h (e g)

theorem a134For_of_component_data {H : Type} [Group H] [Finite H] (hR : A134RankOneFact)
    (hrank : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (⊤ : Subgroup H) ≤ 2)
    (hcomp : ∀ L : Subgroup H, CFSG.IsComponent L →
      (Nat.card (Subgroup.center ↥L) = 1 ∨ Nat.card (Subgroup.center ↥L) = 3) ∧
        A23ListCat (↥L ⧸ Subgroup.center ↥L)) : A134For H := by
  intro L₁ L₂ h₁ h₂ hne ⟨φ⟩
  obtain ⟨hZ₁, hlist⟩ := hcomp L₁ h₁
  have : Group.IsPerfect ↥L₁ := h₁.1.1
  have hcomm := commute_of_components h₁ h₂ hne
  refine ⟨?_, Or.inl (hR _ hlist ?_)⟩
  ·
    intro L hL ⟨e⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨hL1, hL2⟩ := hcon
    obtain ⟨r, hr, hr2, hrL⟩ := exists_odd_prime_dvd_card_of_quasisimple h₁.1
    obtain ⟨a, har, haZ⟩ := exists_orderOf_not_mem_center_of_card_center hZ₁ hr hr2 hrL
    have har' : a ^ r = 1 := har ▸ pow_orderOf_eq_one a
    have hc1L : ∀ u ∈ L₁, ∀ v ∈ L, u * v = v * u := commute_of_components h₁ hL (Ne.symm hL1)
    have hc2L : ∀ u ∈ L₂, ∀ v ∈ L, u * v = v * u := commute_of_components h₂ hL (Ne.symm hL2)
    have hAB : ∀ u ∈ L₁ ⊔ L₂, ∀ v ∈ L, u * v = v * u := by
      have : L₁ ⊔ L₂ ≤ Subgroup.centralizer (L : Set H) :=
        sup_le (fun u hu => Subgroup.mem_centralizer_iff.mpr fun v hv => (hc1L u hu v hv).symm)
          (fun u hu => Subgroup.mem_centralizer_iff.mpr fun v hv => (hc2L u hu v hv).symm)
      intro u hu v hv
      exact (Subgroup.mem_centralizer_iff.mp (this hu) v hv).symm
    have hφa : φ a ∉ Subgroup.center ↥L₂ := not_mem_center_map φ haZ
    have hea : e.symm a ∉ Subgroup.center ↥L := not_mem_center_map e.symm haZ
    have h3 := three_le_pRank_of_commuting_subgroups hr hAB (x := (a : H))
      (y := ((φ a : ↥L₂) : H)) (z := ((e.symm a : ↥L) : H)) (le_sup_left (a := L₁) (b := L₂) a.2)
      (le_sup_right (a := L₁) (b := L₂) (φ a).2) (e.symm a).2
      (by rw [← Subgroup.coe_pow, har', Subgroup.coe_one])
      (by rw [← Subgroup.coe_pow, ← map_pow, har', map_one, Subgroup.coe_one])
      (by rw [← Subgroup.coe_pow, ← map_pow, har', map_one, Subgroup.coe_one])
      (hcomm a a.2 (φ a) (φ a).2)
      (fun h => haZ (by
        have : a = 1 := Subtype.ext h
        rw [this]
        exact Subgroup.one_mem _))
      (fun n hn => hφa (by
        rw [Subgroup.mem_center_iff]
        intro w
        apply Subtype.ext
        have hy1 : ((φ a : ↥L₂) : H) ∈ L₁ := by
          rw [← hn, ← Subgroup.coe_pow]
          exact (a ^ n).2
        exact (hcomm _ hy1 w w.2).symm))
      (by
        rw [Subgroup.mem_center_iff] at hea
        push Not at hea
        obtain ⟨w, hw⟩ := hea
        exact ⟨w, w.2, fun h => hw (Subtype.ext h.symm)⟩)
    have := hrank r hr hr2
    omega
  ·
    intro r hr hr2
    by_contra hgt
    push Not at hgt
    have h2 : 2 ≤ CFSG.Open.pRank r (⊤ : Subgroup (↥L₁ ⧸ Subgroup.center ↥L₁)) := by
      rw [← pRank_eq_open_pRank_top]
      omega
    obtain ⟨a, b, har, hbr, hab, haZ, hba⟩ := exists_noncentral_pair hr hr2 hZ₁ h2
    have hφa : φ a ∉ Subgroup.center ↥L₂ := not_mem_center_map φ haZ
    have h3 := three_le_pRank_of_commuting_subgroups hr hcomm (x := (a : H)) (y := (b : H))
      (z := ((φ a : ↥L₂) : H)) a.2 b.2 (φ a).2
      (by rw [← Subgroup.coe_pow, har, Subgroup.coe_one])
      (by rw [← Subgroup.coe_pow, hbr, Subgroup.coe_one])
      (by rw [← Subgroup.coe_pow, ← map_pow, har, map_one, Subgroup.coe_one])
      (congrArg Subtype.val hab)
      (fun h => haZ (by
        have : a = 1 := Subtype.ext h
        rw [this]
        exact Subgroup.one_mem _))
      (fun n hn => hba n (Subtype.ext (by rw [Subgroup.coe_pow]; exact hn)))
      (by
        rw [Subgroup.mem_center_iff] at hφa
        push Not at hφa
        obtain ⟨w, hw⟩ := hφa
        exact ⟨w, w.2, fun h => hw (Subtype.ext h.symm)⟩)
    have := hrank r hr hr2
    omega

theorem component_center_card
    {G : Type} [Group G] (hG : SQTKHypCat G) {L : Subgroup G}
    (hL : CFSG.IsComponent L) :
    Nat.card (Subgroup.center ↥L) = 1 ∨ Nat.card (Subgroup.center ↥L) = 3 := by
  have := hG.finite
  have hsub : IsSubnormal L ⊤ := A3.subnormal_top_iff.mpr hL.2
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) :=
    A36A.odd_card_center (hG.pCore_two_of_subnormal hsub)
  exact (catalogStepHyp ↥L hL.1 (hG.subgroup L) hodd).1

theorem component_list
    {G : Type} [Group G] (hG : SQTKHypCat G) {L : Subgroup G}
    (hL : CFSG.IsComponent L) : A23ListCat (↥L ⧸ Subgroup.center ↥L) := by
  have := hG.finite
  have := hL.1.2.1
  exact CFSG.Milestones.cl_lit_sqtk_simple_list_section G hG.isSQTKCat L (Subgroup.center ↥L)
    hL.1.2.2

theorem a134For_of_rankOne
    (hR : A134RankOneFact) {H : Type} [Group H] [Finite H]
    (hH : SQTKHypCat H) : A134For H :=
  a134For_of_component_data hR (fun _ hq hq2 => hH.rank_top hq hq2)
    fun _ hL => ⟨component_center_card hH hL, component_list hH hL⟩

theorem a134SQTKFactCat_of_rankOne
    (hR : A134RankOneFact) : A134SQTKFactCat :=
  fun _ _ _ hH => a134For_of_rankOne hR hH

end CFSG.QuasithinUnique.Vol2Native
