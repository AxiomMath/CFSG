module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan

open Subgroup CFSG.ComponentClassification.OuterAutomorphisms

variable {Y : Type*} [Group Y]

private lemma inv_mul_mem_centralizer {N : Subgroup Y} [N.Normal] {m : ↥N} {y : Y}
    (hm : MulAut.conj m = MulAut.conjNormal y) :
    (m : Y)⁻¹ * y ∈ centralizer (N : Set Y) := by
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  have hh : (m : Y) * n * (m : Y)⁻¹ = y * n * y⁻¹ := by
    have h := congrArg (fun (f : MulAut ↥N) => (f ⟨n, hn⟩ : Y)) hm
    rw [MulAut.conj_apply, MulAut.conjNormal_apply] at h
    simpa using h
  calc n * ((m : Y)⁻¹ * y)
      = ((m : Y)⁻¹ * ((m : Y) * n * (m : Y)⁻¹)) * y := by group
    _ = ((m : Y)⁻¹ * (y * n * y⁻¹)) * y := by rw [hh]
    _ = ((m : Y)⁻¹ * y) * n := by group

theorem exists_injective_quotient_outer {N : Subgroup Y} [N.Normal]
    (hC : centralizer (N : Set Y) ≤ N) :
    ∃ f : Y ⧸ N →* Outer ↥N, Function.Injective f := by
  let ψ : Y →* Outer ↥N :=
    (QuotientGroup.mk' (inner ↥N)).comp (MulAut.conjNormal : Y →* MulAut ↥N)
  have hN : N ≤ ψ.ker := by
    intro n hn
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff (N := inner ↥N) (MulAut.conjNormal n)).mpr
      ⟨⟨n, hn⟩, (MulAut.conjNormal_val (H := N) (h := ⟨n, hn⟩)).symm⟩
  refine ⟨QuotientGroup.lift N ψ hN, ?_⟩
  rw [injective_iff_map_eq_one]
  intro y hy
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N y
  simp only [QuotientGroup.mk'_apply] at hy
  change ψ g = 1 at hy
  change (g : Y ⧸ N) = 1
  rw [QuotientGroup.eq_one_iff (N := N)]
  obtain ⟨m, hm⟩ := (QuotientGroup.eq_one_iff (N := inner ↥N) (MulAut.conjNormal g)).mp hy
  have hgN : g ∈ N := by
    have hmN : (m : Y) ∈ N := m.property
    have := N.mul_mem hmN (hC (inv_mul_mem_centralizer hm))
    simpa using this
  exact hgN

theorem index_dvd_card_outer [Finite Y] {N : Subgroup Y} [N.Normal]
    (hC : centralizer (N : Set Y) ≤ N) : N.index ∣ Nat.card (Outer ↥N) := by
  obtain ⟨f, hf⟩ := exists_injective_quotient_outer hC
  rw [N.index_eq_card]
  exact Subgroup.card_dvd_of_injective f hf

theorem isCyclic_quotient_of_isCyclic_outer {N : Subgroup Y} [N.Normal]
    (hC : centralizer (N : Set Y) ≤ N) (hcyc : IsCyclic (Outer ↥N)) : IsCyclic (Y ⧸ N) := by
  obtain ⟨f, hf⟩ := exists_injective_quotient_outer hC
  exact isCyclic_of_injective f hf

theorem index_le_of_card_mulAut_le [Finite Y] {N : Subgroup Y} [N.Normal]
    (hC : centralizer (N : Set Y) ≤ N) (hZ : center ↥N = ⊥) {k : ℕ}
    (h : Nat.card (MulAut ↥N) ≤ k * Nat.card ↥N) : N.index ≤ k := by
  have hinj : Function.Injective (MulAut.conj : ↥N →* MulAut ↥N) := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have hzc : z ∈ center ↥N := by
      rw [Subgroup.mem_center_iff]
      intro x
      have hx : z * x * z⁻¹ = x := by
        simpa using congrArg (fun (f : MulAut ↥N) => f x) hz
      have hzx : z * x = x * z := by
        calc z * x = z * x * z⁻¹ * z := by group
          _ = x * z := by rw [hx]
      exact hzx.symm
    exact Subgroup.mem_bot.mp (hZ ▸ hzc)
  have hinner : Nat.card (inner ↥N) = Nat.card ↥N :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hcardOuter : Nat.card (Outer ↥N) * Nat.card ↥N ≤ k * Nat.card ↥N := by
    calc Nat.card (Outer ↥N) * Nat.card ↥N
        = Nat.card (Outer ↥N) * Nat.card (inner ↥N) := by rw [hinner]
      _ = Nat.card (MulAut ↥N) :=
        (Subgroup.card_eq_card_quotient_mul_card_subgroup (inner ↥N)).symm
      _ ≤ k * Nat.card ↥N := h
  have hOuter : Nat.card (Outer ↥N) ≤ k :=
    Nat.le_of_mul_le_mul_right hcardOuter Finite.card_pos
  have hdvd : N.index ∣ Nat.card (Outer ↥N) := index_dvd_card_outer hC
  have hpos : 0 < Nat.card (Outer ↥N) := Finite.card_pos
  exact le_trans (Nat.le_of_dvd hpos hdvd) hOuter

theorem le_of_isSimpleGroup_of_index_lt [Finite Y] {N A : Subgroup Y} [N.Normal]
    [IsSimpleGroup ↥A] (h : N.index < Nat.card A) : A ≤ N := by
  let f : ↥A →* Y ⧸ N := (QuotientGroup.mk' N).comp A.subtype
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with hbot | htop
  · have hf : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hbot
    have hle : Nat.card ↥A ≤ Nat.card (Y ⧸ N) := Nat.card_le_card_of_injective f hf
    rw [N.index_eq_card] at h
    omega
  · intro a ha
    have hmem : (⟨a, ha⟩ : ↥A) ∈ f.ker := by
      rw [htop]
      trivial
    exact (QuotientGroup.eq_one_iff (N := N) a).mp (by simpa [f, MonoidHom.mem_ker] using hmem)

theorem conjNormal_not_mem_inner {N : Subgroup Y} [N.Normal] (hC : centralizer (N : Set Y) ≤ N)
    {w : Y} (hw : w ∉ N) : MulAut.conjNormal w ∉ inner ↥N := by
  intro hmem
  obtain ⟨m, hm⟩ := hmem
  apply hw
  have hmN : (m : Y) ∈ N := m.property
  have := N.mul_mem hmN (hC (inv_mul_mem_centralizer hm))
  simpa using this

theorem orderOf_conjNormal_eq_two {N : Subgroup Y} [N.Normal] (hC : centralizer (N : Set Y) ≤ N)
    {w : Y} (hw : orderOf w = 2) (hwN : w ∉ N) :
    orderOf (MulAut.conjNormal w : MulAut ↥N) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime
  · have h2 : (MulAut.conjNormal w : MulAut ↥N) ^ 2 = MulAut.conjNormal (w ^ 2) := by
      rw [← map_pow]
    rw [h2, ← hw, pow_orderOf_eq_one, map_one]
  · intro h1
    refine conjNormal_not_mem_inner hC hwN ?_
    rw [h1]
    exact ⟨1, map_one _⟩

theorem card_dvd_card_centralizer_of_le [Finite Y] {N A : Subgroup Y} (hAN : A ≤ N) {w : Y}
    (hwN : w ∈ N) (hAw : A ≤ centralizer ({w} : Set Y)) :
    Nat.card A ∣ Nat.card (centralizer ({(⟨w, hwN⟩ : ↥N)} : Set ↥N)) := by
  have hsub : A.subgroupOf N ≤ Subgroup.centralizer ({(⟨w, hwN⟩ : ↥N)} : Set ↥N) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have hxw : (x : Y) ∈ centralizer ({w} : Set Y) := hAw hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hxw
    simpa using hxw
  have hcard : Nat.card ↥(A.subgroupOf N) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv
  have hdvd : Nat.card ↥(A.subgroupOf N) ∣
      Nat.card (centralizer ({(⟨w, hwN⟩ : ↥N)} : Set ↥N)) := Subgroup.card_dvd_of_le hsub
  simpa [hcard] using hdvd

theorem card_dvd_card_fixed_of_le [Finite Y] {N A : Subgroup Y} [N.Normal] (hAN : A ≤ N) {w : Y}
    (hAw : A ≤ centralizer ({w} : Set Y)) :
    Nat.card A ∣ Nat.card {x : ↥N // (MulAut.conjNormal w : MulAut ↥N) x = x} := by
  let F : Subgroup ↥N :=
    { carrier := {x | (MulAut.conjNormal w : MulAut ↥N) x = x}
      mul_mem' := by
        intro a b ha hb
        show (MulAut.conjNormal w : MulAut ↥N) (a * b) = a * b
        rw [map_mul, ha, hb]
      one_mem' := by
        show (MulAut.conjNormal w : MulAut ↥N) 1 = 1
        rw [map_one]
      inv_mem' := by
        intro a ha
        show (MulAut.conjNormal w : MulAut ↥N) a⁻¹ = a⁻¹
        rw [map_inv, ha] }
  have hsub : A.subgroupOf N ≤ F := by
    intro x hx
    show (MulAut.conjNormal w : MulAut ↥N) x = x
    apply Subtype.ext
    have hxw : (x : Y) ∈ centralizer ({w} : Set Y) := hAw hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hxw
    rw [MulAut.conjNormal_apply, ← hxw]
    group
  have hcard : Nat.card ↥(A.subgroupOf N) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv
  have hdvd : Nat.card ↥(A.subgroupOf N) ∣ Nat.card ↥F := Subgroup.card_dvd_of_le hsub
  have hF : Nat.card ↥F =
      Nat.card {x : ↥N // (MulAut.conjNormal w : MulAut ↥N) x = x} := rfl
  simpa [hcard, hF] using hdvd

theorem exists_mem_orderOf_eq_ten [Finite Y] {N : Subgroup Y} [N.Normal] (hidx : N.index ≤ 2)
    {w d : Y} (hw : orderOf w = 2) (hd : orderOf d = 10) (hwd : w * d = d * w)
    (hdw : ∀ k : ℕ, d ^ k ≠ w) : ∃ x ∈ N, orderOf x = 10 := by
  have hne : N.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hcases : N.index = 1 ∨ N.index = 2 := by omega
  rcases hcases with h1 | h2
  · refine ⟨d, ?_, hd⟩
    rw [Subgroup.index_eq_one.mp h1]
    exact Subgroup.mem_top d
  · have hw2one : w ^ 2 = 1 := by rw [← hw, pow_orderOf_eq_one]
    have hww : w * w = 1 := by simpa [pow_two] using hw2one
    have hcomm : Commute w d := hwd
    by_cases hwN : w ∈ N
    · refine ⟨w * d ^ 2, N.mul_mem hwN (Subgroup.sq_mem_of_index_two h2 d), ?_⟩
      have hd2 : orderOf (d ^ 2) = 5 := by
        rw [orderOf_pow_of_dvd (x := d) (n := 2) (by norm_num) (by rw [hd]; norm_num), hd]
      have hco : (orderOf w).Coprime (orderOf (d ^ 2)) := by
        rw [hw, hd2]
        norm_num
      rw [(hcomm.pow_right 2).orderOf_mul_eq_mul_orderOf_of_coprime hco, hw, hd2]
    · by_cases hdN : d ∈ N
      · exact ⟨d, hdN, hd⟩
      · have hdwN : d * w ∈ N := by
          rw [Subgroup.mul_mem_iff_of_index_two h2]
          exact ⟨fun h => (hdN h).elim, fun h => (hwN h).elim⟩
        refine ⟨d * w, hdwN, ?_⟩
        have hw5 : w ^ 5 = w := by
          rw [show (5 : ℕ) = 2 * 2 + 1 by norm_num, pow_add, pow_mul, pow_one, hw2one]
          simp
        have hdw5 : (d * w) ^ 5 ≠ 1 := by
          intro hcon
          have hmul : 1 = d ^ 5 * w := by
            have h := hcomm.symm.mul_pow 5
            rw [hcon, hw5] at h
            exact h
          have hd5 : d ^ 5 = w := by
            have h' := congrArg (· * w) hmul
            have h2' : w = d ^ 5 := by simpa [mul_assoc, hww] using h'
            exact h2'.symm
          exact hdw 5 hd5
        have hdw2 : (d * w) ^ 2 ≠ 1 := by
          intro hcon
          have hd2ne : d ^ 2 ≠ 1 :=
            pow_ne_one_of_lt_orderOf (n := 2) (by norm_num) (by rw [hd]; norm_num)
          apply hd2ne
          have h := hcomm.symm.mul_pow 2
          rw [hcon, hw2one, mul_one] at h
          exact h.symm
        have hdw10 : (d * w) ^ 10 = 1 := by
          have hd10 : d ^ 10 = 1 := by rw [← hd, pow_orderOf_eq_one]
          have hw10 : w ^ 10 = 1 := by
            rw [← orderOf_dvd_iff_pow_eq_one, hw]
            norm_num
          rw [hcomm.symm.mul_pow 10, hd10, hw10, mul_one]
        refine orderOf_eq_of_pow_and_pow_div_prime (n := 10) (by norm_num) hdw10 ?_
        intro p hp hpdvd
        have hpdvd' : p ∣ 2 * 5 := by
          rwa [show (2 : ℕ) * 5 = 10 by norm_num]
        rcases hp.dvd_mul.mp hpdvd' with h2p | h5p
        · have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2p
          rw [hp2, show 10 / 2 = 5 by norm_num]
          exact hdw5
        · have hp5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h5p
          rw [hp5, show 10 / 5 = 2 by norm_num]
          exact hdw2

theorem exists_mem_orderOf_eq_eight [Finite Y] {N : Subgroup Y} [N.Normal] (hcyc : IsCyclic (Y ⧸ N))
    {w h : Y} (hw : orderOf w = 2) (hwN : w ∉ N) (hh : orderOf h = 8) (hwh : w * h = h * w)
    (hh2 : h ^ 2 ∈ N) : ∃ x ∈ N, orderOf x = 8 := by
  classical
  by_cases hhN : h ∈ N
  · exact ⟨h, hhN, hh⟩
  · have hw2one : w ^ 2 = 1 := by rw [← hw, pow_orderOf_eq_one]
    have hhQ : (h : Y ⧸ N) ^ 2 = 1 := by
      rw [← QuotientGroup.mk'_apply (N := N) (x := h), ← map_pow (QuotientGroup.mk' N) h 2]
      exact (QuotientGroup.eq_one_iff (N := N) (h ^ 2)).mpr hh2
    have hwQ : (w : Y ⧸ N) ^ 2 = 1 := by
      rw [← QuotientGroup.mk'_apply (N := N) (x := w), ← map_pow (QuotientGroup.mk' N) w 2,
        hw2one, map_one]
    have hh1 : (h : Y ⧸ N) ≠ 1 := fun hc => hhN ((QuotientGroup.eq_one_iff (N := N) h).mp hc)
    have hw1 : (w : Y ⧸ N) ≠ 1 := fun hc => hwN ((QuotientGroup.eq_one_iff (N := N) w).mp hc)
    have hclass : (QuotientGroup.mk' N) h = (QuotientGroup.mk' N) w := by
      change (h : Y ⧸ N) = (w : Y ⧸ N)
      haveI : IsCyclic (Y ⧸ N) := hcyc
      haveI : Fintype (Y ⧸ N) := Fintype.ofFinite (Y ⧸ N)
      let S : Finset (Y ⧸ N) := Finset.univ.filter (fun a => a ^ 2 = 1)
      by_contra hne
      have hSsub : ({1, (h : Y ⧸ N), (w : Y ⧸ N)} : Finset (Y ⧸ N)) ⊆ S := by
        intro a ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl | rfl
        · simp [S]
        · simpa [S] using hhQ
        · simpa [S] using hwQ
      have hcardT : ({1, (h : Y ⧸ N), (w : Y ⧸ N)} : Finset (Y ⧸ N)).card = 3 := by
        rw [show ({1, (h : Y ⧸ N), (w : Y ⧸ N)} : Finset (Y ⧸ N)) =
            insert 1 ({(h : Y ⧸ N), (w : Y ⧸ N)} : Finset (Y ⧸ N)) by rfl]
        rw [Finset.card_insert_of_notMem (by simp [hh1.symm, hw1.symm]),
          Finset.card_pair_eq_two_iff.mpr hne]
      have hle : ({1, (h : Y ⧸ N), (w : Y ⧸ N)} : Finset (Y ⧸ N)).card ≤ 2 := by
        refine le_trans (Finset.card_le_card hSsub) ?_
        have := IsCyclic.card_pow_eq_one_le (α := Y ⧸ N) (n := 2) (by norm_num)
        simpa [S] using this
      omega
    have hwhN : w * h ∈ N := by
      rw [← QuotientGroup.eq_one_iff (N := N) (w * h)]
      show (QuotientGroup.mk' N (w * h) : Y ⧸ N) = 1
      rw [map_mul, hclass, ← map_mul, ← pow_two, hw2one, map_one]
    refine ⟨w * h, hwhN, ?_⟩
    have hcomm : Commute w h := hwh
    have hpow4 : (w * h) ^ 4 ≠ 1 := by
      intro hc
      have h4 : h ^ 4 = 1 := by
        have h' := hcomm.mul_pow 4
        rw [hc] at h'
        have hw4 : w ^ 4 = 1 := by
          rw [← orderOf_dvd_iff_pow_eq_one, hw]
          norm_num
        rw [hw4, one_mul] at h'
        exact h'.symm
      exact pow_ne_one_of_lt_orderOf (n := 4) (by norm_num) (by rw [hh]; norm_num) h4
    have hpow8 : (w * h) ^ 8 = 1 := by
      have hw8 : w ^ 8 = 1 := by
        rw [← orderOf_dvd_iff_pow_eq_one, hw]
        norm_num
      have hh8 : h ^ 8 = 1 := by rw [← hh, pow_orderOf_eq_one]
      rw [hcomm.mul_pow 8, hw8, hh8, mul_one]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hnot : ¬ (w * h) ^ (2 ^ 2) = 1 := by simpa using hpow4
    have hfin : (w * h) ^ (2 ^ (2 + 1)) = 1 := by simpa using hpow8
    have horder : orderOf (w * h) = 2 ^ (2 + 1) :=
      orderOf_eq_prime_pow (p := 2) (n := 2) hnot hfin
    norm_num at horder
    exact horder

theorem exists_conj_mem_of_card_eq_pow {G : Type*} [Group G] [Finite G] {p k : ℕ} [Fact p.Prime]
    {P : Subgroup G} (hP : Nat.card P = p ^ k) (hk : ¬ p ^ (k + 1) ∣ Nat.card G) {x : G}
    (hx : orderOf x = p) : ∃ g : G, g * x * g⁻¹ ∈ P := by
  have hGnz : Nat.card G ≠ 0 := (Finite.card_pos (α := G)).ne'
  have hcardP_dvd : p ^ k ∣ Nat.card G := hP ▸ Subgroup.card_subgroup_dvd_card P
  have hle : k ≤ (Nat.card G).factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization Fact.out hGnz).mp hcardP_dvd
  have hlt : (Nat.card G).factorization p < k + 1 := by
    by_contra hcon
    exact hk ((Nat.Prime.pow_dvd_iff_le_factorization Fact.out hGnz).mpr (by omega))
  have hfac : (Nat.card G).factorization p = k := by omega
  have hPeq : Nat.card P = p ^ (Nat.card G).factorization p := by rw [hP, hfac]
  have hy : IsPGroup p (Subgroup.zpowers x) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hx, pow_one]
  obtain ⟨Q, hQ⟩ := hy.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (Sylow.ofCard P hPeq) Q
  have hxQ : x ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers x)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxQ
  refine ⟨g⁻¹, ?_⟩
  have hmem : (MulAut.conj g)⁻¹ • x ∈ P := hxQ
  rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv] at hmem
  simpa using hmem

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan
