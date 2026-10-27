module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type*} [Group G]

private lemma inv_conj_mem_of_normalizes [Finite G] {ρ : G} {P : Subgroup G}
    (hρP : ∀ n ∈ P, ρ * n * ρ⁻¹ ∈ P) : ∀ n ∈ P, ρ⁻¹ * n * ρ ∈ P := by
  have hmap : P.map (MulAut.conj ρ).toMonoidHom ≤ P := by
    rintro x ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using hρP y hy
  have hcard : Nat.card (P.map (MulAut.conj ρ).toMonoidHom) = Nat.card P :=
    Subgroup.card_map_of_injective (MulAut.conj ρ).injective
  have heq : P.map (MulAut.conj ρ).toMonoidHom = P :=
    Subgroup.eq_of_le_of_card_ge hmap (le_of_eq hcard.symm)
  intro n hn
  have hmem : n ∈ P.map (MulAut.conj ρ).toMonoidHom := by rw [heq]; exact hn
  rw [Subgroup.mem_map] at hmem
  obtain ⟨m, hm, hmn⟩ := hmem
  have hm' : (MulAut.conj ρ)⁻¹ n = m := by
    rw [← hmn, MulAut.conj_inv_apply]
    change ρ⁻¹ * (ρ * m * ρ⁻¹) * ρ = m
    group
  have : ρ⁻¹ * n * ρ = m := by rw [← hm', MulAut.conj_inv_apply]
  rwa [this]

theorem exists_comm_mem_of_lt [Finite G] {P U W : Subgroup G} (hP : IsPGroup 2 P)
    (hWP : W ≤ P) (hUW : U < W) (hWn : ∀ n ∈ P, ∀ w ∈ W, n * w * n⁻¹ ∈ W)
    (hUn : ∀ n ∈ P, ∀ u ∈ U, n * u * n⁻¹ ∈ U) :
    ∃ w ∈ W, w ∉ U ∧ ∀ n ∈ P, n * w * n⁻¹ * w⁻¹ ∈ U := by
  classical
  have hUP : U ≤ P := hUW.le.trans hWP
  let U' : Subgroup P := U.subgroupOf P
  let W' : Subgroup P := W.subgroupOf P
  have hU'normal : U'.Normal :=
    (Subgroup.normal_subgroupOf_iff hUP).mpr (fun h k hh hk => hUn k hk h hh)
  have hW'normal : W'.Normal :=
    (Subgroup.normal_subgroupOf_iff hWP).mpr (fun h k hh hk => hWn k hk h hh)
  haveI := hU'normal
  haveI := hW'normal
  let Q := P ⧸ U'
  haveI : Group.IsNilpotent Q := (hP.to_quotient U').isNilpotent
  let N : Subgroup Q := W'.map (QuotientGroup.mk' U')
  have hNnormal : N.Normal := hW'normal.map _ (QuotientGroup.mk'_surjective U')
  haveI := hNnormal
  have hNne : N ≠ ⊥ := by
    intro hbot
    obtain ⟨w, hwW, hwU⟩ := SetLike.exists_of_lt hUW
    have hmem : QuotientGroup.mk' U' ⟨w, hWP hwW⟩ ∈ N :=
      ⟨⟨w, hWP hwW⟩, Subgroup.mem_subgroupOf.mpr hwW, rfl⟩
    rw [hbot] at hmem
    simp only [Subgroup.mem_bot] at hmem
    have : (⟨w, hWP hwW⟩ : P) ∈ U' := (QuotientGroup.eq_one_iff _).mp hmem
    exact hwU (Subgroup.mem_subgroupOf.mp this)
  rcases Subgroup.bot_or_exists_ne_one (N ⊓ center Q) with hbot | ⟨x, hx, hxne⟩
  · exact absurd hbot (Group.IsNilpotent.inf_center_ne_bot_of_normal hNne)
  · obtain ⟨hxN, hxc⟩ := hx
    obtain ⟨y, hyW', hyx⟩ := Subgroup.mem_map.mp hxN
    have hyW : (y : G) ∈ W := Subgroup.mem_subgroupOf.mp hyW'
    have hyU : (y : G) ∉ U := by
      intro hyU
      have hyU' : y ∈ U' := Subgroup.mem_subgroupOf.mpr hyU
      have h1 : QuotientGroup.mk' U' y = 1 := (QuotientGroup.eq_one_iff y).mpr hyU'
      exact hxne (by rw [← hyx, h1])
    refine ⟨(y : G), hyW, hyU, ?_⟩
    intro n hn
    have hyx' : (y : Q) = x := hyx
    have hmem : (⟨n, hn⟩ : P) * y * ⟨n, hn⟩⁻¹ * y⁻¹ ∈ U' := by
      apply (QuotientGroup.eq_one_iff _).mp
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv, QuotientGroup.mk_inv, hyx']
      have hc := Subgroup.mem_center_iff.mp hxc ((⟨n, hn⟩ : P) : P ⧸ U')
      rw [hc]
      group
    simpa using Subgroup.mem_subgroupOf.mp hmem

theorem comm_mem_of_fpf_section [Finite G] {P U W : Subgroup G} {ρ : G} (hP : IsPGroup 2 P)
    (hρ3 : ρ ^ 3 = 1) (hWP : W ≤ P) (hUW : U ≤ W) (hcard : Nat.card W = 4 * Nat.card U)
    (hWn : ∀ n ∈ P, ∀ w ∈ W, n * w * n⁻¹ ∈ W) (hUn : ∀ n ∈ P, ∀ u ∈ U, n * u * n⁻¹ ∈ U)
    (hρP : ∀ n ∈ P, ρ * n * ρ⁻¹ ∈ P) (hρW : ∀ w ∈ W, ρ * w * ρ⁻¹ ∈ W)
    (hρU : ∀ u ∈ U, ρ * u * ρ⁻¹ ∈ U)
    (hfpf : ∀ w ∈ W, ρ * w * ρ⁻¹ * w⁻¹ ∈ U → w ∈ U) :
    ∀ n ∈ P, ∀ w ∈ W, n * w * n⁻¹ * w⁻¹ ∈ U := by
  classical
  have hcardU : 0 < Nat.card U := Nat.card_pos
  have hUWlt : U < W := by
    refine lt_of_le_of_ne hUW ?_
    intro h
    have hc : Nat.card U = Nat.card W := congrArg (fun H : Subgroup G => Nat.card H) h
    omega
  obtain ⟨w₀, hw₀W, hw₀U, hw₀c⟩ := exists_comm_mem_of_lt hP hWP hUWlt hWn hUn
  let F : Subgroup G :=
    { carrier := {w | w ∈ W ∧ ∀ n ∈ P, n * w * n⁻¹ * w⁻¹ ∈ U}
      mul_mem' := by
        intro a b ha hb
        obtain ⟨haW, ha⟩ := ha
        obtain ⟨hbW, hb⟩ := hb
        refine ⟨W.mul_mem haW hbW, ?_⟩
        intro n hn
        have h1 : n * a * n⁻¹ * a⁻¹ ∈ U := ha n hn
        have h2 : n * b * n⁻¹ * b⁻¹ ∈ U := hb n hn
        have h3 : a * (n * b * n⁻¹ * b⁻¹) * a⁻¹ ∈ U := hUn a (hWP haW) _ h2
        have h4 : (n * a * n⁻¹ * a⁻¹) * (a * (n * b * n⁻¹ * b⁻¹) * a⁻¹) ∈ U :=
          U.mul_mem h1 h3
        convert h4 using 1
        group
      one_mem' := by
        refine ⟨W.one_mem, ?_⟩
        intro n hn
        simpa using U.one_mem
      inv_mem' := by
        intro a ha
        obtain ⟨haW, ha⟩ := ha
        refine ⟨W.inv_mem haW, ?_⟩
        intro n hn
        have h1 : n * a * n⁻¹ * a⁻¹ ∈ U := ha n hn
        have h3 : a⁻¹ * (n * a * n⁻¹ * a⁻¹) * a ∈ U := by
          simpa using hUn a⁻¹ (P.inv_mem (hWP haW)) _ h1
        have h4 : (a⁻¹ * (n * a * n⁻¹ * a⁻¹) * a)⁻¹ ∈ U := U.inv_mem h3
        convert h4 using 1
        group }
  have hUF : U ≤ F := by
    intro u hu
    refine ⟨hUW hu, ?_⟩
    intro n hn
    exact U.mul_mem (hUn n hn u hu) (U.inv_mem hu)
  have hFW : F ≤ W := fun x hx => hx.1
  have hw₀F : w₀ ∈ F := ⟨hw₀W, hw₀c⟩
  set w₁ : G := ρ * w₀ * ρ⁻¹ with hw₁_def
  have hw₁F : w₁ ∈ F := by
    refine ⟨hρW w₀ hw₀W, ?_⟩
    intro n hn
    have hn' : ρ⁻¹ * n * ρ ∈ P := inv_conj_mem_of_normalizes hρP n hn
    have hc := hw₀c (ρ⁻¹ * n * ρ) hn'
    have hthis : ρ * ((ρ⁻¹ * n * ρ) * w₀ * (ρ⁻¹ * n * ρ)⁻¹ * w₀⁻¹) * ρ⁻¹ ∈ U :=
      hρU _ hc
    convert hthis using 1
    rw [hw₁_def]
    group
  have hρinvU : ∀ u ∈ U, ρ⁻¹ * u * ρ ∈ U := inv_conj_mem_of_normalizes hρU
  have hw₁U : w₁ ∉ U := by
    intro h
    apply hw₀U
    have h2 : ρ⁻¹ * (ρ * w₀ * ρ⁻¹) * ρ = w₀ := by group
    have hthis := hρinvU w₁ h
    rw [hw₁_def, h2] at hthis
    exact hthis
  have hw₀w₁U : w₀⁻¹ * w₁ ∉ U := by
    intro h
    have hconj : w₀ * (w₀⁻¹ * w₁) * w₀⁻¹ ∈ U := hUn w₀ (hWP hw₀W) _ h
    have heq : w₀ * (w₀⁻¹ * w₁) * w₀⁻¹ = ρ * w₀ * ρ⁻¹ * w₀⁻¹ := by
      rw [hw₁_def]; group
    have hconj' : ρ * w₀ * ρ⁻¹ * w₀⁻¹ ∈ U := by
      rw [← heq]; exact hconj
    exact hw₀U (hfpf w₀ hw₀W hconj')
  let U' : Subgroup F := U.subgroupOf F
  have hU'normal : U'.Normal :=
    (Subgroup.normal_subgroupOf_iff hUF).mpr
      (fun h k hh hk => hUn k (hWP (hFW hk)) h hh)
  haveI := hU'normal
  let Q := F ⧸ U'
  let y' : F := ⟨w₀, hw₀F⟩
  let z' : F := ⟨w₁, hw₁F⟩
  have hy' : QuotientGroup.mk' U' y' ≠ 1 := by
    intro h
    apply hw₀U
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff y').mp h)
  have hz' : QuotientGroup.mk' U' z' ≠ 1 := by
    intro h
    apply hw₁U
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff z').mp h)
  have hyz : QuotientGroup.mk' U' y' ≠ QuotientGroup.mk' U' z' := by
    intro h
    apply hw₀w₁U
    have hmem : y'⁻¹ * z' ∈ U' := QuotientGroup.eq.mp h
    simpa using Subgroup.mem_subgroupOf.mp hmem
  have h3Q : 3 ≤ Nat.card Q := by
    have h1 : (1 : Q) ∉
        (insert (QuotientGroup.mk' U' y') ({QuotientGroup.mk' U' z'} : Finset Q)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (h | h)
      · exact hy' h.symm
      · exact hz' h.symm
    have hay : QuotientGroup.mk' U' y' ∉ ({QuotientGroup.mk' U' z'} : Finset Q) := by
      simpa only [Finset.mem_singleton] using hyz
    have hcard : ({1, QuotientGroup.mk' U' y', QuotientGroup.mk' U' z'} : Finset Q).card = 3 := by
      rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem hay,
        Finset.card_singleton]
    calc 3 = ({1, QuotientGroup.mk' U' y', QuotientGroup.mk' U' z'} : Finset Q).card := hcard.symm
      _ ≤ Nat.card Q := Finset.card_le_natCard _
  have hFcard : Nat.card F = Nat.card Q * Nat.card U := by
    have h1 : Nat.card F = Nat.card Q * Nat.card U' :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup U'
    have h2 : Nat.card U' = Nat.card U :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUF).toEquiv
    rw [h1, h2]
  have hQdvd : Nat.card Q ∣ 4 := by
    obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hFW
    rw [hcard, hFcard] at hc
    refine ⟨c, ?_⟩
    have hc' : 4 * Nat.card U = (Nat.card Q * c) * Nat.card U := by
      rw [hc]; ring
    exact Nat.mul_right_cancel hcardU hc'
  have hQeq : Nat.card Q = 4 := by
    have hle : Nat.card Q ≤ 4 := Nat.le_of_dvd (by norm_num) hQdvd
    have hne3 : Nat.card Q ≠ 3 := by
      intro h3
      rw [h3] at hQdvd
      norm_num at hQdvd
    omega
  have hcardF : Nat.card F = Nat.card W := by
    rw [hcard, hFcard, hQeq]
  have hFW_eq : F = W := Subgroup.eq_of_le_of_card_ge hFW (le_of_eq hcardF.symm)
  intro n hn w hw
  have hwF : w ∈ F := by rw [hFW_eq]; exact hw
  exact hwF.2 n hn

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
