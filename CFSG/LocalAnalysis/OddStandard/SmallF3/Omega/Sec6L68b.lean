module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6L68a
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6L66In

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sec68_conj_mem_sup {t : G} {B : Subgroup G} {n : G}
    (hnt : n * t * n⁻¹ = t) (hnB : n ∈ normalizer (B : Set G)) :
    ∀ y ∈ (zpowers t ⊔ B : Subgroup G), n * y * n⁻¹ ∈ (zpowers t ⊔ B : Subgroup G) := by
  intro y hy
  rw [Subgroup.sup_eq_closure] at hy ⊢
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
      rcases hx with hx | hx
      · change x ∈ zpowers t at hx
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        exact Subgroup.subset_closure (Or.inl
          (Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← conj_zpow, hnt]⟩))
      · change x ∈ B at hx
        exact Subgroup.subset_closure (Or.inr ((Subgroup.mem_normalizer_iff.mp hnB x).mp hx))
  | one => simp
  | mul a b _ _ iha ihb =>
      rw [← conj_mul]
      exact mul_mem iha ihb
  | inv a _ iha =>
      have h : n * a⁻¹ * n⁻¹ = (n * a * n⁻¹)⁻¹ := by group
      rw [h]
      exact inv_mem iha

theorem sec68_t_mem_centralizer [Finite G] {t : G} {L : Subgroup G} (hS : Sec3SettingLB G t L) :
    t ∈ centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.mp (hS.component.le hx)

theorem sec68_coset_eq {t p : G} {B : Subgroup G} (hp : p ∈ cosetSet t B) :
    cosetSet p B = cosetSet t B ∧ (zpowers p ⊔ B : Subgroup G) = zpowers t ⊔ B := by
  obtain ⟨b₀, hb₀, hpb⟩ := hp
  constructor
  · ext x
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b₀ * b, B.mul_mem hb₀ hb, by rw [hpb]; group⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b₀⁻¹ * b, B.mul_mem (B.inv_mem hb₀) hb, by rw [hpb]; group⟩
  · apply le_antisymm
    · refine sup_le ?_ le_sup_right
      rw [zpowers_le, hpb]
      exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers t) hb₀
    · refine sup_le ?_ le_sup_right
      rw [zpowers_le]
      have ht : t = p * b₀⁻¹ := by rw [hpb]; group
      rw [ht]
      exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers p) (B.inv_mem hb₀)

theorem sec68_mem_sup {t : G} {B : Subgroup G} (ht2 : t * t = 1) (hcomm : ∀ b ∈ B, b * t = t * b)
    {y : G} (hy : y ∈ (zpowers t ⊔ B : Subgroup G)) : y ∈ B ∨ ∃ b ∈ B, y = t * b := by
  let S : Subgroup G :=
    { carrier := {y | y ∈ B ∨ ∃ b ∈ B, y = t * b}
      one_mem' := Or.inl B.one_mem
      mul_mem' := by
        rintro a b (ha | ⟨a', ha', rfl⟩) (hb | ⟨b', hb', rfl⟩)
        · exact Or.inl (B.mul_mem ha hb)
        · exact Or.inr ⟨a * b', B.mul_mem ha hb',
            by rw [← mul_assoc a t, hcomm a ha]; group⟩
        · exact Or.inr ⟨a' * b, B.mul_mem ha' hb, by group⟩
        · refine Or.inl ?_
          rw [show (t * a') * (t * b') = a' * b' by
            calc (t * a') * (t * b') = (t * (a' * t)) * b' := by group
              _ = (t * (t * a')) * b' := by rw [hcomm a' ha']
              _ = (t * t) * (a' * b') := by group
              _ = a' * b' := by rw [ht2, one_mul]]
          exact B.mul_mem ha' hb'
      inv_mem' := by
        rintro a (ha | ⟨a', ha', rfl⟩)
        · exact Or.inl (B.inv_mem ha)
        · refine Or.inr ⟨a'⁻¹, B.inv_mem ha', ?_⟩
          rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ht2, hcomm a'⁻¹ (B.inv_mem ha')] }
  have hle : (zpowers t ⊔ B : Subgroup G) ≤ S := by
    refine sup_le ?_ ?_
    · rw [zpowers_le]
      exact Or.inr ⟨1, B.one_mem, (mul_one t).symm⟩
    · intro b hb
      exact Or.inl hb
  exact hle hy

theorem sec68_act {t : G} {B M : Subgroup G} (hM : M ≤ centralizer ({t} : Set G)) {n : G}
    (hn : n ∈ M ⊓ normalizer (B : Set G)) :
    n ∈ normalizer ((zpowers t ⊔ B : Subgroup G) : Set G) ∧ n * t * n⁻¹ = t ∧
      ∀ a ∈ cosetSet t B, n * a * n⁻¹ ∈ cosetSet t B := by
  have hnM : n ∈ M := hn.1
  have hnB : n ∈ normalizer (B : Set G) := hn.2
  have hnt : n * t * n⁻¹ = t := by
    have h : n * t = t * n := Subgroup.mem_centralizer_singleton_iff.mp (hM hnM)
    rw [h]
    group
  have hnt' : n⁻¹ * t * (n⁻¹)⁻¹ = t := by
    rw [inv_inv]
    calc n⁻¹ * t * n = n⁻¹ * (n * t * n⁻¹) * n := by rw [hnt]
      _ = t := by group
  have hnB' : n⁻¹ ∈ normalizer (B : Set G) := (normalizer (B : Set G)).inv_mem hnB
  have hmap := sec68_conj_mem_sup (t := t) (B := B) hnt hnB
  have hmap' := sec68_conj_mem_sup (t := t) (B := B) hnt' hnB'
  refine ⟨?_, hnt, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hmap y
    · intro hy
      have h := hmap' (n * y * n⁻¹) hy
      convert h using 1
      group
  · rintro a ⟨b, hb, rfl⟩
    refine ⟨n * b * n⁻¹, (Subgroup.mem_normalizer_iff.mp hnB b).mp hb, ?_⟩
    rw [show n * (t * b) * n⁻¹ = (n * t * n⁻¹) * (n * b * n⁻¹) by group, hnt]

theorem sec68_trans_B {t : G} {B M : Subgroup G} (hM : M ≤ centralizer ({t} : Set G))
    (htr : ∀ b ∈ B, b ≠ 1 → ∀ b' ∈ B, b' ≠ 1 →
      ∃ n ∈ M ⊓ normalizer (B : Set G), n * b * n⁻¹ = b') :
    ∀ a ∈ cosetSet t B, a ≠ t → ∀ b ∈ cosetSet t B, b ≠ t →
      ∃ n ∈ M ⊓ normalizer (B : Set G), n * t * n⁻¹ = t ∧ n * a * n⁻¹ = b := by
  intro a ha ha_ne b hb hb_ne
  obtain ⟨b₁, hb₁B, rfl⟩ := ha
  obtain ⟨b₂, hb₂B, rfl⟩ := hb
  have hb₁1 : b₁ ≠ 1 := by
    intro h
    exact ha_ne (by rw [h, mul_one])
  have hb₂1 : b₂ ≠ 1 := by
    intro h
    exact hb_ne (by rw [h, mul_one])
  obtain ⟨n, hn, hnb⟩ := htr b₁ hb₁B hb₁1 b₂ hb₂B hb₂1
  have hnt : n * t * n⁻¹ = t := by
    have h : n * t = t * n := Subgroup.mem_centralizer_singleton_iff.mp (hM hn.1)
    rw [h]
    group
  refine ⟨n, hn, hnt, ?_⟩
  rw [show n * (t * b₁) * n⁻¹ = (n * t * n⁻¹) * (n * b₁ * n⁻¹) by group, hnt, hnb]

theorem sec68_no_order_four [Finite G] (h36 : Asc82Lemma36) (hM : Asc82Tab6M) {t : G}
    {L : Subgroup G} (hS : Sec3SettingLB G t L) (hL6 : IsOmega6Minus L) {B : Subgroup G}
    (hB : IsElemAb2 B 4) (hBL : B ≤ L) {g : G} (hgt : g⁻¹ * t * g ≠ t)
    (hgB : g⁻¹ * t * g ∈ cosetSet t B) (hBLg : B ≤ CFSG.conjugate L g) {x : G}
    (hxC : x ∈ centralizer (L : Set G)) (hxx : x * x = t) : False := by
  have hLM : IsOm6M L := ⟨hS.component.isQuasisimple, hL6⟩
  have hSg : Sec3SettingLB G (g⁻¹ * t * g) (CFSG.conjugate L g) := hS.conjugate g
  have hLM' : IsOm6M (CFSG.conjugate L g) := sec68_isOm6M_conjugate hLM g
  obtain ⟨b₀, hb₀B, hpb⟩ := hgB
  have hb₀1 : b₀ ≠ 1 := by
    intro h
    exact hgt (by rw [hpb, h, mul_one])
  have hb₀sq : b₀ * b₀ = 1 := by
    rw [← pow_two]
    exact hB.1.2 b₀ hb₀B
  have hb₀2 : orderOf b₀ = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (p := 2) (by rwa [pow_two]) hb₀1
  have hxt : x * t = t * x := by
    calc x * t = x * (x * x) := by rw [hxx]
      _ = (x * x) * x := by group
      _ = t * x := by rw [hxx]
  have hxb : ∀ b ∈ B, x * b = b * x := by
    intro b hb
    exact (Subgroup.mem_centralizer_iff.mp hxC b (hBL hb)).symm
  have hxp : x ∈ centralizer ({g⁻¹ * t * g} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, hpb]
    calc x * (t * b₀) = (x * t) * b₀ := by group
      _ = (t * x) * b₀ := by rw [hxt]
      _ = t * (x * b₀) := by group
      _ = t * (b₀ * x) := by rw [hxb b₀ hb₀B]
      _ = (t * b₀) * x := by group
  have hxN : x ∈ normalizer (CFSG.conjugate L g : Set G) :=
    mem_normalizer_of_conjugate_eq (conjugate_eq_self_of_lemma36 h36 hSg x hxp)
  have hB2grp : IsPGroup 2 B := IsPGroup.of_card (n := 4) (by rw [hB.2])
  obtain ⟨P, hP, hBP⟩ := sec68_exists_sylow_ge (H := CFSG.conjugate L g) hB2grp hBLg
  have hcent := hM.cent_B G (CFSG.conjugate L g) hLM' P hP B hBP hB x hxN hxb
  have htC' : t ∈ centralizer (CFSG.conjugate L g : Set G) := by
    rcases hcent with ⟨b, hbB, hbC⟩ | ⟨α, hα⟩ | ⟨α, hα⟩
    · have hb'x : x * b⁻¹ = b⁻¹ * x := hxb b⁻¹ (B.inv_mem hbB)
      have hbb : b⁻¹ * b⁻¹ = 1 := by
        have h2 : b * b = 1 := CFSG.Open.IsElemAbelian.mul_self_eq_one hB.1 hbB
        rw [← mul_inv_rev, h2, inv_one]
      have hcc : (x * b⁻¹) * (x * b⁻¹) = t := by
        calc (x * b⁻¹) * (x * b⁻¹) = x * ((b⁻¹ * x) * b⁻¹) := by group
          _ = x * ((x * b⁻¹) * b⁻¹) := by rw [← hb'x]
          _ = (x * x) * (b⁻¹ * b⁻¹) := by group
          _ = t := by rw [hxx, hbb, mul_one]
      rw [← hcc]
      exact mul_mem hbC hbC
    · have hsq := sec68_sq_mem_centralizer hLM' hα
      rwa [hxx] at hsq
    · have hsq := sec68_sq_mem_centralizer hLM' hα
      rwa [hxx] at hsq
  have hpC : g⁻¹ * t * g ∈ centralizer (CFSG.conjugate L g : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hSg.component.le hl)
  have hb₀C : b₀ ∈ centralizer (CFSG.conjugate L g : Set G) := by
    have hb₀eq : b₀ = t⁻¹ * (g⁻¹ * t * g) := by rw [hpb]; group
    rw [hb₀eq]
    exact mul_mem ((centralizer (CFSG.conjugate L g : Set G)).inv_mem htC') hpC
  have hodd := sec66_odd_of_mem_inf (L := CFSG.conjugate L g) hLM' ⟨hBLg hb₀B, hb₀C⟩
  rw [hb₀2] at hodd
  exact Nat.not_odd_iff_even.mpr even_two hodd

theorem sec68_sylow [Finite G] (h36 : Asc82Lemma36) (h82 : Asc82Lemma82) (hM : Asc82Tab6M)
    {t : G} {L : Subgroup G} (hS : Sec3SettingLB G t L) (hL6 : IsOmega6Minus L)
    {B : Subgroup G} (hB : IsElemAb2 B 4) (hBL : B ≤ L) {g : G} (hgt : g⁻¹ * t * g ≠ t)
    (hgB : g⁻¹ * t * g ∈ cosetSet t B) (hBLg : B ≤ CFSG.conjugate L g) :
    IsSylow2Of (zpowers t) (centralizer (L : Set G)) := by
  have htC : t ∈ centralizer (L : Set G) := sec68_t_mem_centralizer hS
  have hzle : zpowers t ≤ centralizer (L : Set G) := zpowers_le.mpr htC
  have hp2 : IsPGroup 2 (zpowers t) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hS.involution, pow_one]
  obtain ⟨P, hP, hle⟩ := sec68_exists_sylow_ge (H := centralizer (L : Set G)) hp2 hzle
  by_cases hPeq : P = zpowers t
  · rw [← hPeq]
    exact hP
  · have hcyc : IsCyclic P := h82 G t L hS hL6 P hP
    obtain ⟨x, hxP, hxx⟩ :=
      sec68_exists_sq hP.2.1 hcyc (hle (Subgroup.mem_zpowers t)) hS.involution hPeq
    exact (sec68_no_order_four h36 hM hS hL6 hB hBL hgt hgB hBLg (hP.1 hxP) hxx).elim

theorem sec68_stabilizers [Finite G] (h36 : Asc82Lemma36) (hM : Asc82Tab6M) {t : G}
    {L : Subgroup G} (hS : Sec3SettingLB G t L) (hL6 : IsOmega6Minus L) {B : Subgroup G}
    (hB : IsElemAb2 B 4) (hBL : B ≤ L) {g : G} (hgt : g⁻¹ * t * g ≠ t)
    (hgB : g⁻¹ * t * g ∈ cosetSet t B) (hBLg : B ≤ CFSG.conjugate L g) :
    (∀ a ∈ cosetSet t B, a ≠ t → ∀ b ∈ cosetSet t B, b ≠ t →
        ∃ n ∈ normalizer ((zpowers t ⊔ B : Subgroup G) : Set G),
          n * t * n⁻¹ = t ∧ n * a * n⁻¹ = b) ∧
      (∀ a ∈ cosetSet t B, a ≠ g⁻¹ * t * g → ∀ b ∈ cosetSet t B, b ≠ g⁻¹ * t * g →
        ∃ n ∈ normalizer ((zpowers t ⊔ B : Subgroup G) : Set G),
          n * (g⁻¹ * t * g) * n⁻¹ = g⁻¹ * t * g ∧ n * a * n⁻¹ = b) ∧
      ∃ q ∈ cosetSet t B, q ≠ t ∧ q ≠ g⁻¹ * t * g := by
  have hLM : IsOm6M L := ⟨hS.component.isQuasisimple, hL6⟩
  have hSg : Sec3SettingLB G (g⁻¹ * t * g) (CFSG.conjugate L g) := hS.conjugate g
  have hLM' : IsOm6M (CFSG.conjugate L g) := sec68_isOm6M_conjugate hLM g
  have hcoset := sec68_coset_eq hgB
  obtain ⟨b₀, hb₀B, hpb⟩ := hgB
  have hB2grp : IsPGroup 2 B := IsPGroup.of_card (n := 4) (by rw [hB.2])
  obtain ⟨P, hP, hBP⟩ := sec68_exists_sylow_ge (H := L) hB2grp hBL
  obtain ⟨P', hP', hBP'⟩ := sec68_exists_sylow_ge (H := CFSG.conjugate L g) hB2grp hBLg
  have htr := (hM.aut_B G L hLM P hP B hBP hB).2.1
  have htr' := (hM.aut_B G (CFSG.conjugate L g) hLM' P' hP' B hBP' hB).2.1
  have hb₀1 : b₀ ≠ 1 := by
    intro h
    exact hgt (by rw [hpb, h, mul_one])
  have hb₀2 : orderOf b₀ = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (p := 2) (hB.1.2 b₀ hb₀B) hb₀1
  refine ⟨?_, ?_, ?_⟩
  · intro a ha ha_ne b hb hb_ne
    obtain ⟨n, hn, hnt, hnab⟩ :=
      sec68_trans_B (M := L) hS.component.le htr a ha ha_ne b hb hb_ne
    exact ⟨n, (sec68_act (M := L) hS.component.le hn).1, hnt, hnab⟩
  · rw [← hcoset.1]
    intro a ha ha_ne b hb hb_ne
    obtain ⟨n, hn, hnt, hnab⟩ :=
      sec68_trans_B (M := CFSG.conjugate L g) hSg.component.le htr' a ha ha_ne b hb hb_ne
    have hnorm := (sec68_act (M := CFSG.conjugate L g) hSg.component.le hn).1
    rw [hcoset.2] at hnorm
    exact ⟨n, hnorm, hnt, hnab⟩
  · have hnot : ¬ (∀ b ∈ B, b = 1 ∨ b = b₀) := by
      intro hsub
      have hBle : B ≤ zpowers b₀ := by
        intro b hb
        rcases hsub b hb with h | h
        · rw [h]
          exact Subgroup.one_mem _
        · rw [h]
          exact Subgroup.mem_zpowers b₀
      have hle := Subgroup.card_le_of_le hBle
      rw [Nat.card_zpowers, hb₀2, hB.2] at hle
      norm_num at hle
    push Not at hnot
    obtain ⟨b, hbB, hb1, hbb₀⟩ := hnot
    refine ⟨t * b, ⟨b, hbB, rfl⟩, ?_, ?_⟩
    · intro h
      have h' : t * b = t * 1 := by rw [h, mul_one]
      exact hb1 (mul_left_cancel h')
    · intro h
      rw [hpb] at h
      exact hbb₀ (mul_left_cancel h)

end CFSG.OddStandard.SmallF3.Omega
