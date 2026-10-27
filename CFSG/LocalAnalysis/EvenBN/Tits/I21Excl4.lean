module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21Excl3
public import CFSG.GroupTheory.ThompsonIndexTwo

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21.Excl

open Subgroup CFSG.Open CFSG.LocalAnalysis.EvenBN.Tits

variable {L : Type} [Group L] [Finite L]

theorem false_of_normal_index_two [IsSimpleGroup L] (hnab : ∃ a b : L, a * b ≠ b * a)
    {N : Subgroup L} (hN : N.Normal) (hidx : N.index = 2) : False := by
  haveI := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h1 | h1
  · rw [h1, Subgroup.index_bot] at hidx
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI := isCyclic_of_prime_card (α := L) hidx
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (IsCyclic.commGroup.mul_comm a b)
  · rw [h1, Subgroup.index_top] at hidx
    exact absurd hidx (by norm_num)

theorem eq_of_isConj_of_fixed (P : Sylow 2 L) {y : L} (hy : ∀ q ∈ (P : Subgroup L), q * y = y * q)
    (hfix : ∀ n ∈ normalizer (P : Subgroup L), n⁻¹ * y * n = y) {x : L}
    (hx : ∀ q ∈ (P : Subgroup L), q * x = x * q) (hconj : IsConj y x) : x = y := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  have hx' : ∀ q ∈ (P : Subgroup L), q * (g⁻¹⁻¹ * y * g⁻¹) = g⁻¹⁻¹ * y * g⁻¹ * q := by
    rw [inv_inv, hg]
    exact hx
  obtain ⟨n, hn, hn'⟩ := exists_normalizer_conj P hy hx'
  rw [← hg]
  have := hn'.trans (hfix n hn)
  rwa [inv_inv] at this

theorem normalizer_fixes_z0 (P : Sylow 2 L) {c r s : L} {m : ℕ} (h : DihRel c r s m)
    (hP : (P : Subgroup L) = closure ({c, r, s} : Set L)) {n : L}
    (hn : n ∈ normalizer (P : Subgroup L)) : n⁻¹ * z0 r m * n = z0 r m := by
  have hrM : r ∈ closure ({c, r, s} : Set L) := Subgroup.subset_closure (by simp)
  set w : L := r ^ (2 ^ (m - 2)) with hw
  have hz0w : z0 r m = w ^ 2 := by
    rw [z0, hw, ← pow_mul]
    congr 1
    have := h.two_le
    rw [← pow_succ]
    congr 1
    omega
  have hwP : w ∈ (P : Subgroup L) := hP ▸ pow_mem hrM _
  have hnw : n⁻¹ * w * n ∈ closure ({c, r, s} : Set L) :=
    hP ▸ conj_mem_of_mem_normalizer hn hwP
  have h1 : n⁻¹ * z0 r m * n = (n⁻¹ * w * n) ^ 2 := by
    have := conj_pow (a := n⁻¹) (b := w) (i := 2)
    rw [inv_inv] at this
    rw [hz0w, this]
  have ho : orderOf (n⁻¹ * z0 r m * n) = 2 := by rw [orderOf_conj_inv, h.orderOf_z0]
  have hne : n⁻¹ * z0 r m * n ≠ 1 := fun h1 => by rw [h1, orderOf_one] at ho; omega
  have hsq : (n⁻¹ * z0 r m * n) ^ 2 = 1 := ho ▸ pow_orderOf_eq_one _
  rcases h.sq_form hnw with h2 | ⟨i, h2⟩
  · exact absurd (h1.trans h2) hne
  · have hne' : r ^ (2 * i) ≠ 1 := by rw [← h2, ← h1]; exact hne
    have hsq' : (r ^ (2 * i)) ^ 2 = 1 := by rw [← h2, ← h1]; exact hsq
    rw [h1, h2]
    exact h.eq_z0_of_sq_eq_one hne' hsq'

theorem normalizer_c_cases (P : Sylow 2 L) {c r s : L} {m : ℕ} (h : DihRel c r s m)
    (hP : (P : Subgroup L) = closure ({c, r, s} : Set L)) {n : L}
    (hn : n ∈ normalizer (P : Subgroup L)) :
    n⁻¹ * c * n = c ∨ n⁻¹ * c * n = c * z0 r m := by
  have hcM : c ∈ closure ({c, r, s} : Set L) := Subgroup.subset_closure (by simp)
  have hcz0ne : c ≠ z0 r m := fun hc => h.c_nmem (by
    rw [hc, z0]
    exact pow_mem (Subgroup.subset_closure (by simp)) _)
  set x := n⁻¹ * c * n with hx
  have hxP : x ∈ closure ({c, r, s} : Set L) := hP ▸ conj_mem_of_mem_normalizer hn (hP ▸ hcM)
  have hxc : ∀ q ∈ closure ({c, r, s} : Set L), q * x = x * q := by
    intro q hq
    have hq' : n * q * n⁻¹ ∈ closure ({c, r, s} : Set L) := by
      rw [← hP] at hq ⊢
      have := conj_mem_of_mem_normalizer (inv_mem hn) hq
      simpa using this
    have h3 := h.c_central hq'
    calc q * x = n⁻¹ * ((n * q * n⁻¹) * c) * n := by rw [hx]; group
      _ = n⁻¹ * (c * (n * q * n⁻¹)) * n := by rw [h3]
      _ = x * q := by rw [hx]; group
  have ho : orderOf x = 2 := by rw [hx, orderOf_conj_inv, h.orderOf_c]
  rcases h.central_cases hxP hxc with h1 | h1 | h1 | h1
  · rw [h1, orderOf_one] at ho
    omega
  · exfalso
    apply hcz0ne
    have h2 : n⁻¹ * c * n = z0 r m := hx.symm.trans h1
    have h3 := normalizer_fixes_z0 P h hP hn
    have h4 : n⁻¹ * c * n = n⁻¹ * z0 r m * n := h2.trans h3.symm
    exact mul_left_cancel (mul_right_cancel h4)
  · exact Or.inl h1
  · exact Or.inr h1

theorem normalizer_fixes_c (P : Sylow 2 L) {c r s : L} {m : ℕ} (h : DihRel c r s m)
    (hP : (P : Subgroup L) = closure ({c, r, s} : Set L)) {n : L}
    (hn : n ∈ normalizer (P : Subgroup L)) : n⁻¹ * c * n = c := by
  have hcc : ∀ q ∈ (P : Subgroup L), q * c = c * q := fun q hq => h.c_central (hP ▸ hq)
  by_contra hn₀c
  have hn₀' : n⁻¹ * c * n = c * z0 r m :=
    (normalizer_c_cases P h hP hn).resolve_left hn₀c
  set Kc : Subgroup L := centralizer ({c} : Set L) ⊓ normalizer (P : Subgroup L) with hKc
  have hmemK : ∀ n ∈ normalizer (P : Subgroup L), n ∈ Kc ↔ n⁻¹ * c * n = c := by
    intro n hn
    rw [hKc, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    refine ⟨fun ⟨h1, _⟩ => ?_, fun h1 => ⟨?_, hn⟩⟩
    · calc n⁻¹ * c * n = n⁻¹ * (c * n) := by rw [mul_assoc]
        _ = n⁻¹ * (n * c) := by rw [h1]
        _ = c := by group
    · calc n * c = n * (n⁻¹ * c * n) := by rw [h1]
        _ = c * n := by group
  have hPK : (P : Subgroup L) ≤ Kc := by
    intro q hq
    rw [hKc, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    exact ⟨hcc q hq, Subgroup.le_normalizer hq⟩
  have hKN : Kc ≤ normalizer (P : Subgroup L) := inf_le_right
  have h2 : Kc.relIndex (normalizer (P : Subgroup L)) ∣ 2 := by
    rw [Subgroup.relIndex_dvd_two_iff]
    refine ⟨n, hn, fun b hb => ?_⟩
    by_cases hbK : b ∈ Kc
    · exact Or.inr hbK
    · refine Or.inl ?_
      have hb' : b⁻¹ * c * b = c * z0 r m :=
        (normalizer_c_cases P h hP hb).resolve_left (fun h1 => hbK ((hmemK b hb).mpr h1))
      refine (hmemK (b * n) (mul_mem hb hn)).mpr ?_
      calc (b * n)⁻¹ * c * (b * n) = n⁻¹ * (b⁻¹ * c * b) * n := by group
        _ = n⁻¹ * (c * z0 r m) * n := by rw [hb']
        _ = (n⁻¹ * c * n) * (n⁻¹ * z0 r m * n) := by group
        _ = c * z0 r m * z0 r m := by rw [hn₀', normalizer_fixes_z0 P h hP hn]
        _ = c := by rw [mul_assoc, ← sq, h.z0_sq, mul_one]
  have h3 : Kc.relIndex (normalizer (P : Subgroup L)) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h4 | h4
    · exfalso
      exact hn₀c ((hmemK n hn).mp (Subgroup.relIndex_eq_one.mp h4 hn))
    · exact h4
  have h4 := Subgroup.relIndex_mul_relIndex _ _ _ hPK hKN
  rw [h3] at h4
  have h5 : (P : Subgroup L).relIndex (normalizer (P : Subgroup L)) ∣ (P : Subgroup L).index :=
    Subgroup.relIndex_dvd_index_of_le Subgroup.le_normalizer
  apply P.not_dvd_index
  refine dvd_trans ?_ h5
  rw [← h4]
  exact Dvd.intro_left _ rfl

theorem fusion_facts (P : Sylow 2 L) {c r s : L} {m : ℕ} (h : DihRel c r s m)
    (hP : (P : Subgroup L) = closure ({c, r, s} : Set L)) :
    (∀ x : L, (∀ q ∈ (P : Subgroup L), q * x = x * q) → IsConj (z0 r m) x → x = z0 r m) ∧
    (∀ x : L, (∀ q ∈ (P : Subgroup L), q * x = x * q) → IsConj c x → x = c) ∧
    (∀ x : L, (∀ q ∈ (P : Subgroup L), q * x = x * q) → IsConj (c * z0 r m) x →
      x = c * z0 r m) := by
  have hz0c : ∀ q ∈ (P : Subgroup L), q * z0 r m = z0 r m * q := fun q hq =>
    h.z0_central (hP ▸ hq)
  have hcc : ∀ q ∈ (P : Subgroup L), q * c = c * q := fun q hq => h.c_central (hP ▸ hq)
  have hcz0 : ∀ q ∈ (P : Subgroup L), q * (c * z0 r m) = c * z0 r m * q := by
    intro q hq
    rw [← mul_assoc, hcc q hq, mul_assoc, hz0c q hq, mul_assoc]
  have hcz0fix : ∀ n ∈ normalizer (P : Subgroup L), n⁻¹ * (c * z0 r m) * n = c * z0 r m := by
    intro n hn
    calc n⁻¹ * (c * z0 r m) * n = (n⁻¹ * c * n) * (n⁻¹ * z0 r m * n) := by group
      _ = c * z0 r m := by
          rw [normalizer_fixes_c P h hP hn, normalizer_fixes_z0 P h hP hn]
  exact ⟨fun x hx hconj => eq_of_isConj_of_fixed P hz0c
      (fun n hn => normalizer_fixes_z0 P h hP hn) hx hconj,
    fun x hx hconj => eq_of_isConj_of_fixed P hcc
      (fun n hn => normalizer_fixes_c P h hP hn) hx hconj,
    fun x hx hconj => eq_of_isConj_of_fixed P hcz0 hcz0fix hx hconj⟩

theorem zpow_conj_mul {r e : L} (hre : e * r * e⁻¹ = r⁻¹) (k : ℤ) :
    r ^ k * e * (r ^ k)⁻¹ = r ^ (2 * k) * e := by
  have h1 : e * r ^ (-k) = r ^ (- -k) * e := mul_zpow_of_inv hre (-k)
  rw [neg_neg] at h1
  calc r ^ k * e * (r ^ k)⁻¹ = r ^ k * (e * r ^ (-k)) := by rw [zpow_neg, mul_assoc]
    _ = r ^ k * (r ^ k * e) := by rw [h1]
    _ = r ^ (2 * k) * e := by rw [← mul_assoc, ← zpow_add, two_mul]

theorem relIndex_eq_two {P U : Subgroup L} {c : L} (hcP : c ∈ P) (hcU : c ∉ U)
    (hcomm : ∀ b ∈ P, c * b = b * c) (h : ∀ b ∈ P, b ∈ U ∨ c * b ∈ U) : U.relIndex P = 2 := by
  have h1 : U.relIndex P ∣ 2 := by
    rw [Subgroup.relIndex_dvd_two_iff]
    refine ⟨c, hcP, fun b hb => ?_⟩
    rcases h b hb with h2 | h2
    · exact Or.inr h2
    · refine Or.inl ?_
      rwa [← hcomm b hb]
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h2 | h2
  · exact absurd (Subgroup.relIndex_eq_one.mp h2 hcP) hcU
  · exact h2

theorem false_of_not_conj_into [IsSimpleGroup L] (hnab : ∃ a b : L, a * b ≠ b * a)
    (P : Sylow 2 L) {U : Subgroup L} (hUP : U ≤ (P : Subgroup L))
    (hidx : U.relIndex (P : Subgroup L) = 2) {b : L} (hbP : b ∈ (P : Subgroup L)) (hbU : b ∉ U)
    (hbo : orderOf b = 2) (hbconj : ∀ g : L, g⁻¹ * b * g ∉ U) : False := by
  have hmin : ∀ y ∈ (P : Subgroup L), y ∉ U → orderOf b ≤ orderOf y := by
    intro y _ hyU
    have hy1 : y ≠ 1 := fun h1 => hyU (h1 ▸ one_mem U)
    have hpos : 0 < orderOf y := orderOf_pos y
    have hne : orderOf y ≠ 1 := fun h1 => hy1 (orderOf_eq_one_iff.mp h1)
    omega
  obtain ⟨N, hN, hNidx⟩ := CFSG.ThompsonIndexTwo.exists_normal_index_two_of_thompson
    P.isPGroup' P.not_dvd_index hUP hidx hbP hbU hmin hbconj
  exact false_of_normal_index_two hnab hN hNidx

theorem prodDihedral_false [IsSimpleGroup L] (hnab : ∃ a b : L, a * b ≠ b * a) (P : Sylow 2 L)
    {c r s : L} {m : ℕ} (h : DihRel c r s m)
    (hP : (P : Subgroup L) = closure ({c, r, s} : Set L)) : False := by
  obtain ⟨hz0iso, hciso, hcz0iso⟩ := fusion_facts P h hP
  have hcM : c ∈ closure ({c, r, s} : Set L) := Subgroup.subset_closure (by simp)
  have hrM : r ∈ closure ({c, r, s} : Set L) := Subgroup.subset_closure (by simp)
  have hz0M : z0 r m ∈ closure ({c, r, s} : Set L) := pow_mem hrM _
  have hz0P : z0 r m ∈ (P : Subgroup L) := hP ▸ hz0M
  have hz0c : ∀ q ∈ (P : Subgroup L), q * z0 r m = z0 r m * q := fun q hq =>
    h.z0_central (hP ▸ hq)
  have hcc : ∀ q ∈ (P : Subgroup L), q * c = c * q := fun q hq => h.c_central (hP ▸ hq)
  have hcz0 : ∀ q ∈ (P : Subgroup L), q * (c * z0 r m) = c * z0 r m * q := by
    intro q hq
    rw [← mul_assoc, hcc q hq, mul_assoc, hz0c q hq, mul_assoc]
  have hcz0ne : c ≠ z0 r m := fun hc => h.c_nmem (by
    rw [hc, z0]
    exact pow_mem (Subgroup.subset_closure (by simp)) _)
  obtain ⟨g, hgP, hgne⟩ := exists_conj_mem_ne hnab P hz0P hz0c h.orderOf_z0
  set e : L := g⁻¹ * z0 r m * g with he
  have heo : orderOf e = 2 := by rw [he, orderOf_conj_inv, h.orderOf_z0]
  have he2 : e ^ 2 = 1 := heo ▸ pow_orderOf_eq_one e
  have heP : e ∈ closure ({c, r, s} : Set L) := hP ▸ hgP
  have hz0e : IsConj (z0 r m) e := isConj_iff.mpr ⟨g⁻¹, by rw [he, inv_inv]⟩
  have hnc : ¬ ∀ q ∈ closure ({c, r, s} : Set L), q * e = e * q := by
    intro hq
    exact hgne (hz0iso e (fun q hq' => hq q (hP ▸ hq')) hz0e)
  obtain ⟨h', hcl⟩ := h.of_noncentral_involution heP he2 hnc
  have hP' : (P : Subgroup L) = closure ({c, r, e} : Set L) := hP.trans hcl.symm
  have hre : e * r * e⁻¹ = r⁻¹ := h'.srs
  set U : Subgroup L := closure ({r, e} : Set L) with hU
  have hrU : r ∈ U := Subgroup.subset_closure (by simp)
  have heU : e ∈ U := Subgroup.subset_closure (by simp)
  have hz0U : z0 r m ∈ U := pow_mem hrU _
  have hUP : U ≤ (P : Subgroup L) := by
    rw [hU, Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hP ▸ hrM
    · exact hP ▸ heP
  have hcU : c ∉ U := h'.c_nmem
  have hcP : c ∈ (P : Subgroup L) := hP ▸ hcM
  have hidx : U.relIndex (P : Subgroup L) = 2 :=
    relIndex_eq_two hcP hcU (fun b hb => (h'.c_central (hP' ▸ hb)).symm) fun b hb =>
      exists_mem_or_mul_mem h'.c_sq h'.cr h'.cs hrU heU (hP' ▸ hb)
  have hcz0o : orderOf (c * z0 r m) = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcomm : Commute c (z0 r m) := h.z0_comm_c.symm
    refine orderOf_eq_prime ?_ ?_
    · rw [hcomm.mul_pow, h.c_sq, h.z0_sq, one_mul]
    · intro h1
      apply hcz0ne
      have : c = (z0 r m)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact inv_eq_of_mul_eq_one_right (by rw [← sq]; exact h.z0_sq)
  have hodd : ∀ b : L, (b = c ∨ b = c * z0 r m) → orderOf b = 2 →
      (∀ q ∈ (P : Subgroup L), q * b = b * q) → (b ≠ z0 r m) →
      ∀ g : L, g⁻¹ * b * g ∈ U → ∃ j : ℤ, Odd j ∧ g⁻¹ * b * g = r ^ j * e := by
    intro b _ hbo hbc hbne g' hg'
    set u := g'⁻¹ * b * g' with hu
    have huo : orderOf u = 2 := by rw [hu, orderOf_conj_inv, hbo]
    have hu1 : u ≠ 1 := fun h1 => by rw [h1, orderOf_one] at huo; omega
    have hu2 : u ^ 2 = 1 := huo ▸ pow_orderOf_eq_one u
    have hbu : IsConj b u := isConj_iff.mpr ⟨g'⁻¹, by rw [hu, inv_inv]⟩
    obtain ⟨j, hj | hj⟩ := exists_zpow_of_mem_closure_dih he2 hre hg'
    · exfalso
      have h1 : r ^ j = z0 r m :=
        h'.eq_z0_of_sq_eq_one (by rw [← hj]; exact hu1) (by rw [← hj]; exact hu2)
      rw [h1] at hj
      exact hbne (hz0iso b hbc (by rw [hj] at hbu; exact hbu.symm))
    · refine ⟨j, ?_, hj⟩
      by_contra hjodd
      rw [Int.not_odd_iff_even] at hjodd
      obtain ⟨k, hk⟩ := hjodd
      have hconj : IsConj e u := by
        rw [hj, show j = 2 * k by omega, ← zpow_conj_mul hre k]
        exact isConj_iff.mpr ⟨r ^ k, rfl⟩
      exact hbne (hz0iso b hbc ((hz0e.trans hconj).trans hbu.symm))
  have hexists : ∃ b : L, (b = c ∨ b = c * z0 r m) ∧ ∀ g : L, g⁻¹ * b * g ∉ U := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g₁, hg₁⟩ := hcon c (Or.inl rfl)
    obtain ⟨g₂, hg₂⟩ := hcon (c * z0 r m) (Or.inr rfl)
    have hne2 : c * z0 r m ≠ z0 r m := fun h1 =>
      h.c_ne_one (mul_right_cancel (h1.trans (one_mul _).symm))
    obtain ⟨j₁, hj₁, hu₁⟩ := hodd c (Or.inl rfl) h.orderOf_c hcc hcz0ne g₁ hg₁
    obtain ⟨j₂, hj₂, hu₂⟩ := hodd (c * z0 r m) (Or.inr rfl) hcz0o hcz0 hne2 g₂ hg₂
    obtain ⟨k, hk⟩ : ∃ k : ℤ, j₂ = j₁ + 2 * k := by
      obtain ⟨a, ha⟩ := hj₁
      obtain ⟨b, hb⟩ := hj₂
      exact ⟨b - a, by omega⟩
    have hc1 : IsConj c (r ^ j₁ * e) := hu₁ ▸ isConj_iff.mpr ⟨g₁⁻¹, by rw [inv_inv]⟩
    have hc2 : IsConj (c * z0 r m) (r ^ j₂ * e) :=
      hu₂ ▸ isConj_iff.mpr ⟨g₂⁻¹, by rw [inv_inv]⟩
    have hu12 : IsConj (r ^ j₁ * e) (r ^ j₂ * e) := by
      refine isConj_iff.mpr ⟨r ^ k, ?_⟩
      have h1 := zpow_conj_mul hre k
      have h2 : r ^ k * r ^ j₁ = r ^ j₁ * r ^ k := (Commute.zpow_zpow_self r k j₁).eq
      calc r ^ k * (r ^ j₁ * e) * (r ^ k)⁻¹ = (r ^ k * r ^ j₁) * e * (r ^ k)⁻¹ := by
            simp only [mul_assoc]
        _ = (r ^ j₁ * r ^ k) * e * (r ^ k)⁻¹ := by rw [h2]
        _ = r ^ j₁ * (r ^ k * e * (r ^ k)⁻¹) := by simp only [mul_assoc]
        _ = r ^ j₁ * (r ^ (2 * k) * e) := by rw [h1]
        _ = r ^ j₂ * e := by rw [← mul_assoc, ← zpow_add, hk]
    have hcc' : IsConj c (c * z0 r m) := hc1.trans (hu12.trans hc2.symm)
    have h3 := hciso (c * z0 r m) hcz0 hcc'
    exact h.z0_ne_one (mul_left_cancel (h3.trans (mul_one c).symm))
  obtain ⟨b, hb, hbconj⟩ := hexists
  have hbP : b ∈ (P : Subgroup L) := by
    rcases hb with rfl | rfl
    · exact hcP
    · exact mul_mem hcP hz0P
  have hbU : b ∉ U := by
    rcases hb with rfl | rfl
    · exact hcU
    · intro h1
      apply hcU
      have := mul_mem h1 (inv_mem hz0U)
      simpa using this
  have hbo : orderOf b = 2 := by
    rcases hb with rfl | rfl
    · exact h.orderOf_c
    · exact hcz0o
  exact false_of_not_conj_into hnab P hUP hidx hbP hbU hbo hbconj

end CFSG.LocalAnalysis.EvenBN.Tits.I21.Excl
