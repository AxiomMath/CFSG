module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseTwoSetup

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open Equiv Equiv.Perm
open scoped commutatorElement

theorem a11TwoSetStab_exists_threeCycle_mem_commutator {i j : Fin 11} (hij : i ≠ j)
    {a b c : Fin 11} (hai : a ≠ i) (haj : a ≠ j)
    (hbi : b ≠ i) (hbj : b ≠ j) (hci : c ≠ i) (hcj : c ≠ j)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ t ∈ ⁅a11TwoSetStab i j, a11TwoSetStab i j⁆,
      (t : Equiv.Perm (Fin 11)) a = b ∧
      (t : Equiv.Perm (Fin 11)) b = c ∧
      (t : Equiv.Perm (Fin 11)) c = a ∧
      (t : Equiv.Perm (Fin 11)).support = {a, b, c} := by
  classical
  have hxmem : (swap a b * swap i j) ∈ alternatingGroup (Fin 11) := by
    rw [mem_alternatingGroup, Perm.sign_mul, sign_swap hab, sign_swap hij]
    norm_num
  have hymem : (swap a c * swap i j) ∈ alternatingGroup (Fin 11) := by
    rw [mem_alternatingGroup, Perm.sign_mul, sign_swap hac, sign_swap hij]
    norm_num
  let x : alternatingGroup (Fin 11) := ⟨swap a b * swap i j, hxmem⟩
  let y : alternatingGroup (Fin 11) := ⟨swap a c * swap i j, hymem⟩
  have hxS : x ∈ a11TwoSetStab i j := by
    change ((x : Perm (Fin 11)) i = i ∧ (x : Perm (Fin 11)) j = j) ∨
      ((x : Perm (Fin 11)) i = j ∧ (x : Perm (Fin 11)) j = i)
    right
    constructor
    · change (swap a b * swap i j) i = j
      rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne haj.symm hbj.symm]
    · change (swap a b * swap i j) j = i
      rw [Perm.mul_apply, swap_apply_right, swap_apply_of_ne_of_ne hai.symm hbi.symm]
  have hyS : y ∈ a11TwoSetStab i j := by
    change ((y : Perm (Fin 11)) i = i ∧ (y : Perm (Fin 11)) j = j) ∨
      ((y : Perm (Fin 11)) i = j ∧ (y : Perm (Fin 11)) j = i)
    right
    constructor
    · change (swap a c * swap i j) i = j
      rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne haj.symm hcj.symm]
    · change (swap a c * swap i j) j = i
      rw [Perm.mul_apply, swap_apply_right, swap_apply_of_ne_of_ne hai.symm hci.symm]
  have hAB : Commute (swap a b) (swap i j) :=
    Perm.Disjoint.commute (Perm.disjoint_swap_swap (by simp [hai, haj, hbi, hbj, hij, hab]))
  have hCB : Commute (swap a c) (swap i j) :=
    Perm.Disjoint.commute (Perm.disjoint_swap_swap (by simp [hac, hai, haj, hci, hcj, hij]))
  have hBB : swap i j * swap i j = 1 := Equiv.swap_mul_self _ _
  have hxy : (swap a b * swap i j) * (swap a c * swap i j) =
      swap a b * swap a c := by
    calc
      (swap a b * swap i j) * (swap a c * swap i j)
          = swap a b * (swap i j * swap a c) * swap i j := by group
      _ = swap a b * (swap a c * swap i j) * swap i j := by rw [hCB.eq]
      _ = swap a b * swap a c * (swap i j * swap i j) := by group
      _ = swap a b * swap a c := by rw [hBB, mul_one]
  have hxinv : (swap a b * swap i j)⁻¹ = swap i j * swap a b := by
    rw [mul_inv_rev]
    simp
  have hyinv : (swap a c * swap i j)⁻¹ = swap i j * swap a c := by
    rw [mul_inv_rev]
    simp
  have hxiny : (swap a b * swap i j)⁻¹ * (swap a c * swap i j)⁻¹ =
      swap a b * swap a c := by
    rw [hxinv, hyinv]
    calc
      (swap i j * swap a b) * (swap i j * swap a c)
          = (swap i j * swap a b) * swap i j * swap a c := by group
      _ = swap i j * (swap a b * swap i j) * swap a c := by group
      _ = swap i j * (swap i j * swap a b) * swap a c := by rw [hAB.eq]
      _ = (swap i j * swap i j) * swap a b * swap a c := by group
      _ = swap a b * swap a c := by rw [hBB, one_mul]
  have hcyc : (swap a b * swap a c).IsThreeCycle :=
    Perm.isThreeCycle_swap_mul_swap_same hab hac hbc
  have hcube : (swap a b * swap a c) ^ 3 = 1 := by
    rw [← hcyc.orderOf, pow_orderOf_eq_one]
  have hprod : (swap a b * swap i j) * (swap a c * swap i j) *
        (swap a b * swap i j)⁻¹ * (swap a c * swap i j)⁻¹ =
      swap a c * swap a b := by
    calc
      (swap a b * swap i j) * (swap a c * swap i j) *
          (swap a b * swap i j)⁻¹ * (swap a c * swap i j)⁻¹
          = (swap a b * swap a c) * ((swap a b * swap i j)⁻¹ *
            (swap a c * swap i j)⁻¹) := by rw [hxy]; group
      _ = (swap a b * swap a c) * (swap a b * swap a c) := by rw [hxiny]
      _ = (swap a b * swap a c) ^ 2 := by rw [pow_two, ← mul_assoc]
      _ = (swap a b * swap a c)⁻¹ := by
        have h3' : (swap a b * swap a c) ^ 2 * (swap a b * swap a c) = 1 := by
          simpa [pow_succ] using hcube
        exact eq_inv_of_mul_eq_one_left h3'
      _ = swap a c * swap a b := by
        rw [mul_inv_rev]
        simp
  have htval : ((⁅x, y⁆ : alternatingGroup (Fin 11)) : Perm (Fin 11)) =
      swap a c * swap a b := by
    rw [commutatorElement_def]
    change ((x : Perm (Fin 11)) * (y : Perm (Fin 11)) * (x : Perm (Fin 11))⁻¹ *
      (y : Perm (Fin 11))⁻¹) = swap a c * swap a b
    dsimp [x, y]
    exact hprod
  refine ⟨⁅x, y⁆, Subgroup.commutator_mem_commutator hxS hyS, ?_, ?_, ?_, ?_⟩
  · rw [htval]
    rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hab.symm hbc]
  · rw [htval]
    rw [Perm.mul_apply, swap_apply_right, swap_apply_left]
  · rw [htval]
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hbc)]
    rw [swap_apply_right]
  · have hcycle : (swap a c * swap a b).IsThreeCycle :=
      Perm.isThreeCycle_swap_mul_swap_same hac hab hbc.symm
    have ht_a : ((⁅x, y⁆ : alternatingGroup (Fin 11)) : Perm (Fin 11)) a = b := by
      rw [htval]
      rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hab.symm hbc]
    have ht_b : ((⁅x, y⁆ : alternatingGroup (Fin 11)) : Perm (Fin 11)) b = c := by
      rw [htval]
      rw [Perm.mul_apply, swap_apply_right, swap_apply_left]
    have ht_c : ((⁅x, y⁆ : alternatingGroup (Fin 11)) : Perm (Fin 11)) c = a := by
      rw [htval]
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hbc)]
      rw [swap_apply_right]
    have ha_mem : a ∈ ((⁅x, y⁆ : alternatingGroup (Fin 11)) : Perm (Fin 11)).support := by
      rw [Perm.mem_support, ht_a]
      exact hab.symm
    have hsupp := (Perm.IsThreeCycle.support_eq_iff_mem_support
      (by rw [htval]; exact hcycle)).mpr ha_mem
    rw [ht_a, ht_b] at hsupp
    exact hsupp

lemma eq_one_or_eq_swap_of_fixes_omega {i j : Fin 11} (hij : i ≠ j)
    {σ : Equiv.Perm (Fin 11)}
    (hfix : ∀ a, a ∈ ((Finset.univ.erase i).erase j) → σ a = a) :
    σ = 1 ∨ σ = Equiv.swap i j := by
  classical
  let Ω : Finset (Fin 11) := (Finset.univ.erase i).erase j
  have hmem : ∀ x, x ∈ Ω ↔ x ≠ i ∧ x ≠ j := by
    intro x
    simp [Ω, Finset.mem_erase, and_assoc, and_comm, and_left_comm]
  have hnot : ∀ x, x ∉ Ω ↔ x = i ∨ x = j := by
    intro x
    rw [hmem]
    tauto
  have hcompl : ∀ x, x ∉ Ω → σ x ∉ Ω := by
    intro x hx hσx
    have h1 : σ (σ x) = σ x := hfix (σ x) hσx
    have h2 : σ x = x := σ.injective h1
    exact hx (h2 ▸ hσx)
  have hi_not : i ∉ Ω := by
    rw [hnot]
    exact Or.inl rfl
  have hj_not : j ∉ Ω := by
    rw [hnot]
    exact Or.inr rfl
  have hσi : σ i = i ∨ σ i = j := (hnot (σ i)).mp (hcompl i hi_not)
  have hσj : σ j = i ∨ σ j = j := (hnot (σ j)).mp (hcompl j hj_not)
  rcases hσi with hi | hi
  · left
    have hj : σ j = j := by
      rcases hσj with hji | hjj
      · exact absurd (σ.injective (hji.trans hi.symm)) hij.symm
      · exact hjj
    ext x
    by_cases hxi : x = i
    · rw [hxi, hi]; rfl
    · by_cases hxj : x = j
      · rw [hxj, hj]; rfl
      · have hxΩ : x ∈ Ω := (hmem x).mpr ⟨hxi, hxj⟩
        rw [hfix x hxΩ]; rfl
  · right
    have hj : σ j = i := by
      rcases hσj with hji | hjj
      · exact hji
      · exact absurd (σ.injective (hjj.trans hi.symm)) hij.symm
    ext x
    by_cases hxi : x = i
    · rw [hxi, hi]; rw [Equiv.swap_apply_left]
    · by_cases hxj : x = j
      · rw [hxj, hj]; rw [Equiv.swap_apply_right]
      · have hxΩ : x ∈ Ω := (hmem x).mpr ⟨hxi, hxj⟩
        rw [hfix x hxΩ]
        rw [Equiv.swap_apply_of_ne_of_ne hxi hxj]

theorem eq_one_or_eq_swap_of_forall_conjNormal_eq {i j : Fin 11} (hij : i ≠ j)
    {σ : Equiv.Perm (Fin 11)}
    (hσ : ∀ x ∈ ⁅a11TwoSetStab i j, a11TwoSetStab i j⁆,
      (MulAut.conjNormal σ) x = x) :
    σ = 1 ∨ σ = Equiv.swap i j := by
  classical
  let Ω : Finset (Fin 11) := (Finset.univ.erase i).erase j
  have hΩcard : Ω.card = 9 := by
    change ((Finset.univ.erase i).erase j).card = 9
    rw [Finset.card_erase_of_mem
        (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩),
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin]
  have hmem : ∀ x, x ∈ Ω ↔ x ≠ i ∧ x ≠ j := by
    intro x
    simp [Ω, Finset.mem_erase, and_assoc, and_comm, and_left_comm]
  have hconj : ∀ g : alternatingGroup (Fin 11),
      g ∈ ⁅a11TwoSetStab i j, a11TwoSetStab i j⁆ →
      ∀ k : Fin 11, σ k ∈ (g : Equiv.Perm (Fin 11)).support ↔
        k ∈ (g : Equiv.Perm (Fin 11)).support := by
    intro g hg k
    have hval : σ * (g : Equiv.Perm (Fin 11)) * σ⁻¹ = (g : Equiv.Perm (Fin 11)) := by
      have := congrArg (fun u : alternatingGroup (Fin 11) =>
        (u : Equiv.Perm (Fin 11))) (hσ g hg)
      simpa [MulAut.conjNormal_apply] using this
    have hsupp : (g : Equiv.Perm (Fin 11)).support =
        Finset.map σ.toEmbedding (g : Equiv.Perm (Fin 11)).support := by
      have h := Equiv.Perm.support_conj (σ := σ) (τ := (g : Equiv.Perm (Fin 11)))
      rwa [hval] at h
    constructor
    · intro hk
      rw [hsupp, Finset.mem_map] at hk
      obtain ⟨y, hy, hyk⟩ := hk
      rwa [σ.injective hyk] at hy
    · intro hk
      rw [hsupp, Finset.mem_map]
      exact ⟨k, hk, rfl⟩
  have hfix : ∀ a, a ∈ Ω → σ a = a := by
    intro a ha
    obtain ⟨b, hb, -⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := (∅ : Finset (Fin 11))) (t := Ω.erase a) (by
        rw [Finset.card_erase_of_mem ha, hΩcard]
        simp)
    obtain ⟨c, hc, -⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := (∅ : Finset (Fin 11))) (t := (Ω.erase a).erase b) (by
        rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem ha, hΩcard]
        simp)
    have hbΩ : b ∈ Ω := (Finset.mem_erase.mp hb).2
    have hba : b ≠ a := (Finset.mem_erase.mp hb).1
    have hcΩ : c ∈ Ω := (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).2
    have hca : c ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).1
    have hcb : c ≠ b := (Finset.mem_erase.mp hc).1
    obtain ⟨hai, haj⟩ := (hmem a).mp ha
    obtain ⟨hbi, hbj⟩ := (hmem b).mp hbΩ
    obtain ⟨hci, hcj⟩ := (hmem c).mp hcΩ
    obtain ⟨t, htC, hta, htb, htc, hsupp⟩ :=
      a11TwoSetStab_exists_threeCycle_mem_commutator hij hai haj hbi hbj hci hcj
        hba.symm hca.symm hcb.symm
    have hsub : ({a, b, c} : Finset (Fin 11)) ⊆ Ω := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact ha
      · exact hbΩ
      · exact hcΩ
    have hσaΩ : σ a ∈ Ω := by
      apply hsub
      have hmem_supp : σ a ∈ (t : Equiv.Perm (Fin 11)).support := by
        rw [hconj t htC]
        rw [Equiv.Perm.mem_support, hta]
        exact hba
      rwa [hsupp] at hmem_supp
    by_cases hσaa : σ a = a
    · exact hσaa
    · have hdlt : ({a, σ a} : Finset (Fin 11)).card < Ω.card := by
        rw [hΩcard]
        have h2 : ({a, σ a} : Finset (Fin 11)).card ≤ 2 := by
          calc ({a, σ a} : Finset (Fin 11)).card ≤ ({σ a} : Finset (Fin 11)).card + 1 :=
                Finset.card_insert_le _ _
            _ = 2 := by simp
        omega
      obtain ⟨d, hdΩ, hdnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hdlt
      have hda : d ≠ a := by
        intro h
        exact hdnot (by simp [h])
      have hds : d ≠ σ a := by
        intro h
        exact hdnot (by simp [h])
      have helt : ({a, d, σ a} : Finset (Fin 11)).card < Ω.card := by
        rw [hΩcard]
        have h3 : ({a, d, σ a} : Finset (Fin 11)).card ≤ 3 := Finset.card_le_three
        omega
      obtain ⟨e, heΩ, henot⟩ := Finset.exists_mem_notMem_of_card_lt_card helt
      have hea : e ≠ a := by
        intro h
        exact henot (by simp [h])
      have hed : e ≠ d := by
        intro h
        exact henot (by simp [h])
      have hes : e ≠ σ a := by
        intro h
        exact henot (by simp [h])
      obtain ⟨hai, haj⟩ := (hmem a).mp ha
      obtain ⟨hdi, hdj⟩ := (hmem d).mp hdΩ
      obtain ⟨hei, hej⟩ := (hmem e).mp heΩ
      obtain ⟨u, huC, hua, hud, hue, husupp⟩ :=
        a11TwoSetStab_exists_threeCycle_mem_commutator hij hai haj hdi hdj hei hej
          hda.symm hea.symm hed.symm
      have humem : σ a ∈ (u : Equiv.Perm (Fin 11)).support := by
        rw [hconj u huC]
        rw [Equiv.Perm.mem_support, hua]
        exact hda
      rw [husupp] at humem
      simp only [Finset.mem_insert, Finset.mem_singleton] at humem
      exfalso
      rcases humem with h | h | h
      · exact hσaa h
      · exact hds h.symm
      · exact hes h.symm
  exact eq_one_or_eq_swap_of_fixes_omega hij (by simpa [Ω] using hfix)

private lemma eq_one_of_fixes_omega {i j : Fin 11} (hij : i ≠ j)
    {d : alternatingGroup (Fin 11)}
    (hfix : ∀ a, a ∈ ((Finset.univ.erase i).erase j) → (d : Equiv.Perm (Fin 11)) a = a) :
    d = 1 := by
  rcases eq_one_or_eq_swap_of_fixes_omega hij hfix with h | h
  · exact Subtype.ext h
  · exfalso
    have hsign : Equiv.Perm.sign (d : Equiv.Perm (Fin 11)) = 1 :=
      Equiv.Perm.mem_alternatingGroup.mp d.2
    rw [h, Equiv.Perm.sign_swap hij] at hsign
    norm_num at hsign

private lemma orbit_map_subset {i j : Fin 11}
    {D : Subgroup (alternatingGroup (Fin 11))}
    (hN : ⁅a11TwoSetStab i j, a11TwoSetStab i j⁆ ≤
      Subgroup.normalizer (D : Set (alternatingGroup (Fin 11))))
    {g : alternatingGroup (Fin 11)}
    (hg : g ∈ ⁅a11TwoSetStab i j, a11TwoSetStab i j⁆)
    {a x : Fin 11} (hx : x ∈ MulAction.orbit D a) :
    g • x ∈ MulAction.orbit D (g • a) := by
  rw [MulAction.mem_orbit_iff] at hx ⊢
  obtain ⟨d, hd⟩ := hx
  subst hd
  refine ⟨⟨g * d * g⁻¹, ?_⟩, ?_⟩
  · have hgN := hN hg
    rw [Subgroup.mem_normalizer_iff] at hgN
    exact (hgN d).mp d.2
  · simp only [Subgroup.smul_def, Equiv.Perm.smul_def, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    simp

private lemma omega_subset_orbit_of_two {i j : Fin 11} (hij : i ≠ j)
    {D : Subgroup (alternatingGroup (Fin 11))}
    (hN : ⁅a11TwoSetStab i j, a11TwoSetStab i j⁆ ≤
      Subgroup.normalizer (D : Set (alternatingGroup (Fin 11))))
    {a b : Fin 11}
    (ha : a ∈ ((Finset.univ.erase i).erase j))
    (hb : b ∈ ((Finset.univ.erase i).erase j))
    (hab : a ≠ b)
    (hbO : b ∈ MulAction.orbit D a) :
    ∀ c ∈ ((Finset.univ.erase i).erase j), c ∈ MulAction.orbit D a := by
  classical
  let Ω : Finset (Fin 11) := (Finset.univ.erase i).erase j
  have hΩcard : Ω.card = 9 := by
    change ((Finset.univ.erase i).erase j).card = 9
    rw [Finset.card_erase_of_mem
        (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩),
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin]
  have hmem : ∀ x, x ∈ Ω ↔ x ≠ i ∧ x ≠ j := by
    intro x
    simp [Ω, Finset.mem_erase, and_assoc, and_comm, and_left_comm]
  intro c hc
  by_cases hca : c = a
  · rw [hca]
    simpa using MulAction.mem_orbit a (1 : D)
  by_cases hcb : c = b
  · rw [hcb]
    exact hbO
  · have hdlt : ({a, b, c} : Finset (Fin 11)).card < Ω.card := by
      rw [hΩcard]
      have h3 : ({a, b, c} : Finset (Fin 11)).card ≤ 3 := Finset.card_le_three
      omega
    obtain ⟨d, hdΩ, hdnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hdlt
    have hda : d ≠ a := by
      intro h
      exact hdnot (by simp [h])
    have hdb : d ≠ b := by
      intro h
      exact hdnot (by simp [h])
    have hdc : d ≠ c := by
      intro h
      exact hdnot (by simp [h])
    obtain ⟨hai, haj⟩ := (hmem a).mp ha
    obtain ⟨hbi, hbj⟩ := (hmem b).mp hb
    obtain ⟨hci, hcj⟩ := (hmem c).mp hc
    obtain ⟨hdi, hdj⟩ := (hmem d).mp hdΩ
    obtain ⟨t, htC, htb, htc, htd, hsupp⟩ :=
      a11TwoSetStab_exists_threeCycle_mem_commutator hij hbi hbj hci hcj hdi hdj
        (Ne.symm hcb) (Ne.symm hdb) (Ne.symm hdc)
    have hac : a ≠ c := fun h => hca h.symm
    have had : a ≠ d := fun h => hda h.symm
    have hta : (t : Equiv.Perm (Fin 11)) a = a := by
      apply Equiv.Perm.notMem_support.mp
      rw [hsupp]
      simp [hab, hac, had]
    have hta' : t • a = a := by
      rw [Subgroup.smul_def, Equiv.Perm.smul_def, hta]
    have htb' : t • b = c := by
      rw [Subgroup.smul_def, Equiv.Perm.smul_def, htb]
    have htmap := orbit_map_subset (i := i) (j := j) hN htC hbO
    rw [hta', htb'] at htmap
    exact htmap

private lemma not_two_omega_in_orbit {i j : Fin 11} (hij : i ≠ j)
    {D : Subgroup (alternatingGroup (Fin 11))} (hD : IsPGroup 2 D)
    (hN : ⁅a11TwoSetStab i j, a11TwoSetStab i j⁆ ≤
      Subgroup.normalizer (D : Set (alternatingGroup (Fin 11))))
    {a b : Fin 11}
    (ha : a ∈ ((Finset.univ.erase i).erase j))
    (hb : b ∈ ((Finset.univ.erase i).erase j))
    (hab : a ≠ b)
    (hbO : b ∈ MulAction.orbit D a) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Ω : Finset (Fin 11) := (Finset.univ.erase i).erase j
  have hΩcard : Ω.card = 9 := by
    change ((Finset.univ.erase i).erase j).card = 9
    rw [Finset.card_erase_of_mem
        (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩),
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin]
  have hsub : ∀ c ∈ Ω, c ∈ MulAction.orbit D a :=
    omega_subset_orbit_of_two hij hN ha hb hab hbO
  have hΩsub : (Ω : Set (Fin 11)) ⊆ MulAction.orbit D a := by
    intro c hc
    exact hsub c hc
  have hinj : Function.Injective (fun x : {x // x ∈ Ω} =>
      (⟨x.1, hΩsub x.2⟩ : MulAction.orbit D a)) := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : MulAction.orbit D a => (z : Fin 11)) hxy
  have h9 : 9 ≤ Nat.card (MulAction.orbit D a) := by
    have hle := Fintype.card_le_of_injective
      (fun x : {x // x ∈ Ω} => (⟨x.1, hΩsub x.2⟩ : MulAction.orbit D a)) hinj
    simpa [Nat.card_eq_fintype_card, Fintype.card_coe, hΩcard] using hle
  have hupper : Nat.card (MulAction.orbit D a) ≤ 11 := by
    have hinj2 : Function.Injective (fun x : MulAction.orbit D a => (x : Fin 11)) := by
      intro x y hxy
      exact Subtype.ext hxy
    have hle := Fintype.card_le_of_injective
      (fun x : MulAction.orbit D a => (x : Fin 11)) hinj2
    simpa [Nat.card_eq_fintype_card] using hle
  obtain ⟨n, hn⟩ := hD.card_orbit a
  have h9' : 9 ≤ 2 ^ n := by rwa [← hn]
  have h11' : 2 ^ n ≤ 11 := by rwa [← hn]
  have hn4 : n < 4 := by
    by_contra h
    have h4 : 4 ≤ n := by omega
    have hge : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h4
    omega
  have hn_cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases hn_cases with h0 | h1 | h2 | h3
  · rw [h0] at h9'; norm_num at h9'
  · rw [h1] at h9'; norm_num at h9'
  · rw [h2] at h9'; norm_num at h9'
  · rw [h3] at h9'; norm_num at h9'

private lemma false_of_orbit_meets_omega {i j : Fin 11} (hij : i ≠ j)
    {D : Subgroup (alternatingGroup (Fin 11))} (hD : IsPGroup 2 D)
    (hN : ⁅a11TwoSetStab i j, a11TwoSetStab i j⁆ ≤
      Subgroup.normalizer (D : Set (alternatingGroup (Fin 11))))
    {k a : Fin 11} (hk : k = i ∨ k = j)
    (ha : a ∈ ((Finset.univ.erase i).erase j))
    (haO : a ∈ MulAction.orbit D k) : False := by
  classical
  let Ω : Finset (Fin 11) := (Finset.univ.erase i).erase j
  have hΩcard : Ω.card = 9 := by
    change ((Finset.univ.erase i).erase j).card = 9
    rw [Finset.card_erase_of_mem
        (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩),
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin]
  have hmem : ∀ x, x ∈ Ω ↔ x ≠ i ∧ x ≠ j := by
    intro x
    simp [Ω, Finset.mem_erase, and_assoc, and_comm, and_left_comm]
  obtain ⟨b, hb, -⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := (∅ : Finset (Fin 11))) (t := Ω.erase a) (by
      rw [Finset.card_erase_of_mem ha, hΩcard]
      simp)
  obtain ⟨e, he, -⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := (∅ : Finset (Fin 11))) (t := (Ω.erase a).erase b) (by
      rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem ha, hΩcard]
      simp)
  have hbΩ : b ∈ Ω := (Finset.mem_erase.mp hb).2
  have hba : b ≠ a := (Finset.mem_erase.mp hb).1
  have heΩ : e ∈ Ω := (Finset.mem_erase.mp (Finset.mem_erase.mp he).2).2
  have hea : e ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp he).2).1
  have heb : e ≠ b := (Finset.mem_erase.mp he).1
  obtain ⟨hai, haj⟩ := (hmem a).mp ha
  obtain ⟨hbi, hbj⟩ := (hmem b).mp hbΩ
  obtain ⟨hei, hej⟩ := (hmem e).mp heΩ
  obtain ⟨t, htC, hta, htb, hte, hsupp⟩ :=
    a11TwoSetStab_exists_threeCycle_mem_commutator hij hai haj hbi hbj hei hej
      hba.symm hea.symm heb.symm
  have htk : (t : Equiv.Perm (Fin 11)) k = k := by
    apply Equiv.Perm.notMem_support.mp
    rw [hsupp]
    rcases hk with rfl | rfl
    · simp [hai.symm, hbi.symm, hei.symm]
    · simp [haj.symm, hbj.symm, hej.symm]
  have htk' : t • k = k := by
    rw [Subgroup.smul_def, Equiv.Perm.smul_def, htk]
  have hta' : t • a = b := by
    rw [Subgroup.smul_def, Equiv.Perm.smul_def, hta]
  have htmap := orbit_map_subset (i := i) (j := j) hN htC haO
  rw [htk', hta'] at htmap
  have hbOa : b ∈ MulAction.orbit D a := by
    have horb : MulAction.orbit D a = MulAction.orbit D k :=
      (MulAction.orbit_eq_iff).mpr haO
    rw [horb]
    exact htmap
  exact not_two_omega_in_orbit hij hD hN ha hbΩ hba.symm hbOa

theorem a11TwoSetStab_twoSubgroup_eq_bot {i j : Fin 11} (hij : i ≠ j)
    {D : Subgroup (alternatingGroup (Fin 11))} (hD : IsPGroup 2 D)
    (hN : ⁅a11TwoSetStab i j, a11TwoSetStab i j⁆ ≤
      Subgroup.normalizer (D : Set (alternatingGroup (Fin 11)))) :
    D = ⊥ := by
  classical
  rw [Subgroup.eq_bot_iff_forall]
  intro d hd
  let dD : D := ⟨d, hd⟩
  let Ω : Finset (Fin 11) := (Finset.univ.erase i).erase j
  have hmem : ∀ x, x ∈ Ω ↔ x ≠ i ∧ x ≠ j := by
    intro x
    simp [Ω, Finset.mem_erase, and_assoc, and_comm, and_left_comm]
  have hnot : ∀ x, x ∉ Ω ↔ x = i ∨ x = j := by
    intro x
    rw [hmem x]
    tauto
  have hfix : ∀ a, a ∈ Ω → (d : Equiv.Perm (Fin 11)) a = a := by
    intro a ha
    by_contra hda
    have hda_eq : dD • a = (d : Equiv.Perm (Fin 11)) a := by
      rw [Subgroup.smul_def]
      change (((dD : D) : alternatingGroup (Fin 11)) : Equiv.Perm (Fin 11)) a =
        (d : Equiv.Perm (Fin 11)) a
      rfl
    have hd_a : dD • a ∈ MulAction.orbit D a := MulAction.mem_orbit a dD
    have hda_orbit : (d : Equiv.Perm (Fin 11)) a ∈ MulAction.orbit D a := by
      rwa [hda_eq] at hd_a
    by_cases hdaΩ : (d : Equiv.Perm (Fin 11)) a ∈ Ω
    · exact not_two_omega_in_orbit hij hD hN ha hdaΩ (Ne.symm hda) hda_orbit
    · have hk : (d : Equiv.Perm (Fin 11)) a = i ∨
          (d : Equiv.Perm (Fin 11)) a = j := (hnot _).mp hdaΩ
      have horb : MulAction.orbit D (dD • a) = MulAction.orbit D a :=
        (MulAction.orbit_eq_iff).mpr hd_a
      have haO : a ∈ MulAction.orbit D (dD • a) := by
        rw [horb]
        simpa using MulAction.mem_orbit a (1 : D)
      have haO' : a ∈ MulAction.orbit D ((d : Equiv.Perm (Fin 11)) a) := by
        rwa [hda_eq] at haO
      exact false_of_orbit_meets_omega hij hD hN hk ha haO'
  exact eq_one_of_fixes_omega hij (by simpa [Ω] using hfix)

theorem a11TwoSetStab_threePrime_eq_bot {i j : Fin 11} (hij : i ≠ j)
    {D : Subgroup (alternatingGroup (Fin 11))} (hD : ¬ 3 ∣ Nat.card D)
    (hDS : D ≤ a11TwoSetStab i j)
    (hN : ⁅a11TwoSetStab i j, a11TwoSetStab i j⁆ ≤
      Subgroup.normalizer (D : Set (alternatingGroup (Fin 11)))) :
    D = ⊥ := by
  classical
  rw [Subgroup.eq_bot_iff_forall]
  intro d hd
  let dD : D := ⟨d, hd⟩
  let Ω : Finset (Fin 11) := (Finset.univ.erase i).erase j
  have hΩcard : Ω.card = 9 := by
    change ((Finset.univ.erase i).erase j).card = 9
    rw [Finset.card_erase_of_mem
        (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩),
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin]
  have hmem : ∀ x, x ∈ Ω ↔ x ≠ i ∧ x ≠ j := by
    intro x
    simp [Ω, Finset.mem_erase, and_assoc, and_comm, and_left_comm]
  have hSmap : ∀ g : alternatingGroup (Fin 11), g ∈ a11TwoSetStab i j →
      ∀ x ∈ Ω, (g : Equiv.Perm (Fin 11)) x ∈ Ω := by
    intro g hg x hx
    obtain ⟨hxi, hxj⟩ := (hmem x).mp hx
    rw [hmem]
    have hinj : Function.Injective (g : Equiv.Perm (Fin 11)) :=
      (g : Equiv.Perm (Fin 11)).injective
    rcases hg with ⟨hgi, hgj⟩ | ⟨hgi, hgj⟩
    · exact ⟨fun h => hxi (hinj (h.trans hgi.symm)),
        fun h => hxj (hinj (h.trans hgj.symm))⟩
    · exact ⟨fun h => hxj (hinj (h.trans hgj.symm)),
        fun h => hxi (hinj (h.trans hgi.symm))⟩
  have hfix : ∀ a, a ∈ Ω → (d : Equiv.Perm (Fin 11)) a = a := by
    intro a ha
    by_contra hda
    have hdaΩ : (d : Equiv.Perm (Fin 11)) a ∈ Ω := hSmap d (hDS hd) a ha
    have hdaO : (d : Equiv.Perm (Fin 11)) a ∈ MulAction.orbit D a := by
      have h := MulAction.mem_orbit a dD
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def, dD] using h
    have hΩsub : (Ω : Set (Fin 11)) ⊆ MulAction.orbit D a := fun c hc =>
      omega_subset_orbit_of_two hij hN ha hdaΩ (Ne.symm hda) hdaO c hc
    have horbΩ : (MulAction.orbit D a : Set (Fin 11)) ⊆ (Ω : Set (Fin 11)) := by
      intro x hx
      rw [MulAction.mem_orbit_iff] at hx
      obtain ⟨e, he⟩ := hx
      subst he
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hSmap e (hDS e.2) a ha
    have hΩnat : Nat.card (Ω : Set (Fin 11)) = Ω.card := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_coe Ω
    have horbcard : Nat.card (MulAction.orbit D a) = 9 := by
      have hcard : Nat.card (MulAction.orbit D a) = Nat.card (Ω : Set (Fin 11)) :=
        Nat.card_congr
          { toFun := fun x => ⟨x.1, horbΩ x.2⟩
            invFun := fun x => ⟨x.1, hΩsub x.2⟩
            left_inv := fun x => by ext; rfl
            right_inv := fun x => by ext; rfl }
      rw [hcard, hΩnat, hΩcard]
    have hdvd : Nat.card (MulAction.orbit D a) ∣ Nat.card D := by
      have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group D a
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      exact ⟨Fintype.card (MulAction.stabilizer D a), h.symm⟩
    rw [horbcard] at hdvd
    exact hD ((by norm_num : 3 ∣ 9).trans hdvd)
  exact eq_one_of_fixes_omega hij (by simpa [Ω] using hfix)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
