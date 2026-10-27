module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

private lemma y4_klein_cover {Q : Type*} [Group Q] [Finite Q] (hQ : Nat.card Q = 4)
    {q₀ q₁ : Q} (hq₀ : q₀ ≠ 1) (hq₁ : q₁ ≠ 1) (hq₀₁ : q₀ ≠ q₁)
    (hq₀sq : q₀ * q₀ = 1) (hq₁sq : q₁ * q₁ = 1) :
    ∀ q : Q, q = 1 ∨ q = q₀ ∨ q = q₁ ∨ q = q₀ * q₁ := by
  classical
  haveI : Fintype Q := Fintype.ofFinite Q
  have hFcard : Fintype.card Q = 4 := by rw [← Nat.card_eq_fintype_card, hQ]
  have hq₀q₁ : q₀ * q₁ ≠ 1 := by
    intro h
    exact hq₀₁ (by
      have := congrArg (fun t => t * q₁) h
      simpa [mul_assoc, hq₁sq] using this)
  have hq₀_ne_q₀q₁ : q₀ ≠ q₀ * q₁ := by
    intro h
    exact hq₁ (by
      have := congrArg (fun t => q₀⁻¹ * t) h
      simpa using this.symm)
  have hq₁_ne_q₀q₁ : q₁ ≠ q₀ * q₁ := by
    intro h
    exact hq₀ (by
      have := congrArg (fun t => t * q₁⁻¹) h
      simpa [mul_assoc] using this.symm)
  have h1 : (1 : Q) ∉ ({q₀, q₁, q₀ * q₁} : Finset Q) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hq₀, Ne.symm hq₁, Ne.symm hq₀q₁⟩
  have h2 : q₀ ∉ ({q₁, q₀ * q₁} : Finset Q) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hq₀₁, hq₀_ne_q₀q₁⟩
  have h3 : q₁ ∉ ({q₀ * q₁} : Finset Q) := by
    simpa only [Finset.mem_singleton] using hq₁_ne_q₀q₁
  have hfin : ({1, q₀, q₁, q₀ * q₁} : Finset Q).card = 4 := by
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
      Finset.card_insert_of_notMem h3]
    simp
  have huniv : ({1, q₀, q₁, q₀ * q₁} : Finset Q) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [hfin, hFcard])
  intro q
  have hq : q ∈ ({1, q₀, q₁, q₀ * q₁} : Finset Q) := by
    rw [huniv]; exact Finset.mem_univ q
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hq

theorem y4_lam_mem {Γ : Type*} [Group Γ] {J V : Subgroup Γ} {x : Γ}
    (hJc : ∀ a ∈ J, ∀ b ∈ J, a * b = b * a)
    (hJsq : ∀ j ∈ J, j * j ∈ V) (hJ1 : ∀ j ∈ J, j * j = 1 → j ∈ V)
    (hxJ : ∀ j ∈ J, x * j * x⁻¹ ∈ J) (hxV : ∀ v ∈ V, x * v * x⁻¹ = v) :
    ∀ j ∈ J, x * j * x⁻¹ * j⁻¹ ∈ V := by
  intro j hj
  have hJinv : j⁻¹ ∈ J := J.inv_mem hj
  let a : Γ := x * j * x⁻¹
  have ha : a ∈ J := hxJ j hj
  have hdJ : a * j⁻¹ ∈ J := J.mul_mem ha hJinv
  refine hJ1 (a * j⁻¹) hdJ ?_
  have haa : a * a = j * j := by
    calc a * a = x * (j * j) * x⁻¹ := by
          dsimp only [a]; group
      _ = j * j := hxV (j * j) (hJsq j hj)
  have hdd : (a * j⁻¹) * (a * j⁻¹) = (a * a) * (j⁻¹ * j⁻¹) := by
    rw [show (a * j⁻¹) * (a * j⁻¹) = a * (j⁻¹ * a) * j⁻¹ by group]
    rw [hJc j⁻¹ hJinv a ha]
    rw [show a * (a * j⁻¹) * j⁻¹ = (a * a) * (j⁻¹ * j⁻¹) by group]
  rw [hdd, haa, ← mul_inv_rev j j, mul_inv_cancel]

theorem y4_core_prep {Γ : Type*} [Group Γ] {J V B : Subgroup Γ} {α x j₀ : Γ}
    (hVJ : V ≤ J) (hJB : J ≤ B) (hJc : ∀ a ∈ J, ∀ b ∈ J, a * b = b * a)
    (hVsq : ∀ v ∈ V, v * v = 1)
    (hJsq : ∀ j ∈ J, j * j ∈ V) (hJ1 : ∀ j ∈ J, j * j = 1 → j ∈ V)
    (hcardV : Nat.card ↥V = 4) (hcardJ : Nat.card ↥J = 16)
    (hBcases : ∀ b ∈ B, b ∈ J ∨ ∃ j ∈ J, b = j * α)
    (hx2 : x * x = 1) (hxJ : ∀ j ∈ J, x * j * x⁻¹ ∈ J) (hxV : ∀ v ∈ V, x * v * x⁻¹ = v)
    (hj₀ : j₀ ∈ J) (hj₀V : j₀ ∉ V) (hxα : x * α * x⁻¹ = j₀ * α)
    (hcard : 8 ≤ Nat.card ↥(B ⊓ Subgroup.centralizer ({x} : Set Γ))) :
    ∃ j₁ ∈ J, j₁ ∉ V ∧ x * j₁ * x⁻¹ = j₁ ∧
      ∀ j ∈ J, j ∈ V ∨ j₀⁻¹ * j ∈ V ∨ j₁⁻¹ * j ∈ V ∨ (j₀ * j₁)⁻¹ * j ∈ V := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hxj₀ : x * j₀ * x⁻¹ = j₀⁻¹ := by
    have h1 : x * (x * α * x⁻¹) * x⁻¹ = α := by
      calc x * (x * α * x⁻¹) * x⁻¹ = (x * x) * α * (x⁻¹ * x⁻¹) := by group
        _ = α := by rw [hx2, hxinv, hx2]; group
    have hconj : α = (x * j₀ * x⁻¹) * (j₀ * α) := by
      calc α = x * (x * α * x⁻¹) * x⁻¹ := h1.symm
        _ = x * (j₀ * α) * x⁻¹ := by rw [hxα]
        _ = (x * j₀ * x⁻¹) * (x * α * x⁻¹) := by group
        _ = (x * j₀ * x⁻¹) * (j₀ * α) := by rw [hxα]
    have hcancel : (x * j₀ * x⁻¹) * j₀ = 1 := by
      have := congrArg (fun t => t * α⁻¹) hconj
      simpa [mul_assoc, mul_inv_cancel] using this.symm
    exact eq_inv_of_mul_eq_one_left hcancel
  let C : Subgroup Γ := B ⊓ Subgroup.centralizer ({x} : Set Γ)
  have hCcard : 8 ≤ Nat.card ↥C := hcard
  have hCJ : C ≤ J := by
    intro b hb
    obtain ⟨hbB, hbcent⟩ := Subgroup.mem_inf.mp hb
    rcases hBcases b hbB with hbJ | ⟨j, hj, rfl⟩
    · exact hbJ
    · exfalso
      have hcomm : x * (j * α) = (j * α) * x :=
        (Subgroup.mem_centralizer_iff.mp hbcent) x (Set.mem_singleton x)
      have hx1 : x * (j * α) * x⁻¹ = j * α := by
        rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      have heq : x * (j * α) * x⁻¹ = (x * j * x⁻¹) * (j₀ * α) := by
        calc x * (j * α) * x⁻¹ = (x * j * x⁻¹) * (x * α * x⁻¹) := by group
          _ = (x * j * x⁻¹) * (j₀ * α) := by rw [hxα]
      rw [heq] at hx1
      have haj : (x * j * x⁻¹) * j₀ = j :=
        mul_right_cancel (by rw [mul_assoc]; exact hx1)
      have ha_eq : x * j * x⁻¹ = j * j₀⁻¹ := eq_mul_inv_of_mul_eq haj
      have hdj : x * j * x⁻¹ * j⁻¹ = j₀⁻¹ := by
        rw [ha_eq, mul_assoc, hJc j₀⁻¹ (J.inv_mem hj₀) j⁻¹ (J.inv_mem hj),
          ← mul_assoc, mul_inv_cancel, one_mul]
      have hdjV := y4_lam_mem hJc hJsq hJ1 hxJ hxV j hj
      rw [hdj] at hdjV
      exact hj₀V (by simpa using V.inv_mem hdjV)
  let K : Subgroup Γ := J ⊓ Subgroup.centralizer ({x} : Set Γ)
  have hKleJ : K ≤ J := inf_le_left
  have hVK : V ≤ K := by
    intro v hv
    refine ⟨hVJ hv, ?_⟩
    change v ∈ Subgroup.centralizer ({x} : Set Γ)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    calc x * v = (x * v * x⁻¹) * x := by group
      _ = v * x := by rw [hxV v hv]
  have hCK : C ≤ K := fun c hc => ⟨hCJ hc, (Subgroup.mem_inf.mp hc).2⟩
  have hKcard : 8 ≤ Nat.card ↥K := by
    haveI : Finite ↥J := Nat.finite_of_card_ne_zero (by rw [hcardJ]; norm_num)
    haveI : Finite ↥K :=
      Finite.of_injective (Subgroup.inclusion hKleJ : ↥K → ↥J)
        (Subgroup.inclusion_injective hKleJ)
    have hle : Nat.card ↥C ≤ Nat.card ↥K := Subgroup.card_le_of_le hCK
    omega
  have hKneV : K ≠ V := by
    intro hKV
    have hCV : C ≤ V := by
      have h := hCK
      rw [hKV] at h
      exact h
    haveI : Finite ↥V := Nat.finite_of_card_ne_zero (by rw [hcardV]; norm_num)
    have hle : Nat.card ↥C ≤ Nat.card ↥V := Subgroup.card_le_of_le hCV
    have : Nat.card ↥C ≤ 4 := by simpa [hcardV] using hle
    omega
  have hKnotleV : ¬ (K : Set Γ) ⊆ (V : Set Γ) :=
    fun hKV => hKneV (le_antisymm hKV hVK)
  obtain ⟨j₁, hj₁K, hj₁V⟩ := Set.not_subset.mp hKnotleV
  have hj₁J : j₁ ∈ J := hKleJ hj₁K
  have hj₁x : x * j₁ * x⁻¹ = j₁ := by
    have hcent : j₁ ∈ Subgroup.centralizer ({x} : Set Γ) := (Subgroup.mem_inf.mp hj₁K).2
    have hcomm : x * j₁ = j₁ * x :=
      (Subgroup.mem_centralizer_iff.mp hcent) x (Set.mem_singleton x)
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  let N : Subgroup ↥J := V.subgroupOf J
  haveI hJcomm : IsMulCommutative ↥J :=
    isMulCommutative_iff.mpr (fun a b : ↥J => Subtype.ext (hJc a a.2 b b.2))
  have hNcard : Nat.card ↥N = 4 := by
    have he : Nat.card ↥N = Nat.card ↥V :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVJ).toEquiv
    rw [he, hcardV]
  haveI hNfin : Finite ↥N := Nat.finite_of_card_ne_zero (by rw [hNcard]; norm_num)
  let Q := ↥J ⧸ N
  have hQcard : Nat.card Q = 4 := by
    change Nat.card (↥J ⧸ N) = 4
    rw [← Subgroup.index_eq_card N, Subgroup.index_eq_card_div, hcardJ, hNcard]
  let J₀ : ↥J := ⟨j₀, hj₀⟩
  let J₁ : ↥J := ⟨j₁, hj₁J⟩
  have hq₀sq : (J₀ : Q) * (J₀ : Q) = 1 := by
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr (by simpa using hJsq j₀ hj₀)
  have hq₁sq : (J₁ : Q) * (J₁ : Q) = 1 := by
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr (by simpa using hJsq j₁ hj₁J)
  have hq₀ne1 : (J₀ : Q) ≠ 1 := by
    intro h
    exact hj₀V (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff J₀).mp h))
  have hq₁ne1 : (J₁ : Q) ≠ 1 := by
    intro h
    exact hj₁V (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff J₁).mp h))
  have hq₀q₁_ne1 : (J₀ : Q) * (J₁ : Q) ≠ 1 := by
    intro h
    have h' : ((J₀ * J₁ : ↥J) : Q) = 1 := by
      rw [← QuotientGroup.mk_mul] at h
      exact h
    have hmem : (J₀ * J₁ : ↥J) ∈ N := (QuotientGroup.eq_one_iff (J₀ * J₁)).mp h'
    have hjV : j₀ * j₁ ∈ V := by
      simpa using Subgroup.mem_subgroupOf.mp hmem
    have hxconj : x * (j₀ * j₁) * x⁻¹ = j₀ * j₁ := hxV (j₀ * j₁) hjV
    have hxcalc : x * (j₀ * j₁) * x⁻¹ = j₀⁻¹ * j₁ := by
      calc x * (j₀ * j₁) * x⁻¹ = (x * j₀ * x⁻¹) * (x * j₁ * x⁻¹) := by group
        _ = j₀⁻¹ * j₁ := by rw [hxj₀, hj₁x]
    have hjinj : j₀⁻¹ = j₀ := mul_right_cancel (hxcalc.symm.trans hxconj)
    have hj₀sq : j₀ * j₀ = 1 := by
      calc j₀ * j₀ = j₀⁻¹ * j₀ := by rw [hjinj]
        _ = 1 := inv_mul_cancel j₀
    exact hj₀V (hJ1 j₀ hj₀ hj₀sq)
  have hq₀_ne_q₁ : (J₀ : Q) ≠ (J₁ : Q) := by
    intro h
    exact hq₀q₁_ne1 (by rw [h, hq₁sq])
  haveI : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQcard]; norm_num)
  have hmem := y4_klein_cover hQcard hq₀ne1 hq₁ne1 hq₀_ne_q₁ hq₀sq hq₁sq
  refine ⟨j₁, hj₁J, hj₁V, hj₁x, ?_⟩
  intro j hj
  let Jj : ↥J := ⟨j, hj⟩
  have hq := hmem (Jj : Q)
  rcases hq with h1' | h2' | h3' | h4'
  · left
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff Jj).mp h1')
  · right; left
    have he : (Jj : Q) = (J₀ : Q) := h2'
    have hmemN : Jj / J₀ ∈ N := (QuotientGroup.eq_iff_div_mem (N := N)).mp he
    have hV : j * j₀⁻¹ ∈ V := by
      simpa [div_eq_mul_inv] using Subgroup.mem_subgroupOf.mp hmemN
    rw [hJc j hj j₀⁻¹ (J.inv_mem hj₀)] at hV
    exact hV
  · right; right; left
    have he : (Jj : Q) = (J₁ : Q) := h3'
    have hmemN : Jj / J₁ ∈ N := (QuotientGroup.eq_iff_div_mem (N := N)).mp he
    have hV : j * j₁⁻¹ ∈ V := by
      simpa [div_eq_mul_inv] using Subgroup.mem_subgroupOf.mp hmemN
    rw [hJc j hj j₁⁻¹ (J.inv_mem hj₁J)] at hV
    exact hV
  · right; right; right
    have he : (Jj : Q) = (J₀ * J₁ : ↥J) := by
      rw [h4', QuotientGroup.mk_mul]
    have hmemN : Jj / (J₀ * J₁) ∈ N := (QuotientGroup.eq_iff_div_mem (N := N)).mp he
    have hV : j * (j₀ * j₁)⁻¹ ∈ V := by
      simpa [div_eq_mul_inv] using Subgroup.mem_subgroupOf.mp hmemN
    rw [hJc j hj (j₀ * j₁)⁻¹ (J.inv_mem (J.mul_mem hj₀ hj₁J))] at hV
    exact hV

end CFSG.OddStandard.HigherRank.YamadaG23
