module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCentralizerTU
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotToralCentralizer

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  RootOps
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootChar)
open scoped commutatorElement

local instance f4CentralizerTUPerfectNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section Checks

theorem f4_negC3_torus_check : ∀ γ ∈ rootFinset .F4, γ 0 = 0 → height γ < 0 →
    f4Pairing ![1, 0, -1, 1] γ ∈ [1, -1, 2, -2] ∨ f4Pairing ![1, -2, 1, 0] γ ∈ [1, -1, 2, -2] ∨
      f4Pairing ![1, 0, 0, -1] γ ∈ [1, -1, 2, -2] := by
  decide +kernel

theorem f4_negB2_torus_check : ∀ γ ∈ rootFinset .F4, γ 0 = 0 → γ 3 = 0 → height γ < 0 →
    f4Pairing ![1, 0, -1, 1] γ ∈ [1, -1, 2, -2] ∨ f4Pairing ![1, -2, 1, 0] γ ∈ [1, -1, 2, -2] := by
  decide +kernel

theorem f4_torus_directions_perp :
    f4Pairing ![1, 0, -1, 1] (orbitCertRoot .F4 47) = 0 ∧
      f4Pairing ![1, -2, 1, 0] (orbitCertRoot .F4 47) = 0 ∧
      f4Pairing ![1, 0, 0, -1] (orbitCertRoot .F4 47) = 0 ∧
      f4Pairing ![1, 0, -1, 1] (orbitCertRoot .F4 44) = 0 ∧
      f4Pairing ![1, -2, 1, 0] (orbitCertRoot .F4 44) = 0 := by
  decide +kernel

end Checks

section Commutator

variable {K : Type} [Field K]


theorem subgroupOf_rootSpan_le {P : Subgroup (adjointGroup .F4 K)}
    {S : Set (Fin (Tag.rank .F4) → ℤ)}
    (h : ∀ γ ∈ S, ∀ c : K,
      (⟨pinnedX .F4 K γ c, pinnedX_mem_adjointGroup γ c⟩ : adjointGroup .F4 K) ∈ P) :
    (rootSpan .F4 K S).subgroupOf (adjointGroup .F4 K) ≤ P := by
  rw [rootSpan_subgroupOf_eq_closure, closure_le]
  rintro g ⟨γ, hγ, c, hg⟩
  have e : g = ⟨pinnedX .F4 K γ c, pinnedX_mem_adjointGroup γ c⟩ := Subtype.ext hg.symm
  rw [e]
  exact h γ hγ c

theorem pinnedX_mem_commutator_of_conj {P : Subgroup (adjointGroup .F4 K)}
    {h : adjointGroup .F4 K} (hh : h ∈ P) {γ : Fin (Tag.rank .F4) → ℤ} {l : K} (hl : l ≠ 1)
    (hconj : ∀ d : K, (h : ModGL .F4 K) * pinnedX .F4 K γ d * (h : ModGL .F4 K)⁻¹ =
      pinnedX .F4 K γ (l * d))
    (hγP : ∀ d : K,
      (⟨pinnedX .F4 K γ d, pinnedX_mem_adjointGroup γ d⟩ : adjointGroup .F4 K) ∈ P) (c : K) :
    (⟨pinnedX .F4 K γ c, pinnedX_mem_adjointGroup γ c⟩ : adjointGroup .F4 K) ∈ ⁅P, P⁆ := by
  have hl' : l - 1 ≠ 0 := sub_ne_zero.2 hl
  set d := c / (l - 1) with hd
  have e : (⟨pinnedX .F4 K γ c, pinnedX_mem_adjointGroup γ c⟩ : adjointGroup .F4 K) =
      ⁅h, (⟨pinnedX .F4 K γ d, pinnedX_mem_adjointGroup γ d⟩ : adjointGroup .F4 K)⁆ := by
    refine Subtype.ext ?_
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hconj, pinnedX_neg, ← pinnedX_add]
    congr 1
    rw [hd]
    field_simp
    ring
  rw [e]
  exact commutator_mem_commutator hh (hγP d)

theorem exists_ne_zero_ne_one_of_three_le_card [Finite K] (hq : 3 ≤ Nat.card K) :
    ∃ c₀ : K, c₀ ≠ 0 ∧ c₀ ≠ 1 := by
  by_contra hcon'
  have hcon : ∀ x : K, x ≠ 0 → x = 1 := fun x hx => by_contra fun h => hcon' ⟨x, hx, h⟩
  have hsurj : Function.Surjective (fun b : Bool => if b then (1 : K) else 0) := by
    intro x
    by_cases hx : x = 0
    · exact ⟨false, by simp [hx]⟩
    · exact ⟨true, by simp [hcon x hx]⟩
  have hle := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at hle
  omega


theorem pinnedX_mem_commutator_of_direction [CharP K 2] {w : Kˣ} (hw : w ≠ 1)
    {P : Subgroup (adjointGroup .F4 K)} {m : Fin (Tag.rank .F4) → ℤ}
    (hmP : (⟨rootDiagUnit .F4 (fun i => w ^ m i), f4RootDiagUnit_mem_adjointGroup _⟩ :
      adjointGroup .F4 K) ∈ P)
    {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) (hmγ : f4Pairing m γ ∈ [1, -1, 2, -2])
    (hγP : ∀ d : K,
      (⟨pinnedX .F4 K γ d, pinnedX_mem_adjointGroup γ d⟩ : adjointGroup .F4 K) ∈ P) (c : K) :
    (⟨pinnedX .F4 K γ c, pinnedX_mem_adjointGroup γ c⟩ : adjointGroup .F4 K) ∈ ⁅P, P⁆ := by
  have hl : ((rootChar (fun i => w ^ m i) γ : Kˣ) : K) ≠ 1 := by
    rw [Ne, Units.val_eq_one, rootChar_zpow]
    exact zpow_ne_one_of_charTwo hw (by simpa using hmγ)
  exact pinnedX_mem_commutator_of_conj hmP hl
    (fun d => rootDiagUnit_conj_pinnedX _ hγ d) hγP c


theorem f4x_mem_commutator [CharP K 2] {c₀ : K} (hc₀0 : c₀ ≠ 0) (hc₀1 : c₀ ≠ 1)
    {P : Subgroup (adjointGroup .F4 K)}
    (hU : ∀ p, 24 ≤ p → p ≤ 47 → ∀ c : K,
      (⟨f4x K p c, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) ∈ P)
    (hT : ∀ a : Fin Tag.F4.rank → Kˣ, rootChar a (orbitCertRoot .F4 47) = 1 →
      rootChar a (orbitCertRoot .F4 44) = 1 →
        (⟨rootDiagUnit .F4 a, f4RootDiagUnit_mem_adjointGroup a⟩ : adjointGroup .F4 K) ∈ P)
    {p : ℕ} (hp : 24 ≤ p ∧ p ≤ 47) (c : K) :
    (⟨f4x K p c, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) ∈ ⁅P, P⁆ := by
  set w : Kˣ := Units.mk0 c₀ hc₀0
  have hw : w ≠ 1 := fun h => hc₀1 (by simpa [w] using congrArg Units.val h)
  have hstep : ∀ m : Fin Tag.F4.rank → ℤ, f4Pairing m (orbitCertRoot .F4 47) = 0 →
      f4Pairing m (orbitCertRoot .F4 44) = 0 → ∀ q : ℕ, 24 ≤ q ∧ q ≤ 47 →
      f4Pairing m (orbitCertRoot .F4 q) ∈ [1, -1, 2, -2] → ∀ c : K,
      (⟨f4x K q c, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) ∈ ⁅P, P⁆ := by
    intro m hm47 hm44 q hq hmq c
    exact pinnedX_mem_commutator_of_direction hw
      (hT _ (by rw [rootChar_zpow, hm47, zpow_zero]) (by rw [rootChar_zpow, hm44, zpow_zero]))
      (f4_isRoot_pos hq).1 hmq (fun d => hU q hq.1 hq.2 d) c
  have g : ∀ q ∈ f4GenericList, ∀ c : K,
      (⟨f4x K q c, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) ∈ ⁅P, P⁆ := by
    intro q hq c
    have hq' : 24 ≤ q ∧ q ≤ 47 := by
      simp only [f4GenericList, List.mem_cons, List.not_mem_nil, or_false] at hq
      omega
    obtain ⟨⟨h1, h2, h3, h4⟩, hall⟩ := f4_torus_check
    rcases hall q hq with h | h
    · exact hstep _ h1 h2 q hq' h c
    · exact hstep _ h3 h4 q hq' h c
  have hcl : ∀ {i j : ℕ} (s t' : K),
      (⟨f4x K i s, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) ∈ ⁅P, P⁆ →
      (⟨f4x K j t', pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) ∈ ⁅P, P⁆ →
      ∀ x : adjointGroup .F4 K, (x : ModGL .F4 K) = ⁅f4x K i s, f4x K j t'⁆ → x ∈ ⁅P, P⁆ := by
    intro i j s t' hi hj x hx
    have e : x = ⁅(⟨f4x K i s, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K),
        ⟨f4x K j t', pinnedX_mem_adjointGroup _ _⟩⁆ := by
      refine Subtype.ext ?_
      rw [hx, commutatorElement_def, commutatorElement_def]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hi hj) (inv_mem hi)) (inv_mem hj)
  have hp' : p ∈ f4GenericList ∨ p = 32 ∨ p = 35 ∨ p = 44 ∨ p = 47 := by
    obtain ⟨hp1, hp2⟩ := hp
    interval_cases p <;> simp [f4GenericList]
  rcases hp' with hp' | rfl | rfl | rfl | rfl
  · exact g p hp' c
  ·
    have h := f4x_commutator_eq (K := K) (i := 24) (j := 30) ⟨by norm_num, by norm_num⟩
      ⟨by norm_num, by norm_num⟩ (by norm_num) 1 c
    have hl : (f4OddCommutatorFactors.lookup (24, 30)).getD [] = [(1, 1, 31), (2, 1, 32)] := by
      decide +kernel
    rw [hl] at h
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow,
      one_mul, pow_one] at h
    have hc := hcl (i := 24) (j := 30) 1 c (g 24 (by decide) 1) (g 30 (by decide) c)
      ⟨f4x K 31 c * f4x K 32 c, mul_mem (pinnedX_mem_adjointGroup _ _)
        (pinnedX_mem_adjointGroup _ _)⟩ h.symm
    have e : (⟨f4x K 32 c, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) =
        (⟨f4x K 31 c, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K)⁻¹ *
          ⟨f4x K 31 c * f4x K 32 c, mul_mem (pinnedX_mem_adjointGroup _ _)
            (pinnedX_mem_adjointGroup _ _)⟩ :=
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group)
    rw [e]
    exact mul_mem (inv_mem (g 31 (by decide) c)) hc
  ·
    have h := f4x_commutator_eq (K := K) (i := 33) (j := 28) ⟨by norm_num, by norm_num⟩
      ⟨by norm_num, by norm_num⟩ (by norm_num) 1 c
    have hl : (f4OddCommutatorFactors.lookup (33, 28)).getD [] = [(1, 1, 35), (1, 2, 40)] := by
      decide +kernel
    rw [hl] at h
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow,
      one_mul, pow_one] at h
    have hc := hcl (i := 33) (j := 28) 1 c (g 33 (by decide) 1) (g 28 (by decide) c)
      ⟨f4x K 35 c * f4x K 40 (c ^ 2), mul_mem (pinnedX_mem_adjointGroup _ _)
        (pinnedX_mem_adjointGroup _ _)⟩ h.symm
    have e : (⟨f4x K 35 c, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) =
        ⟨f4x K 35 c * f4x K 40 (c ^ 2), mul_mem (pinnedX_mem_adjointGroup _ _)
            (pinnedX_mem_adjointGroup _ _)⟩ *
          (⟨f4x K 40 (c ^ 2), pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K)⁻¹ :=
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group)
    rw [e]
    exact mul_mem hc (inv_mem (g 40 (by decide) _))
  ·
    exact hcl (i := 24) (j := 43) 1 c (g 24 (by decide) 1) (g 43 (by decide) c) _
      (CFSG.Monster.B.GSide.f4x_44_eq_commutator c)
  ·
    exact hcl (i := 33) (j := 46) 1 c (g 33 (by decide) 1) (g 46 (by decide) c) _
      (CFSG.Monster.B.GSide.f4x_47_eq_commutator c)

theorem pinnedX_mem_commutator_of_pos [CharP K 2] {c₀ : K} (hc₀0 : c₀ ≠ 0) (hc₀1 : c₀ ≠ 1)
    {P : Subgroup (adjointGroup .F4 K)}
    (hU : ∀ p, 24 ≤ p → p ≤ 47 → ∀ c : K,
      (⟨f4x K p c, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) ∈ P)
    (hT : ∀ a : Fin Tag.F4.rank → Kˣ, rootChar a (orbitCertRoot .F4 47) = 1 →
      rootChar a (orbitCertRoot .F4 44) = 1 →
        (⟨rootDiagUnit .F4 a, f4RootDiagUnit_mem_adjointGroup a⟩ : adjointGroup .F4 K) ∈ P)
    {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) (hγp : 0 < height γ) (c : K) :
    (⟨pinnedX .F4 K γ c, pinnedX_mem_adjointGroup γ c⟩ : adjointGroup .F4 K) ∈ ⁅P, P⁆ := by
  obtain ⟨p, hp, hp', rfl⟩ := (f4_even_positive_root_commutator_table.{0}.1 γ).1 ⟨hγ, hγp⟩
  exact f4x_mem_commutator hc₀0 hc₀1 hU hT ⟨hp, hp'⟩ c

end Commutator

section Perfect

variable {K : Type} [Field K]


theorem commutator_centralizer_zT [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) :
    ⁅centralizer ({zT K} : Set (adjointGroup .F4 K)),
      centralizer ({zT K} : Set (adjointGroup .F4 K))⁆ =
      centralizer ({zT K} : Set (adjointGroup .F4 K)) := by
  obtain ⟨c₀, hc₀0, hc₀1⟩ := exists_ne_zero_ne_one_of_three_le_card (K := K) (by omega)
  set w : Kˣ := Units.mk0 c₀ hc₀0
  have hw : w ≠ 1 := fun h => hc₀1 (by simpa [w] using congrArg Units.val h)
  set C := centralizer ({zT K} : Set (adjointGroup .F4 K)) with hCdef
  obtain ⟨-, hsup, -, -⟩ := isTwoRadicalDecomp_zT (K := K)
  have hU : ∀ p, 24 ≤ p → p ≤ 47 → ∀ c : K,
      (⟨f4x K p c, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) ∈ C := by
    intro p hp hp' c
    refine mem_centralizer_iff.2 ?_
    rintro _ rfl
    exact Subtype.ext (f4x_central (Or.inr rfl) 1 (f4x_mem_posUnipotent ⟨hp, hp'⟩ c)).symm
  have hT : ∀ a : Fin Tag.F4.rank → Kˣ, rootChar a (orbitCertRoot .F4 47) = 1 →
      (⟨rootDiagUnit .F4 a, f4RootDiagUnit_mem_adjointGroup a⟩ : adjointGroup .F4 K) ∈ C := by
    intro a ha
    refine mem_centralizer_iff.2 ?_
    rintro _ rfl
    exact Subtype.ext (rootDiagUnit_commute_pinnedX_one
      (f4_isRoot_pos (i := 47) ⟨by norm_num, by norm_num⟩).1 ha).symm
  have hL : ∀ γ ∈ c3LeviRoots, ∀ c : K,
      (⟨pinnedX .F4 K γ c, pinnedX_mem_adjointGroup γ c⟩ : adjointGroup .F4 K) ∈ C := by
    intro γ hγ c
    rw [hCdef, ← hsup]
    exact mem_sup_right (pinnedX_mem_C3Levi hγ c)
  have hpos := fun {γ} (hγ : IsRoot .F4 γ) (hγp : 0 < height γ) (c : K) =>
    pinnedX_mem_commutator_of_pos hc₀0 hc₀1 hU (fun a h47 _ => hT a h47) hγ hγp c
  obtain ⟨hp1, hp2, hp3, -, -⟩ := f4_torus_directions_perp
  refine le_antisymm (commutator_le_self _) ?_
  calc C = radicalT K ⊔ C3Levi K := hsup.symm
    _ ≤ ⁅C, C⁆ := sup_le (subgroupOf_rootSpan_le fun γ hγ c => hpos hγ.1.1 hγ.1.2 c)
        (subgroupOf_rootSpan_le fun γ hγ c => ?_)
  rcases IsRoot.height_pos_or_neg hγ.1 with hγp | hγn
  · exact hpos hγ.1 hγp c
  · have hdir : ∀ m : Fin Tag.F4.rank → ℤ, f4Pairing m (orbitCertRoot .F4 47) = 0 →
        f4Pairing m γ ∈ [1, -1, 2, -2] →
        (⟨pinnedX .F4 K γ c, pinnedX_mem_adjointGroup γ c⟩ : adjointGroup .F4 K) ∈ ⁅C, C⁆ :=
      fun m hm hmγ => pinnedX_mem_commutator_of_direction hw
        (hT _ (by rw [rootChar_zpow, hm, zpow_zero])) hγ.1 hmγ (fun d => hL γ hγ d) c
    rcases f4_negC3_torus_check γ (mem_rootFinset.2 hγ.1) hγ.2 hγn with h | h | h
    · exact hdir _ hp1 h
    · exact hdir _ hp2 h
    · exact hdir _ hp3 h

theorem commutator_centralizer_zU [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) :
    ⁅centralizer ({zU K} : Set (adjointGroup .F4 K)),
      centralizer ({zU K} : Set (adjointGroup .F4 K))⁆ =
      centralizer ({zU K} : Set (adjointGroup .F4 K)) := by
  have h := commutator_centralizer_map (commutator_centralizer_zT (K := K) hq) (graphAutF4 K)
  have e : graphAutF4 K (zT K) = zU K := graphAutF4_zT
  rwa [e] at h

theorem commutator_centralizer_zTU [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) :
    ⁅centralizer ({zT K * zU K} : Set (adjointGroup .F4 K)),
      centralizer ({zT K * zU K} : Set (adjointGroup .F4 K))⁆ =
      centralizer ({zT K * zU K} : Set (adjointGroup .F4 K)) := by
  obtain ⟨c₀, hc₀0, hc₀1⟩ := exists_ne_zero_ne_one_of_three_le_card (K := K) (by omega)
  set w : Kˣ := Units.mk0 c₀ hc₀0
  have hw : w ≠ 1 := fun h => hc₀1 (by simpa [w] using congrArg Units.val h)
  set C := centralizer ({zT K * zU K} : Set (adjointGroup .F4 K)) with hCdef
  obtain ⟨-, hsup, -, -⟩ := isTwoRadicalDecomp_zTU (K := K)
  have hU : ∀ p, 24 ≤ p → p ≤ 47 → ∀ c : K,
      (⟨f4x K p c, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) ∈ C := by
    intro p hp hp' c
    refine mem_centralizer_iff.2 ?_
    rintro _ rfl
    have hu := f4x_mem_posUnipotent ⟨hp, hp'⟩ c
    refine Subtype.ext ?_
    change f4x K 47 1 * f4x K 44 1 * f4x K p c = f4x K p c * (f4x K 47 1 * f4x K 44 1)
    rw [mul_assoc, ← f4x_central (Or.inl rfl) 1 hu, ← mul_assoc, ← f4x_central (Or.inr rfl) 1 hu,
      mul_assoc]
  have hT : ∀ a : Fin Tag.F4.rank → Kˣ, rootChar a (orbitCertRoot .F4 47) = 1 →
      rootChar a (orbitCertRoot .F4 44) = 1 →
      (⟨rootDiagUnit .F4 a, f4RootDiagUnit_mem_adjointGroup a⟩ : adjointGroup .F4 K) ∈ C := by
    intro a ha hb
    refine mem_centralizer_iff.2 ?_
    rintro _ rfl
    have h1 := rootDiagUnit_commute_pinnedX_one
      (f4_isRoot_pos (i := 47) ⟨by norm_num, by norm_num⟩).1 ha
    have h2 := rootDiagUnit_commute_pinnedX_one
      (f4_isRoot_pos (i := 44) ⟨by norm_num, by norm_num⟩).1 hb
    refine Subtype.ext ?_
    change f4x K 47 1 * f4x K 44 1 * rootDiagUnit .F4 a =
      rootDiagUnit .F4 a * (f4x K 47 1 * f4x K 44 1)
    simp only [f4x] at h1 h2 ⊢
    rw [mul_assoc, ← h2, ← mul_assoc, ← h1, mul_assoc]
  have hL : ∀ γ ∈ b2LeviRoots, ∀ c : K,
      (⟨pinnedX .F4 K γ c, pinnedX_mem_adjointGroup γ c⟩ : adjointGroup .F4 K) ∈ C := by
    intro γ hγ c
    rw [hCdef, ← hsup]
    refine mem_sup_right ?_
    exact mem_subgroupOf.2 (le_iSup₂ (f := fun γ (_ : γ ∈ b2LeviRoots) => rootSubgroup .F4 K γ)
      γ hγ (subset_closure ⟨c, rfl⟩))
  have hpos := fun {γ} (hγ : IsRoot .F4 γ) (hγp : 0 < height γ) (c : K) =>
    pinnedX_mem_commutator_of_pos hc₀0 hc₀1 hU hT hγ hγp c
  obtain ⟨hp1, hp2, -, hs1, hs2⟩ := f4_torus_directions_perp
  refine le_antisymm (commutator_le_self _) ?_
  calc C = radicalTU K ⊔ B2Levi K := hsup.symm
    _ ≤ ⁅C, C⁆ := sup_le (subgroupOf_rootSpan_le fun γ hγ c => hpos hγ.1.1 hγ.1.2 c)
        (subgroupOf_rootSpan_le fun γ hγ c => ?_)
  obtain ⟨hγr, hγ0, hγ3⟩ := mem_b2LeviRoots.1 hγ
  rcases IsRoot.height_pos_or_neg hγr with hγp | hγn
  · exact hpos hγr hγp c
  · have hdir : ∀ m : Fin Tag.F4.rank → ℤ, f4Pairing m (orbitCertRoot .F4 47) = 0 →
        f4Pairing m (orbitCertRoot .F4 44) = 0 → f4Pairing m γ ∈ [1, -1, 2, -2] →
        (⟨pinnedX .F4 K γ c, pinnedX_mem_adjointGroup γ c⟩ : adjointGroup .F4 K) ∈ ⁅C, C⁆ :=
      fun m hm hm' hmγ => pinnedX_mem_commutator_of_direction hw
        (hT _ (by rw [rootChar_zpow, hm, zpow_zero]) (by rw [rootChar_zpow, hm', zpow_zero]))
        hγr hmγ (fun d => hL γ hγ d) c
    rcases f4_negB2_torus_check γ (mem_rootFinset.2 hγr) hγ0 hγ3 hγn with h | h
    · exact hdir _ hp1 hs1 h
    · exact hdir _ hp2 hs2 h

theorem factF3Perfect [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) : FactF3Perfect K := by
  obtain ⟨hT, hU, hTU⟩ := conj_nD_zT_zU (K := K)
  intro κ
  cases κ with
  | t =>
    have h := commutator_centralizer_map (commutator_centralizer_zT (K := K) hq)
      (MulAut.conj (nD K))
    rwa [hT] at h
  | u =>
    have h := commutator_centralizer_map (commutator_centralizer_zU (K := K) hq)
      (MulAut.conj (nD K))
    rwa [hU] at h
  | tu =>
    have h := commutator_centralizer_map (commutator_centralizer_zTU (K := K) hq)
      (MulAut.conj (nD K))
    rwa [hTU] at h

end Perfect

end CFSG.SeitzReduction.F4Pilot
