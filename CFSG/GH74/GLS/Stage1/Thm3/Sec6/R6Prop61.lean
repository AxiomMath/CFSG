module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R6Lem510
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Extremal
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Glue2
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Glue4

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

namespace Std6

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}

theorem S_top (h : Std6 G z S) : M.Syl2In S ⊤ := by
  obtain ⟨t₀, ht₀C, ht₀z, ht₀n⟩ := h.thm2
  have hcl := h.classical.2 t₀ ht₀C ht₀z ht₀n
  exact sTop_of_clause_d h.syl_C hcl.2.2.2.1

theorem exists_extremal_conj (h : Std6 G z S) {a : G} (haS : a ∈ S) :
    ∃ c ∈ centralizer ({z} : Set G), c * a * c⁻¹ ∈ S ∧
      M.Syl2In (S ⊓ centralizer ({c * a * c⁻¹} : Set G))
        (centralizer ({z} : Set G) ⊓ centralizer ({c * a * c⁻¹} : Set G)) := by
  have hSC : S ≤ centralizer ({z} : Set G) := h.syl_C.1
  have hT02 : IsPGroup 2 ↥(S ⊓ centralizer ({a} : Set G)) := h.S_pgroup.to_inf_left
  have hXle : S ⊓ centralizer ({a} : Set G) ≤ centralizer ({z} : Set G) ⊓ centralizer ({a} : Set G) :=
    le_inf (inf_le_left.trans hSC) inf_le_right
  obtain ⟨Ta, hTa, hT0Ta⟩ := M.exists_syl2In_ge hT02 hXle
  have haT0 : a ∈ S ⊓ centralizer ({a} : Set G) :=
    ⟨haS, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have hTaC : Ta ≤ centralizer ({z} : Set G) := hTa.1.trans inf_le_left
  obtain ⟨P', hP', hTaP'⟩ := M.exists_syl2In_ge hTa.2.1 hTaC
  obtain ⟨c, hcC, hcP⟩ := h.syl_C.exists_conj hP'
  have hcz : c * z * c⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.1 hcC
    rw [this]; group
  have haP' : a ∈ P' := hTaP' (hT0Ta haT0)
  rw [hcP, M.mem_cj] at haP'
  refine ⟨c, hcC, haP', ?_⟩
  have hY := M.syl2In_cj hTa c⁻¹
  have hXeq : M.cj (centralizer ({z} : Set G) ⊓ centralizer ({a} : Set G)) c⁻¹ =
      centralizer ({z} : Set G) ⊓ centralizer ({c * a * c⁻¹} : Set G) := by
    rw [M.cj_inf, M.cj_centralizer, M.cj_centralizer, inv_inv, hcz]
  rw [hXeq] at hY
  have hYS : M.cj Ta c⁻¹ ≤ S := by
    intro x hx
    have h1 : c⁻¹ * x * c ∈ Ta := by
      have := M.mem_cj.1 hx
      simpa using this
    have h2 : c⁻¹ * x * c ∈ P' := hTaP' h1
    rw [hcP, M.mem_cj] at h2
    have e : c * (c⁻¹ * x * c) * c⁻¹ = x := by group
    rwa [e] at h2
  have hYle : M.cj Ta c⁻¹ ≤ S ⊓ centralizer ({c * a * c⁻¹} : Set G) :=
    le_inf hYS (hY.1.trans inf_le_right)
  have hQ2 : IsPGroup 2 ↥(S ⊓ centralizer ({c * a * c⁻¹} : Set G)) := h.S_pgroup.to_inf_left
  have hQle : S ⊓ centralizer ({c * a * c⁻¹} : Set G) ≤
      centralizer ({z} : Set G) ⊓ centralizer ({c * a * c⁻¹} : Set G) :=
    inf_le_inf_right _ hSC
  have := hY.eq_of_le hQ2 hYle hQle
  rw [this]
  exact hY

end Std6

theorem core61 (h14 : IVK_1_4a_quat) (h119 : IVK_1_19_lift) {G : Type} [Group G] [Finite G] {z : G}
    {S : Subgroup G} (h : Std6 G z S) {a : G} (haS : a ∈ S) (ha2 : orderOf a = 2)
    (hanot : a ∉ commBar z) (hK : ∃ K : Subgroup G, IsRigidRankOneComp z K ∧ InducesFAut a K) :
    False := by
  obtain ⟨c, hcC, hcaS, hext⟩ := h.exists_extremal_conj haS
  have hcC' : c ∈ Cz z := hcC
  have ha2' : a * a = 1 := mul_self_eq_one_of_orderOf_eq_two ha2
  have ha1 : a ≠ 1 := ne_one_of_orderOf_eq_two ha2
  have hsq : (c * a * c⁻¹) * (c * a * c⁻¹) = 1 := by
    calc (c * a * c⁻¹) * (c * a * c⁻¹) = c * (a * a) * c⁻¹ := by group
      _ = 1 := by rw [ha2']; group
  have hne : c * a * c⁻¹ ≠ 1 := by
    intro e
    apply ha1
    calc a = c⁻¹ * (c * a * c⁻¹) * c := by group
      _ = 1 := by rw [e]; group
  have hord : orderOf (c * a * c⁻¹) = 2 := orderOf_eq_two_of_mul_self_eq_one hsq hne
  have hnot : c * a * c⁻¹ ∉ commBar z := by
    intro hm
    apply hanot
    have := commBar_conj ((Cz z).inv_mem hcC') hm
    have e : c⁻¹ * (c * a * c⁻¹) * c⁻¹⁻¹ = a := by group
    rwa [e] at this
  obtain ⟨K, hK, hfa⟩ := hK
  have hK' : IsRigidRankOneComp z (cmap c K) := isRigidRankOneComp_cmap hK hcC
  have hfa' : InducesFAut (c * a * c⁻¹) (cmap c K) := inducesFAut_conj c hfa
  have h63 := lemma_6_3 h14 h119 G z S h (c * a * c⁻¹) hcaS hord (isSylowOf_of_syl2In hext)
    ⟨cmap c K, hK', hfa'⟩
  refine ctrl_contra h.simple.1 h.simple.2.1 h.S_top h.syl_C.1 hcaS hsq hne hnot
    (syl2In_of_isSylowOf h63.1) (fun g hg hcon => h63.2 g hg ?_ hcon)
  have hT1 : M.Syl2In (M.cj (S ⊓ centralizer ({c * a * c⁻¹} : Set G)) g)
      (centralizer ({g⁻¹ * (c * a * c⁻¹) * g} : Set G)) := by
    have := M.syl2In_cj (syl2In_of_isSylowOf h63.1) g
    rwa [M.cj_centralizer] at this
  rw [cj_eq_conjugate, hcon] at hT1
  exact isSylowOf_of_syl2In hT1

theorem exists_invol_ne {G : Type} [Group G] [Finite G] {H : Subgroup G} {z : G}
    (hr : 2 ≤ pRank 2 ↥H) : ∃ a ∈ H, orderOf a = 2 ∧ a ≠ z := by
  classical
  obtain ⟨A, hA, hcard⟩ := exists_elem_of_pRank (p := 2) (by norm_num) (by omega : 1 ≤ pRank 2 ↥H)
  have h4 : 4 ≤ Nat.card A := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ pRank 2 ↥H := Nat.pow_le_pow_right (by norm_num) hr
  by_contra hno
  push Not at hno
  have hsub : ∀ e ∈ A.map H.subtype, e ∈ ({1, z} : Finset G) := by
    intro e he
    obtain ⟨x, hxA, rfl⟩ := Subgroup.mem_map.1 he
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases hx1 : (x : G) = 1
    · exact Or.inl hx1
    · right
      have hx2' := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) x hxA
      have hxx : (x : ↥H) * x = 1 := by simpa [pow_two] using hx2'
      have hxx' : (x : G) * (x : G) = 1 := by simpa using congrArg Subtype.val hxx
      exact hno (x : G) x.2 (orderOf_eq_two_of_mul_self_eq_one hxx' hx1)
  have h1 := B.card_subgroup_le_finset (A.map H.subtype) _ hsub
  have h2 : Nat.card (A.map H.subtype) = Nat.card A :=
    Subgroup.card_map_of_injective H.subtype_injective
  have h3 : ({1, z} : Finset G).card ≤ 2 := Finset.card_le_two
  omega

theorem one_le_pRank_of_invol {G : Type} [Group G] [Finite G] {H : Subgroup G} {z : G} (hz : z ∈ H)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) : 1 ≤ pRank 2 ↥H := by
  obtain ⟨zz, hzzv⟩ : ∃ zz : ↥H, (zz : G) = z := ⟨⟨z, hz⟩, rfl⟩
  have hzz : zz * zz = 1 := Subtype.ext (by simpa [hzzv] using hz2)
  have hz1' : zz ≠ 1 := fun e => hz1 (by rw [← hzzv, e]; rfl)
  have hord : orderOf zz = 2 := orderOf_eq_two_of_mul_self_eq_one hzz hz1'
  have hEA : IsElementaryAbelian 2 ↥(Subgroup.zpowers zz) := by
    apply isElemAbelian_of_sq_one
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    rw [← zpow_add, ← two_mul, zpow_mul]
    simp [pow_two, hzz]
  have hbdd : BddAbove {r : ℕ | ∃ A : Subgroup ↥H, IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ r} :=
    ⟨Nat.card ↥H, by
      rintro r ⟨B, -, hB⟩
      calc r ≤ 2 ^ r := (Nat.lt_pow_self (by norm_num)).le
        _ = Nat.card B := hB.symm
        _ ≤ Nat.card ↥H := Subgroup.card_le_card_group B⟩
  exact le_csSup hbdd ⟨Subgroup.zpowers zz, hEA, by rw [Nat.card_zpowers, hord]; simp⟩

namespace Std6

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}

theorem cases (h : Std6 G z S) :
    (∃ K, Std6r1 G z S K) ∨ ∃ K₁ K₂, Std4 G z S K₁ K₂ := by
  obtain ⟨t₀, ht₀C, ht₀z, ht₀n⟩ := h.thm2
  have hcl := h.classical.2 t₀ ht₀C ht₀z ht₀n
  rcases hcl.1 with h1 | h2
  · obtain ⟨K₀, hK₀⟩ := Set.ncard_eq_one.1 h1
    exact Or.inl ⟨K₀, h, hK₀⟩
  · obtain ⟨K₁, K₂, hne, hK⟩ := Set.ncard_eq_two.1 h2
    exact Or.inr ⟨K₁, K₂, h.simple, h.rank, h.rank_le, h.gen4, h.classical, h.thm2, h.sylow, hK, hne, h.kgh⟩

theorem z_mem_Qof' (hII : II4_4_4_center) (h : Std6 G z S) {K : Subgroup G}
    (hK : IsRigidRankOneComp z K) : z ∈ Qof S K := by
  have hm : K ∈ {K' | IsRigidRankOneComp z K'} := hK
  rcases h.cases with ⟨K₀, h1⟩ | ⟨K₁, K₂, h2⟩
  · rw [h1.comps] at hm
    have : K = K₀ := hm
    subst this
    exact h1.z_mem_Q
  · rw [h2.comps] at hm
    exact z_mem_Qof (m4_of_std hII h2) (by simpa using hm)

end Std6

@[expose] def Elim61 (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) : Prop :=
  (∀ K : Subgroup G, IsRigidRankOneComp z K → 2 ≤ pRank 2 ↥(Qof S K) →
      ∀ a ∈ Qof S K, orderOf a = 2 → a ≠ z → a ∉ commBar z) ∧
  ((∀ K' : Subgroup G, IsRigidRankOneComp z K' → pRank 2 ↥(Qof S K') = 1) →
    ∀ K : Subgroup G, IsRigidRankOneComp z K → ∀ b ∈ S, b * b ∈ Rz S z → InducesFAut b K →
      b ∉ cSec K → ∃ a ∈ S, orderOf a = 2 ∧ InducesFAut a K ∧ a ∉ commBar z)

namespace Std6

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}

theorem elim61 (h5r1 : Prop5_9_r1) (h10r1 : Lemma5_10_r1) (h5 : Prop5_9) (h10 : Lemma5_10)
    (h : Std6 G z S) : Elim61 G z S := by
  rcases h.cases with ⟨K₀, h1⟩ | ⟨K₁, K₂, h2⟩
  · have hrig : ∀ K : Subgroup G, IsRigidRankOneComp z K → K = K₀ := by
      intro K hK
      have hm : K ∈ {K' | IsRigidRankOneComp z K'} := hK
      rw [h1.comps] at hm
      exact hm
    refine ⟨fun K hK hr a ha ha2 haz => ?_, fun hQ K hK b hb hbR hfa hbn => ?_⟩
    · obtain rfl := hrig K hK
      exact h5r1 G z S K h1 hr a ha ha2 haz
    · obtain rfl := hrig K hK
      exact h10r1 G z S K h1 (hQ K hK) b hb hbR hfa hbn
  · have hrig : ∀ K : Subgroup G, IsRigidRankOneComp z K → K ∈ ({K₁, K₂} : Set (Subgroup G)) := by
      intro K hK
      have hm : K ∈ {K' | IsRigidRankOneComp z K'} := hK
      rw [h2.comps] at hm
      exact hm
    have hr1 : IsRigidRankOneComp z K₁ := h2.comp_rigid (Or.inl rfl)
    have hr2 : IsRigidRankOneComp z K₂ := h2.comp_rigid (Or.inr rfl)
    refine ⟨fun K hK hr a ha ha2 haz => ?_, fun hQ K hK b hb hbR hfa hbn => ?_⟩
    · exact h5 G z S K₁ K₂ h2 K (hrig K hK) hr a ha ha2 haz
    · exact h10 G z S K₁ K₂ h2 (hQ K₁ hr1) (hQ K₂ hr2) b hb hbR K (hrig K hK) hfa hbn

theorem cond6b (h14 : IVK_1_4a_quat) (h119 : IVK_1_19_lift) (htriv : IVK_triv_fAut)
    (hII : II4_4_4_center) (he : Elim61 G z S) (h : Std6 G z S) :
    ∀ K : Subgroup G, IsRigidRankOneComp z K → Cond6b S K := by
  intro K hK
  by_contra hne
  have hz := h.z_mem_Qof' hII hK
  have h1 : 1 ≤ pRank 2 ↥(Qof S K) := one_le_pRank_of_invol hz h.z_sq h.z_ne
  have h2 : 2 ≤ pRank 2 ↥(Qof S K) := by
    unfold Cond6b at hne
    omega
  obtain ⟨a, haQ, ha2, haz⟩ := exists_invol_ne (z := z) h2
  exact core61 h14 h119 h haQ.1 ha2 (he.1 K hK h2 a haQ ha2 haz)
    ⟨K, hK, htriv G z S h K hK a haQ.2⟩

theorem cond6a (h14 : IVK_1_4a_quat) (h119 : IVK_1_19_lift) (hpow : IVK_f_pow) (hsqR : IVK_f_sq_R)
    (he : Elim61 G z S) (h : Std6 G z S) (hb : ∀ K : Subgroup G, IsRigidRankOneComp z K → Cond6b S K) :
    ∀ K : Subgroup G, IsRigidRankOneComp z K → Cond6a S K := by
  intro K hK s hs hfa
  by_contra hns
  obtain ⟨b, hbS, hbfa, hbn, hbsq⟩ := hpow G z S h K hK s hs hfa hns
  have hbR : b * b ∈ Rz S z := hsqR G z S h hb K hK b hbS hbfa hbsq
  obtain ⟨a, haS, ha2, hafa, hanot⟩ := he.2 hb K hK b hbS hbR hbfa hbn
  exact core61 h14 h119 h haS ha2 hanot ⟨K, hK, hafa⟩

end Std6

end CFSG.GH74.GLS.Stage1.Thm3.Sec6
