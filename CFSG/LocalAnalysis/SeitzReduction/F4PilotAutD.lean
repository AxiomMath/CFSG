module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneF4InnerVBasic
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneF4Inner

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open CFSG.LieType.Ree (ReeTag)
open CFSG.LieType.Steinberg.Adjoint (iform)

variable {K : Type} [Field K]

theorem eq_zero_or_eq_one_of_iform_single_eq_four : ∀ i : Fin Tag.F4.rank,
    iform (Pi.single i 1 : Fin Tag.F4.rank → ℤ) (Pi.single i 1) = 4 →
      i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ := by
  decide

theorem exists_smul_single_eq_single_zero_of_long {i : Fin Tag.F4.rank}
    (hi : iform (Pi.single i 1 : Fin Tag.F4.rank → ℤ) (Pi.single i 1) = 4) :
    ∃ u : WeylGroup .F4,
      u • (Pi.single i 1 : Fin Tag.F4.rank → ℤ) = Pi.single ⟨0, by decide⟩ 1 := by
  rcases eq_zero_or_eq_one_of_iform_single_eq_four i hi with rfl | rfl
  · exact ⟨1, one_smul _ _⟩
  · refine ⟨simple .F4 ⟨1, by decide⟩ * simple .F4 ⟨0, by decide⟩, ?_⟩
    rw [mul_smul, simple_smul, simple_smul]
    decide


theorem exists_smul_eq_of_iform_eq_four {γ : Fin Tag.F4.rank → ℤ} (hγ : IsRoot .F4 γ)
    (h4 : iform γ γ = 4) : ∃ w : WeylGroup .F4, w • orbitCertRoot .F4 47 = γ := by
  obtain ⟨w, j, rfl⟩ := isRoot_iff_exists_smul_single.1 hγ
  rw [iform_smul] at h4
  have hr := (f4_isRoot_pos (i := 47) ⟨by norm_num, by norm_num⟩).1
  obtain ⟨v, i, hv⟩ := isRoot_iff_exists_smul_single.1 hr
  have hi : iform (Pi.single i 1 : Fin Tag.F4.rank → ℤ) (Pi.single i 1) = 4 := by
    rw [← iform_smul v, hv]
    decide
  obtain ⟨u, hu⟩ := exists_smul_single_eq_single_zero_of_long hi
  obtain ⟨u', hu'⟩ := exists_smul_single_eq_single_zero_of_long h4
  refine ⟨w * u'⁻¹ * u * v⁻¹, ?_⟩
  rw [← hv, mul_smul, mul_smul, mul_smul, inv_smul_smul, hu, ← hu', inv_smul_smul]

theorem exists_borel_conj_f4x_47 [CharP K 2] {b : ModGL .F4 K} (hb : b ∈ borelGroup .F4 K) :
    ∃ l : K, l ≠ 0 ∧ ∀ c : K, b * f4x K 47 c * b⁻¹ = f4x K 47 (l * c) := by
  have hb' : b ∈ (borelGroup .F4 K : Set (ModGL .F4 K)) := hb
  rw [(triangular_borel_structure.{0, 0} .F4 K).2.2.2.2.1] at hb'
  obtain ⟨t, ht, u, hu, rfl⟩ := Set.mem_mul.1 hb'
  have hr := (f4_isRoot_pos (i := 47) ⟨by norm_num, by norm_num⟩).1
  have key : ∀ c : K, t * u * f4x K 47 c * (t * u)⁻¹ =
      f4x K 47 (torusRootChar t (orbitCertRoot .F4 47) * c) := by
    intro c
    have hcomm := f4x_central (Or.inr rfl) c hu
    have e : t * u * f4x K 47 c * (t * u)⁻¹ = t * f4x K 47 c * t⁻¹ := by
      rw [mul_assoc t u, hcomm]
      group
    rw [e, f4x, conj_pinnedX_of_mem_torusGroup ht hr]
    rfl
  refine ⟨torusRootChar t (orbitCertRoot .F4 47), fun h0 => ?_, key⟩
  have h1 := key 1
  rw [h0, zero_mul, f4x_zero, mul_inv_eq_one, mul_eq_left] at h1
  exact one_ne_zero (pinnedX_injective .F4 K _ (h1.trans (pinnedX_zero .F4 K _).symm))

theorem eq_of_pinnedX_eq_f4x_47 {δ : Fin Tag.F4.rank → ℤ} (hδ : IsRoot .F4 δ) {d e : K}
    (hd : d ≠ 0) (h : pinnedX .F4 K δ d = f4x K 47 e) : δ = orbitCertRoot .F4 47 := by
  by_contra hne
  have hr := f4_isRoot_pos (i := 47) ⟨by norm_num, by norm_num⟩
  rcases IsRoot.height_pos_or_neg hδ with hpos | hneg
  · have hL := pinnedX_list_prod_injective (R := K) [δ, orbitCertRoot .F4 47]
      (by simpa using hne)
      (by
        intro α hα
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hα
        rcases hα with rfl | rfl
        · exact ⟨hδ, hpos⟩
        · exact hr)
      (fun α => if α = δ then d else 0)
      (fun α => if α = orbitCertRoot .F4 47 then e else 0)
      (by
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hne,
          Ne.symm hne, ↓reduceIte, pinnedX_zero, one_mul]
        exact h)
      δ (by simp)
    simp only [hne, ↓reduceIte] at hL
    exact hd hL
  · have hneg' : pinnedX .F4 K δ d ∈ negUnipotent .F4 K :=
      pinnedX_mem_rootSpan (S := {α | IsRoot .F4 α ∧ height α < 0}) ⟨hδ, hneg⟩ d
    have hB : pinnedX .F4 K δ d ∈ borelGroup .F4 K := by
      rw [h]
      exact Subgroup.mem_sup_right (f4x_mem_posUnipotent ⟨by norm_num, by norm_num⟩ e)
    have h0 := Subgroup.mem_inf.2 ⟨hB, hneg'⟩
    rw [borelGroup_inf_negUnipotent, Subgroup.mem_bot] at h0
    exact hd (pinnedX_injective .F4 K _ (h0.trans (pinnedX_zero .F4 K _).symm))

theorem exists_conj_f4x_47_eq_mul [CharP K 2] {g : ModGL .F4 K} (hg : g ∈ adjointGroup .F4 K)
    {μ : K} (hμ : g * f4x K 47 1 * g⁻¹ = f4x K 47 μ) :
    ∃ l : K, ∀ c : K, g * f4x K 47 c * g⁻¹ = f4x K 47 (l * c) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hg' : g ∈ ⋃ w, bruhatCell .F4 K w := by
    rw [← adjointGroup_eq_iUnion_bruhatCell]
    exact hg
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg'
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hw
  set n := canonicalRep (coxeterSystem .F4) K w with hn
  have hr := (f4_isRoot_pos (i := 47) ⟨by norm_num, by norm_num⟩).1
  obtain ⟨l₁, hl₁, h₁⟩ := exists_borel_conj_f4x_47 hb'
  obtain ⟨l₂, -, h₂⟩ := exists_borel_conj_f4x_47 (inv_mem hb)
  obtain ⟨l₃, -, h₃⟩ := exists_borel_conj_f4x_47 hb
  have hnx : ∀ c : K, n * f4x K 47 c * n⁻¹ = pinnedX .F4 K (w • orbitCertRoot .F4 47) c :=
    fun c => canonicalRep_mul_pinnedX_mul_inv_of_two h2 w hr c
  have hkey : pinnedX .F4 K (w • orbitCertRoot .F4 47) l₁ = f4x K 47 (l₂ * μ) := by
    rw [← h₂, ← hμ, ← hnx, ← mul_one l₁, ← h₁]
    group
  have hwr := eq_of_pinnedX_eq_f4x_47 (IsRoot.smul hr w) hl₁ hkey
  refine ⟨l₃ * l₁, fun c => ?_⟩
  calc b * n * b' * f4x K 47 c * (b * n * b')⁻¹ =
        b * (n * (b' * f4x K 47 c * b'⁻¹) * n⁻¹) * b⁻¹ := by group
    _ = f4x K 47 (l₃ * l₁ * c) := by
      rw [h₁, hnx, hwr, ← f4x, h₃, mul_assoc]

theorem entrywiseGL_pinnedX_F4 (σ : K →+* K) (γ : Fin Tag.F4.rank → ℤ) (c : K) :
    CFSG.LieType.Ree.entrywiseGL Tag.F4 K σ (pinnedX .F4 K γ c) = pinnedX .F4 K γ (σ c) :=
  Units.ext (entrywise_pinnedX σ γ c)

section Frobenius

variable [Finite K] [CharP K ReeTag.F4.prime]

theorem coe_f4Fr_pinnedX (γ : Fin Tag.F4.rank → ℤ) (c : K) :
    ((f4Fr (K := K)) ⟨pinnedX .F4 K γ c, pinnedX_mem_adjointGroup _ _⟩ : ModGL .F4 K) =
      pinnedX .F4 K γ (c ^ ReeTag.F4.prime) :=
  (ReeTag.coe_finiteFrobeniusAut _).trans
    ((entrywiseGL_pinnedX_F4 _ γ c).trans (by rw [frobenius_def]))

theorem coe_f4Fr_pow_pinnedX (j : ℕ) (γ : Fin Tag.F4.rank → ℤ) (c : K) :
    (((f4Fr (K := K)) ^ j) ⟨pinnedX .F4 K γ c, pinnedX_mem_adjointGroup _ _⟩ : ModGL .F4 K) =
      pinnedX .F4 K γ (c ^ ReeTag.F4.prime ^ j) := by
  induction j generalizing c with
  | zero => simp
  | succ j ih =>
    have hFr : (f4Fr (K := K)) ⟨pinnedX .F4 K γ c, pinnedX_mem_adjointGroup _ _⟩ =
        ⟨pinnedX .F4 K γ (c ^ ReeTag.F4.prime), pinnedX_mem_adjointGroup _ _⟩ :=
      Subtype.ext (coe_f4Fr_pinnedX γ c)
    rw [pow_succ, MulAut.mul_apply, hFr, ih, ← pow_mul, ← pow_succ']

theorem coe_f4Fr_pow_f4x (j p : ℕ) (c : K) :
    (((f4Fr (K := K)) ^ j) ⟨f4x K p c, pinnedX_mem_adjointGroup _ _⟩ : ModGL .F4 K) =
      f4x K p (c ^ ReeTag.F4.prime ^ j) :=
  coe_f4Fr_pow_pinnedX j _ c

theorem f4Fr_pow_eq_one_of_forall {j : ℕ} (hj : ∀ c : K, c ^ ReeTag.F4.prime ^ j = c) :
    (f4Fr (K := K)) ^ j = 1 := by
  refine mulAut_ext_adjX_adjY (τ := ReeTag.F4.tag) (fun i c => ?_) fun i c => ?_
  · change (ReeTag.F4.finiteFrobeniusAut K ^ j) (xElement i c) = xElement i c
    rw [ReeTag.finiteFrobeniusAut_pow_xElement, hj]
  · change (ReeTag.F4.finiteFrobeniusAut K ^ j) (yElement i c) = yElement i c
    rw [ReeTag.finiteFrobeniusAut_pow_yElement, hj]

end Frobenius

theorem exists_eq_conj_of_fix_f4x_47 {f : ℕ} (hf : 1 ≤ f) [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ f) (β : MulAut (adjointGroup .F4 K))
    (hβ : ∀ c : K, β ⟨f4x K 47 c, pinnedX_mem_adjointGroup _ _⟩ =
      ⟨f4x K 47 c, pinnedX_mem_adjointGroup _ _⟩) :
    ∃ g : adjointGroup .F4 K, β = MulAut.conj g := by
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  obtain ⟨-, hnf, -⟩ := even_F4_exact_automorphism_normal_form hf K hK
  obtain ⟨⟨g₀, k⟩, hgk₀, -⟩ := hnf β
  set g : adjointGroup .F4 K := g₀
  have hgk : β = MulAut.conj g * (f4Phi (K := K)) ^ (k : ℕ) := hgk₀
  clear_value g
  clear hgk₀
  rcases Nat.even_or_odd (k : ℕ) with ⟨j, hj⟩ | ⟨j, hj⟩
  · rw [hj, ← two_mul, f4Phi_pow_two_mul] at hgk
    have hfix : ∀ c : K, (g : ModGL .F4 K) * f4x K 47 (c ^ ReeTag.F4.prime ^ j) *
        (g : ModGL .F4 K)⁻¹ = f4x K 47 c := by
      intro c
      have h := congrArg Subtype.val (hβ c)
      rw [hgk, MulAut.mul_apply, MulAut.conj_apply] at h
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
      rw [coe_f4Fr_pow_f4x] at h
      exact h
    have h1 : (g : ModGL .F4 K) * f4x K 47 1 * (g : ModGL .F4 K)⁻¹ = f4x K 47 1 := by
      have e := hfix 1
      rwa [one_pow] at e
    obtain ⟨l, hl⟩ := exists_conj_f4x_47_eq_mul g.2 h1
    have hl1 : l = 1 := by
      have e := (hl 1).symm.trans h1
      rw [mul_one] at e
      exact pinnedX_injective .F4 K _ e
    have hj' : ∀ c : K, c ^ ReeTag.F4.prime ^ j = c := by
      intro c
      have e := (hl (c ^ ReeTag.F4.prime ^ j)).symm.trans (hfix c)
      rw [hl1, one_mul] at e
      exact pinnedX_injective .F4 K _ e
    refine ⟨g, ?_⟩
    rw [hgk, f4Fr_pow_eq_one_of_forall hj', mul_one]
  · exfalso
    have h := congrArg Subtype.val (hβ 1)
    rw [hgk, MulAut.mul_apply, hj, f4Phi_pow_odd_f4x_47, MulAut.conj_apply] at h
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
    apply conj_f4x_47_ne_f4x_44 (g := (g : ModGL .F4 K)⁻¹) (inv_mem g.2)
    rw [← h]
    group

theorem exists_eq_conj_of_fix_pinnedX_long {f : ℕ} (hf : 1 ≤ f) [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ f) {γ : Fin Tag.F4.rank → ℤ} (hγ : IsRoot .F4 γ) (h4 : iform γ γ = 4)
    (β : MulAut (adjointGroup .F4 K))
    (hβ : ∀ c : K, β ⟨pinnedX .F4 K γ c, pinnedX_mem_adjointGroup _ _⟩ =
      ⟨pinnedX .F4 K γ c, pinnedX_mem_adjointGroup _ _⟩) :
    ∃ g : adjointGroup .F4 K, β = MulAut.conj g := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨w, hw⟩ := exists_smul_eq_of_iform_eq_four hγ h4
  have hr := (f4_isRoot_pos (i := 47) ⟨by norm_num, by norm_num⟩).1
  set n : adjointGroup .F4 K :=
    ⟨canonicalRep (coxeterSystem .F4) K w, canonicalRep_mem_adjointGroup _ K w⟩ with hn
  have hnx : ∀ c : K, MulAut.conj n ⟨f4x K 47 c, pinnedX_mem_adjointGroup _ _⟩ =
      ⟨pinnedX .F4 K γ c, pinnedX_mem_adjointGroup _ _⟩ := by
    intro c
    refine Subtype.ext ?_
    rw [MulAut.conj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hn]
    rw [f4x, canonicalRep_mul_pinnedX_mul_inv_of_two h2 w hr, hw]
  have hβ' : ∀ c : K, (MulAut.conj n⁻¹ * β * MulAut.conj n)
      ⟨f4x K 47 c, pinnedX_mem_adjointGroup _ _⟩ = ⟨f4x K 47 c, pinnedX_mem_adjointGroup _ _⟩ := by
    intro c
    rw [MulAut.mul_apply, MulAut.mul_apply, hnx, hβ, ← hnx, ← MulAut.mul_apply, ← map_mul,
      inv_mul_cancel, map_one, MulAut.one_apply]
  obtain ⟨g', hg'⟩ := exists_eq_conj_of_fix_f4x_47 hf hK _ hβ'
  refine ⟨n * g' * n⁻¹, ?_⟩
  have e : β = MulAut.conj n * (MulAut.conj n⁻¹ * β * MulAut.conj n) * MulAut.conj n⁻¹ := by
    rw [map_inv]
    group
  rw [e, hg', ← map_mul, ← map_mul]

theorem exists_eq_conj_of_fix_of_rootSubgroup_le {f : ℕ} (hf : 1 ≤ f) [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ f) {H : Subgroup (ModGL .F4 K)} {γ : Fin Tag.F4.rank → ℤ}
    (hγ : IsRoot .F4 γ) (h4 : iform γ γ = 4) (hγH : rootSubgroup .F4 K γ ≤ H)
    (β : MulAut (adjointGroup .F4 K))
    (hβ : ∀ x : adjointGroup .F4 K, (x : ModGL .F4 K) ∈ H → β x = x) :
    ∃ g : adjointGroup .F4 K, β = MulAut.conj g ∧
      ∀ x : adjointGroup .F4 K, (x : ModGL .F4 K) ∈ H → g * x = x * g := by
  obtain ⟨g, hg⟩ := exists_eq_conj_of_fix_pinnedX_long hf hK hγ h4 β fun c =>
    hβ _ (hγH (Subgroup.subset_closure ⟨c, rfl⟩))
  refine ⟨g, hg, fun x hx => ?_⟩
  have e := hβ x hx
  rw [hg, MulAut.conj_apply] at e
  calc g * x = g * x * g⁻¹ * g := by group
    _ = x * g := by rw [e]

@[expose] def c3PerpRoots : Set (Fin Tag.F4.rank → ℤ) :=
  {γ | IsRoot .F4 γ ∧ iform γ (orbitCertRoot .F4 47) = 0}

theorem mem_c3PerpRoots_iff {γ : Fin Tag.F4.rank → ℤ} :
    γ ∈ c3PerpRoots ↔ IsRoot .F4 γ ∧ γ ⟨0, by decide⟩ = 0 := by
  have key : ∀ k : Fin 48, iform (Tag.F4.rootCertificate.root k) (orbitCertRoot .F4 47) =
      2 * Tag.F4.rootCertificate.root k ⟨0, by decide⟩ := by
    decide
  refine ⟨fun h => ⟨h.1, ?_⟩, fun h => ⟨h.1, ?_⟩⟩
  · obtain ⟨k, rfl⟩ := isRoot_f4_iff.1 h.1
    have := key k
    have h2 := h.2
    omega
  · obtain ⟨k, rfl⟩ := isRoot_f4_iff.1 h.1
    have := key k
    have h2 := h.2
    omega

@[expose] noncomputable def c3PerpLevi (K : Type) [Field K] : Subgroup (ModGL .F4 K) :=
  rootSpan .F4 K c3PerpRoots

theorem long_mem_c3PerpRoots :
    IsRoot .F4 (orbitCertRoot .F4 32) ∧ iform (orbitCertRoot .F4 32) (orbitCertRoot .F4 32) = 4 ∧
      orbitCertRoot .F4 32 ∈ c3PerpRoots := by
  have hroot := (f4_isRoot_pos (i := 32) ⟨by norm_num, by norm_num⟩).1
  exact ⟨hroot, by decide, hroot, by decide⟩

theorem exists_eq_conj_of_fix_c3PerpLevi {f : ℕ} (hf : 1 ≤ f) [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ f) (β : MulAut (adjointGroup .F4 K))
    (hβ : ∀ x : adjointGroup .F4 K, (x : ModGL .F4 K) ∈ c3PerpLevi K → β x = x) :
    ∃ g : adjointGroup .F4 K, β = MulAut.conj g ∧
      ∀ x : adjointGroup .F4 K, (x : ModGL .F4 K) ∈ c3PerpLevi K → g * x = x * g := by
  obtain ⟨hroot, h4, hmem⟩ := long_mem_c3PerpRoots
  exact exists_eq_conj_of_fix_of_rootSubgroup_le hf hK hroot h4
    (le_iSup₂_of_le (f := fun γ (_ : γ ∈ c3PerpRoots) => rootSubgroup .F4 K γ) _ hmem le_rfl)
    β hβ

end CFSG.SeitzReduction.F4Pilot
