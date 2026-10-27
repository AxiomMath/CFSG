module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7E6E16
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4F2Model
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitSylowTools
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCat81E6PSp

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ABGLocalTools

namespace Cat7E6

open CatFactsSp4 CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag

theorem isSylowOf_of_exists {G : Type*} [Group G] {p : ℕ} {S M : Subgroup G} (hSM : S ≤ M)
    (h : ∃ R : Sylow p ↥M, (R : Subgroup ↥M) = S.subgroupOf M) : IsSylowOf p S M := by
  obtain ⟨R, hR⟩ := h
  refine ⟨R, ?_⟩
  rw [hR, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hSM]

theorem isPGroup_zpowers_of_sq {G : Type*} [Group G] {x : G} (hx : x * x = 1) :
    IsPGroup 2 (zpowers x) := by
  rintro ⟨_, k, rfl⟩
  refine ⟨1, Subtype.ext ?_⟩
  simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
  rw [← zpow_natCast, Nat.cast_two, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_two, hx,
    one_zpow]

theorem isPGroup_of_sq {G : Type*} [Group G] {E : Subgroup G} (hE : ∀ e ∈ E, e * e = 1) :
    IsPGroup 2 E := by
  rintro ⟨e, he⟩
  exact ⟨1, Subtype.ext (by simp [pow_two, hE e he])⟩

variable {K : Type} [Field K]

theorem fld_model [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) {α : MulAut (StatedProj (StatedSp 2 K))}
    (hα : Cat8.IsAdmQ (StatedProj (StatedSp 2 K)) (p ^ f) α)
    {S₀ : Subgroup (MulAut (StatedProj (StatedSp 2 K)))}
    (hS₀ : IsSylowOf 2 S₀ (Cat8.innA (StatedProj (StatedSp 2 K)) α))
    {ψ : MulAut (StatedProj (StatedSp 2 K))} (hψn : ψ ∈ normalizer (S₀ : Set _))
    (hψN : ψ ∉ Cat8.innA (StatedProj (StatedSp 2 K)) α) (hψ2 : ψ * ψ ∈ S₀) :
    ∃ σ ∈ S₀, σ * ψ * (σ * ψ) = 1 ∧ ∃ E : Subgroup (MulAut (StatedProj (StatedSp 2 K))),
      E ≤ S₀ ∧ E ≤ centralizer ({σ * ψ} : Set (MulAut (StatedProj (StatedSp 2 K)))) ∧
        (∀ e ∈ E, e * e = 1) ∧ Nat.card E = 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut (StatedProj (StatedSp 2 K))) :=
    Finite.of_injective (fun φ : MulAut (StatedProj (StatedSp 2 K)) => (φ : _ → _))
      (fun φ ψ h => MulEquiv.ext (congrFun h))
  have hodd := ringChar_ne_two_of_card (K := K) hp hp2 hK
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card (odd_card_of_card_eq hp hp2 hK)
  set N := Cat8.innA (StatedProj (StatedSp 2 K)) α with hNdef
  have hNeq : N = (conjAut 2 K).range := innA_eq_range hp hp2 hf hK hα
  have hNn : N.Normal := hNeq ▸ range_conjAut_normal hodd
  have hS₀N : S₀ ≤ N := hS₀.le
  obtain ⟨B, τ, hψ⟩ := exists_eq_conjAut_mul_fieldAut hodd ψ
  have hBN : conjAut 2 K B ∈ N := hNeq ▸ ⟨B, rfl⟩
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    apply hψN
    rw [hψ, map_one, mul_one]
    exact hBN
  have hτ2 : τ * τ = 1 := by
    have h1 : ψ * ψ = conjAut 2 K (B * gspFieldMap τ B) * fieldAut 2 K (τ * τ) := by
      rw [hψ, map_mul, map_mul, ← fieldAut_mul_conjAut_mul_inv]
      group
    have h3 : fieldAut 2 K (τ * τ) ∈ (conjAut 2 K).range := by
      have h4 := hS₀N hψ2
      rw [h1, hNeq] at h4
      have h5 := mul_mem (inv_mem (⟨B * gspFieldMap τ B, rfl⟩ :
        conjAut 2 K (B * gspFieldMap τ B) ∈ (conjAut 2 K).range)) h4
      rwa [inv_mul_cancel_left] at h5
    exact eq_one_of_fieldAut_mem h3
  set φ₀ := fieldAut 2 K τ with hφ₀def
  have hφ₀2 : φ₀ * φ₀ = 1 := by rw [← map_mul, hτ2, map_one]
  have hφ₀N : φ₀ ∉ N := fun h => hτ1 (eq_one_of_fieldAut_mem (hNeq ▸ h))
  set M := N ⊔ zpowers φ₀ with hMdef
  have hMN : N.relIndex M = 2 := relIndex_sup_zpowers hφ₀2 hφ₀N
  have hψM : ψ ∈ M := by
    rw [hψ]
    exact mul_mem (mem_sup_left hBN) (mem_sup_right (mem_zpowers _))
  have hψS : ψ ∉ S₀ := fun h => hψN (hS₀N h)
  set G₁ := S₀ ⊔ zpowers ψ with hG₁def
  have hG₁S : S₀.relIndex G₁ = 2 := relIndex_sup_zpowers_eq_two hψn hψ2 hψS
  have hG₁M : G₁ ≤ M := sup_le (hS₀N.trans le_sup_left) (zpowers_le.mpr hψM)
  have hG₁syl : IsSylowOf 2 G₁ M := by
    rw [isSylowOf_iff] at hS₀ ⊢
    obtain ⟨-, hS₀p, hS₀i⟩ := hS₀
    refine ⟨hG₁M, ?_, ?_⟩
    · obtain ⟨k, hk⟩ := hS₀p.exists_card_eq
      apply IsPGroup.of_card (n := k + 1)
      have h1 := Subgroup.relIndex_mul_card (H := S₀) (K := G₁)
      rw [hG₁S, inf_of_le_left le_sup_left, hk] at h1
      rw [← h1, pow_succ, mul_comm]
    · have e1 := Subgroup.relIndex_mul_relIndex S₀ N M hS₀N le_sup_left
      have e2 := Subgroup.relIndex_mul_relIndex S₀ G₁ M le_sup_left hG₁M
      rw [hMN] at e1
      rw [hG₁S, ← e1] at e2
      have e3 : G₁.relIndex M = S₀.relIndex N := by omega
      rw [e3]
      exact hS₀i
  obtain ⟨h16, h16sq⟩ := card_e16 (K := K) h2
  have hEN : e16 K ≤ N := hNeq ▸ e16_le_range
  have hEφ : e16 K ≤ centralizer ({φ₀} : Set _) := e16_le_centralizer τ
  set T₀ := zpowers φ₀ ⊔ e16 K with hT₀def
  have hT₀p : IsPGroup 2 T₀ := by
    refine IsPGroup.to_sup_of_normal_right' (isPGroup_zpowers_of_sq hφ₀2) (isPGroup_of_sq h16sq) ?_
    rw [zpowers_le]
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hc := mem_centralizer_singleton_iff.mp (hEφ hx)
      rw [← hc, mul_inv_cancel_right]
      exact hx
    · intro hx
      have hc := mem_centralizer_singleton_iff.mp (hEφ hx)
      rw [inv_mul_cancel_right] at hc
      rw [mul_left_cancel hc]
      exact hx
  have hT₀M : T₀ ≤ M := sup_le (le_sup_right) (hEN.trans le_sup_left)
  obtain ⟨m, hmM, hm⟩ := FooteLit.exists_conj_le_of_isSylowOf hG₁syl hT₀M hT₀p
  have hφ' : m⁻¹ * φ₀ * m ∈ G₁ := hm φ₀ (mem_sup_left (mem_zpowers φ₀))
  have hφ'N : m⁻¹ * φ₀ * m ∉ N := by
    intro h
    apply hφ₀N
    have := hNn.conj_mem _ h m
    rwa [show m * (m⁻¹ * φ₀ * m) * m⁻¹ = φ₀ by group] at this
  have hψ2N : ψ * ψ ∈ N := hS₀N hψ2
  obtain ⟨s, hs, k, hsk⟩ := (mem_sup_zpowers_iff hψn).mp hφ'
  have hkodd : ¬ Even k := by
    intro hk
    apply hφ'N
    rw [hsk]
    exact hS₀N (mul_mem hs ((zpow_mem_iff_even hψ2 hψS k).mpr hk))
  obtain ⟨j, rfl⟩ := Int.not_even_iff_odd.mp hkodd
  refine ⟨s * ψ ^ (2 * j), mul_mem hs ((zpow_mem_iff_even hψ2 hψS _).mpr (even_two_mul j)), ?_,
    ?_⟩
  · have e : s * ψ ^ (2 * j) * ψ = m⁻¹ * φ₀ * m := by rw [hsk, zpow_add_one, mul_assoc]
    rw [e, show m⁻¹ * φ₀ * m * (m⁻¹ * φ₀ * m) = m⁻¹ * (φ₀ * φ₀) * m by group, hφ₀2]
    group
  · have e : s * ψ ^ (2 * j) * ψ = m⁻¹ * φ₀ * m := by rw [hsk, zpow_add_one, mul_assoc]
    rw [e]
    refine ⟨(e16 K).map (MulAut.conj m⁻¹).toMonoidHom, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      change m⁻¹ * x * m⁻¹⁻¹ ∈ S₀
      rw [inv_inv]
      have hxG := hm x (mem_sup_right hx)
      have hxN : m⁻¹ * x * m ∈ N := by
        have := hNn.conj_mem _ (hEN hx) m⁻¹
        rwa [inv_inv] at this
      obtain ⟨s', hs', k', hk'⟩ := (mem_sup_zpowers_iff hψn).mp hxG
      have hk'N : ψ ^ k' ∈ N := by
        have := mul_mem (inv_mem (hS₀N hs')) hxN
        rwa [hk', inv_mul_cancel_left] at this
      have hev : Even k' := (zpow_mem_iff_even hψ2N hψN k').mp hk'N
      rw [hk']
      exact mul_mem hs' ((zpow_mem_iff_even hψ2 hψS k').mpr hev)
    · rintro _ ⟨x, hx, rfl⟩
      rw [mem_centralizer_singleton_iff]
      change m⁻¹ * x * m⁻¹⁻¹ * (m⁻¹ * φ₀ * m) = m⁻¹ * φ₀ * m * (m⁻¹ * x * m⁻¹⁻¹)
      have hc := mem_centralizer_singleton_iff.mp (hEφ hx)
      rw [inv_inv, show m⁻¹ * x * m * (m⁻¹ * φ₀ * m) = m⁻¹ * (x * φ₀) * m by group, hc]
      group
    · rintro _ ⟨x, hx, rfl⟩
      change m⁻¹ * x * m⁻¹⁻¹ * (m⁻¹ * x * m⁻¹⁻¹) = 1
      rw [show m⁻¹ * x * m⁻¹⁻¹ * (m⁻¹ * x * m⁻¹⁻¹) = m⁻¹ * (x * x) * m by group, h16sq x hx]
      group
    · rw [Subgroup.card_map_of_injective (MulAut.conj m⁻¹).injective, h16]

end Cat7E6

open Cat7E6 in
theorem cf81E6FldPSp : CF81E6FldPSp := by
  intro K₀ _ _ p f hp hp2 hf _ hL α hα S₀ hS₀ hS₀N ψ hψn hψN hψ2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut K₀) := Finite.of_injective (fun φ : MulAut K₀ => (φ : K₀ → K₀))
    (fun φ ψ h => MulEquiv.ext (congrFun h))
  obtain ⟨-, -, K, _, _, hK, ⟨e⟩⟩ := GH74.Generic.lieModel_psp_data hL
  set Φ := MulAut.congr e with hΦ
  have hS₀' : IsSylowOf 2 (S₀.map Φ.toMonoidHom) (Cat8.innA _ (Φ α)) := by
    refine isSylowOf_of_exists ?_ (exists_sylow_map Φ hS₀N hS₀ (map_innA e α))
    rw [← map_innA]
    exact Subgroup.map_mono hS₀N
  have hψn' : Φ ψ ∈ normalizer ((S₀.map Φ.toMonoidHom : Subgroup _) : Set _) := by
    rw [mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, map_mul, map_mul, map_inv,
      MulEquiv.symm_apply_apply]
    exact mem_normalizer_iff.mp hψn _
  have hψN' : Φ ψ ∉ Cat8.innA _ (Φ α) := by
    rw [← map_innA, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
    exact hψN
  have hψ2' : Φ ψ * Φ ψ ∈ S₀.map Φ.toMonoidHom := by
    rw [← map_mul]
    exact Subgroup.mem_map_of_mem _ hψ2
  obtain ⟨σ', hσ', hσ2, E', hE'S, hE'C, hE'sq, hE'card⟩ :=
    fld_model hp hp2 hf hK (isAdmQ_congr e hα) hS₀' hψn' hψN' hψ2'
  refine ⟨Φ.symm σ', ?_, ?_, E'.map Φ.symm.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_map_equiv] at hσ'
    exact hσ'
  · have := congrArg Φ.symm hσ2
    rwa [map_mul, map_mul, map_one, MulEquiv.symm_apply_apply] at this
  · intro x hx
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm] at hx
    have := hE'S hx
    rw [Subgroup.mem_map_equiv] at this
    simpa using this
  · have h1 := Subgroup.map_mono (f := Φ.symm.toMonoidHom) hE'C
    rw [map_centralizer_single, map_mul, MulEquiv.symm_apply_apply] at h1
    exact h1
  · intro x hx
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm] at hx
    have := hE'sq _ hx
    have h2 := congrArg Φ.symm this
    rwa [map_mul, map_one, MulEquiv.symm_apply_apply] at h2
  · rw [Subgroup.card_map_of_injective Φ.symm.injective, hE'card]

end CFSG.ComponentClassification.GSThmB
