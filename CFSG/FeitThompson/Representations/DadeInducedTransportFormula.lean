module

public import CFSG.FeitThompson.Representations.DadeSubsetSemidirectProduct
public import CFSG.FeitThompson.Representations.FrobeniusReciprocityClassFunctions
public import CFSG.FeitThompson.Definitions.TotalDadeSupport
import CFSG.FeitThompson.Representations.DadeSupportPacketsLocalClasses
import CFSG.FeitThompson.Representations.CoprimeAutomorphismCosetPartition

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise

variable {G : Type*} [Group G] {L : Subgroup G} {A B : Set G} {H : G → Subgroup G}

def dadeTransporter (H : G → Subgroup G) (B : Set G) (g b : G) : Set G :=
  {x : G | x⁻¹ * g * x ∈ (dadeInter H B : Set G) * {b}}

theorem mem_dadeTransporter_iff {g b x : G} :
    x ∈ dadeTransporter H B g b ↔ x⁻¹ * g * x * b⁻¹ ∈ dadeInter H B := by
  have h : x ∈ dadeTransporter H B g b ↔ x⁻¹ * g * x ∈ (dadeInter H B : Set G) * {b} := Iff.rfl
  rw [h, Set.mul_singleton]
  refine ⟨fun ⟨u, hu, he⟩ => ?_, fun hmem => ⟨_, hmem, by group⟩⟩
  rw [← he]; simpa using hu

theorem mem_dadeTransporter_of_conj_mem {g b x : G}
    (hx : x⁻¹ * g * x ∈ (dadeInter H B : Set G) * {b}) : x ∈ dadeTransporter H B g b := hx

theorem dadeTransporter_finite [Finite G] (H : G → Subgroup G) (B : Set G) (g b : G) :
    (dadeTransporter H B g b).Finite := Set.toFinite _

theorem nonempty_of_ncard_dadeTransporter_ne_zero {g b : G}
    (h : (dadeTransporter H B g b).ncard ≠ 0) : (dadeTransporter H B g b).Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  exact fun he => h (by rw [he, Set.ncard_empty])

def conjClassIn (L : Subgroup G) (a : G) : Set G := {b : G | ∃ l ∈ L, l * a * l⁻¹ = b}

theorem mem_conjClassIn_iff {a b : G} : b ∈ conjClassIn L a ↔ ∃ l ∈ L, l * a * l⁻¹ = b := Iff.rfl

theorem self_mem_conjClassIn (L : Subgroup G) (a : G) : a ∈ conjClassIn L a :=
  ⟨1, one_mem L, by group⟩

theorem conjClassIn_subset_of_subset_of_conj_mem (hA : ∀ ⦃a : G⦄, a ∈ A → ∀ ⦃x : G⦄, x ∈ L →
    x * a * x⁻¹ ∈ A) {a : G} (ha : a ∈ A) : conjClassIn L a ⊆ A := by
  rintro b ⟨l, hl, rfl⟩
  exact hA ha hl

open scoped Classical in
private theorem finsum_mem_eq_sum_ite {α : Type*} [Fintype α] (S : Set α) (F : α → ℂ) :
    ∑ᶠ b ∈ S, F b = ∑ b : α, if b ∈ S then F b else 0 := by
  classical
  rw [finsum_mem_def, finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun b _ => Set.indicator_apply S F b

open scoped Classical in
private theorem sum_ite_mem_const {α : Type*} [Fintype α] (T : Set α) (c : ℂ) :
    ∑ _x : α, (if _x ∈ T then c else 0) = (T.ncard : ℂ) * c := by
  classical
  have hfin : Finset.univ.filter (· ∈ T) = T.toFinset := by ext x; simp
  rw [← Finset.sum_filter, hfin, Finset.sum_const, Set.ncard_eq_toFinset_card', nsmul_eq_mul]

namespace IsDadeData

section

variable [Finite G]

theorem dadeInter_mul_singleton_subset (hD : IsDadeData L A H) (hBA : B ⊆ A) {b : G}
    (hb : b ∈ dadeStab L B) :
    (dadeInter H B : Set G) * {b} ⊆ ((dadeSubsetGroup H L B : Subgroup G) : Set G) := by
  rw [← hD.coe_dadeInter_mul_dadeStab hBA]
  exact Set.mul_subset_mul_left (by simpa using hb)

theorem conj_mem_dadeSubsetGroup_of_mem_dadeTransporter (hD : IsDadeData L A H) (hBA : B ⊆ A)
    {g b x : G} (hb : b ∈ dadeStab L B) (hx : x ∈ dadeTransporter H B g b) :
    x⁻¹ * g * x ∈ dadeSubsetGroup H L B :=
  hD.dadeInter_mul_singleton_subset hBA hb hx

theorem eq_of_mem_dadeTransporter (hD : IsDadeData L A H) (hBA : B ⊆ A) (hB : B.Nonempty)
    {g b₁ b₂ x : G} (hb₁ : b₁ ∈ dadeStab L B) (hb₂ : b₂ ∈ dadeStab L B)
    (h₁ : x ∈ dadeTransporter H B g b₁) (h₂ : x ∈ dadeTransporter H B g b₂) : b₁ = b₂ := by
  rw [mem_dadeTransporter_iff] at h₁ h₂
  have hmem : b₂ * b₁⁻¹ ∈ dadeInter H B ⊓ dadeStab L B := by
    refine ⟨?_, (dadeStab L B).mul_mem hb₂ ((dadeStab L B).inv_mem hb₁)⟩
    have h3 := (dadeInter H B).mul_mem ((dadeInter H B).inv_mem h₂) h₁
    have he : (x⁻¹ * g * x * b₂⁻¹)⁻¹ * (x⁻¹ * g * x * b₁⁻¹) = b₂ * b₁⁻¹ := by group
    rwa [he] at h3
  rw [hD.dadeInter_inf_dadeStab_eq_bot hBA hB] at hmem
  exact (mul_inv_eq_one.1 (by simpa using hmem)).symm

theorem extendByZero_dadePullback_of_mem_dadeTransporter (hD : IsDadeData L A H)
    (hBA : B ⊆ A) (hB : B.Nonempty) (f : L → ℂ) {g b x : G} (hb : b ∈ dadeStab L B)
    (hx : x ∈ dadeTransporter H B g b) :
    extendByZero (dadeSubsetGroup H L B) (dadePullback (hD.dadeProj hBA hB) f) (x⁻¹ * g * x)
      = extendByZero L f b := by
  have hh : x⁻¹ * g * x * b⁻¹ ∈ dadeInter H B := mem_dadeTransporter_iff.1 hx
  have hcoe : ((⟨x⁻¹ * g * x * b⁻¹ * b,
      (hD.mem_dadeSubsetGroup_iff hBA).2 ⟨_, hh, b, hb, rfl⟩⟩ :
      dadeSubsetGroup H L B) : G) = x⁻¹ * g * x := by group
  rw [← hcoe, extendByZero_apply_coe, hD.dadePullback_dadeProj_apply_mul hBA hB f hh hb,
    ← extendByZero_apply_coe L f ⟨b, dadeStab_le_left hb⟩]

theorem mem_dadeSupport_of_mem_dadeInter_mul (hD : IsDadeData L A H) (hBA : B ⊆ A)
    (hB : B.Nonempty) {b y : G} (hb : b ∈ dadeStab L B) (hbA : b ∈ A)
    (hy : y ∈ (dadeInter H B : Set G) * {b}) : y ∈ dadeSupport H b := by
  obtain ⟨b₀, hb₀⟩ := hB
  have hcop : (Nat.card ↥(dadeInter H B)).Coprime (orderOf b) := by
    have h1 : Nat.card ↥(dadeInter H B) ∣ Nat.card ↥(H b₀) :=
      Subgroup.card_dvd_of_le (dadeInter_le hb₀)
    have h2 : orderOf b ∣ Nat.card ↥(L ⊓ Subgroup.centralizer ({b} : Set G)) :=
      Subgroup.orderOf_dvd_natCard _ ⟨dadeStab_le_left hb, self_mem_centralizer b⟩
    exact ((hD.coprime_card (hBA hb₀) hbA).coprime_dvd_left h1).coprime_dvd_right h2
  have hnorm : b ∈ Subgroup.normalizer ((dadeInter H B : Subgroup G) : Set G) :=
    hD.dadeStab_le_normalizer_dadeInter hBA hb
  rw [← sUnion_centralizerCosetConjugates hcop (isOfFinOrder_of_finite b) hnorm,
    Set.mem_sUnion] at hy
  obtain ⟨S, hS, hyS⟩ := hy
  obtain ⟨c, -, rfl⟩ := mem_centralizerCosetConjugates_iff.1 hS
  rw [mem_conjAct_smul_set_iff] at hyS
  have hle : dadeInter H B ⊓ Subgroup.centralizer ({b} : Set G) ≤ H b := by
    rw [← hD.dadeInter_inf_H hbA hBA ⟨b₀, hb₀⟩]; exact inf_le_right
  exact mem_dadeSupport_iff.2 ⟨c⁻¹ * y * c,
    mem_dadeCoset_iff.2 (hle (mem_centralizerCoset_iff.1 hyS)),
    _root_.isConj_iff.2 ⟨c, by group⟩⟩

theorem mem_dadeSupport_of_mem_dadeTransporter (hD : IsDadeData L A H) (hBA : B ⊆ A)
    (hB : B.Nonempty) {g b x : G} (hb : b ∈ dadeStab L B) (hbA : b ∈ A)
    (hx : x ∈ dadeTransporter H B g b) : g ∈ dadeSupport H b := by
  have h2 := conj_mem_dadeSupport
    (hD.mem_dadeSupport_of_mem_dadeInter_mul hBA hB hb hbA hx) x⁻¹
  have he : x⁻¹⁻¹ * (x⁻¹ * g * x) * x⁻¹ = g := by group
  rwa [he] at h2

omit [Finite G] in
theorem extendByZero_eq_zero_of_notMem {f : L → ℂ}
    (hf0 : ∀ x : L, (x : G) ∉ A → f x = 0) {b : G} (hb : b ∉ A) : extendByZero L f b = 0 := by
  by_cases hbL : b ∈ L
  · rw [show b = ((⟨b, hbL⟩ : L) : G) from rfl, extendByZero_apply_coe]
    exact hf0 _ hb
  · exact extendByZero_of_notMem L f hbL

theorem extendByZero_eq_of_mem_conjClassIn (hD : IsDadeData L A H) {f : L → ℂ}
    (hf : IsClassFun f) {a b : G} (ha : a ∈ A) (hb : b ∈ conjClassIn L a) :
    extendByZero L f b = f ⟨a, hD.mem_of_mem ha⟩ := by
  obtain ⟨l, hl, rfl⟩ := hb
  have hbL : l * a * l⁻¹ ∈ L := L.mul_mem (L.mul_mem hl (hD.mem_of_mem ha)) (L.inv_mem hl)
  have hconj : IsConj (⟨a, hD.mem_of_mem ha⟩ : L) ⟨l * a * l⁻¹, hbL⟩ :=
    _root_.isConj_iff.2 ⟨⟨l, hl⟩, Subtype.ext rfl⟩
  rw [show l * a * l⁻¹ = ((⟨l * a * l⁻¹, hbL⟩ : L) : G) from rfl, extendByZero_apply_coe,
    hf.apply_eq hconj.symm]

theorem inter_support_dadeTransporter_eq (hD : IsDadeData L A H) (hBA : B ⊆ A) (hB : B.Nonempty)
    {f : L → ℂ} (hf0 : ∀ x : L, (x : G) ∉ A → f x = 0) {a g : G} (ha : a ∈ A)
    (hg : g ∈ dadeSupport H a) :
    ((dadeStab L B : Set G)) ∩
        Function.support (fun b => ((dadeTransporter H B g b).ncard : ℂ) * extendByZero L f b)
      = ((dadeStab L B : Set G) ∩ conjClassIn L a) ∩
        Function.support (fun b => ((dadeTransporter H B g b).ncard : ℂ) * extendByZero L f b) := by
  refine Set.Subset.antisymm (fun b hb' => ?_) (fun b hb' => ⟨hb'.1.1, hb'.2⟩)
  obtain ⟨hb, hbs⟩ := hb'
  refine ⟨⟨hb, ?_⟩, hbs⟩
  obtain ⟨hcard, hval⟩ := mul_ne_zero_iff.1 hbs
  have hbA : b ∈ A := by
    by_contra hbA
    exact hval (extendByZero_eq_zero_of_notMem hf0 hbA)
  obtain ⟨x, hx⟩ := nonempty_of_ncard_dadeTransporter_ne_zero
    (H := H) (B := B) (g := g) (b := b) (fun h => hcard (by rw [h]; norm_num))
  exact hD.exists_conj_of_dadeSupport_inter_nonempty ha hbA
    ⟨g, hg, hD.mem_dadeSupport_of_mem_dadeTransporter hBA hB hb hbA hx⟩

end

section

variable [Fintype G]

open scoped Classical in
theorem indClassFun_dadePullback_apply (hD : IsDadeData L A H) (hBA : B ⊆ A) (hB : B.Nonempty)
    (f : L → ℂ) (g : G) :
    indClassFun (dadeSubsetGroup H L B) (dadePullback (hD.dadeProj hBA hB) f) g
      = (Nat.card ↥(dadeSubsetGroup H L B) : ℂ)⁻¹ *
        ∑ᶠ b ∈ (dadeStab L B : Set G),
          ((dadeTransporter H B g b).ncard : ℂ) * extendByZero L f b := by
  classical
  set F : G → G → ℂ := fun b x => if b ∈ dadeStab L B then
    (if x ∈ dadeTransporter H B g b then extendByZero L f b else 0) else 0 with hF
  have hrow : ∀ x : G,
      extendByZero (dadeSubsetGroup H L B) (dadePullback (hD.dadeProj hBA hB) f) (x⁻¹ * g * x)
        = ∑ b : G, F b x := by
    intro x
    by_cases hmem : x⁻¹ * g * x ∈ dadeSubsetGroup H L B
    · obtain ⟨h, hh, u, hu, hx⟩ := (hD.mem_dadeSubsetGroup_iff hBA).1 hmem
      have hxT : x ∈ dadeTransporter H B g u := by
        refine mem_dadeTransporter_iff.2 ?_
        rw [← hx]; simpa using hh
      rw [Finset.sum_eq_single_of_mem u (Finset.mem_univ u) ?_]
      · rw [hF]
        simp only [if_pos hu, if_pos hxT]
        exact hD.extendByZero_dadePullback_of_mem_dadeTransporter hBA hB f hu hxT
      · intro b _ hbu
        rw [hF]
        by_cases hb : b ∈ dadeStab L B
        · simp only [if_pos hb, ite_eq_right_iff]
          intro hxb
          exact absurd (hD.eq_of_mem_dadeTransporter hBA hB hb hu hxb hxT) hbu
        · simp [hb]
    · rw [extendByZero_of_notMem _ _ hmem]
      refine (Finset.sum_eq_zero fun b _ => ?_).symm
      rw [hF]
      by_cases hb : b ∈ dadeStab L B
      · simp only [if_pos hb, ite_eq_right_iff]
        intro hxb
        exact absurd (hD.conj_mem_dadeSubsetGroup_of_mem_dadeTransporter hBA hb hxb) hmem
      · simp [hb]
  have hcol : ∀ b : G, ∑ x : G, F b x
      = if b ∈ (dadeStab L B : Set G) then
          ((dadeTransporter H B g b).ncard : ℂ) * extendByZero L f b else 0 := by
    intro b
    by_cases hb : b ∈ dadeStab L B
    · simp only [hF, SetLike.mem_coe, if_pos hb]
      exact sum_ite_mem_const _ _
    · simp only [hF, SetLike.mem_coe, if_neg hb, Finset.sum_const_zero]
  rw [indClassFun_eq_sum_extendByZero, finsum_mem_eq_sum_ite]
  congr 1
  rw [Finset.sum_congr rfl fun x _ => hrow x, Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => hcol b

theorem indClassFun_dadePullback_eq_zero (hD : IsDadeData L A H) (hBA : B ⊆ A) (hB : B.Nonempty)
    {f : L → ℂ} (hf0 : ∀ x : L, (x : G) ∉ A → f x = 0) {g : G}
    (hg : g ∉ totalDadeSupport A H) :
    indClassFun (dadeSubsetGroup H L B) (dadePullback (hD.dadeProj hBA hB) f) g = 0 := by
  rw [hD.indClassFun_dadePullback_apply hBA hB f g]
  refine mul_eq_zero_of_right _ (finsum_mem_of_eqOn_zero fun b hb => ?_)
  by_cases hzero : (dadeTransporter H B g b).ncard = 0
  · simp [hzero]
  by_cases hbA : b ∈ A
  · obtain ⟨x, hx⟩ := nonempty_of_ncard_dadeTransporter_ne_zero hzero
    exact absurd (dadeSupport_subset_totalDadeSupport hbA
      (hD.mem_dadeSupport_of_mem_dadeTransporter hBA hB hb hbA hx)) hg
  · simp [extendByZero_eq_zero_of_notMem hf0 hbA]

theorem indClassFun_dadePullback_apply_of_mem_dadeSupport (hD : IsDadeData L A H) (hBA : B ⊆ A)
    (hB : B.Nonempty) {f : L → ℂ} (hf : IsClassFun f) (hf0 : ∀ x : L, (x : G) ∉ A → f x = 0)
    {a g : G} (ha : a ∈ A) (hg : g ∈ dadeSupport H a) :
    indClassFun (dadeSubsetGroup H L B) (dadePullback (hD.dadeProj hBA hB) f) g
      = f ⟨a, hD.mem_of_mem ha⟩ / (Nat.card ↥(dadeSubsetGroup H L B) : ℂ) *
        ∑ᶠ b ∈ ((dadeStab L B : Set G) ∩ conjClassIn L a),
          ((dadeTransporter H B g b).ncard : ℂ) := by
  rw [hD.indClassFun_dadePullback_apply hBA hB f g,
    finsum_mem_inter_support_eq _ _ _ (hD.inter_support_dadeTransporter_eq hBA hB hf0 ha hg),
    finsum_mem_congr rfl (fun b hb => by
      rw [hD.extendByZero_eq_of_mem_conjClassIn hf ha hb.2]),
    ← finsum_mem_mul]
  ring

end

end IsDadeData

end CFSG.FeitThompson
