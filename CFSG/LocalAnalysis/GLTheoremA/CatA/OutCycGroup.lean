module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FP
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIInnDiag
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.OutCycCore
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsAlpha
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPRows

public section

namespace CFSG.LocalAnalysis.GLTheoremA.OutCyc

open CFSG.Open CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.S3 CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.StandardType

@[expose] noncomputable def psiHom {G : Type} [Group G] (p : ℕ) (L : Subgroup G) {R : Type} [Group R]
    (θ : PQuot p L ⧸ Subgroup.center (PQuot p L) ≃* R) :
    ↥(Subgroup.normalizer (L : Set G)) →* MulAut R :=
  (MulAut.congr θ).toMonoidHom.comp (chevAut p L)

theorem indAut_eq_inv_chevAut {G : Type} [Group G] [Finite G] (p : ℕ) (L : Subgroup G) (g : G)
    (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    indAut p L g hg = (chevAut p L ⟨g, hg⟩)⁻¹ := by
  rw [indAut, ← map_inv]
  rfl

theorem induces_iff_psi {G : Type} [Group G] [Finite G] {p : ℕ} {L : Subgroup G} {R : Type}
    [Group R] (θ : PQuot p L ⧸ Subgroup.center (PQuot p L) ≃* R) {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) (φ : MulAut R) :
    LargeEvenInduces θ (indRel p L g) φ ↔ φ = (psiHom p L θ ⟨g, hg⟩)⁻¹ := by
  rw [induces_indRel_iff hg θ, indAut_eq_inv_chevAut p L g hg, map_inv]
  rfl

theorem centralMod_congr {R₁ R₂ : Type} [Group R₁] [Group R₂] (σ : R₁ ≃* R₂)
    {I₁ : Set (MulAut R₁)} {I₂ : Set (MulAut R₂)}
    (hI : ∀ β : MulAut R₁, β ∈ I₁ ↔ MulAut.congr σ β ∈ I₂)
    {α : MulAut R₁} (hα : FP.CentralMod I₁ α) : FP.CentralMod I₂ (MulAut.congr σ α) := by
  intro γ
  have hc : ∀ δ : MulAut R₂, MulAut.congr σ (MulAut.congr σ.symm δ) = δ := by
    intro δ
    ext x
    simp [MulAut.congr_apply]
  have h := (hI _).1 (hα (MulAut.congr σ.symm γ))
  have e : MulAut.congr σ (MulAut.congr σ.symm γ * α * (MulAut.congr σ.symm γ)⁻¹ * α⁻¹) =
      γ * MulAut.congr σ α * γ⁻¹ * (MulAut.congr σ α)⁻¹ := by
    simp only [map_mul, map_inv, hc]
  rw [← e]
  exact h

theorem centralMod_normalizes {R : Type} [Group R] [Finite R] (I : Subgroup (MulAut R))
    {α : MulAut R} (hα : FP.CentralMod (I : Set (MulAut R)) α) :
    α ∈ Subgroup.normalizer (I : Set (MulAut R)) := by
  have fwd : ∀ v ∈ I, α * v * α⁻¹ ∈ I := by
    intro v hv
    have h := I.inv_mem (hα v)
    have e : α * v * α⁻¹ = (α * v * α⁻¹ * v⁻¹) * v := by group
    rw [e]
    exact I.mul_mem (by simpa [mul_assoc] using h) hv
  have hle : I.map (MulAut.conj α).toMonoidHom ≤ I := by
    rintro _ ⟨y, hy, rfl⟩
    exact fwd y hy
  have heq : I.map (MulAut.conj α).toMonoidHom = I :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (MulAut.conj α).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact fun hh => fwd h hh
  · intro hh
    have hm : α * h * α⁻¹ ∈ I.map (MulAut.conj α).toMonoidHom := by
      rw [heq]
      exact hh
    obtain ⟨y, hy, hyeq⟩ := hm
    have hyh : y = h := by
      have := hyeq
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
      exact (MulAut.conj α).injective (by simpa [MulAut.conj_apply] using this)
    rw [← hyh]
    exact hy


theorem push_inner {G : Type} [Group G] {p : ℕ} (L : Subgroup G) {R₁ : Type} [Group R₁]
    {I₁ F₁ : Set (MulAut R₁)} (hCMI : FP.CMIiff R₁ I₁ F₁)
    (θ₁ : PQuot p L ⧸ Subgroup.center (PQuot p L) ≃* R₁) (T : Set G)
    (hT : ∀ a ∈ T, ∃ φ ∈ I₁, LargeEvenInduces θ₁ (indRel p L a) φ)
    {P : LargeEvenMarkProp (PQuot p L)}
    (h₂ : CFSG.Assembly.LargeEvenMarking (PQuot p L) P) :
    CFSG.Assembly.LargeEvenMarking (PQuot p L) fun lab R _ I F θ =>
      P lab R I F θ ∧ ∀ a ∈ T, ∃ φ ∈ I, LargeEvenInduces θ (indRel p L a) φ := by
  obtain ⟨hX, lab₂, hlab₂, hraw₂⟩ := h₂
  have hMI := hCMI lab₂ hlab₂
  have hraw₂' := hMI _ hraw₂
  refine ⟨hX, lab₂, hlab₂, CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw₂'⟩
  rintro R _ I F ⟨⟨hs, hna, θ₂, hP⟩, hG⟩
  refine ⟨hs, hna, θ₂, hP, ?_⟩
  intro a ha
  obtain ⟨φ₁, hφ₁, hind₁⟩ := hT a ha
  let σ : R₁ ≃* R := θ₁.symm.trans θ₂
  refine ⟨MulAut.congr σ φ₁, (hG hs hna σ φ₁).1 hφ₁, ?_⟩
  intro l l' hll'
  have h1 := hind₁ l l' hll'
  simp only [σ, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_trans_apply,
    MulEquiv.symm_symm, MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply, h1]

theorem pullback_inner {G : Type} [Group G] {p : ℕ} (L : Subgroup G) {R₁ : Type} [Group R₁]
    {I₁ F₁ : Set (MulAut R₁)} (hCMI : FP.CMIiff R₁ I₁ F₁) (a : G)
    (h : CFSG.Assembly.LargeEvenMarking (PQuot p L) fun _ _ _ I _ θ =>
      ∃ φ ∈ I, LargeEvenInduces θ (indRel p L a) φ)
    (θ₁ : PQuot p L ⧸ Subgroup.center (PQuot p L) ≃* R₁) :
    ∃ φ ∈ I₁, LargeEvenInduces θ₁ (indRel p L a) φ := by
  obtain ⟨-, lab₃, hlab₃, hraw₃⟩ := h
  have hraw₃' := hCMI lab₃ hlab₃ _ hraw₃
  obtain ⟨R₃, _, I₃, F₃, ⟨⟨hs, hna, θ₃, φ₃, hφ₃, hind₃⟩, hG⟩⟩ :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw₃'
  let σ : R₁ ≃* R₃ := θ₁.symm.trans θ₃
  have hc : MulAut.congr σ (MulAut.congr σ.symm φ₃) = φ₃ := by
    ext x
    simp [MulAut.congr_apply]
  refine ⟨MulAut.congr σ.symm φ₃, ?_, ?_⟩
  · exact (hG hs hna σ (MulAut.congr σ.symm φ₃)).2 (by rw [hc]; exact hφ₃)
  · intro l l' hll'
    have h1 := hind₃ l l' hll'
    simp only [σ, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_trans_apply,
      MulEquiv.symm_symm, MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply, h1]

theorem outCyc_of_source {G : Type} [Group G] [Finite G] {p : ℕ} (hp : 0 < p)
    (L A : Subgroup G) (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hexp : ∀ a ∈ A, a ^ p = 1)
    {P₀ : LargeEvenMarkProp (PQuot p L)} (M₀ : CFSG.Assembly.LargeEvenMarking (PQuot p L) P₀)
    {R₁ : Type} [Group R₁] [Finite R₁] {I₁ F₁ : Set (MulAut R₁)}
    (θ₁ : PQuot p L ⧸ Subgroup.center (PQuot p L) ≃* R₁) (hCMI : FP.CMIiff R₁ I₁ F₁)
    (J : Subgroup (MulAut R₁)) (hJI : ∀ x, x ∈ J ↔ x ∈ I₁)
    (S : Subgroup (MulAut R₁)) (g : MulAut R₁) (hJS : J ≤ S) (hJn : (J.subgroupOf S).Normal)
    (hg : g ∈ S) (hψS : ∀ (a : G) (ha : a ∈ A), psiHom p L θ₁ ⟨a, hAN ha⟩ ∈ S)
    (hgen : ∀ (a : G) (ha : a ∈ A), ∃ k : ℤ, g ^ k * psiHom p L θ₁ ⟨a, hAN ha⟩ ∈ J) :
    ∃ A₀ : Subgroup G, A₀ ≤ A ∧ InnDiagOn p A₀ L ∧ Nat.card A ≤ p * Nat.card A₀ ∧
      ∀ a ∈ A, InnDiagOn p (Subgroup.zpowers a) L → a ∈ A₀ := by
  obtain ⟨A₀, hA₀A, hmem, hcard⟩ :=
    OutCyc.index_le_core hAN (psiHom p L θ₁) hp hexp hJS hJn hg hψS hgen
  have hA₀N : A₀ ≤ Subgroup.normalizer (L : Set G) := hA₀A.trans hAN
  have hT : ∀ a ∈ (A₀ : Set G), ∃ φ ∈ I₁, LargeEvenInduces θ₁ (indRel p L a) φ := by
    intro a ha
    have haA : a ∈ A := hA₀A ha
    refine ⟨(psiHom p L θ₁ ⟨a, hAN haA⟩)⁻¹, ?_, (induces_iff_psi θ₁ (hAN haA) _).2 rfl⟩
    rw [← hJI]
    exact J.inv_mem ((hmem a haA).1 ha)
  have hM := push_inner L hCMI θ₁ (A₀ : Set G) hT M₀
  refine ⟨A₀, hA₀A, ⟨hA₀N, ?_⟩, hcard, ?_⟩
  · exact CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.2) hM
  · intro a ha hIn
    have hmark' : CFSG.Assembly.LargeEvenMarking (PQuot p L) fun _ _ _ I _ θ' =>
        ∃ φ ∈ I, LargeEvenInduces θ' (indRel p L a) φ := by
      exact CFSG.StandardType.Canonical.largeEvenMarking_mono
        (fun _ _ _ _ _ _ h => h a (Subgroup.mem_zpowers a)) hIn.2
    obtain ⟨φ, hφ, hind⟩ := pullback_inner L hCMI a hmark' θ₁
    rw [induces_iff_psi θ₁ (hAN ha)] at hind
    apply (hmem a ha).2
    have h1 : (psiHom p L θ₁ ⟨a, hAN ha⟩)⁻¹ ∈ J := (hJI _).2 (by rw [← hind]; exact hφ)
    simpa using J.inv_mem h1


@[expose] def rawSubgroup {p : ℕ} {R : Type} [Group R] {I F : Set (MulAut R)} (h : MI.RawInnBody p R I F) :
    Subgroup (MulAut R) where
  carrier := I
  mul_mem' := fun ha hb => h.1 _ ha _ hb
  one_mem' := by
    have e : MulAut.conj (1 : R) = 1 := by
      ext x
      simp
    have := h.2.2.1 1
    rwa [e] at this
  inv_mem' := fun ha => h.2.1 _ ha

theorem psiHom_pow_eq_one {G : Type} [Group G] {p : ℕ} (L A : Subgroup G)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hexp : ∀ a ∈ A, a ^ p = 1)
    {R : Type} [Group R] (θ : PQuot p L ⧸ Subgroup.center (PQuot p L) ≃* R) {a : G} (ha : a ∈ A) :
    psiHom p L θ ⟨a, hAN ha⟩ ^ p = 1 := by
  rw [← map_pow]
  have h : (⟨a, hAN ha⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ p = 1 :=
    Subtype.ext (by simpa using hexp a ha)
  rw [h, map_one]

theorem d4_group_data {G : Type} [Group G] [Finite G] {p : ℕ} (hp : 0 < p) (L A : Subgroup G)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hexp : ∀ a ∈ A, a ^ p = 1)
    {R : Type} [Group R] [Finite R] {I F : Set (MulAut R)}
    (θ : PQuot p L ⧸ Subgroup.center (PQuot p L) ≃* R)
    (J : Subgroup (MulAut R)) (hJI : ∀ x, x ∈ J ↔ x ∈ I)
    (hcent : ∀ a ∈ A, ∀ φ : MulAut R, LargeEvenInduces θ (indRel p L a) φ → FP.CentralMod I φ)
    (hOAC : ∀ α : MulAut R, α ^ p = 1 → FP.CentralMod I α →
      ∃ u ∈ I, ∃ f ∈ Subgroup.closure F, α = u * f)
    (hFC : ∃ f₀ : MulAut R, ∀ f ∈ F, f ∈ Subgroup.zpowers f₀) :
    ∃ (S : Subgroup (MulAut R)) (g : MulAut R), J ≤ S ∧ (J.subgroupOf S).Normal ∧ g ∈ S ∧
      (∀ (a : G) (ha : a ∈ A), psiHom p L θ ⟨a, hAN ha⟩ ∈ S) ∧
      (∀ (a : G) (ha : a ∈ A), ∃ k : ℤ, g ^ k * psiHom p L θ ⟨a, hAN ha⟩ ∈ J) := by
  have hJset : (J : Set (MulAut R)) = I := Set.ext fun x => hJI x
  obtain ⟨f₀, hf₀⟩ := hFC
  have hJS : J ≤ Subgroup.normalizer (J : Set (MulAut R)) := Subgroup.le_normalizer
  have hpsiS : ∀ (a : G) (ha : a ∈ A),
      psiHom p L θ ⟨a, hAN ha⟩ ∈ Subgroup.normalizer (J : Set (MulAut R)) := by
    intro a ha
    have hcα := hcent a ha ((psiHom p L θ ⟨a, hAN ha⟩)⁻¹)
      ((induces_iff_psi θ (hAN ha) _).2 rfl)
    have hcα' : FP.CentralMod (J : Set (MulAut R)) ((psiHom p L θ ⟨a, hAN ha⟩)⁻¹) := by
      rw [hJset]
      exact hcα
    have hn := centralMod_normalizes J hcα'
    have := (Subgroup.normalizer (J : Set (MulAut R))).inv_mem hn
    simpa using this
  let C : Subgroup (MulAut R) := Subgroup.zpowers f₀ ⊓ Subgroup.normalizer (J : Set (MulAut R))
  have hC : IsCyclic ↥C := Subgroup.isCyclic_of_le inf_le_left
  obtain ⟨f₁, hf₁⟩ := IsCyclic.exists_generator (α := ↥C)
  have hf₁S : (f₁ : MulAut R) ∈ Subgroup.normalizer (J : Set (MulAut R)) := f₁.2.2
  refine ⟨Subgroup.normalizer (J : Set (MulAut R)), (f₁ : MulAut R), hJS,
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJS).2 le_rfl, hf₁S, fun a ha => hpsiS a ha, ?_⟩
  intro a ha
  set ψ := psiHom p L θ ⟨a, hAN ha⟩ with hψdef
  have hαp : ψ⁻¹ ^ p = 1 := by
    rw [inv_pow, psiHom_pow_eq_one L A hAN hexp θ ha, inv_one]
  have hcα : FP.CentralMod I ψ⁻¹ := hcent a ha ψ⁻¹ ((induces_iff_psi θ (hAN ha) _).2 rfl)
  obtain ⟨u, hu, f, hf, hαuf⟩ := hOAC ψ⁻¹ hαp hcα
  have hff₀ : f ∈ Subgroup.zpowers f₀ := (Subgroup.closure_le _).2 (fun x hx => hf₀ x hx) hf
  have hfS : f ∈ Subgroup.normalizer (J : Set (MulAut R)) := by
    have hu' : u ∈ Subgroup.normalizer (J : Set (MulAut R)) := hJS ((hJI u).2 hu)
    have hα' : ψ⁻¹ ∈ Subgroup.normalizer (J : Set (MulAut R)) :=
      (Subgroup.normalizer (J : Set (MulAut R))).inv_mem (hpsiS a ha)
    have e : f = u⁻¹ * ψ⁻¹ := by
      rw [hαuf]
      group
    rw [e]
    exact (Subgroup.normalizer (J : Set (MulAut R))).mul_mem
      ((Subgroup.normalizer (J : Set (MulAut R))).inv_mem hu') hα'
  have hfC : (⟨f, hff₀, hfS⟩ : ↥C) ∈ Subgroup.zpowers f₁ := hf₁ _
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hfC
  have hjf : (f₁ : MulAut R) ^ j = f := by
    have := congrArg Subtype.val hj
    simpa using this
  refine ⟨j, ?_⟩
  rw [hjf]
  have e : f * ψ = u⁻¹ := by
    have hψ : ψ = (u * f)⁻¹ := by
      rw [← hαuf, inv_inv]
    rw [hψ]
    group
  rw [e]
  exact J.inv_mem ((hJI u).2 hu)


theorem caTrue (lab : LargeEvenLabel) (P : LargeEvenRawCont)
    (h : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), P R I F) : MI.CAll lab P :=
  fun Q hQ => CFSG.StandardType.Canonical.largeEvenRawDatum_mono
    (fun R _ I F hq => ⟨hq, h R I F⟩) hQ


theorem outCyclicAt_of_le_one {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p ≤ 1) :
    OutCyclicAt G p := by
  intro B x L A hS _ _ _ _
  obtain ⟨hB, hx, -⟩ := hS
  have hcard : Nat.card B = p ^ GLATwoLocalRank p G := hB.2.1
  have h2 : 1 < Nat.card B := by
    rw [Finite.one_lt_card_iff_nontrivial]
    exact ⟨⟨⟨x, hx.1⟩, 1, fun h => hx.2.1 (congrArg Subtype.val h)⟩⟩
  have hp1 : p ^ GLATwoLocalRank p G ≤ 1 := by
    calc p ^ GLATwoLocalRank p G ≤ 1 ^ GLATwoLocalRank p G := Nat.pow_le_pow_left hp _
      _ = 1 := one_pow _
  rw [hcard] at h2
  omega


end CFSG.LocalAnalysis.GLTheoremA.OutCyc

end
