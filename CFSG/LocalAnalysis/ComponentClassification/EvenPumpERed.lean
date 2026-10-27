module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotTools
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotIso
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerSemidihedralTwoComponents
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrSourceChange
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinConvention
public import CFSG.LocalAnalysis.ComponentClassification.PComponentNormalizerEnlargement
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Basic
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Seven

public section

namespace CFSG.ComponentClassification.EvenPump

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def autFixed {L : Type*} [Group L] (Q : Subgroup (MulAut L)) : Subgroup L where
  carrier := {l | ∀ q ∈ Q, q l = l}
  one_mem' := fun q _ => map_one q
  mul_mem' := fun ha hb q hq => by rw [map_mul, ha q hq, hb q hq]
  inv_mem' := fun ha q hq => by rw [map_inv, ha q hq]

theorem mem_autFixed {L : Type*} [Group L] {Q : Subgroup (MulAut L)} {l : L} :
    l ∈ autFixed Q ↔ ∀ q ∈ Q, q l = l :=
  Iff.rfl

theorem inf_centralizer_subgroupOf {G : Type*} [Group G] {N E : Subgroup G} (hE : E ≤ N)
    (M : Subgroup G) :
    (M ⊓ centralizer (E : Set G)).subgroupOf N =
      M.subgroupOf N ⊓ centralizer ((E.subgroupOf N : Subgroup N) : Set N) := by
  ext ⟨x, hx⟩
  simp only [mem_subgroupOf, mem_inf, mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨hxM, hxE⟩
    exact ⟨hxM, fun e he => Subtype.ext (hxE e he)⟩
  · rintro ⟨hxM, hxE⟩
    exact ⟨hxM, fun e he => congrArg Subtype.val (hxE ⟨e, hE he⟩ he)⟩

theorem exists_reduced_pump {H : Type} [Group H] [Finite H] (hK : SectionRank.IsKGroupCat H)
    {M : Subgroup H} (hM : IsPComponent 2 M) {E : Subgroup H} (hE : IsPGroup 2 E)
    (hEN : E ≤ normalizer (M : Set H)) (hE2 : ∀ e ∈ E, e ^ 2 ∈ coreActionKernel M) {k : ℕ}
    (hEk : Nat.card E ≤ k * Nat.card ↥(E ⊓ coreActionKernel M)) {T : Subgroup H} (hTM : T ≤ M)
    (hTE : T ≤ centralizer (E : Set H))
    (hT : IsPComponent 2 (T.subgroupOf (centralizer (E : Set H)))) :
    ∃ (L : Type) (_ : Group L) (_ : Finite L), SectionRank.IsKGroupCat L ∧ IsQuasisimple L ∧
      pPrimeCore 2 L = ⊥ ∧ Nonempty (L ≃* ↥M ⧸ pPrimeCore 2 ↥M) ∧
      ∃ Q : Subgroup (MulAut L), (∀ q ∈ Q, q * q = 1) ∧ Nat.card Q ≤ k ∧
        ∃ Tb : Subgroup L, Tb ≤ autFixed Q ∧ IsPComponent 2 (Tb.subgroupOf (autFixed Q)) ∧
          Nonempty (↥T ⧸ pPrimeCore 2 ↥T ≃* ↥Tb ⧸ pPrimeCore 2 ↥Tb) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (M : Set H) with hNdef
  have hMN : M ≤ N := le_normalizer
  set M₁ : Subgroup N := M.subgroupOf N with hM₁def
  have hM₁n : M₁.Normal := normal_in_normalizer
  set O₁ : Subgroup N := (pPrimeCore 2 ↥M₁).map M₁.subtype with hO₁def
  have hO₁n : O₁.Normal := ConjAct.normal_of_characteristic_of_normal
  set φ : N →* N ⧸ O₁ := QuotientGroup.mk' O₁ with hφdef
  have hφ : ¬ 2 ∣ Nat.card φ.ker := by
    rw [hφdef, QuotientGroup.ker_mk', hO₁def,
      Subgroup.card_map_of_injective M₁.subtype_injective]
    exact Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card
  let eM : ↥M₁ ≃* ↥M := subgroupOfEquivOfLe hMN
  have hO₁H : O₁.map N.subtype = (pPrimeCore 2 ↥M).map M.subtype := by
    rw [hO₁def, ← pPrimeCore_map_iso 2 eM, Subgroup.map_map, Subgroup.map_map]
    rfl
  set Mb : Subgroup (N ⧸ O₁) := M₁.map φ with hMbdef
  have hMbn : Mb.Normal := hM₁n.map φ (QuotientGroup.mk'_surjective O₁)
  have hKL : ∀ g : N, (g : H) ∈ coreActionKernel M → ∀ y ∈ Mb, φ g * y = y * φ g := by
    intro g hg y hy
    obtain ⟨m, hm, rfl⟩ := hy
    have h1 := (mem_coreActionKernel.mp hg).2 (m : H) hm
    rw [← hO₁H] at h1
    obtain ⟨o, ho, hoe⟩ := h1
    have h2 : o = m⁻¹ * g⁻¹ * m * g := Subtype.ext (by simpa using hoe)
    have h3 : φ (m⁻¹ * g⁻¹ * m * g) = 1 := by
      rw [← h2]
      exact (QuotientGroup.eq_one_iff o).mpr ho
    simp only [map_mul, map_inv] at h3
    have h4 := congrArg (fun z => φ g * φ m * z) h3
    simp only [mul_one] at h4
    have h5 : φ g * φ m * ((φ m)⁻¹ * (φ g)⁻¹ * φ m * φ g) = φ m * φ g := by group
    rw [h5] at h4
    exact h4.symm
  let f₁ : ↥M₁ →* ↥Mb := φ.subgroupMap M₁
  have hf₁s : Function.Surjective f₁ := φ.subgroupMap_surjective M₁
  have hf₁k : f₁.ker = pPrimeCore 2 ↥M₁ := by
    ext m
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : φ (m : N) = 1 := congrArg Subtype.val h
      have h2 : (m : N) ∈ O₁ := (QuotientGroup.eq_one_iff _).mp h1
      obtain ⟨m', hm', hmm'⟩ := h2
      rw [← M₁.subtype_injective hmm']
      exact hm'
    · intro h
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff _).mpr (mem_map_of_mem M₁.subtype h)
  let eL : ↥Mb ≃* ↥M ⧸ pPrimeCore 2 ↥M :=
    ((QuotientGroup.quotientKerEquivOfSurjective f₁ hf₁s).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hf₁k)).trans (Sol78.coreQuotCongr eM)
  have hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
    ((CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 M).mp hM).2.2
  have hMbq : IsQuasisimple ↥Mb := LocalCores.isQuasisimple_of_mulEquiv eL.symm hMq
  have hMbO : pPrimeCore 2 ↥Mb = ⊥ := by
    have h1 := pPrimeCore_map_iso 2 eL
    rw [pPrimeCore_quotient_pPrimeCore_eq_bot] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ eL.injective).mp h1
  set E₁ : Subgroup N := E.subgroupOf N with hE₁def
  have hE₁ : IsPGroup 2 E₁ := hE.of_equiv (subgroupOfEquivOfLe hEN).symm
  set Eb : Subgroup (N ⧸ O₁) := E₁.map φ with hEbdef
  let ι : ↥E →* N := inclusion hEN
  let ψ : ↥E →* MulAut ↥Mb := (MulAut.conjNormal (H := Mb)).comp (φ.comp ι)
  have hψ : ∀ e : ↥E, ∀ y : ↥Mb, ((ψ e y : ↥Mb) : N ⧸ O₁) = φ (ι e) * y * (φ (ι e))⁻¹ :=
    fun e y => MulAut.conjNormal_apply _ _
  have hψ1 : ∀ e : ↥E, (e : H) ∈ coreActionKernel M → ψ e = 1 := by
    intro e he
    refine MulEquiv.ext fun y => Subtype.ext ?_
    rw [hψ, hKL (ι e) he y y.2, mul_inv_cancel_right]
    rfl
  set Q : Subgroup (MulAut ↥Mb) := ψ.range with hQdef
  have hfix : autFixed Q = (Mb ⊓ centralizer (Eb : Set (N ⧸ O₁))).subgroupOf Mb := by
    ext y
    rw [mem_autFixed, mem_subgroupOf, mem_inf, mem_centralizer_iff]
    constructor
    · intro h
      refine ⟨y.2, ?_⟩
      rintro _ ⟨e₁, he₁, rfl⟩
      have h1 := congrArg Subtype.val (h (ψ ⟨(e₁ : H), he₁⟩) ⟨_, rfl⟩)
      rw [hψ] at h1
      have h2 : ι ⟨(e₁ : H), he₁⟩ = e₁ := Subtype.ext rfl
      rw [h2] at h1
      calc φ e₁ * (y : N ⧸ O₁) = φ e₁ * y * (φ e₁)⁻¹ * φ e₁ := by group
        _ = y * φ e₁ := by rw [h1]
    · rintro ⟨-, hc⟩ _ ⟨e, rfl⟩
      apply Subtype.ext
      rw [hψ, hc (φ (ι e)) ⟨ι e, e.2, rfl⟩, mul_inv_cancel_right]
  refine ⟨↥Mb, inferInstance, inferInstance, ((hK.subgroup N).quotient O₁).subgroup Mb, hMbq,
    hMbO, ⟨eL⟩, Q, ?_, ?_, ?_⟩
  ·
    rintro _ ⟨e, rfl⟩
    rw [← map_mul]
    apply hψ1
    have h1 := hE2 e e.2
    rwa [pow_two] at h1
  ·
    have hle : (E ⊓ coreActionKernel M).subgroupOf E ≤ ψ.ker := by
      intro e he
      exact MonoidHom.mem_ker.mpr (hψ1 e (mem_subgroupOf.mp he).2)
    have h1 : Nat.card ↥(E ⊓ coreActionKernel M) ≤ Nat.card ψ.ker := by
      rw [← Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : E ⊓ coreActionKernel M ≤ E)).toEquiv]
      exact Subgroup.card_le_of_le hle
    have h2 := Subgroup.card_ker_mul_card_range ψ
    have hpos : 0 < Nat.card ψ.ker := Nat.card_pos
    have h3 : Nat.card ψ.ker * Nat.card Q ≤ Nat.card ψ.ker * k := by
      calc Nat.card ψ.ker * Nat.card Q = Nat.card E := h2
        _ ≤ k * Nat.card ↥(E ⊓ coreActionKernel M) := hEk
        _ ≤ k * Nat.card ψ.ker := Nat.mul_le_mul_left k h1
        _ = Nat.card ψ.ker * k := mul_comm _ _
    exact Nat.le_of_mul_le_mul_left h3 hpos
  set T₁ : Subgroup N := T.subgroupOf N with hT₁def
  have hT₁Y : T₁ ≤ (M ⊓ centralizer (E : Set H)).subgroupOf N := fun t ht =>
    mem_subgroupOf.mpr ⟨hTM ht, hTE ht⟩
  have hT₁ : IsPComponent 2 (T₁.subgroupOf ((M ⊓ centralizer (E : Set H)).subgroupOf N)) :=
    (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' (inf_le_left.trans hMN) 2
      Nat.prime_two).mpr
      (CatalogueBPrimeJoin.pComponent_subgroupOf_of_le (le_inf hTM hTE) inf_le_right hT)
  have hmap := GSThmB.OddQuot.isPComponent_map φ hφ hT₁Y hT₁
  have hcop : ((M ⊓ centralizer (E : Set H)).subgroupOf N).map φ =
      Mb ⊓ centralizer (Eb : Set (N ⧸ O₁)) := by
    rw [inf_centralizer_subgroupOf hEN M]
    exact GSThmB.OddQuot.map_inf_centralizer φ hE₁
      (by rw [normalizer_eq_top_iff.mpr hM₁n]; exact le_top)
      (GSThmB.OddQuot.not_two_dvd_card_ker_domRestrict φ hφ M₁)
  rw [hcop] at hmap
  have hT₁Mb : T₁.map φ ≤ Mb := map_mono fun t ht => hTM ht
  refine ⟨(T₁.map φ).subgroupOf Mb, ?_, ?_, ?_⟩
  · rw [hfix]
    intro y hy
    rw [mem_subgroupOf] at hy ⊢
    exact (map_mono hT₁Y).trans hcop.le hy
  · rw [hfix]
    exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_left 2
      Nat.prime_two).mpr hmap
  · let eT₁ : ↥T₁ ≃* ↥T := subgroupOfEquivOfLe (hTM.trans hMN)
    obtain ⟨e₂⟩ := GSThmB.OddQuot.nonempty_pPrimeCore_equiv_of_surjective (φ.subgroupMap T₁)
      (φ.subgroupMap_surjective T₁) (GSThmB.OddQuot.not_two_dvd_card_ker_subgroupMap φ hφ T₁)
    let eTb : ↥((T₁.map φ).subgroupOf Mb) ≃* ↥(T₁.map φ) := subgroupOfEquivOfLe hT₁Mb
    exact ⟨(Sol78.coreQuotCongr eT₁).symm.trans (e₂.trans (Sol78.coreQuotCongr eTb).symm)⟩

end CFSG.ComponentClassification.EvenPump
