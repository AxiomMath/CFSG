module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParP
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParPstd

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaPar

open Subgroup CFSG.ABGLocalTools CFSG.EvenSmallLie.UnitarySix.YamadaEnd
open scoped MatrixGroups

theorem map_conjR' {G G' : Type*} [Group G] [Group G'] (φ : G' →* G) (X : Subgroup G') (g : G') :
    (conjR X g).map φ = conjR (X.map φ) (φ g) := by
  ext x
  simp only [Subgroup.mem_map, mem_conjR]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g * y * g⁻¹, hy, by simp [map_mul, map_inv]⟩
  · rintro ⟨y, hy, hyx⟩
    refine ⟨g⁻¹ * y * g, by simpa [mul_assoc] using hy, ?_⟩
    rw [map_mul, map_mul, map_inv, hyx]
    group

section Pre

variable {G : Type} [Group G] {t : G} {D₁ V₁ A₁ K₁ D₂ : Subgroup G} {θ : K₁ ≃* SU42b}
  {ιG : (Fin 8 → ZMod 2) → G}
variable [(D₁.subgroupOf (nOne D₁ K₁ D₂)).Normal]

@[expose] noncomputable def barG (D₁ K₁ D₂ : Subgroup G) [(D₁.subgroupOf (nOne D₁ K₁ D₂)).Normal]
    (Y : Subgroup G) : Subgroup (↥(nOne D₁ K₁ D₂) ⧸ D₁.subgroupOf (nOne D₁ K₁ D₂)) :=
  (Y.subgroupOf (nOne D₁ K₁ D₂)).map (mkG D₁ K₁ D₂)

theorem mkG_eq_iff' (n n' : nOne D₁ K₁ D₂) :
    mkG D₁ K₁ D₂ n = mkG D₁ K₁ D₂ n' ↔ (n : G)⁻¹ * n' ∈ D₁ := by
  rw [mkG, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  simp

theorem mkG_mem_barG_iff {Y : Subgroup G} (hDY : D₁ ≤ Y) (n : nOne D₁ K₁ D₂) :
    mkG D₁ K₁ D₂ n ∈ barG D₁ K₁ D₂ Y ↔ (n : G) ∈ Y := by
  constructor
  · rintro ⟨y, hy, hyn⟩
    rw [mkG_eq_iff'] at hyn
    have : (n : G) = y * ((y : G)⁻¹ * n) := by group
    rw [this]
    exact mul_mem hy (hDY hyn)
  · intro hn
    exact ⟨n, hn, rfl⟩

theorem card_eq_mul_card_barG {Y : Subgroup G} (hDY : D₁ ≤ Y) (hYN : Y ≤ nOne D₁ K₁ D₂) :
    Nat.card Y = Nat.card D₁ * Nat.card (barG D₁ K₁ D₂ Y) := by
  set f : Y →* (↥(nOne D₁ K₁ D₂) ⧸ D₁.subgroupOf (nOne D₁ K₁ D₂)) :=
    (mkG D₁ K₁ D₂).comp (Subgroup.inclusion hYN)
  have hker : f.ker = D₁.subgroupOf Y := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.comp_apply, ← map_one (mkG D₁ K₁ D₂),
      mkG_eq_iff']
    simp
  have hrange : f.range = barG D₁ K₁ D₂ Y := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨Subgroup.inclusion hYN y, y.2, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n, hn⟩, rfl⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange, hker,
    card_subgroupOf_of_le hDY, mul_comm]

theorem barG_inf_conjR {P : Subgroup G} (hDP : D₁ ≤ P)
    (hN : nOne D₁ K₁ D₂ ≤ normalizer (D₁ : Set G)) {w : G} (hw : w ∈ nOne D₁ K₁ D₂) :
    barG D₁ K₁ D₂ (P ⊓ conjR P w) =
      barG D₁ K₁ D₂ P ⊓ conjR (barG D₁ K₁ D₂ P) (mkG D₁ K₁ D₂ ⟨w, hw⟩) := by
  have hDw : D₁ ≤ conjR P w := fun d hd => by
    rw [mem_conjR]
    exact hDP ((mem_normalizer_iff.mp (hN hw) d).mp hd)
  ext x
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (D₁.subgroupOf (nOne D₁ K₁ D₂)) x
  change mkG D₁ K₁ D₂ n ∈ _ ↔ mkG D₁ K₁ D₂ n ∈ _
  have : mkG D₁ K₁ D₂ ⟨w, hw⟩ * mkG D₁ K₁ D₂ n * (mkG D₁ K₁ D₂ ⟨w, hw⟩)⁻¹ =
      mkG D₁ K₁ D₂ (⟨w, hw⟩ * n * ⟨w, hw⟩⁻¹) := by simp only [map_mul, map_inv]
  rw [mkG_mem_barG_iff (le_inf hDP hDw), Subgroup.mem_inf, Subgroup.mem_inf,
    mkG_mem_barG_iff hDP, mem_conjR, mem_conjR, this, mkG_mem_barG_iff hDP]
  rfl

theorem card_inf_conjR_eq {P : Subgroup G} (hDP : D₁ ≤ P) (hPN : P ≤ nOne D₁ K₁ D₂)
    (hN : nOne D₁ K₁ D₂ ≤ normalizer (D₁ : Set G)) {w : G} (hw : w ∈ nOne D₁ K₁ D₂) :
    Nat.card (P ⊓ conjR P w : Subgroup G) = Nat.card D₁ *
      Nat.card (barG D₁ K₁ D₂ P ⊓ conjR (barG D₁ K₁ D₂ P) (mkG D₁ K₁ D₂ ⟨w, hw⟩) :
        Subgroup _) := by
  have hDw : D₁ ≤ conjR P w := fun d hd => by
    rw [mem_conjR]
    exact hDP ((mem_normalizer_iff.mp (hN hw) d).mp hd)
  rw [card_eq_mul_card_barG (le_inf hDP hDw) (inf_le_left.trans hPN),
    barG_inf_conjR hDP hN hw]

end Pre

theorem card_map_inj {G G' : Type*} [Group G] [Group G'] (f : G →* G') (hf : Function.Injective f)
    (X : Subgroup G) : Nat.card (X.map f) = Nat.card X :=
  Subgroup.card_map_of_injective hf

theorem map_inf_conjR_inj {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Injective f) (X : Subgroup G) (g : G) :
    (X ⊓ conjR X g).map f = X.map f ⊓ conjR (X.map f) (f g) := by
  rw [Subgroup.map_inf_eq _ _ f hf, map_conjR']

theorem card_prod' {G G' : Type*} [Group G] [Group G'] (H : Subgroup G) (K : Subgroup G') :
    Nat.card (H.prod K) = Nat.card H * Nat.card K := by
  rw [Nat.card_congr (Subgroup.prodEquiv H K).toEquiv, Nat.card_prod]

theorem card_le_of_isPGroup {G : Type*} [Group G] [Finite G] {X : Subgroup G} (hX : IsPGroup 2 X)
    {m : ℕ} (hm : ¬ 2 ∣ m) (hG : Nat.card G = 2 ^ 6 * m) : Nat.card X ≤ 2 ^ 6 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := X)).mp hX
  have hd : 2 ^ k ∣ 2 ^ 6 * m := hk ▸ hG ▸ Subgroup.card_subgroup_dvd_card X
  have hcop : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left _
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hm)
  have h6 : 2 ^ k ∣ 2 ^ 6 := hcop.dvd_of_dvd_mul_right hd
  rw [hk]
  exact Nat.le_of_dvd (by positivity) h6

section Unitary

variable {Γ : Type} [Group Γ] [Finite Γ] {F : Type} [Field F] [Finite F] [CharP F 2]

noncomputable abbrev pSig (F : Type) [Field F] [Finite F] [CharP F 2] :
    Subgroup (msigma F) := (pstd F).subgroupOf (msigma F)

theorem map_pSig_inf (A : msigma F) :
    (pSig F ⊓ conjR (pSig F) A).map (msigma F).subtype =
      msigma F ⊓ pstd F ⊓ conjR (pstd F) (A : SL(4, F)) := by
  rw [map_inf_conjR_inj _ (msigma F).subtype_injective, Subgroup.subgroupOf_map_subtype]
  have hA : (A : SL(4, F)) ∈ normalizer ((msigma F : Subgroup _) : Set _) :=
    Subgroup.le_normalizer A.2
  rw [Subgroup.coe_subtype, conjR_inf, conjR_eq_self hA, inf_comm (pstd F)]
  ext x
  simp only [Subgroup.mem_inf]
  tauto

theorem card_pSig_inf (A : msigma F) :
    Nat.card ↥(pSig F ⊓ conjR (pSig F) A) =
      Nat.card ↥(msigma F ⊓ pstd F ⊓ conjR (pstd F) (A : SL(4, F))) := by
  rw [← map_pSig_inf, card_map_inj _ (msigma F).subtype_injective]

theorem card_pSig (hF : Nat.card F = 4) : Nat.card (pSig F) = 2 ^ 6 := by
  rw [← card_map_inj _ (msigma F).subtype_injective, Subgroup.subgroupOf_map_subtype, inf_comm,
    card_msigma_inf_pstd hF]

theorem card_inf_conjR_unitary (hF : Nat.card F = 4) (ψ : SU42b × SU42b ≃* Γ) (τ : Γ →* Γ)
    (hτ : ∀ p, τ (ψ p) = ψ p.swap) (χb : msigma F →* Γ) (hχb : Function.Injective χb)
    (hfix : ∀ A, τ (χb A) = χb A) {Pb : Subgroup Γ} (hP2 : IsPGroup 2 Pb)
    (hPc : Nat.card Pb = 2 ^ 12) (hPσ : ∀ A ∈ pSig F, χb A ∈ Pb) (A : msigma F) :
    Nat.card (Pb ⊓ conjR Pb (χb A) : Subgroup Γ) =
      Nat.card ↥(msigma F ⊓ pstd F ⊓ conjR (pstd F) (A : SL(4, F))) ^ 2 := by
  set ψi := ψ.symm.toMonoidHom
  have hψi : Function.Injective ψi := ψ.symm.injective
  set β : msigma F →* SU42b := (MonoidHom.fst _ _).comp (ψi.comp χb)
  have hdiag : ∀ A, ψi (χb A) = (β A, β A) := fun A => by
    have h1 : ψ (ψi (χb A)).swap = ψ (ψi (χb A)) := by
      rw [← hτ]
      simp only [ψi, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, hfix]
    have h2 := ψ.injective h1
    exact Prod.ext rfl (congrArg Prod.snd h2).symm
  have hβ : Function.Injective β := fun A B hAB => by
    apply hχb
    apply hψi
    rw [hdiag, hdiag, hAB]
  set U := (pSig F).map β
  have hU : Nat.card U = 2 ^ 6 := by rw [card_map_inj _ hβ, card_pSig hF]
  set Q := Pb.map ψi
  have hQ : Nat.card Q = 2 ^ 12 := by rw [card_map_inj _ hψi, hPc]
  have hQ2 : IsPGroup 2 Q := hP2.map ψi
  have hUQ : ∀ x ∈ U, (x, x) ∈ Q := by
    rintro _ ⟨A, hA, rfl⟩
    exact ⟨χb A, hPσ A hA, hdiag A⟩
  have hcard : Nat.card SU42b = 2 ^ 6 * 405 := by rw [card_SU42b]; norm_num
  have hfst : Q.map (MonoidHom.fst _ _) = U := by
    refine (Subgroup.eq_of_le_of_card_ge
      (fun x hx => Subgroup.mem_map.mpr ⟨(x, x), hUQ x hx, rfl⟩) ?_).symm
    rw [hU]
    exact card_le_of_isPGroup (hQ2.map _) (by norm_num) hcard
  have hsnd : Q.map (MonoidHom.snd _ _) = U := by
    refine (Subgroup.eq_of_le_of_card_ge
      (fun x hx => Subgroup.mem_map.mpr ⟨(x, x), hUQ x hx, rfl⟩) ?_).symm
    rw [hU]
    exact card_le_of_isPGroup (hQ2.map _) (by norm_num) hcard
  have hQUU : Q = U.prod U := by
    refine Subgroup.eq_of_le_of_card_ge (fun q hq => ?_) ?_
    · exact ⟨hfst ▸ Subgroup.mem_map.mpr ⟨q, hq, rfl⟩, hsnd ▸ Subgroup.mem_map.mpr ⟨q, hq, rfl⟩⟩
    · rw [card_prod', hU, hQ]; norm_num
  have hconj : Q ⊓ conjR Q (β A, β A) = (U ⊓ conjR U (β A)).prod (U ⊓ conjR U (β A)) := by
    rw [hQUU]
    ext ⟨x, y⟩
    simp only [Subgroup.mem_inf, Subgroup.mem_prod, mem_conjR, Prod.mk_mul_mk, Prod.inv_mk]
    tauto
  have hUA : U ⊓ conjR U (β A) = (pSig F ⊓ conjR (pSig F) A).map β :=
    (map_inf_conjR_inj β hβ _ A).symm
  have h1 : Nat.card (Pb ⊓ conjR Pb (χb A) : Subgroup Γ) =
      Nat.card (Q ⊓ conjR Q (β A, β A) : Subgroup _) := by
    rw [← card_map_inj ψi hψi, map_inf_conjR_inj ψi hψi, hdiag]
  rw [h1, hconj, card_prod', hUA, card_map_inj _ hβ, card_pSig_inf, sq]

end Unitary

section Linear

variable {Γ : Type} [Group Γ] [Finite Γ] {F : Type} [Field F] [Finite F] [CharP F 2]

theorem center_SL4_eq_bot : center SL(4, F) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Fintype.card_fin] at hr
  have h1 : (r + 1) ^ 2 ^ 2 = r ^ 2 ^ 2 + 1 := by
    rw [add_pow_char_pow, one_pow]
  have h2 : (r + 1) ^ 2 ^ 2 = 0 := by
    rw [h1, show (2 : ℕ) ^ 2 = 4 by norm_num, hr, CharTwo.add_self_eq_zero]
  have hr1 : r = 1 := by
    have := (pow_eq_zero_iff (n := 2 ^ 2) (by norm_num)).mp h2
    rwa [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at this
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrA, hr1, map_one, Matrix.SpecialLinearGroup.coe_one]

@[expose] def autOf (τ : Γ →* Γ) (hττ : ∀ g, τ (τ g) = g) : MulAut Γ where
  toFun := τ
  invFun := τ
  left_inv := hττ
  right_inv := hττ
  map_mul' := map_mul τ

theorem autOf_mul_conj (τ : Γ →* Γ) (hττ : ∀ g, τ (τ g) = g) (g : Γ) :
    autOf τ hττ * MulAut.conj g * (autOf τ hττ)⁻¹ = MulAut.conj (τ g) := by
  ext y
  have hinv : (autOf τ hττ)⁻¹ y = τ y := rfl
  simp only [MulAut.mul_apply, hinv, MulAut.conj_apply, map_mul, map_inv]
  change τ g * τ (τ y) * (τ g)⁻¹ = _
  rw [hττ]

theorem card_inf_conjR_linear (hL44 : L44Input) (hF : Nat.card F = 4) (ψ : SL(4, F) →* Γ)
    (hψ : Function.Bijective ψ) (τ : Γ →* Γ) (hττ : ∀ g, τ (τ g) = g)
    (χb : msigma F →* Γ) (hχb : Function.Injective χb) (hfix : ∀ γ, τ γ = γ ↔ γ ∈ χb.range)
    {Pb : Subgroup Γ} (hPS : IsSylowOf 2 Pb ⊤) (hPσ : ∀ A ∈ pSig F, χb A ∈ Pb)
    (A : msigma F) :
    Nat.card (Pb ⊓ conjR Pb (χb A) : Subgroup Γ) =
      Nat.card ↥(pstd F ⊓ conjR (pstd F) (A : SL(4, F))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut Γ) := Finite.of_injective (fun f : MulAut Γ => (f : Γ → Γ))
    (fun f g hfg => MulEquiv.ext (congrFun hfg))
  have hcent : ∀ g : Γ, (∀ x, g * x = x * g) → g = 1 := by
    intro g hg
    obtain ⟨a, rfl⟩ := hψ.2 g
    have ha : a ∈ center SL(4, F) := Subgroup.mem_center_iff.mpr fun b => hψ.1 (by
      rw [map_mul, map_mul, hg])
    rw [center_SL4_eq_bot, Subgroup.mem_bot] at ha
    rw [ha, map_one]
  set c := (MulAut.conj : Γ →* MulAut Γ)
  have hc : Function.Injective c := by
    intro g g' hgg'
    have h1 : ∀ x, g * x * g⁻¹ = g' * x * g'⁻¹ := fun x => by
      have := congrArg (fun f : MulAut Γ => f x) hgg'
      simpa [c, MulAut.conj_apply] using this
    have h2 := hcent (g'⁻¹ * g) fun x => by
      have := h1 x
      calc g'⁻¹ * g * x = g'⁻¹ * (g * x * g⁻¹) * g := by group
        _ = g'⁻¹ * (g' * x * g'⁻¹) * g := by rw [this]
        _ = x * (g'⁻¹ * g) := by group
    calc g = g' * (g'⁻¹ * g) := by group
      _ = g' := by rw [h2, mul_one]
  set L₁ := c.range
  set ψ' : SL(4, F) →* L₁ := c.rangeRestrict.comp ψ
  have hψ' : Function.Surjective ψ' := c.rangeRestrict_surjective.comp hψ.2
  have hker : ψ'.ker ≤ center SL(4, F) := by
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    have h1 : c (ψ a) = c 1 := by
      have := congrArg Subtype.val ha
      simpa [ψ', c] using this
    rw [hψ.1 ((hc h1).trans (map_one ψ).symm)]
    exact Subgroup.one_mem _
  set tb := autOf τ hττ
  have htb : tb * tb = 1 := MulEquiv.ext fun x => hττ x
  have htinv : tb⁻¹ = tb := inv_eq_of_mul_eq_one_right htb
  have hconj : ∀ g, tb * c g * tb⁻¹ = c (τ g) := autOf_mul_conj τ hττ
  have htN : tb ∈ normalizer (L₁ : Set (MulAut Γ)) := by
    rw [mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨τ g, (hconj g).symm⟩
    · rintro ⟨g, hg⟩
      refine ⟨τ g, ?_⟩
      rw [← hconj g, hg, htinv]
      calc tb * (tb * x * tb) * tb = (tb * tb) * x * (tb * tb) := by group
        _ = x := by rw [htb]; group
  have hχL : ∀ A, c (χb A) ∈ (L₁ ⊓ centralizer ({tb} : Set (MulAut Γ)) : Subgroup _) :=
    fun A => ⟨⟨χb A, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr (by
      have h1 := hconj (χb A)
      rw [(hfix (χb A)).mpr ⟨A, rfl⟩] at h1
      calc c (χb A) * tb = tb * c (χb A) * tb⁻¹ * tb := by rw [h1]
        _ = tb * c (χb A) := by group)⟩
  set χ'' := (c.comp χb).codRestrict _ hχL
  have hχ''b : Function.Bijective χ'' := by
    refine ⟨fun A B hAB => hχb (hc (congrArg Subtype.val hAB)), ?_⟩
    rintro ⟨x, ⟨g, rfl⟩, hx⟩
    have h1 : c g * tb = tb * c g := Subgroup.mem_centralizer_singleton_iff.mp hx
    have h2 : c (τ g) = c g := by
      rw [← hconj, ← h1, mul_inv_cancel_right]
    obtain ⟨A, hA⟩ := (hfix g).mp (hc h2)
    exact ⟨A, Subtype.ext (by simp [χ'', hA])⟩
  set χ' := MulEquiv.ofBijective χ'' hχ''b
  have hχ' : ∀ A, (χ' A : MulAut Γ) = c (χb A) := fun A => rfl
  set P₁ := Pb.map c
  have hP₁ : IsSylowOf 2 P₁ L₁ := by
    refine isSylowOf_of_card (Subgroup.map_le_range c Pb) ?_
    rw [card_map_inj c hc, hPS.card_eq, Subgroup.card_top,
      Nat.card_congr (MonoidHom.ofInjective hc).toEquiv]
  have hS : ∀ A : msigma F, (A : SL(4, F)) ∈ pstd F → (χ' A : MulAut Γ) ∈ P₁ := fun A hA =>
    ⟨χb A, hPσ A (Subgroup.mem_subgroupOf.mpr hA), rfl⟩
  obtain ⟨φ, hφ, -, hφχ, -, hφP⟩ := hL44 F hF (MulAut Γ) L₁ ψ' hψ' hker tb htb htN χ' P₁ hP₁ hS
  rw [← card_map_inj c hc, map_inf_conjR_inj c hc, ← hχ', ← hφχ, show Pb.map c = P₁ from rfl,
    ← hφP, ← map_inf_conjR_inj φ hφ, card_map_inj φ hφ]

end Linear

theorem sY_mem_msigma' (F : Type) [Field F] [Finite F] [CharP F 2] :
    sY F 0 * sY F 2 ∈ msigma F ∧ sY F 1 ∈ msigma F := by
  refine ⟨?_, ?_⟩
  · change YamadaEnd.sigmaSL F (sY F 0 * sY F 2) = sY F 0 * sY F 2
    rw [map_mul, sigmaSL_sY_zero, sigmaSL_sY_two]
    exact (CFSG.ClassicalInvolution.WeakCT.blockSL2_comm 3 0 2 (by decide) _ _).symm
  · exact sigmaSL_sY_one F

theorem factorization_two_mul {k m : ℕ} (hm : ¬ 2 ∣ m) : (2 ^ k * m).factorization 2 = k := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero 2)
  rw [Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero]

section Main

variable {G : Type} [Group G] {t : G} {D₁ V₁ A₁ K₁ D₂ : Subgroup G} {θ : K₁ ≃* SU42b}
  {ιG : (Fin 8 → ZMod 2) → G}

theorem Y13Hyp.card_inf_conjR_w [Finite G] (h : Y13Hyp t D₁ V₁ A₁ K₁ D₂ θ ιG)
    (hL44 : L44Input) (F : Type) [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    {S P : Subgroup G} {w₂ w₃ : G} (χ : msigma F ≃* K₁)
    (hw₂ : ∀ A : msigma F, (A : SL(4, F)) = sY F 0 * sY F 2 → (χ A : G) = w₂)
    (hw₃ : ∀ A : msigma F, (A : SL(4, F)) = sY F 1 → (χ A : G) = w₃)
    (hχS : ∀ A : msigma F, (A : SL(4, F)) ∈ pstd F → (χ A : G) ∈ S)
    (hP : IsSylowOf 2 P (nOne D₁ K₁ D₂)) (hSP : S ≤ P) (hD₁P : D₁ ≤ P) :
    Nat.card (P ⊓ conjR P w₂ : Subgroup G) = 2 ^ 26 ∧
      Nat.card (P ⊓ conjR P w₃ : Subgroup G) = 2 ^ 28 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (ElemSec D₁ V₁) := ⟨h.sec⟩
  have : (D₁.subgroupOf (nOne D₁ K₁ D₂)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.D₁_le_nOne).mpr h.nOne_le_normalizer
  obtain ⟨fV, hfV⟩ := h.exists_fV
  obtain ⟨hfix, hcase⟩ := (h.r3Hyp fV hfV).main
  set χb := (kmap h).comp χ.toMonoidHom
  have hχb : Function.Injective χb := (kmap_injective h).comp χ.injective
  have hfixχ : ∀ γ, tauG h γ = γ ↔ γ ∈ χb.range := fun γ => by
    constructor
    · intro hγ
      obtain ⟨k, hk⟩ := hfix γ hγ
      exact ⟨χ.symm k, by simp [χb, hk]⟩
    · rintro ⟨A, rfl⟩
      exact h.r3_τK ⟨χ A, rfl⟩
  set Pb := barG D₁ K₁ D₂ P
  have hPN := hP.le
  have hPcard : Nat.card P = 2 ^ 30 := by rw [hP.card_eq, h.factorization_card_nOne]
  have hPb : Nat.card Pb = 2 ^ 12 := by
    have := card_eq_mul_card_barG (K₁ := K₁) (D₂ := D₂) hD₁P hPN
    rw [hPcard, h.card_D₁] at this
    have h2 : 2 ^ 18 * Nat.card Pb = 2 ^ 18 * 2 ^ 12 := by rw [← this]; norm_num
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h2
  have hPσ : ∀ A ∈ pSig F, χb A ∈ Pb := fun A hA =>
    (mkG_mem_barG_iff hD₁P _).mpr (hSP (hχS A (Subgroup.mem_subgroupOf.mp hA)))
  obtain ⟨hu, hv⟩ := sY_mem_msigma' F
  set A₂ : msigma F := ⟨_, hu⟩
  set A₃ : msigma F := ⟨_, hv⟩
  have hw₂N : w₂ ∈ nOne D₁ K₁ D₂ := hw₂ A₂ rfl ▸ h.K₁_le_nOne (χ A₂).2
  have hw₃N : w₃ ∈ nOne D₁ K₁ D₂ := hw₃ A₃ rfl ▸ h.K₁_le_nOne (χ A₃).2
  have hχ₂ : χb A₂ = mkG D₁ K₁ D₂ ⟨w₂, hw₂N⟩ := by
    simp only [χb, kmap, MonoidHom.comp_apply]
    congr 1
    exact Subtype.ext (hw₂ A₂ rfl)
  have hχ₃ : χb A₃ = mkG D₁ K₁ D₂ ⟨w₃, hw₃N⟩ := by
    simp only [χb, kmap, MonoidHom.comp_apply]
    congr 1
    exact Subtype.ext (hw₃ A₃ rfl)
  rw [card_inf_conjR_eq hD₁P hPN h.nOne_le_normalizer hw₂N,
    card_inf_conjR_eq hD₁P hPN h.nOne_le_normalizer hw₃N, ← hχ₂, ← hχ₃, h.card_D₁]
  rcases hcase with ⟨ψ, -⟩ | ⟨ψ, hτ⟩
  ·
    set ψF := ψ.toMonoidHom.comp (slEquivF4 F hF).toMonoidHom
    have hψF : Function.Bijective ψF :=
      ⟨ψ.injective.comp (slEquivF4 F hF).injective, ψ.surjective.comp (slEquivF4 F hF).surjective⟩
    have hΓ : Nat.card (↥(nOne D₁ K₁ D₂) ⧸ D₁.subgroupOf (nOne D₁ K₁ D₂)) = 2 ^ 12 * 240975 := by
      rw [← Nat.card_congr ψ.toEquiv, card_SL4]; norm_num
    have hPS : IsSylowOf 2 Pb ⊤ := isSylowOf_of_card le_top (by
      rw [hPb, Subgroup.card_top, hΓ, factorization_two_mul (by norm_num)])
    rw [card_inf_conjR_linear hL44 hF ψF hψF (tauG h) h.r3_ττ χb hχb hfixχ hPS hPσ A₂,
      card_inf_conjR_linear hL44 hF ψF hψF (tauG h) h.r3_ττ χb hχb hfixχ hPS hPσ A₃,
      card_pstd_inf_u₀, card_pstd_inf_v₀, hF]
    norm_num
  ·
    have hP2 : IsPGroup 2 Pb := IsPGroup.of_card hPb
    have hfix' : ∀ A, tauG h (χb A) = χb A := fun A => (hfixχ _).mpr ⟨A, rfl⟩
    rw [card_inf_conjR_unitary hF ψ (tauG h) hτ χb hχb hfix' hP2 hPb hPσ A₂,
      card_inf_conjR_unitary hF ψ (tauG h) hτ χb hχb hfix' hP2 hPb hPσ A₃,
      card_msigma_inf_u₀ hF, card_msigma_inf_v₀ hF]
    norm_num

end Main

end CFSG.EvenSmallLie.UnitarySix.YamadaPar
