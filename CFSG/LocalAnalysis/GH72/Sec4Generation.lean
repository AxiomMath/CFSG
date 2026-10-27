module

public import CFSG.LocalAnalysis.GH72.Sec4Factor
public import CFSG.StronglyEmbedded.DihedralSylowNoStrongEmbedding
public import CFSG.Open.BenderStronglyEmbedded
public import CFSG.CGT.PushingUpLit.T2KSW.StrongEmb
public import CFSG.Holt.H78.Prelim
public import CFSG.Dihedral.GorensteinWalter.FieldTransport
public import CFSG.Walter.Bender1970.S2.PSL2Overgroups

public section

namespace CFSG.GH72

open Subgroup
open scoped MatrixGroups

namespace G4c

section Basic

variable {Γ : Type*} [Group Γ]

theorem not_fusionStronglyEmbedded_of_comm (hc : ∀ x y : Γ, x * y = y * x) (H : Subgroup Γ) :
    ¬ CFSG.Open.fusionStronglyEmbedded H := by
  rintro ⟨hH, hev, hodd⟩
  obtain ⟨g, hg⟩ : ∃ g, g ∉ H := by
    by_contra h
    push Not at h
    exact hH (eq_top_iff.mpr fun g _ => h g)
  have e : (MulAut.conj g⁻¹).toMonoidHom = MonoidHom.id Γ := by
    ext x
    show g⁻¹ * x * g⁻¹⁻¹ = x
    rw [hc g⁻¹ x, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
  have h := hodd g hg
  rw [e, map_id, inf_idem] at h
  exact (Nat.not_even_iff_odd.mpr h) hev

theorem isKleinFour_of_mulEquiv {V W : Type*} [Group V] [Group W] (e : V ≃* W) [IsKleinFour W] :
    IsKleinFour V :=
  ⟨by rw [Nat.card_congr e.toEquiv]; exact IsKleinFour.card_four,
    by rw [Monoid.exponent_eq_of_mulEquiv e]; exact IsKleinFour.exponent_two⟩

theorem nonempty_map_mk'_mulEquiv {K P : Subgroup Γ} [K.Normal] (h : P ⊓ K = ⊥) :
    Nonempty (P.map (QuotientGroup.mk' K) ≃* P) := by
  set φ : P →* Γ ⧸ K := (QuotientGroup.mk' K).comp P.subtype with hφ
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
      QuotientGroup.ker_mk'] at hx
    have hx' : (x : Γ) ∈ P ⊓ K := ⟨x.2, hx⟩
    rw [h, mem_bot] at hx'
    rw [mem_bot]
    exact Subtype.ext hx'
  have hrange : φ.range = P.map (QuotientGroup.mk' K) := by
    rw [hφ, MonoidHom.range_comp, range_subtype]
  exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm⟩

variable [Finite Γ]

theorem sup_eq_top_of_normalizer_le {K H : Subgroup Γ} [K.Normal] (hK : Odd (Nat.card K))
    (P : Sylow 2 Γ) (hP : (P : Subgroup Γ) ≠ ⊥)
    (hN : ∀ R : Subgroup Γ, R ≤ P → R ≠ ⊥ → normalizer (R : Set Γ) ≤ H)
    (hSE : ∀ H' : Subgroup (Γ ⧸ K), ¬ CFSG.Open.fusionStronglyEmbedded H') : H ⊔ K = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPK : (P : Subgroup Γ) ⊓ K = ⊥ := by
    rw [inf_comm]
    exact inf_eq_bot_of_odd_of_isPGroup hK P.isPGroup'
  by_cases hHt : H.map (QuotientGroup.mk' K) = ⊤
  · rw [eq_top_iff]
    intro g _
    have hg : QuotientGroup.mk' K g ∈ H.map (QuotientGroup.mk' K) := hHt ▸ mem_top _
    obtain ⟨h, hh, hhg⟩ := hg
    have hk : h⁻¹ * g ∈ K := by
      rw [← QuotientGroup.ker_mk' K, MonoidHom.mem_ker, map_mul, map_inv, hhg, inv_mul_cancel]
    rw [show g = h * (h⁻¹ * g) by group]
    exact mul_mem_sup hh hk
  · exfalso
    set B : Sylow 2 (Γ ⧸ K) := Sylow.mapSurjective (QuotientGroup.mk'_surjective K) P with hBdef
    have hBc : (B : Subgroup (Γ ⧸ K)) = (P : Subgroup Γ).map (QuotientGroup.mk' K) :=
      Sylow.coe_mapSurjective _ _
    have hB : CFSG.ABGLocalTools.IsSylowOf 2 (B : Subgroup (Γ ⧸ K)) ⊤ :=
      ⟨B.subtype le_top, by rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_top]⟩
    have hbot : ∀ R : Subgroup Γ, R ≤ P → R.map (QuotientGroup.mk' K) = ⊥ → R = ⊥ := by
      intro R hRP hR
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hR
      rw [eq_bot_iff, ← hPK]
      exact le_inf hRP hR
    have hB1 : (B : Subgroup (Γ ⧸ K)) ≠ ⊥ := by
      rw [hBc]
      exact fun h => hP (hbot _ le_rfl h)
    refine hSE _ (CFSG.CGT.PushingUpLit.T2KSW.fusionStronglyEmbedded_of_normalizer_le hB hB1 hHt ?_)
    intro R' hR'B hR'1
    set R := (P : Subgroup Γ) ⊓ R'.comap (QuotientGroup.mk' K) with hR
    have hRR' : R.map (QuotientGroup.mk' K) = R' := by
      apply le_antisymm
      · rw [map_le_iff_le_comap]
        exact inf_le_right
      · intro r hr
        have hr' : r ∈ (P : Subgroup Γ).map (QuotientGroup.mk' K) := by
          rw [← hBc]
          exact hR'B hr
        obtain ⟨p, hp, rfl⟩ := hr'
        exact mem_map_of_mem _ ⟨hp, hr⟩
    have hR1 : R ≠ ⊥ := fun h => hR'1 (by rw [← hRR', h, Subgroup.map_bot])
    rw [← hRR', ← CFSG.Holt.H78.map_normalizer_eq_of_odd K hK (P.isPGroup'.to_le inf_le_left)]
    exact map_mono (hN R inf_le_left hR1)

theorem not_fusionStronglyEmbedded_of_isKleinFour {Q : Type}
    [Group Q] [Finite Q] (hQ : IsSimpleGroup Q) (B : Sylow 2 Q) (hB : IsKleinFour (B : Subgroup Q))
    (hnot : ¬ Nonempty (Q ≃* PSL(2, ZMod 5))) (H : Subgroup Q) :
    ¬ CFSG.Open.fusionStronglyEmbedded H := by
  intro hH
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB4 : Nat.card (B : Subgroup Q) = 4 := hB.card_four
  have hev : Even (Nat.card Q) := by
    have h := card_subgroup_dvd_card (B : Subgroup Q)
    rw [hB4] at h
    exact even_iff_two_dvd.mpr ((show (2 : ℕ) ∣ 4 by norm_num).trans h)
  have hsurj : ∀ {W : Type} [Group W] (e : Q ≃* W), Function.Surjective e.toMonoidHom :=
    fun e => e.surjective
  have hcard : ∀ {W : Type} [Group W] (e : Q ≃* W),
      Nat.card ((Sylow.mapSurjective (hsurj e) B : Sylow 2 W) : Subgroup W) = 4 := by
    intro W _ e
    rw [Sylow.coe_mapSurjective,
      card_map_of_injective (show Function.Injective e.toMonoidHom from e.injective), hB4]
  rcases CFSG.Open.Open.bender_strongly_embedded Q H hH with
    h | ⟨M', N', hM'n, hN'n, hMN, -, hM'odd, hN'odd, hBG⟩
  · rcases h B with hc | ⟨r, hr, ⟨e⟩⟩
    · exact @IsKleinFour.not_isCyclic _ _ hB hc
    · have h1 := Nat.card_congr e.toEquiv
      rw [hB4, Nat.card_eq_fintype_card, QuaternionGroup.card] at h1
      have h2 : 2 ≤ 2 ^ (r - 2) :=
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (r - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  · have := hM'n
    have := hN'n
    have hM' : M' = ⊥ := by
      refine (hQ.eq_bot_or_eq_top_of_normal M').resolve_right fun h => ?_
      rw [h, card_top] at hM'odd
      exact (Nat.not_even_iff_odd.mpr hM'odd) hev
    have hN' : N' = ⊤ := by
      refine (hQ.eq_bot_or_eq_top_of_normal N').resolve_left fun h => ?_
      rw [h, index_bot] at hN'odd
      exact (Nat.not_even_iff_odd.mpr hN'odd) hev
    subst hM' hN'
    have eW : Q ≃* (↥(⊤ : Subgroup Q) ⧸ (⊥ : Subgroup Q).subgroupOf ⊤) :=
      Subgroup.topEquiv.symm.trans (QuotientGroup.quotientBot.symm.trans
        (QuotientGroup.quotientMulEquivOfEq (bot_subgroupOf ⊤).symm))
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    rcases hBG with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
    · obtain ⟨-, -, -, -, hc⟩ := CFSG.Open.Open.bender_psl2_borel f hf
        (Sylow.mapSurjective (hsurj (eW.trans e)) B)
      rw [hcard (eW.trans e), pow_one] at hc
      have hf2 : f = 2 := Nat.pow_right_injective le_rfl (show 2 ^ f = 2 ^ 2 by rw [← hc])
      subst hf2
      obtain ⟨e₅⟩ := CFSG.Walter.nonempty_psl2_five_mulEquiv_psl2_four
      exact hnot ⟨((eW.trans e).trans e₅.symm).trans
        (CFSG.GorensteinWalter.FieldTransport.pslZModEquivGaloisFieldOne 5).symm⟩
    · obtain ⟨-, -, -, -, hc⟩ := CFSG.Open.Open.bender_psu3_borel f hf
        (Sylow.mapSurjective (hsurj (eW.trans e)) B)
      rw [hcard (eW.trans e), ← pow_mul] at hc
      have h2 := Nat.pow_right_injective le_rfl (show 2 ^ 2 = 2 ^ (f * 3) by rw [← hc])
      omega
    · obtain ⟨-, -, -, -, hc⟩ := CFSG.Open.Open.bender_suzuki_borel a ha
        (Sylow.mapSurjective (hsurj (eW.trans e)) B)
      rw [hcard (eW.trans e), ← pow_mul] at hc
      have h2 := Nat.pow_right_injective le_rfl (show 2 ^ 2 = 2 ^ ((2 * a + 1) * 2) by rw [← hc])
      omega

end Basic

section Setting

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_map_subtype {K : Subgroup G} {R : Subgroup K} {n : K}
    (hn : n ∈ normalizer (R : Set K)) :
    (n : G) ∈ normalizer ((R.map K.subtype : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨n * r * n⁻¹, (mem_normalizer_iff.mp hn r).mp hr, rfl⟩
  · rintro ⟨r, hr, hrx⟩
    have hx : x = ((n⁻¹ * r * n : K) : G) := by
      have hrx' : (r : G) = n * x * (n : G)⁻¹ := hrx
      simp only [coe_mul, coe_inv, hrx']
      group
    rw [hx]
    have h := (mem_normalizer_iff.mp (inv_mem hn) r).mp hr
    rw [inv_inv] at h
    exact ⟨_, h, rfl⟩

omit [Finite G] in
theorem C_le_normalizer_zpowers (y : G) : C y ≤ normalizer ((zpowers y : Subgroup G) : Set G) :=
  fun c hc => by
    refine mem_normalizer_of_map_cj_eq ?_
    rw [MonoidHom.map_zpowers, cj_apply, mem_centralizer_singleton_iff.mp hc,
      mul_inv_cancel_right]

theorem exists_sylow_quotient_mulEquiv {K K₀ T : Subgroup G} [((O K).subgroupOf K₀).Normal]
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T K₀) :
    ∃ B : Sylow 2 (K₀ ⧸ (O K).subgroupOf K₀),
      Nonempty ((B : Subgroup (K₀ ⧸ (O K).subgroupOf K₀)) ≃* T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hPT⟩ := hT
  refine ⟨Sylow.mapSurjective (QuotientGroup.mk'_surjective _) P, ?_⟩
  have hPK : (P : Subgroup K₀) ⊓ (O K).subgroupOf K₀ = ⊥ := by
    rw [inf_comm]
    exact inf_eq_bot_of_odd_of_isPGroup (Odd.of_dvd_nat (odd_card_O K) (card_subgroupOf_dvd _ _))
      P.isPGroup'
  obtain ⟨e₁⟩ := nonempty_map_mk'_mulEquiv hPK
  rw [Sylow.coe_mapSurjective]
  exact ⟨e₁.trans (((P : Subgroup K₀).equivMapOfInjective K₀.subtype
    K₀.subtype_injective).trans (MulEquiv.subgroupCongr hPT))⟩

theorem le_sup_O_of_forall {K K₀ Ks T : Subgroup G} (hK₀K : K₀ ≤ K) [((O K).subgroupOf K₀).Normal]
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T K₀) (hT1 : T ≠ ⊥)
    (hKs : ∀ R : Subgroup G, R ≤ T → R ≠ ⊥ → K ⊓ normalizer (R : Set G) ≤ Ks)
    (hSE : ∀ H' : Subgroup (K₀ ⧸ (O K).subgroupOf K₀), ¬ CFSG.Open.fusionStronglyEmbedded H') :
    K₀ ≤ Ks ⊔ O K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hPT⟩ := hT
  have hKodd : Odd (Nat.card ((O K).subgroupOf K₀)) :=
    Odd.of_dvd_nat (odd_card_O K) (card_subgroupOf_dvd _ _)
  have hP1 : (P : Subgroup K₀) ≠ ⊥ := fun h => hT1 (by rw [← hPT, h, Subgroup.map_bot])
  have htop := sup_eq_top_of_normalizer_le (H := Ks.subgroupOf K₀) hKodd P hP1
    (fun R hRP hR1 n hn => by
      rw [mem_subgroupOf]
      have hRT : R.map K₀.subtype ≤ T := (map_mono hRP).trans hPT.le
      have hR1' : R.map K₀.subtype ≠ ⊥ := fun h =>
        hR1 ((map_eq_bot_iff_of_injective _ K₀.subtype_injective).mp h)
      exact hKs _ hRT hR1' ⟨hK₀K n.2, mem_normalizer_map_subtype hn⟩) hSE
  intro m hm
  have h1 : (⟨m, hm⟩ : K₀) ∈ Ks.subgroupOf K₀ ⊔ (O K).subgroupOf K₀ := htop ▸ mem_top _
  have h2 := mem_map_of_mem K₀.subtype h1
  rw [Subgroup.map_sup, subgroupOf_map_subtype, subgroupOf_map_subtype] at h2
  exact (sup_le_sup (inf_le_left : Ks ⊓ K₀ ≤ Ks) (inf_le_left : O K ⊓ K₀ ≤ O K)) h2

end Setting

end G4c

namespace Sec4Setting

open G4c
open CFSG.CGT.Foote81L6.TStruct (isElemAbelian_two_iff comm_of_mul_self)

variable {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G}
  (hAS : A ≤ 𝔖.S) (hA : IsE16 A)

include hAS hA in
theorem lemma_4_16_of
    (h47 : QuotIs (𝔖.M₀ A) (O (𝔖.M A)) (fun L _ => IsL2OrA7 L 7) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₂ (𝔖.M₀ A) ∧
      𝔖.M A = 𝔖.M₀ A ⊔ (𝔖.M A ⊓ normalizer (A : Set G)) ∧
      𝔖.M A = 𝔖.M₀ A ⊔ (𝔖.M A ⊓ normalizer (𝔖.S₂ : Set G)) ∧
      (∀ x ∈ 𝔖.X A, x ≠ 1 → O2 (C x) = (O2 (𝔖.M A) ⊓ O2 (C x)) ⊔ O (C x)) ∧
      (∀ x ∈ 𝔖.X A, x ≠ 1 → ⁅O2 (C x), O2 (C x)⁆ ⊔ O (C x) =
        (𝔖.M₀ A ⊓ ⁅O2 (C x), O2 (C x)⁆) ⊔ O (C x)))
    (h48 : QuotIs (𝔖.N₀ A) (O (𝔖.N A)) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₁ (𝔖.N₀ A) ∧
      𝔖.N A = 𝔖.N₀ A ⊔ (𝔖.N A ⊓ normalizer (A : Set G)) ∧
      𝔖.N A = 𝔖.N₀ A ⊔ (𝔖.N A ⊓ normalizer (𝔖.S₁ : Set G)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → O2 (C y) = (O2 (𝔖.N A) ⊓ O2 (C y)) ⊔ O (C y)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → ⁅O2 (C y), O2 (C y)⁆ ⊔ O (C y) =
        (𝔖.N₀ A ⊓ ⁅O2 (C y), O2 (C y)⁆) ⊔ O (C y))) :
    𝔖.M A = ⨆ (T₂ : Subgroup G) (_ : T₂ ≤ 𝔖.S₂) (_ : T₂ ≠ ⊥),
      𝔖.M A ⊓ normalizer (T₂ : Set G) ∧
    (¬ QuotIs (𝔖.N₀ A) (O (𝔖.N A)) (fun L _ => Nonempty (L ≃* PSL(2, ZMod 5))) →
      𝔖.N A = ⨆ (T₁ : Subgroup G) (_ : T₁ ≤ 𝔖.S₁) (_ : T₁ ≠ ⊥),
        𝔖.N A ⊓ normalizer (T₁ : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYM : 𝔖.Y A ≤ 𝔖.M A := fun y hy => mem_centralizer_iff.mpr
    fun x hx => comm_of_mul_self (isElemAbelian_two_iff.1 hA.1) (X_le_A hx) (Y_le_A hy)
  have hXN : 𝔖.X A ≤ 𝔖.N A := fun x hx => mem_centralizer_iff.mpr
    fun y hy => comm_of_mul_self (isElemAbelian_two_iff.1 hA.1) (Y_le_A hy) (X_le_A hx)
  have hne : ∀ {T : Subgroup G} {z : G}, z ∈ T → orderOf z = 2 → T ≠ ⊥ := by
    intro T z hz hz2 h
    rw [h, mem_bot] at hz
    rw [hz, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hS₁1 : 𝔖.S₁ ≠ ⊥ := hne 𝔖.hz₁.1 𝔖.hz₁.2.1
  have hS₂1 : 𝔖.S₂ ≠ ⊥ := hne 𝔖.hz₂.1 𝔖.hz₂.2.1
  constructor
  ·
    set Ms := ⨆ (T₂ : Subgroup G) (_ : T₂ ≤ 𝔖.S₂) (_ : T₂ ≠ ⊥),
      𝔖.M A ⊓ normalizer (T₂ : Set G) with hMs
    have hle : ∀ T₂ : Subgroup G, T₂ ≤ 𝔖.S₂ → T₂ ≠ ⊥ → 𝔖.M A ⊓ normalizer (T₂ : Set G) ≤ Ms :=
      fun T₂ h₁ h₂ => le_iSup_of_le T₂ (le_iSup_of_le h₁ (le_iSup_of_le h₂ le_rfl))
    have hOM : O (𝔖.M A) ≤ Ms := by
      refine (le_iSup_inf_C (odd_card_O _) (isKleinFour_Y hAS hA)
        (hYM.trans (le_normalizer_O _))).trans
        (iSup_le fun y => iSup_le fun hy => iSup_le fun hy1 => ?_)
      exact (le_inf (inf_le_left.trans (O_le _))
        (inf_le_right.trans (C_le_normalizer_zpowers y))).trans
        (hle _ (zpowers_le.mpr (Y_le_S₂ hy)) (zpowers_eq_bot.not.mpr hy1))
    have : ((O (𝔖.M A)).subgroupOf (𝔖.M₀ A)).Normal :=
      normal_subgroupOf_of_le_normalizer (M₀_le_M.trans (le_normalizer_O _))
    have hSE : ∀ H' : Subgroup (𝔖.M₀ A ⧸ (O (𝔖.M A)).subgroupOf (𝔖.M₀ A)),
        ¬ CFSG.Open.fusionStronglyEmbedded H' := by
      obtain ⟨B, ⟨eB⟩⟩ := exists_sylow_quotient_mulEquiv (K := 𝔖.M A) h47.2.1
      obtain ⟨a, ha, ⟨eS⟩⟩ := 𝔖.decomp.dih₂
      exact CFSG.StronglyEmbedded.not_fusionStronglyEmbedded_of_sylow_mulEquiv_dihedralGroup B
        (m := 2 ^ a) (calc 3 ≤ 2 ^ 2 := by norm_num
          _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha) (eB.trans eS)
    have hM₀ : 𝔖.M₀ A ≤ Ms ⊔ O (𝔖.M A) := le_sup_O_of_forall M₀_le_M h47.2.1 hS₂1
      (fun R hR hR1 => hle R hR hR1) hSE
    refine le_antisymm ?_ (iSup_le fun T₂ => iSup_le fun _ => iSup_le fun _ => inf_le_left)
    calc 𝔖.M A = 𝔖.M₀ A ⊔ (𝔖.M A ⊓ normalizer (𝔖.S₂ : Set G)) := h47.2.2.2.1
      _ ≤ Ms := sup_le (hM₀.trans (sup_le le_rfl hOM)) (hle _ le_rfl hS₂1)
  ·
    intro hPSL
    set Ns := ⨆ (T₁ : Subgroup G) (_ : T₁ ≤ 𝔖.S₁) (_ : T₁ ≠ ⊥),
      𝔖.N A ⊓ normalizer (T₁ : Set G) with hNs
    have hle : ∀ T₁ : Subgroup G, T₁ ≤ 𝔖.S₁ → T₁ ≠ ⊥ → 𝔖.N A ⊓ normalizer (T₁ : Set G) ≤ Ns :=
      fun T₁ h₁ h₂ => le_iSup_of_le T₁ (le_iSup_of_le h₁ (le_iSup_of_le h₂ le_rfl))
    have hON : O (𝔖.N A) ≤ Ns := by
      refine (le_iSup_inf_C (odd_card_O _) (isKleinFour_X hAS hA)
        (hXN.trans (le_normalizer_O _))).trans
        (iSup_le fun x => iSup_le fun hx => iSup_le fun hx1 => ?_)
      exact (le_inf (inf_le_left.trans (O_le _))
        (inf_le_right.trans (C_le_normalizer_zpowers x))).trans
        (hle _ (zpowers_le.mpr (X_le_S₁ hx)) (zpowers_eq_bot.not.mpr hx1))
    have : ((O (𝔖.N A)).subgroupOf (𝔖.N₀ A)).Normal :=
      normal_subgroupOf_of_le_normalizer (N₀_le_N.trans (le_normalizer_O _))
    have hnot : ¬ Nonempty ((𝔖.N₀ A ⧸ (O (𝔖.N A)).subgroupOf (𝔖.N₀ A)) ≃* PSL(2, ZMod 5)) :=
      fun h => hPSL ⟨_, inferInstance, QuotientGroup.mk' _, QuotientGroup.mk'_surjective _,
        QuotientGroup.ker_mk' _, h⟩
    have hSE : ∀ H' : Subgroup (𝔖.N₀ A ⧸ (O (𝔖.N A)).subgroupOf (𝔖.N₀ A)),
        ¬ CFSG.Open.fusionStronglyEmbedded H' := by
      obtain ⟨B, ⟨eB⟩⟩ := exists_sylow_quotient_mulEquiv (K := 𝔖.N A) h48.2.1
      obtain ⟨a, ha, ⟨eS⟩⟩ := 𝔖.decomp.dih₁
      rcases Nat.lt_or_ge a 2 with ha2 | ha2
      ·
        obtain rfl : a = 1 := by omega
        obtain ⟨L, _, f, hf, hker, hL⟩ := h48.1
        let eQL : (𝔖.N₀ A ⧸ (O (𝔖.N A)).subgroupOf (𝔖.N₀ A)) ≃* L :=
          (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
            (QuotientGroup.quotientKerEquivOfSurjective f hf)
        rcases hL with hL | hL
        · have hQs := (MulEquiv.isSimpleGroup_congr eQL).mpr (isSimpleGroup_of_isL2OrA7' le_rfl hL)
          have h4 : IsKleinFour (DihedralGroup (2 ^ 1)) := by
            rw [pow_one]
            infer_instance
          exact not_fusionStronglyEmbedded_of_isKleinFour hQs B
            (isKleinFour_of_mulEquiv (eB.trans eS)) hnot
        · have hcL : ∀ x y : L, x * y = y * x := mul_comm_of_exponent_two hL.exponent_two
          exact not_fusionStronglyEmbedded_of_comm fun x y =>
            eQL.injective (by rw [map_mul, map_mul, hcL])
      · exact CFSG.StronglyEmbedded.not_fusionStronglyEmbedded_of_sylow_mulEquiv_dihedralGroup B
          (m := 2 ^ a) (calc 3 ≤ 2 ^ 2 := by norm_num
            _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha2) (eB.trans eS)
    have hN₀ : 𝔖.N₀ A ≤ Ns ⊔ O (𝔖.N A) := le_sup_O_of_forall N₀_le_N h48.2.1 hS₁1
      (fun R hR hR1 => hle R hR hR1) hSE
    refine le_antisymm ?_ (iSup_le fun T₁ => iSup_le fun _ => iSup_le fun _ => inf_le_left)
    calc 𝔖.N A = 𝔖.N₀ A ⊔ (𝔖.N A ⊓ normalizer (𝔖.S₁ : Set G)) := h48.2.2.2.1
      _ ≤ Ns := sup_le (hN₀.trans (sup_le le_rfl hON)) (hle _ le_rfl hS₁1)

end Sec4Setting

end CFSG.GH72
