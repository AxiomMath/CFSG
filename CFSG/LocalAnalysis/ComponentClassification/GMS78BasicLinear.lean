module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Aut

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open
open CFSG.ComponentClassification.AschbacherToolkit.Bender
open CFSG.ComponentClassification.AschbacherToolkit.Bender.LinearInv
open scoped MatrixGroups

theorem card_fix_semilinear_le {K : Type*} [Field K] [Finite K] (θ : K →+* K) (lam : K) :
    Nat.card {b : K // lam * θ b = b} ≤ Nat.card {x : K // θ x = x} := by
  classical
  by_cases h : ∃ b₀ : K, b₀ ≠ 0 ∧ lam * θ b₀ = b₀
  · obtain ⟨b₀, hb₀, hfix⟩ := h
    have hlam : lam ≠ 0 := by
      rintro rfl
      rw [zero_mul] at hfix
      exact hb₀ hfix.symm
    have hθ : ∀ b : K, lam * θ b = b → θ b = b / lam := fun b hb => by
      rw [eq_div_iff hlam, mul_comm, hb]
    refine Nat.card_le_card_of_injective (fun b => ⟨b.1 / b₀, ?_⟩) ?_
    · rw [map_div₀, hθ b.1 b.2, hθ b₀ hfix]
      field_simp
    · intro b b' hbb
      have h1 : b.1 / b₀ = b'.1 / b₀ := congrArg Subtype.val hbb
      exact Subtype.ext ((div_left_inj' hb₀).mp h1)
  · push Not at h
    have hle : Nat.card {b : K // lam * θ b = b} ≤ 1 := by
      rw [Finite.card_le_one_iff_subsingleton]
      refine ⟨fun b b' => Subtype.ext ?_⟩
      have hb : b.1 = 0 := by
        by_contra hb0
        exact h b.1 hb0 b.2
      have hb' : b'.1 = 0 := by
        by_contra hb0
        exact h b'.1 hb0 b'.2
      rw [hb, hb']
    have : 1 ≤ Nat.card {x : K // θ x = x} :=
      Nat.one_le_iff_ne_zero.mpr (Nat.card_ne_zero.mpr ⟨⟨⟨0, map_zero θ⟩⟩, Subtype.finite⟩)
    omega

theorem card_fix_sq_le_of_not_inner_sl2 (f : ℕ) (hf : 2 ≤ f)
    (γ : MulAut SL(2, GaloisField 2 f)) (hγγ : γ * γ = 1)
    (hγ : ¬ ∃ y, γ = MulAut.conj y) (R : Sylow 2 SL(2, GaloisField 2 f))
    (hγR : ∀ r ∈ (R : Subgroup SL(2, GaloisField 2 f)), γ r ∈ (R : Subgroup _)) :
    Nat.card {r : (R : Subgroup SL(2, GaloisField 2 f)) // γ r = r} ^ 2 ≤
      Nat.card (R : Subgroup SL(2, GaloisField 2 f)) := by
  classical
  set K := GaloisField 2 f
  have : Finite K := inferInstance
  let eS : PSL(2, K) ≃* SL(2, K) := CFSG.Walter.psl2MulEquivSL2OfCharTwo
  have : Finite PSL(2, K) := Finite.of_injective eS eS.injective
  have hB : fusionBenderBorel SL(2, K) (2 ^ f) 1 :=
    (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_1 f
      hf).map_mulEquiv eS
  have : IsSimpleGroup SL(2, K) :=
    CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup
      (Or.inl ⟨f, hf, ⟨eS.symm⟩⟩)
  have hKcard : Nat.card K = 2 ^ f := GaloisField.card 2 f (by omega)
  have hsyl : ∀ H : Subgroup SL(2, K), Nat.card H = 2 ^ f →
      ∃ P : Sylow 2 SL(2, K), (P : Subgroup SL(2, K)) = H := by
    intro H hH
    obtain ⟨P, hP⟩ := (IsPGroup.of_card hH).exists_le_sylow
    refine ⟨P, (Subgroup.eq_of_le_of_card_ge hP ?_).symm⟩
    obtain ⟨-, -, -, hPcard⟩ := benderBorel_sylowCenter hB P
    rw [hPcard, hH, pow_one]
  obtain ⟨U, hU⟩ := hsyl upSub (by rw [card_upSub, hKcard])
  obtain ⟨V, hV⟩ := hsyl loSub (by rw [card_loSub, hKcard])
  obtain ⟨hSE, -, -, hUcard⟩ := benderBorel_sylowCenter hB U
  have hcard : Nat.card (Sylow 2 SL(2, K)) = Nat.card (U : Subgroup SL(2, K)) + 1 := by
    rw [← card_sylow_eq_of_mulEquiv eS 2, CFSG.Walter.psl2_even_card_sylow (by omega), hUcard,
      pow_one]
  have hVU : V ≠ U := by
    intro h
    apply upSub_ne_loSub (K := K)
    rw [← hU, ← hV, h]
  have hdich := invDichotomyAt_of_mulEquiv_psl2 hf eS.symm R
  rcases hdich γ hγγ hγR with hin | ⟨x, hxN, hxR⟩
  · exact absurd hin hγ
  have hγR' : γ • R = R := Omega.smul_eq_of_mapsTo hγR
  set R₀ := x • R with hR₀
  have hR₀R : R₀ ≠ R := fun h => hxN (Sylow.smul_eq_iff_mem_normalizer.mp h)
  have hγR₀ : γ • R₀ = R₀ := by
    apply Omega.smul_eq_of_mapsTo
    intro y hy
    show γ y ∈ ((x • R : Sylow 2 SL(2, K)) : Subgroup SL(2, K))
    rw [Omega.mem_conj_smul_iff] at hy ⊢
    have h1 := hxR _ hy
    have h2 : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
    rw [h2] at h1
    exact h1
  obtain ⟨g₁, hg₁⟩ := MulAction.exists_smul_eq SL(2, K) R U
  have hg₁R₀ : g₁ • R₀ ≠ U := by
    intro h
    apply hR₀R
    have h' : g₁ • R₀ = g₁ • R := h.trans hg₁.symm
    exact smul_left_cancel g₁ h'
  obtain ⟨r, hrU, hr⟩ := Omega.exists_smul_eq hSE hcard hg₁R₀ hVU
  set g := r * g₁ with hgdef
  have hgR : g • R = U := by
    rw [hgdef, mul_smul, hg₁]
    exact (Sylow.smul_eq_iff_mem_normalizer).mpr (le_normalizer hrU)
  have hgR₀ : g • R₀ = V := by rw [hgdef, mul_smul, hr]
  set γ' : MulAut SL(2, K) := MulAut.conj g * γ * (MulAut.conj g)⁻¹ with hγ'def
  have hγ'γ' : γ' * γ' = 1 := by
    rw [hγ'def, show MulAut.conj g * γ * (MulAut.conj g)⁻¹ * (MulAut.conj g * γ *
      (MulAut.conj g)⁻¹) = MulAut.conj g * (γ * γ) * (MulAut.conj g)⁻¹ by group, hγγ, mul_one,
      mul_inv_cancel]
  have hsmul : ∀ P : Sylow 2 SL(2, K), γ • P = P → γ' • (g • P) = g • P := by
    intro P hP
    rw [hγ'def, Sylow.smul_def, mul_smul, mul_smul, inv_smul_smul, hP]
  have hγ'U : γ' • U = U := by rw [← hgR]; exact hsmul R hγR'
  have hγ'V : γ' • V = V := by rw [← hgR₀]; exact hsmul R₀ hγR₀
  obtain ⟨θ, lam, hθθ, hlamθ, hγ'up⟩ := RankTwoBender.linear_coord U V hU hV γ' hγ'γ' hγ'U hγ'V
  have hθ : ∃ e, θ e ≠ e := by
    by_contra hall
    push Not at hall
    have hlam1 : lam = 1 := by
      have h := hlamθ
      rw [hall] at h
      exact CharTwo.sq_injective (show lam ^ 2 = 1 ^ 2 by rw [sq, h, one_pow])
    have h1 := Omega.eq_one_of_centralizes hSE hcard hVU γ' hγ'U hγ'V fun s hs => by
      rw [hU] at hs
      obtain ⟨b, rfl⟩ := mem_upSub.mp hs
      rw [hγ'up, hall, hlam1, one_mul]
    apply hγ
    refine ⟨1, ?_⟩
    have h2 : γ = (MulAut.conj g)⁻¹ * γ' * MulAut.conj g := by rw [hγ'def]; group
    rw [h2, h1, mul_one, inv_mul_cancel, map_one]
  obtain ⟨e₀, he₀⟩ := hθ
  have hfix := InvField.card_fix_sq θ hθθ he₀
  have hconj : ∀ y : SL(2, K), γ y = g⁻¹ * γ' (g * y * g⁻¹) * g := by
    intro y
    rw [hγ'def, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_symm_apply,
      MulAut.conj_apply]
    group
  have hmemU : ∀ y : SL(2, K),
      y ∈ (R : Subgroup SL(2, K)) ↔ g * y * g⁻¹ ∈ (U : Subgroup SL(2, K)) := by
    intro y
    rw [← hgR, Omega.mem_conj_smul_iff]
    simp [mul_assoc]
  have hex : ∀ y : {y : (R : Subgroup SL(2, K)) // γ y = y}, ∃ b : K,
      g * (y.1 : SL(2, K)) * g⁻¹ = up b ∧ lam * θ b = b := by
    rintro ⟨⟨y, hyR⟩, hy⟩
    have hyU := (hmemU y).mp hyR
    rw [hU] at hyU
    obtain ⟨b, hb⟩ := mem_upSub.mp hyU
    refine ⟨b, hb, up_injective ?_⟩
    rw [← hγ'up, ← hb]
    have h1 := hconj y
    have hy' : γ y = y := hy
    rw [hy'] at h1
    calc γ' (g * y * g⁻¹) = g * (g⁻¹ * γ' (g * y * g⁻¹) * g) * g⁻¹ := by group
      _ = g * y * g⁻¹ := by rw [← h1]
  choose bOf hbOf using hex
  have hinj : Function.Injective (fun y => (⟨bOf y, (hbOf y).2⟩ : {b : K // lam * θ b = b})) := by
    intro y y' hyy
    have h1 : bOf y = bOf y' := congrArg Subtype.val hyy
    have h2 : g * (y.1 : SL(2, K)) * g⁻¹ = g * (y'.1 : SL(2, K)) * g⁻¹ := by
      rw [(hbOf y).1, (hbOf y').1, h1]
    exact Subtype.ext (Subtype.ext (by simpa using h2))
  have hle := Nat.card_le_card_of_injective _ hinj
  have hle2 := card_fix_semilinear_le θ lam
  have hRU : Nat.card (R : Subgroup SL(2, K)) = Nat.card (U : Subgroup SL(2, K)) := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  have hRcard : Nat.card (R : Subgroup SL(2, K)) = Nat.card K := by
    rw [hRU, hUcard, hKcard, pow_one]
  calc Nat.card {r : (R : Subgroup SL(2, K)) // γ r = r} ^ 2
      ≤ Nat.card {x : K // θ x = x} ^ 2 := Nat.pow_le_pow_left (hle.trans hle2) 2
    _ = Nat.card (R : Subgroup SL(2, K)) := by rw [hfix, hRcard]

theorem card_fix_sq_le_of_not_inner_psl2 {X : Type*} [Group X]
    [Finite X] {f : ℕ} (hf : 2 ≤ f) (e : X ≃* PSL(2, GaloisField 2 f)) (α : MulAut X)
    (hαα : α * α = 1) (hα : ¬ ∃ y, α = MulAut.conj y) (R : Sylow 2 X)
    (hαR : ∀ r ∈ (R : Subgroup X), α r ∈ (R : Subgroup X)) :
    Nat.card {r : (R : Subgroup X) // α r = r} ^ 2 ≤ Nat.card (R : Subgroup X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e' : X ≃* SL(2, GaloisField 2 f) := e.trans CFSG.Walter.psl2MulEquivSL2OfCharTwo
  set γ := MulAut.congr e' α with hγ
  have hγapp : ∀ r, γ r = e' (α (e'.symm r)) := fun r => by
    have h := AschbacherToolkit.Bender.AutTransport.congr_apply' e' α (e'.symm r)
    rwa [MulEquiv.apply_symm_apply] at h
  have hγγ : γ * γ = 1 := by rw [hγ, ← map_mul, hαα, map_one]
  have hγout : ¬ ∃ y, γ = MulAut.conj y := by
    rintro ⟨y, hy⟩
    apply hα
    refine ⟨e'.symm y, (MulAut.congr e').injective ?_⟩
    rw [AschbacherToolkit.Bender.AutTransport.congr_conj, MulEquiv.apply_symm_apply, ← hγ, hy]
  let R' : Sylow 2 SL(2, GaloisField 2 f) := R.mapSurjective (f := e'.toMonoidHom) e'.surjective
  have hR' : (R' : Subgroup SL(2, GaloisField 2 f)) = (R : Subgroup X).map e'.toMonoidHom := rfl
  have hγR : ∀ r ∈ (R' : Subgroup SL(2, GaloisField 2 f)),
      γ r ∈ (R' : Subgroup SL(2, GaloisField 2 f)) := by
    intro r hr
    rw [hR', AschbacherToolkit.Bender.AutTransport.mem_map_iff'] at hr ⊢
    rw [hγapp, MulEquiv.symm_apply_apply]
    exact hαR _ hr
  have h1 := card_fix_sq_le_of_not_inner_sl2 f hf γ hγγ hγout R' hγR
  have hmem : ∀ r : (R : Subgroup X), e' r ∈ (R' : Subgroup SL(2, GaloisField 2 f)) := fun r =>
    (AschbacherToolkit.Bender.AutTransport.mem_map_iff e').mpr r.2
  let φ : {r : (R : Subgroup X) // α r = r} →
      {r : (R' : Subgroup SL(2, GaloisField 2 f)) // γ r = r} := fun r =>
    ⟨⟨e' r.1, hmem r.1⟩, by
      show γ (e' r.1) = e' r.1
      rw [hγapp, MulEquiv.symm_apply_apply, r.2]⟩
  have hφ : Function.Injective φ := by
    intro r r' h
    have h1 : e' (r.1 : X) = e' (r'.1 : X) :=
      congrArg (fun x : {r : (R' : Subgroup SL(2, GaloisField 2 f)) // γ r = r} =>
        (x.1 : SL(2, GaloisField 2 f))) h
    exact Subtype.ext (Subtype.ext (e'.injective h1))
  have hcard : Nat.card (R' : Subgroup SL(2, GaloisField 2 f)) = Nat.card (R : Subgroup X) := by
    rw [hR']
    exact Subgroup.card_map_of_injective e'.injective
  calc Nat.card {r : (R : Subgroup X) // α r = r} ^ 2
      ≤ Nat.card {r : (R' : Subgroup SL(2, GaloisField 2 f)) // γ r = r} ^ 2 :=
        Nat.pow_le_pow_left (Nat.card_le_card_of_injective φ hφ) 2
    _ ≤ Nat.card (R : Subgroup X) := hcard ▸ h1

theorem card_centralizer_sq_le_of_psl2 {G : Type} [Group G]
    [Finite G] {L : Subgroup G} (hLp : commutator L = ⊤) (hZ : Odd (Nat.card (center L)))
    {f : ℕ} (hf : 2 ≤ f) (e : RankTwoStandard.rankTwoQuot L ≃* PSL(2, GaloisField 2 f))
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 2 P L) {w : G}
    (hwN : w ∈ normalizer (L : Set G)) (hww : w * w = 1) (hwP : ∀ x ∈ P, w * x * w⁻¹ ∈ P)
    (hwLK : w ∉ L ⊔ centralizer (L : Set G)) :
    Nat.card (P ⊓ centralizer ({w} : Set G) : Subgroup G) ^ 2 ≤ Nat.card P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : L →* RankTwoStandard.rankTwoQuot L := QuotientGroup.mk' (center L) with hπ
  set n : normalizer (L : Set G) := ⟨w, hwN⟩ with hn
  set α := quotAutHom L n with hαdef
  have hαα : α * α = 1 := by
    rw [hαdef, ← map_mul]
    have : n * n = 1 := Subtype.ext hww
    rw [this, map_one]
  have hα : ¬ ∃ y, α = MulAut.conj y := by
    rintro ⟨y, hy⟩
    exact hwLK (mem_sup_centralizer_of_quotAut_mem_inner hLp hwN ⟨y, hy.symm⟩)
  obtain ⟨Q, hQ⟩ := hP.exists_sylow_eq_subgroupOf
  have hmemQ : ∀ x : L, x ∈ (Q : Subgroup L) ↔ (x : G) ∈ P := fun x => by
    rw [hQ]
    rfl
  let R : Sylow 2 (RankTwoStandard.rankTwoQuot L) :=
    Q.mapSurjective (f := π) (QuotientGroup.mk'_surjective _)
  have hR : (R : Subgroup (RankTwoStandard.rankTwoQuot L)) = (Q : Subgroup L).map π := rfl
  have hbot : (Q : Subgroup L) ⊓ center L = ⊥ :=
    AschbacherTightEmbedding.two_subgroup_of_odd_eq_bot _ (center L) Q.isPGroup'.to_inf_left hZ
      inf_le_right
  have hπinj : ∀ x ∈ (Q : Subgroup L), ∀ y ∈ (Q : Subgroup L), π x = π y → x = y := by
    intro x hx y hy hxy
    have hc : x⁻¹ * y ∈ center L := QuotientGroup.eq.mp hxy
    have h1 : x⁻¹ * y ∈ (Q : Subgroup L) ⊓ center L := mem_inf.mpr ⟨mul_mem (inv_mem hx) hy, hc⟩
    rw [hbot, mem_bot, inv_mul_eq_one] at h1
    exact h1
  have hconj : ∀ x : L, ((L.normalizerMonoidHom n x : L) : G) = w * x * w⁻¹ := fun x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L n x
  have hαR : ∀ r ∈ (R : Subgroup _), α r ∈ (R : Subgroup (RankTwoStandard.rankTwoQuot L)) := by
    intro r hr
    rw [hR] at hr ⊢
    obtain ⟨x, hx, rfl⟩ := hr
    refine ⟨L.normalizerMonoidHom n x, (hmemQ _).mpr ?_, (quotAutHom_apply_mk L n x).symm⟩
    rw [hconj]
    exact hwP _ ((hmemQ x).mp hx)
  have h1 := card_fix_sq_le_of_not_inner_psl2 hf e α hαα hα R hαR
  have hxL : ∀ x : (P ⊓ centralizer ({w} : Set G) : Subgroup G), (x : G) ∈ L := fun x =>
    hP.le x.2.1
  let xL : (P ⊓ centralizer ({w} : Set G) : Subgroup G) → L := fun x => ⟨x, hxL x⟩
  have hxQ : ∀ x, xL x ∈ (Q : Subgroup L) := fun x => (hmemQ _).mpr x.2.1
  have hxR : ∀ x, π (xL x) ∈ (R : Subgroup (RankTwoStandard.rankTwoQuot L)) := fun x => by
    rw [hR]
    exact ⟨xL x, hxQ x, rfl⟩
  have hfix : ∀ x, α (π (xL x)) = π (xL x) := by
    intro x
    rw [hπ, QuotientGroup.mk'_apply, ← QuotientGroup.mk'_apply, quotAutHom_apply_mk]
    congr 1
    apply Subtype.ext
    rw [hconj]
    have hc : w * (x : G) = x * w := (mem_centralizer_singleton_iff.mp x.2.2).symm
    show w * (x : G) * w⁻¹ = x
    rw [hc, mul_inv_cancel_right]
  let φ : (P ⊓ centralizer ({w} : Set G) : Subgroup G) →
      {r : (R : Subgroup (RankTwoStandard.rankTwoQuot L)) // α r = r} :=
    fun x => ⟨⟨π (xL x), hxR x⟩, hfix x⟩
  have hφ : Function.Injective φ := by
    intro x y hxy
    have h1 : π (xL x) = π (xL y) :=
      congrArg (fun r => ((r.1 : _) : RankTwoStandard.rankTwoQuot L)) hxy
    have h2 := hπinj _ (hxQ x) _ (hxQ y) h1
    have h3 : ((xL x : L) : G) = ((xL y : L) : G) := congrArg Subtype.val h2
    exact Subtype.ext h3
  let ψ : ↥(Q : Subgroup L) → ↥(R : Subgroup (RankTwoStandard.rankTwoQuot L)) := fun x =>
    ⟨π x, by rw [hR]; exact ⟨x, x.2, rfl⟩⟩
  have hψ : Function.Surjective ψ := by
    rintro ⟨r, hr⟩
    rw [hR] at hr
    obtain ⟨x, hx, rfl⟩ := hr
    exact ⟨⟨x, hx⟩, rfl⟩
  have hRQ := Nat.card_le_card_of_surjective ψ hψ
  have hQP : Nat.card (Q : Subgroup L) = Nat.card P := by
    rw [hQ]
    exact Nat.card_congr (subgroupOfEquivOfLe hP.le).toEquiv
  calc Nat.card (P ⊓ centralizer ({w} : Set G) : Subgroup G) ^ 2
      ≤ Nat.card {r : (R : Subgroup (RankTwoStandard.rankTwoQuot L)) // α r = r} ^ 2 :=
        Nat.pow_le_pow_left (Nat.card_le_card_of_injective φ hφ) 2
    _ ≤ Nat.card (R : Subgroup (RankTwoStandard.rankTwoQuot L)) := h1
    _ ≤ Nat.card P := hRQ.trans hQP.le

theorem sylow_elem_of_psl2 {X : Type*} [Group X] [Finite X] {f : ℕ}
    (hf : 2 ≤ f) (e : X ≃* PSL(2, GaloisField 2 f)) (R : Sylow 2 X) :
    (∀ x ∈ (R : Subgroup X), x ^ 2 = 1) ∧
      ∀ x ∈ (R : Subgroup X), ∀ y ∈ (R : Subgroup X), x * y = y * x := by
  have hB : fusionBenderBorel X (2 ^ f) 1 :=
    (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_1 f
      hf).map_mulEquiv e.symm
  obtain ⟨-, hZ2, hZcard, hRcard⟩ := benderBorel_sylowCenter hB R
  have hZR : sylowCenter (R : Subgroup X) = R :=
    Subgroup.eq_of_le_of_card_ge (sylowCenter_le _) (by rw [hZcard, hRcard, pow_one])
  have hmem : ∀ x ∈ (R : Subgroup X), x ∈ sylowCenter (R : Subgroup X) := fun x hx => by
    rw [hZR]
    exact hx
  exact ⟨fun x hx => hZ2 x (hmem x hx), fun x hx y hy => ((mem_sylowCenter.mp (hmem y hy)).2 x hx)⟩

theorem isElemAbelian_of_psl2 {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hZ : Odd (Nat.card (center L))) {f : ℕ} (hf : 2 ≤ f)
    (e : RankTwoStandard.rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 2 P L) : IsElemAbelian 2 P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : L →* RankTwoStandard.rankTwoQuot L := QuotientGroup.mk' (center L) with hπ
  obtain ⟨Q, hQ⟩ := hP.exists_sylow_eq_subgroupOf
  have hmemQ : ∀ x : L, x ∈ (Q : Subgroup L) ↔ (x : G) ∈ P := fun x => by
    rw [hQ]
    rfl
  let R : Sylow 2 (RankTwoStandard.rankTwoQuot L) :=
    Q.mapSurjective (f := π) (QuotientGroup.mk'_surjective _)
  have hR : (R : Subgroup (RankTwoStandard.rankTwoQuot L)) = (Q : Subgroup L).map π := rfl
  have hbot : (Q : Subgroup L) ⊓ center L = ⊥ :=
    AschbacherTightEmbedding.two_subgroup_of_odd_eq_bot _ (center L) Q.isPGroup'.to_inf_left hZ
      inf_le_right
  have hπinj : ∀ x ∈ (Q : Subgroup L), ∀ y ∈ (Q : Subgroup L), π x = π y → x = y := by
    intro x hx y hy hxy
    have hc : x⁻¹ * y ∈ center L := QuotientGroup.eq.mp hxy
    have h1 : x⁻¹ * y ∈ (Q : Subgroup L) ⊓ center L := mem_inf.mpr ⟨mul_mem (inv_mem hx) hy, hc⟩
    rw [hbot, mem_bot, inv_mul_eq_one] at h1
    exact h1
  obtain ⟨hsq, hcomm⟩ := sylow_elem_of_psl2 hf e R
  have hxL : ∀ x ∈ P, x ∈ L := fun x hx => hP.le hx
  have hπR : ∀ x (hx : x ∈ P), π ⟨x, hxL x hx⟩ ∈ (R : Subgroup (RankTwoStandard.rankTwoQuot L)) :=
    fun x hx => by
      rw [hR]
      exact ⟨⟨x, hxL x hx⟩, (hmemQ _).mpr hx, rfl⟩
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · have h1 := hcomm _ (hπR x.1 x.2) _ (hπR y.1 y.2)
    rw [← map_mul, ← map_mul] at h1
    have hx : (⟨x.1, hxL _ x.2⟩ : L) ∈ (Q : Subgroup L) := (hmemQ _).mpr x.2
    have hy : (⟨y.1, hxL _ y.2⟩ : L) ∈ (Q : Subgroup L) := (hmemQ _).mpr y.2
    have h2 := hπinj _ (mul_mem hx hy) _ (mul_mem hy hx) h1
    have h3 : (x.1 : G) * y.1 = y.1 * x.1 := congrArg Subtype.val h2
    exact h3
  · have h1 := hsq _ (hπR x hx)
    rw [← map_pow, ← map_one π] at h1
    have h2 := hπinj _ (pow_mem ((hmemQ ⟨x, hxL x hx⟩).mpr hx) 2) _ (one_mem _) h1
    have h3 := congrArg Subtype.val h2
    simpa using h3

end CFSG.ComponentClassification.GMS78
