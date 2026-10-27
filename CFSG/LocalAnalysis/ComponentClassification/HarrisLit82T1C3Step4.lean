module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Config

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancedLayer
open CFSG.LieType.Universal.Spin CliffordAlgebra
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem eq_of_le_of_isTwoComponentIn {J J' A : Subgroup G} (hJ : IsTwoComponentIn J A)
    (hJ' : IsTwoComponentIn J' A) (hle : J ≤ J') : J = J' := by
  obtain ⟨hJA, hJt⟩ := L219.isTwoComponentIn_iff_twoComponents.mp hJ
  obtain ⟨hJ'A, hJ't⟩ := L219.isTwoComponentIn_iff_twoComponents.mp hJ'
  have h1 := TwoComponentSubnormal.eq_of_le _ _ hJt hJ't (fun x hx => hle hx)
  rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr hJA, inf_eq_left.mpr hJ'A] at h1
  exact h1

omit [Finite G] in
theorem mk_mem_center_of_mem_center {Y : Type*} [Group Y] {N : Subgroup Y} [N.Normal] {y : Y}
    (hy : y ∈ center Y) : (QuotientGroup.mk y : Y ⧸ N) ∈ center (Y ⧸ N) := by
  rw [mem_center_iff]
  intro g
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.mp hy g]

theorem mk_ne_one_of_orderOf_two {Y : Type} [Group Y] [Finite Y] {y : Y}
    (hy : orderOf y = 2) : (QuotientGroup.mk y : Y ⧸ pPrimeCore 2 Y) ≠ 1 := fun h1 => by
  have h2 := orderOf_mk_eq_two (odd_card_pPrimeCore_two Y) hy
  rw [QuotientGroup.mk'_apply, h1, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem mem_centralizer_comm {Y : Type*} [Group Y] {x y : Y} (h : x ∈ centralizer ({y} : Set Y)) :
    y ∈ centralizer ({x} : Set Y) :=
  mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp h).symm

theorem isPGroup_zpowers_of_orderOf_two {Y : Type*} [Group Y] {y : Y} (hy : orderOf y = 2) :
    IsPGroup 2 (zpowers y) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])

section CertifiedSmall


variable {z : G} {L : Subgroup G} {p f : ℕ}

theorem C3Config.step1 (hI : C3Inputs) (h : C3Config G z L p f) {τ : G} (hτ : orderOf τ = 2)
    (hτz : τ ∈ centralizer {z}) (hτQ : τ ∈ coreActionKernel L) :
    ∃ K : Subgroup G, IsTwoComponentIn K (centralizer {τ}) ∧ centralizerResidual L τ ≤ K ∧
      ∃ hzK : z ∈ K, (QuotientGroup.mk ⟨z, hzK⟩ : Bar K) ∈ center (Bar K) := by
  have := h.simple
  obtain ⟨hJ, ⟨e⟩, -⟩ := h.pumpdown_Q hτ hτQ
  have hzJ := h.mem_pumpdown_Q hτ hτQ hτz
  set J := centralizerResidual L τ with hJdef
  have hzτ : z ∈ centralizer ({τ} : Set G) := mem_centralizer_comm hτz
  have hJ' : IsTwoComponentIn J (centralizer {τ} ⊓ centralizer {z}) :=
    inf_comm (centralizer {z}) (centralizer {τ}) ▸ hJ
  obtain ⟨K₀, hK₀, -, -, hJK⟩ := T23.exists_pumpup_of_mem h.hz hzτ hJ' hzJ
  set K := K₀.map (centralizer {τ}).subtype with hKdef
  have hKc : IsTwoComponentIn K (centralizer {τ}) := T23.isTwoComponentIn_map_subtype hK₀
  have hJKle : J ≤ K := by
    intro x hx
    have hx' : (⟨x, (hJ'.1 hx).1⟩ : ↥(centralizer ({τ} : Set G))) ∈ J.subgroupOf _ := hx
    exact ⟨⟨x, (hJ'.1 hx).1⟩, (hJK.1 hx').1, rfl⟩
  have hzK : z ∈ K := hJKle hzJ
  refine ⟨K, hKc, hJKle, hzK, ?_⟩
  by_contra hZ
  have hle : K ⊓ centralizer {z} ≤ centralizer {τ} ⊓ centralizer {z} := inf_le_inf_right _ hKc.1
  have hJK' : IsTwoComponentIn J (K ⊓ centralizer {z}) :=
    ⟨le_inf hJKle (hJ'.1.trans inf_le_right), L219.isSubnormal_subgroupOf_of_le hle hJ'.2.1,
      hJ'.2.2⟩
  have hKtop : K ≠ ⊤ := fun ht =>
    centralizer_ne_top_of_simple h.nonab hτ (top_unique (ht ▸ hKc.1))
  have hMJ : IsMTypeSchur p ↥J := isMTypeSchur_of_bar_equiv h.hM hJ.2.2 e.symm
  have hcovJ : IsCoverOf .POmegaOdd 3 p f 2 (↥J ⧸ pPrimeCore 2 ↥J) :=
    isCoverOf_of_mulEquiv e.symm h.hcov
  have hIJ : InductionTypeField p ↥J := ⟨f, one_le_of_five_le_pow h.h5, .inl hcovJ⟩
  have hch := isSimpleChevalleyOver_of_knownRow hI.known h.kProper hKtop hKc.2.2 hzK h.hz hJK'
    hzJ h.hp h.hp2 hMJ hIJ
  have hz' : orderOf (⟨z, hzK⟩ : ↥K) = 2 := by rw [Subgroup.orderOf_mk]; exact h.hz
  let eJ : ↥(J.subgroupOf K) ≃* ↥J := subgroupOfEquivOfLe hJKle
  exact false_of_lemma51e hI.l51e hKc.2.2 h.hp h.hp2 hch hz' hZ
    (isTwoComponentIn_subgroupOf_inf hzK hJK') hzJ h.h5
    (isCoverOf_of_mulEquiv (QuotientGroup.congr _ _ eJ.symm (pPrimeCore_map_iso 2 eJ.symm)) hcovJ)

end CertifiedSmall

section Certified


variable {z : G} {L : Subgroup G} {p f : ℕ}

theorem C3Config.false_of_nonSL (hI : C3Inputs) (h : C3Config G z L p f) {τ : G}
    (hτ : orderOf τ = 2) (hτz : τ ∈ centralizer {z}) (hτL : τ ∉ L) {K : Subgroup G}
    (hK : IsTwoComponentIn K (centralizer {τ})) (hτK : τ ∈ K) (eK : Bar K ≃* Bar L)
    {J : Subgroup G} (hJ : IsTwoComponentIn J (centralizer {z} ⊓ centralizer {τ}))
    (hzJ : z ∈ J) (hJL : J ≤ L) (hnsl : ¬ IsSLTwoOver (p ^ f) (↥J ⧸ pPrimeCore 2 ↥J)) :
    False := by
  have := h.simple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzτ : z ∈ centralizer ({τ} : Set G) := mem_centralizer_comm hτz
  have hJ' : IsTwoComponentIn J (centralizer {τ} ⊓ centralizer {z}) :=
    inf_comm (centralizer {z}) (centralizer {τ}) ▸ hJ
  have hcovK : IsCoverOf .POmegaOdd 3 p f 2 (Bar K) := isCoverOf_of_mulEquiv eK.symm h.hcov
  have hτ2 := isPGroup_zpowers_of_orderOf_two hτ
  have hz2 := isPGroup_zpowers_of_orderOf_two h.hz
  have hττ : τ ^ 2 ^ 1 = 1 := by rw [pow_one, ← hτ, pow_orderOf_eq_one]
  obtain ⟨Y₀, hY₀, -, -, hJY⟩ := T23.exists_pumpup_of_mem h.hz hzτ hJ' hzJ
  set Y := Y₀.map (centralizer {τ}).subtype with hYdef
  have hYc : IsTwoComponentIn Y (centralizer {τ}) := T23.isTwoComponentIn_map_subtype hY₀
  have hJY' : J ≤ Y := by
    intro x hx
    have hx' : (⟨x, (hJ'.1 hx).1⟩ : ↥(centralizer ({τ} : Set G))) ∈ J.subgroupOf _ := hx
    exact ⟨⟨x, (hJ'.1 hx).1⟩, (hJY.1 hx').1, rfl⟩
  by_cases hYK : Y = K
  · have hJK : J ≤ K := hYK ▸ hJY'
    have hzK : z ∈ K := hJK hzJ
    have hzN : z ∈ normalizer (K : Set G) := le_normalizer hzK
    by_cases hc : (QuotientGroup.mk ⟨z, hzK⟩ : Bar K) ∈ center (Bar K)
    ·
      have htriv : barAction K ⟨z, hzN⟩ = 1 := barAction_eq_one_of_mem_center (t := ⟨z, hzK⟩) hc hzN
      obtain ⟨hX, -⟩ := pumpdown hK hzN hz2 htriv
      have hτX : τ ∈ centralizerResidual K z :=
        mem_centralizerResidual_of_two_pow hzN hz2 hK.2.2.2.1 htriv hτK hτz hττ
      have hJX : J ≤ centralizerResidual K z :=
        le_perfectResidual_map (le_inf hJK (hJ.1.trans inf_le_left)) hJ.2.2.1
      have heq := eq_of_le_of_isTwoComponentIn hJ' hX hJX
      exact hτL (hJL (heq ▸ hτX))
    ·
      have hle : K ⊓ centralizer {z} ≤ centralizer {τ} ⊓ centralizer {z} :=
        inf_le_inf_right _ hK.1
      have hJK' : IsTwoComponentIn J (K ⊓ centralizer {z}) :=
        ⟨le_inf hJK (hJ.1.trans inf_le_left), L219.isSubnormal_subgroupOf_of_le hle hJ'.2.1,
          hJ.2.2⟩
      have hz' : orderOf (⟨z, hzK⟩ : ↥K) = 2 := by rw [Subgroup.orderOf_mk]; exact h.hz
      obtain ⟨hJbar, ⟨eJbar⟩⟩ :=
        isTwoComponentIn_map_bar hz' (isTwoComponentIn_subgroupOf_inf hzK hJK')
      have hτc : (⟨τ, hτK⟩ : ↥K) ∈ center ↥K := mem_center_of_le_centralizer hK.1 hτK
      have hτ' : orderOf (⟨τ, hτK⟩ : ↥K) = 2 := by rw [Subgroup.orderOf_mk]; exact hτ
      obtain ⟨-, h410t⟩ := hI.l410 (Bar K) p f h.hp h.hp2 h.h5 hcovK _
        (mk_mem_center_of_mem_center hτc) (mk_ne_one_of_orderOf_two hτ')
      obtain ⟨hc2, -, -⟩ :=
        h410t _ (orderOf_mk_eq_two (odd_card_pPrimeCore_two ↥K) hz') hc
      have hsl := (hc2 _ hJbar).1
      let eJK : ↥(J.subgroupOf K) ≃* ↥J := subgroupOfEquivOfLe hJK
      exact hnsl (isSLTwoOver_of_mulEquiv'
        ((QuotientGroup.congr _ _ eJK.symm (pPrimeCore_map_iso 2 eJK.symm)).trans eJbar).symm hsl)
  ·
    have hzQ : z ∈ coreActionKernel K := le_coreActionKernel_of_ne hYc hK hYK (hJY' hzJ)
    have hzN : z ∈ normalizer (K : Set G) := (mem_coreActionKernel.mp hzQ).1
    have htriv : barAction K ⟨z, hzN⟩ = 1 :=
      MonoidHom.mem_ker.mp ((mem_ker_barAction K ⟨z, hzN⟩).mpr hzQ)
    obtain ⟨hX, ⟨eX⟩⟩ := pumpdown hK hzN hz2 htriv
    set X := centralizerResidual K z with hXdef
    have hτX : τ ∈ X := mem_centralizerResidual_of_two_pow hzN hz2 hK.2.2.2.1 htriv hτK hτz hττ
    have hX' : IsTwoComponentIn X (centralizer {z} ⊓ centralizer {τ}) :=
      inf_comm (centralizer {τ}) (centralizer {z}) ▸ hX
    have heK : ↥X ⧸ pPrimeCore 2 ↥X ≃* Bar L := eX.trans eK
    have hcovX : IsCoverOf .POmegaOdd 3 p f 2 (↥X ⧸ pPrimeCore 2 ↥X) :=
      isCoverOf_of_mulEquiv heK.symm h.hcov
    obtain ⟨Y₁, hY₁, -, -, hXY⟩ := T23.exists_pumpup_of_mem hτ hτz hX' hτX
    set 𝒴 := Y₁.map (centralizer {z}).subtype with h𝒴def
    have h𝒴c : IsTwoComponentIn 𝒴 (centralizer {z}) := T23.isTwoComponentIn_map_subtype hY₁
    have hX𝒴 : X ≤ 𝒴 := by
      intro x hx
      have hx' : (⟨x, (hX'.1 hx).1⟩ : ↥(centralizer ({z} : Set G))) ∈ X.subgroupOf _ := hx
      exact ⟨⟨x, (hX'.1 hx).1⟩, (hXY.1 hx').1, rfl⟩
    have hτ𝒴 : τ ∈ 𝒴 := hX𝒴 hτX
    by_cases h𝒴L : 𝒴 = L
    · exact hτL (h𝒴L ▸ hτ𝒴)
    · have hτN : τ ∈ normalizer (𝒴 : Set G) := le_normalizer hτ𝒴
      by_cases hc : (QuotientGroup.mk ⟨τ, hτ𝒴⟩ : Bar 𝒴) ∈ center (Bar 𝒴)
      ·
        have htriv' : barAction 𝒴 ⟨τ, hτN⟩ = 1 :=
          barAction_eq_one_of_mem_center (t := ⟨τ, hτ𝒴⟩) hc hτN
        obtain ⟨hX'', ⟨eX''⟩⟩ := pumpdown h𝒴c hτN hτ2 htriv'
        have hXX'' : X ≤ centralizerResidual 𝒴 τ :=
          le_perfectResidual_map (le_inf hX𝒴 (hX'.1.trans inf_le_right)) hX.2.2.1
        have heq := eq_of_le_of_isTwoComponentIn hX' hX'' hXX''
        let eY : ↥X ≃* ↥(centralizerResidual 𝒴 τ) := MulEquiv.subgroupCongr heq
        exact h𝒴L (h.eq_of_isCoverOf hI h𝒴c (isCoverOf_of_mulEquiv
          ((QuotientGroup.congr _ _ eY (pPrimeCore_map_iso 2 eY)).trans eX'') hcovX))
      ·
        have h𝒴top : 𝒴 ≠ ⊤ := fun ht =>
          centralizer_ne_top_of_simple h.nonab h.hz (top_unique (ht ▸ h𝒴c.1))
        have hle : 𝒴 ⊓ centralizer {τ} ≤ centralizer {z} ⊓ centralizer {τ} :=
          inf_le_inf_right _ h𝒴c.1
        have hX𝒴' : IsTwoComponentIn X (𝒴 ⊓ centralizer {τ}) :=
          ⟨le_inf hX𝒴 (hX'.1.trans inf_le_right), L219.isSubnormal_subgroupOf_of_le hle hX'.2.1,
            hX'.2.2⟩
        have hMX := isMTypeSchur_of_bar_equiv h.hM hX.2.2 heK.symm
        have hIX : InductionTypeField p ↥X := ⟨f, one_le_of_five_le_pow h.h5, .inl hcovX⟩
        have hch := isSimpleChevalleyOver_of_knownRow hI.known h.kProper h𝒴top h𝒴c.2.2 hτ𝒴 hτ
          hX𝒴' hτX h.hp h.hp2 hMX hIX
        have hτ' : orderOf (⟨τ, hτ𝒴⟩ : ↥𝒴) = 2 := by rw [Subgroup.orderOf_mk]; exact hτ
        let eX𝒴 : ↥(X.subgroupOf 𝒴) ≃* ↥X := subgroupOfEquivOfLe hX𝒴
        exact false_of_lemma51e hI.l51e h𝒴c.2.2 h.hp h.hp2 hch hτ' hc
          (isTwoComponentIn_subgroupOf_inf hτ𝒴 hX𝒴') hτX h.h5
          (isCoverOf_of_mulEquiv (QuotientGroup.congr _ _ eX𝒴.symm (pPrimeCore_map_iso 2 eX𝒴.symm))
            hcovX)

theorem C3Config.mem_of_intrinsic (hI : C3Inputs) (h : C3Config G z L p f) {τ : G}
    (hτ : orderOf τ = 2) (hτz : τ ∈ centralizer {z}) {K : Subgroup G}
    (hK : IsTwoComponentIn K (centralizer {τ})) (hτK : τ ∈ K) (eK : Bar K ≃* Bar L) :
    τ ∈ L := by
  by_contra hτL
  have := h.simple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzτ : z ∈ centralizer ({τ} : Set G) := mem_centralizer_comm hτz
  have hcovK : IsCoverOf .POmegaOdd 3 p f 2 (Bar K) := isCoverOf_of_mulEquiv eK.symm h.hcov
  have hz2 := isPGroup_zpowers_of_orderOf_two h.hz
  have hττ : τ ^ 2 ^ 1 = 1 := by rw [pow_one, ← hτ, pow_orderOf_eq_one]
  have hτsq : τ * τ = 1 := by rw [← sq, ← hτ, pow_orderOf_eq_one]
  have hf := one_le_of_five_le_pow h.h5
  have hzH : z ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  have hLn := h.normal hI
  have hLhn : (hatIn z L).Normal := hLn.map _ (QuotientGroup.mk'_surjective _)
  obtain ⟨hcompL, -, ⟨EL⟩⟩ := hatIn_spec h.hL
  have hcovLh : IsCoverOf .POmegaOdd 3 p f 2 ↥(hatIn z L) := isCoverOf_of_mulEquiv EL h.hcov
  obtain ⟨K₁, _, _, hK₁, -, hp, hp2, ⟨e₁⟩⟩ := nonempty_mulEquiv_spinOdd h.h5 h.hcov
  let e : ↥(hatIn z L) ≃* spinGroup (quadOdd 3 K₁) := EL.symm.trans e₁
  set zh : MBar z := QuotientGroup.mk ⟨z, hzH⟩ with hzh
  have hzhL : zh ∈ hatIn z L := mk_mem_hatIn h.hzL hzH
  have hzhc : (⟨zh, hzhL⟩ : ↥(hatIn z L)) ∈ center ↥(hatIn z L) := by
    rw [mem_center_iff]
    intro g
    apply Subtype.ext
    obtain ⟨g', hg'⟩ := QuotientGroup.mk_surjective (g : MBar z)
    change (g : MBar z) * zh = zh * (g : MBar z)
    rw [← hg', hzh, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp g'.2)
  have hz' : orderOf (⟨z, hzH⟩ : ↥(centralizer ({z} : Set G))) = 2 := by
    rw [Subgroup.orderOf_mk]; exact h.hz
  have hzh1 : zh ≠ 1 := mk_ne_one_of_orderOf_two hz'
  have hzh1' : (⟨zh, hzhL⟩ : ↥(hatIn z L)) ≠ 1 := fun h1 => hzh1 (congrArg Subtype.val h1)
  set τh : MBar z := QuotientGroup.mk ⟨τ, hτz⟩ with hτh
  have hτh2 : τh * τh = 1 := by
    have h1 : (⟨τ, hτz⟩ : ↥(centralizer ({z} : Set G))) * ⟨τ, hτz⟩ = 1 := Subtype.ext hτsq
    rw [hτh, ← QuotientGroup.mk_mul, h1, QuotientGroup.mk_one]
  set α : MulAut ↥(hatIn z L) := MulAut.conjNormal τh with hα
  have hαα : α * α = 1 := by rw [hα, ← map_mul, hτh2, map_one]
  have hαapp : ∀ y : ↥(hatIn z L), ((α y : ↥(hatIn z L)) : MBar z) = τh * y * τh⁻¹ :=
    fun y => MulAut.conjNormal_apply τh y
  have hfix : (fixedSubgroup α).map (hatIn z L).subtype = hatIn z L ⊓ centralizer {τh} := by
    ext y
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine mem_inf.mpr ⟨y.2, ?_⟩
      rw [mem_centralizer_singleton_iff]
      have h1 : ((α y : ↥(hatIn z L)) : MBar z) = y :=
        congrArg Subtype.val (mem_fixedSubgroup.mp hy)
      rw [hαapp] at h1
      calc (y : MBar z) * τh = τh * y * τh⁻¹ * τh := by rw [h1]
        _ = τh * y := by group
    · rintro ⟨hyL, hyτ⟩
      refine ⟨⟨y, hyL⟩, mem_fixedSubgroup.mpr (Subtype.ext ?_), rfl⟩
      rw [hαapp]
      have h1 : y * τh = τh * y := mem_centralizer_singleton_iff.mp hyτ
      calc τh * y * τh⁻¹ = y * τh * τh⁻¹ := by rw [h1]
        _ = y := by group
  have toC : ∀ {Y : Subgroup (MBar z)}, IsTwoComponentIn Y (hatIn z L ⊓ centralizer {τh}) →
      IsTwoComponentIn Y (centralizer {τh}) := fun hY => by
    have h1 := isTwoComponentIn_inf_of_subnormal (le_top : hatIn z L ≤ ⊤) hcompL.1.subgroupOf
      (centralizer {τh}) hY
    rwa [top_inf_eq] at h1
  rcases hI.u1 ↥(hatIn z L) p f h.hp h.hp2 h.h5 hcovLh ⟨zh, hzhL⟩ hzhc hzh1' α hαα with
    ⟨x, hx2, hxZ, hαx⟩ | ⟨J', hJ', hzJ', hnsl'⟩
  ·
    have hx1 : x ≠ 1 := fun h1 => hxZ (h1 ▸ one_mem _)
    have hxo : orderOf (x : MBar z) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_eq_prime (by rw [sq, hx2]) hx1
    have hαx' : ∀ y : ↥(hatIn z L), ((α y : ↥(hatIn z L)) : MBar z) =
        (x : MBar z) * y * (x : MBar z)⁻¹ := fun y => by rw [hαx]; rfl
    have hCC : hatIn z L ⊓ centralizer {(x : MBar z)} = hatIn z L ⊓ centralizer {τh} := by
      ext y
      constructor
      · rintro ⟨hyL, hyx⟩
        refine mem_inf.mpr ⟨hyL, ?_⟩
        have h1 := hαx' ⟨y, hyL⟩
        rw [hαapp] at h1
        have hyx' : y * (x : MBar z) = (x : MBar z) * y := mem_centralizer_singleton_iff.mp hyx
        have h2 : τh * y * τh⁻¹ = y := by rw [h1, ← hyx', mul_inv_cancel_right]
        rw [mem_centralizer_singleton_iff]
        calc y * τh = τh * y * τh⁻¹ * τh := by rw [h2]
          _ = τh * y := by group
      · rintro ⟨hyL, hyτ⟩
        refine mem_inf.mpr ⟨hyL, ?_⟩
        have h1 := hαx' ⟨y, hyL⟩
        rw [hαapp] at h1
        have hyτ' : y * τh = τh * y := mem_centralizer_singleton_iff.mp hyτ
        have h2 : (x : MBar z) * y * (x : MBar z)⁻¹ = y := by
          rw [← h1, ← hyτ', mul_inv_cancel_right]
        rw [mem_centralizer_singleton_iff]
        calc y * (x : MBar z) = (x : MBar z) * y * (x : MBar z)⁻¹ * (x : MBar z) := by rw [h2]
          _ = (x : MBar z) * y := by group
    obtain ⟨Y₁, -, -, ⟨hY₁, -, hs₁, hzY₁⟩, -, -⟩ :=
      spinSeven_three_in hp hp2 hK₁ h.h5 e x.2 hxo hxZ hzhL hzhc hzh1
    have hY₁' := toC (hCC ▸ hY₁)
    obtain ⟨J, hJ, hmem, -, ⟨eJ⟩⟩ := lift_twoComponent hτz hτ hY₁'
    have hzJ : z ∈ J := hmem z hzH hzτ ⟨1, by rw [pow_one]; exact h.hz⟩ hzY₁
    have hslJ := isSLTwoOver_quot_of_equiv hp hp2 hf h.h5 eJ hs₁
    have hne : z ≠ τ := fun he => hτL (he ▸ h.hzL)
    have hzτc : z * τ = τ * z := mem_centralizer_singleton_iff.mp hzτ
    by_cases hzQK : z ∈ coreActionKernel K
    ·
      have hzN : z ∈ normalizer (K : Set G) := (mem_coreActionKernel.mp hzQK).1
      have htriv : barAction K ⟨z, hzN⟩ = 1 :=
        MonoidHom.mem_ker.mp ((mem_ker_barAction K ⟨z, hzN⟩).mpr hzQK)
      obtain ⟨hX, ⟨eX⟩⟩ := pumpdown hK hzN hz2 htriv
      have hτX := mem_centralizerResidual_of_two_pow hzN hz2 hK.2.2.2.1 htriv hτK hτz hττ
      have hX' : IsTwoComponentIn (centralizerResidual K z) (centralizer {z} ⊓ centralizer {τ}) :=
        inf_comm (centralizer {τ}) (centralizer {z}) ▸ hX
      exact false_of_fourGroup hI h.nonab h.kProper h.notCat h.hz hτ hne hzτc hJ hX' hzJ hτX
        h.hp h.hp2 h.h5 hslJ h.h5 (isMTypeSchur_of_bar_equiv h.hM hX.2.2 (eX.trans eK).symm)
        (isCoverOf_of_mulEquiv (eX.trans eK).symm h.hcov)
    ·
      have hJ' : IsTwoComponentIn J (centralizer {τ} ⊓ centralizer {z}) :=
        inf_comm (centralizer {z}) (centralizer {τ}) ▸ hJ
      rcases lemma221 h.hz hzτ hJ' hzJ hK with hJK | hJK
      · have hzK : z ∈ K := hJK hzJ
        have hzZ : (QuotientGroup.mk (⟨z, hzK⟩ : ↥K) : Bar K) ∉ center (Bar K) := fun hc =>
          hzQK ((mem_ker_barAction K ⟨z, le_normalizer hzK⟩).mp (MonoidHom.mem_ker.mpr
            (barAction_eq_one_of_mem_center (t := ⟨z, hzK⟩) hc (le_normalizer hzK))))
        obtain ⟨J₁, -, -, ⟨hJ₁, -, -, hsl₁, hτJ₁⟩, -, -⟩ :=
          spinSeven_lift_three h.h5 hK hτK hτ hcovK hzK h.hz hzZ
        exact h.false_of_slTwo hI hτ hτz hτL (inf_comm (centralizer {τ}) (centralizer {z}) ▸ hJ₁)
          hτJ₁ h.h5 hsl₁
      · exact hzQK (hJK hzJ)
  ·
    have hJh : IsTwoComponentIn (J'.map (hatIn z L).subtype) (hatIn z L ⊓ centralizer {τh}) := by
      have h1 := L35.isTwoComponentIn_map_of_injective (hatIn z L).subtype
        (hatIn z L).subtype_injective hJ'
      rwa [hfix] at h1
    obtain ⟨J, hJ, hmem, hgen, ⟨eJ⟩⟩ := lift_twoComponent hτz hτ (toC hJh)
    have hzJ : z ∈ J := hmem z hzH hzτ ⟨1, by rw [pow_one]; exact h.hz⟩ ⟨_, hzJ', rfl⟩
    have hJL : J ≤ L := lift_le_of_le_hatIn h.hL (map_subtype_le J') hgen
    have hnsl : ¬ IsSLTwoOver (p ^ f) (↥J ⧸ pPrimeCore 2 ↥J) := fun hsl => hnsl' (by
      let eJ' : ↥J' ≃* ↥(J'.map (hatIn z L).subtype) :=
        J'.equivMapOfInjective (hatIn z L).subtype (hatIn z L).subtype_injective
      exact isSLTwoOver_of_mulEquiv'
        (eJ.trans (QuotientGroup.congr _ _ eJ'.symm (pPrimeCore_map_iso 2 eJ'.symm))) hsl)
    exact h.false_of_nonSL hI hτ hτz hτL hK hτK eK hJ hzJ hJL hnsl

theorem C3Config.conj_mem (hI : C3Inputs) (h : C3Config G z L p f) (g : G)
    (hg : g * z * g⁻¹ ∈ centralizer {z}) : g * z * g⁻¹ ∈ L := by
  have hmap : (centralizer ({z} : Set G)).map (MulAut.conj g).toMonoidHom =
      centralizer {g * z * g⁻¹} := by
    rw [map_centralizer_singleton_mulEquiv, MulAut.conj_apply]
  have hK : IsTwoComponentIn (L.map (MulAut.conj g).toMonoidHom) (centralizer {g * z * g⁻¹}) :=
    hmap ▸ L35.isTwoComponentIn_map_of_injective _ (MulAut.conj g).injective h.hL
  let eg : ↥L ≃* ↥(L.map (MulAut.conj g).toMonoidHom) :=
    L.equivMapOfInjective _ (MulAut.conj g).injective
  have hτ : orderOf (g * z * g⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]; exact h.hz
  exact h.mem_of_intrinsic hI hτ hg hK ⟨z, h.hzL, rfl⟩
    (QuotientGroup.congr _ _ eg (pPrimeCore_map_iso 2 eg)).symm

end Certified

variable {z : G} {L : Subgroup G} {p f : ℕ}

theorem C3Config.eq_of_mk_mem_center (h : C3Config G z L p f) {u : G} (huL : u ∈ L)
    (hu : orderOf u = 2) (huZ : (QuotientGroup.mk (⟨u, huL⟩ : ↥L) : Bar L) ∈ center (Bar L)) :
    u = z := by
  have hOodd := odd_card_pPrimeCore_two ↥L
  have hzc := mem_center_of_le_centralizer h.hL.1 h.hzL
  have hz' : orderOf (⟨z, h.hzL⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk]; exact h.hz
  have hu' : orderOf (⟨u, huL⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk]; exact hu
  have hZ2 : Nat.card ↥(center (Bar L)) = 2 := h.hcov.2.1
  have heq := T23.eq_of_ne_one_of_card_two hZ2 (a := ⟨_, huZ⟩)
    (b := ⟨_, mk_mem_center_of_mem_center hzc⟩)
    (fun h1 => mk_ne_one_of_orderOf_two hu' (congrArg Subtype.val h1))
    (fun h1 => mk_ne_one_of_orderOf_two hz' (congrArg Subtype.val h1))
  have heq' : (QuotientGroup.mk (⟨u, huL⟩ : ↥L) : Bar L) = QuotientGroup.mk ⟨z, h.hzL⟩ :=
    congrArg Subtype.val heq
  rw [QuotientGroup.eq] at heq'
  have huu : (⟨u, huL⟩ : ↥L) * ⟨u, huL⟩ = 1 := by rw [← sq, ← hu', pow_orderOf_eq_one]
  have hzz : (⟨z, h.hzL⟩ : ↥L) * ⟨z, h.hzL⟩ = 1 := by rw [← sq, ← hz', pow_orderOf_eq_one]
  obtain ⟨c, -, hc⟩ := exists_conj_of_inv_mul_mem hOodd huu hzz heq'
  have h1 : (⟨u, huL⟩ : ↥L) = ⟨z, h.hzL⟩ := by
    calc (⟨u, huL⟩ : ↥L) = c⁻¹ * (c * ⟨u, huL⟩ * c⁻¹) * c := by group
      _ = c⁻¹ * ⟨z, h.hzL⟩ * c := by rw [hc]
      _ = ⟨z, h.hzL⟩ := by rw [mul_assoc, ← mem_center_iff.mp hzc c, inv_mul_cancel_left]
  exact congrArg Subtype.val h1

theorem C3Config.exists_conj_ne (h : C3Config G z L p f) :
    ∃ g : G, g * z * g⁻¹ ∈ centralizer {z} ∧ g * z * g⁻¹ ≠ z := by
  have := h.simple
  by_contra hcon
  push Not at hcon
  have := Fintype.ofFinite G
  have hz1 : z ≠ 1 := fun h1 => by
    have h2 := h.hz
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hzz : z * z = 1 := by rw [← sq, ← h.hz, pow_orderOf_eq_one]
  obtain ⟨N, hN, hNodd, hNz⟩ := ZStar.glauberman_zStar G z hz1 hzz
    (fun g hg => hcon g (mem_centralizer_singleton_iff.mpr hg))
  have hNbot : N = ⊥ := by
    have := hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h1 | h1
    · exact h1
    · exfalso
      have hzN : z ∈ N := h1 ▸ mem_top z
      have hdvd := orderOf_dvd_natCard (⟨z, hzN⟩ : N)
      rw [Subgroup.orderOf_mk, h.hz] at hdvd
      exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr hdvd)
  have hZ : center G = ⊥ := CatLeaf.center_eq_bot_of_simple h.nonab
  have hzc : z ∈ center G := by
    rw [mem_center_iff]
    intro g
    have h1 := hNz g
    rw [hNbot, mem_bot] at h1
    calc g * z = g * z * g⁻¹ * z⁻¹ * (z * g) := by group
      _ = z * g := by rw [h1, one_mul]
  rw [hZ, mem_bot] at hzc
  exact hz1 hzc

section Certified


theorem C3Config.exists_conj (hI : C3Inputs) (h : C3Config G z L p f) {u : G} (huL : u ∈ L)
    (hu : orderOf u = 2) : ∃ g : G, g * z * g⁻¹ = u := by
  by_cases huZ : (QuotientGroup.mk (⟨u, huL⟩ : ↥L) : Bar L) ∈ center (Bar L)
  · exact ⟨1, by rw [h.eq_of_mk_mem_center huL hu huZ]; group⟩
  · obtain ⟨g₀, hg₀C, hg₀ne⟩ := h.exists_conj_ne
    have hvL := h.conj_mem hI g₀ hg₀C
    have hv : orderOf (g₀ * z * g₀⁻¹) = 2 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]; exact h.hz
    have hvZ : (QuotientGroup.mk (⟨_, hvL⟩ : ↥L) : Bar L) ∉ center (Bar L) := fun hc =>
      hg₀ne (h.eq_of_mk_mem_center hvL hv hc)
    obtain ⟨x, -, hx⟩ := spinSeven_conj_of_involution h.h5 h.hcov hvL huL hv hu hvZ huZ
    exact ⟨x * g₀, by rw [← hx]; group⟩

theorem C3Config.conj_iff (hI : C3Inputs) (h : C3Config G z L p f) {x : G}
    (hx : x ∈ centralizer ({z} : Set G)) :
    (∃ g : G, g * z * g⁻¹ = x) ↔ (x ∈ L ∧ orderOf x = 2) := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨h.conj_mem hI g hx, by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]; exact h.hz⟩
  · rintro ⟨hxL, hx2⟩
    exact h.exists_conj hI hxL hx2

end Certified

end CFSG.ComponentClassification.HarrisLit.T1
