module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyP2Field
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyP2Square
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyP2Embedded
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyOddClassical
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2NormalExtension
public import CFSG.Adapters.QiuzhenLegacy.GorensteinWalter.PGammaL2ProjectiveHilbert90

public section

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG CFSG.GorensteinWalter CFSG.QuasithinUnique.Setup.X3 CFSG.SectionRank.OddCover
  CFSG.LocalAnalysis.ComponentInitial CFSG.Quasithin CFSG.Assembly.LowTwoRank Module

section FieldPart

variable {p : ℕ} [hpf : Fact p.Prime] {K : Type} [Field K] [Fintype K] [CharP K p]

theorem exists_pow_ne_self (hK : Fintype.card K = p ^ 2) : ∃ x : K, x ^ p ≠ x := by
  by_contra hall
  push Not at hall
  have hbot : ∀ y : K, y ∈ (⊥ : Subfield K) := fun y =>
    (Subfield.mem_bot_iff_pow_eq_self K p).2 (hall y)
  have h1 : Nat.card (⊥ : Subfield K) = Nat.card K :=
    Nat.card_congr (Equiv.subtypeUnivEquiv hbot)
  rw [Subfield.card_bot K p, Nat.card_eq_fintype_card, hK] at h1
  have h2 := hpf.out.one_lt
  nlinarith

theorem ringAut_eq_frob (hK : Fintype.card K = p ^ 2) {σ : K ≃+* K} (hσ : σ ≠ 1) (a : K) :
    σ a = a ^ p := by
  have hcard : Nat.card (K ≃+* K) = 2 :=
    (card_ringAut_and_isCyclic hpf.out K (by rw [Nat.card_eq_fintype_card, hK])).1
  let F : K ≃+* K := RingEquiv.ofBijective (frobenius K p)
    (Finite.injective_iff_bijective.1 (frobenius_inj K p))
  have hF : F ≠ 1 := by
    intro h
    obtain ⟨x, hx⟩ := exists_pow_ne_self hK
    apply hx
    exact DFunLike.congr_fun h x
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : K ≃+* K)).1 hcard
  have hσF : σ = F := (huniq σ hσ).trans (huniq F hF).symm
  rw [hσF]
  rfl

end FieldPart

section Gamma

variable {K : Type} [Field K] {Hg : Type*} [Group Hg]

@[expose] def linPart (j : Hg →* PGammaL2 K) : Subgroup Hg :=
  (SemidirectProduct.rightHom.comp j).ker

@[expose] def linMap (j : Hg →* PGammaL2 K) : linPart j →* PGL2 K where
  toFun h := (j h.1).left
  map_one' := by simp
  map_mul' a b := by
    have ha : (j a.1).right = 1 := a.2
    simp [SemidirectProduct.mul_left, ha]

theorem j_eq_inl (j : Hg →* PGammaL2 K) (h : linPart j) :
    j h.1 = SemidirectProduct.inl (linMap j h) := by
  have h1 := SemidirectProduct.inl_left_mul_inr_right (j h.1)
  have h2 : (j h.1).right = 1 := h.2
  rw [h2, map_one, mul_one] at h1
  exact h1.symm

theorem linMap_injective {j : Hg →* PGammaL2 K} (hj : Function.Injective j) :
    Function.Injective (linMap j) := by
  intro a b hab
  apply Subtype.ext
  apply hj
  rw [j_eq_inl j a, j_eq_inl j b, hab]

theorem card_le_eight
    [Finite K] (hK : ringChar K ≠ 2) (hcard : Nat.card (K ≃+* K) = 2)
    {j : Hg →* PGammaL2 K} (hj : Function.Injective j) {B : Subgroup Hg}
    (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hB2 : ∀ a ∈ B, a * a = 1) :
    Nat.card B ≤ 8 := by
  let φ : ↥B →* (K ≃+* K) := SemidirectProduct.rightHom.comp (j.comp B.subtype)
  have h1 : Nat.card φ.ker * Nat.card φ.range = Nat.card B := Subgroup.card_ker_mul_card_range φ
  have h2 : Nat.card φ.range ≤ 2 := by
    have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
    rw [← hcard]
    exact Subgroup.card_le_card_group _
  let ψ : φ.ker →* ↥(linPart j) :=
    ((B.subtype).comp φ.ker.subtype).codRestrict (linPart j) (fun x => x.2)
  let δ : φ.ker →* PGL2 K := (linMap j).comp ψ
  have hδ : Function.Injective δ := by
    intro x y hxy
    have h3 : ψ x = ψ y := linMap_injective hj hxy
    have h4 : ((ψ x : linPart j) : Hg) = ((ψ y : linPart j) : Hg) := congrArg Subtype.val h3
    exact Subtype.ext (Subtype.ext h4)
  have h3 : Nat.card φ.ker ≤ 4 := by
    have hel : CFSG.IsElementaryAbelian 2 δ.range := by
      refine isElementaryAbelian_two_of ?_ ?_
      · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (Subtype.ext (hBc _ x.1.2 _ y.1.2))
      · rintro _ ⟨x, rfl⟩
        rw [← map_mul]
        have : x * x = 1 := Subtype.ext (Subtype.ext (hB2 _ x.1.2))
        rw [this, map_one]
    calc Nat.card φ.ker = Nat.card δ.range := Nat.card_congr (MonoidHom.ofInjective hδ).toEquiv
      _ ≤ 4 := card_le_four_of_elementaryAbelian hK δ.range
  calc Nat.card B = Nat.card φ.ker * Nat.card φ.range := h1.symm
    _ ≤ 4 * 2 := Nat.mul_le_mul h3 h2

end Gamma

section Field

variable {p : ℕ} [hpf : Fact p.Prime] {K : Type} [Field K] [Fintype K] [CharP K p]

omit [Fintype K] in
theorem psl2FieldAut_pslU (σ : K ≃+* K) (a : K) :
    psl2FieldAut K σ (pslU (Multiplicative.ofAdd a)) = pslU (Multiplicative.ofAdd (σ a)) := by
  rw [pslU_apply, pslU_apply, toAdd_ofAdd, toAdd_ofAdd]
  show psl2RingEquiv σ (QuotientGroup.mk' (Subgroup.center _) (slU a)) = _
  rw [psl2RingEquiv_mk]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_slU]

theorem field_involution_rank (hp5 : 5 ≤ p) (hK : Fintype.card K = p ^ 2) {E : Type*}
    [AddCommGroup E] [Module (ZMod 2) E] [Module.Finite (ZMod 2) E] {Hg : Type*} [Group Hg]
    (ρ : Hg →* (E ≃ₗ[ZMod 2] E)) (hρ : Function.Injective ρ) (j : Hg →* PGammaL2 K)
    (hj : Function.Injective j) (ι : PSL2 K →* Hg)
    (hjι : ∀ y, j (ι y) = SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL y))
    {t : Hg} {σ : K ≃+* K} (hσ : σ ≠ 1) (hjt : j t = SemidirectProduct.inr σ) :
    4 ≤ finrank (ZMod 2) (LinearMap.range (disp ρ t)) := by
  have hσp : ∀ a, σ a = a ^ p := ringAut_eq_frob hK hσ
  let U : Multiplicative K →* (E ≃ₗ[ZMod 2] E) := ρ.comp (ι.comp pslU)
  have hU1 : ∀ a : K, a ≠ 0 → U (Multiplicative.ofAdd a) ≠ 1 := by
    intro a ha h
    have h1 : ι (pslU (Multiplicative.ofAdd a)) = 1 := hρ (by rw [map_one]; exact h)
    have h2 : Matrix.ProjectiveSpecialLinearGroup.toPGL (pslU (Multiplicative.ofAdd a)) = 1 := by
      have h3 := hjι (pslU (Multiplicative.ofAdd a))
      rw [h1, map_one] at h3
      exact SemidirectProduct.inl_injective (h3.symm.trans (map_one _).symm)
    have h3 : pslU (Multiplicative.ofAdd a) = 1 :=
      Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (by rw [h2, map_one])
    have h4 : Multiplicative.ofAdd a = 1 := pslU_injective (by rw [h3, map_one])
    exact ha (ofAdd_eq_one.1 h4)
  have hT : ∀ c : K, c ≠ 0 → ∃ T : E ≃ₗ[ZMod 2] E, ∀ a : K,
      T * U (Multiplicative.ofAdd a) * T⁻¹ = U (Multiplicative.ofAdd (c ^ 2 * a)) := by
    intro c hc
    refine ⟨ρ (ι (pslMk (slD (Units.mk0 c hc)))), fun a => ?_⟩
    have h2 := pslD_conj_pslU (K := K) (Units.mk0 c hc) a
    have h3 := congrArg (fun z => ρ (ι z)) h2
    simpa [U, map_mul, map_inv] using h3
  have hτ : ∀ a : K, ρ t * U (Multiplicative.ofAdd a) * (ρ t)⁻¹ =
      U (Multiplicative.ofAdd (a ^ p)) := by
    intro a
    have key : t * ι (pslU (Multiplicative.ofAdd a)) * t⁻¹ =
        ι (pslU (Multiplicative.ofAdd (a ^ p))) := by
      apply hj
      rw [map_mul, map_mul, map_inv, hjt, hjι, hjι, ← map_inv SemidirectProduct.inr,
        ← SemidirectProduct.inl_aut]
      congr 1
      rw [← psl2FieldAut_toPGL σ (pslU (Multiplicative.ofAdd a)), psl2FieldAut_pslU, hσp]
    have h3 := congrArg ρ key
    simpa [U, map_mul, map_inv] using h3
  exact rank_ge_four hK U hp5 hU1 hT hτ

end Field

section Offender

variable {p : ℕ} [hpf : Fact p.Prime] {K : Type} [Field K] [Fintype K] [CharP K p]

omit [Field K] [CharP K p] in
theorem isOddPrimePower_sq (hp5 : 5 ≤ p) (hK : Fintype.card K = p ^ 2) :
    IsOddPrimePower (Nat.card K) :=
  ⟨p, 2, hpf.out, hpf.out.odd_of_ne_two (by omega), by norm_num,
    by rw [Nat.card_eq_fintype_card, hK]⟩

omit hpf [Field K] [CharP K p] in
theorem three_lt_card_sq (hp5 : 5 ≤ p) (hK : Fintype.card K = p ^ 2) : 3 < Nat.card K := by
  rw [Nat.card_eq_fintype_card, hK]
  nlinarith

omit hpf [Fintype K] in
theorem ringChar_ne_two_sq (hp5 : 5 ≤ p) : ringChar K ≠ 2 := by
  rw [ringChar.eq K p]
  omega

theorem no_offender_gamma
    (hp5 : 5 ≤ p) (hK : Fintype.card K = p ^ 2) {E : Type*}
    [AddCommGroup E] [Module (ZMod 2) E] [Module.Finite (ZMod 2) E] {Hg : Type*} [Group Hg]
    (ρ : Hg →* (E ≃ₗ[ZMod 2] E)) (hρ : Function.Injective ρ) (j : Hg →* PGammaL2 K)
    (hj : Function.Injective j) (ι : PSL2 K →* Hg)
    (hjι : ∀ y, j (ι y) = SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL y))
    {B : Subgroup Hg} (hB1 : B ≠ ⊥) (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hB2 : ∀ a ∈ B, a * a = 1)
    (hoff : finrank (ZMod 2) E - finrank (ZMod 2) (fixedSub ρ B) ≤ Nat.log 2 (Nat.card B)) :
    False := by
  have hoddpp := isOddPrimePower_sq hp5 hK
  have hcard3 := three_lt_card_sq hp5 hK
  have hch : ringChar K ≠ 2 := ringChar_ne_two_sq (K := K) (p := p) hp5
  have hcardAut : Nat.card (K ≃+* K) = 2 :=
    (card_ringAut_and_isCyclic hpf.out K (by rw [Nat.card_eq_fintype_card, hK])).1
  have hι : Function.Injective ι := by
    intro y z hyz
    have h1 := hjι y
    rw [hyz, hjι z] at h1
    exact Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
      (SemidirectProduct.inl_injective h1.symm)
  by_cases hfield : ∃ t ∈ B, (j t).right ≠ 1
  · obtain ⟨t, htB, htf⟩ := hfield
    have ht2 : t * t = 1 := hB2 t htB
    have ht1 : t ≠ 1 := by
      rintro rfl
      exact htf (by simp)
    have hord : orderOf (j t) = 2 := by
      rw [orderOf_injective j hj t]
      exact orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1
    obtain ⟨C, hC⟩ := pGammaL2_involution_conj_inr hoddpp (j t) hord htf
    let j' : Hg →* PGammaL2 K :=
      (MulAut.conj ((SemidirectProduct.inl C)⁻¹ : PGammaL2 K)).toMonoidHom.comp j
    let ι' : PSL2 K →* Hg := ι.comp (pgl2InnerAutPSL2 K hoddpp hcard3 C).toMonoidHom
    have hj' : Function.Injective j' := (MulAut.conj _).injective.comp hj
    have hjι' : ∀ y, j' (ι' y) =
        SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL y) := by
      intro y
      show (SemidirectProduct.inl C)⁻¹ * j (ι (pgl2InnerAutPSL2 K hoddpp hcard3 C y)) *
        ((SemidirectProduct.inl C)⁻¹)⁻¹ = _
      rw [hjι, toPGL_pgl2InnerAutPSL2_apply]
      simp only [map_mul, map_inv, inv_inv]
      group
    have hjt' : j' t = SemidirectProduct.inr (j t).right := by
      show (SemidirectProduct.inl C)⁻¹ * j t * ((SemidirectProduct.inl C)⁻¹)⁻¹ = _
      rw [inv_inv]
      exact hC
    have h4 := field_involution_rank hp5 hK ρ hρ j' hj' ι' hjι' htf hjt'
    have hB8 : Nat.card B ≤ 8 := card_le_eight hch hcardAut hj hBc hB2
    have hlog : Nat.log 2 (Nat.card B) ≤ 3 :=
      (Nat.log_mono_right hB8).trans (by norm_num)
    have h5 := finrank_range_disp_le_of_offender ρ htB (hoff.trans hlog)
    omega
  · push Not at hfield
    have hBle : B ≤ linPart j := fun t ht => hfield t ht
    refine no_offender_of_inner_rank hch (linMap j) (linMap_injective hj) ?_
      (ρ.comp (linPart j).subtype) ?_ (B := B.subgroupOf (linPart j)) ?_ ?_ ?_ ?_
    · rintro _ ⟨y, rfl⟩
      have hmem : ι y ∈ linPart j := by
        show (j (ι y)).right = 1
        rw [hjι]
        rfl
      refine ⟨⟨ι y, hmem⟩, ?_⟩
      show (j (ι y)).left = _
      rw [hjι]
      rfl
    · intro a haS ha1 ha2
      obtain ⟨y, hy⟩ := haS
      have hia : ι y = a.1 := by
        apply hj
        rw [hjι, j_eq_inl j a, hy]
      have hy1 : y ≠ 1 := by
        rintro rfl
        apply ha1
        apply Subtype.ext
        rw [← hia, map_one]
        rfl
      have hy2 : y * y = 1 := by
        apply hι
        rw [map_mul, map_one, hia]
        exact congrArg Subtype.val ha2
      have h3 := psl2_square_inner_involution_rank hp5 (by rw [Nat.card_eq_fintype_card, hK])
        (ρ.comp ι) (hρ.comp hι) hy1 hy2
      have h4 : disp (ρ.comp ι) y = disp (ρ.comp (linPart j).subtype) a := by
        show disp ρ (ι y) = disp ρ a.1
        rw [hia]
      rwa [h4] at h3
    · obtain ⟨b, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB1
      refine Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨⟨b, hBle b.2⟩, b.2⟩, fun h => hb1 ?_⟩
      exact Subtype.ext (congrArg (fun x : ↥(B.subgroupOf (linPart j)) => ((x : linPart j) : Hg)) h)
    · intro a ha b hb
      exact Subtype.ext (hBc _ ha _ hb)
    · intro a ha
      apply Subtype.ext
      exact hB2 _ ha
    · have hfix : fixedSub (ρ.comp (linPart j).subtype) (B.subgroupOf (linPart j)) =
          fixedSub ρ B := by
        ext x
        rw [mem_fixedSub, mem_fixedSub]
        constructor
        · intro h a ha
          exact h ⟨a, hBle ha⟩ ha
        · intro h a ha
          exact h a.1 ha
      have hcardB : Nat.card (B.subgroupOf (linPart j)) = Nat.card B :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBle).toEquiv
      rw [hfix, hcardB]
      exact hoff

end Offender

section Final

theorem normalPSL2ToPGammaL2_apply {R : Type} [Group R] (N : Subgroup R) [N.Normal] (K : Type)
    [Field K] [Finite K] (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (e : N ≃* PSL2 K) (hsurj : Function.Surjective (pGammaL2ToMulAutPSL2 K hK hcard))
    (y : PSL2 K) :
    normalPSL2ToPGammaL2 N K hK hcard e hsurj ((e.symm y : N) : R) =
      SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL y) := by
  apply (pGammaL2EquivMulAutPSL2 K hK hcard hsurj).injective
  simp only [normalPSL2ToPGammaL2, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply]
  change normalPSL2ConjAction N K e ((e.symm y : N) : R) =
    pGammaL2ToMulAutPSL2 K hK hcard
      (SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL y))
  rw [pGammaL2ToMulAutPSL2_inl, pgl2InnerAutPSL2_toPGL]
  change MulAut.congr e (MulAut.conjNormal ((e.symm y : N) : R)) = MulAut.conj y
  rw [MulAut.conjNormal_val]
  have hconj : MulAut.congr e (MulAut.conj (e.symm y)) = MulAut.conj y := by
    ext x
    simp [MulAut.congr, MulAut.conj_apply]
  exact hconj

theorem centralizer_trivial {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {L A : Subgroup (MulAut W)}
    (hL : ∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hcenter : Subgroup.center ↥L = ⊥) (hA : A ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hA2 : IsElemAbelian2 A) :
    ∀ z : ↥(L ⊔ A), (∀ n ∈ L.subgroupOf (L ⊔ A), z * n = n * z) → z = 1 := by
  intro z hz
  obtain ⟨l, hl, a, ha, hzla⟩ := mem_sup_of_le_normalizer hA z.2
  have hzc : ∀ y ∈ L, (z : MulAut W) * y = y * (z : MulAut W) := by
    intro y hy
    have hyN : (⟨y, Subgroup.mem_sup_left hy⟩ : ↥(L ⊔ A)) ∈ L.subgroupOf (L ⊔ A) := hy
    exact congrArg Subtype.val (hz _ hyN)
  have ha2 : a * a = 1 := by
    have := hA2.2 a ha
    rwa [pow_two] at this
  have hzl : (z : MulAut W) * l⁻¹ = l⁻¹ * (z : MulAut W) := hzc _ (L.inv_mem hl)
  have hal : a = l⁻¹ * (z : MulAut W) := by rw [hzla]; group
  have hkey : (l⁻¹ * (z : MulAut W)) * (l⁻¹ * (z : MulAut W)) =
      l⁻¹ * l⁻¹ * ((z : MulAut W) * (z : MulAut W)) := by
    calc (l⁻¹ * (z : MulAut W)) * (l⁻¹ * (z : MulAut W))
        = l⁻¹ * ((z : MulAut W) * l⁻¹) * (z : MulAut W) := by group
      _ = l⁻¹ * (l⁻¹ * (z : MulAut W)) * (z : MulAut W) := by rw [hzl]
      _ = l⁻¹ * l⁻¹ * ((z : MulAut W) * (z : MulAut W)) := by group
  have hzz : (z : MulAut W) * (z : MulAut W) = l * l := by
    rw [← hal, ha2] at hkey
    have := eq_inv_of_mul_eq_one_right hkey.symm
    simpa using this
  have hzzL : (z : MulAut W) * (z : MulAut W) ∈ L := by rw [hzz]; exact L.mul_mem hl hl
  have hzz1 : (z : MulAut W) * (z : MulAut W) = 1 := by
    have hcen : (⟨(z : MulAut W) * (z : MulAut W), hzzL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      show (y : MulAut W) * ((z : MulAut W) * (z : MulAut W)) =
        ((z : MulAut W) * (z : MulAut W)) * (y : MulAut W)
      have hy := hzc y y.2
      calc (y : MulAut W) * ((z : MulAut W) * (z : MulAut W))
          = ((y : MulAut W) * (z : MulAut W)) * (z : MulAut W) := by rw [mul_assoc]
        _ = ((z : MulAut W) * (y : MulAut W)) * (z : MulAut W) := by rw [← hy]
        _ = (z : MulAut W) * ((y : MulAut W) * (z : MulAut W)) := by rw [mul_assoc]
        _ = (z : MulAut W) * ((z : MulAut W) * (y : MulAut W)) := by rw [← hy]
        _ = ((z : MulAut W) * (z : MulAut W)) * (y : MulAut W) := by rw [mul_assoc]
    rw [hcenter, Subgroup.mem_bot] at hcen
    exact congrArg Subtype.val hcen
  have hz1 : (z : MulAut W) = 1 :=
    eq_one_of_centralizes_irreducible hW hL (fun l hl => (hzc l hl)) hzz1
  exact Subtype.ext hz1

theorem primeSquareExclusion
    : PrimeSquareExclusionProp := by
  intro p hp hp5 W _ _ hW Lb hperf hirr hmod A hAN hA1 hA2
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (∀ w : W, w * w = 1) := ⟨hW⟩
  have : Nontrivial W := hirr.1
  have hp2 : p ≠ 2 := by omega
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have := hperf
  have hodd := odd_card_center_of_irreducible hW hirr.2
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
  have : Fintype K := Fintype.ofFinite K
  have hKcard : Fintype.card K = p ^ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  have : CharP K p := charP_of_card_eq_prime_pow hKcard
  have hoddpp := isOddPrimePower_sq hp5 hKcard
  have hcard3 := three_lt_card_sq hp5 hKcard
  let π : ↥Lb →* StatedProj (StatedSL 2 K) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥Lb))
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center ↥Lb := ker_comp_mk'_center e
  have hcenter : Subgroup.center ↥Lb = ⊥ := by
    have h25 : 25 ≤ p ^ 2 := by nlinarith
    have h := (odd_psl_two_perfect_odd_cover_kernel (p := p) (f := 2) hp2 hK π hπs hker.le
      (hker ▸ hodd)).1 (by omega)
    rw [← hker]
    exact h
  have hπinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).1 (hker.trans hcenter)
  let θ : ↥Lb ≃* PSL2 K :=
    (MulEquiv.ofBijective π ⟨hπinj, hπs⟩).trans
      (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have hHn : Lb ⊔ A ≤ Subgroup.normalizer (Lb : Set (MulAut W)) :=
    sup_le Subgroup.le_normalizer hAN
  have hNnormal : (Lb.subgroupOf (Lb ⊔ A)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 hHn
  let θ' : (Lb.subgroupOf (Lb ⊔ A)) ≃* PSL2 K :=
    (Subgroup.subgroupOfEquivOfLe (le_sup_left : Lb ≤ Lb ⊔ A)).trans θ
  have hC := centralizer_trivial hW hirr.2 hcenter hAN hA2
  have hCbot : Subgroup.centralizer
      ((Lb.subgroupOf (Lb ⊔ A) : Subgroup ↥(Lb ⊔ A)) : Set ↥(Lb ⊔ A)) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    apply hC z
    intro n hn
    exact (Subgroup.mem_centralizer_iff.1 hz n hn).symm
  have hsurj : Function.Surjective (pGammaL2ToMulAutPSL2 K hoddpp hcard3) :=
    pGammaL2ToMulAutPSL2_surjective K (p := p) (f := 2) hK hoddpp hcard3
  let j := normalPSL2ToPGammaL2 (Lb.subgroupOf (Lb ⊔ A)) K hoddpp hcard3 θ' hsurj
  have hj : Function.Injective j :=
    normalPSL2ToPGammaL2_injective _ K hoddpp hcard3 θ' hCbot hsurj
  let ι : PSL2 K →* ↥(Lb ⊔ A) := (Lb.subgroupOf (Lb ⊔ A)).subtype.comp θ'.symm.toMonoidHom
  have hjι : ∀ y, j (ι y) =
      SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL y) := fun y =>
    normalPSL2ToPGammaL2_apply _ K hoddpp hcard3 θ' hsurj y
  let ρH : ↥(Lb ⊔ A) →* (Additive W ≃ₗ[ZMod 2] Additive W) := binaryLin.comp (Lb ⊔ A).subtype
  have hρH : ∀ (g : ↥(Lb ⊔ A)) (v : Additive W),
      ρH g v = Additive.ofMul ((g : MulAut W) (Additive.toMul v)) := fun g v => rfl
  have hρinj : Function.Injective ρH := by
    intro g g' h
    apply Subtype.ext
    apply MulEquiv.ext
    intro w
    have h1 := LinearEquiv.congr_fun h (Additive.ofMul w)
    rw [hρH, hρH] at h1
    exact Additive.ofMul.injective h1
  by_contra hne
  push Not at hne
  have hAH : A ≤ Lb ⊔ A := le_sup_right
  have hB1 : A.subgroupOf (Lb ⊔ A) ≠ ⊥ := by
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA1
    refine Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨⟨a, hAH a.2⟩, a.2⟩, fun h => ha ?_⟩
    exact Subtype.ext
      (congrArg (fun x : ↥(A.subgroupOf (Lb ⊔ A)) => ((x : ↥(Lb ⊔ A)) : MulAut W)) h)
  have hBc : ∀ a ∈ A.subgroupOf (Lb ⊔ A), ∀ b ∈ A.subgroupOf (Lb ⊔ A), a * b = b * a :=
    fun a ha b hb => Subtype.ext (hA2.1 _ ha _ hb)
  have hB2 : ∀ a ∈ A.subgroupOf (Lb ⊔ A), a * a = 1 := fun a ha => by
    apply Subtype.ext
    have := hA2.2 _ ha
    rwa [pow_two] at this
  have hfix : Nat.card (fixedSub ρH (A.subgroupOf (Lb ⊔ A))) = Nat.card (fixV A) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨Additive.toMul x.1, fun a ha => ?_⟩
        invFun := fun w => ⟨Additive.ofMul w.1, fun b hb => ?_⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun w => Subtype.ext rfl }
    · have h1 := x.2 ⟨a, hAH ha⟩ ha
      exact congrArg Additive.toMul h1
    · have hb' : (b : MulAut W) ∈ A := hb
      have h1 := w.2 (b : MulAut W) hb'
      exact congrArg Additive.ofMul h1
  have hcardB : Nat.card (A.subgroupOf (Lb ⊔ A)) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv
  have hpgrp : IsPGroup 2 (A.subgroupOf (Lb ⊔ A)) := fun a => ⟨1, by
    rw [pow_one, pow_two]
    exact Subtype.ext (hB2 (a : ↥(Lb ⊔ A)) a.2)⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hpgrp
  have hcardE : Nat.card (Additive W) = Nat.card W := Nat.card_congr Additive.toMul
  have hoff : finrank (ZMod 2) (Additive W) -
      finrank (ZMod 2) (fixedSub ρH (A.subgroupOf (Lb ⊔ A))) ≤
        Nat.log 2 (Nat.card (A.subgroupOf (Lb ⊔ A))) := by
    refine finrank_sub_le_log_of_card_le _ hk ?_
    rw [hcardE, hcardB, hfix]
    exact hne
  exact no_offender_gamma hp5 hKcard ρH hρinj j hj ι hjι hB1 hBc hB2 hoff

end Final

end CFSG.QuasithinUnique.Setup.Family
