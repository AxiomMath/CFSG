module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldMirrorHost
public import CFSG.GroupTheory.ConjTransport
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldMirrorAut
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Aux.L364Ord

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)

private lemma card_statedProj_statedSL_three_lt {K K' : Type} [Field K] [Finite K]
    [Field K'] [Finite K'] (hK : Nat.card K' = Nat.card K ^ 2) (hq : 3 ≤ Nat.card K) :
    Nat.card (Open.StatedProj (Open.StatedSL 3 K)) <
      Nat.card (Open.StatedProj (Open.StatedSL 3 K')) := by
  set q := Nat.card K with hqdef
  have hpq : 0 < q := by omega
  have htop : Nat.card (Open.StatedProj (Open.StatedSL 3 K)) < q ^ 8 := by
    rw [CFSG.HardMathSupport.Dickson.Sec6.Up34Ord.card_psl3]
    calc q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd 3 (q - 1)
        ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := Nat.div_le_self _ _
      _ < q ^ 3 * (q ^ 2 * q ^ 3) := by
          refine Nat.mul_lt_mul_of_pos_left ?_ (pow_pos hpq 3)
          exact Nat.mul_lt_mul'' (Nat.sub_lt (pow_pos hpq 2) (by norm_num))
            (Nat.sub_lt (pow_pos hpq 3) (by norm_num))
      _ = q ^ 8 := by ring
  have hbot : q ^ 8 ≤ Nat.card (Open.StatedProj (Open.StatedSL 3 K')) := by
    rw [CFSG.HardMathSupport.Dickson.Sec6.Up34Ord.card_psl3, hK]
    rw [Nat.le_div_iff_mul_le
      (Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left 3 (q ^ 2 - 1)) (by norm_num))]
    have hgcd : Nat.gcd 3 (q ^ 2 - 1) ≤ 3 :=
      Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 3 (q ^ 2 - 1))
    have h1 : q ^ 3 ≤ q ^ 4 - 1 := by
      have h2 : q ^ 3 + 1 ≤ q ^ 4 := by
        calc q ^ 3 + 1 ≤ q ^ 3 + q ^ 3 := by
              have : 1 ≤ q ^ 3 := Nat.one_le_iff_ne_zero.mpr (pow_pos hpq 3).ne'
              omega
          _ = 2 * q ^ 3 := by ring
          _ ≤ q * q ^ 3 := Nat.mul_le_mul_right _ (by omega)
          _ = q ^ 4 := by ring
      omega
    have h2 : q ^ 5 ≤ q ^ 6 - 1 := by
      have h3 : q ^ 5 + 1 ≤ q ^ 6 := by
        calc q ^ 5 + 1 ≤ q ^ 5 + q ^ 5 := by
              have : 1 ≤ q ^ 5 := Nat.one_le_iff_ne_zero.mpr (pow_pos hpq 5).ne'
              omega
          _ = 2 * q ^ 5 := by ring
          _ ≤ q * q ^ 5 := Nat.mul_le_mul_right _ (by omega)
          _ = q ^ 6 := by ring
      omega
    have hq6 : 3 ≤ q ^ 6 := by
      have h3 : (3 : ℕ) ^ 6 ≤ q ^ 6 := Nat.pow_le_pow_left hq 6
      norm_num at h3
      omega
    have h4 : (q ^ 2) ^ 2 = q ^ 4 := by ring
    have h6 : (q ^ 2) ^ 3 = q ^ 6 := by ring
    rw [h4, h6]
    calc q ^ 8 * Nat.gcd 3 (q ^ 2 - 1) ≤ q ^ 8 * 3 := Nat.mul_le_mul_left _ hgcd
      _ ≤ q ^ 8 * q ^ 6 := Nat.mul_le_mul_left _ hq6
      _ = q ^ 6 * (q ^ 3 * q ^ 5) := by ring
      _ ≤ q ^ 6 * ((q ^ 4 - 1) * (q ^ 6 - 1)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul h1 h2)
  exact lt_of_lt_of_le htop hbot

theorem false_of_field_host_field_normal (hcat : L3TwoPowProperFixedCatalog)
    (hmult : Quasithin.SchurMult2L3) {G : Type} [Group G] [Finite G] {t : G} {P W M : Subgroup G}
    (hset : L34FieldNormalSetting G t P) (hWodd : Odd (Nat.card W)) (hW1 : W ≠ ⊥)
    (hPW : normalizer (P : Set G) ≤ normalizer (W : Set G))
    (hWE : ∀ E : Subgroup G, E ≤ centralizer ({t} : Set G) → Open.IsElemAbelian 2 E →
      8 ≤ Nat.card E → GrSLit.wGroup E = W)
    (hM : normalizer (W : Set G) = M) {L : Subgroup (↥M ⧸ pPrimeCore 2 ↥M)} (hL : IsComponent L)
    (hLn : L.Normal) (hZ : center ↥L = ⊥)
    (hPL : (P.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M)) ≤ L) {m : ℕ} (hm : 4 ≤ m)
    (hme : Even m) (hPm : Blueprint.LieModel (P ⧸ Open.fusionZStar P) .PSL 3 2 m)
    (hLm : Blueprint.LieModel (↥L ⧸ center ↥L) .PSL 3 2 (2 * m)) : False := by
  classical
  haveI hfact2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hset' : L34FieldNormalSetting G t P := hset
  obtain ⟨-, ht2, hPt, hPp, hPn, -, -, -, -⟩ := hset
  have hCM : centralizer ({t} : Set G) ≤ M := by
    rw [← hM]
    exact ((normal_subgroupOf_iff_le_normalizer hPt).mp hPn).trans hPW
  have htM : t ∈ M := hCM (mem_centralizer_singleton_iff.mpr rfl)
  have hPM : P ≤ M := hPt.trans hCM
  have hOX : pPrimeCore 2 (↥M ⧸ pPrimeCore 2 ↥M) = ⊥ :=
    GH74.pPrimeCore_quotient_pPrimeCore_eq_bot _ 2
  have hOL : pPrimeCore 2 ↥L = ⊥ := pPrimeCore_eq_bot_of_isSubnormal hOX hL.2
  have hZL : Open.fusionZStar ↥L = center ↥L := by
    refine CatLeaf.fusionZStar_eq_center_of_quasisimple hL.1 ?_
    rw [hOL]
    have : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hL.1
    exact bot_ne_top
  have hPSL : Open.StatedClassicalModel (↥L ⧸ center ↥L) .PSL 3 2 (2 * m) := by
    rcases hLm with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    all_goals exact absurd h (by norm_num)
  obtain ⟨-, F, _, _, hF, ⟨eF⟩⟩ := hPSL
  have hFfin : Fintype F := Fintype.ofFinite F
  have hFchar : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * m) (by
    rwa [← Nat.card_eq_fintype_card])
  let eL : ↥L ≃* projectiveSL 3 F :=
    (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans eF).trans
      ((Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm.trans
        (LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F))
  obtain ⟨B, hB, φ, hφ⟩ := exists_hom_ne_one_of_properFixedComponent (F := F) hm hme hF
  set π : ↥M →* (↥M ⧸ pPrimeCore 2 ↥M) := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hπ
  set s : ↥M := ⟨t, htM⟩ with hs
  have hs2 : orderOf s = 2 := by rw [hs, Subgroup.orderOf_mk]; exact ht2
  set u : ↥M ⧸ pPrimeCore 2 ↥M := π s with hu
  have hu2 : orderOf u = 2 := GH74.GLS.TwoThin.orderOf_barMk hs2
  have huu : u * u = 1 := by
    have h := pow_orderOf_eq_one u
    rwa [hu2, pow_two] at h
  have hΛs : P.subgroupOf M ≤ centralizer ({s} : Set ↥M) := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (hPt (mem_subgroupOf.mp hx))
  have hΛ : IsPComponent 2 ((P.subgroupOf M).subgroupOf (centralizer ({s} : Set ↥M))) := by
    rw [hs, FooteLit.centralizer_mk_eq htM,
      UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_right 2 Nat.prime_two,
      inf_of_le_left hCM]
    exact hPp
  have hΛ2 : TwoComponents.IsTwoComponent
      ((P.subgroupOf M).subgroupOf (centralizer ({s} : Set ↥M))) :=
    (CatalogueBAlternating.pComponent_two_iff _).mp hΛ
  have hΛbC : (P.subgroupOf M).map π ≤
      centralizer ({u} : Set (↥M ⧸ pPrimeCore 2 ↥M)) :=
    (Subgroup.map_mono hΛs).trans (GH74.GLS.TwoThin.map_centralizer_barMk hs2).le
  have hΛbp : IsPComponent 2 (((P.subgroupOf M).map π).subgroupOf
      (centralizer ({u} : Set (↥M ⧸ pPrimeCore 2 ↥M)))) :=
    (CatalogueBAlternating.pComponent_two_iff _).mpr
      (GH74.GLS.TwoThin.isTwoComponent_map_barMk hs2 hΛs hΛ2)
  have hΛL : Blueprint.LieModel (↥(P.subgroupOf M) ⧸ Open.fusionZStar ↥(P.subgroupOf M))
      .PSL 3 2 m :=
    Blueprint.LieModel.of_mulEquiv
      (Sol78.fusionZStarQuotCongr (subgroupOfEquivOfLe hPM).symm) hPm
  have hΛbL : Blueprint.LieModel (↥((P.subgroupOf M).map π) ⧸
      Open.fusionZStar ↥((P.subgroupOf M).map π)) .PSL 3 2 m := by
    set f : ↥(P.subgroupOf M) →* ↥((P.subgroupOf M).map π) :=
      π.subgroupMap (P.subgroupOf M) with hf
    have hfs : Function.Surjective f := π.subgroupMap_surjective (P.subgroupOf M)
    have hfk : ¬ 2 ∣ Nat.card f.ker := by
      have hle : f.ker.map (P.subgroupOf M).subtype ≤ pPrimeCore 2 ↥M := by
        rintro _ ⟨x, hx, rfl⟩
        have h1 : (f x : ↥M ⧸ pPrimeCore 2 ↥M) = 1 :=
          congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
        rw [← QuotientGroup.ker_mk' (pPrimeCore 2 ↥M)]
        exact h1
      have hdvd : Nat.card f.ker ∣ Nat.card (pPrimeCore 2 ↥M) := by
        rw [← Subgroup.card_map_of_injective (P.subgroupOf M).subtype_injective]
        exact Subgroup.card_dvd_of_le hle
      intro h2
      have hc := pPrimeCore_coprime_card (p := 2) (G := ↥M)
      exact absurd (Nat.dvd_gcd (dvd_refl 2) (h2.trans hdvd)) (by rw [hc]; norm_num)
    obtain ⟨e⟩ := GSThmB.OddQuot.nonempty_fusionZStar_equiv_of_surjective f hfs hfk
    exact Blueprint.LieModel.of_mulEquiv e hΛL
  set Pbar : Subgroup ↥L := ((P.subgroupOf M).map π).subgroupOf L with hPbar
  have hPbarL : Blueprint.LieModel (↥Pbar ⧸ Open.fusionZStar ↥Pbar) .PSL 3 2 m :=
    Blueprint.LieModel.of_mulEquiv
      (Sol78.fusionZStarQuotCongr (subgroupOfEquivOfLe hPL).symm) hΛbL
  set cL : MulAut ↥L := MulAut.conjNormal u with hcL
  set σ : MulAut (projectiveSL 3 F) := MulAut.congr eL cL with hσ
  set Q : Subgroup (projectiveSL 3 F) := Pbar.map eL.toMonoidHom with hQ
  have hQL : Blueprint.LieModel (↥Q ⧸ Open.fusionZStar ↥Q) .PSL 3 2 m :=
    Blueprint.LieModel.of_mulEquiv
      (Sol78.fusionZStarQuotCongr (Pbar.equivMapOfInjective eL.toMonoidHom eL.injective)) hPbarL
  have hcapp : ∀ x : ↥L, ((cL x : ↥L) : ↥M ⧸ pPrimeCore 2 ↥M) =
      u * (x : ↥M ⧸ pPrimeCore 2 ↥M) * u⁻¹ := fun x => MulAut.conjNormal_apply u x
  have hfixC : FixedCommutingProduct.fixedSubgroup cL =
      (L ⊓ centralizer ({u} : Set (↥M ⧸ pPrimeCore 2 ↥M))).subgroupOf L := by
    ext x
    rw [LocalAnalysis.ComponentInitial.mem_fixedSubgroup_iff, mem_subgroupOf, mem_inf,
      mem_centralizer_singleton_iff]
    constructor
    · intro hx
      have h1 := congrArg Subtype.val hx
      rw [hcapp] at h1
      refine ⟨x.2, ?_⟩
      calc (x : ↥M ⧸ pPrimeCore 2 ↥M) * u = u * (x : ↥M ⧸ pPrimeCore 2 ↥M) * u⁻¹ * u := by
            rw [h1]
        _ = u * (x : ↥M ⧸ pPrimeCore 2 ↥M) := by group
    · rintro ⟨-, hx⟩
      apply Subtype.ext
      rw [hcapp]
      calc u * (x : ↥M ⧸ pPrimeCore 2 ↥M) * u⁻¹ =
            (x : ↥M ⧸ pPrimeCore 2 ↥M) * u * u⁻¹ := by rw [hx]
        _ = (x : ↥M ⧸ pPrimeCore 2 ↥M) := by group
  have hPbarFix : Pbar ≤ FixedCommutingProduct.fixedSubgroup cL := by
    intro x hx
    rw [LocalAnalysis.ComponentInitial.mem_fixedSubgroup_iff]
    apply Subtype.ext
    have hx' : (x : ↥M ⧸ pPrimeCore 2 ↥M) ∈ (P.subgroupOf M).map π := by
      rw [hPbar] at hx
      exact mem_subgroupOf.mp hx
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hx'
    show u * (x : ↥M ⧸ pPrimeCore 2 ↥M) * u⁻¹ = (x : ↥M ⧸ pPrimeCore 2 ↥M)
    rw [← hxy]
    have hconj : u * π y * u⁻¹ = π (⟨t, htM⟩ * y * ⟨t, htM⟩⁻¹) := by
      rw [hu, hs]
      simp
    have hfix : ⟨t, htM⟩ * y * ⟨t, htM⟩⁻¹ = y := by
      apply Subtype.ext
      show t * (y : G) * t⁻¹ = (y : G)
      have hyP : (y : G) ∈ P := mem_subgroupOf.mp hy
      have hc : (y : G) * t = t * (y : G) := mem_centralizer_singleton_iff.mp (hPt hyP)
      rw [← hc]
      group
    rw [hconj, hfix]
  have hTp : IsPComponent 2 (((P.subgroupOf M).map π).subgroupOf
      (L ⊓ centralizer ({u} : Set (↥M ⧸ pPrimeCore 2 ↥M)))) :=
    Burgoyne.C.isPComponent_subgroupOf_of_le (le_inf hPL hΛbC) inf_le_right hΛbp
  have hT'p : IsPComponent 2 (Pbar.subgroupOf (FixedCommutingProduct.fixedSubgroup cL)) := by
    rw [hPbar, hfixC]
    exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff'
      (L := (P.subgroupOf M).map π) inf_le_left 2 Nat.prime_two).mpr hTp
  have hPbarNeTop : Pbar ≠ ⊤ := by
    intro htop
    have hQtop : Q = ⊤ := by
      rw [hQ, htop, Subgroup.map_top_of_surjective _ eL.surjective]
    have hQLiso : ↥Q ≃* ↥L :=
      ((MulEquiv.subgroupCongr hQtop).trans Subgroup.topEquiv).trans eL.symm
    have hcardQ : Nat.card (↥Q ⧸ Open.fusionZStar ↥Q) = Nat.card (↥L ⧸ center ↥L) :=
      Nat.card_congr ((Sol78.fusionZStarQuotCongr hQLiso).trans
        (QuotientGroup.quotientMulEquivOfEq hZL)).toEquiv
    have hPSLq : Open.StatedClassicalModel (↥Q ⧸ Open.fusionZStar ↥Q) .PSL 3 2 m := by
      rcases hQL with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      all_goals exact absurd h (by norm_num)
    obtain ⟨-, F₁, _, _, hF₁, ⟨e₁⟩⟩ := hPSLq
    have heq : Nat.card (Open.StatedProj (Open.StatedSL 3 F₁)) =
        Nat.card (Open.StatedProj (Open.StatedSL 3 F)) := by
      rw [← Nat.card_congr e₁.toEquiv, hcardQ]
      exact Nat.card_congr eF.toEquiv
    have hq3 : 3 ≤ Nat.card F₁ := by
      rw [hF₁]
      calc 3 ≤ 2 ^ 4 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have hKsq : Nat.card F = Nat.card F₁ ^ 2 := by
      rw [hF, hF₁, Nat.mul_comm 2 m, pow_mul]
    exact absurd heq (card_statedProj_statedSL_three_lt (K := F₁) (K' := F) hKsq hq3).ne
  have hProperL : CatLeaf.ProperFixedComponent cL Pbar := by
    refine ⟨?_, hPbarFix, hT'p, hPbarNeTop⟩
    intro y
    have h2 : cL * cL = 1 := by
      have h : MulAut.conjNormal (H := L) u * MulAut.conjNormal (H := L) u = 1 := by
        rw [← map_mul, huu, map_one]
      exact h
    rw [← MulAut.mul_apply, h2, MulAut.one_apply]
  have hProperQ : CatLeaf.ProperFixedComponent σ Q := (hProperL.map eL).1
  set χ : ↥M →* B := (φ.comp (MulAut.congr eL).toMonoidHom).comp
    ((MulAut.conjNormal (H := L)).comp π) with hχ
  set χN : ↥(normalizer (W : Set G)) →* B :=
    χ.comp (MulEquiv.subgroupCongr hM).toMonoidHom with hχNdef
  have htN : t ∈ normalizer (W : Set G) := by rw [hM]; exact htM
  have hχN : χN ⟨t, htN⟩ = 1 :=
    hom_eq_one_of_field_signalizer hcat hmult hset' hWodd hW1 hPW hWE htN χN
  have hχ1 : χ ⟨t, htM⟩ = 1 := by
    have h2 : (MulEquiv.subgroupCongr hM) ⟨t, htN⟩ = ⟨t, htM⟩ := Subtype.ext (by rfl)
    rw [← h2]
    exact hχN
  have hχσ : χ ⟨t, htM⟩ = φ σ := by simp [hχ, hσ, hcL, hu, hs]
  exact hφ σ Q hProperQ hQL (hχσ.symm.trans hχ1)

theorem false_of_field_host_swap_pair (hcat : L3TwoPowProperFixedCatalog)
    (hmult : Quasithin.SchurMult2L3) {G : Type} [Group G] [Finite G] {t : G} {P W M : Subgroup G}
    (hset : L34FieldNormalSetting G t P) (hWodd : Odd (Nat.card W)) (hW1 : W ≠ ⊥)
    (hPW : normalizer (P : Set G) ≤ normalizer (W : Set G))
    (hWE : ∀ E : Subgroup G, E ≤ centralizer ({t} : Set G) → Open.IsElemAbelian 2 E →
      8 ≤ Nat.card E → GrSLit.wGroup E = W)
    (hM : normalizer (W : Set G) = M) (htM : t ∈ M) {L : Subgroup (↥M ⧸ pPrimeCore 2 ↥M)}
    (hmove : L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨t, htM⟩)).toMonoidHom ≠ L)
    (hpair : ∀ g : ↥M ⧸ pPrimeCore 2 ↥M, L.map (MulAut.conj g).toMonoidHom = L ∨
      L.map (MulAut.conj g).toMonoidHom =
        L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨t, htM⟩)).toMonoidHom) :
    False := by
  subst M
  classical
  let X := ↥(normalizer (W : Set G)) ⧸ pPrimeCore 2 ↥(normalizer (W : Set G))
  let π : ↥(normalizer (W : Set G)) →* X :=
    QuotientGroup.mk' (pPrimeCore 2 ↥(normalizer (W : Set G)))
  let a : X := (⟨t, htM⟩ : ↥(normalizer (W : Set G)))
  let Lg : X → Subgroup X := fun g => L.map (MulAut.conj g).toMonoidHom
  have ha_ne : Lg a ≠ L := by simpa [Lg, a] using hmove
  have hpairLg : ∀ g : X, Lg g = L ∨ Lg g = Lg a := by
    intro g
    simpa [Lg, a] using hpair g
  have hLg_mul : ∀ g h : X, Lg (g * h) = (Lg h).map (MulAut.conj g).toMonoidHom := by
    intro g h
    exact (CFSG.GroupTheory.map_conj_map_conj g h L).symm
  have hmap_inj : ∀ g : X, Function.Injective
      (fun H : Subgroup X => H.map (MulAut.conj g).toMonoidHom) :=
    fun g => Subgroup.map_injective (MulAut.conj g).injective
  let f : X → ℤˣ := fun g => if Lg g = L then (1 : ℤˣ) else -1
  have hf_mul : ∀ g h : X, f (g * h) = f g * f h := by
    intro g h
    rcases hpairLg g with hg | hg <;> rcases hpairLg h with hh | hh
    · have hgh : Lg (g * h) = L := by
        rw [hLg_mul, hh]
        exact hg
      have hfgh : f (g * h) = 1 := if_pos hgh
      have hfg : f g = 1 := if_pos hg
      have hfh : f h = 1 := if_pos hh
      rw [hfgh, hfg, hfh, mul_one]
    · have hne : Lg (g * h) ≠ L := by
        rw [hLg_mul, hh]
        intro hcon
        have hEq : (Lg a).map (MulAut.conj g).toMonoidHom =
            L.map (MulAut.conj g).toMonoidHom := by
          rw [hcon]
          simpa [Lg] using hg.symm
        exact ha_ne ((hmap_inj g) hEq)
      have hgh : Lg (g * h) = Lg a := by
        rcases hpairLg (g * h) with h' | h'
        · exact absurd h' hne
        · exact h'
      have hfgh : f (g * h) = -1 := if_neg hne
      have hfg : f g = 1 := if_pos hg
      have hfh : f h = -1 := if_neg (by rw [hh]; exact ha_ne)
      rw [hfgh, hfg, hfh, one_mul]
    · have hgh : Lg (g * h) = Lg a := by
        rw [hLg_mul, hh]
        exact hg
      have hne : Lg (g * h) ≠ L := by rw [hgh]; exact ha_ne
      have hfgh : f (g * h) = -1 := if_neg hne
      have hfg : f g = -1 := if_neg (by rw [hg]; exact ha_ne)
      have hfh : f h = 1 := if_pos hh
      rw [hfgh, hfg, hfh, mul_one]
    · have hne : Lg (g * h) ≠ Lg a := by
        rw [hLg_mul, hh]
        intro hcon
        have hEq : (Lg a).map (MulAut.conj g).toMonoidHom =
            L.map (MulAut.conj g).toMonoidHom := by
          rw [hcon]
          simpa [Lg] using hg.symm
        exact ha_ne ((hmap_inj g) hEq)
      have hgh : Lg (g * h) = L := by
        rcases hpairLg (g * h) with h' | h'
        · exact h'
        · exact absurd h' hne
      have hfgh : f (g * h) = 1 := if_pos hgh
      have hfg : f g = -1 := if_neg (by rw [hg]; exact ha_ne)
      have hfh : f h = -1 := if_neg (by rw [hh]; exact ha_ne)
      rw [hfgh, hfg, hfh, Int.units_mul_self]
  let ε : X →* ℤˣ := MonoidHom.mk' f hf_mul
  let χ : ↥(normalizer (W : Set G)) →* ℤˣ := ε.comp π
  have hkill : χ ⟨t, htM⟩ = 1 :=
    hom_eq_one_of_field_signalizer hcat hmult hset hWodd hW1 hPW hWE htM χ
  have hχ : χ ⟨t, htM⟩ = -1 := by
    have hε : ε a = -1 := by
      rw [show ε = MonoidHom.mk' f hf_mul from rfl, MonoidHom.mk'_apply]
      simp [f, ha_ne]
    change ε ((QuotientGroup.mk' (pPrimeCore 2 ↥(normalizer (W : Set G)))) ⟨t, htM⟩) = -1
    rw [QuotientGroup.mk'_apply]
    exact hε
  rw [hkill] at hχ
  exact (by decide : (1 : ℤˣ) ≠ -1) hχ

end CFSG.ComponentClassification.GrSLit.L34Sec5S

end
