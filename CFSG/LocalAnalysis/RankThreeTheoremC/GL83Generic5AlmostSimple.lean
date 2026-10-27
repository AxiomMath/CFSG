module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Abstract
import CFSG.LocalAnalysis.RankThreeTheoremC.LayerNormal
import CFSG.LocalAnalysis.RankThreeTheoremC.PSLTwoRank
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_8_27

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.PreuniquenessRankFour.Helpers (pRank_map_of_injective pRank_attained)
open scoped MatrixGroups

namespace GL83Generic5AlmostSimple

section PSL

variable {p : ℕ} [Fact p.Prime]

theorem natCast_ne_zero {n : ℕ} (hn0 : n ≠ 0) (hnp : n < p) : (n : GaloisField p 2) ≠ 0 := by
  rw [ne_eq, CharP.cast_eq_zero_iff (GaloisField p 2) p]
  exact fun h => absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) h) (by omega)

theorem isPerfect_psl (hp5 : 5 ≤ p) : Group.IsPerfect PSL(2, GaloisField p 2) := by
  refine ⟨SL2Simple.PSL_commutator_eq_top ⟨2, ?_, fun h => ?_⟩⟩
  · exact_mod_cast natCast_ne_zero (n := 2) (by norm_num) (by omega)
  · have h3 : ((3 : ℕ) : GaloisField p 2) = 0 := by
      push_cast
      linear_combination h
    exact natCast_ne_zero (n := 3) (by norm_num) (by omega) h3

theorem pRank_sylow_psl (Q : Sylow p PSL(2, GaloisField p 2)) :
    CFSG.Open.pRank p (Q : Subgroup PSL(2, GaloisField p 2)) = 2 := by
  have hp : p.Prime := Fact.out
  have hcard : Nat.card (Q : Subgroup PSL(2, GaloisField p 2)) = p ^ 2 := by
    obtain ⟨f⟩ := CFSG.BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive
      (GaloisField.card p 2 (by norm_num)) Q
    rw [← Nat.card_congr f.toEquiv, Nat.card_congr Multiplicative.toAdd,
      GaloisField.card p 2 (by norm_num)]
  refine le_antisymm ?_ ?_
  · obtain ⟨E, hEQ, -, hEc⟩ := pRank_attained p hp (Q : Subgroup PSL(2, GaloisField p 2))
    have hle := Subgroup.card_le_of_le hEQ
    rw [hEc, hcard] at hle
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
  · rw [CFSG.PreuniquenessRankFour.Helpers.pRank_sylow_eq_globalRank p hp Q]
    exact le_pRank_psl_two p 2 (by norm_num)

end PSL

variable {p : ℕ} {Y : Type} [Group Y]

theorem normal_eq_bot (S : Sylow p Y) {Γ : Subgroup Y} (hΓ : Γ ≠ ⊤)
    (hN : ∀ D : Subgroup Y, D ≤ S → D ≠ ⊥ → normalizer (D : Set Y) ≤ Γ)
    {N : Subgroup Y} [N.Normal] (hNp : IsPGroup p N) : N = ⊥ := by
  by_contra hne
  have h := hN N (hNp.le_sylow_of_normal S) hne
  rw [normalizer_eq_top] at h
  exact hΓ (top_le_iff.mp h)

theorem pCore_eq_bot (S : Sylow p Y) {Γ : Subgroup Y} (hΓ : Γ ≠ ⊤)
    (hN : ∀ D : Subgroup Y, D ≤ S → D ≠ ⊥ → normalizer (D : Set Y) ≤ Γ) :
    CFSG.pCore p Y = ⊥ :=
  have : (CFSG.pCore p Y).Normal := CFSG.pCore_normal
  normal_eq_bot S hΓ hN CFSG.pCore_isPGroup

theorem normal_of_unique {K : Subgroup Y} (hK : IsComponentOf K ⊤)
    (huniq : ∀ K' : Subgroup Y, IsComponentOf K' ⊤ → K' = K) : K.Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hmap : K.map (MulAut.conj g).toMonoidHom = K :=
    huniq _ (IsComponentOf.map_conj hK (mem_top g))
  have : (MulAut.conj g) n ∈ K.map (MulAut.conj g).toMonoidHom := mem_map_of_mem _ hn
  rw [hmap] at this
  simpa using this

theorem simple_of_center_eq_bot {K : Subgroup Y} (hK : IsComponentOf K ⊤)
    (hZ : center K = ⊥) : IsSimpleGroup K ∧ ∃ a b : K, a * b ≠ b * a := by
  let e : K ≃* K ⧸ center K :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  have : IsSimpleGroup (K ⧸ center K) := hK.2.2.2
  refine ⟨e.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK.2.2
  refine ⟨e.symm a, e.symm b, fun hba => hab ?_⟩
  simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e hba

theorem notSecExcl3 (hexcl : NoExcludedSection3 Y) {K : Subgroup Y}
    (hq : CFSG.Open.IsQuasisimple K) (hZ : center K = ⊥) : NotSecExcl3 K := by
  let e : K ≃* (⊤ : Subgroup (K ⧸ (⊥ : Subgroup K))) :=
    QuotientGroup.quotientBot.symm.trans Subgroup.topEquiv.symm
  have hZ' : center (⊤ : Subgroup (K ⧸ (⊥ : Subgroup K))) = ⊥ := by
    rw [← Subgroup.map_center_eq e, hZ, Subgroup.map_bot]
  exact notSecExcl3_of_mulEquiv
    (e.trans ((QuotientGroup.quotientMulEquivOfEq hZ').trans QuotientGroup.quotientBot).symm)
    (hexcl K ⊥ ⊤ (CFSG.ComponentClassification.Components.quasisimple_of_equiv e.symm hq))

theorem conjNormal_injective {K : Subgroup Y} [K.Normal] (hC : centralizer (K : Set Y) = ⊥) :
    Function.Injective (MulAut.conjNormal : Y →* MulAut K) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hC]
  intro x hx
  rw [mem_centralizer_iff]
  intro y hy
  have h := congrArg (fun α : MulAut K => ((α ⟨y, hy⟩ : K) : Y)) (MonoidHom.mem_ker.1 hx)
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h
  calc y * x = x * y * x⁻¹ * x := by rw [h]
    _ = x * y := by group

theorem le_of_isPerfect {K : Subgroup Y} [K.Normal] (hC : centralizer (K : Set Y) = ⊥)
    [Group.IsSolvable (Outer K)] (J : Subgroup Y) [Group.IsPerfect J] : J ≤ K := by
  let φ : Y →* Outer K := (QuotientGroup.mk' (inner K)).comp MulAut.conjNormal
  have : Group.IsPerfect (J.map φ) := Group.IsPerfect.map φ
  have : Subsingleton (J.map φ) :=
    CFSG.ComponentClassification.SolvableKernelContainment.perfect_solvable_subsingleton
  have hJ : J ≤ φ.ker := (map_eq_bot_iff J).mp (eq_bot_of_subsingleton _)
  intro y hy
  obtain ⟨k, hk⟩ : MulAut.conjNormal y ∈ inner K :=
    (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp (hJ hy))
  have hc : (k : Y)⁻¹ * y ∈ centralizer (K : Set Y) := by
    rw [mem_centralizer_iff]
    intro m hm
    have h := congrArg (fun α : MulAut K => ((α ⟨m, hm⟩ : K) : Y)) hk
    simp only [MulAut.conj_apply, MulAut.conjNormal_apply, coe_mul, coe_inv] at h
    calc m * ((k : Y)⁻¹ * y) = (k : Y)⁻¹ * (k * m * (k : Y)⁻¹) * y := by group
      _ = (k : Y)⁻¹ * (y * m * y⁻¹) * y := by rw [h]
      _ = (k : Y)⁻¹ * y * m := by group
  rw [hC, mem_bot, inv_mul_eq_one] at hc
  rw [← hc]
  exact k.2

variable [Finite Y]

theorem center_eq_bot (hp : p.Prime) (hcore : primeComplementCore (G := Y) p = ⊥)
    {K : Subgroup Y} [K.Normal] (hK : IsComponentOf K ⊤)
    (hnorm : ∀ N : Subgroup Y, N.Normal → IsPGroup p N → N = ⊥) : center K = ⊥ := by
  have hpg : IsPGroup p (center K) :=
    CFSG.AGLEmbedding.isPGroup_center_of_isComponentOf hp hcore hK
  have : ((center K).map K.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
  exact (map_eq_bot_iff_of_injective _ K.subtype_injective).mp
    (hnorm _ inferInstance (hpg.map K.subtype))

theorem centralizer_eq_bot [Fact p.Prime] (hcore : primeComplementCore (G := Y) p = ⊥)
    (hpc : CFSG.pCore p Y = ⊥) {K : Subgroup Y} (hK : IsComponentOf K ⊤)
    (huniq : ∀ K' : Subgroup Y, IsComponentOf K' ⊤ → K' = K) (hZ : center K = ⊥) :
    centralizer (K : Set Y) = ⊥ := by
  have hF : CFSG.generalizedFitting Y = K := by
    rw [CFSG.generalizedFitting, CFSG.Fitting_eq_pcore Y p hcore, hpc, bot_sup_eq]
    exact le_antisymm
      (sSup_le fun K' hK' => (huniq K' ((CFSG.isComponent_iff_open K').mp hK')).le)
      (CFSG.AGLEmbedding.le_layer_of_isComponentOf hK)
  have hle := CFSG.centralizer_generalizedFitting_le Y
  rw [hF] at hle
  refine eq_bot_iff.mpr fun x hx => ?_
  have hz : (⟨x, hle hx⟩ : K) ∈ center K :=
    mem_center_iff.mpr fun y => Subtype.ext ((mem_centralizer_iff.mp hx) y y.2)
  rw [hZ, mem_bot] at hz
  exact mem_bot.mpr (congrArg Subtype.val hz)

theorem exists_isComponentOf [Fact p.Prime] (hcore : primeComplementCore (G := Y) p = ⊥)
    (hpc : CFSG.pCore p Y = ⊥) (hY : (⊤ : Subgroup Y) ≠ ⊥) :
    ∃ K : Subgroup Y, IsComponentOf K ⊤ := by
  by_contra hno
  have hlayer : CFSG.layer Y = ⊥ := by
    by_contra hne
    exact hno (CFSG.AGLEmbedding.exists_isComponentOf_of_layer_ne_bot hne)
  have hchar : centralizer (CFSG.pCore p Y : Set Y) ≤ CFSG.pCore p Y :=
    CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot Y p hcore hlayer
  have htop : centralizer (((⊥ : Subgroup Y) : Set Y)) = ⊤ :=
    eq_top_iff.mpr fun x _ => mem_centralizer_iff.mpr fun y hy => by
      rw [SetLike.mem_coe, mem_bot] at hy
      rw [hy, one_mul, mul_one]
  rw [hpc, htop] at hchar
  exact hY (le_bot_iff.mp hchar)

theorem eq_of_isComponentOf [Fact p.Prime] (hp2 : p ≠ 2)
    (hcore : primeComplementCore (G := Y) p = ⊥) (S : Sylow p Y) {Γ : Subgroup Y} (hΓ : Γ ≠ ⊤)
    (hN : ∀ D : Subgroup Y, D ≤ S → D ≠ ⊥ → normalizer (D : Set Y) ≤ Γ)
    {K₁ K₂ : Subgroup Y} (h₁ : IsComponentOf K₁ ⊤) (h₂ : IsComponentOf K₂ ⊤) : K₁ = K₂ := by
  have hp : p.Prime := Fact.out
  by_contra hne
  obtain ⟨t₁, ⟨ht₁S, ht₁K⟩, ht₁o, -⟩ :=
    CFSG.AGLEmbedding.exists_mem_sylow_inf_component hp hp2 hcore S h₁
  obtain ⟨t₂, ⟨ht₂S, ht₂K⟩, ht₂o, -⟩ :=
    CFSG.AGLEmbedding.exists_mem_sylow_inf_component hp hp2 hcore S h₂
  have hz : ∀ {t : Y}, orderOf t = p → zpowers t ≠ ⊥ := fun {t} ht hbot => by
    rw [zpowers_eq_bot] at hbot
    rw [hbot, orderOf_one] at ht
    exact hp.one_lt.ne ht
  have hle : ∀ {K K' : Subgroup Y} {t : Y}, IsComponentOf K ⊤ → IsComponentOf K' ⊤ → K' ≠ K →
      t ∈ (S : Subgroup Y) → t ∈ K → orderOf t = p → K' ≤ Γ := by
    intro K K' t hK hK' hne' htS htK hto
    have hK'K : K' ≤ centralizer (K : Set Y) := commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne K' K hK' hK hne')
    have hzt : K' ≤ centralizer ((zpowers t : Subgroup Y) : Set Y) :=
      le_centralizer_iff.mp ((zpowers_le.mpr htK).trans (le_centralizer_iff.mp hK'K))
    exact hzt.trans ((centralizer_le_normalizer _).trans
      (hN _ (zpowers_le.mpr htS) (hz hto)))
  have hall : ∀ K : Subgroup Y, IsComponentOf K ⊤ → K ≤ Γ := by
    intro K hK
    by_cases h1 : K = K₁
    · exact hle h₂ hK (fun h => hne (h1.symm.trans h)) ht₂S ht₂K ht₂o
    · exact hle h₁ hK h1 ht₁S ht₁K ht₁o
  have hE : CFSG.ComponentClassification.Layer.subgroup Y ≤ Γ := sSup_le fun K hK => hall K hK
  have : (CFSG.ComponentClassification.Layer.subgroup Y).Normal :=
    CFSG.ComponentClassification.Layer.normal Y
  have hSE : zpowers t₁ ≤ (S : Subgroup Y) ⊓ CFSG.ComponentClassification.Layer.subgroup Y :=
    zpowers_le.mpr ⟨ht₁S, (le_sSup (s := {K : Subgroup Y | IsComponentOf K ⊤}) h₁) ht₁K⟩
  have hNE := hN _ inf_le_left (fun hbot => hz ht₁o (le_bot_iff.mp (hbot ▸ hSE)))
  exact CFSG.AGLEmbedding.not_le_of_normalizer_inf_le S hNE hΓ hE

theorem eq_bot [Fact p.Prime] (K1 : StronglyEmbeddedRankTwoKFactNoBM)
    (Sch : CFSG.AGLEmbedding.KFactCatalogSchreier) (KA : KFactSignalizerTrivial) (hp5 : 5 ≤ p)
    (hcore : primeComplementCore (G := Y) p = ⊥)
    (hcat : CFSG.AGLEmbedding.CatalogSimpleSections Y) (hexcl : NoExcludedSection3 Y)
    {L U Γ : Subgroup Y} (e : L ≃* PSL(2, GaloisField p 2))
    (hUL : CFSG.ABGLocalTools.IsSylowOf p U L) (hUY : CFSG.ABGLocalTools.IsSylowOf p U ⊤)
    (hΓ : Γ ≠ ⊤) (hN : ∀ D : Subgroup Y, D ≤ U → D ≠ ⊥ → normalizer (D : Set Y) ≤ Γ)
    (hLΓ : ¬ L ≤ Γ) {W : Subgroup Y} (hW : Nat.Coprime p (Nat.card W))
    (hUW : U ≤ normalizer (W : Set Y)) : W = ⊥ := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  obtain ⟨Q₀, hQ₀⟩ := hUY
  let S : Sylow p Y := Sylow.mapSurjective (f := (⊤ : Subgroup Y).subtype)
    (fun y => ⟨⟨y, mem_top y⟩, rfl⟩) Q₀
  have hSU : (S : Subgroup Y) = U := (Sylow.coe_mapSurjective _ _).trans hQ₀
  have hNS : ∀ D : Subgroup Y, D ≤ S → D ≠ ⊥ → normalizer (D : Set Y) ≤ Γ := hSU ▸ hN
  have hpc := pCore_eq_bot S hΓ hNS
  have hY : (⊤ : Subgroup Y) ≠ ⊥ := fun h => hLΓ (le_top.trans (h ▸ bot_le))
  obtain ⟨K, hK⟩ := exists_isComponentOf hcore hpc hY
  have huniq : ∀ K' : Subgroup Y, IsComponentOf K' ⊤ → K' = K :=
    fun K' hK' => eq_of_isComponentOf hp2 hcore S hΓ hNS hK' hK
  have : K.Normal := normal_of_unique hK huniq
  have hZ := center_eq_bot hp hcore hK fun N _ hNp => normal_eq_bot S hΓ hNS hNp
  obtain ⟨hsimple, hnonab⟩ := simple_of_center_eq_bot hK hZ
  have hcatK : IsCatalogGroup K := hcat.simple_subgroup K hsimple hnonab
  have hC := centralizer_eq_bot hcore hpc hK huniq hZ
  have : Group.IsSolvable (Outer K) := Sch K hsimple hnonab hcatK
  have : Group.IsPerfect PSL(2, GaloisField p 2) := isPerfect_psl hp5
  have : Group.IsPerfect L :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hLK : L ≤ K := le_of_isPerfect hC L
  obtain ⟨T, hT⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal S ‹K.Normal›.isSubnormal
  rw [hSU, inf_eq_left.mpr (hUL.le.trans hLK)] at hT
  have hrank : CFSG.Open.pRank p (T : Subgroup K) = 2 := by
    obtain ⟨Q, hQ⟩ := hUL
    rw [← pRank_map_of_injective p hp K.subtype K.subtype_injective, hT, ← hQ,
      pRank_map_of_injective p hp L.subtype L.subtype_injective,
      ← pRank_map_of_injective p hp e.toMonoidHom e.injective]
    have := pRank_sylow_psl (Sylow.mapSurjective (f := e.toMonoidHom) e.surjective Q)
    rwa [Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective Q] at this
  have hgamma : rankThreeGamma 1 p (T : Subgroup K) ≠ ⊤ := by
    have hle : rankThreeGamma 1 p (T : Subgroup K) ≤ Γ.comap K.subtype := by
      refine sSup_le ?_
      rintro _ ⟨D, hDT, hD1, rfl⟩ n hn
      change (n : Y) ∈ Γ
      have hDne : D.map K.subtype ≠ ⊥ := by
        rw [Ne, map_eq_bot_iff_of_injective _ K.subtype_injective]
        rintro rfl
        obtain ⟨E, hE, -, hEc⟩ := pRank_attained p hp (⊥ : Subgroup K)
        rw [le_bot_iff.mp hE, card_bot, ← pow_zero p] at hEc
        have := Nat.pow_right_injective hp.two_le hEc
        omega
      exact hN _ (hT ▸ map_mono hDT) hDne (le_normalizer_map K.subtype ⟨n, hn, rfl⟩)
    intro htop
    rw [htop, top_le_iff] at hle
    refine hLΓ fun l hl => ?_
    have : (⟨l, hLK hl⟩ : K) ∈ Γ.comap K.subtype := hle ▸ mem_top _
    exact this
  have hexK := notSecExcl3 hexcl hK.2.2 hZ
  have hBM : NotBM K :=
    ⟨hexK .B (by simp [sectionExcludedNames3]), hexK .M (by simp [sectionExcludedNames3])⟩
  have hSE := K1 K hsimple hnonab hcatK hBM p hp hp2 T hrank hgamma
  have hW' : W.map (MulAut.conjNormal : Y →* MulAut K) = ⊥ := by
    refine KA p hp hp5 K hsimple hnonab hcatK hSE (hexK .Fi22 (by simp [sectionExcludedNames3]))
      T _ (Nat.Coprime.coprime_dvd_right (card_map_dvd W _) hW) ?_
    intro g hg w hw
    obtain ⟨y, hy, rfl⟩ := hw
    have hconj : MulAut.conj g = MulAut.conjNormal (g : Y) := by
      ext k
      simp [MulAut.conjNormal_apply]
    rw [hconj, ← map_inv, ← map_mul, ← map_mul]
    refine mem_map_of_mem _ ?_
    have hgU : (g : Y) ∈ U := hT ▸ mem_map_of_mem K.subtype hg
    exact (mem_normalizer_iff.mp (hUW hgU) y).mp hy
  exact (map_eq_bot_iff_of_injective W (conjNormal_injective hC)).mp hW'

end GL83Generic5AlmostSimple

theorem gl83Generic5CaseI_holds : GL83Generic5CaseI :=
  fun K1 Sch KA _ _ hp5 _ _ _ hcore hcat hexcl _ _ _ e hUL hUY hΓ hN hLΓ _ hW hUW =>
    GL83Generic5AlmostSimple.eq_bot K1 Sch KA hp5 hcore hcat hexcl e hUL hUY hΓ hN hLΓ hW hUW

end CFSG.LocalAnalysis.RankThreeTheoremC
