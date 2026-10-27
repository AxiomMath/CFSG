module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeToolsSU
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeToolsInner
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeTargets
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoLinThree
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowKleinTools
import CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3Mat
import CFSG.GH74.KGroups.L33
import CFSG.Adapters.TauCetiLieModels
import CFSG.Models.Blueprint
import CFSG.LocalAnalysis.AGLEmbedding.CZeroSubnormalCommute
import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionDatum
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111 Subgroup
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3 (Heis heisEquivBar)
open scoped commutatorElement

theorem perm_three_commute_of_pow_three : ∀ a b : Equiv.Perm (Fin 3), a ^ 3 = 1 → b ^ 3 = 1 →
    a * b = b * a := by decide

section Generic

variable {Y : Type} [Group Y] [Finite Y]

theorem card_inf_and_pow_three_of_linThree {q : TauCeti.PrimePower}
    {d : TauCeti.ValidLieTypeIndex} (hq3 : q.p = 3) (hq1 : q.exponent = 1) (hd : d.1 = .A 2 q)
    {K : Subgroup Y} [K.Normal] (e : ↥K ≃* (TauCeti.CFSGIndex.lie d).Group) (R : Sylow 3 Y) :
    Nat.card ↥((R : Subgroup Y) ⊓ K) = 27 ∧ ∀ u ∈ (R : Subgroup Y) ⊓ K, u ^ 3 = 1 := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hv⟩ := d
  change x = _ at hd
  subst hd
  have hF : Nat.card (GaloisField q.p q.exponent) = 3 := by
    rw [GaloisField.card _ _ (by omega), hq1, pow_one, hq3]
  have eM : (TauCeti.CFSGIndex.lie ⟨.A 2 q, hv⟩).Group ≃*
      projectiveSL 3 (GaloisField q.p q.exponent) :=
    (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 _)
  obtain ⟨T, hT⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal R K
  obtain ⟨S, hS⟩ := exists_sylow_projUnitriangular (K := GaloisField q.p q.exponent) q.p
    (n := 3) (by norm_num)
  have hSp : IsPGroup 3 (projUnitriangular 3 (GaloisField q.p q.exponent)) := by
    have h := S.isPGroup'
    rw [hS] at h
    exact hq3 ▸ h
  have hSi : ¬ 3 ∣ (projUnitriangular 3 (GaloisField q.p q.exponent)).index := by
    have h := S.not_dvd_index
    rw [hS] at h
    exact hq3 ▸ h
  obtain ⟨Φ, hΦ⟩ := exists_mulEquiv_map_eq_sylow (e.trans eM) hSp hSi T
  have hinj : Function.Injective (K.subtype.comp Φ.toMonoidHom) :=
    K.subtype_injective.comp Φ.injective
  have hTY : (projUnitriangular 3 (GaloisField q.p q.exponent)).map
      (K.subtype.comp Φ.toMonoidHom) = (R : Subgroup Y) ⊓ K := by
    rw [← hT, hΦ, ← Subgroup.map_map]
  rw [← hTY]
  refine ⟨?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hinj, card_projUnitriangular, hF]
    norm_num
  · rintro _ ⟨u, hu, rfl⟩
    have hu3 : u ^ 3 = 1 := by
      obtain ⟨h, hh⟩ : ∃ h : Heis (GaloisField q.p q.exponent), heisEquivBar h = ⟨u, hu⟩ :=
        ⟨_, heisEquivBar.apply_symm_apply _⟩
      have h3 : h ^ 3 = 1 :=
        (congrArg (fun k => h ^ k) hq3.symm).trans
          (CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3.Heis.pow_prime_eq_one q.prime_p (by omega) h)
      have : (⟨u, hu⟩ : ↥(projUnitriangular 3 (GaloisField q.p q.exponent))) ^ 3 = 1 := by
        rw [← hh, ← map_pow, h3, map_one]
      simpa using congrArg Subtype.val this
    rw [← map_pow, hu3, map_one]

end Generic

section Solvable

variable {Y I₀ : Type} [Group Y] [Finite Y] [Group I₀] [Finite I₀]

theorem commute_of_le_sup_of_symThree (σ : I₀ →* Y)
    (f : I₀ ⧸ CFSG.pCore 2 I₀ ≃* Equiv.Perm (Fin 3)) {K : Subgroup Y} [K.Normal]
    (hKC : K ⊓ centralizer (K : Set Y) = ⊥)
    (hσC : (CFSG.pCore 2 I₀).map σ ≤ centralizer (K : Set Y)) {Q : Subgroup Y} (hQK : Q ≤ K)
    (hQJ : Q ≤ (CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀)).map σ ⊔
      centralizer (K : Set Y)) :
    ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := by
  set C := centralizer (K : Set Y) with hCdef
  haveI : C.Normal := by rw [hCdef]; infer_instance
  set J := (CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀)).map σ with hJdef
  have hb : IsSymThreeOrSUThreeTwo (I₀ ⧸ CFSG.pCore 2 I₀) := Or.inl ⟨f⟩
  have hJJ : ∀ a ∈ J, ∀ b ∈ J, a * b * a⁻¹ * b⁻¹ ∈ C := by
    rintro _ ⟨g₁, hg₁, rfl⟩ _ ⟨g₂, hg₂, rfl⟩
    have hc : ∀ g ∈ CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀),
        f (g : I₀ ⧸ CFSG.pCore 2 I₀) ^ 3 = 1 := by
      intro g hg
      rw [← map_pow, ← QuotientGroup.mk_pow,
        (QuotientGroup.eq_one_iff _).mpr (cube_mem_pCore_two hb g hg), map_one]
    have hcomm := perm_three_commute_of_pow_three _ _ (hc g₁ hg₁) (hc g₂ hg₂)
    have h1 : ((g₁ * g₂ * g₁⁻¹ * g₂⁻¹ : I₀) : I₀ ⧸ CFSG.pCore 2 I₀) = 1 := by
      apply f.injective
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm, map_one]
      group
    have h2 := hσC (Subgroup.mem_map_of_mem σ ((QuotientGroup.eq_one_iff _).mp h1))
    simpa only [map_mul, map_inv] using h2
  have hJC : ∀ a ∈ J ⊔ C, ∀ b ∈ J ⊔ C, a * b * a⁻¹ * b⁻¹ ∈ C := by
    intro a ha b hb'
    rw [← SetLike.mem_coe, Subgroup.mul_normal J C] at ha hb'
    obtain ⟨j₁, hj₁, c₁, hc₁, rfl⟩ := Set.mem_mul.mp ha
    obtain ⟨j₂, hj₂, c₂, hc₂, rfl⟩ := Set.mem_mul.mp hb'
    have e1 : (c₁ : Y ⧸ C) = 1 := (QuotientGroup.eq_one_iff c₁).mpr hc₁
    have e2 : (c₂ : Y ⧸ C) = 1 := (QuotientGroup.eq_one_iff c₂).mpr hc₂
    have h1 := (QuotientGroup.eq_one_iff _).mpr (hJJ j₁ hj₁ j₂ hj₂)
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, e1, e2, mul_one] at h1 ⊢
    exact h1
  intro x hx y hy
  have h1 : x * y * x⁻¹ * y⁻¹ ∈ K ⊓ C :=
    ⟨K.mul_mem (K.mul_mem (K.mul_mem (hQK hx) (hQK hy)) (K.inv_mem (hQK hx)))
      (K.inv_mem (hQK hy)), hJC x (hQJ hx) y (hQJ hy)⟩
  rw [hKC, Subgroup.mem_bot] at h1
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = y * x := by rw [h1, one_mul]

end Solvable

section Certified


theorem threeFourSolvThreeLinThree_holds : ThreeFourSolvThreeLinThree := by
  intro q d hq3 hq1 hd Y _ _ K Y₀ E R I₀ _ _ σ hK hKX hZ _ hrkC hC hcomp hER hE hEc hcore hO2
    hker hσY hσs hb hcond hdir
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := hK
  set C := centralizer (K : Set Y) with hCdef
  haveI : C.Normal := by rw [hCdef]; infer_instance
  have hKC := CFSG.QuasithinUnique.RankOneRecog.inf_centralizer_eq_bot_of_center_eq_bot hZ
  have hrkC' : CFSG.Open.pRank 3 C ≤ 1 := by
    rwa [CFSG.SectionRank.pRank_coe_eq_openPRank] at hrkC
  have hσC : (CFSG.pCore 2 I₀).map σ ≤ C := (map_pCore_two_le_pCoreOf σ hσs).trans hO2
  obtain ⟨eK⟩ := hKX
  have hLie : CFSG.Blueprint.LieModel ↥K .PSL 3 3 1 := by
    obtain ⟨x, hv⟩ := d
    change x = _ at hd
    subst hd
    have h := CFSG.Models.lieModel_A 2 q hv eK
    rw [hq3, hq1] at h
    exact CFSG.Models.LieModel.toBlueprint (by decide) h
  obtain ⟨e'⟩ := CFSG.GH74.KGroups.L33.equiv_of_lieModel hLie
  have hcent : ∀ R' : Subgroup (MulAut ↥K), CFSG.GH74.KGroups.ElemAb 3 R' → Nat.card R' = 9 →
      ∀ ψ : MulAut ↥K, ψ ^ 2 = 1 → (∀ r ∈ R', ψ * r = r * ψ) → ψ = 1 :=
    fun R' hR' hc ψ hψ h => CFSG.GH74.KGroups.L33.autCentralizer e' R' hR' hc ψ hψ h
  have hX3 : ∀ α : MulAut ↥K, α ^ 3 = 1 → ∃ g : ↥K, α = MulAut.conj g := fun α hα => by
    obtain ⟨k, hk⟩ := CFSG.GH74.KGroups.L33.inner3 e' α hα
    exact ⟨k, MulEquiv.ext fun x => by rw [hk x, MulAut.conj_apply]⟩
  have hinner : ∀ y ∈ σ.range, y ^ 3 = 1 → ∃ k ∈ K, ∃ c ∈ C, y = k * c :=
    fun y _ h => exists_mul_of_pow_three hX3 h
  by_cases hs3 : ¬ Nonempty (I₀ ⧸ CFSG.pCore 2 I₀ ≃* Equiv.Perm (Fin 3))
  · have hA : ∀ Q : Subgroup (MulAut ↥K), IsPGroup 3 Q → Nat.card Q ≤ 27 := by
      intro Q hQ
      haveI := CFSG.GH74.KGroups.L33.finite_mulAut e'
      have hdvd : Nat.card Q ∣ 11232 := by
        rw [← CFSG.GH74.KGroups.L33.card_mulAut e']
        exact Subgroup.card_subgroup_dvd_card Q
      obtain ⟨a, ha⟩ := hQ.exists_card_eq
      rw [ha] at hdvd ⊢
      have ha3 : a ≤ 3 := by
        by_contra h
        have h81 : 3 ^ 4 ∣ 11232 := (pow_dvd_pow 3 (by omega)).trans hdvd
        norm_num at h81
      calc 3 ^ a ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) ha3
        _ = 27 := by norm_num
    exact (false_of_not_symThree_of_card_le σ hb hs3 hker hKC hrkC' hinner hA hcond).elim
  push Not at hs3
  obtain ⟨f⟩ := hs3
  set J := (CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀)).map σ with hJdef
  rcases SolvNone.le_centralizer_or_le_of_inner σ hZ hinner
      (fun Q hQK hQJ _ => commute_of_le_sup_of_symThree σ f hKC hσC hQK hQJ) hrkC hC hO2 hker
      hσY hσs hb with h | ⟨hJK, y₀, hy₀K, hy₀3, hJy₀⟩
  · exact h
  by_contra hJC
  have hJne : J ≠ ⊥ := fun h => hJC (by rw [h]; exact bot_le)
  have hy₀1 : y₀ ≠ 1 := fun h => hJne (eq_bot_iff.mpr (hJy₀.trans (by
    rw [h, zpowers_one_eq_bot])))
  have hcardz : Nat.card (zpowers y₀) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hy₀3 hy₀1]
  have hJeq : J = zpowers y₀ := by
    refine Subgroup.eq_of_le_of_card_ge hJy₀ ?_
    rw [hcardz]
    have h1 : Nat.card J ∣ 3 := hcardz ▸ Subgroup.card_dvd_of_le hJy₀
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact absurd (Subgroup.eq_bot_of_card_eq J h) hJne
    · omega
  have hJcard : Nat.card J = 3 := by rw [hJeq, hcardz]
  have hy₀J : y₀ ∈ J := hJeq ▸ mem_zpowers y₀
  have hy₀S : y₀ ∈ σ.range := (Subgroup.map_le_range σ _) hy₀J
  obtain ⟨t, htS, ⟨m, htm⟩, htw⟩ := exists_two_pow_inv_of_symThree σ f hσC hy₀S
    (Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hy₀3))
  have hty : t * y₀ * t⁻¹ = y₀⁻¹ := by
    have h1 : t * y₀ * t⁻¹ * y₀ ∈ K ⊓ C := ⟨K.mul_mem (hK.conj_mem y₀ hy₀K t) hy₀K, htw⟩
    rw [hKC, Subgroup.mem_bot] at h1
    exact eq_inv_of_mul_eq_one_left h1
  have hty' : t⁻¹ * y₀ * t = y₀⁻¹ := by
    have h1 : t⁻¹ * y₀⁻¹ * t = y₀ := by
      rw [← hty]
      group
    calc t⁻¹ * y₀ * t = (t⁻¹ * y₀⁻¹ * t)⁻¹ := by group
      _ = y₀⁻¹ := by rw [h1]
  have htY : t ∈ Y₀ := hσY htS
  set T : Subgroup Y := (R : Subgroup Y) ⊓ K with hTdef
  obtain ⟨hT27, hT3⟩ := card_inf_and_pow_three_of_linThree hq3 hq1 hd eK R
  have hTp : IsPGroup 3 T := IsPGroup.of_card (n := 3) (by rw [hT27]; norm_num)
  have hNR : normalizer ((R : Subgroup Y) : Set Y) ≤ Y₀ :=
    (normalizer_sylow_le_threeFourCore Nat.prime_three R hER hE hEc).trans hcore
  have hTY : T ≤ Y₀ := inf_le_left.trans (Subgroup.le_normalizer.trans hNR)
  suffices htN : t ∈ normalizer (T : Set Y) by
    have htC : t ∈ C := mem_centralizer_of_symThree_of_forall σ f hcent hKC hσs inf_le_right
      hT27 hT3 hTY htS htN htm
    have h1 : t * y₀ * t⁻¹ = y₀ := by
      rw [← Subgroup.mem_centralizer_iff.mp htC y₀ hy₀K, mul_inv_cancel_right]
    have h2 : y₀ = y₀⁻¹ := h1.symm.trans hty
    apply hy₀1
    have h3 : y₀ * y₀ = 1 := by
      calc y₀ * y₀ = y₀ * y₀⁻¹ := by rw [← h2]
        _ = 1 := mul_inv_cancel y₀
    calc y₀ = y₀ ^ 3 * (y₀ * y₀)⁻¹ := by group
      _ = 1 := by rw [hy₀3, h3]; group
  obtain ⟨hXs, ⟨a, b, hab⟩, -⟩ := linThree_catalog_facts Nat.prime_three hq3 hq1 hd
  haveI : IsSimpleGroup ↥K := (MulEquiv.isSimpleGroup_congr eK).2 hXs
  have hnab : ∃ a b : ↥K, a * b ≠ b * a :=
    ⟨eK.symm a, eK.symm b, fun h => hab (by simpa using congrArg eK h)⟩
  have hKnle : ¬ K ≤ Y₀ := by
    refine hcomp K ?_ le_rfl
    haveI : Group.IsPerfect ↥K := ⟨CFSG.ComponentClassification.Helpers.commutator_eq_top ↥K hnab⟩
    exact ⟨le_top, IsSubnormal.step le_top inferInstance (IsSubnormal.refl ⊤),
      CFSG.ComponentClassification.Quasisimple.simple_of_perfect ↥K⟩
  obtain ⟨N, hNH, hNp, hHN, hCN⟩ := threeFourTwoLinThree_inf Nat.prime_three (by norm_num) hq3
    hq1 hd R hK ⟨eK⟩ hER hE hEc hcore hKnle
  set H : Subgroup Y := K ⊓ Y₀ with hHdef
  set V : Subgroup Y := pCoreOf 3 H with hVdef
  have hVp : IsPGroup 3 V := CFSG.LieType.BorelTits.pCoreOf_isPGroup 3 H
  have hVH : V ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 3 H
  have hNV : N ≤ V := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 3 hNH hHN hNp
  have hCV : centralizer (V : Set Y) ⊓ H ≤ V := fun x hx =>
    hNV (hCN ⟨Subgroup.centralizer_le hNV hx.1, hx.2⟩)
  have hY₀H : Y₀ ≤ normalizer (H : Set Y) := fun g hg =>
    Subgroup.mem_normalizer_fintype fun x hx =>
      ⟨hK.conj_mem x hx.1 g, Y₀.mul_mem (Y₀.mul_mem hg hx.2) (Y₀.inv_mem hg)⟩
  have hY₀V : Y₀ ≤ normalizer (V : Set Y) :=
    hY₀H.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 3 H)
  have hHV : H ≤ normalizer (V : Set Y) := inf_le_right.trans hY₀V
  have hJp : IsPGroup 3 J := by
    rw [hJeq]
    exact isPGroup_zpowers_of_pow_eq_one (n := 1) (by rwa [pow_one])
  have hJV : J ≤ V := by
    have h1 := CFSG.AGLEmbedding.SubnormalCommute.le_pCoreOf_of_isSubnormal
      (isSubnormal_oUpperTwo_map σ hσs) hJp
    refine (le_inf h1 hJK).trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 3
      (le_inf inf_le_right (inf_le_left.trans (CFSG.LieType.BorelTits.pCoreOf_le 3 Y₀)))
      (fun h hh => Subgroup.mem_normalizer_fintype fun x hx => ⟨?_, hK.conj_mem _ hx.2 h⟩)
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 3 Y₀).to_le inf_le_left))
    exact (mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 3 Y₀ hh.2) x).mp
      hx.1
  obtain ⟨T₀, hT₀⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal R K
  have hTH : T ≤ H := le_inf inf_le_right hTY
  have hTmax : ∀ A : Subgroup Y, A ≤ K → IsPGroup 3 A → T ≤ A → A ≤ T := by
    intro A hAK hAp hTA
    have hmax := T₀.is_maximal' (hAp.comap_of_injective K.subtype K.subtype_injective) (by
      intro x hx
      rw [Subgroup.mem_comap]
      refine hTA ?_
      rw [hTdef, ← hT₀]
      exact ⟨x, hx, rfl⟩)
    intro a ha
    have : (⟨a, hAK ha⟩ : ↥K) ∈ (T₀ : Subgroup ↥K) := by
      rw [← hmax]
      exact ha
    rw [hTdef, ← hT₀]
    exact ⟨_, this, rfl⟩
  have hVT : V ≤ T := by
    have hp : IsPGroup 3 ↥(V ⊔ T) := hVp.to_sup_of_normal_left' hTp (hTH.trans hHV)
    exact le_sup_left.trans (hTmax _ (sup_le (hVH.trans inf_le_left) inf_le_right) hp
      le_sup_right)
  by_cases hV27 : Nat.card V = 27
  ·
    have hVeq : V = T := Subgroup.eq_of_le_of_card_ge hVT (by rw [hT27, hV27])
    rw [← hVeq]
    exact hY₀V htY
  have hV9 : Nat.card V ≤ 9 := by
    have hdvd : Nat.card V ∣ 27 := hT27 ▸ Subgroup.card_dvd_of_le hVT
    obtain ⟨a, ha⟩ := hVp.exists_card_eq
    rw [ha] at hdvd hV27 ⊢
    have ha3 : a ≤ 3 := by
      by_contra h
      have h4 : 3 ^ 4 ∣ 27 := (pow_dvd_pow 3 (by omega)).trans hdvd
      norm_num at h4
    have ha2 : a ≤ 2 := by
      by_contra h
      apply hV27
      rw [show a = 3 by omega]
      norm_num
    calc 3 ^ a ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) ha2
      _ = 9 := by norm_num
  have hO2J : CFSG.pCore 2 ↥J = ⊥ := by
    have h2 : IsPGroup 2 (CFSG.pCore 2 ↥J) := CFSG.pCore_isPGroup
    have h3 : IsPGroup 3 (⊤ : Subgroup ↥J) := (hJp.of_equiv Subgroup.topEquiv.symm)
    rw [eq_bot_iff]
    intro x hx
    exact (IsPGroup.disjoint_of_ne 2 3 (by norm_num) _ _ h2 h3).le_bot ⟨hx, Subgroup.mem_top _⟩
  have hcardJq : Nat.card (↥J ⧸ CFSG.pCore 2 ↥J) = 3 := by
    rw [hO2J, Nat.card_congr (QuotientGroup.quotientBot).toEquiv, hJcard]
  have hD'V : (⨆ y ∈ Y₀, J.map (MulAut.conj y).toMonoidHom) ≤ V := iSup₂_le fun y hy => by
    rintro _ ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using (mem_normalizer_iff.mp (hY₀V hy) x).mp (hJV hx)
  have hh : ((normalizer (J : Set Y) ⊓ Y₀).subgroupOf Y₀).index ≤ 2 := by
    have hd' := hdir
    unfold SolvThreeDirectCond at hd'
    rw [hcardJq] at hd'
    have h9 : 3 ^ ((normalizer (J : Set Y) ⊓ Y₀).subgroupOf Y₀).index ≤ 3 ^ 2 := by
      rw [← hd']
      calc _ ≤ Nat.card ↥(⨆ y ∈ Y₀, J.map (MulAut.conj y).toMonoidHom) :=
            Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
        _ ≤ Nat.card V := Subgroup.card_le_of_le hD'V
        _ ≤ 3 ^ 2 := by norm_num; exact hV9
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h9
  have hTN : ∀ u ∈ T, u ∈ normalizer (J : Set Y) := by
    intro u hu
    have huY : u ∈ Y₀ := hTY hu
    set M := (normalizer (J : Set Y) ⊓ Y₀).subgroupOf Y₀ with hM
    suffices h : (⟨u, huY⟩ : ↥Y₀) ∈ M from (Subgroup.mem_subgroupOf.mp h).1
    have hidx : M.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    obtain ⟨n, hn⟩ := hTp ⟨u, hu⟩
    have hun : u ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
    rcases (show M.index = 1 ∨ M.index = 2 by omega) with h1 | h2
    · rw [Subgroup.index_eq_one.mp h1]
      exact Subgroup.mem_top _
    · obtain ⟨k, hk⟩ : Odd (3 ^ n) := Odd.pow (by decide)
      have he : (⟨u, huY⟩ : ↥Y₀) = ((⟨u, huY⟩ : ↥Y₀) ^ 2) ^ (k + 1) := by
        apply Subtype.ext
        simp only [SubgroupClass.coe_pow]
        rw [← pow_mul, show 2 * (k + 1) = 3 ^ n + 1 by omega, pow_succ, hun, one_mul]
      rw [he]
      exact M.pow_mem (Subgroup.sq_mem_of_index_two h2 _) _
  have hTJ : ∀ u ∈ T, u * y₀ = y₀ * u := by
    intro u hu
    obtain ⟨n, hn⟩ := hTp ⟨u, hu⟩
    have hun : u ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have huN : u ∈ normalizer (zpowers y₀ : Set Y) := by
      rw [← hJeq]
      exact hTN u hu
    exact (commute_of_mem_normalizer_zpowers_of_pow_prime_pow Nat.prime_three
      (orderOf_eq_prime hy₀3 hy₀1) huN hun).eq
  have hcz : ∀ g : Y, g * y₀ = y₀ * g → ∀ z ∈ zpowers y₀, g * z * g⁻¹ = z := by
    intro g hg z hz
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
    rw [(Commute.zpow_right (show Commute g y₀ from hg) k).eq, mul_inv_cancel_right]
  have hJT : zpowers y₀ ≤ T := hJeq ▸ (hJV.trans hVT)
  have hTcomm : ∀ u ∈ T, ∀ w ∈ T, u * w * u⁻¹ * w⁻¹ ∈ zpowers y₀ := by
    set J' : Subgroup ↥T := (zpowers y₀).subgroupOf T with hJ'
    have hJ'c : J' ≤ center ↥T := by
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro g
      have hx' : (x : Y) ∈ zpowers y₀ := Subgroup.mem_subgroupOf.mp hx
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      have := hcz g (hTJ g g.2) _ hx'
      calc (g : Y) * x = ((g : Y) * x * (g : Y)⁻¹) * g := by group
        _ = x * g := by rw [this]
    haveI : J'.Normal := Subgroup.normal_of_le_center hJ'c
    have hJ'card : Nat.card J' = 3 := by
      rw [hJ', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJT).toEquiv, hcardz]
    have hq : Nat.card (↥T ⧸ J') = 3 ^ 2 := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup J'
      rw [hT27, hJ'card] at h1
      omega
    intro u hu w hw
    have hc := IsPGroup.commutative_of_card_eq_prime_sq (p := 3) hq
      ((⟨u, hu⟩ : ↥T) : ↥T ⧸ J') ((⟨w, hw⟩ : ↥T) : ↥T ⧸ J')
    have h1 : ((⟨u, hu⟩ * ⟨w, hw⟩ * (⟨u, hu⟩ : ↥T)⁻¹ * (⟨w, hw⟩ : ↥T)⁻¹ : ↥T) :
        ↥T ⧸ J') = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv, hc]
      group
    have h2 := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
    simpa using h2
  let A : Subgroup Y :=
    { carrier := {h | h ∈ H ∧ h * y₀ = y₀ * h ∧ ∀ v ∈ V, h * v * h⁻¹ * v⁻¹ ∈ zpowers y₀}
      mul_mem' := by
        rintro a b ⟨haH, hay, hav⟩ ⟨hbH, hby, hbv⟩
        refine ⟨H.mul_mem haH hbH, ?_, fun v hv => ?_⟩
        · calc a * b * y₀ = a * (b * y₀) := by group
            _ = a * (y₀ * b) := by rw [hby]
            _ = (a * y₀) * b := by group
            _ = (y₀ * a) * b := by rw [hay]
            _ = y₀ * (a * b) := by group
        · have he : a * b * v * (a * b)⁻¹ * v⁻¹ =
              (a * (b * v * b⁻¹ * v⁻¹) * a⁻¹) * (a * v * a⁻¹ * v⁻¹) := by group
          rw [he, hcz a hay _ (hbv v hv)]
          exact Subgroup.mul_mem _ (hbv v hv) (hav v hv)
      one_mem' := ⟨H.one_mem, by group, fun v _ => by simp⟩
      inv_mem' := by
        rintro a ⟨haH, hay, hav⟩
        refine ⟨H.inv_mem haH, ?_, fun v hv => ?_⟩
        · calc a⁻¹ * y₀ = a⁻¹ * (y₀ * a) * a⁻¹ := by group
            _ = a⁻¹ * (a * y₀) * a⁻¹ := by rw [hay]
            _ = y₀ * a⁻¹ := by group
        · have hw : a⁻¹ * v * a ∈ V := by
            have := (mem_normalizer_iff.mp (hHV (H.inv_mem haH)) v).mp hv
            simpa using this
          have h1 := hav _ hw
          have he : a * (a⁻¹ * v * a) * a⁻¹ * (a⁻¹ * v * a)⁻¹ = (a⁻¹ * v * a⁻¹⁻¹ * v⁻¹)⁻¹ := by
            group
          rw [he] at h1
          exact (zpowers y₀).inv_mem_iff.mp h1 }
  have hAH : A ≤ H := fun a ha => ha.1
  have hAp : IsPGroup 3 A := by
    rintro ⟨a, haH, hay, hav⟩
    have ha3 : a ^ 3 ∈ centralizer (V : Set Y) := by
      refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
      set j := a * v * a⁻¹ * v⁻¹ with hjdef
      have hjz : j ∈ zpowers y₀ := hav v hv
      have hj : a * v * a⁻¹ = j * v := by rw [hjdef]; group
      have hja : a * j * a⁻¹ = j := hcz a hay j hjz
      have hj3 : j ^ 3 = 1 := by
        obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hjz
        rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy₀3, one_zpow]
      have hj3' : j * j * j = 1 := by rw [← hj3, pow_succ, pow_two]
      have e3 : a * a * a * v * (a * a * a)⁻¹ = v := by
        calc a * a * a * v * (a * a * a)⁻¹ = a * (a * (a * v * a⁻¹) * a⁻¹) * a⁻¹ := by group
          _ = a * (a * (j * v) * a⁻¹) * a⁻¹ := by rw [hj]
          _ = a * ((a * j * a⁻¹) * (a * v * a⁻¹)) * a⁻¹ := by group
          _ = a * (j * (j * v)) * a⁻¹ := by rw [hja, hj]
          _ = (a * j * a⁻¹) * (a * j * a⁻¹) * (a * v * a⁻¹) := by group
          _ = j * j * (j * v) := by rw [hja, hj]
          _ = (j * j * j) * v := by group
          _ = v := by rw [hj3', one_mul]
      rw [pow_succ, pow_two]
      calc v * (a * a * a) = (a * a * a * v * (a * a * a)⁻¹) * (a * a * a) := by rw [e3]
        _ = a * a * a * v := by group
    have ha3V : a ^ 3 ∈ V := hCV ⟨ha3, H.pow_mem haH 3⟩
    obtain ⟨k, hk⟩ := hVp ⟨a ^ 3, ha3V⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have hk' : (a ^ 3) ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [pow_succ', pow_mul, hk']
  have hTA : T ≤ A := fun u hu => ⟨hTH hu, hTJ u hu, fun v hv => hTcomm u hu v (hVT hv)⟩
  have hAT : A ≤ T := hTmax A (hAH.trans inf_le_left) hAp hTA
  refine Subgroup.mem_normalizer_fintype fun u hu => hAT ⟨?_, ?_, fun v hv => ?_⟩
  · exact (mem_normalizer_iff.mp (hY₀H htY) u).mp (hTH hu)
  · have hu' : u * y₀⁻¹ = y₀⁻¹ * u := (Commute.inv_right (show Commute u y₀ from hTJ u hu)).eq
    have h1 : t * u * t⁻¹ * y₀ * (t * u * t⁻¹)⁻¹ = y₀ := by
      calc t * u * t⁻¹ * y₀ * (t * u * t⁻¹)⁻¹ = t * u * (t⁻¹ * y₀ * t) * u⁻¹ * t⁻¹ := by group
        _ = t * (u * y₀⁻¹) * u⁻¹ * t⁻¹ := by rw [hty']; group
        _ = t * (y₀⁻¹ * u) * u⁻¹ * t⁻¹ := by rw [hu']
        _ = (t * y₀ * t⁻¹)⁻¹ := by group
        _ = y₀ := by rw [hty, inv_inv]
    calc t * u * t⁻¹ * y₀ = (t * u * t⁻¹ * y₀ * (t * u * t⁻¹)⁻¹) * (t * u * t⁻¹) := by group
      _ = y₀ * (t * u * t⁻¹) := by rw [h1]
  · have hv' : t⁻¹ * v * t ∈ V := by
      have := (mem_normalizer_iff.mp (hY₀V (Y₀.inv_mem htY)) v).mp hv
      simpa using this
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hTcomm u hu _ (hVT hv'))
    have he : t * u * t⁻¹ * v * (t * u * t⁻¹)⁻¹ * v⁻¹ =
        t * (u * (t⁻¹ * v * t) * u⁻¹ * (t⁻¹ * v * t)⁻¹) * t⁻¹ := by group
    rw [he, ← hk, ← conj_zpow, hty]
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (mem_zpowers y₀)) k

end Certified

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
