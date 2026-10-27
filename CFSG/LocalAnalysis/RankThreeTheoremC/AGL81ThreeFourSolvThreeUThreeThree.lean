module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeUnitary
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeToolsSU
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeTargets
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Proved
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.U33Proved
import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoUThree
import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionDatum
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenSevenFourL34Of
import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairA6Atlas
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.GH74.KGroups.U33
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.TightCensus
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeTools

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped commutatorElement

section Generic

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_mul_of_mem_normalizer {K : Subgroup Y} [K.Normal] (hK : IsRankThreeU3 ↥K)
    (hKC : K ⊓ centralizer (K : Set Y) = ⊥) {U : Subgroup Y} (hUK : U ≤ K)
    (hU27 : Nat.card U = 27) {w : Y} (hw : w ∈ normalizer (U : Set Y)) {n : ℕ}
    (hwn : w ^ 3 ^ n = 1) : ∃ k ∈ U, ∃ c ∈ centralizer (K : Set Y), w = k * c := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨θ, hθ⟩ : ∃ θ : Y →* MulAut K, θ = MulAut.conjNormal := ⟨_, rfl⟩
  have hθ1 : ∀ a : Y, θ a = 1 ↔ a ∈ centralizer (K : Set Y) := fun a => by
    rw [hθ]; exact conjNormal_eq_one_iff
  have hθU : ∀ u ∈ U, θ u = 1 → u = 1 := fun u hu h1 => by
    have : u ∈ K ⊓ centralizer (K : Set Y) := ⟨hUK hu, (hθ1 u).mp h1⟩
    rwa [hKC, Subgroup.mem_bot] at this
  have hU1 : Nat.card (U.map θ) = 27 := by rw [card_map_of_forall_eq_one θ hθU, hU27]
  have hUp : IsPGroup 3 (U.map θ) := IsPGroup.of_card (n := 3) (by rw [hU1]; norm_num)
  have hzp : IsPGroup 3 (zpowers (θ w)) :=
    isPGroup_zpowers_of_pow_eq_one (by rw [← map_pow, hwn, map_one])
  have hθw : θ w ∈ normalizer ((U.map θ : Subgroup (MulAut K)) : Set (MulAut K)) :=
    Subgroup.le_normalizer_map θ (Subgroup.mem_map_of_mem θ hw)
  have hsup := hUp.to_sup_of_normal_left' hzp (zpowers_le.mpr hθw)
  have hdvd := u3AutData_proved ↥K hK _ hsup
  have hfin : Finite ↥(U.map θ ⊔ zpowers (θ w)) :=
    Nat.finite_of_card_ne_zero fun h => by rw [h] at hdvd; norm_num at hdvd
  have heq : U.map θ = U.map θ ⊔ zpowers (θ w) :=
    Subgroup.eq_of_le_of_card_ge le_sup_left
      (by rw [hU1]; exact (Nat.le_of_dvd (by norm_num) hdvd).trans (by norm_num))
  have hmem : θ w ∈ U.map θ := by
    rw [heq]
    exact mem_sup_right (mem_zpowers _)
  obtain ⟨k, hk, hkw⟩ := hmem
  refine ⟨k, hk, k⁻¹ * w, (hθ1 _).mp ?_, by group⟩
  rw [map_mul, map_inv, hkw, inv_mul_cancel]

end Generic

section Solvable

variable {Y I₀ : Type} [Group Y] [Finite Y] [Group I₀] [Finite I₀]

theorem le_centralizer_of_symThree (σ : I₀ →* Y)
    (f : I₀ ⧸ CFSG.pCore 2 I₀ ≃* Equiv.Perm (Fin 3)) {K Y₀ U : Subgroup Y} [K.Normal]
    (e : ↥K ≃* CFSG.GH74.KGroups.U33.QP.originalSubgroup)
    (hKC : K ⊓ centralizer (K : Set Y) = ⊥)
    (hσC : (CFSG.pCore 2 I₀).map σ ≤ centralizer (K : Set Y))
    (hσY : σ.range ≤ Y₀) (hσs : IsSubnormal σ.range Y₀)
    (hUK : U ≤ K) (hU27 : Nat.card U = 27) (hU3 : ∀ u ∈ U, u ^ 3 = 1) (hUY : U ≤ Y₀)
    (hY₀U : Y₀ ≤ normalizer (U : Set Y)) :
    (CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀)).map σ ≤
      centralizer (K : Set Y) := by
  set C := centralizer (K : Set Y) with hCdef
  haveI : C.Normal := by rw [hCdef]; infer_instance
  have hb : IsSymThreeOrSUThreeTwo (I₀ ⧸ CFSG.pCore 2 I₀) := Or.inl ⟨f⟩
  refine oUpperTwo_map_le_of_odd σ fun y hy hodd => ?_
  have hy3 := pow_three_eq_one_of_mem_range_of_odd σ hb hy hodd
  obtain ⟨t, htS, ⟨m, htm⟩, htw⟩ := exists_two_pow_inv_of_symThree σ f hσC hy hodd
  have htC : t ∈ C := mem_centralizer_of_symThree_of_forall σ f
    (fun R hR hc ψ hψ h => CFSG.GH74.KGroups.U33.autCentralizer e R hR hc ψ hψ h) hKC hσs hUK
    hU27 hU3 hUY htS (hY₀U (hσY htS)) htm
  have hy2 : y ^ 2 ∈ C := by
    have h1 : y * t⁻¹ * y ∈ C := by
      have h0 := C.mul_mem (C.inv_mem htC) htw
      have he : t⁻¹ * (t * y * t⁻¹ * y) = y * t⁻¹ * y := by group
      rwa [he] at h0
    have h2 : y * t⁻¹ * y⁻¹ ∈ C := (inferInstance : C.Normal).conj_mem _ (C.inv_mem htC) y
    have h3 := C.mul_mem (C.inv_mem h2) h1
    have he : (y * t⁻¹ * y⁻¹)⁻¹ * (y * t⁻¹ * y) = y ^ 2 := by rw [pow_two]; group
    rwa [he] at h3
  have hye : y = (y ^ 2) ^ 2 := by
    calc y = y ^ 3 * y := by rw [hy3, one_mul]
      _ = (y ^ 2) ^ 2 := by group
  rw [hye]
  exact C.pow_mem hy2 2

theorem false_of_not_symThree (σ : I₀ →* Y) (hb : IsSymThreeOrSUThreeTwo (I₀ ⧸ CFSG.pCore 2 I₀))
    (hs3 : ¬ Nonempty (I₀ ⧸ CFSG.pCore 2 I₀ ≃* Equiv.Perm (Fin 3)))
    (hker : Nat.Coprime 3 (Nat.card σ.ker)) {K Y₀ U : Subgroup Y} [K.Normal]
    (hK : IsRankThreeU3 ↥K) (hKC : K ⊓ centralizer (K : Set Y) = ⊥)
    (hrkC : CFSG.Open.pRank 3 (centralizer (K : Set Y)) ≤ 1)
    (hσY : σ.range ≤ Y₀) (hUK : U ≤ K) (hU27 : Nat.card U = 27)
    (hY₀U : Y₀ ≤ normalizer (U : Set Y)) (hcond : SolvThreeAutCond Y₀ σ) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := centralizer (K : Set Y) with hCdef
  haveI : C.Normal := by rw [hCdef]; infer_instance
  obtain ⟨θ, hθ⟩ : ∃ θ : Y →* MulAut K, θ = MulAut.conjNormal := ⟨_, rfl⟩
  have hθ1 : ∀ a : Y, θ a = 1 ↔ a ∈ C := fun a => by
    rw [hθ]; exact conjNormal_eq_one_iff
  have h216 := card_quotient_pCore_of_not_symThree hb hs3
  have hdec : ∀ w ∈ Y₀, (∃ n : ℕ, w ^ 3 ^ n = 1) → ∃ k ∈ U, ∃ c ∈ C, w = k * c :=
    fun w hw ⟨_, hn⟩ => exists_mul_of_mem_normalizer hK hKC hUK hU27 (hY₀U hw) hn
  have hθU : ∀ u ∈ U, θ u = 1 → u = 1 := fun u hu h1 => by
    have : u ∈ K ⊓ C := ⟨hUK hu, (hθ1 u).mp h1⟩
    rwa [hKC, Subgroup.mem_bot] at this
  have hU1 : Nat.card (U.map θ) = 27 := by rw [card_map_of_forall_eq_one θ hθU, hU27]
  have hsyl : ∀ P₀ : Sylow 3 I₀, ((P₀ : Subgroup I₀).map σ).map θ = U.map θ ∧
      ∀ z ∈ (P₀ : Subgroup I₀).map σ, z ∈ C → z = 1 := by
    intro P₀
    set P : Subgroup Y := (P₀ : Subgroup I₀).map σ with hP
    have hPS : P ≤ σ.range := Subgroup.map_le_range σ _
    have hP3e : ∀ x ∈ P, ∃ n : ℕ, x ^ 3 ^ n = 1 := by
      rintro _ ⟨u, hu, rfl⟩
      obtain ⟨n, hn⟩ := P₀.isPGroup' ⟨u, hu⟩
      have hun : u ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
      exact ⟨n, by rw [← map_pow, hun, map_one]⟩
    have hP3 : ∀ x ∈ P, x ^ 3 = 1 := by
      intro x hx
      obtain ⟨n, hn⟩ := hP3e x hx
      exact pow_three_eq_one_of_mem_range_of_odd σ hb (hPS hx)
        (Odd.of_dvd_nat (Odd.pow (by decide)) (orderOf_dvd_of_pow_eq_one hn))
    have hPdec : ∀ x ∈ P, ∃ k ∈ U, ∃ c ∈ C, x = k * c := fun x hx =>
      hdec x (hσY (hPS hx)) (hP3e x hx)
    have hPle : P.map θ ≤ U.map θ := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨k, hk, c, hc, rfl⟩ := hPdec x hx
      refine ⟨k, hk, ?_⟩
      rw [map_mul, (hθ1 c).mpr hc, mul_one]
    have hPKC : P ≤ K ⊔ C := fun x hx => by
      obtain ⟨k, hk, c, hc, rfl⟩ := hPdec x hx
      exact mul_mem_sup (hUK hk) hc
    have hPnc : ¬ ∀ x ∈ P.map θ, ∀ y ∈ P.map θ, x * y = y * x := by
      intro hab
      apply not_comm_map_sylow σ hb hs3 hker P₀
      refine commute_of_commutator_mem hKC hrkC hP3 hPKC fun x hx y hy => (hθ1 _).mp ?_
      rw [map_mul, map_mul, map_mul, map_inv, map_inv,
        hab _ (Subgroup.mem_map_of_mem θ hx) _ (Subgroup.mem_map_of_mem θ hy)]
      group
    have hPeq : P.map θ = U.map θ := eq_of_le_of_not_comm hPle hU1 hPnc
    refine ⟨hPeq, fun z hz hzC => ?_⟩
    have hPp : IsPGroup 3 P := P₀.isPGroup'.map σ
    have hPcard : Nat.card P ≤ 27 := by
      have hdvd := card_dvd_card_quotient_of_isPGroup σ hPp hPS
      rw [h216] at hdvd
      obtain ⟨a, ha⟩ := hPp.exists_card_eq
      rw [ha] at hdvd ⊢
      have ha3 : a ≤ 3 := by
        by_contra h
        have h81 : 3 ^ 4 ∣ 216 := (pow_dvd_pow 3 (by omega)).trans hdvd
        norm_num at h81
      calc 3 ^ a ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) ha3
        _ = 27 := by norm_num
    have hbij := (θ.subgroupMap_surjective P).bijective_of_nat_card_le
      (by rw [hPeq, hU1]; exact hPcard)
    have h1 : θ.subgroupMap P ⟨z, hz⟩ = 1 := Subtype.ext ((hθ1 z).mpr hzC)
    exact congrArg Subtype.val ((injective_iff_map_eq_one _).mp hbij.1 _ h1)
  set M : Subgroup I₀ := C.comap σ with hM
  haveI : M.Normal := Subgroup.Normal.comap inferInstance σ
  have hM3 : ¬ 3 ∣ Nat.card M := by
    intro h3
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := M) 3 h3
    have hgo : orderOf (g : I₀) = 3 := by rw [Subgroup.orderOf_coe, hg]
    have hg3 : (g : I₀) ^ 3 ^ 1 = 1 := by rw [pow_one, ← hgo, pow_orderOf_eq_one]
    obtain ⟨P', hP'⟩ := (isPGroup_zpowers_of_pow_eq_one hg3).exists_le_sylow
    have hσg : σ g = 1 :=
      (hsyl P').2 _ (Subgroup.mem_map_of_mem σ (hP' (mem_zpowers _))) g.2
    have hdvd : orderOf (⟨g, MonoidHom.mem_ker.mpr hσg⟩ : σ.ker) ∣ Nat.card σ.ker :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hgo] at hdvd
    exact absurd (Nat.Coprime.eq_one_of_dvd hker hdvd) (by norm_num)
  haveI : (M.map (QuotientGroup.mk' (CFSG.pCore 2 I₀))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hMbar : M.map (QuotientGroup.mk' (CFSG.pCore 2 I₀)) = ⊥ :=
    SevenFourL34.normal_eq_bot_of_not_three_dvd
      SevenFourL34.kFactSUThreeTwoNoNormalThreePrime_holds hb _
      fun h => hM3 (h.trans (Subgroup.card_map_dvd M _))
  have hMO : ∀ g ∈ M, g ∈ CFSG.pCore 2 I₀ := by
    intro g hg
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 I₀) g ∈
        M.map (QuotientGroup.mk' (CFSG.pCore 2 I₀)) := Subgroup.mem_map_of_mem _ hg
    rw [hMbar, Subgroup.mem_bot] at h1
    exact (QuotientGroup.eq_one_iff g).mp h1
  rcases hcond with hf | ⟨y₀, hy₀, hy₀3, α, hα, g₁, hg₁⟩
  · exact hs3 hf
  apply hg₁
  obtain ⟨P₀⟩ : Nonempty (Sylow 3 I₀) := inferInstance
  obtain ⟨k, hk, c, hc, hkc⟩ := hdec y₀ hy₀ hy₀3
  have hθk : θ k ∈ ((P₀ : Subgroup I₀).map σ).map θ := by
    rw [(hsyl P₀).1]
    exact Subgroup.mem_map_of_mem θ hk
  obtain ⟨_, ⟨x₀, hx₀, rfl⟩, hpk⟩ := hθk
  set c' := (σ x₀)⁻¹ * y₀ with hc'
  have hc'C : c' ∈ C := by
    rw [← hθ1, hc', map_mul, map_inv, hpk, hkc, map_mul, (hθ1 c).mpr hc, mul_one,
      inv_mul_cancel]
  have hy₀e : y₀ = σ x₀ * c' := by rw [hc']; group
  have hx₀O : x₀ ∈ CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀) := by
    obtain ⟨n, hn⟩ := P₀.isPGroup' ⟨x₀, hx₀⟩
    have hxn : x₀ ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
    exact Subgroup.subset_closure ⟨Subgroup.mem_top x₀,
      Odd.of_dvd_nat (Odd.pow (by decide)) (orderOf_dvd_of_pow_eq_one hxn)⟩
  haveI := (normal_oUpperTwo_top :
    (CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀)).Normal)
  have hM' : x₀⁻¹ * α g₁ * x₀ * g₁⁻¹ ∈ M := by
    show σ (x₀⁻¹ * α g₁ * x₀ * g₁⁻¹) ∈ C
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hα, hy₀e]
    have he : (σ x₀)⁻¹ * (σ x₀ * c' * σ g₁ * (σ x₀ * c')⁻¹) * σ x₀ * (σ g₁)⁻¹ =
        c' * (σ g₁ * c'⁻¹ * (σ g₁)⁻¹) := by group
    rw [he]
    exact C.mul_mem hc'C ((inferInstance : C.Normal).conj_mem _ (C.inv_mem hc'C) _)
  have hO := hMO _ hM'
  have he : α g₁ * g₁⁻¹ =
      (x₀ * (x₀⁻¹ * α g₁ * x₀ * g₁⁻¹) * x₀⁻¹) * (x₀ * (g₁ * x₀⁻¹ * g₁⁻¹)) := by group
  rw [he]
  refine Subgroup.mul_mem _ (mem_sup_right ?_) (mem_sup_left ?_)
  · exact (inferInstance : (CFSG.pCore 2 I₀).Normal).conj_mem _ hO x₀
  · exact Subgroup.mul_mem _ hx₀O
      ((inferInstance : (CFSG.ComponentClassification.AS76b.oUpperTwo
        (⊤ : Subgroup I₀)).Normal).conj_mem _ (Subgroup.inv_mem _ hx₀O) g₁)

end Solvable

section Certified

theorem threeFourSolvThreeUThreeThree_holds : ThreeFourSolvThreeUThreeThree := by
  intro q d hq3 hq1 hd Y _ _ K Y₀ E R I₀ _ _ σ hK hKX hZ _ hrkC _ hcomp hER hE hEc hcore hO2
    hker hσY hσs hb hcond _
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := hK
  set C := centralizer (K : Set Y) with hCdef
  have hKC := CFSG.QuasithinUnique.RankOneRecog.inf_centralizer_eq_bot_of_center_eq_bot hZ
  have hrkC' : CFSG.Open.pRank 3 C ≤ 1 := by
    rwa [CFSG.SectionRank.pRank_coe_eq_openPRank] at hrkC
  have hσC : (CFSG.pCore 2 I₀).map σ ≤ C := (map_pCore_two_le_pCoreOf σ hσs).trans hO2
  obtain ⟨e⟩ := hKX
  have hqc : q.card = 3 := by rw [TauCeti.PrimePower.card_def, hq3, hq1, pow_one]
  have hU : CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.IsUThreeThree ↥K :=
    ⟨d, ⟨q, hqc, hd⟩, ⟨e⟩⟩
  obtain ⟨hsimple, hcard, -⟩ := CFSG.AGLEmbeddingD2.McLaughlin.u33_simple_card_center hU
  obtain ⟨e'⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel
    (CFSG.AGLEmbeddingD2.McLaughlin.lieModel_of_isUThreeThree hU)
  have hrkK : CFSG.Open.pRank 3 K ≤ 2 := by
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank, CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact a6a_pRank_top_le_two_of_isUThreeThree hU
  obtain ⟨i, hv⟩ := d
  have hd' : i = .twistedA 2 q := hd
  subst hd'
  have hRank : IsRankThreeU3 ↥K := ⟨q, hq3, hq1, hv, ⟨e⟩⟩
  have hOut : Nat.card (Outer ↥K) = 2 := by
    have hmod := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
    rw [hq3, hq1] at hmod
    exact card_outer_eq_two_of_model_psu_three_three hmod
  have hX : ∀ α : MulAut K, ∀ k : ℕ, α ^ 3 ^ k = 1 → ∃ g : K, α = MulAut.conj g :=
    fun α k hα => exists_conj_of_pow_three_pow (by rw [hOut]; norm_num) hα
  obtain ⟨T, hT⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal R K
  obtain ⟨hT27, hTexp, -, ⟨F₀, hF₀T, hF₀el, hF₀c⟩, -, hmax⟩ := u3SylowData_proved ↥K hRank T
  set U : Subgroup Y := (R : Subgroup Y) ⊓ K with hUdef
  have hUK : U ≤ K := inf_le_right
  have hU27 : Nat.card U = 27 := by
    rw [← hT, Subgroup.card_map_of_injective K.subtype_injective, hT27]
    norm_num
  have hU3 : ∀ u ∈ U, u ^ 3 = 1 := by
    intro u hu
    rw [← hT] at hu
    obtain ⟨v, hv', rfl⟩ := hu
    have h1 := hTexp v hv'
    simpa using congrArg Subtype.val h1
  have hF : ∃ F : Subgroup Y, F ≤ U ∧ IsElemAbelian 3 F ∧ Nat.card F = 3 ^ 2 := by
    refine ⟨F₀.map K.subtype, ?_, hF₀el.map _, ?_⟩
    · rw [← hT]
      exact Subgroup.map_mono hF₀T
    · rw [Subgroup.card_map_of_injective K.subtype_injective, hF₀c]
  have hnab : ∃ a b : K, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have htop : Subgroup.center K = ⊤ :=
      eq_top_iff.mpr fun x _ => Subgroup.mem_center_iff.mpr fun y => h y x
    rw [hZ] at htop
    have h1 : Nat.card K = 1 := by
      rw [← Subgroup.card_top (G := K), ← htop, Subgroup.card_bot]
    omega
  have hKnle : ¬ K ≤ Y₀ := by
    refine hcomp K ?_ le_rfl
    haveI : Group.IsPerfect K := ⟨CFSG.ComponentClassification.Helpers.commutator_eq_top K hnab⟩
    exact ⟨le_top, IsSubnormal.step le_top inferInstance (IsSubnormal.refl ⊤),
      CFSG.ComponentClassification.Quasisimple.simple_of_perfect K⟩
  obtain ⟨hUY, hY₀U⟩ :=
    le_normalizer_of_borel hKC hX hrkK T hT hF hmax hKnle hER hE hEc hcore
  by_cases hs3 : Nonempty (I₀ ⧸ CFSG.pCore 2 I₀ ≃* Equiv.Perm (Fin 3))
  · obtain ⟨f⟩ := hs3
    exact le_centralizer_of_symThree σ f e' hKC hσC hσY hσs hUK hU27 hU3 hUY hY₀U
  · exact (false_of_not_symThree σ hb hs3 hker hRank hKC hrkC' hσY hUK hU27 hY₀U hcond).elim

theorem threeFourSolvThreeUnitary_holds : ThreeFourSolvThreeUnitary :=
  threeFourSolvThreeUnitary_of threeFourSolvThreeUThreeThree_holds

end Certified

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
