module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeToolsInner
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeToolsAut
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeAltSix
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourOneOf
import CFSG.Quasithin.Vol2.Ch11SecQ9aL3D
import CFSG.LocalAnalysis.AGLEmbedding.CZeroSubnormalCommute
import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionDatum
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.GH74.Uniqueness.SU.SU1Basic
public import CFSG.Monster.B.TwoA.Census.PermClasses
import CFSG.LocalAnalysis.AGLEmbedding.SUPairModel

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111 Subgroup
open CFSG.RankThreeCoreUniqueness.Helpers

namespace SolvNone

private theorem mul_conj_mul_inv_l34 {K : Type*} [Group K] (φ : MulAut K) (k : K) :
    φ * MulAut.conj k * φ⁻¹ = MulAut.conj (φ k) := by
  ext z
  simp [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply]

theorem l34_facts {K : Type} [Group K] [Finite K] (hK : IsLinThreeFour K) (T : Sylow 3 K) :
    Nat.card K = 20160 ∧ IsSimpleGroup K ∧
      KFactProofs.L34Local.LocalData K (T : Subgroup K) ∧
      (∀ α : MulAut K, (∀ t ∈ (T : Subgroup K), α t = t) → (∃ n : ℕ, α ^ 3 ^ n = 1) →
        ∃ t ∈ (T : Subgroup K), α = MulAut.conj t) ∧
      CFSG.pRank 3 (MulAut K) = 2 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ε₀⟩ := KFactProofs.L34Local.nonempty_equiv_of_isLinThreeFour hK
  have hk : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hK20 : Nat.card K = 20160 := by
    rw [Nat.card_congr ε₀.toEquiv]
    exact CFSG.RankThree.PartTwo.KFacts.L34.card_projectiveSL hk
  have hsimple : IsSimpleGroup K := by
    haveI := CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A.isSimpleGroup_projectiveSL_four hk
    exact ε₀.isSimpleGroup
  have hTcard : Nat.card (T : Subgroup K) = 9 := KFactProofs.L34Local.card_sylow_three hK20 T
  have hP₁ : Nat.card ((T : Subgroup K).map ε₀.toMonoidHom) = 9 := by
    rw [← hTcard]
    exact (Nat.card_congr (ε₀.subgroupMap (T : Subgroup K)).toEquiv).symm
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.KFacts.L34.exists_eq_map_conj_eZero hk hP₁
  set ε : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 (GaloisField 2 2) ≃* K :=
    (MulAut.conj g).trans ε₀.symm with hε
  have hεT : ∀ y, y ∈ CFSG.RankThree.PartTwo.KFacts.L34.eZero (GaloisField 2 2) ↔
      ε y ∈ (T : Subgroup K) := by
    intro y
    have h1 : ε y ∈ (T : Subgroup K) ↔ g * y * g⁻¹ ∈ (T : Subgroup K).map ε₀.toMonoidHom := by
      rw [Subgroup.mem_map_equiv]
      rfl
    rw [h1, hg, Subgroup.mem_map_equiv]
    simp only [MulAut.conj_symm_apply]
    rw [show g⁻¹ * (g * y * g⁻¹) * g = y by group]
  have hloc : KFactProofs.L34Local.LocalData K (T : Subgroup K) :=
    (KFactProofs.L34Local.localData_eZero hk).map ε hεT
  refine ⟨hK20, hsimple, hloc, fun α hα h3 => ?_, ?_⟩
  ·
    have := CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.charP_two_of_card_eq_four hk
    have hσ : ∀ a : GaloisField 2 2, frobeniusEquiv (GaloisField 2 2) 2 a = a ^ 2 :=
      fun a => frobeniusEquiv_apply (GaloisField 2 2) 2 a
    set α' : MulAut (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3
      (GaloisField 2 2)) := ε.trans (α.trans ε.symm) with hα'
    have hfix : ∀ x ∈ CFSG.RankThree.PartTwo.KFacts.L34.eZero (GaloisField 2 2), α' x = x := by
      intro x hx
      simp only [hα', MulEquiv.trans_apply]
      rw [hα _ ((hεT x).mp hx), MulEquiv.symm_apply_apply]
    obtain ⟨n, hn⟩ := h3
    have hα'n : α' ^ 3 ^ n = 1 := by
      have : α' = MulAut.congr ε.symm α := by
        ext x
        simp [hα', MulAut.congr_apply]
      rw [this, ← map_pow, hn, map_one]
    obtain ⟨e, he, hαe | hαe⟩ :=
      (CFSG.RankThree.PartTwo.KFacts.L34.forall_fixes_eZero_iff hk hσ α').mp hfix
    · refine ⟨ε e, (hεT e).mp he, ?_⟩
      ext k
      have h1 : α' (ε.symm k) = e * ε.symm k * e⁻¹ := by rw [hαe]; rfl
      have h2 : α k = ε (α' (ε.symm k)) := by simp [hα']
      rw [h2, h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      rfl
    · exfalso
      set β := CFSG.RankThree.PartTwo.KFacts.L34.betaAut (frobeniusEquiv (GaloisField 2 2) 2)
      have he9 : e ^ 9 = 1 := by
        have := (KFactProofs.L34Local.localData_eZero hk).card_eq
        have h := orderOf_dvd_natCard (⟨e, he⟩ :
          ↥(CFSG.RankThree.PartTwo.KFacts.L34.eZero (GaloisField 2 2)))
        rw [this, Subgroup.orderOf_mk] at h
        exact orderOf_dvd_iff_pow_eq_one.mp h
      have hcomm : Commute (MulAut.conj e) α' := by
        have h1 := mul_conj_mul_inv_l34 α' e
        rw [hfix e he] at h1
        exact (mul_inv_eq_iff_eq_mul.mp h1).symm
      have hβ : β = (MulAut.conj e)⁻¹ * α' := by rw [hαe]; group
      have hβ3 : β ^ (9 * 3 ^ n) = 1 := by
        rw [hβ, (hcomm.inv_left).mul_pow, inv_pow, ← map_pow, pow_mul, he9, one_pow, map_one,
          inv_one, one_mul, mul_comm, pow_mul, hα'n, one_pow]
      have hβ2 : β ^ 2 = 1 := by
        rw [pow_two]
        exact CFSG.RankThree.PartTwo.KFacts.L34.betaAut_mul_self hk hσ
      have hcop : Nat.Coprime (9 * 3 ^ n) 2 := by
        rw [Nat.coprime_two_right]
        exact (Odd.mul (by decide) (Odd.pow (by decide)))
      have hβ1 : β = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
        (orderOf_dvd_of_pow_eq_one hβ3) (orderOf_dvd_of_pow_eq_one hβ2))
      exact CFSG.RankThree.PartTwo.KFacts.L34.betaAut_ne_one hk hβ1
  · exact CFSG.RankThree.PartTwo.KFacts.L34.pRank_three_mulAut_of_mulEquiv hk ε₀

private theorem map_conj_eq_of_mem_normalizer_l34 {Y : Type*} [Group Y] {J : Subgroup Y} {n : Y}
    (hn : n ∈ normalizer (J : Set Y)) : J.map (MulAut.conj n).toMonoidHom = J := by
  ext x
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact (mem_normalizer_iff.mp hn j).mp hj
  · intro hx
    refine ⟨n⁻¹ * x * n, (mem_normalizer_iff.mp hn _).mpr (by simpa [mul_assoc] using hx), ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

private theorem map_conj_mul_l34 {Y : Type*} [Group Y] (J : Subgroup Y) (a b : Y) :
    J.map (MulAut.conj (a * b)).toMonoidHom =
      (J.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

end SolvNone

open SolvNone

theorem threeFourSolvThreeNoneAt_l34
    (q : TauCeti.PrimePower)
    (d : TauCeti.ValidLieTypeIndex) (hq2 : q.p = 2) (hqe : q.exponent = 2) (hd : d.1 = .A 2 q) :
    ThreeFourSolvThreeNoneAt (TauCeti.CFSGIndex.lie d).Group := by
  intro Y _ _ K Y₀ E R I₀ _ _ σ hKn hKX hZ _ hrkC hC hcomp hER hE hEc hcore hO2 hker hσY hσs hb
    _ hdir
  classical
  haveI := hKn
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd34 : CFSG.AGLEmbeddingD2.IsL34Index d := ⟨q, hq2, hqe, hd⟩
  have hKL : IsLinThreeFour ↥K := ⟨d, ⟨q, hq2, hqe, hd⟩, hKX⟩
  set C := centralizer (K : Set Y) with hCdef
  haveI : C.Normal := by rw [hCdef]; infer_instance
  set J := (CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀)).map σ with hJdef
  have hKC := CFSG.QuasithinUnique.RankOneRecog.inf_centralizer_eq_bot_of_center_eq_bot hZ
  have hKC' : ∀ x ∈ K, x ∈ C → x = 1 := fun x hxK hxC => by
    have h : x ∈ K ⊓ C := ⟨hxK, hxC⟩
    rwa [hKC, Subgroup.mem_bot] at h
  have hRY₀ : (R : Subgroup Y) ≤ Y₀ :=
    (sylow_le_threeFourCore Nat.prime_three R hER hE hEc).trans hcore
  obtain ⟨T, hT⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal R K
  obtain ⟨hcardK, hKsimple, hloc, haut, hrkA⟩ := l34_facts hKL T
  set TY : Subgroup Y := (T : Subgroup ↥K).map K.subtype with hTY
  have hTYeq : TY = (R : Subgroup Y) ⊓ K := hT
  have hTYR : TY ≤ R := by rw [hTYeq]; exact inf_le_left
  have hTYK : TY ≤ K := by rw [hTYeq]; exact inf_le_right
  have hTcard : Nat.card (T : Subgroup ↥K) = 9 := hloc.card_eq
  have hTYcard : Nat.card TY = 9 := by
    rw [hTY, Subgroup.card_map_of_injective K.subtype_injective, hTcard]
  have hK27 : ¬ 27 ∣ Nat.card ↥K := by rw [hcardK]; norm_num
  have hTexp : ∀ t ∈ (T : Subgroup ↥K), t ^ 3 = 1 := by
    obtain ⟨t₀, ht₀⟩ := exists_prime_orderOf_dvd_card' (G := (T : Subgroup ↥K)) 3
      (by rw [hTcard]; norm_num)
    intro t ht
    by_cases ht1 : t = 1
    · rw [ht1, one_pow]
    have ht₀1 : ((t₀ : ↥K)) ≠ 1 := by
      intro h
      have : t₀ = 1 := Subtype.ext h
      rw [this, orderOf_one] at ht₀
      norm_num at ht₀
    obtain ⟨n, -, hn⟩ := hloc.trans _ t₀.2 ht₀1 t ht ht1
    have h3 : (t₀ : ↥K) ^ 3 = 1 := by
      have h := pow_orderOf_eq_one t₀
      rw [ht₀] at h
      simpa using congrArg Subtype.val h
    rw [← hn, conj_pow, h3, mul_one, mul_inv_cancel]
  have hTel : IsElemAbelian 3 (T : Subgroup ↥K) :=
    ⟨⟨⟨fun x y => Subtype.ext (hloc.commute_of_card_eq x x.2 y y.2)⟩⟩, hTexp⟩
  have hTYel : IsElemAbelian 3 TY := hTel.map _
  have hnab : ∃ a b : ↥K, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have htop : Subgroup.center ↥K = ⊤ :=
      eq_top_iff.mpr fun x _ => Subgroup.mem_center_iff.mpr fun g => h g x
    have h1 : Nat.card (⊤ : Subgroup ↥K) = Nat.card (⊥ : Subgroup ↥K) := by rw [← htop, hZ]
    rw [Subgroup.card_top, Subgroup.card_bot, hcardK] at h1
    norm_num at h1
  have hKcomp : IsComponentOf K ⊤ := by
    haveI := hKsimple
    haveI : Group.IsPerfect ↥K := ⟨CFSG.ComponentClassification.Helpers.commutator_eq_top ↥K hnab⟩
    exact ⟨le_top, IsSubnormal.step le_top inferInstance (IsSubnormal.refl ⊤),
      CFSG.ComponentClassification.Quasisimple.simple_of_perfect ↥K⟩
  have hKY₀ : ¬ K ≤ Y₀ := hcomp K hKcomp le_rfl
  set θ := (MulAut.conjNormal : Y →* MulAut ↥K).rangeRestrict with hθ
  have hθs : Function.Surjective θ := MonoidHom.rangeRestrict_surjective _
  have hθker : θ.ker = C := SolvNone.ker_rangeRestrict_conjNormal K
  have hθ1 : ∀ y : Y, θ y = 1 ↔ y ∈ C := fun y => by rw [← MonoidHom.mem_ker, hθker]
  have hθeq : ∀ a b : Y, θ a = θ b ↔ a⁻¹ * b ∈ C := fun a b => by
    rw [← hθ1, map_mul, map_inv, inv_mul_eq_one]
  haveI : Finite (MulAut ↥K) := MulEquiv.finite_left
  set Kb := K.map θ with hKb
  haveI : Kb.Normal := hKn.map θ hθs
  have hCX : centralizer (Kb : Set (MulAut.conjNormal : Y →* MulAut ↥K).range) = ⊥ :=
    SolvNone.centralizer_map_rangeRestrict_conjNormal_eq_bot hZ
  have hKbX : Nonempty (Kb ≃* (TauCeti.CFSGIndex.lie d).Group) := by
    obtain ⟨f⟩ := SolvNone.nonempty_mulEquiv_map_rangeRestrict_conjNormal (K := K) hZ
    obtain ⟨eK⟩ := hKX
    exact ⟨f.trans eK⟩
  have hθK : Function.Injective (θ.comp K.subtype) := by
    refine (injective_iff_map_eq_one _).mpr fun k hk => ?_
    exact Subtype.ext (hKC' k k.2 ((hθ1 k).mp hk))
  have hθapp : ∀ (y : Y) (x : ↥K), (((θ y : MulAut ↥K) x : ↥K) : Y) = y * x * y⁻¹ := fun y x => by
    simp [hθ, MulAut.conjNormal_apply]
  have hθK' : ∀ k : ↥K, ((θ k : MulAut ↥K)) = MulAut.conj k := fun k => MulAut.conjNormal_val
  set Tb := TY.map θ with hTb
  have hTbKb : Tb ≤ Kb := Subgroup.map_mono hTYK
  have hTbcard : Nat.card Tb = 9 := by
    rw [hTb, hTY, Subgroup.map_map, Subgroup.card_map_of_injective hθK, hTcard]
  have hTbel : IsElemAbelian 3 Tb := hTYel.map _
  have hTbY₀ : Tb ≤ Y₀.map θ := Subgroup.map_mono (hTYR.trans hRY₀)
  have hY₀top : Y₀.map θ ≠ ⊤ := by
    intro h
    apply hKY₀
    intro k hk
    obtain ⟨y, hy, hyk⟩ := (h ▸ Subgroup.mem_top (θ k) : θ k ∈ Y₀.map θ)
    have hc : y⁻¹ * k ∈ C := (hθeq y k).mp hyk
    have := Y₀.mul_mem hy (hC hc)
    simpa using this
  have hnormT : ∀ y : Y, θ y ∈ normalizer (Tb : Set _) → ∀ t ∈ TY, y * t * y⁻¹ ∈ TY := by
    intro y hy t ht
    obtain ⟨t', ht', ht't⟩ := (mem_normalizer_iff.mp hy (θ t)).mp (Subgroup.mem_map_of_mem θ ht)
    have h2 : θ t' = θ (y * t * y⁻¹) := by rw [ht't, map_mul, map_mul, map_inv]
    have h1 : t'⁻¹ * (y * t * y⁻¹) = 1 :=
      hKC' _ (K.mul_mem (K.inv_mem (hTYK ht')) (hKn.conj_mem t (hTYK ht) y)) ((hθeq _ _).mp h2)
    rw [← inv_mul_eq_one.mp h1]
    exact ht'
  have hKbcard : Nat.card Kb = 20160 := by
    have : Kb = (θ.comp K.subtype).range := by rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [this, ← Nat.card_congr (MonoidHom.ofInjective hθK).toEquiv, hcardK]
  have hKb3 : ∀ S : Subgroup (MulAut.conjNormal : Y →* MulAut ↥K).range, S ≤ Kb →
      IsPGroup 3 S → Nat.card S ≤ 9 := by
    intro S hS hSp
    obtain ⟨n, hn⟩ := hSp.exists_card_eq
    have hdvd : 3 ^ n ∣ 20160 := hn ▸ hKbcard ▸ Subgroup.card_dvd_of_le hS
    have hn2 : n ≤ 2 := by
      by_contra h
      push Not at h
      have : 3 ^ 3 ∣ 20160 := (pow_dvd_pow 3 h).trans hdvd
      norm_num at this
    rw [hn]
    calc 3 ^ n ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn2
      _ = 9 := by norm_num
  have hNY₀ : normalizer (Tb : Set _) ≤ Y₀.map θ := by
    by_cases h3C : 3 ∣ Nat.card C
    ·
      obtain ⟨P, hP⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal R C
      set RC := (R : Subgroup Y) ⊓ C with hRC
      have hRCcard : 3 ∣ Nat.card RC := by
        rw [← hP, Subgroup.card_map_of_injective C.subtype_injective]
        exact P.dvd_card_of_dvd_card h3C
      obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := RC) 3 hRCcard
      have hz3 : (z : Y) ^ 3 = 1 := by
        rw [← Subgroup.orderOf_coe] at hz
        rw [← hz]
        exact pow_orderOf_eq_one _
      have hzK : (z : Y) ∉ TY := by
        intro h
        have h1 : (z : Y) = 1 := hKC' _ (hTYK h) z.2.2
        have h2 : z = 1 := Subtype.ext h1
        rw [h2, orderOf_one] at hz
        norm_num at hz
      set Q := TY ⊔ RC with hQ
      have hQR : Q ≤ R := sup_le hTYR inf_le_left
      have hcommz : ∀ a ∈ TY, ∀ b ∈ zpowers (z : Y), a * b = b * a := by
        intro a ha b hb
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hb
        exact (Commute.zpow_right (show Commute a (z : Y) from
          mem_centralizer_iff.mp z.2.2 a (hTYK ha)) k).eq
      have hel : IsElemAbelian 3 (TY ⊔ zpowers (z : Y)) :=
        CFSG.GH74.Uniqueness.SU.SU1.IsElemAbelian.sup hTYel
          (CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_zpowers hz3) hcommz
      obtain ⟨k₂₇, hk₂₇⟩ :=
        CFSG.GH74.Uniqueness.SU.SU1.IsElemAbelian.exists_card Nat.prime_three hel
      have hlt : TY < TY ⊔ zpowers (z : Y) :=
        lt_of_le_of_ne le_sup_left fun h => hzK (h ▸ mem_sup_right (mem_zpowers _))
      have hk3 : 3 ≤ k₂₇ := by
        have h1 := CFSG.GH74.Uniqueness.SU.SU1.card_lt_of_lt hlt
        rw [hTYcard, hk₂₇] at h1
        by_contra hk
        push Not at hk
        interval_cases k₂₇ <;> norm_num at h1
      have hzQ : TY ⊔ zpowers (z : Y) ≤ Q := sup_le_sup_left (zpowers_le.mpr z.2) _
      have hrkQ2 : 2 ≤ CFSG.Open.pRank 3 Q :=
        CFSG.SectionRank.le_pRank (by norm_num) le_sup_left hTYel (by rw [hTYcard]; norm_num)
      have hrkQ3 : 3 ≤ CFSG.Open.pRank 3 (Q ⊔ ((R : Subgroup Y) ⊓ centralizer (Q : Set Y))) :=
        hk3.trans (CFSG.SectionRank.le_pRank (by norm_num) (hzQ.trans le_sup_left) hel hk₂₇)
      have hrkR : 3 ≤ CFSG.pRank 3 (R : Subgroup Y) := by
        rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
        exact hk3.trans (CFSG.SectionRank.le_pRank (by norm_num) (hzQ.trans hQR) hel hk₂₇)
      have hNQ : normalizer (Q : Set Y) ≤ Y₀ := by
        have hcore' := hcore
        rw [if_pos hrkR] at hcore'
        refine le_trans ?_ hcore'
        rw [GLBWeakCore, rankThreeAschCore]
        exact le_sSup ⟨Q, hQR, hrkQ2, hrkQ3, rfl⟩
      intro x hx
      obtain ⟨y, rfl⟩ := hθs x
      have hyT := hnormT y hx
      set φ : MulAut ↥C := MulAut.conjNormal y with hφ
      have hφs : Function.Surjective (φ.toMonoidHom : ↥C →* ↥C) := fun x =>
        ⟨φ.symm x, by simp⟩
      set P' : Sylow 3 ↥C := P.mapSurjective hφs with hP'
      obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥C P' P
      set g : Y := (c : Y) * y with hg
      have hgRC : ∀ w ∈ RC, g * w * g⁻¹ ∈ RC := by
        intro w hw
        rw [← hP] at hw ⊢
        obtain ⟨p, hp, rfl⟩ := hw
        have hφp : φ p ∈ (P' : Subgroup ↥C) := by
          rw [hP', Sylow.coe_mapSurjective]
          exact ⟨p, hp, rfl⟩
        have hcp : c * φ p * c⁻¹ ∈ (P : Subgroup ↥C) := by
          rw [← hc, Sylow.coe_subgroup_smul]
          exact ⟨φ p, hφp, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
        refine ⟨c * φ p * c⁻¹, hcp, ?_⟩
        simp [hg, hφ, MulAut.conjNormal_apply, mul_assoc]
      have hgT : ∀ t ∈ TY, g * t * g⁻¹ ∈ TY := by
        intro t ht
        have h1 := hyT t ht
        have hck := mem_centralizer_iff.mp c.2 _ (hTYK h1)
        have h2 : g * t * g⁻¹ = y * t * y⁻¹ := by
          calc g * t * g⁻¹ = (c : Y) * (y * t * y⁻¹) * (c : Y)⁻¹ := by rw [hg]; group
            _ = y * t * y⁻¹ := by rw [← hck, mul_inv_cancel_right]
        rw [h2]
        exact h1
      have hgQ : g ∈ normalizer (Q : Set Y) := by
        refine Subgroup.mem_normalizer_fintype fun x hx => ?_
        have hle : Q.map (MulAut.conj g).toMonoidHom ≤ Q := by
          rw [hQ, Subgroup.map_sup]
          refine sup_le_sup ?_ ?_
          · rintro _ ⟨t, ht, rfl⟩
            simpa [MulAut.conj_apply] using hgT t ht
          · rintro _ ⟨w, hw, rfl⟩
            simpa [MulAut.conj_apply] using hgRC w hw
        exact hle ⟨x, hx, by simp [MulAut.conj_apply]⟩
      refine ⟨g, hNQ hgQ, ?_⟩
      rw [hg, map_mul, (hθ1 (c : Y)).mpr c.2, one_mul]
    ·
      have hker' : Nat.Coprime 3 (Nat.card θ.ker) := by
        rw [hθker]
        exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3C
      have hcoreX := SolvNone.map_threeFourCore_le hθs hker' R hER hcore
      have hrkX : ¬ 3 ≤ CFSG.pRank 3 ((R : Subgroup Y).map θ) := by
        intro h
        have h1 : CFSG.pRank 3 ↥((R : Subgroup Y).map θ) ≤
            CFSG.pRank 3 ↥(MulAut.conjNormal : Y →* MulAut ↥K).range := by
          rw [CFSG.SectionRank.pRank_coe_eq_openPRank, CFSG.SectionRank.pRank_eq_open_pRank_top]
          exact CFSG.SectionRank.pRank_mono (by norm_num) le_top
        have h2 : CFSG.pRank 3 ↥(MulAut.conjNormal : Y →* MulAut ↥K).range ≤
            CFSG.pRank 3 (MulAut ↥K) := by
          rw [CFSG.SectionRank.pRank_coe_eq_openPRank, CFSG.SectionRank.pRank_eq_open_pRank_top]
          exact CFSG.SectionRank.pRank_mono (by norm_num) le_top
        omega
      rw [if_neg hrkX] at hcoreX
      have hEinj : Function.Injective (θ.comp E.subtype) := by
        refine (injective_iff_map_eq_one _).mpr fun x hx => ?_
        exact Subtype.ext (SolvNone.eq_one_of_isPGroup_of_coprime hker' hE.isPGroup x x.2 hx)
      have hEb9 : Nat.card (E.map θ) = 3 ^ 2 := by
        have : E.map θ = (θ.comp E.subtype).range := by
          rw [MonoidHom.range_comp, Subgroup.range_subtype]
        rw [this, ← Nat.card_congr (MonoidHom.ofInjective hEinj).toEquiv, hEc]
      have hEbel : IsElemAbelian 3 (E.map θ) := hE.map θ
      by_cases hEK : E.map θ ≤ Kb
      ·
        have hS : IsPGroup 3 ↥((R : Subgroup Y).map θ ⊓ Kb) :=
          (R.isPGroup'.map θ).to_le inf_le_left
        have hTbS : Tb ≤ (R : Subgroup Y).map θ ⊓ Kb :=
          le_inf (Subgroup.map_mono hTYR) hTbKb
        have hSTb : Tb = (R : Subgroup Y).map θ ⊓ Kb :=
          Subgroup.eq_of_le_of_card_ge hTbS (by rw [hTbcard]; exact hKb3 _ inf_le_right hS)
        have hEbT : E.map θ = Tb := by
          have hle : E.map θ ≤ Tb := by
            rw [hSTb]
            exact le_inf (Subgroup.map_mono hER) hEK
          exact Subgroup.eq_of_le_of_card_ge hle (by rw [hTbcard, hEb9]; norm_num)
        have hrk1 : 1 ≤ CFSG.Open.pRank 3 (E.map θ) :=
          le_trans (by norm_num) (CFSG.SectionRank.le_pRank (by norm_num) le_rfl hEbel hEb9)
        have hle : normalizer ((E.map θ : Subgroup _) : Set _) ≤ GLBCore 3 1 (E.map θ) :=
          le_sSup ⟨E.map θ, le_rfl, hrk1, rfl⟩
        rw [← hEbT]
        exact hle.trans hcoreX
      · exfalso
        have htop := CFSG.AGLEmbeddingD2.kFactL34Outer d hd34 _ Kb inferInstance hCX hKbX
          (E.map θ) hEbel hEb9 hEK
        exact hY₀top (eq_top_iff.mpr (htop ▸ hcoreX))
  have hY₀N : Y₀.map θ = normalizer (Tb : Set _) := by
    rcases CFSG.AGLEmbeddingD2.kFactL34Inner d hd34 _ Kb inferInstance hCX hKbX Tb hTbel
        (by rw [hTbcard]; norm_num) hTbKb (Y₀.map θ) hNY₀ with h | h
    · exact h
    · exact absurd h hY₀top
  set W := pCoreOf 3 (Y₀.map θ) with hW
  have hWp : IsPGroup 3 W := pCoreOf_isPGroup 3 _
  have hWnorm : Y₀.map θ ≤ normalizer (W : Set _) := localGroup_le_normalizer_pCoreOf 3 _
  have hWY₀ : W ≤ Y₀.map θ := pCoreOf_le 3 _
  have hWKb : W ≤ Kb := by
    by_contra hWK
    obtain ⟨w, hwW, hwK⟩ := SetLike.not_le_iff_exists.mp hWK
    set U := W ⊔ Tb with hU
    have hTbN : Tb ≤ normalizer (W : Set _) := hTbY₀.trans hWnorm
    have hUp : IsPGroup 3 U := hWp.to_sup_of_normal_left' hTbel.isPGroup hTbN
    have hUY₀ : U ≤ Y₀.map θ := sup_le hWY₀ hTbY₀
    have hUnorm : ∀ m ∈ Y₀.map θ, ∀ v ∈ U, m * v * m⁻¹ ∈ U := by
      intro m hm v hv
      have hmW : m ∈ normalizer (W : Set _) := hWnorm hm
      have hmT : m ∈ normalizer (Tb : Set _) := hY₀N ▸ hm
      have hle : U.map (MulAut.conj m).toMonoidHom ≤ U := by
        rw [hU, Subgroup.map_sup, map_conj_eq_of_mem_normalizer_l34 hmW,
          map_conj_eq_of_mem_normalizer_l34 hmT]
      exact hle ⟨v, hv, by simp [MulAut.conj_apply]⟩
    have hUK : ∀ u ∈ U, u ∈ Kb → u ∈ Tb := by
      intro u hu huK
      have hle : Tb ≤ U ⊓ Kb := le_inf le_sup_right hTbKb
      have heq : Tb = U ⊓ Kb := Subgroup.eq_of_le_of_card_ge hle
        (by rw [hTbcard]; exact hKb3 _ inf_le_right (hUp.to_le inf_le_left))
      rw [heq]
      exact ⟨hu, huK⟩
    obtain ⟨u, huU, huK, hucent⟩ : ∃ u ∈ U, u ∉ Kb ∧ ∀ t ∈ Tb, u * t = t * u := by
      by_cases hZU : ∃ z ∈ U, z ∉ Kb ∧ ∀ v ∈ U, z * v = v * z
      · obtain ⟨z, hzU, hzK, hz⟩ := hZU
        exact ⟨z, hzU, hzK, fun t ht => hz t (Subgroup.mem_sup_right ht)⟩
      push Not at hZU
      refine ⟨w, Subgroup.mem_sup_left hwW, hwK, ?_⟩
      haveI : Nontrivial U := ⟨⟨⟨w, Subgroup.mem_sup_left hwW⟩, 1, fun h => hwK (by
        have : w = 1 := congrArg Subtype.val h
        rw [this]
        exact Kb.one_mem)⟩⟩
      haveI := hUp.center_nontrivial
      obtain ⟨z₀, hz₀1⟩ := exists_ne (1 : Subgroup.center U)
      set z : (MulAut.conjNormal : Y →* MulAut ↥K).range := (z₀ : ↥U).1 with hz
      have hzU : z ∈ U := (z₀ : ↥U).2
      have hz1 : z ≠ 1 := fun h => hz₀1 (Subtype.ext (Subtype.ext h))
      have hzc : ∀ v ∈ U, z * v = v * z := fun v hv => by
        have := Subgroup.mem_center_iff.mp z₀.2 ⟨v, hv⟩
        exact (congrArg Subtype.val this).symm
      have hzK : z ∈ Kb := by
        by_contra hK
        obtain ⟨v, hv, hvz⟩ := hZU z hzU hK
        exact hvz (hzc v hv)
      have hzT : z ∈ Tb := hUK z hzU hzK
      obtain ⟨_, ⟨t₀', ht₀', rfl⟩, ht₀z⟩ := hzT
      have ht₀1 : t₀' ≠ 1 := by
        rintro rfl
        apply hz1
        rw [← ht₀z]
        simp
      intro t ht
      obtain ⟨_, ⟨t₁, ht₁, rfl⟩, rfl⟩ := ht
      by_cases ht₁1 : t₁ = 1
      · simp [ht₁1]
      obtain ⟨n, hn, hnt⟩ := hloc.trans t₀' ht₀' ht₀1 t₁ ht₁ ht₁1
      have hθn : θ (n : Y) ∈ Y₀.map θ := by
        rw [hY₀N]
        refine Subgroup.mem_normalizer_fintype fun x hx => ?_
        obtain ⟨_, ⟨s, hs, rfl⟩, rfl⟩ := hx
        refine ⟨K.subtype (n * s * n⁻¹), ⟨n * s * n⁻¹, (mem_normalizer_iff.mp hn s).mp hs, rfl⟩, ?_⟩
        simp [map_mul, map_inv]
      have he : θ (K.subtype t₁) = θ (n : Y) * z * (θ (n : Y))⁻¹ := by
        rw [← ht₀z, ← hnt]
        simp [map_mul, map_inv]
      have hv' : (θ (n : Y))⁻¹ * w * (θ (n : Y))⁻¹⁻¹ ∈ U :=
        hUnorm _ (Subgroup.inv_mem _ hθn) w (Subgroup.mem_sup_left hwW)
      have h1 := hzc _ hv'
      rw [he]
      calc w * (θ (n : Y) * z * (θ (n : Y))⁻¹)
          = θ (n : Y) * (((θ (n : Y))⁻¹ * w * (θ (n : Y))⁻¹⁻¹) * z) * (θ (n : Y))⁻¹ := by group
        _ = θ (n : Y) * (z * ((θ (n : Y))⁻¹ * w * (θ (n : Y))⁻¹⁻¹)) * (θ (n : Y))⁻¹ := by
            rw [← h1]
        _ = θ (n : Y) * z * (θ (n : Y))⁻¹ * w := by group
    have hufix : ∀ t ∈ (T : Subgroup ↥K), (u : MulAut ↥K) t = t := by
      intro t ht
      have h1 := hucent (θ (K.subtype t)) ⟨K.subtype t, ⟨t, ht, rfl⟩, rfl⟩
      have h2 : (u : MulAut ↥K) * MulAut.conj t * (u : MulAut ↥K)⁻¹ = MulAut.conj t := by
        have h3 := congrArg Subtype.val h1
        simp only [Subgroup.coe_mul] at h3
        have hθt : ((θ (K.subtype t) : (MulAut.conjNormal : Y →* MulAut ↥K).range) :
            MulAut ↥K) = MulAut.conj t := hθK' t
        rw [hθt] at h3
        rw [h3, mul_inv_cancel_right]
      rw [mul_conj_mul_inv_l34] at h2
      exact SolvNone.conj_injective_of_center_eq_bot hZ h2
    obtain ⟨n3, hn3⟩ := hUp ⟨u, huU⟩
    have hu3 : (u : MulAut ↥K) ^ 3 ^ n3 = 1 := by
      have := congrArg (fun v : U => ((v : _) : MulAut ↥K)) hn3
      simpa using this
    obtain ⟨t₀, ht₀, hut₀⟩ := haut _ hufix ⟨n3, hu3⟩
    apply huK
    refine ⟨(t₀ : Y), t₀.2, ?_⟩
    apply Subtype.ext
    rw [hθK' t₀, hut₀]
  have hJ3C : ∀ x ∈ J, x ^ 3 ∈ C := cube_mem_of_pCoreOf_le σ hσs hO2 hb
  have hθJp : IsPGroup 3 (J.map θ) := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨1, Subtype.ext (by
      show θ x ^ 3 ^ 1 = 1
      rw [pow_one, ← map_pow]
      exact (hθ1 _).mpr (hJ3C x hx))⟩
  have hJθ : J.map θ ≤ W := CFSG.AGLEmbedding.SubnormalCommute.le_pCoreOf_of_isSubnormal
    ((isSubnormal_oUpperTwo_map σ hσs).map θ) hθJp
  have hinner : ∀ y ∈ σ.range, y ^ 3 = 1 → ∃ k ∈ K, ∃ c ∈ C, y = k * c := by
    intro y hy hy3
    have hodd : Odd (orderOf y) := Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hy3)
    have hJ' : CFSG.ComponentClassification.AS76b.oUpperTwo σ.range = J := by
      rw [hJdef, SUPair.map_oUpperTwo, ← MonoidHom.range_eq_map]
    have hyJ : y ∈ J := hJ' ▸ Subgroup.subset_closure ⟨hy, hodd⟩
    obtain ⟨k, hk, hkθ⟩ := hWKb (hJθ (Subgroup.mem_map_of_mem θ hyJ))
    exact ⟨k, hk, k⁻¹ * y, (hθeq k y).mp hkθ, by group⟩
  rcases SolvNone.le_centralizer_or_le_of_inner σ hZ hinner
      (fun Q hQ _ h3 => commute_of_le_of_not_dvd hQ hK27 h3) hrkC hC hO2 hker hσY hσs hb with
    h | ⟨hJK, y₀, hy₀K, hy₀3, hJy₀⟩
  · exact h
  by_contra hJC
  have hY₀T : ∀ y ∈ Y₀, ∀ t ∈ TY, y * t * y⁻¹ ∈ TY := fun y hy =>
    hnormT y (hY₀N ▸ Subgroup.mem_map_of_mem θ hy)
  have hNK : ∀ k : ↥K, k ∈ normalizer ((T : Subgroup ↥K) : Set ↥K) → (k : Y) ∈ Y₀ := by
    intro k hk
    have h1 : θ (k : Y) ∈ Y₀.map θ := by
      rw [hY₀N]
      refine Subgroup.mem_normalizer_fintype fun x hx => ?_
      obtain ⟨_, ⟨s, hs, rfl⟩, rfl⟩ := hx
      refine ⟨K.subtype (k * s * k⁻¹), ⟨k * s * k⁻¹, (mem_normalizer_iff.mp hk s).mp hs, rfl⟩, ?_⟩
      simp
    obtain ⟨y, hy, hyk⟩ := h1
    have := Y₀.mul_mem hy (hC ((hθeq y k).mp hyk))
    simpa using this
  have hY₀K : Y₀.comap K.subtype = normalizer ((T : Subgroup ↥K) : Set ↥K) := by
    ext k
    constructor
    · intro hk
      refine Subgroup.mem_normalizer_fintype fun s hs => ?_
      obtain ⟨s', hs', hss'⟩ := hY₀T k hk s ⟨s, hs, rfl⟩
      have : s' = k * s * k⁻¹ := Subtype.ext (by simpa using hss')
      rw [← this]
      exact hs'
    · exact hNK k
  have hJsub : IsSubnormal J Y₀ := isSubnormal_oUpperTwo_map σ hσs
  have hJ3 : ∀ x ∈ J, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp (hJy₀ hx)
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy₀3, one_zpow]
  have hJp : IsPGroup 3 J := fun x => ⟨1, Subtype.ext (by simpa using hJ3 x x.2)⟩
  set J' : Subgroup ↥K := J.comap K.subtype with hJ'
  have hJ'map : J'.map K.subtype = J :=
    Subgroup.map_comap_eq_self (by rw [Subgroup.range_subtype]; exact hJK)
  have hJ'T : J' ≤ (T : Subgroup ↥K) := by
    have h1 := CFSG.AGLEmbedding.SubnormalCommute.le_pCoreOf_of_isSubnormal
      (hJsub.comap K.subtype) (hJp.comap_of_injective K.subtype K.subtype_injective)
    rw [hY₀K] at h1
    have hp := (pCoreOf_isPGroup 3 (normalizer ((T : Subgroup ↥K) : Set ↥K))).to_sup_of_normal_left'
      T.isPGroup' (le_normalizer.trans (localGroup_le_normalizer_pCoreOf 3 _))
    exact h1.trans (le_sup_left.trans (T.is_maximal' hp le_sup_right).le)
  have hJT : J ≤ TY := by
    rw [← hJ'map]
    exact Subgroup.map_mono hJ'T
  have hJne : J ≠ ⊥ := fun h => hJC (by rw [h]; exact bot_le)
  have hJcard : Nat.card J = 3 := by
    have h1 : Nat.card J ∣ orderOf y₀ := by
      rw [← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le hJy₀
    have h3 : Nat.card J ∣ 3 := h1.trans (orderOf_dvd_of_pow_eq_one hy₀3)
    rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h
    · exact absurd (Subgroup.eq_bot_of_card_eq J h) hJne
    · exact h
  have hO2J : CFSG.pCore 2 ↥J = ⊥ := by
    have h2 : IsPGroup 2 (CFSG.pCore 2 ↥J) := CFSG.pCore_isPGroup
    have h3 : IsPGroup 3 (⊤ : Subgroup ↥J) := (hJp.of_equiv Subgroup.topEquiv.symm)
    rw [eq_bot_iff]
    intro x hx
    exact (IsPGroup.disjoint_of_ne 2 3 (by norm_num) _ _ h2 h3).le_bot ⟨hx, Subgroup.mem_top _⟩
  have hcardJq : Nat.card (↥J ⧸ CFSG.pCore 2 ↥J) = 3 := by
    rw [hO2J, Nat.card_congr (QuotientGroup.quotientBot).toEquiv, hJcard]
  have hD'T : (⨆ y ∈ Y₀, J.map (MulAut.conj y).toMonoidHom) ≤ TY := iSup₂_le fun y hy => by
    rintro _ ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using hY₀T y hy x (hJT hx)
  have hh : ((normalizer (J : Set Y) ⊓ Y₀).subgroupOf Y₀).index ≤ 2 := by
    have hd := hdir
    unfold SolvThreeDirectCond at hd
    rw [hcardJq] at hd
    have h9 : 3 ^ ((normalizer (J : Set Y) ⊓ Y₀).subgroupOf Y₀).index ≤ 3 ^ 2 := by
      rw [← hd]
      calc _ ≤ Nat.card ↥(⨆ y ∈ Y₀, J.map (MulAut.conj y).toMonoidHom) :=
            Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
        _ ≤ Nat.card TY := Subgroup.card_le_of_le hD'T
        _ = 3 ^ 2 := by rw [hTYcard]; norm_num
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h9
  set M := (normalizer (J : Set Y) ⊓ Y₀).subgroupOf Y₀ with hM
  obtain ⟨g, hg⟩ : ∃ g : Y, ∀ y ∈ Y₀, J.map (MulAut.conj y).toMonoidHom = J ∨
      J.map (MulAut.conj y).toMonoidHom = J.map (MulAut.conj g).toMonoidHom := by
    have hidx : M.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rcases (show M.index = 1 ∨ M.index = 2 by omega) with h1 | h2
    · refine ⟨1, fun y hy => Or.inl ?_⟩
      have hyM : (⟨y, hy⟩ : ↥Y₀) ∈ M := (Subgroup.index_eq_one.mp h1) ▸ Subgroup.mem_top _
      exact map_conj_eq_of_mem_normalizer_l34 (Subgroup.mem_subgroupOf.mp hyM).1
    · obtain ⟨g, hgM⟩ : ∃ g : ↥Y₀, g ∉ M := by
        by_contra h
        push Not at h
        have : M = ⊤ := eq_top_iff.mpr fun x _ => h x
        rw [this, Subgroup.index_top] at h2
        omega
      refine ⟨g, fun y hy => ?_⟩
      by_cases hyM : (⟨y, hy⟩ : ↥Y₀) ∈ M
      · exact Or.inl (map_conj_eq_of_mem_normalizer_l34 (Subgroup.mem_subgroupOf.mp hyM).1)
      · right
        have hgyM : g⁻¹ * ⟨y, hy⟩ ∈ M := by
          rw [Subgroup.mul_mem_iff_of_index_two h2, Subgroup.inv_mem_iff]
          exact iff_of_false hgM hyM
        have hN' : (g : Y)⁻¹ * y ∈ normalizer (J : Set Y) := by
          simpa using (Subgroup.mem_subgroupOf.mp hgyM).1
        calc J.map (MulAut.conj y).toMonoidHom
            = J.map (MulAut.conj ((g : Y) * ((g : Y)⁻¹ * y))).toMonoidHom := by
              rw [mul_inv_cancel_left]
          _ = (J.map (MulAut.conj ((g : Y)⁻¹ * y)).toMonoidHom).map
                (MulAut.conj (g : Y)).toMonoidHom := map_conj_mul_l34 J _ _
          _ = J.map (MulAut.conj (g : Y)).toMonoidHom := by
              rw [map_conj_eq_of_mem_normalizer_l34 hN']
  obtain ⟨j, hjJ, hj1⟩ : ∃ j ∈ J, j ≠ 1 := by
    by_contra h
    push Not at h
    exact hJne (eq_bot_iff.mpr fun x hx => (Subgroup.mem_bot).mpr (h x hx))
  obtain ⟨jK, hjK, rfl⟩ := hJT hjJ
  have hjK1 : jK ≠ 1 := fun h => hj1 (by rw [h]; rfl)
  have hcover : (TY : Set Y) ⊆ (J : Set Y) ∪ (J.map (MulAut.conj g).toMonoidHom : Set Y) := by
    rintro _ ⟨t, ht, rfl⟩
    by_cases ht1 : t = 1
    · left
      rw [ht1]
      exact J.one_mem
    obtain ⟨n, hnN, hnt⟩ := hloc.trans jK hjK hjK1 t ht ht1
    have htmem : (t : Y) ∈ J.map (MulAut.conj (n : Y)).toMonoidHom :=
      ⟨jK, hjJ, by rw [← hnt]; simp [MulAut.conj_apply]⟩
    rcases hg n (hNK n hnN) with h | h
    · left
      rw [h] at htmem
      exact htmem
    · right
      rw [h] at htmem
      exact htmem
  have h1 := Set.ncard_le_ncard hcover (Set.toFinite _)
  have h2 := Set.ncard_union_le (J : Set Y) (J.map (MulAut.conj g).toMonoidHom : Set Y)
  have h3 : (TY : Set Y).ncard = 9 := by rw [← Nat.card_coe_set_eq]; exact hTYcard
  have h4 : (J : Set Y).ncard = 3 := by rw [← Nat.card_coe_set_eq]; exact hJcard
  have h5 : (J.map (MulAut.conj g).toMonoidHom : Set Y).ncard = 3 := by
    rw [← Nat.card_coe_set_eq]
    change Nat.card (J.map (MulAut.conj g).toMonoidHom) = 3
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hJcard]
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

end
