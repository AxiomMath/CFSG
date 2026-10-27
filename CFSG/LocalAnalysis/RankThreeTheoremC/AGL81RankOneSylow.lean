module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenRankOneDefs
import CFSG.LocalAnalysis.RankFourTheoremC.PPointSmallTypes
import CFSG.LocalAnalysis.RankFourTheoremC.NongenerationMonster
import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Local
import CFSG.Adapters.Certificate43Check
import CFSG.RankThree.PartOne.S11d.OutCentral
public import CFSG.GH74.Uniqueness.SU.SU1Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenOtherCfgOf

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2

variable {G : Type} [Group G] [Finite G]

namespace RankOneSylow

theorem suzuki_model_of_isCaseTwoGroup_five {K : Type} [Group K]
    (h : IsCaseTwoGroup 5 K) : ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nat.card F = 2 ^ (2 * 2 + 1) ∧ Nonempty (K ≃* CFSG.Open.GLASzGroup 2 F) := by
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := h
  rcases hd with ⟨h53, -⟩ | ⟨-, hdq⟩
  · omega
  · simp only at hdq
    subst hdq
    have hiso : CFSG.RankThree.PartOne.Census3.IsoLie K (.suzuki 2) := ⟨hv, ⟨e⟩⟩
    obtain ⟨-, a, -, F, hFf, hFfin, hfa, hF, ⟨eF⟩⟩ :=
      CFSG.RankThree.PartOne.CTP.suzukiModel_of_isoLie 2 hiso
    have ha : a = 2 := by omega
    subst ha
    exact ⟨F, hFf, hFfin, hF, ⟨eF.trans
      (MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup 2 F))⟩⟩

theorem eq_three_or_five_of_isCaseTwoGroup {p : ℕ} {K : Type} [Group K]
    (h : IsCaseTwoGroup p K) : p = 3 ∨ p = 5 := by
  obtain ⟨⟨d, hv⟩, hd, -⟩ := h
  rcases hd with ⟨h3, -⟩ | ⟨h5, -⟩
  · exact Or.inl h3
  · exact Or.inr h5

theorem isSimpleGroup_of_isCaseTwoGroup {p : ℕ} {K : Type} [Group K]
    (h : IsCaseTwoGroup p K) : IsSimpleGroup K := by
  rcases eq_three_or_five_of_isCaseTwoGroup h with rfl | rfl
  · exact isSimpleGroup_of_isCaseTwoGroup_three h
  · obtain ⟨F, hFf, hFfin, hF, ⟨eF⟩⟩ := suzuki_model_of_isCaseTwoGroup_five h
    haveI : IsSimpleGroup (CFSG.Open.Sz 2) :=
      CFSG.SignalizerFunctorTheorem.McBride.SzModel.sz_isSimpleGroup (by norm_num)
    exact (eF.trans (CFSG.ShultStronglyClosedTI.glaSzEquivNative 2 (by norm_num) hF)).isSimpleGroup

theorem isCyclic_sylow_of_isCaseTwoGroup {p : ℕ} {K : Type} [Group K] [Finite K]
    (h : IsCaseTwoGroup p K) (T : Sylow p K) : IsCyclic T := by
  rcases eq_three_or_five_of_isCaseTwoGroup h with rfl | rfl
  · exact CFSG.LocalAnalysis.RankFourTheoremC.isCyclic_sylow_three_of_l28 h T
  · obtain ⟨F, hFf, hFfin, hF, ⟨eF⟩⟩ := suzuki_model_of_isCaseTwoGroup_five h
    haveI := CFSG.Adapters.certificate43_holds
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.suzuki_model_oddSylow_cyclic
      2 (by norm_num) hF eF 5 (by norm_num) T

theorem center_trivial_of_simple {K : Type} [Group K] [Finite K] [IsSimpleGroup K] {p : ℕ}
    (hp : p.Prime) (T : Sylow p K) (hT : Nat.card T = p ^ 2) :
    ∀ k : K, (∀ k' : K, k * k' = k' * k) → k = 1 := by
  intro k hk
  by_contra hk1
  have hcen : Subgroup.center K = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
    · exfalso
      apply hk1
      have : k ∈ Subgroup.center K := Subgroup.mem_center_iff.mpr fun g => (hk g).symm
      rw [h] at this
      exact Subgroup.mem_bot.mp this
    · exact h
  letI : CommGroup K :=
    { (inferInstance : Group K) with
      mul_comm := fun a b => by
        have := Subgroup.mem_center_iff.mp (hcen ▸ Subgroup.mem_top a) b
        exact this.symm }
  have hprime := IsSimpleGroup.prime_card (α := K)
  have hdvd : p ^ 2 ∣ Nat.card K := hT ▸ Subgroup.card_subgroup_dvd_card (T : Subgroup K)
  have h1 : p ∣ Nat.card K := (dvd_pow_self p two_ne_zero).trans hdvd
  rcases (Nat.Prime.eq_one_or_self_of_dvd hprime p h1) with h | h
  · exact hp.ne_one h
  · rw [← h] at hdvd
    have := Nat.le_of_dvd hp.pos hdvd
    nlinarith [hp.two_le]

theorem card_le_of_isPGroup {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (hT : ∀ T : Sylow p K, Nat.card T = p ^ 2) {B : Subgroup K} (hB : IsPGroup p B) :
    Nat.card B ≤ p ^ 2 := by
  obtain ⟨T, hBT⟩ := hB.exists_le_sylow
  exact (Subgroup.card_le_of_le hBT).trans (hT T).le

theorem conj_injective {K : Type} [Group K]
    (hZ : ∀ k : K, (∀ k' : K, k * k' = k' * k) → k = 1) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  rw [injective_iff_map_eq_one]
  intro k hk
  refine hZ k fun k' => ?_
  have := congrArg (fun f : MulAut K => f k') hk
  simp only [MulAut.conj_apply, MulAut.one_apply] at this
  calc k * k' = (k * k' * k⁻¹) * k := by group
    _ = k' * k := by rw [this]

theorem card_le_of_isCyclic_of_pow_eq_one {K : Type} [Group K] [Finite K] {p : ℕ} (hp : 0 < p)
    {A : Subgroup K} (hA : IsCyclic A) (hAp : ∀ a ∈ A, a ^ p = 1) : Nat.card A ≤ p := by
  have hC : ∀ c : A, c ^ p = 1 := fun c => Subtype.ext (by simpa using hAp c c.2)
  rw [← IsCyclic.exponent_eq_card]
  exact Nat.le_of_dvd hp (Monoid.exponent_dvd_of_forall_pow_eq_one hC)

theorem card_map_mul_card_inf {Hh M : Type} [Group Hh] [Finite Hh] [Group M] (φ : Hh →* M)
    (F : Subgroup Hh) : Nat.card (F.map φ) * Nat.card (φ.ker ⊓ F : Subgroup Hh) = Nat.card F := by
  rw [← Subgroup.relIndex_ker, Subgroup.relIndex_mul_card]

theorem exists_isElemAbelian_card_pow_three {X : Type} [Group X] [Finite X] {p : ℕ}
    [hp : Fact p.Prime] {B : Subgroup X} (hB : 3 ≤ Open.pRank p B) :
    ∃ E ≤ B, IsElemAbelian p E ∧ Nat.card E = p ^ 3 := by
  obtain ⟨A, hAB, hA, hAcard⟩ := CFSG.SectionRank.exists_pRank hp.out.one_lt B
  obtain ⟨C, hC⟩ := Sylow.exists_subgroup_card_pow_prime (G := A) p (n := 3)
    (hAcard ▸ pow_dvd_pow p hB)
  have : IsMulCommutative A := hA.1
  have hC' : IsElemAbelian p C := ⟨inferInstance, fun x _ => Subtype.ext (hA.2 x x.property)⟩
  refine ⟨C.map A.subtype, (Subgroup.map_subtype_le C).trans hAB, hC'.map _, ?_⟩
  rw [Subgroup.card_map_of_injective A.subtype_injective, hC]

theorem exists_central_orderOf {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {R N : Subgroup X} (hR : IsPGroup p R) [N.Normal] (hne : R ⊓ N ≠ ⊥) :
    ∃ z ∈ R ⊓ N, orderOf z = p ∧ ∀ g ∈ R, g * z = z * g := by
  have hp : p.Prime := Fact.out
  obtain ⟨z, hzU, hz1, hzc⟩ := CFSG.GH74.Uniqueness.SU.SU1.exists_central_of_normal hp hR
    (inf_le_left : R ⊓ N ≤ R)
    (fun g hg u hu => ⟨R.mul_mem (R.mul_mem hg hu.1) (R.inv_mem hg),
      Subgroup.Normal.conj_mem inferInstance u hu.2 g⟩) hne
  have hzle : Subgroup.zpowers z ≤ R ⊓ N := Subgroup.zpowers_le.2 hzU
  have hAp : IsPGroup p (Subgroup.zpowers z) := hR.to_le (hzle.trans inf_le_left)
  have hA1 : Subgroup.zpowers z ≠ ⊥ := fun h => hz1 (by simpa [h] using Subgroup.mem_zpowers z)
  obtain ⟨a, ha, hao⟩ :=
    CFSG.LocalAnalysis.RankFourTheoremC.exists_mem_orderOf_eq_of_isPGroup_ne_bot hAp hA1
  refine ⟨a, hzle ha, hao, fun g hg => ?_⟩
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  exact (Commute.zpow_right (show Commute g z from hzc g hg) j).eq

section Embed

variable {Hh : Type} [Group Hh] [Finite Hh] {O : Subgroup Hh} [O.Normal]

theorem inf_eq_bot_of_isPGroup {p : ℕ} [Fact p.Prime] (hO : p.Coprime (Nat.card O))
    {A : Subgroup Hh} (hA : IsPGroup p A) : A ⊓ O = ⊥ := by
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  refine Subgroup.inf_eq_bot_of_coprime ?_
  rw [hn]
  exact hO.pow_left n

theorem card_le_of_le_comap {p : ℕ} [Fact p.Prime] (hO : p.Coprime (Nat.card O))
    {K : Subgroup (Hh ⧸ O)} (hT : ∀ T : Sylow p K, Nat.card T = p ^ 2)
    {A : Subgroup Hh} (hA : IsPGroup p A) (hAK : A ≤ K.comap (QuotientGroup.mk' O)) :
    Nat.card A ≤ p ^ 2 := by
  have hAO := inf_eq_bot_of_isPGroup hO hA
  let ρ : A →* K := ((QuotientGroup.mk' O).comp A.subtype).codRestrict K (fun a => hAK a.2)
  have hρ : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : QuotientGroup.mk' O (a : Hh) = 1 := congrArg Subtype.val ha
    have h2 : (a : Hh) ∈ O := (QuotientGroup.eq_one_iff _).mp h1
    have h3 : (a : Hh) ∈ A ⊓ O := ⟨a.2, h2⟩
    rw [hAO, Subgroup.mem_bot] at h3
    exact Subtype.ext h3
  have hrange : IsPGroup p ρ.range :=
    hA.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  calc Nat.card A = Nat.card ρ.range := Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv
    _ ≤ p ^ 2 := card_le_of_isPGroup hT hrange

end Embed

theorem exists_outer {p : ℕ} [hp : Fact p.Prime] {Hh : Type} [Group Hh] [Finite Hh] {K : Type}
    [Group K] [Finite K] (hZ : ∀ k : K, (∀ k' : K, k * k' = k' * k) → k = 1)
    (hcyc : ∀ T : Sylow p K, IsCyclic T) (φ : Hh →* MulAut K) {F : Subgroup Hh}
    (hF : IsElemAbelian p F) (hF3 : Nat.card F = p ^ 3)
    (hker : Nat.card (φ.ker ⊓ F : Subgroup Hh) ≤ p) :
    ∃ a ∈ F, φ a ∉ (MulAut.conj : K →* MulAut K).range := by
  by_contra hcon
  push Not at hcon
  have hcinj : Function.Injective (MulAut.conj : K →* MulAut K) := conj_injective hZ
  set E₁ : Subgroup (MulAut K) := F.map φ with hE₁
  have hE₁le : E₁ ≤ (MulAut.conj : K →* MulAut K).range := by
    rintro _ ⟨a, ha, rfl⟩
    exact hcon a ha
  have hcard := card_map_mul_card_inf φ F
  set E₂ : Subgroup K := E₁.comap (MulAut.conj : K →* MulAut K) with hE₂
  have hmap : E₂.map (MulAut.conj : K →* MulAut K) = E₁ := by
    rw [hE₂, Subgroup.map_comap_eq, inf_of_le_right hE₁le]
  have hcard2 : Nat.card E₂ = Nat.card E₁ := by
    rw [← hmap]
    exact (Subgroup.card_map_of_injective hcinj).symm
  have hE₂p : ∀ x ∈ E₂, x ^ p = 1 := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := (hx : (MulAut.conj : K →* MulAut K) x ∈ E₁)
    apply hcinj
    rw [map_pow, ← hax, ← map_pow, hF.2 a ha, map_one, map_one]
  have hE₂P : IsPGroup p E₂ := fun x => ⟨1, Subtype.ext (by simpa using hE₂p x x.2)⟩
  obtain ⟨T, hT⟩ := hE₂P.exists_le_sylow
  haveI := hcyc T
  have hE₂c : IsCyclic E₂ := Subgroup.isCyclic_of_le hT
  have hle : Nat.card E₂ ≤ p := card_le_of_isCyclic_of_pow_eq_one hp.out.pos hE₂c hE₂p
  have hpos : 0 < p := hp.out.pos
  have h2 : p ^ 2 ≤ Nat.card E₁ := by
    have : p ^ 2 * p ≤ Nat.card E₁ * p := by
      calc p ^ 2 * p = p ^ 3 := by ring
        _ = Nat.card E₁ * Nat.card (φ.ker ⊓ F : Subgroup Hh) := by rw [hcard, hF3]
        _ ≤ Nat.card E₁ * p := Nat.mul_le_mul_left _ hker
    exact Nat.le_of_mul_le_mul_right this hpos
  have h3 : p < p ^ 2 := by
    have := hp.out.two_le
    nlinarith
  omega

theorem inf_ker_ne_bot {p : ℕ} [hp : Fact p.Prime] {Hh : Type} [Group Hh] [Finite Hh] {K : Type}
    [Group K] [Finite K] (hZ : ∀ k : K, (∀ k' : K, k * k' = k' * k) → k = 1)
    (hcyc : ∀ T : Sylow p K, IsCyclic T) (hT2 : ∀ T : Sylow p K, Nat.card T = p ^ 2)
    (hA3 : ∀ A : Subgroup (MulAut K), IsPGroup p A → Nat.card A ≤ p ^ 3)
    (φ : Hh →* MulAut K) {F : Subgroup Hh} (hF : IsElemAbelian p F) (hF3 : Nat.card F = p ^ 3) :
    φ.ker ⊓ F ≠ ⊥ := by
  intro hcon
  have hcinj := conj_injective hZ
  have hE₁card : Nat.card (F.map φ) = p ^ 3 := by
    have := card_map_mul_card_inf φ F
    rw [hcon, Subgroup.card_bot, mul_one, hF3] at this
    exact this
  have hE₁P : IsPGroup p (F.map φ) := hF.isPGroup.map φ
  obtain ⟨S, hS⟩ := hE₁P.exists_le_sylow
  have hSle : Nat.card S ≤ p ^ 3 := hA3 S S.isPGroup'
  have hSE : (S : Subgroup (MulAut K)) = F.map φ :=
    (Subgroup.eq_of_le_of_card_ge hS (by rw [hE₁card]; exact hSle)).symm
  obtain ⟨T⟩ : Nonempty (Sylow p K) := inferInstance
  haveI := hcyc T
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := T)
  have hgord : orderOf (g : K) = p ^ 2 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hT2 T]
  set u : MulAut K := MulAut.conj (g : K) with hu
  have huord : orderOf u = p ^ 2 := by
    rw [hu, ← hgord]
    exact orderOf_injective _ hcinj _
  have huP : IsPGroup p (Subgroup.zpowers u) := IsPGroup.of_card (by rw [Nat.card_zpowers, huord])
  obtain ⟨S', hS'⟩ := huP.exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq (MulAut K) S S'
  have huS' : u ∈ (S' : Subgroup (MulAut K)) := hS' (Subgroup.mem_zpowers u)
  rw [← hm, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at huS'
  obtain ⟨s, hs, hsu⟩ := huS'
  rw [hSE] at hs
  obtain ⟨a, ha, rfl⟩ := hs
  have hup : u ^ p = 1 := by
    rw [← hsu, MulAut.smul_def, MulAut.conj_apply, conj_pow, ← map_pow, hF.2 a ha, map_one,
      mul_one, mul_inv_cancel]
  have hdvd : orderOf u ∣ p := orderOf_dvd_of_pow_eq_one hup
  rw [huord] at hdvd
  have := Nat.le_of_dvd hp.out.pos hdvd
  nlinarith [hp.out.two_le]

section Act

variable {Hh : Type} [Group Hh] (O : Subgroup Hh) [O.Normal] (K : Subgroup (Hh ⧸ O)) [K.Normal]

noncomputable def act : Hh →* MulAut K :=
  MulAut.conjNormal.comp (QuotientGroup.mk' O)

variable {O K}

theorem act_apply (h : Hh) (k : K) :
    ((act O K h k : K) : Hh ⧸ O) = (h : Hh ⧸ O) * k * (h : Hh ⧸ O)⁻¹ := by
  simp [act, MulAut.conjNormal_apply]

theorem act_eq_conj {h : Hh} (hk : (h : Hh ⧸ O) ∈ K) :
    act O K h = MulAut.conj (⟨(h : Hh ⧸ O), hk⟩ : K) := by
  ext k
  rw [act_apply]
  simp [MulAut.conj_apply]

theorem mem_ker_act {h : Hh} :
    h ∈ (act O K).ker ↔ (h : Hh ⧸ O) ∈ Subgroup.centralizer (K : Set (Hh ⧸ O)) := by
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro h1 k hk
    have := congrArg (fun f : MulAut K => ((f ⟨k, hk⟩ : K) : Hh ⧸ O)) h1
    simp only [act_apply, MulAut.one_apply] at this
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  · intro h1
    ext k
    rw [act_apply, MulAut.one_apply, mul_inv_eq_iff_eq_mul]
    exact (h1 k k.2).symm

theorem ker_act_eq :
    (act O K).ker = (Subgroup.centralizer (K : Set (Hh ⧸ O))).comap (QuotientGroup.mk' O) := by
  ext h
  rw [mem_ker_act]
  rfl

theorem mem_sup_iff_act_mem_range (h : Hh) :
    h ∈ K.comap (QuotientGroup.mk' O) ⊔ (act O K).ker ↔
      act O K h ∈ (MulAut.conj : K →* MulAut K).range := by
  constructor
  · have hle : K.comap (QuotientGroup.mk' O) ⊔ (act O K).ker ≤
        (MulAut.conj : K →* MulAut K).range.comap (act O K) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · exact ⟨⟨(x : Hh ⧸ O), hx⟩, (act_eq_conj hx).symm⟩
      · rw [Subgroup.mem_comap, (MonoidHom.mem_ker.mp hx)]
        exact Subgroup.one_mem _
    exact fun hh => hle hh
  · rintro ⟨k, hk⟩
    obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective O (k : Hh ⧸ O)
    have hbK : (b : Hh ⧸ O) ∈ K := by
      have : QuotientGroup.mk' O b = (b : Hh ⧸ O) := rfl
      rw [← this, hb]
      exact k.2
    have hab : act O K b = MulAut.conj k := by
      rw [act_eq_conj hbK]
      congr 1
      exact Subtype.ext hb
    have hker : h * b⁻¹ ∈ (act O K).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab, hk, mul_inv_cancel]
    have hbmem : b ∈ K.comap (QuotientGroup.mk' O) := hbK
    have : h * b⁻¹ * b ∈ (act O K).ker ⊔ K.comap (QuotientGroup.mk' O) :=
      Subgroup.mul_mem_sup hker hbmem
    rw [inv_mul_cancel_right, sup_comm] at this
    exact this

end Act

section Core

variable {p : ℕ} {H : Subgroup G} {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} [K.Normal]

theorem d1PlusCore_eq :
    d1PlusCore p H K = (act (primeComplementCore (G := H) p) K).ker.map H.subtype := by
  unfold d1PlusCore
  rw [ker_act_eq]

theorem mem_hyp111_sup_d1PlusCore_iff (a : H) :
    (a : G) ∈ hyp111Pre p H K ⊔ d1PlusCore p H K ↔
      act (primeComplementCore (G := H) p) K a ∈ (MulAut.conj : K →* MulAut K).range := by
  have h : hyp111Pre p H K ⊔ d1PlusCore p H K =
      (K.comap (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊔
        (act (primeComplementCore (G := H) p) K).ker).map H.subtype := by
    rw [Subgroup.map_sup, d1PlusCore_eq]
    rfl
  rw [h, ← mem_sup_iff_act_mem_range]
  exact Subgroup.mem_map_iff_mem H.subtype_injective

end Core

section Lift

variable {p : ℕ} {H : Subgroup G}

theorem d1LiftX_mono (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) {Q W : Subgroup G}
    (h : Q ≤ W) : d1LiftX p H Q K ≤ d1LiftX p H W K := by
  unfold d1LiftX
  exact Subgroup.map_mono (inf_le_inf_right _ (Subgroup.subgroupOf_mono H h))

theorem card_d1LiftX_le [Fact p.Prime] {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hT : ∀ T : Sylow p K, Nat.card T = p ^ 2) {W : Subgroup G} (hWp : IsPGroup p W) :
    Nat.card (d1LiftX p H W K) ≤ p ^ 2 := by
  set A : Subgroup H :=
    W.subgroupOf H ⊓ K.comap (QuotientGroup.mk' (primeComplementCore (G := H) p))
  have hA : IsPGroup p A := hWp.comap_subtype.to_le inf_le_left
  have := card_le_of_le_comap (primeComplementCore_coprime (G := H) p) hT hA inf_le_right
  unfold d1LiftX
  rwa [Subgroup.card_map_of_injective H.subtype_injective]

theorem exists_sylow_eq_subgroupOf [Fact p.Prime] {W : Subgroup G} (hWH : W ≤ H)
    (hWp : IsPGroup p W)
    (hmax : ∀ V : Subgroup G, V ≤ H → IsPGroup p V → W ≤ V → V = W) :
    ∃ S : Sylow p H, (S : Subgroup H) = W.subgroupOf H := by
  have hW'p : IsPGroup p (W.subgroupOf H) := hWp.comap_subtype
  obtain ⟨S, hWS⟩ := hW'p.exists_le_sylow
  refine ⟨S, le_antisymm ?_ hWS⟩
  have hmapW : (W.subgroupOf H).map H.subtype = W := Subgroup.map_subgroupOf_eq_of_le hWH
  have h1 : (S : Subgroup H).map H.subtype = W :=
    hmax _ (Subgroup.map_subtype_le _) (S.isPGroup'.map _)
      (by rw [← hmapW]; exact Subgroup.map_mono hWS)
  intro x hx
  have : (x : G) ∈ (S : Subgroup H).map H.subtype := ⟨x, hx, rfl⟩
  rw [h1] at this
  exact this

end Lift

end RankOneSylow

theorem exists_rankOneSylowData (hS : Setting G) {p : ℕ} {P : Sylow p G} {M H Q : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hd : AGL81CfgData p P M H Q K)
    (hshape : IsCaseTwoGroup p ↥K) (hKn : K.Normal) (hXM : d1PlusCore p H K ≤ M)
    (hX1 : Open.pRank p (d1PlusCore p H K) ≤ 1) (hH3 : 3 ≤ Open.pRank p H)
    (hSA : KFactCaseTwoSylowAut) (hCT : KFactCaseTwoLocal) :
    ∃ (W : Subgroup G) (y z : G), RankOneSylowData p M H Q K W y z := by
  haveI := hKn
  obtain ⟨H₁, R₁, hesc⟩ := hd.escape
  have hp : p.Prime := hesc.prime
  have hp2 : p ≠ 2 := hesc.ne_two
  haveI : Fact p.Prime := ⟨hp⟩
  have hO : p.Coprime (Nat.card (primeComplementCore (G := H) p)) :=
    primeComplementCore_coprime (G := H) p
  obtain ⟨hT2, hA3⟩ := hSA p ↥K hshape
  haveI hsimple : IsSimpleGroup ↥K := RankOneSylow.isSimpleGroup_of_isCaseTwoGroup hshape
  obtain ⟨T₀⟩ : Nonempty (Sylow p ↥K) := inferInstance
  have hZ : ∀ k : K, (∀ k' : K, k * k' = k' * k) → k = 1 :=
    RankOneSylow.center_trivial_of_simple hp T₀ (hT2 T₀)
  have hcyc : ∀ T : Sylow p ↥K, IsCyclic ↥T :=
    RankOneSylow.isCyclic_sylow_of_isCaseTwoGroup hshape
  obtain ⟨W, hQW, hWH, hWM, hWp, hWmax⟩ :=
    exists_maxPSubgroup_of_normalizer_le hd.base.2.1 hd.le_H hd.base.1
      (fun U hQU hUM hU =>
        normalizer_le_of_isAGLQ_of_escape hesc (isAGLQ_of_le hd.base hQU hUM hU))
  obtain ⟨hAX, S, hSmap, ⟨e⟩⟩ := OtherCfg.d1LiftX_facts_gen hd hZ
  have hQcard : Nat.card (d1LiftX p H Q K) = p ^ 2 := by
    rw [Nat.card_congr e.toEquiv]
    exact hT2 S
  haveI : IsCyclic ↥(d1LiftX p H Q K) := e.isCyclic.mpr (hcyc S)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(d1LiftX p H Q K))
  have hyQ : d1LiftX p H Q K = Subgroup.zpowers (g : G) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, by simpa using congrArg Subtype.val hn⟩
    · rw [Subgroup.zpowers_le]
      exact g.2
  have hyord : orderOf (g : G) = p ^ 2 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hQcard]
  have hle : d1LiftX p H Q K ≤ d1LiftX p H W K := RankOneSylow.d1LiftX_mono K hQW
  have hWcard : Nat.card (d1LiftX p H W K) ≤ p ^ 2 := RankOneSylow.card_d1LiftX_le hT2 hWp
  have hyW : d1LiftX p H W K = Subgroup.zpowers (g : G) :=
    (Subgroup.eq_of_le_of_card_ge hle (by rw [hQcard]; exact hWcard)).symm.trans hyQ
  have hcycWX : IsCyclic ↥(W ⊓ d1PlusCore p H K) :=
    CFSG.RankThree.PartOne.isCyclic_of_pRank_le_one hp hp2 inf_le_right
      (hWp.to_le inf_le_left) (by rw [CFSG.SectionRank.pRank_coe_eq_openPRank]; exact hX1)
  set W' : Subgroup H := W.subgroupOf H
  have hW'p : IsPGroup p W' := hWp.comap_subtype
  obtain ⟨S₀, hS₀⟩ := RankOneSylow.exists_sylow_eq_subgroupOf hWH hWp hWmax
  have hr3 : 3 ≤ Open.pRank p (S₀ : Subgroup H) := by
    rw [(CFSG.SectionRank.pRank_sylow S₀).1, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup H]
    exact hH3
  obtain ⟨F, hFS, hF, hF3⟩ := RankOneSylow.exists_isElemAbelian_card_pow_three hr3
  rw [hS₀] at hFS
  set φ : H →* MulAut ↥K := RankOneSylow.act (primeComplementCore (G := H) p) K
  have hker1 : Nat.card (φ.ker ⊓ F : Subgroup H) ≤ p := by
    have hE : IsElemAbelian p (φ.ker ⊓ F : Subgroup H) := hF.mono inf_le_right
    obtain ⟨k, hk⟩ := CFSG.GH74.Uniqueness.SU.SU1.IsElemAbelian.exists_card hp hE
    have hk1 : k ≤ Open.pRank p φ.ker :=
      CFSG.SectionRank.le_pRank hp.one_lt inf_le_left hE hk
    have hk2 : Open.pRank p φ.ker ≤ 1 := by
      refine (CFSG.SectionRank.pRank_le_map hp.one_lt H.subtype H.subtype_injective φ.ker).trans ?_
      rw [← RankOneSylow.d1PlusCore_eq]
      exact hX1
    rw [hk]
    calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
      _ = p := pow_one p
  have hne : φ.ker ⊓ F ≠ ⊥ := RankOneSylow.inf_ker_ne_bot hZ hcyc hT2 hA3 φ hF hF3
  obtain ⟨a', ha'F, ha'out⟩ := RankOneSylow.exists_outer hZ hcyc φ hF hF3 hker1
  haveI : φ.ker.Normal := MonoidHom.normal_ker φ
  have hne' : W' ⊓ φ.ker ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ W' ⊓ φ.ker := ⟨hFS hx.2, hx.1⟩
    rw [h] at this
    exact this
  obtain ⟨z', hz'mem, hz'ord, hz'cent⟩ := RankOneSylow.exists_central_orderOf hW'p hne'
  have hker_eq : d1PlusCore p H K = φ.ker.map H.subtype := RankOneSylow.d1PlusCore_eq
  refine ⟨W, (g : G), (z' : G), ?_⟩
  refine
    { pgroup := hWp
      le := le_inf hWH hWM
      max := fun V hV hVH hWV => hWmax V hVH hV hWV
      z_mem := ⟨hz'mem.1, ?_⟩
      z_order := ?_
      z_central := ?_
      cyclic := hcycWX
      y_lift := hyW
      y_Q := hyQ
      y_order := hyord
      y_X := ?_
      outer := ?_
      noncomm := ?_ }
  · rw [hker_eq]
    exact ⟨z', hz'mem.2, rfl⟩
  · rw [Subgroup.orderOf_coe]
    exact hz'ord
  · intro w hw
    have := hz'cent ⟨w, hWH hw⟩ hw
    exact congrArg Subtype.val this
  · rw [← hyQ]
    exact hAX
  · refine ⟨(a' : G), hFS ha'F, ?_, ?_⟩
    · have h1 : a' ≠ 1 := by
        rintro rfl
        exact ha'out (by rw [map_one]; exact Subgroup.one_mem _)
      rw [Subgroup.orderOf_coe]
      exact orderOf_eq_prime (hF.2 a' ha'F) h1
    · rw [RankOneSylow.mem_hyp111_sup_d1PlusCore_iff]
      exact ha'out
  · intro a haW haX hcomm
    have haH : a ∈ H := hWH haW
    have hyH : (g : G) ∈ H := d1LiftX_le_H p H Q K g.2
    set a₀ : H := ⟨a, haH⟩
    set y₀ : H := ⟨(g : G), hyH⟩
    have hcomm' : Commute a₀ y₀ := Subtype.ext hcomm
    have hfix : ∀ x ∈ (S : Subgroup ↥K), φ a₀ x = x := by
      intro x hx
      have hx' : (x : H ⧸ primeComplementCore (G := H) p) ∈
          ((d1LiftX p H Q K).subgroupOf H).map
            (QuotientGroup.mk' (primeComplementCore (G := H) p)) := by
        rw [← hSmap]
        exact ⟨x, hx, rfl⟩
      obtain ⟨u, hu, hux⟩ := hx'
      have hu2 : (u : G) ∈ d1LiftX p H Q K := hu
      rw [hyQ] at hu2
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hu2
      have hu' : u = y₀ ^ m := Subtype.ext (by simpa using hm.symm)
      have hcu : a₀ * u * a₀⁻¹ = u := by
        rw [hu', (hcomm'.zpow_right m).eq, mul_inv_cancel_right]
      apply Subtype.ext
      rw [RankOneSylow.act_apply]
      rw [← hux]
      have := congrArg (QuotientGroup.mk' (primeComplementCore (G := H) p)) hcu
      simpa using this
    obtain ⟨t, -, hft⟩ := ((hCT p ↥K hshape).2.2 S).2.1 (φ a₀) hfix
    exact haX ((RankOneSylow.mem_hyp111_sup_d1PlusCore_iff a₀).mpr ⟨t, hft.symm⟩)

end CFSG.LocalAnalysis.RankThreeTheoremC
