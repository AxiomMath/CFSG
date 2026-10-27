module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2K0
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2GenDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Cyclic
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Lemmas
import CFSG.ClassicalInvolution.LBalance.Glauberman.SylowTools
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3U3RemarkAux

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

structure PointConfig3 (Typ : ℕ → ∀ (Q : Type) [Group Q], Prop) (G : Type) [Group G] [Finite G]
    (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x : G) (J : Subgroup G) : Prop where
  sigma : p ∈ rankThreeSigmaA G
  core : IsCoreMaxLocal p P M
  fail : ¬ rankThreeGamma 1 p (P : Subgroup G) ≤ M
  larger : LargerPrimesUnique G p
  generic : IsGenericPoint p P M x
  three : p = 3
  le_cent : J ≤ Subgroup.centralizer ({x} : Set G)
  cent_le : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (J : Set G)
  perfect : Group.IsPerfect J
  lt : rankThreePrimeCore p J < J
  minimal : ∀ N : Subgroup G, N ≤ J → (N.subgroupOf J).Normal → rankThreePrimeCore p J ≤ N →
    N = rankThreePrimeCore p J ∨ N = J
  not_le : ¬ J ≤ M
  typ : ∃ (Q : Type) (_ : Group Q) (ψ : ↥J →* Q), Function.Surjective ψ ∧
    ψ.ker = (rankThreePrimeCore p J).subgroupOf J ∧ Typ p Q

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}
  {J : Subgroup G}

theorem PointConfig3.prime {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}
    (hc : PointConfig3 Typ G p P M x J) : p.Prime :=
  sigmaA_prime p hc.sigma

theorem u3K0_conj_gen3 {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}
    (hc : PointConfig3 Typ G p P M x J) :
    ∀ c ∈ Subgroup.centralizer ({x} : Set G), ∀ k ∈ u3K0 p x J, c * k * c⁻¹ ∈ u3K0 p x J := by
  intro c hcC k hk
  obtain ⟨hkC, hkN, hkO⟩ := hk
  have hcN : c ∈ Subgroup.normalizer (J : Set G) := hc.cent_le hcC
  refine ⟨mul_mem (mul_mem hcC hkC) (inv_mem hcC), mul_mem (mul_mem hcN hkN) (inv_mem hcN),
    fun j hj => ?_⟩
  have hj' : c⁻¹ * j * c ∈ J := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hcN) j).mp hj
    simpa using this
  have h1 := u3_core_conj hcN (hkO (c⁻¹ * j * c) hj')
  have e : c * (k * (c⁻¹ * j * c) * k⁻¹ * (c⁻¹ * j * c)⁻¹) * c⁻¹ =
      c * k * c⁻¹ * j * (c * k * c⁻¹)⁻¹ * j⁻¹ := by
    group
  rwa [e] at h1

theorem u3_core_le_K0_gen3 {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}
    (hc : PointConfig3 Typ G p P M x J) : rankThreePrimeCore p J ≤ u3K0 p x J := by
  intro o ho
  have hOJ : rankThreePrimeCore p J ≤ J := CFSG.AGLEmbedding.glbPrimeCore_le p J
  refine ⟨hc.le_cent (hOJ ho), Subgroup.le_normalizer (hOJ ho), fun j hj => ?_⟩
  have h1 : j * o⁻¹ * j⁻¹ ∈ rankThreePrimeCore p J :=
    u3_core_conj (Subgroup.le_normalizer hj) (inv_mem ho)
  have h2 := mul_mem ho h1
  have e : o * (j * o⁻¹ * j⁻¹) = o * j * o⁻¹ * j⁻¹ := by group
  rwa [e] at h2

theorem x_mem_u3K0_gen3 {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}
    (hc : PointConfig3 Typ G p P M x J) : x ∈ u3K0 p x J := by
  have hxC : x ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  refine ⟨hxC, hc.cent_le hxC, fun j hj => ?_⟩
  have h : j * x = x * j := Subgroup.mem_centralizer_singleton_iff.mp (hc.le_cent hj)
  have e : x * j * x⁻¹ * j⁻¹ = 1 := by rw [← h]; group
  rw [e]
  exact one_mem _

theorem u3_T_inf_K0_gen3 {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}
    (hc : PointConfig3 Typ G p P M x J) : u3T P x J ⊓ u3K0 p x J = ⊥ := by
  have hp : p.Prime := hc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, hQg, ψ, hψ, hker, hQ⟩ := hc.typ
  set O : Subgroup G := rankThreePrimeCore p J with hO
  have hOJ : O ≤ J := CFSG.AGLEmbedding.glbPrimeCore_le p J
  have hOcop : p.Coprime (Nat.card O) := CFSG.AGLEmbedding.glbPrimeCore_coprime p J
  have hZ : Subgroup.center Q = ⊥ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.u3main_center_bot hOJ hc.perfect hc.lt hc.minimal ψ hψ hker
  have hPO : (P : Subgroup G) ⊓ O = ⊥ := by
    have hPp : IsPGroup p ↥((P : Subgroup G) ⊓ O) := P.isPGroup'.to_inf_left
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hPp
    have hdvd : Nat.card ((P : Subgroup G) ⊓ O : Subgroup G) ∣ Nat.card O :=
      Subgroup.card_dvd_of_le inf_le_right
    have hk0 : k = 0 := by
      by_contra hk0
      have : p ∣ Nat.card O := (dvd_pow_self p hk0).trans (hk ▸ hdvd)
      exact (hp.coprime_iff_not_dvd.mp hOcop) this
    rw [hk0, pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq _ hk
  rw [eq_bot_iff]
  rintro t ⟨htT, htK⟩
  obtain ⟨⟨htP, htC⟩, htJ⟩ := htT
  obtain ⟨-, -, htO⟩ := htK
  have hcentral : ψ ⟨t, htJ⟩ ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨j, rfl⟩ := hψ q
    have hmem : (⟨t, htJ⟩ * j * (⟨t, htJ⟩ : J)⁻¹ * j⁻¹ : J) ∈ ψ.ker := by
      rw [hker, Subgroup.mem_subgroupOf]
      exact htO (j : G) j.2
    have h1 : ψ ⟨t, htJ⟩ * ψ j * (ψ ⟨t, htJ⟩)⁻¹ * (ψ j)⁻¹ = 1 := by
      have := MonoidHom.mem_ker.mp hmem
      simpa using this
    have h2 : ψ ⟨t, htJ⟩ * ψ j = ψ j * ψ ⟨t, htJ⟩ := by
      have := mul_inv_eq_one.mp h1
      exact mul_inv_eq_iff_eq_mul.mp this
    exact h2.symm
  rw [hZ, Subgroup.mem_bot] at hcentral
  have htker : (⟨t, htJ⟩ : J) ∈ ψ.ker := hcentral
  rw [hker, Subgroup.mem_subgroupOf] at htker
  have : t ∈ (P : Subgroup G) ⊓ O := ⟨htP, htker⟩
  rw [hPO] at this
  exact this

private theorem dec_exists_conj_hom (J H : Subgroup G) (hH : H ≤ Subgroup.normalizer (J : Set G)) :
    ∃ ι : H →* MulAut J, ∀ (c : H) (j : J), ((ι c j : J) : G) = (c : G) * j * (c : G)⁻¹ := by
  let f : ∀ c : G, c ∈ Subgroup.normalizer (J : Set G) → MulAut J := fun c hc =>
    { toFun := fun j => ⟨c * j * c⁻¹, (Subgroup.mem_normalizer_iff.mp hc j).mp j.2⟩
      invFun := fun j => ⟨c⁻¹ * j * c, by
        simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hc) j).mp j.2⟩
      left_inv := fun j => by ext; simp [mul_assoc]
      right_inv := fun j => by ext; simp [mul_assoc]
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  refine ⟨{ toFun := fun c => f c (hH c.2), map_one' := ?_, map_mul' := ?_ }, fun c j => rfl⟩
  · ext j; simp [f]
  · intro a b; ext j; simp [f, mul_assoc]

private theorem dec_exists_descent {J Q H : Type} [Group J] [Group Q] [Group H] (ψ : J →* Q)
    (hψ : Function.Surjective ψ) (ι : H →* MulAut J)
    (h : ∀ c j, ψ j = 1 → ψ (ι c j) = 1) :
    ∃ θ : H →* MulAut Q, ∀ c j, θ c (ψ j) = ψ (ι c j) := by
  have key : ∀ c : H, ∃ f : Q →* Q, ∀ j, f (ψ j) = ψ (ι c j) := by
    intro c
    refine ⟨ψ.liftOfSurjective hψ ⟨ψ.comp (ι c).toMonoidHom, fun j hj => h c j hj⟩, fun j => ?_⟩
    simp
  choose F hF using key
  have hmul : ∀ c d : H, ∀ q, F (c * d) q = F c (F d q) := by
    intro c d q
    obtain ⟨j, rfl⟩ := hψ q
    rw [hF, hF, hF]
    simp
  have hone : ∀ q, F 1 q = q := by
    intro q
    obtain ⟨j, rfl⟩ := hψ q
    rw [hF]
    simp
  let θ' : ∀ c : H, MulAut Q := fun c =>
    { toFun := F c
      invFun := F c⁻¹
      left_inv := fun q => by rw [← hmul, inv_mul_cancel, hone]
      right_inv := fun q => by rw [← hmul, mul_inv_cancel, hone]
      map_mul' := (F c).map_mul }
  refine ⟨{ toFun := θ', map_one' := ?_, map_mul' := ?_ }, fun c j => hF c j⟩
  · ext q; exact hone q
  · intro a b; ext q; exact hmul a b q

theorem u3_P_decomp_core3 {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}
    (hc : PointConfig3 Typ G p P M x J)
    (hP : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G)) {k : ℕ}
    (hTcard : Nat.card (u3T P x J) = p ^ k)
    (hAut : ∀ (K : Type) [Group K] [Finite K], Typ p K → Subgroup.center K = ⊥ →
      ∀ S : Subgroup (MulAut K), IsPGroup p S → Nat.card S ∣ p ^ k) :
    (P : Subgroup G) ≤ u3T P x J ⊔ ((P : Subgroup G) ⊓ u3K0 p x J) := by
  have hp : p.Prime := hc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, hQg, ψ, hψ, hker, hQ⟩ := hc.typ
  haveI : Finite Q := Finite.of_surjective ψ hψ
  have hPN : (P : Subgroup G) ≤ Subgroup.normalizer (J : Set G) := hP.trans hc.cent_le
  obtain ⟨ι, hι⟩ := dec_exists_conj_hom J (P : Subgroup G) hPN
  have hOker : ∀ j : J, ψ j = 1 ↔ (j : G) ∈ rankThreePrimeCore p J := by
    intro j
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  have hιker : ∀ (c : (P : Subgroup G)) (j : J), ψ j = 1 → ψ (ι c j) = 1 := by
    intro c j hj
    rw [hOker] at hj ⊢
    rw [hι]
    exact u3_core_conj (hPN c.2) hj
  obtain ⟨θ, hθ⟩ := dec_exists_descent ψ hψ ι hιker
  have hθK : ∀ c : (P : Subgroup G), θ c = 1 → (c : G) ∈ u3K0 p x J := by
    intro c hc1
    refine ⟨hP c.2, hPN c.2, fun j hj => ?_⟩
    have h1 : ψ (ι c ⟨j, hj⟩) = ψ ⟨j, hj⟩ := by
      rw [← hθ, hc1]; rfl
    have h2 : ψ ((ι c ⟨j, hj⟩) * ⟨j, hj⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    have h3 := (hOker _).mp h2
    simpa [hι] using h3
  have hTP : u3T P x J ≤ (P : Subgroup G) := (inf_le_left : u3T P x J ≤ u3S P x).trans inf_le_left
  set T₀ : Subgroup (P : Subgroup G) := (u3T P x J).subgroupOf (P : Subgroup G) with hT₀
  have hinj : Function.Injective (θ.comp T₀.subtype) := by
    rw [injective_iff_map_eq_one]
    intro t ht
    have htK : ((t : (P : Subgroup G)) : G) ∈ u3K0 p x J := hθK t ht
    have htT : ((t : (P : Subgroup G)) : G) ∈ u3T P x J := t.2
    have : ((t : (P : Subgroup G)) : G) ∈ u3T P x J ⊓ u3K0 p x J := ⟨htT, htK⟩
    rw [u3_T_inf_K0_gen3 hc, Subgroup.mem_bot] at this
    exact Subtype.ext (Subtype.ext this)
  have hcardT : Nat.card ↥(T₀.map θ) = p ^ k := by
    have e1 : (θ.comp T₀.subtype).range = T₀.map θ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← e1, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTP).toEquiv]
    exact hTcard
  have hSp : IsPGroup p θ.range :=
    P.isPGroup'.of_surjective θ.rangeRestrict θ.rangeRestrict_surjective
  haveI : Finite θ.range := Finite.of_surjective θ.rangeRestrict θ.rangeRestrict_surjective
  have hOJ : rankThreePrimeCore p J ≤ J := CFSG.AGLEmbedding.glbPrimeCore_le p J
  have hZ : Subgroup.center Q = ⊥ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.u3main_center_bot hOJ hc.perfect hc.lt hc.minimal ψ hψ hker
  have hdvd : Nat.card θ.range ∣ p ^ k := hAut Q hQ hZ θ.range hSp
  have hA : T₀.map θ = θ.range :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.map_le_range θ T₀) (by
      rw [hcardT]; exact Nat.le_of_dvd (pow_pos hp.pos k) hdvd)
  intro s hs
  have hs' : θ ⟨s, hs⟩ ∈ T₀.map θ := by
    rw [hA]; exact ⟨⟨s, hs⟩, rfl⟩
  obtain ⟨t, ht, htθ⟩ := hs'
  have hkθ : θ (t⁻¹ * ⟨s, hs⟩) = 1 := by rw [map_mul, map_inv, htθ, inv_mul_cancel]
  have hkK := hθK _ hkθ
  have hkP : ((t⁻¹ * ⟨s, hs⟩ : (P : Subgroup G)) : G) ∈ (P : Subgroup G) :=
    (t⁻¹ * ⟨s, hs⟩).2
  have hsd : s = (t : G) * ((t⁻¹ * ⟨s, hs⟩ : (P : Subgroup G)) : G) := by
    simp
  rw [hsd]
  exact Subgroup.mul_mem_sup ht ⟨hkP, hkK⟩

theorem u3_P_decomp_gen3 {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}
    (hc : PointConfig3 Typ G p P M x J)
    (hP : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G)) (hTstr : TypeTStruct p P x J)
    (hAut : TypeAutPCard Typ p) :
    (P : Subgroup G) ≤ u3T P x J ⊔ ((P : Subgroup G) ⊓ u3K0 p x J) :=
  u3_P_decomp_core3 hc hP hTstr.1 hAut

private theorem dec_inf_core (hp : p.Prime) :
    (P : Subgroup G) ⊓ rankThreePrimeCore p J = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hOcop : p.Coprime (Nat.card (rankThreePrimeCore p J)) :=
    CFSG.AGLEmbedding.glbPrimeCore_coprime p J
  have hPp : IsPGroup p ↥((P : Subgroup G) ⊓ rankThreePrimeCore p J) := P.isPGroup'.to_inf_left
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hPp
  have hdvd : Nat.card ((P : Subgroup G) ⊓ rankThreePrimeCore p J : Subgroup G) ∣
      Nat.card (rankThreePrimeCore p J) := Subgroup.card_dvd_of_le inf_le_right
  have hk0 : k = 0 := by
    by_contra hk0
    have : p ∣ Nat.card (rankThreePrimeCore p J) := (dvd_pow_self p hk0).trans (hk ▸ hdvd)
    exact (hp.coprime_iff_not_dvd.mp hOcop) this
  rw [hk0, pow_zero] at hk
  exact Subgroup.eq_bot_of_card_eq _ hk

private theorem dec_mem_sup_of_commute {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {s : G} (hs : s ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, s = a * b := by
  have hr := MonoidHom.noncommCoprod_range A.subtype B.subtype (fun a b => h a a.2 b b.2)
  rw [Subgroup.range_subtype, Subgroup.range_subtype] at hr
  rw [← hr] at hs
  obtain ⟨⟨a, b⟩, rfl⟩ := hs
  exact ⟨a, a.2, b, b.2, rfl⟩

theorem u3_pdata_common3 {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}
    (hc : PointConfig3 Typ G p P M x J)
    (hP : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G)) (hSdec : TypeSDecomp p P x J)
    (hdec : (P : Subgroup G) ≤ u3T P x J ⊔ ((P : Subgroup G) ⊓ u3K0 p x J)) :
    u3T P x J ≤ (P : Subgroup G) ∧ (P : Subgroup G) ⊓ u3K0 p x J ≤ (P : Subgroup G) ∧
      u3T P x J ⊔ ((P : Subgroup G) ⊓ u3K0 p x J) = (P : Subgroup G) ∧
      u3T P x J ⊓ ((P : Subgroup G) ⊓ u3K0 p x J) = ⊥ ∧
      (∀ t ∈ u3T P x J, ∀ d ∈ (P : Subgroup G) ⊓ u3K0 p x J, t * d = d * t) ∧
      IsCyclic ↥((P : Subgroup G) ⊓ u3K0 p x J) ∧ x ∈ (P : Subgroup G) ⊓ u3K0 p x J ∧
        orderOf x = p := by
  have hp : p.Prime := hc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hTP : u3T P x J ≤ (P : Subgroup G) := (inf_le_left : u3T P x J ≤ u3S P x).trans inf_le_left
  have hPN : (P : Subgroup G) ≤ Subgroup.normalizer (J : Set G) := hP.trans hc.cent_le
  have hPO := dec_inf_core (P := P) (J := J) hp
  have hinf : u3T P x J ⊓ ((P : Subgroup G) ⊓ u3K0 p x J) = ⊥ := by
    rw [eq_bot_iff, ← u3_T_inf_K0_gen3 hc]
    exact inf_le_inf_left _ inf_le_right
  have hTconj : ∀ a ∈ (P : Subgroup G), ∀ t ∈ u3T P x J, a * t * a⁻¹ ∈ u3T P x J := by
    intro a ha t ht
    have ht' : (t ∈ (P : Subgroup G) ∧ t ∈ Subgroup.centralizer ({x} : Set G)) ∧ t ∈ J := ht
    have h1 : a * t * a⁻¹ ∈ (P : Subgroup G) := mul_mem (mul_mem ha ht'.1.1) (inv_mem ha)
    have h2 : a * t * a⁻¹ ∈ Subgroup.centralizer ({x} : Set G) :=
      mul_mem (mul_mem (hP ha) ht'.1.2) (inv_mem (hP ha))
    have h3 : a * t * a⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (hPN ha) t).mp ht'.2
    exact ⟨⟨h1, h2⟩, h3⟩
  have hcomm : ∀ t ∈ u3T P x J, ∀ d ∈ (P : Subgroup G) ⊓ u3K0 p x J, t * d = d * t := by
    intro t ht d hd
    obtain ⟨hdP, -, -, hdO⟩ := hd
    have h1 : d * t * d⁻¹ * t⁻¹ ∈ rankThreePrimeCore p J := hdO t ht.2
    have h2 : d * t * d⁻¹ * t⁻¹ ∈ u3T P x J := mul_mem (hTconj d hdP t ht) (inv_mem ht)
    have h3 : d * t * d⁻¹ * t⁻¹ ∈ (P : Subgroup G) ⊓ rankThreePrimeCore p J := ⟨hTP h2, h1⟩
    rw [hPO, Subgroup.mem_bot] at h3
    have h4 : d * t = t * d := by
      calc d * t = d * t * d⁻¹ * t⁻¹ * (t * d) := by group
        _ = t * d := by rw [h3, one_mul]
    exact h4.symm
  have hDP : (P : Subgroup G) ⊓ u3K0 p x J ≤ (P : Subgroup G) := inf_le_left
  have hDcyc : IsCyclic ↥((P : Subgroup G) ⊓ u3K0 p x J) := by
    obtain ⟨Z, hZc, -, hZS, hZT, -, hTZS⟩ := hSdec
    have hS : u3S P x = (P : Subgroup G) := inf_eq_left.mpr hP
    rw [hS] at hZS hTZS
    haveI := hZc
    let T₀ : Subgroup (P : Subgroup G) := (u3T P x J).subgroupOf (P : Subgroup G)
    haveI hT₀n : T₀.Normal := ⟨fun n hn g => hTconj g g.2 n hn⟩
    let q : (P : Subgroup G) →* (P : Subgroup G) ⧸ T₀ := QuotientGroup.mk' T₀
    let g : Z →* (P : Subgroup G) ⧸ T₀ := q.comp (Subgroup.inclusion hZS)
    have hg : Function.Surjective g := by
      intro y
      obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective y
      have hs : (s : G) ∈ u3T P x J ⊔ Z := by rw [hTZS]; exact s.2
      obtain ⟨t, ht, z, hz, hsz⟩ :=
        dec_mem_sup_of_commute (fun a ha b hb => (hZT b hb a ha).symm) hs
      refine ⟨⟨z, hz⟩, ?_⟩
      have hts : (⟨t, hTP ht⟩ : (P : Subgroup G)) ∈ T₀ := ht
      have hsz' : s = ⟨t, hTP ht⟩ * ⟨z, hZS hz⟩ := Subtype.ext hsz
      show (QuotientGroup.mk (⟨z, hZS hz⟩ : (P : Subgroup G)) : (P : Subgroup G) ⧸ T₀) =
        QuotientGroup.mk s
      rw [hsz', QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (N := T₀) _).mpr hts, one_mul]
    haveI : IsCyclic ((P : Subgroup G) ⧸ T₀) := isCyclic_of_surjective g hg
    let f : ↥((P : Subgroup G) ⊓ u3K0 p x J) →* (P : Subgroup G) ⧸ T₀ :=
      q.comp (Subgroup.inclusion hDP)
    have hf : Function.Injective f := by
      rw [injective_iff_map_eq_one]
      intro d hd
      have hd' : (QuotientGroup.mk (Subgroup.inclusion hDP d) : (P : Subgroup G) ⧸ T₀) = 1 := hd
      have hdT0 : Subgroup.inclusion hDP d ∈ T₀ := (QuotientGroup.eq_one_iff (N := T₀) _).mp hd'
      have hdT : (d : G) ∈ u3T P x J := hdT0
      have : (d : G) ∈ u3T P x J ⊓ ((P : Subgroup G) ⊓ u3K0 p x J) := ⟨hdT, d.2⟩
      rw [hinf, Subgroup.mem_bot] at this
      exact Subtype.ext this
    exact isCyclic_of_injective f hf
  have hxD : x ∈ (P : Subgroup G) ⊓ u3K0 p x J := ⟨hc.generic.1, x_mem_u3K0_gen3 hc⟩
  have hsup : u3T P x J ⊔ ((P : Subgroup G) ⊓ u3K0 p x J) = (P : Subgroup G) :=
    le_antisymm (sup_le hTP hDP) hdec
  have hord : orderOf x = p := orderOf_eq_prime hc.generic.2.1.2.2.1 hc.generic.2.1.2.1
  exact ⟨hTP, hDP, hsup, hinf, hcomm, hDcyc, hxD, hord⟩

theorem u3_pdata_gen3 {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop} (hc : PointConfig3 Typ G p P M x J)
    (hP : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G)) (hTstr : TypeTStruct p P x J)
    (hSdec : TypeSDecomp p P x J) (hAut : TypeAutPCard Typ p) :
    PGroupData p (P : Subgroup G) (u3T P x J) ((P : Subgroup G) ⊓ u3K0 p x J) x := by
  obtain ⟨hTcard, hTexp, hTnab, -⟩ := id hTstr
  obtain ⟨hTP, hDP, hsup, hinf, hcomm, hDcyc, hxD, hord⟩ :=
    u3_pdata_common3 hc hP hSdec (u3_P_decomp_gen3 hc hP hTstr hAut)
  exact ⟨hTP, hDP, hsup, hinf, hcomm, hTcard, hTexp, hTnab, hDcyc, hxD, hord⟩

private theorem burnside_normalizer_le_centralizer {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    (hp : p.Prime) (Q : Sylow p Y) (hQc : IsCyclic (Q : Subgroup Y)) {x : Y}
    (hxQ : x ∈ (Q : Subgroup Y)) (hxo : orderOf x = p) (hxc : ∀ y : Y, y * x = x * y) :
    Subgroup.normalizer ((Q : Subgroup Y) : Set Y) ≤ Subgroup.centralizer
      ((Q : Subgroup Y) : Set Y) := by
  haveI := hQc
  haveI : Fact p.Prime := ⟨hp⟩
  intro g hg
  set Qs : Subgroup Y := (Q : Subgroup Y) with hQs
  set φ : Subgroup.normalizer (Qs : Set Y) →* MulAut Qs := Qs.normalizerMonoidHom with hφ
  set s : ℕ := φ.ker.index with hs
  have hQN : Qs ≤ Subgroup.normalizer (Qs : Set Y) := Subgroup.le_normalizer
  have hle : Qs.subgroupOf (Subgroup.normalizer (Qs : Set Y)) ≤ φ.ker := by
    intro n hn
    rw [hφ, Subgroup.normalizerMonoidHom_ker]
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact Subgroup.le_centralizer Qs hn
  have hcop : Nat.Coprime p s := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    apply Q.not_dvd_index
    refine hdvd.trans ?_
    refine (Subgroup.index_dvd_of_le hle).trans ?_
    exact Subgroup.relIndex_dvd_index_of_le hQN
  have hgD : ∀ d ∈ Qs, g * d * g⁻¹ ∈ Qs := fun d hd => ((Subgroup.mem_normalizer_iff.mp hg) d).mp hd
  have hgx : g * x * g⁻¹ = x := by rw [hxc g, mul_assoc, mul_inv_cancel, mul_one]
  have hDp : ∀ d ∈ Qs, ∃ k : ℕ, d ^ (p ^ k) = 1 := by
    intro d hd
    obtain ⟨k, hk⟩ := Q.isPGroup' ⟨d, hd⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hgs : ∀ d ∈ Qs, (g ^ s) * d * (g ^ s)⁻¹ = d := by
    intro d hd
    have h1 : (⟨g, hg⟩ : Subgroup.normalizer (Qs : Set Y)) ^ s ∈ φ.ker := Subgroup.pow_index_mem _ _
    rw [hφ, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_iff] at h1
    have h2 := h1 d hd
    simp only [Subgroup.coe_pow] at h2
    rw [mul_inv_eq_iff_eq_mul]
    exact h2.symm
  have key := cyclic_coprime_aut_trivial hp (D := Qs) hDp hxQ hxo hgD hgx hcop hgs
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have := key d hd
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this.symm

private theorem burnside_exists_complement {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    (hp : p.Prime) (Q : Sylow p Y)
    (hQ : Subgroup.normalizer ((Q : Subgroup Y) : Set Y) ≤
      Subgroup.centralizer ((Q : Subgroup Y) : Set Y)) :
    ∃ N : Subgroup Y, (∀ n ∈ N, Nat.Coprime p (orderOf n)) ∧
      (∀ y : Y, Nat.Coprime p (orderOf y) → y ∈ N) ∧
      (∀ y : Y, ∃ n ∈ N, ∃ d ∈ (Q : Subgroup Y), y = n * d) := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine ⟨(MonoidHom.transferSylow Q hQ).ker, ?_, ?_, ?_⟩
  · intro n hn
    have h1 : orderOf n ∣ Nat.card (MonoidHom.transferSylow Q hQ).ker := by
      have := orderOf_dvd_natCard (⟨n, hn⟩ : (MonoidHom.transferSylow Q hQ).ker)
      simpa using this
    exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr
      (MonoidHom.not_dvd_card_ker_transferSylow Q hQ)).coprime_dvd_right h1
  · intro y hy
    rw [MonoidHom.mem_ker]
    obtain ⟨k, hk⟩ := Q.isPGroup' (MonoidHom.transferSylow Q hQ y)
    have h2 : orderOf (MonoidHom.transferSylow Q hQ y) ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
    have h3 : orderOf (MonoidHom.transferSylow Q hQ y) ∣ orderOf y := orderOf_map_dvd _ y
    have h4 : Nat.Coprime (p ^ k) (orderOf y) := Nat.Coprime.pow_left k hy
    have h5 : orderOf (MonoidHom.transferSylow Q hQ y) = 1 := Nat.eq_one_of_dvd_coprimes h4 h2 h3
    exact orderOf_eq_one_iff.mp h5
  · intro y
    have hcomp := MonoidHom.ker_transferSylow_isComplement' Q hQ
    obtain ⟨⟨a, d⟩, h, -⟩ := hcomp.existsUnique y
    exact ⟨a.1, a.2, d.1, d.2, h.symm⟩

theorem u3_K0_pComplement_core3 {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}
    (hc : PointConfig3 Typ G p P M x J)
    (hP : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G))
    (hDcyc : IsCyclic ↥((P : Subgroup G) ⊓ u3K0 p x J)) (hxD : x ∈ (P : Subgroup G) ⊓ u3K0 p x J)
    (hxo' : orderOf x = p) :
    ∃ N₀ : Subgroup G, N₀ ≤ u3K0 p x J ∧
      (∀ c ∈ Subgroup.centralizer ({x} : Set G), ∀ n ∈ N₀, c * n * c⁻¹ ∈ N₀) ∧
      (∀ n ∈ N₀, Nat.Coprime p (orderOf n)) ∧
      ∀ k ∈ u3K0 p x J, ∃ n ∈ N₀, ∃ d ∈ (P : Subgroup G) ⊓ u3K0 p x J, k = n * d := by
  have hp : p.Prime := hc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hnorm := u3K0_conj_gen3 hc
  have hK₀C : u3K0 p x J ≤ Subgroup.centralizer ({x} : Set G) := fun k hk => hk.1
  have hK₀N : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer
    ((u3K0 p x J : Subgroup G) : Set G) := by
    intro c hcC
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · exact fun hk => hnorm c hcC k hk
    · intro hk
      have := hnorm c⁻¹ ((Subgroup.centralizer ({x} : Set G)).inv_mem hcC) _ hk
      simpa [mul_assoc] using this
  have hsyl : CFSG.ABGLocalTools.IsSylowOf p ((P : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G))
      (Subgroup.centralizer ({x} : Set G)) := hc.generic.2.2.1
  have hsyl' : CFSG.ABGLocalTools.IsSylowOf p ((P : Subgroup G) ⊓ u3K0 p x J) (u3K0 p x J) := by
    have := hsyl.inf_of_le_normalizer hK₀C hK₀N
    rwa [inf_assoc, inf_eq_right.mpr hK₀C] at this
  obtain ⟨Q, hQ⟩ := hsyl'.exists_sylow_eq_subgroupOf
  have hxK : x ∈ u3K0 p x J := hxD.2
  have hQc : IsCyclic (Q : Subgroup (u3K0 p x J)) := by
    have hcyc := hDcyc
    rw [hQ]
    exact (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : (P : Subgroup G) ⊓ u3K0 p x J ≤ u3K0 p x J))).mpr hcyc
  have hxQ : (⟨x, hxK⟩ : u3K0 p x J) ∈ (Q : Subgroup (u3K0 p x J)) := by
    rw [hQ, Subgroup.mem_subgroupOf]
    exact hxD
  have hxo : orderOf (⟨x, hxK⟩ : u3K0 p x J) = p := by
    rw [Subgroup.orderOf_mk]
    exact hxo'
  have hxc : ∀ y : u3K0 p x J, y * ⟨x, hxK⟩ = ⟨x, hxK⟩ * y := by
    intro y
    apply Subtype.ext
    exact (y.2.1 x (Set.mem_singleton x)).symm
  have hQN := burnside_normalizer_le_centralizer hp Q hQc hxQ hxo hxc
  obtain ⟨N, hN1, hN2, hN3⟩ := burnside_exists_complement hp Q hQN
  refine ⟨N.map (u3K0 p x J).subtype, Subgroup.map_subtype_le N, ?_, ?_, ?_⟩
  · intro c hcC n hn
    obtain ⟨n', hn', rfl⟩ := hn
    have hmem : c * (n' : G) * c⁻¹ ∈ u3K0 p x J := hnorm c hcC n' n'.2
    have hm : (⟨c * (n' : G) * c⁻¹, hmem⟩ : u3K0 p x J) ∈ N := by
      apply hN2
      rw [Subgroup.orderOf_mk]
      have h1 : orderOf (c * (n' : G) * c⁻¹) = orderOf (n' : G) := by
        have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective (n' : G)
        simpa using this
      rw [h1, Subgroup.orderOf_coe]
      exact hN1 n' hn'
    exact ⟨_, hm, rfl⟩
  · rintro n ⟨n', hn', rfl⟩
    have := hN1 n' hn'
    rwa [← Subgroup.orderOf_coe] at this
  · intro k hk
    obtain ⟨n', hn', d', hd', hkd⟩ := hN3 ⟨k, hk⟩
    rw [hQ, Subgroup.mem_subgroupOf] at hd'
    exact ⟨n', ⟨n', hn', rfl⟩, d', hd', congrArg Subtype.val hkd⟩

open CFSG.ABGLocalTools in
private theorem torA_frattini_ker {Γ Q : Type*} [Group Γ] [Finite Γ] [Group Q] {p : ℕ}
    [Fact p.Prime]
    (ψ : Γ →* Q) (hcop : Nat.Coprime p (Nat.card ψ.ker)) {T : Subgroup Γ} (hT : IsPGroup p T)
    {j : Γ} (hj : ψ j ∈ Subgroup.normalizer ((T.map ψ : Subgroup Q) : Set Q)) :
    ∃ n ∈ Subgroup.normalizer (T : Set Γ), ψ n = ψ j := by
  classical
  set K := ψ.ker with hK
  set H : Subgroup Γ := K ⊔ T with hH
  have hTH : IsSylowOf p T H := by
    rw [isSylowOf_iff]
    refine ⟨le_sup_right, hT, ?_⟩
    rw [hH, relIndex_sup_eq_relIndex_of_normal K T]
    intro hdvd
    exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).mp hcop)
      (hdvd.trans (Subgroup.index_dvd_card (T.subgroupOf K)))
  set Tj : Subgroup Γ := T.map (MulAut.conj j).toMonoidHom with hTj
  have hmemTj : ∀ y, y ∈ Tj ↔ j⁻¹ * y * j ∈ T := by
    intro y
    rw [hTj, Subgroup.mem_map_equiv]
    simp [MulAut.conj_symm_apply]
  have hTjH : Tj ≤ H := by
    intro y hy
    rw [hmemTj] at hy
    have h1 : ψ y ∈ T.map ψ := by
      have h2 := (Subgroup.mem_normalizer_iff.mp hj (ψ (j⁻¹ * y * j))).mp
        (Subgroup.mem_map_of_mem ψ hy)
      have e : ψ j * ψ (j⁻¹ * y * j) * (ψ j)⁻¹ = ψ y := by
        rw [← map_inv, ← map_mul, ← map_mul]
        congr 1
        group
      rwa [e] at h2
    obtain ⟨t', ht', hψ⟩ := h1
    have hk : y * t'⁻¹ ∈ K := by
      rw [hK, MonoidHom.mem_ker, map_mul, map_inv, ← hψ, mul_inv_cancel]
    have : y = (y * t'⁻¹) * t' := by group
    rw [this]
    exact Subgroup.mul_mem_sup hk ht'
  have hcardTj : Nat.card Tj = Nat.card T :=
    Subgroup.card_map_of_injective (MulAut.conj j).injective
  have hTjS : IsSylowOf p Tj H := isSylowOf_of_card hTjH (by rw [hcardTj]; exact hTH.card_eq)
  obtain ⟨x, hxH, hx⟩ := CFSG.ClassicalInvolution.GlaubermanAut.isSylowOf_exists_conj hTH hTjS
  obtain ⟨k, hk, t, htT, hkt⟩ := Subgroup.mem_sup_of_normal_left.mp hxH
  subst hkt
  refine ⟨k⁻¹ * j, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 : y ∈ T ↔ j * y * j⁻¹ ∈ Tj := by
      rw [hmemTj]
      have : j⁻¹ * (j * y * j⁻¹) * j = y := by group
      rw [this]
    have h2 : (j * y * j⁻¹ ∈ Tj) ↔ (k * t)⁻¹ * (j * y * j⁻¹) * (k * t) ∈ T := hx _
    have h3 : (k * t)⁻¹ * (j * y * j⁻¹) * (k * t) =
        t⁻¹ * ((k⁻¹ * j) * y * (k⁻¹ * j)⁻¹) * t := by group
    have h4 : t⁻¹ * ((k⁻¹ * j) * y * (k⁻¹ * j)⁻¹) * t ∈ T ↔
        (k⁻¹ * j) * y * (k⁻¹ * j)⁻¹ ∈ T := by
      constructor
      · intro h
        have := T.mul_mem (T.mul_mem htT h) (T.inv_mem htT)
        simpa [mul_assoc] using this
      · intro h
        exact T.mul_mem (T.mul_mem (T.inv_mem htT) h) htT
    rw [h1, h2, h3, h4]
  · rw [map_mul, map_inv, MonoidHom.mem_ker.mp hk, inv_one, one_mul]

omit [Finite G] in
private theorem torA_T_le_J (P : Sylow p G) (x : G) (J : Subgroup G) : u3T P x J ≤ J := inf_le_right

omit [Finite G] in
private theorem torA_T_le_P (P : Sylow p G) (x : G) (J : Subgroup G) : u3T P x J ≤
    (P : Subgroup G) :=
  inf_le_left.trans inf_le_left

private theorem torA_isPGroup_T (P : Sylow p G) (x : G) (J : Subgroup G) :
    IsPGroup p ((u3T P x J).subgroupOf J) :=
  (P.isPGroup'.to_le (torA_T_le_P P x J)).comap_subtype

private theorem torA_ker_coprime (p : ℕ) (J : Subgroup G) {Q : Type} [Group Q] (ψ : ↥J →* Q)
    (hker : ψ.ker = (rankThreePrimeCore p J).subgroupOf J) : Nat.Coprime p (Nat.card ψ.ker) := by
  have hle : rankThreePrimeCore p J ≤ J := CFSG.AGLEmbedding.glbPrimeCore_le p J
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
  exact CFSG.AGLEmbedding.glbPrimeCore_coprime p J

theorem u3_normalizer_onto_gen3 {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}
    (hc : PointConfig3 Typ G p P M x J) :
    ∃ (Q : Type) (_ : Group Q) (ψ : ↥J →* Q), Function.Surjective ψ ∧
      ψ.ker = (rankThreePrimeCore p J).subgroupOf J ∧ Typ p Q ∧
      ∀ q ∈ Subgroup.normalizer (((u3T P x J).subgroupOf J).map ψ : Set Q),
        ∃ n ∈ Subgroup.normalizer ((u3T P x J : Subgroup G) : Set G) ⊓ J, ∃ hn : n ∈ J,
          ψ ⟨n, hn⟩ = q := by
  haveI : Fact p.Prime := ⟨hc.prime⟩
  obtain ⟨Q, iQ, ψ, hsurj, hker, hU3⟩ := hc.typ
  refine ⟨Q, iQ, ψ, hsurj, hker, hU3, ?_⟩
  intro q hq
  obtain ⟨j, rfl⟩ := hsurj q
  obtain ⟨n, hn, hψ⟩ := torA_frattini_ker ψ (torA_ker_coprime p J ψ hker) (torA_isPGroup_T P x J) hq
  refine ⟨(n : G), Subgroup.mem_inf.mpr ⟨?_, n.2⟩, n.2, ?_⟩
  · have := u3main_mem_normalizer_map hn
    rwa [Subgroup.map_subgroupOf_eq_of_le (torA_T_le_J P x J)] at this
  · simpa using hψ

private noncomputable def torA_ext {Q : Type} [Group Q] (J : Subgroup G) (ψ : ↥J →* Q)
    (g : G) : Q :=
  open Classical in if h : g ∈ J then ψ ⟨g, h⟩ else 1

private theorem torA_ext_of_mem {Q : Type} [Group Q] (J : Subgroup G) (ψ : ↥J →* Q) {g : G}
    (hg : g ∈ J) : torA_ext J ψ g = ψ ⟨g, hg⟩ := by
  unfold torA_ext
  rw [dif_pos hg]

private theorem torA_ext_mul {Q : Type} [Group Q] (J : Subgroup G) (ψ : ↥J →* Q) {a b : G}
    (ha : a ∈ J) (hb : b ∈ J) : torA_ext J ψ (a * b) = torA_ext J ψ a * torA_ext J ψ b := by
  rw [torA_ext_of_mem J ψ ha, torA_ext_of_mem J ψ hb, torA_ext_of_mem J ψ (J.mul_mem ha hb)]
  exact map_mul ψ ⟨a, ha⟩ ⟨b, hb⟩

private theorem torA_ext_inv {Q : Type} [Group Q] (J : Subgroup G) (ψ : ↥J →* Q) {a : G}
    (ha : a ∈ J) : torA_ext J ψ a⁻¹ = (torA_ext J ψ a)⁻¹ := by
  rw [torA_ext_of_mem J ψ ha, torA_ext_of_mem J ψ (J.inv_mem ha)]
  exact map_inv ψ ⟨a, ha⟩

private theorem torA_ext_one {Q : Type} [Group Q] (J : Subgroup G) (ψ : ↥J →* Q) :
    torA_ext J ψ 1 = 1 := by
  rw [torA_ext_of_mem J ψ J.one_mem]
  exact map_one ψ

private theorem torA_ext_pow {Q : Type} [Group Q] (J : Subgroup G) (ψ : ↥J →* Q) {a : G}
    (ha : a ∈ J) (k : ℕ) : torA_ext J ψ (a ^ k) = (torA_ext J ψ a) ^ k := by
  rw [torA_ext_of_mem J ψ ha, torA_ext_of_mem J ψ (J.pow_mem ha k)]
  exact map_pow ψ ⟨a, ha⟩ k

theorem u3_torusProps_NJ_gen3 {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}
    (hc : PointConfig3 Typ G p P M x J) (hIrr : TypeTorusIrred Typ p) (hFpf : TypeTorusFpf Typ p)
    (hOn : TypeTorusOnCenter Typ p) :
    TorusProps p (u3T P x J) (Subgroup.normalizer ((u3T P x J : Subgroup G) : Set G) ⊓ J) := by
  haveI : Fact p.Prime := ⟨hc.prime⟩
  obtain ⟨Q, iQ, ψ, hsurj, hker, hU3, hnorm⟩ := u3_normalizer_onto_gen3 hc
  haveI : Finite Q := Finite.of_surjective ψ hsurj
  have hTJ : u3T P x J ≤ J := torA_T_le_J P x J
  have hcop : Nat.Coprime p (Nat.card ψ.ker) := torA_ker_coprime p J ψ hker
  have hsyl : CFSG.ABGLocalTools.IsSylowOf p (u3T P x J) J :=
    hc.generic.2.2.1.inf_of_le_normalizer hc.le_cent hc.cent_le
  obtain ⟨S, hS⟩ := hsyl.exists_sylow_eq_subgroupOf
  set TS : Sylow p Q := S.mapSurjective hsurj with hTSdef
  set T : Subgroup G := u3T P x J with hT
  set F : Subgroup G := Subgroup.normalizer (T : Set G) ⊓ J with hF
  set Tb : Subgroup Q := (T.subgroupOf J).map ψ with hTb
  have hTS : (TS : Subgroup Q) = Tb := by
    show (S : Subgroup ↥J).map ψ = _
    rw [hS]
  obtain ⟨e, he_of_mem, he_mul, he_inv, he_one, he_pow⟩ : ∃ e : G → Q,
      (∀ g (hg : g ∈ J), e g = ψ ⟨g, hg⟩) ∧ (∀ {a b : G}, a ∈ J → b ∈ J → e (a * b) = e a * e b) ∧
      (∀ {a : G}, a ∈ J → e a⁻¹ = (e a)⁻¹) ∧ e 1 = 1 ∧
      (∀ {a : G}, a ∈ J → ∀ k : ℕ, e (a ^ k) = e a ^ k) :=
    ⟨torA_ext J ψ, fun g hg => torA_ext_of_mem J ψ hg, fun ha hb => torA_ext_mul J ψ ha hb,
      fun ha => torA_ext_inv J ψ ha, torA_ext_one J ψ, fun ha k => torA_ext_pow J ψ ha k⟩
  have he_mk : ∀ j : ↥J, e (j : G) = ψ j := fun j => he_of_mem _ j.2
  have hinj0 : ∀ t ∈ T.subgroupOf J, ψ t = 1 → t = 1 :=
    u3main_eq_one_of_ker ψ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mp hcop)
      (torA_isPGroup_T P x J)
  have hinj : ∀ a ∈ T, ∀ b ∈ T, e a = e b → a = b := by
    intro a ha b hb hab
    have haJ := hTJ ha
    have hbJ := hTJ hb
    have h1 : (⟨a, haJ⟩ * ⟨b, hbJ⟩⁻¹ : ↥J) ∈ T.subgroupOf J := by
      rw [Subgroup.mem_subgroupOf]
      exact T.mul_mem ha (T.inv_mem hb)
    have h2 : ψ (⟨a, haJ⟩ * ⟨b, hbJ⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, ← he_of_mem _ haJ, ← he_of_mem _ hbJ]
      rw [hab, mul_inv_cancel]
    have h3 := hinj0 _ h1 h2
    have : (⟨a, haJ⟩ : ↥J) = ⟨b, hbJ⟩ := mul_inv_eq_one.mp h3
    exact congrArg Subtype.val this
  have hmemTb : ∀ q, q ∈ Tb ↔ ∃ t ∈ T, e t = q := by
    intro q
    rw [hTb, Subgroup.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨(a : G), ha, he_mk a⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, hTJ ht⟩, ht, (he_of_mem _ (hTJ ht)).symm⟩
  have hC : ∀ t ∈ T, (e t ∈ Subgroup.centralizer (Tb : Set Q) ↔
      t ∈ Subgroup.centralizer (T : Set G)) := by
    intro t ht
    have htJ := hTJ ht
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro h t' ht'
      have h1 := h (e t') ((hmemTb _).mpr ⟨t', ht', rfl⟩)
      rw [← he_mul (hTJ ht') htJ, ← he_mul htJ (hTJ ht')] at h1
      exact hinj _ (T.mul_mem ht' ht) _ (T.mul_mem ht ht') h1
    · intro h q hq
      obtain ⟨t', ht', rfl⟩ := (hmemTb q).mp hq
      rw [← he_mul (hTJ ht') htJ, ← he_mul htJ (hTJ ht'), h t' ht']
  have hnorm' : ∀ q ∈ Subgroup.normalizer (Tb : Set Q), ∃ n ∈ F, e n = q := by
    intro q hq
    obtain ⟨n, hnF, hnJ, hψ⟩ := hnorm q hq
    exact ⟨n, hnF, by rw [he_of_mem _ hnJ, hψ]⟩
  have hconj : ∀ m ∈ F, ∀ t ∈ J, e (m * t * m⁻¹) = e m * e t * (e m)⁻¹ := by
    intro m hm t ht
    have hmJ := (Subgroup.mem_inf.mp hm).2
    rw [he_mul (J.mul_mem hmJ ht) (J.inv_mem hmJ), he_mul hmJ ht,
      he_inv hmJ]
  have hirr : ∀ {A : Subgroup Q}, A ≤ Tb → Tb ⊓ Subgroup.centralizer (Tb : Set Q) ≤ A →
      (∀ n ∈ Subgroup.normalizer (Tb : Set Q), ∀ a ∈ A, n * a * n⁻¹ ∈ A) →
      A = Tb ⊓ Subgroup.centralizer (Tb : Set Q) ∨ A = Tb := by
    intro A h1 h2 h3
    have := hIrr Q hU3 TS A (by rw [hTS]; exact h1)
      (by rw [hTS]; exact h2) (by rw [hTS]; exact h3)
    rwa [hTS] at this
  have hfpf : ∀ {t : Q}, t ∈ Tb → (∀ n ∈ Subgroup.normalizer (Tb : Set Q),
      n * t * n⁻¹ * t⁻¹ ∈ Tb ⊓ Subgroup.centralizer (Tb : Set Q)) →
      t ∈ Tb ⊓ Subgroup.centralizer (Tb : Set Q) := by
    intro t ht h
    have := hFpf Q hU3 TS t (by rw [hTS]; exact ht) (by rw [hTS]; exact h)
    rwa [hTS] at this
  have hon : ∀ {c : Q}, c ∈ Tb → c ∈ Subgroup.centralizer (Tb : Set Q) → c ≠ 1 →
      ∀ k : ℤ, ¬ (p : ℤ) ∣ k → ∃ n ∈ Subgroup.normalizer (Tb : Set Q), n * c * n⁻¹ = c ^ k := by
    intro c hcT hcZ hc1 k hk
    have := hOn Q hU3 TS c (by rw [hTS]; exact hcT)
      (by rw [hTS]; exact hcZ) hc1 k hk
    rwa [hTS] at this
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f hf t ht
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp hf).1 t).mp ht
  · intro A hAT hZA hinv
    have hAJ : A ≤ J := hAT.trans hTJ
    set Ab : Subgroup Q := (A.subgroupOf J).map ψ with hAb
    have hmemAb : ∀ q, q ∈ Ab ↔ ∃ a ∈ A, e a = q := by
      intro q
      rw [hAb, Subgroup.mem_map]
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨(a : G), ha, he_mk a⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨⟨t, hAJ ht⟩, ht, (he_of_mem _ (hAJ ht)).symm⟩
    have h1 : Ab ≤ Tb := by
      intro q hq
      obtain ⟨a, ha, rfl⟩ := (hmemAb q).mp hq
      exact (hmemTb _).mpr ⟨a, hAT ha, rfl⟩
    have h2 : Tb ⊓ Subgroup.centralizer (Tb : Set Q) ≤ Ab := by
      intro q hq
      obtain ⟨hqT, hqC⟩ := Subgroup.mem_inf.mp hq
      obtain ⟨t, ht, rfl⟩ := (hmemTb q).mp hqT
      have : t ∈ zOf T := Subgroup.mem_inf.mpr ⟨ht, (hC t ht).mp hqC⟩
      exact (hmemAb _).mpr ⟨t, hZA this, rfl⟩
    have h3 : ∀ n ∈ Subgroup.normalizer (Tb : Set Q), ∀ a ∈ Ab, n * a * n⁻¹ ∈ Ab := by
      intro n hn a ha
      obtain ⟨m, hmF, rfl⟩ := hnorm' n hn
      obtain ⟨a₀, ha₀, rfl⟩ := (hmemAb a).mp ha
      refine (hmemAb _).mpr ⟨m * a₀ * m⁻¹, hinv m hmF a₀ ha₀, ?_⟩
      exact hconj m hmF a₀ (hAJ ha₀)
    rcases hirr h1 h2 h3 with h | h
    · left
      refine le_antisymm (fun a ha => ?_) hZA
      have haT := hAT ha
      have h4 : e a ∈ Ab := (hmemAb _).mpr ⟨a, ha, rfl⟩
      rw [h] at h4
      exact Subgroup.mem_inf.mpr ⟨haT, (hC a haT).mp (Subgroup.mem_inf.mp h4).2⟩
    · right
      refine le_antisymm hAT (fun t ht => ?_)
      have h4 : e t ∈ Tb := (hmemTb _).mpr ⟨t, ht, rfl⟩
      rw [← h] at h4
      obtain ⟨a, ha, hat⟩ := (hmemAb _).mp h4
      have h5 := hinj a (hAT ha) t ht hat
      exact h5 ▸ ha
  · intro t ht h
    have htb : e t ∈ Tb := (hmemTb _).mpr ⟨t, ht, rfl⟩
    have hz : ∀ z ∈ zOf T, e z ∈ Tb ⊓ Subgroup.centralizer (Tb : Set Q) := by
      intro z hz
      obtain ⟨hzT, hzC⟩ := Subgroup.mem_inf.mp hz
      exact Subgroup.mem_inf.mpr ⟨(hmemTb _).mpr ⟨z, hzT, rfl⟩, (hC z hzT).mpr hzC⟩
    have h6 := hfpf htb (by
      intro n hn
      obtain ⟨m, hmF, rfl⟩ := hnorm' n hn
      have h1 := hz _ (h m hmF)
      have hmJ := (Subgroup.mem_inf.mp hmF).2
      have htJ := hTJ ht
      rw [he_mul (J.mul_mem (J.mul_mem hmJ htJ) (J.inv_mem hmJ)) (J.inv_mem htJ),
        hconj m hmF t htJ, he_inv htJ] at h1
      exact h1)
    exact Subgroup.mem_inf.mpr ⟨ht, (hC t ht).mp (Subgroup.mem_inf.mp h6).2⟩
  · intro z hz k hk
    obtain ⟨hzT, hzC⟩ := Subgroup.mem_inf.mp hz
    by_cases hz1 : z = 1
    · subst hz1
      exact ⟨1, F.one_mem, by simp⟩
    · have hzJ := hTJ hzT
      have hez1 : e z ≠ 1 := by
        intro h1
        apply hz1
        exact hinj z hzT 1 T.one_mem (by rw [h1, he_one])
      have hezT : e z ∈ Tb := (hmemTb _).mpr ⟨z, hzT, rfl⟩
      have hezC : e z ∈ Subgroup.centralizer (Tb : Set Q) := (hC z hzT).mpr hzC
      obtain ⟨n, hn, hnz⟩ := hon hezT hezC hez1 (k : ℤ) (by exact_mod_cast hk)
      obtain ⟨m, hmF, rfl⟩ := hnorm' n hn
      refine ⟨m, hmF, ?_⟩
      have hmz : m * z * m⁻¹ ∈ T :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp hmF).1 z).mp hzT
      apply hinj _ hmz _ (T.pow_mem hzT k)
      rw [hconj m hmF z hzJ, hnz, he_pow hzJ, zpow_natCast]

end CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3U3RemarkAux
