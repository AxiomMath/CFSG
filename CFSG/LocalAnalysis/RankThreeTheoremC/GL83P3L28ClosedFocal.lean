module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28ClosedAct
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28ClosedNorm
import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantConjugacy

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28Cl

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open scoped Pointwise

theorem hom_eq_one_of_perfect {G A : Type*} [Group G] [CommGroup A] (hG : commutator G = ⊤)
    (f : G →* A) (g : G) : f g = 1 := by
  have h : commutator G ≤ f.ker := by
    rw [commutator_def]
    refine Subgroup.commutator_le.mpr fun g₁ _ g₂ _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  rw [hG] at h
  exact h (Subgroup.mem_top g)

theorem commutator_le_ker {G A : Type*} [Group G] [CommGroup A] (f : G →* A) :
    ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ f.ker := by
  refine Subgroup.commutator_le.mpr fun g₁ _ g₂ _ => ?_
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm _ _

variable {Y : Type} [Group Y] [Finite Y] {P : Subgroup Y} {x k : Y} {K₁ K₂ Q : Subgroup Y}
  {a b t : Y}

theorem map_conj_one (K : Subgroup Y) : K.map (MulAut.conj (1 : Y)).toMonoidHom = K := by
  have : (MulAut.conj (1 : Y)).toMonoidHom = MonoidHom.id Y := by
    ext z
    simp
  rw [this, Subgroup.map_id]

namespace SwapData

variable (sd : SwapData P K₁ K₂ Q a b t)

include sd

theorem rank_le_one : CFSG.Open.pRank 3 K₁ ≤ 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hEK, hE, hEc⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained 3
    Nat.prime_three K₁
  have hEp : IsPGroup 3 E := elementary_isPGroup 3 E hE
  obtain ⟨g, -, hg⟩ := GL83P3L28Aux.exists_mem_conj_le_sylow sd.two.sylow_inf hEK hEp
  have hcyc : ∀ y ∈ zpowers a, y ^ 3 = 1 → y ∈ zpowers (a ^ 3) := by
    intro y hy hy3
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
    have h1 : a ^ (i * 3) = 1 := by
      rw [zpow_mul]
      simpa using hy3
    have h2 : ((orderOf a : ℕ) : ℤ) ∣ i * 3 := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rw [sd.q.a_ord] at h2
    obtain ⟨j, hj⟩ : (3 : ℤ) ∣ i := by omega
    refine ⟨j, ?_⟩
    rw [hj]
    group
  have hmem : ∀ y : E, g⁻¹ * (y : Y) * g ∈ zpowers (a ^ 3) := by
    intro y
    have h1 := hg y y.2
    rw [sd.q.S₁_eq] at h1
    refine hcyc _ h1 ?_
    have := hE.2 y y.2
    calc (g⁻¹ * (y : Y) * g) ^ 3 = g⁻¹ * (y : Y) ^ 3 * g := by
          have := conj_pow (a := g⁻¹) (b := (y : Y)) (i := 3)
          simpa using this
      _ = 1 := by rw [this]; group
  have hinj : Function.Injective
      (fun y : E => (⟨g⁻¹ * (y : Y) * g, hmem y⟩ : zpowers (a ^ 3))) := by
    intro y₁ y₂ h
    have h1 : g⁻¹ * (y₁ : Y) * g = g⁻¹ * (y₂ : Y) * g := congrArg Subtype.val h
    exact Subtype.ext (by simpa using h1)
  have hcard : Nat.card (zpowers (a ^ 3)) = 3 := by
    have ho := orderOf_pow' (x := a) (n := 3) (by norm_num)
    rw [Nat.card_zpowers, ho, sd.q.a_ord]
    norm_num
  have h3 : Nat.card E ≤ 3 := hcard ▸ Nat.card_le_card_of_injective _ hinj
  rw [hEc] at h3
  by_contra hlt
  push Not at hlt
  have : 3 ^ 2 ≤ 3 ^ CFSG.Open.pRank 3 K₁ := Nat.pow_le_pow_right (by norm_num) hlt
  omega

end SwapData

theorem P_le_sup_cent (hd : ClosedData P x k) (hs : CompSetting P) {K D : Subgroup Y}
    (hK : IsComponentOf K ⊤) (hN : KFactOutThreeNilpotent) (hrk : CFSG.Open.pRank 3 K ≤ 1)
    (hDN : D ≤ normalizer (K : Set Y)) (hPD : P ≤ D)
    (hcomm : ∀ (p : Y) (hp : p ∈ D), p ∈ P → (⟨p, hp⟩ : D) ∈ commutator D) :
    ∀ p ∈ P, p ∈ K ⊔ centralizer (K : Set Y) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hs1, hnab⟩ := hs.simple hK
  have hcat : IsCatalogGroup K := hd.catalog.simple_subgroup K hs1 hnab
  obtain ⟨R, -, hRnorm, -, hdR, hRK⟩ := hN Y K hs1 hnab hcat hrk
  haveI hR'n : (R.subgroupOf D).Normal := ⟨fun r hr g => by
    rw [mem_subgroupOf] at hr ⊢
    exact hRnorm g (hDN g.2) r hr⟩
  have hB3 : IsPGroup 3 (↥D ⧸ R.subgroupOf D) := by
    intro bq
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective bq
    obtain ⟨n, hn⟩ := hdR d (hDN d.2)
    refine ⟨n, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact mem_subgroupOf.mpr (by simpa using hn)
  have hPsyl : ¬ 3 ∣ (P.subgroupOf D).index :=
    (isSylowOf_iff.mp (hs.sylow.of_le hPD le_top)).2.2
  let ρ : ↥D →* ↥D ⧸ R.subgroupOf D := QuotientGroup.mk' (R.subgroupOf D)
  have hmap : (P.subgroupOf D).map ρ = ⊤ := by
    have hdvd : ((P.subgroupOf D).map ρ).index ∣ (P.subgroupOf D).index :=
      Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _)
    obtain ⟨n, hn⟩ := hB3.index ((P.subgroupOf D).map ρ)
    have hn0 : n = 0 := by
      by_contra hn0
      exact hPsyl ((dvd_pow_self 3 hn0).trans (hn ▸ hdvd))
    rw [hn0, pow_zero] at hn
    exact Subgroup.index_eq_one.mp hn
  have hcommB : commutator (↥D ⧸ R.subgroupOf D) = ⊤ := by
    rw [commutator_def, eq_top_iff]
    have h1 : P.subgroupOf D ≤ commutator ↥D := fun p hp => hcomm p.1 p.2 (mem_subgroupOf.mp hp)
    have h2 := Subgroup.map_mono (f := ρ) h1
    rw [hmap, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective ρ (QuotientGroup.mk'_surjective _)] at h2
    exact h2
  have hBtriv : ∀ bq : ↥D ⧸ R.subgroupOf D, bq = 1 := by
    by_contra hne
    push Not at hne
    obtain ⟨bq, hbq⟩ := hne
    haveI : Nontrivial (↥D ⧸ R.subgroupOf D) := ⟨⟨bq, 1, hbq⟩⟩
    haveI : Group.IsNilpotent (↥D ⧸ R.subgroupOf D) := hB3.isNilpotent
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (↥D ⧸ R.subgroupOf D)).ne hcommB
  intro p hp
  have hpD : p ∈ D := hPD hp
  have hpR : p ∈ R := mem_subgroupOf.mp
    ((QuotientGroup.eq_one_iff (⟨p, hpD⟩ : D)).mp (hBtriv _))
  obtain ⟨n, hn⟩ := hs.sylow.isPGroup ⟨p, hp⟩
  refine hRK p hpR ⟨n, ?_⟩
  rw [show p ^ 3 ^ n = 1 from congrArg Subtype.val hn]
  exact Subgroup.one_mem _


namespace SwapData

variable (sd : SwapData P K₁ K₂ Q a b t)

include sd

theorem false_of_swap (hd : ClosedData P x k) (hN : KFactOutThreeNilpotent) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, huP, huQ, q, hqQ, hutq⟩ := sd.exists_u hd
  set D : Subgroup Y := normalizer (K₁ : Set Y) with hD
  haveI hDn : D.Normal := sd.two.normal_normalizer
  have hPD : P ≤ D := sd.two.hs.normalizes sd.two.c₁
  have hQD : Q ≤ D := sd.q.Q_le.trans hPD
  have hDN₂ : D ≤ normalizer (K₂ : Set Y) := fun g hg =>
    mem_normalizer_iff_map_conj_eq.mpr
      (sd.two.map_conj_of_mem (mem_normalizer_iff_map_conj_eq.mp hg))
  have h2 : K₂.map (MulAut.conj t⁻¹).toMonoidHom = K₁ := by
    rw [← sd.t_swap, ← CFSG.RankThreeEvenClassification.Helpers.subgroup_map_conj_mul,
      inv_mul_cancel]
    exact map_conj_one K₁
  have ht : ∀ y : Y, y ∉ D → t⁻¹ * y ∈ D := by
    intro y hy
    have hy' : K₁.map (MulAut.conj y).toMonoidHom ≠ K₁ := fun h =>
      hy (mem_normalizer_iff_map_conj_eq.mpr h)
    obtain ⟨hy1, -⟩ := sd.two.swap_of_ne hy'
    refine mem_normalizer_iff_map_conj_eq.mpr ?_
    show K₁.map (MulAut.conj (t⁻¹ * y)).toMonoidHom = K₁
    rw [CFSG.RankThreeEvenClassification.Helpers.subgroup_map_conj_mul, hy1, h2]
  obtain ⟨h, hh⟩ := exists_norm_hom D t ht
  have hfoc : ∀ p ∈ P, h p = 1 := fun p hp => (commutator_le_ker h) (hd.focal hp)
  have hK₁D : K₁ ≤ D := Subgroup.le_normalizer
  have hK₂D : K₂ ≤ D := sd.two.symm.le_cent.trans (Subgroup.centralizer_le_normalizer _)
  have hofK : ∀ K : Subgroup Y, IsComponentOf K ⊤ → ∀ hKD : K ≤ D, ∀ (y : Y) (hyK : y ∈ K)
      (hyD : y ∈ D), Abelianization.of (⟨y, hyD⟩ : D) = 1 := by
    intro K hK hKD y hyK hyD
    exact hom_eq_one_of_perfect hK.2.2.1 ((Abelianization.of).comp (Subgroup.inclusion hKD))
      ⟨y, hyK⟩
  have hab : a * b = b * a :=
    (mem_centralizer_iff.mp (sd.two.le_cent sd.q.a_mem.2) b sd.q.b_mem.2).symm
  have hofQ : ∀ (y : Y) (hyQ : y ∈ Q) (hyD : y ∈ D), Abelianization.of (⟨y, hyD⟩ : D) = 1 := by
    intro y hyQ hyD
    rw [sd.q.Q_eq] at hyQ
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := mem_sup_prod (GL83P3L28Aux.le_normalizer_of_comm
      (zpowers_comm hab)) hyQ
    have h1K : y₁ ∈ K₁ := (zpowers_le.mpr sd.q.a_mem.2) hy₁
    have h2K : y₂ ∈ K₂ := (zpowers_le.mpr sd.q.b_mem.2) hy₂
    have : (⟨y₁ * y₂, hyD⟩ : D) = ⟨y₁, hK₁D h1K⟩ * ⟨y₂, hK₂D h2K⟩ := Subtype.ext rfl
    rw [this, map_mul, hofK K₁ sd.two.c₁ hK₁D y₁ h1K (hK₁D h1K),
      hofK K₂ sd.two.c₂ hK₂D y₂ h2K (hK₂D h2K), mul_one]
  have huD : u ∈ D := hPD huP
  have hqD : q ∈ D := hQD hqQ
  have hconj : MulAut.conjNormal t (⟨u, huD⟩ : D) = ⟨u, huD⟩ * ⟨q, hqD⟩ :=
    Subtype.ext (by simp [MulAut.conjNormal_apply, hutq])
  have hnorm : normMap D t ⟨u, huD⟩ =
      Abelianization.of (⟨u, huD⟩ : D) * Abelianization.of (⟨u, huD⟩ : D) := by
    rw [normMap_apply, hconj, map_mul, hofQ q hqQ hqD, mul_one]
  have hh1 : (Abelianization.of (⟨u, huD⟩ : D) * Abelianization.of (⟨u, huD⟩ : D)) ^ 2 = 1 := by
    rw [← hnorm, ← hh ⟨u, huD⟩]
    exact hfoc u huP
  obtain ⟨n, hn⟩ := sd.two.hs.sylow.isPGroup ⟨u, huP⟩
  have hu3 : (Abelianization.of (⟨u, huD⟩ : D)) ^ 3 ^ n = 1 := by
    rw [← map_pow]
    have : (⟨u, huD⟩ : D) ^ 3 ^ n = 1 := Subtype.ext (by simpa using congrArg Subtype.val hn)
    rw [this, map_one]
  have hu4 : (Abelianization.of (⟨u, huD⟩ : D)) ^ 4 = 1 := by
    have : (Abelianization.of (⟨u, huD⟩ : D) * Abelianization.of (⟨u, huD⟩ : D)) ^ 2 =
        (Abelianization.of (⟨u, huD⟩ : D)) ^ 4 := by
      rw [← pow_two, ← pow_mul]
    rw [← this]
    exact hh1
  have hofu : Abelianization.of (⟨u, huD⟩ : D) = 1 := by
    have := pow_gcd_eq_one.mpr ⟨hu4, hu3⟩
    rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right n (by norm_num)), pow_one] at this
  have hofP : ∀ (p : Y) (hp : p ∈ P), Abelianization.of (⟨p, hPD hp⟩ : D) = 1 := by
    intro p hp
    have hmem : p ∈ zpowers u ⊔ Q := by
      rw [sd.P_eq_sup huP huQ]
      exact hp
    obtain ⟨w, hw, q', hq', hwq⟩ := mem_sup_prod (zpowers_le.mpr (sd.q.P_norm huP)) hmem
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hw
    have : (⟨p, hPD hp⟩ : D) = ⟨u, huD⟩ ^ i * ⟨q', hQD hq'⟩ := Subtype.ext (by
      simp only [Subgroup.coe_mul, Subgroup.coe_zpow]
      exact hwq.symm)
    rw [this, map_mul, map_zpow, hofu, one_zpow, hofQ q' hq' (hQD hq'), mul_one]
  have hcomm : ∀ (p : Y) (hp : p ∈ D), p ∈ P → (⟨p, hp⟩ : D) ∈ commutator D := by
    intro p hp hpP
    have h1 : (⟨p, hp⟩ : D) ∈ (Abelianization.of : D →* Abelianization D).ker :=
      MonoidHom.mem_ker.mpr (hofP p hpP)
    rwa [Abelianization.ker_of] at h1
  have hP1 := P_le_sup_cent hd sd.two.hs sd.two.c₁ hN sd.rank_le_one le_rfl hPD hcomm
  have hP2 := P_le_sup_cent hd sd.two.hs sd.two.c₂ hN sd.symm.rank_le_one hDN₂ hPD hcomm
  have hPL : P ≤ K₁ ⊔ K₂ := sd.two.le_sup_of_cent hP1 hP2
  have hfac : ∀ {A B : Subgroup Y}, TwoData P A B → Nat.card (P ⊓ A : Subgroup Y) = 3 ^ 2 →
      (Nat.card A).factorization 3 = 2 := by
    intro A B hAB hc
    have := hAB.sylow_inf.card_eq
    rw [hc] at this
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) this).symm
  have hf1 := hfac sd.two (by rw [sd.q.S₁_eq, Nat.card_zpowers, sd.q.a_ord]; norm_num)
  have hf2 := hfac sd.two.symm (by rw [sd.q.S₂_eq, Nat.card_zpowers, sd.q.b_ord]; norm_num)
  have hdvd : 3 ^ 5 ∣ Nat.card K₁ * Nat.card K₂ := by
    rw [← sd.two.card_sup_comp, ← sd.two.hs.shape.1]
    exact Subgroup.card_dvd_of_le hPL
  have hne1 : Nat.card K₁ ≠ 0 := Nat.card_pos.ne'
  have hne2 : Nat.card K₂ ≠ 0 := Nat.card_pos.ne'
  have h5 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three
    (Nat.mul_ne_zero hne1 hne2)).mp hdvd
  rw [Nat.factorization_mul hne1 hne2, Finsupp.add_apply, hf1, hf2] at h5
  omega

end SwapData

theorem ClosedData.false_of_setting (hd : ClosedData P x k) (hs : CompSetting P)
    (h12 : KFactL28ThreeQuotient) (hC : KFactOutThreeCoprime) (hN : KFactOutThreeNilpotent) :
    False := by
  obtain ⟨K₁, K₂, h₁, h₂, hne, hall⟩ := hd.two_components hs h12
  have htw : TwoData P K₁ K₂ := ⟨hs, h₁, h₂, hne, hall⟩
  obtain ⟨ι, hιx, hικ⟩ := hd.invert
  have hswap := hd.iota_swaps htw hιx hικ
  obtain ⟨t, ht, hts⟩ := htw.exists_normalizer_swap hswap
  obtain ⟨Q, a, b, hq⟩ := htw.exists_QData hd hC ht hts
  exact (SwapData.mk htw hq ht hts).false_of_swap hd hN

end CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28Cl
