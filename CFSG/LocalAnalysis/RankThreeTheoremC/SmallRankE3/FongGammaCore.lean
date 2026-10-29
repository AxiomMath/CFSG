module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSeitzB1
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421LinGrp
public import CFSG.LocalAnalysis.QuasithinUnique.K1.Glue

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongGamma

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.GLTheoremB (quotAutHom quotAutHom_mk)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {A : Type} [Group A]

theorem Bact_aux (H N B : Subgroup A) (hBH : B ≤ normalizer (H : Set A))
    (hBN : B ≤ normalizer (N : Set A)) (y : ↥B) :
    (N.subgroupOf H).map
      (((H.normalizerMonoidHom).comp (Subgroup.inclusion hBH)) y).toMonoidHom =
      N.subgroupOf H := by
  have key : ∀ z : ↥B, (N.subgroupOf H).map
      (((H.normalizerMonoidHom).comp (Subgroup.inclusion hBH)) z).toMonoidHom ≤ N.subgroupOf H := by
    intro z x hx
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    show (z : A) * (n : A) * (z : A)⁻¹ ∈ N
    exact (Subgroup.mem_normalizer_iff.mp (hBN z.2) (n : A)).mp hn
  refine le_antisymm (key y) ?_
  intro n hn
  have hm := key y⁻¹ (Subgroup.mem_map_of_mem
    (((H.normalizerMonoidHom).comp (Subgroup.inclusion hBH)) y⁻¹).toMonoidHom hn)
  refine Subgroup.mem_map.mpr ⟨_, hm, ?_⟩
  apply Subtype.ext
  show (y : A) * ((y : A)⁻¹ * (n : A) * (y : A)⁻¹⁻¹) * (y : A)⁻¹ = (n : A)
  group

@[expose] noncomputable def Bact (H N B : Subgroup A) [(N.subgroupOf H).Normal]
    (hBH : B ≤ normalizer (H : Set A)) (hBN : B ≤ normalizer (N : Set A)) :
    ↥B →* MulAut (↥H ⧸ N.subgroupOf H) :=
  quotAutHom (N.subgroupOf H) ((H.normalizerMonoidHom).comp (Subgroup.inclusion hBH))
    (Bact_aux H N B hBH hBN)

section Core

variable {H N B K₀ : Subgroup A} [(N.subgroupOf H).Normal]

theorem Bact_mk (hBH : B ≤ normalizer (H : Set A)) (hBN : B ≤ normalizer (N : Set A)) (y : ↥B)
    (h : ↥H) :
    Bact H N B hBH hBN y (QuotientGroup.mk h) =
      QuotientGroup.mk (⟨(y : A) * h * (y : A)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hBH y.2) h).mp h.2⟩ : ↥H) := by
  unfold Bact
  exact quotAutHom_mk (N.subgroupOf H) ((H.normalizerMonoidHom).comp (Subgroup.inclusion hBH))
    (Bact_aux H N B hBH hBN) y h

theorem Bact_of_mem (hBH : B ≤ normalizer (H : Set A)) (hBN : B ≤ normalizer (N : Set A))
    (y : ↥B) (hy : (y : A) ∈ H) :
    Bact H N B hBH hBN y =
      MulAut.conj (QuotientGroup.mk (⟨(y : A), hy⟩ : ↥H) : ↥H ⧸ N.subgroupOf H) := by
  ext x
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
  rw [Bact_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  exact congrArg QuotientGroup.mk (Subtype.ext rfl)

theorem pRank_quot_le {p : ℕ} (hp : p.Prime) [Finite A] (hHK : H ≤ K₀) (hNH : N ≤ H)
    (hNp : ¬ p ∣ Nat.card N) :
    CFSG.Open.pRank p (⊤ : Subgroup (↥H ⧸ N.subgroupOf H)) ≤ CFSG.Open.pRank p K₀ := by
  have hN' : ¬ p ∣ Nat.card (N.subgroupOf H) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv]
    exact hNp
  exact (CFSG.QuasithinUnique.K1.pRank_top_quotient_le H (N.subgroupOf H) hp hN').trans
    (CFSG.SectionRank.pRank_mono hp.one_lt hHK)

theorem conj_injective_J (hJ : IsSimpleGroup (↥H ⧸ N.subgroupOf H))
    (hJnc : ¬ ∀ a b : ↥H ⧸ N.subgroupOf H, a * b = b * a) :
    Function.Injective
      (MulAut.conj : (↥H ⧸ N.subgroupOf H) →* MulAut (↥H ⧸ N.subgroupOf H)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hcent : g ∈ Subgroup.center (↥H ⧸ N.subgroupOf H) := by
    rw [Subgroup.mem_center_iff]
    intro x
    have hx : g * x * g⁻¹ = x := by
      have h := DFunLike.congr_fun hg x
      simpa [MulAut.conj_apply] using h
    exact (mul_inv_eq_iff_eq_mul.mp hx).symm
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center (↥H ⧸ N.subgroupOf H)) with hbot | htop
  · rw [hbot] at hcent
    exact Subgroup.mem_bot.mp hcent
  · exfalso
    apply hJnc
    intro a b
    have hb : b ∈ Subgroup.center (↥H ⧸ N.subgroupOf H) := by
      rw [htop]
      exact Subgroup.mem_top b
    rw [Subgroup.mem_center_iff] at hb
    exact hb a

theorem exists_lam (hBH : B ≤ normalizer (H : Set A)) (hBN : B ≤ normalizer (N : Set A))
    (hJ : IsSimpleGroup (↥H ⧸ N.subgroupOf H))
    (hJnc : ¬ ∀ a b : ↥H ⧸ N.subgroupOf H, a * b = b * a)
    (hin : ∀ y : ↥B, Bact H N B hBH hBN y ∈ inner (↥H ⧸ N.subgroupOf H)) :
    ∃ lam : ↥B →* ↥H ⧸ N.subgroupOf H, ∀ y : ↥B, Bact H N B hBH hBN y = MulAut.conj (lam y) := by
  have hinj := conj_injective_J hJ hJnc
  have key : ∀ w : (MulAut.conj : (↥H ⧸ N.subgroupOf H) →* MulAut (↥H ⧸ N.subgroupOf H)).range,
      MulAut.conj ((MonoidHom.ofInjective hinj).symm w) = (w : MulAut (↥H ⧸ N.subgroupOf H)) := by
    intro w
    have h1 := MonoidHom.ofInjective_apply hinj (x := (MonoidHom.ofInjective hinj).symm w)
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1.symm
  refine ⟨(MonoidHom.ofInjective hinj).symm.toMonoidHom.comp
    (MonoidHom.codRestrict (Bact H N B hBH hBN)
      (MulAut.conj : (↥H ⧸ N.subgroupOf H) →* MulAut (↥H ⧸ N.subgroupOf H)).range hin), ?_⟩
  intro y
  exact (key (MonoidHom.codRestrict (Bact H N B hBH hBN)
      (MulAut.conj : (↥H ⧸ N.subgroupOf H) →* MulAut (↥H ⧸ N.subgroupOf H)).range hin y)).symm

theorem exists_ne_one_ker {J : Type*} [Group J] [Finite J] {B : Subgroup A} [Finite A] {p : ℕ}
    (hp : p.Prime) (hB : IsElemAbelian p B) (hBc : Nat.card B = p ^ 2)
    (hJr : CFSG.Open.pRank p (⊤ : Subgroup J) ≤ 1) (lam : ↥B →* J) :
    ∃ w : ↥B, w ≠ 1 ∧ lam w = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  have hcomm : ∀ a b : ↥B, a * b = b * a := isMulCommutative_iff.1 hB.1
  have hpow : ∀ a : ↥B, a ^ p = 1 := fun a => Subtype.ext (by
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact hB.2 _ a.2)
  have hE : IsElemAbelian p lam.range := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 x.2
      obtain ⟨b, hb⟩ := MonoidHom.mem_range.1 y.2
      show x * y = y * x
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha, ← hb, ← map_mul, ← map_mul, hcomm a b]
    · obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 hx
      rw [← ha, ← map_pow, hpow a, map_one]
  have hPG : IsPGroup p lam.range := by
    refine isPGroup_iff_pow_pow_eq_one.2 fun g => ⟨1, ?_⟩
    rw [pow_one]
    exact Subtype.ext (by
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
      exact hE.2 _ g.2)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hPG
  have hJr' : CFSG.Open.pRank p (⊤ : Subgroup J) ≤ 1 := hJr
  have hk0 : k ≤ CFSG.Open.pRank p (⊤ : Subgroup J) :=
    CFSG.SectionRank.le_pRank hp1 le_top hE hk
  have hk1 : k ≤ 1 := hk0.trans hJr'
  have hImg : Nat.card lam.range ≤ p := by
    rw [hk]
    calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hk1
      _ = p := pow_one p
  by_contra hcon
  push Not at hcon
  have hker : lam.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro w hw
    by_contra hw1
    exact hcon w hw1 (MonoidHom.mem_ker.1 hw)
  have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup lam.ker
  have hquot : Nat.card (↥B ⧸ lam.ker) = Nat.card lam.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange lam).toEquiv
  rw [hquot, hker, Subgroup.card_bot, mul_one] at hsplit
  have hle : p ^ 2 ≤ p := by
    rw [← hBc, hsplit]
    exact hImg
  rw [sq] at hle
  have h2 : 2 * p ≤ p * p := Nat.mul_le_mul hp.two_le le_rfl
  omega

theorem exists_good_y [Finite A] {p : ℕ} (hp : p.Prime)
    (hBH : B ≤ normalizer (H : Set A)) (hBN : B ≤ normalizer (N : Set A))
    (hB : IsElemAbelian p B) (hBc : Nat.card B = p ^ 2) {z : A} (hzB : z ∈ B) (hzH : z ∈ H)
    (hzo : orderOf z = p) (hNH : N ≤ H) (hNp : ¬ p ∣ Nat.card N)
    (hJ : IsSimpleGroup (↥H ⧸ N.subgroupOf H))
    (hJnc : ¬ ∀ a b : ↥H ⧸ N.subgroupOf H, a * b = b * a)
    (hJr : CFSG.Open.pRank p (⊤ : Subgroup (↥H ⧸ N.subgroupOf H)) ≤ 1) :
    ∃ y : ↥B, (y : A) ∉ zpowers z ∧ Bact H N B hBH hBN y ^ p = 1 ∧
      (Bact H N B hBH hBN y = 1 ∨ Bact H N B hBH hBN y ∉ inner (↥H ⧸ N.subgroupOf H)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hcon
  have hBpow : ∀ y : ↥B, y ^ p = 1 := fun y => Subtype.ext (by simpa using hB.2 (y : A) y.2)
  have hpow : ∀ y : ↥B, Bact H N B hBH hBN y ^ p = 1 := fun y => by
    rw [← map_pow, hBpow y, map_one]
  have key : ∀ y : ↥B, (y : A) ∉ zpowers z →
      Bact H N B hBH hBN y ≠ 1 ∧ Bact H N B hBH hBN y ∈ inner (↥H ⧸ N.subgroupOf H) := by
    intro y hy
    refine ⟨fun h1 => hcon ⟨y, hy, hpow y, Or.inl h1⟩, ?_⟩
    by_contra hnin
    exact hcon ⟨y, hy, hpow y, Or.inr hnin⟩
  have hin : ∀ y : ↥B, Bact H N B hBH hBN y ∈ inner (↥H ⧸ N.subgroupOf H) := by
    intro y
    by_cases hy : (y : A) ∈ zpowers z
    · obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hy
      have hyH : (y : A) ∈ H := by rw [← hi]; exact zpow_mem hzH i
      rw [Bact_of_mem hBH hBN y hyH]
      exact ⟨_, rfl⟩
    · exact (key y hy).2
  obtain ⟨lam, hlam⟩ := exists_lam hBH hBN hJ hJnc hin
  obtain ⟨w, hw1, hlw⟩ := exists_ne_one_ker hp hB hBc hJr lam
  have hinj := conj_injective_J (H := H) (N := N) hJ hJnc
  set zB : ↥B := ⟨z, hzB⟩ with hzBdef
  have hzmk : lam zB = (QuotientGroup.mk (⟨z, hzH⟩ : ↥H) : ↥H ⧸ N.subgroupOf H) := by
    apply hinj
    rw [← hlam zB, Bact_of_mem hBH hBN zB hzH]
  have hmk_ne : (QuotientGroup.mk (⟨z, hzH⟩ : ↥H) : ↥H ⧸ N.subgroupOf H) ≠ 1 := by
    intro h1
    have h2 := (QuotientGroup.eq_one_iff _).mp h1
    have h3 : z ∈ N := Subgroup.mem_subgroupOf.mp h2
    apply hNp
    rw [← hzo]
    exact Subgroup.orderOf_dvd_natCard N h3
  have hzp : z ^ p = 1 := by rw [← hzo]; exact pow_orderOf_eq_one z
  have hpow_mk : (QuotientGroup.mk (⟨z, hzH⟩ : ↥H) : ↥H ⧸ N.subgroupOf H) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : (⟨z, hzH⟩ : ↥H) ^ p = 1 := Subtype.ext (by simpa using hzp)
    rw [this]
    rfl
  have hord_mk : orderOf (QuotientGroup.mk (⟨z, hzH⟩ : ↥H) : ↥H ⧸ N.subgroupOf H) = p :=
    orderOf_eq_prime hpow_mk hmk_ne
  have hwz : (w : A) ∉ zpowers z := by
    intro hwz
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hwz
    have hwi : w = zB ^ i := Subtype.ext (by simpa [zB] using hi.symm)
    have h1 : lam zB ^ i = 1 := by rw [← map_zpow, ← hwi]; exact hlw
    rw [hzmk] at h1
    have hdvd : ((orderOf (QuotientGroup.mk (⟨z, hzH⟩ : ↥H) : ↥H ⧸ N.subgroupOf H) : ℕ) : ℤ) ∣ i :=
      orderOf_dvd_iff_zpow_eq_one.mpr h1
    rw [hord_mk] at hdvd
    have hz1 : z ^ i = 1 := by
      apply orderOf_dvd_iff_zpow_eq_one.mp
      rw [hzo]
      exact hdvd
    apply hw1
    apply Subtype.ext
    rw [Subgroup.coe_one, ← hi]
    exact hz1
  exact (key w hwz).1 (by rw [hlam w, hlw, map_one])

theorem fixed_le_image [Finite A] (hBH : B ≤ normalizer (H : Set A))
    (hBN : B ≤ normalizer (N : Set A)) {p : ℕ} (hp : p.Prime) (hNH : N ≤ H)
    (hNp : ¬ p ∣ Nat.card N) (y : ↥B) (hy : (y : A) ^ p = 1) :
    fixedSubgroup (Bact H N B hBH hBN y) ≤
      ((H ⊓ centralizer ({(y : A)} : Set A)).subgroupOf H).map
        (QuotientGroup.mk' (N.subgroupOf H)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hyp : y ^ p = 1 := Subtype.ext (by simpa using hy)
  have hF : IsPGroup p ↥(Subgroup.zpowers y) := by
    intro g
    refine ⟨1, Subtype.ext ?_⟩
    have h1 : (g : ↥B) ^ p = 1 := by
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 g.2
      rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hyp, one_zpow]
    simpa using h1
  have hNp' : ¬ p ∣ Nat.card (N.subgroupOf H) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv]
    exact hNp
  have hzpow : ∀ (τ : MulAut (↥H ⧸ N.subgroupOf H)) (q : ↥H ⧸ N.subgroupOf H), τ q = q →
      ∀ m : ℤ, (τ ^ m) q = q := by
    intro τ q hq m
    induction m using Int.induction_on with
    | zero => simp
    | succ n ih => rw [zpow_add_one, MulAut.mul_apply, hq, ih]
    | pred n ih =>
      have hinv : τ⁻¹ q = q := by
        conv_lhs => rw [← hq]
        exact MulAut.inv_apply_self _ τ q
      rw [zpow_sub_one, MulAut.mul_apply, hinv, ih]
  intro j hj
  have hjfix : Bact H N B hBH hBN y j = j := hj
  have hx : ∀ f ∈ Subgroup.zpowers y, Bact H N B hBH hBN f j = j := by
    intro f hf
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hf
    rw [map_zpow]
    exact hzpow _ j hjfix m
  obtain ⟨k, hkj, hkfix⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10F.exists_fixed_lift (q := p)
    (N.subgroupOf H) ((H.normalizerMonoidHom).comp (Subgroup.inclusion hBH))
    (Bact_aux H N B hBH hBN) hF hNp' j hx
  have hky : (y : A) * (k : A) * (y : A)⁻¹ = (k : A) :=
    congrArg Subtype.val (hkfix y (Subgroup.mem_zpowers y))
  have hC : (k : A) ∈ centralizer ({(y : A)} : Set A) := by
    refine Subgroup.mem_centralizer_iff.2 ?_
    intro g hg
    rw [Set.mem_singleton_iff.1 hg]
    exact mul_inv_eq_iff_eq_mul.1 hky
  refine Subgroup.mem_map.2 ⟨k, Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨k.2, hC⟩), ?_⟩
  rw [QuotientGroup.mk'_apply]
  exact hkj

theorem pSolvable_fixed [Finite A] (hBH : B ≤ normalizer (H : Set A))
    (hBN : B ≤ normalizer (N : Set A)) {p : ℕ} (hp : p.Prime) (hHK : H ≤ K₀) (hNH : N ≤ H)
    (hNp : ¬ p ∣ Nat.card N) (y : ↥B) (hy : (y : A) ^ p = 1)
    (h : CFSG.HallHigman.IsPSolvable p ↥(K₀ ⊓ centralizer ({(y : A)} : Set A))) :
    CFSG.HallHigman.IsPSolvable p ↥(fixedSubgroup (Bact H N B hBH hBN y)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hle₁ : H ⊓ centralizer ({(y : A)} : Set A) ≤ K₀ ⊓ centralizer ({(y : A)} : Set A) := by
    intro x hx
    exact Subgroup.mem_inf.mpr ⟨hHK (Subgroup.mem_inf.mp hx).1, (Subgroup.mem_inf.mp hx).2⟩
  have hle₂ : H ⊓ centralizer ({(y : A)} : Set A) ≤ H := by
    intro x hx
    exact (Subgroup.mem_inf.mp hx).1
  have hHC : CFSG.HallHigman.IsPSolvable p ↥(H ⊓ centralizer ({(y : A)} : Set A)) :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_of_le h hle₁
  have hHC' : CFSG.HallHigman.IsPSolvable p
      ↥((H ⊓ centralizer ({(y : A)} : Set A)).subgroupOf H) :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hle₂).symm hHC
  have himg : CFSG.HallHigman.IsPSolvable p
      ↥(((H ⊓ centralizer ({(y : A)} : Set A)).subgroupOf H).map
        (QuotientGroup.mk' (N.subgroupOf H))) :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_map
      (QuotientGroup.mk' (N.subgroupOf H)) hHC'
  exact CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_of_le himg
    (fixed_le_image hBH hBN hp hNH hNp y hy)

theorem gammaCore [Finite A] {p : ℕ} (hp : p.Prime)
    (hBH : B ≤ normalizer (H : Set A)) (hBN : B ≤ normalizer (N : Set A))
    (hB : IsElemAbelian p B) (hBc : Nat.card B = p ^ 2) {z : A} (hzB : z ∈ B) (hzH : z ∈ H)
    (hzo : orderOf z = p) (hHK : H ≤ K₀) (hNH : N ≤ H) (hNp : ¬ p ∣ Nat.card N)
    (hJ : IsSimpleGroup (↥H ⧸ N.subgroupOf H))
    (hJnc : ¬ ∀ a b : ↥H ⧸ N.subgroupOf H, a * b = b * a)
    (hJp : p ∣ Nat.card (↥H ⧸ N.subgroupOf H))
    (hK₀r : CFSG.Open.pRank p K₀ ≤ 1)
    (hI2 : ∀ α : MulAut (↥H ⧸ N.subgroupOf H), α ^ p = 1 → α ∉ inner (↥H ⧸ N.subgroupOf H) →
      ¬ CFSG.HallHigman.IsPSolvable p ↥(fixedSubgroup α)) :
    ∃ y ∈ B, y ∉ zpowers z ∧
      ¬ CFSG.HallHigman.IsPSolvable p ↥(K₀ ⊓ centralizer ({y} : Set A)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hJr : CFSG.Open.pRank p (⊤ : Subgroup (↥H ⧸ N.subgroupOf H)) ≤ 1 :=
    (pRank_quot_le hp hHK hNH hNp).trans hK₀r
  obtain ⟨y, hyz, hyp, hy⟩ := exists_good_y hp hBH hBN hB hBc hzB hzH hzo hNH hNp hJ hJnc hJr
  refine ⟨(y : A), y.2, hyz, ?_⟩
  intro hsolv
  have hBpow : (y : A) ^ p = 1 := by simpa using hB.2 (y : A) y.2
  have hfix := pSolvable_fixed hBH hBN hp hHK hNH hNp y hBpow hsolv
  rcases hy with h1 | h1
  · rw [h1] at hfix
    have htop : fixedSubgroup (1 : MulAut (↥H ⧸ N.subgroupOf H)) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      simp [fixedSubgroup]
    rw [htop] at hfix
    have hJsolv : CFSG.HallHigman.IsPSolvable p (↥H ⧸ N.subgroupOf H) :=
      CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
        (Subgroup.topEquiv : (⊤ : Subgroup (↥H ⧸ N.subgroupOf H)) ≃* _) hfix
    have hne : Nat.card (↥H ⧸ N.subgroupOf H) ≠ p := by
      intro hc
      haveI : Fact (Nat.card (↥H ⧸ N.subgroupOf H)).Prime := ⟨hc ▸ hp⟩
      haveI := isCyclic_of_prime_card hc
      exact hJnc fun a b => (IsCyclic.commGroup (α := ↥H ⧸ N.subgroupOf H)).mul_comm a b
    exact CFSG.LocalAnalysis.RankThreeUC.S15.K421GrpProof.not_isPSolvable_of_simple hJ hp hJp hne
      hJsolv
  · exact hI2 _ hyp h1 hfix

end Core

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongGamma
