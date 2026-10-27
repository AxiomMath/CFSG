module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PrimeComplementCore
public import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.GroupTheory.FrattiniQuotient
import CFSG.RankThree.PartTwo.Sec5.Bender.Core

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

private theorem mul_card_le_card_of_lt {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {B W : Subgroup G} (hW : IsPGroup p W) (h : B < W) : p * Nat.card B ≤ Nat.card W := by
  have hp : p.Prime := Fact.out
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hW
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp (hW.to_le h.le)
  have hlt := Subgroup.card_lt_of_lt h
  rw [ha, hb] at hlt
  rw [ha, hb, ← pow_succ']
  exact Nat.pow_le_pow_right hp.pos ((Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt)

private theorem sup_zpowers_le_centralizer_self {G : Type*} [Group G] {B : Subgroup G} {y : G}
    (hB : B ≤ Subgroup.centralizer (B : Set G)) (hy : y ∈ Subgroup.centralizer (B : Set G)) :
    B ⊔ Subgroup.zpowers y ≤
      Subgroup.centralizer ((B ⊔ Subgroup.zpowers y : Subgroup G) : Set G) := by
  have h1 : Subgroup.zpowers y ≤ Subgroup.centralizer (B : Set G) := Subgroup.zpowers_le.mpr hy
  have h2 : B ⊔ Subgroup.zpowers y ≤ Subgroup.centralizer (Subgroup.zpowers y : Set G) :=
    sup_le (Subgroup.le_centralizer_iff.mp h1) (Subgroup.le_centralizer _)
  exact sup_le (Subgroup.le_centralizer_iff.mp (sup_le hB h1)) (Subgroup.le_centralizer_iff.mp h2)

theorem card_le_of_isPGroup_of_injective_mulAut {p : ℕ} [Fact p.Prime] {V A : Type*} [Group V]
    [Finite V] (hVc : ∀ x y : V, x * y = y * x) (hVe : ∀ x : V, x ^ p = 1)
    (hVcard : Nat.card V ≤ p ^ 2) [Group A] [Finite A] (hA : IsPGroup p A) (f : A →* MulAut V)
    (hf : Function.Injective f) : Nat.card A ≤ p := by
  have hp : p.Prime := Fact.out
  letI : MulDistribMulAction A V := MulDistribMulAction.compHom V f
  set F := FixedPoints.subgroup A V
  have hF : ∀ v, v ∈ F ↔ ∀ a : A, f a v = v := fun v => Iff.rfl
  have hVp : IsPGroup p V := fun v => ⟨1, by rw [pow_one, hVe]⟩
  by_cases hFtop : F = ⊤
  · have h1 : ∀ a : A, a = 1 := fun a => hf <| by
      ext v
      rw [map_one, MulAut.one_apply]
      exact (hF v).mp (hFtop ▸ Subgroup.mem_top v) a
    have : Subsingleton A := ⟨fun a b => (h1 a).trans (h1 b).symm⟩
    exact (Finite.card_le_one_iff_subsingleton.mpr this).trans hp.one_lt.le
  obtain ⟨u, hu⟩ : ∃ u, u ∉ F := by
    by_contra h
    push Not at h
    exact hFtop (eq_top_iff.mpr fun v _ => h v)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hVp
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    have : Subsingleton V := (Nat.card_eq_one_iff_unique.mp hn).1
    exact hu (Subsingleton.elim (1 : V) u ▸ F.one_mem)
  have hpF : p ∣ Nat.card F :=
    (Nat.ModEq.dvd_iff (hA.card_modEq_card_fixedPoints V) dvd_rfl).mp
      (hn ▸ dvd_pow_self p hn0)
  have hFp : p ≤ Nat.card F := Nat.le_of_dvd Nat.card_pos hpF
  have hW : F ⊔ Subgroup.zpowers u = ⊤ := by
    have hlt : F < F ⊔ Subgroup.zpowers u := SetLike.lt_iff_le_and_exists.mpr
      ⟨le_sup_left, u, Subgroup.mem_sup_right (Subgroup.mem_zpowers u), hu⟩
    have h1 := mul_card_le_card_of_lt (hVp.to_subgroup _) hlt
    refine Subgroup.eq_top_of_card_eq _ (le_antisymm (Subgroup.card_le_card_group _) ?_)
    calc Nat.card V ≤ p ^ 2 := hVcard
      _ = p * p := sq p
      _ ≤ p * Nat.card F := Nat.mul_le_mul_left p hFp
      _ ≤ _ := h1
  have hinj : Function.Injective fun a : A => f a u := by
    intro a b hab
    have hc : f (b⁻¹ * a) u = u := by
      change f a u = f b u at hab
      rw [map_mul, MulAut.mul_apply, hab, map_inv, MulAut.inv_apply, MulEquiv.symm_apply_apply]
    have hle : F ⊔ Subgroup.zpowers u ≤
        MonoidHom.eqLocus (f (b⁻¹ * a)).toMonoidHom (MonoidHom.id V) :=
      sup_le (fun v hv => (hF v).mp hv _) (Subgroup.zpowers_le.mpr hc)
    have h1 : f (b⁻¹ * a) = f 1 := by
      rw [map_one]
      ext v
      exact hle (hW ▸ Subgroup.mem_top v)
    exact (inv_mul_eq_one.mp (hf h1)).symm
  have hlt : Nat.card A < Nat.card V := by
    have hu1 : u ≠ 1 := fun h => hu (h ▸ F.one_mem)
    haveI := Fintype.ofFinite A
    haveI := Fintype.ofFinite V
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    refine Fintype.card_lt_of_injective_of_notMem _ hinj (b := 1) ?_
    rintro ⟨a, ha⟩
    exact hu1 ((f a).map_eq_one_iff.mp ha)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA
  have hk2 : p ^ k < p ^ 2 := hk ▸ hlt.trans_le hVcard
  have hk1 : k ≤ 1 := by
    have := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hk2
    omega
  rw [hk]
  calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hk1
    _ = p := pow_one p

theorem card_le_sq_mul_card_commutator {p : ℕ} [Fact p.Prime] {X : Type*} [Group X] [Finite X]
    {D : Subgroup X} (hDe : ∀ x ∈ D, x ^ p = 1)
    (hDc : ⁅D, D⁆ ≤ Subgroup.centralizer (D : Set X)) (hD2 : CFSG.Open.pRank p D ≤ 2) :
    Nat.card D ≤ p ^ 2 * Nat.card (⁅D, D⁆ : Subgroup X) := by
  have hp : p.Prime := Fact.out
  have hDp : IsPGroup p D := fun d => ⟨1, Subtype.ext (by simpa using hDe d d.2)⟩
  have hab : ∀ B : Subgroup X, B ≤ D → B ≤ Subgroup.centralizer (B : Set X) →
      Nat.card B ≤ p ^ 2 := by
    intro B hBD hBc
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hDp.to_le hBD)
    have hk2 := (CFSG.SectionRank.le_pRank hp.one_lt hBD
      ⟨Subgroup.le_centralizer_iff_isMulCommutative.mp hBc, fun x hx => hDe x (hBD hx)⟩
      hk).trans hD2
    rw [hk]
    exact Nat.pow_le_pow_right hp.pos hk2
  have hgrow : ∀ B : Subgroup X, B ≤ D → B ≤ Subgroup.centralizer (B : Set X) →
      ∀ y ∈ D, y ∈ Subgroup.centralizer (B : Set X) → y ∉ B →
        p * Nat.card B ≤ Nat.card (B ⊔ Subgroup.zpowers y : Subgroup X) ∧
          Nat.card (B ⊔ Subgroup.zpowers y : Subgroup X) ≤ p ^ 2 := by
    intro B hBD hBc y hyD hyB hyn
    have hWD : B ⊔ Subgroup.zpowers y ≤ D := sup_le hBD (Subgroup.zpowers_le.mpr hyD)
    have hlt : B < B ⊔ Subgroup.zpowers y := SetLike.lt_iff_le_and_exists.mpr
      ⟨le_sup_left, y, Subgroup.mem_sup_right (Subgroup.mem_zpowers y), hyn⟩
    exact ⟨mul_card_le_card_of_lt (hDp.to_le hWD) hlt,
      hab _ hWD (sup_zpowers_le_centralizer_self hBc hyB)⟩
  by_cases hDab : D ≤ Subgroup.centralizer (D : Set X)
  · calc Nat.card D ≤ p ^ 2 := hab D le_rfl hDab
      _ ≤ p ^ 2 * Nat.card (⁅D, D⁆ : Subgroup X) := Nat.le_mul_of_pos_right _ Nat.card_pos
  obtain ⟨x, hxD, hxc⟩ := SetLike.not_le_iff_exists.mp hDab
  set Z := D ⊓ Subgroup.centralizer (D : Set X)
  have hZD : Z ≤ D := inf_le_left
  have hZc : Z ≤ Subgroup.centralizer (Z : Set X) := fun z hz w hw => hz.2 w hw.1
  have hxZ : x ∈ Subgroup.centralizer (Z : Set X) := fun z hz => (hz.2 x hxD).symm
  have hD'D : ⁅D, D⁆ ≤ D := Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact D.mul_mem (D.mul_mem (D.mul_mem h₁ h₂) (D.inv_mem h₁)) (D.inv_mem h₂)
  have hZbot : ⊥ < Z := by
    refine bot_lt_iff_ne_bot.mpr fun h => hDab ?_
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, eq_bot_iff, ← h]
    exact le_inf hD'D hDc
  have hZp : p ≤ Nat.card Z := by
    simpa using mul_card_le_card_of_lt (hDp.to_le hZD) hZbot
  obtain ⟨h1, h2⟩ := hgrow Z hZD hZc x hxD hxZ fun h => hxc h.2
  have hBD : Z ⊔ Subgroup.zpowers x ≤ D := sup_le hZD (Subgroup.zpowers_le.mpr hxD)
  have hBc := sup_zpowers_le_centralizer_self hZc hxZ
  have hC : ∀ y ∈ D, ⁅x, y⁆ = 1 → y ∈ Z ⊔ Subgroup.zpowers x := by
    intro y hyD hxy
    by_contra hyB
    have hyc : y ∈ Subgroup.centralizer ((Z ⊔ Subgroup.zpowers x : Subgroup X) : Set X) := by
      rw [← Subgroup.zpowers_le, Subgroup.le_centralizer_iff]
      refine sup_le ?_ ?_
      · rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
        exact fun z hz => (hz.2 y hyD).symm
      · rw [Subgroup.zpowers_le, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
          Subgroup.mem_centralizer_singleton_iff]
        exact commutatorElement_eq_one_iff_mul_comm.mp hxy
    obtain ⟨h3, h4⟩ := hgrow _ hBD hBc y hyD hyc hyB
    have h5 : p ^ 3 ≤ p ^ 2 := by
      calc p ^ 3 = p * (p * p) := by ring
        _ ≤ p * (p * Nat.card Z) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hZp)
        _ ≤ p * Nat.card (Z ⊔ Subgroup.zpowers x : Subgroup X) := Nat.mul_le_mul_left _ h1
        _ ≤ p ^ 2 := h3.trans h4
    have := (Nat.pow_le_pow_iff_right hp.one_lt).mp h5
    omega
  let ψ : D →* (⁅D, D⁆ : Subgroup X) :=
    { toFun := fun y => ⟨⁅x, (y : X)⁆, Subgroup.commutator_mem_commutator hxD y.2⟩
      map_one' := Subtype.ext (commutatorElement_one_right x)
      map_mul' := fun y₁ y₂ => Subtype.ext <| by
        have hc := Subgroup.mem_centralizer_iff.mp
          (hDc (Subgroup.commutator_mem_commutator hxD y₂.2)) _ (D.inv_mem y₁.2)
        change ⁅x, (y₁ : X) * y₂⁆ = ⁅x, (y₁ : X)⁆ * ⁅x, (y₂ : X)⁆
        calc ⁅x, (y₁ : X) * y₂⁆ = x * y₁ * x⁻¹ * (⁅x, (y₂ : X)⁆ * (y₁ : X)⁻¹) := by
              simp only [commutatorElement_def]; group
          _ = x * y₁ * x⁻¹ * ((y₁ : X)⁻¹ * ⁅x, (y₂ : X)⁆) := by rw [hc]
          _ = ⁅x, (y₁ : X)⁆ * ⁅x, (y₂ : X)⁆ := by simp only [commutatorElement_def]; group }
  have hker : Nat.card ψ.ker ≤ Nat.card (Z ⊔ Subgroup.zpowers x : Subgroup X) := by
    rw [← Subgroup.card_map_of_injective D.subtype_injective]
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨y, hy, rfl⟩
    exact hC y y.2 (congrArg Subtype.val (MonoidHom.mem_ker.mp hy))
  calc Nat.card D = Nat.card ψ.ker * ψ.ker.index := (Subgroup.card_mul_index _).symm
    _ = Nat.card ψ.ker * Nat.card ψ.range := by rw [Subgroup.index_ker]
    _ ≤ Nat.card (Z ⊔ Subgroup.zpowers x : Subgroup X) * Nat.card (⁅D, D⁆ : Subgroup X) :=
        Nat.mul_le_mul hker (Subgroup.card_le_card_group _)
    _ ≤ p ^ 2 * Nat.card (⁅D, D⁆ : Subgroup X) := Nat.mul_le_mul_right _ h2

theorem false_of_pRank_le_two_of_surjective {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {X : Type*}
    [Group X] [Finite X] (hcore : primeComplementCore (G := X) p = ⊥) (hlayer : CFSG.layer X = ⊥)
    (hrank : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2) {J : Subgroup X} {S : Type*} [Group S]
    [Finite S] (hS : IsSimpleGroup S) (hSnab : ∃ a b : S, a * b ≠ b * a) (φ : J →* S)
    (hφ : Function.Surjective φ) (hS2 : p ^ 2 ∣ Nat.card S) : False := by
  have hp : p.Prime := Fact.out
  set Q := CFSG.pCore p X with hQdef
  have hQn : Q.Normal := CFSG.pCore_normal
  have hQp : IsPGroup p Q := CFSG.pCore_isPGroup
  have hQc : Subgroup.centralizer (Q : Set X) ≤ Q :=
    CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot X p hcore hlayer
  have hidx : p ^ 2 ∣ Q.index := by
    set E := Q.subgroupOf J
    have hEker : E ≤ φ.ker := by
      have hEn : (E.map φ).Normal := (Subgroup.normal_subgroupOf).map φ hφ
      haveI := hEn
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (E.map φ) with hb | ht
      · exact (Subgroup.map_eq_bot_iff _).mp hb
      · exfalso
        have hSp : IsPGroup p S := by
          have hEp : IsPGroup p E := hQp.comap_subtype
          have := hEp.map φ
          rw [ht] at this
          exact this.of_equiv Subgroup.topEquiv
        have hc := IsPGroup.center_nontrivial hSp
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with hb | ht
        · exact (Subgroup.nontrivial_iff_ne_bot _).mp hc hb
        · obtain ⟨a, b, hab⟩ := hSnab
          exact hab (Subgroup.mem_center_iff.mp (ht ▸ Subgroup.mem_top b) a)
    have hJ1 : Nat.card S * Nat.card φ.ker = Nat.card J := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv]
      exact (Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker).symm
    obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hEker
    have hSc : Nat.card S * c = E.index := by
      apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := E))
      rw [Subgroup.index_mul_card E, ← hJ1, hc]
      ring
    exact (hS2.trans (Dvd.intro c hSc)).trans (Subgroup.relIndex_dvd_index_of_normal Q J)
  have hQbot : Q ≠ ⊥ := by
    intro hQ
    have htop : Q = ⊤ := eq_top_iff.mpr fun x _ => hQc fun h hh => by
      rw [hQ] at hh
      rw [Subgroup.mem_bot.mp hh, one_mul, mul_one]
    rw [htop, Subgroup.index_top] at hidx
    have h1 := Nat.le_of_dvd one_pos hidx
    have h2 := Nat.one_lt_pow two_ne_zero hp.one_lt
    omega
  obtain ⟨D, hDQ, hDN, hDe, hDQc, hfaith⟩ :=
    CFSG.RankThree.PartTwo.Sec5.Bender.exists_critical_faithful hp2 hQp hQbot
  have hNQ : Subgroup.normalizer (Q : Set X) = ⊤ := Subgroup.normalizer_eq_top Q
  have hDn : D.Normal := Subgroup.normalizer_eq_top_iff.mp
    (eq_top_iff.mpr fun g _ => hDN g (hNQ ▸ Subgroup.mem_top g))
  have hDp : IsPGroup p D := hQp.to_le hDQ
  have hcard := card_le_sq_mul_card_commutator hDe
    ((Subgroup.commutator_mono le_rfl hDQ).trans hDQc)
    ((CFSG.SectionRank.pRank_mono hp.one_lt le_top).trans hrank)
  obtain ⟨-, hVc, hVe, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hDp
  have hVcard : Nat.card (D ⧸ frattini D) ≤ p ^ 2 := by
    have e1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini D)
    have e2 : Nat.card (_root_.commutator D) = Nat.card (⁅D, D⁆ : Subgroup X) := by
      rw [← Subgroup.card_map_of_injective D.subtype_injective, commutator_def,
        Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have e3 : Nat.card (⁅D, D⁆ : Subgroup X) ≤ Nat.card (frattini D) := by
      rw [← e2]
      exact Subgroup.card_le_of_le
        (CFSG.OrderReductions.FrattiniElementary.commutator_le_frattini p hDp)
    refine Nat.le_of_mul_le_mul_right ?_ (Nat.card_pos (α := (⁅D, D⁆ : Subgroup X)))
    calc Nat.card (D ⧸ frattini D) * Nat.card (⁅D, D⁆ : Subgroup X)
        ≤ Nat.card (D ⧸ frattini D) * Nat.card (frattini D) := Nat.mul_le_mul_left _ e3
      _ = Nat.card D := e1.symm
      _ ≤ p ^ 2 * Nat.card (⁅D, D⁆ : Subgroup X) := hcard
  let ρ : X →* MulAut (D ⧸ frattini D) :=
    (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini D)).comp
      MulAut.conjNormal
  have hKp : IsPGroup p ρ.ker := by
    rintro ⟨g, hg⟩
    obtain ⟨k, m, hm, hgm⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' p hp.ne_one
    refine ⟨k, Subtype.ext ?_⟩
    change g ^ p ^ k = 1
    have hym : (g ^ p ^ k) ^ m = 1 := by rw [← pow_mul, ← hgm, pow_orderOf_eq_one]
    have hρy : ρ (g ^ p ^ k) = 1 := by rw [map_pow, MonoidHom.mem_ker.mp hg, one_pow]
    generalize g ^ p ^ k = y at hym hρy ⊢
    have hyo : orderOf y ∣ m := orderOf_dvd_of_pow_eq_one hym
    obtain ⟨n, hn⟩ := (CFSG.GroupTheory.frattini_automorphism_kernel hDp).2
      ⟨MulAut.conjNormal y, MonoidHom.mem_ker.mpr hρy⟩
    have hc1 : (MulAut.conjNormal y : MulAut D) = 1 :=
      CFSG.RankThree.PartTwo.Sec5.Bender.eq_one_of_orderOf_dvd_of_pPow hp
        ⟨n, by simpa using congrArg Subtype.val hn⟩
        ((orderOf_map_dvd MulAut.conjNormal y).trans hyo) hm
    have hyD : y ∈ Subgroup.centralizer (D : Set X) := by
      refine Subgroup.mem_centralizer_iff.mpr fun d hd => ?_
      have h : y * d * y⁻¹ = d := by
        simpa using congrArg Subtype.val (DFunLike.congr_fun hc1 ⟨d, hd⟩)
      calc d * y = y * d * y⁻¹ * y := by rw [h]
        _ = y * d := by group
    have hyQ : y ∈ Q := hQc (hfaith (Subgroup.zpowers y)
      (by rw [Nat.card_zpowers]; exact fun h => hm (h.trans hyo))
      (by rw [hNQ]; exact le_top) (Subgroup.zpowers_le.mpr hyD) (Subgroup.mem_zpowers y))
    obtain ⟨n', hn'⟩ := hQp ⟨y, hyQ⟩
    exact CFSG.RankThree.PartTwo.Sec5.Bender.eq_one_of_orderOf_dvd_of_pPow hp
      ⟨n', by simpa using congrArg Subtype.val hn'⟩ hyo hm
  have hKQ : ρ.ker ≤ Q := by
    rw [hQdef]
    exact le_sSup ⟨ρ.normal_ker, hKp⟩
  have hdvd : p ^ 2 ∣ Nat.card (MulAut (D ⧸ frattini D)) := by
    refine hidx.trans ((Subgroup.index_dvd_of_le hKQ).trans ?_)
    rw [Subgroup.index_ker]
    exact Subgroup.card_subgroup_dvd_card _
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime p hdvd
  have hle := card_le_of_isPGroup_of_injective_mulAut (fun x y => mul_comm' x y) hVe hVcard
    (IsPGroup.of_card hP) P.subtype P.subtype_injective
  rw [hP] at hle
  have := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hle.trans_eq (pow_one p).symm)
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC
