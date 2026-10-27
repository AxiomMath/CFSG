module

public import CFSG.LocalAnalysis.AGLEmbedding.ResidualShared
import CFSG.LocalAnalysis.AGLEmbedding.PushingUpLemmas

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem exists_qElement_not_central {Y : Type} [Group Y] [Finite Y] {q : ℕ} (hq : q.Prime)
    {L : Subgroup Y} (hdvd : q ∣ Nat.card (↥L ⧸ Subgroup.center ↥L)) :
    ∃ y ∈ L, IsPGroup q (Subgroup.zpowers y) ∧ ∃ l ∈ L, y * l ≠ l * y := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨ub, hub⟩ := exists_prime_orderOf_dvd_card' (G := ↥L ⧸ Subgroup.center ↥L) q hdvd
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective ub
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos u).ne' q hq.ne_one
  set y : ↥L := u ^ b with hy
  have hyq : y ^ q ^ a = 1 := by
    rw [hy, ← pow_mul, mul_comm, ← hab, pow_orderOf_eq_one]
  have hyZ : y ∉ Subgroup.center ↥L := by
    intro hyc
    have h1 : ((u : ↥L ⧸ Subgroup.center ↥L)) ^ b = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hyc
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hub] at h2
    exact hb h2
  have hyq' : (y : Y) ^ q ^ a = 1 := by rw [← Subgroup.coe_pow, hyq, Subgroup.coe_one]
  refine ⟨(y : Y), y.2, isPGroup_zpowers_of_pow_eq_one hyq', ?_⟩
  rw [Subgroup.mem_center_iff] at hyZ
  push Not at hyZ
  obtain ⟨l, hl⟩ := hyZ
  exact ⟨l, l.2, fun he => hl (Subtype.ext he.symm)⟩

variable {G : Type} [Group G] [Finite G]

theorem le_pRank_of_injective_conj (hRank : StmtComponentRank) (hLift : StmtBarPRankLift)
    {M A : Subgroup G} (hAM : A ≤ M) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hLb : IsComponentOf Lb ⊤) (hLbA : Lb ≤ barM M A)
    {y l : ↥M ⧸ CFSG.pCore 2 ↥M} (hyL : y ∈ Lb) (hyq : IsPGroup q (Subgroup.zpowers y))
    (hlL : l ∈ Lb) (hyl : y * l ≠ l * y) {m : ℕ} (g : Fin m → ↥M ⧸ CFSG.pCore 2 ↥M)
    (hg : ∀ j, g j ∈ barM M A)
    (hinj : Function.Injective fun j => Lb.map (MulAut.conj (g j)).toMonoidHom) :
    m ≤ Open.pRank q A := by
  have h1 := hRank hq (fun j => Lb.map (MulAut.conj (g j)).toMonoidHom)
    (fun j => (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj (g j))
      Lb).mpr hLb) hinj (barM M A) (fun j => g j * y * (g j)⁻¹)
    (fun j => (barM M A).mul_mem ((barM M A).mul_mem (hg j) (hLbA hyL))
      ((barM M A).inv_mem (hg j)))
    (fun j => ⟨y, hyL, rfl⟩)
    (fun j => by
      obtain ⟨k, hk⟩ := hyq ⟨y, Subgroup.mem_zpowers y⟩
      have hk' : y ^ q ^ k = 1 := by simpa using congrArg Subtype.val hk
      exact isPGroup_zpowers_of_pow_eq_one (by rw [conj_pow, hk']; group))
    (fun j => ⟨g j * l * (g j)⁻¹, ⟨l, hlL, rfl⟩, fun he => hyl (by
      have := congrArg (fun z => (g j)⁻¹ * z * g j) he
      simpa [mul_assoc] using this)⟩)
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  exact h1.trans (hLift hq hq2 M A hAM)

omit [Finite G] in
theorem map_conj_inf_preimage_centralizer_le {M X : Subgroup G}
    {Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} {g : G} (hg : g ∈ M)
    (hgX : g ∈ Subgroup.normalizer (X : Set G))
    (hgL : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g, hg⟩ ∈ Subgroup.normalizer (Lb : Set _)) :
    (X ⊓ ((Subgroup.centralizer (Lb : Set _)).comap
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype).map (MulAut.conj g).toMonoidHom ≤
      X ⊓ ((Subgroup.centralizer (Lb : Set _)).comap
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype := by
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  rintro _ ⟨x, ⟨hxX, ⟨m, hm, hmx⟩⟩, rfl⟩
  refine ⟨(Subgroup.mem_normalizer_iff.mp hgX x).mp hxX, ⟨⟨g, hg⟩ * m * (⟨g, hg⟩)⁻¹,
    ?_, by simp [MulAut.conj_apply, ← hmx]⟩⟩
  show mk (⟨g, hg⟩ * m * (⟨g, hg⟩)⁻¹) ∈ Subgroup.centralizer (Lb : Set _)
  rw [map_mul, map_mul, map_inv, Subgroup.mem_centralizer_iff]
  intro z hz
  have hz' : (mk ⟨g, hg⟩)⁻¹ * z * mk ⟨g, hg⟩ ∈ Lb := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgL) z).mp hz
    simpa [mul_assoc] using this
  have hc := Subgroup.mem_centralizer_iff.mp hm _ hz'
  calc z * (mk ⟨g, hg⟩ * mk m * (mk ⟨g, hg⟩)⁻¹)
      = mk ⟨g, hg⟩ * (((mk ⟨g, hg⟩)⁻¹ * z * mk ⟨g, hg⟩) * mk m) * (mk ⟨g, hg⟩)⁻¹ := by
        group
    _ = mk ⟨g, hg⟩ * (mk m * ((mk ⟨g, hg⟩)⁻¹ * z * mk ⟨g, hg⟩)) * (mk ⟨g, hg⟩)⁻¹ := by
        rw [hc]
    _ = mk ⟨g, hg⟩ * mk m * (mk ⟨g, hg⟩)⁻¹ * z := by group

omit [Finite G] in
theorem injective_conj_pow_of_inf_preimage_centralizer {M X : Subgroup G}
    {Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} {r : ℕ} {t : G} (htM : t ∈ M)
    (htX : t ∈ Subgroup.normalizer (X : Set G))
    (hirr : ∀ k : ℕ, ¬ r ∣ k → ∀ Y : Subgroup G, Y ≤ X →
      t ^ k ∈ Subgroup.normalizer (Y : Set G) → Y = ⊥ ∨ Y = X)
    (hbot : X ⊓ ((Subgroup.centralizer (Lb : Set _)).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype ≠ ⊥)
    (htop : X ⊓ ((Subgroup.centralizer (Lb : Set _)).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype ≠ X) :
    Function.Injective fun j : Fin r => Lb.map
      (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨t, htM⟩ ^ (j : ℕ))).toMonoidHom := by
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set CX := X ⊓ ((Subgroup.centralizer (Lb : Set _)).comap mk).map M.subtype with hCX
  set tb := mk ⟨t, htM⟩ with htb
  have hstep : ∀ i j : ℕ, i < j → j < r →
      Lb.map (MulAut.conj (tb ^ i)).toMonoidHom = Lb.map (MulAut.conj (tb ^ j)).toMonoidHom →
      False := by
    intro i j hij hjr he
    have htbk : tb ^ (j - i) ∈ Subgroup.normalizer (Lb : Set _) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have hj : tb ^ j = tb ^ i * tb ^ (j - i) := by rw [← pow_add]; congr 1; omega
      rw [hj, map_conj_mul_eq] at he
      exact (Subgroup.map_injective (MulAut.conj (tb ^ i)).injective he).symm
    have htk : t ^ (j - i) ∈ Subgroup.normalizer (CX : Set G) := by
      have hle : Subgroup.zpowers (t ^ (j - i)) ≤ Subgroup.normalizer (CX : Set G) := by
        refine le_normalizer_of_forall_map_conj_le fun g hg => ?_
        obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
        have hgM : (t ^ (j - i)) ^ z ∈ M := M.zpow_mem (M.pow_mem htM _) z
        refine map_conj_inf_preimage_centralizer_le hgM
          (Subgroup.zpow_mem _ (Subgroup.pow_mem _ htX _) z) ?_
        have : mk ⟨(t ^ (j - i)) ^ z, hgM⟩ = (tb ^ (j - i)) ^ z := by
          rw [htb, ← map_pow, ← map_zpow]
          rfl
        rw [this]
        exact Subgroup.zpow_mem _ htbk z
      exact hle (Subgroup.mem_zpowers _)
    have hrk : ¬ r ∣ j - i := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    rcases hirr (j - i) hrk CX inf_le_left htk with h1 | h1
    · exact hbot h1
    · exact htop h1
  intro i j hij
  by_contra hne
  have hne' : (i : ℕ) ≠ j := fun h => hne (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hne' with hlt | hlt
  · exact hstep i j hlt j.2 hij
  · exact hstep j i hlt i.2 hij.symm

theorem D1L2Data.inf_preimage_centralizer_ne_bot {p n : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M H R X : Subgroup G} (h : D1L2Data p n P M H R X) (hβ : KFactOutElemRank) (hp : 5 ≤ p)
    {Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hLbC : IsComponentOf Lb ⊤)
    (hLcat : IsCatalogGroup (↥Lb ⧸ Subgroup.center ↥Lb)) (hpL : ¬ p ∣ Nat.card Lb)
    (hXN : barM M X ≤ Subgroup.normalizer (Lb : Set _)) :
    X ⊓ ((Subgroup.centralizer (Lb : Set _)).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype ≠ ⊥ := by
  intro hCXbot
  have hpp : p.Prime := Fact.out
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have hXM : X ≤ M := h.le_R.trans h.ph3.le_M
  have hO2 : p.Coprime (Nat.card (CFSG.pCore 2 ↥M)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hpp Nat.prime_two).mpr h.ph3.ne_two)
  have hXsub : IsPGroup p (X.subgroupOf M) := by
    intro z
    have hz : ((z : M) : G) ^ p = 1 := h.isElemAbelian.2 _ (Subgroup.mem_subgroupOf.mp z.2)
    exact ⟨1, Subtype.ext (Subtype.ext (by simpa using hz))⟩
  have hEl : IsElemAbelian p (barM M X) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨⟨a', ha'M⟩, ha', rfl⟩⟩ := a
      obtain ⟨_, ⟨⟨b', hb'M⟩, hb', rfl⟩⟩ := b
      change mk ⟨a', ha'M⟩ * mk ⟨b', hb'M⟩ = mk ⟨b', hb'M⟩ * mk ⟨a', ha'M⟩
      rw [← map_mul, ← map_mul]
      congr 1
      have : IsMulCommutative X := h.isElemAbelian.1
      exact Subtype.ext (setLike_mul_comm (Subgroup.mem_subgroupOf.mp ha')
        (Subgroup.mem_subgroupOf.mp hb'))
    · rintro _ ⟨⟨x, hxM⟩, hxX, rfl⟩
      have hx1 : x ^ p = 1 := h.isElemAbelian.2 x (Subgroup.mem_subgroupOf.mp hxX)
      have : (⟨x, hxM⟩ : M) ^ p = 1 := Subtype.ext (by simpa using hx1)
      rw [← map_pow, this, map_one]
  have hinf : barM M X ⊓ Subgroup.centralizer (Lb : Set _) = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨⟨⟨x, hxM⟩, hxX, rfl⟩, hzC⟩
    have hxCX : x ∈ X ⊓ ((Subgroup.centralizer (Lb : Set _)).comap mk).map M.subtype :=
      ⟨Subgroup.mem_subgroupOf.mp hxX, ⟨⟨x, hxM⟩, hzC, rfl⟩⟩
    rw [hCXbot, Subgroup.mem_bot] at hxCX
    have : (⟨x, hxM⟩ : M) = 1 := Subtype.ext hxCX
    rw [Subgroup.mem_bot, this, map_one]
  have hle := hβ _ Lb (barM M X) hLbC hLcat p hpp hp hpL hXN hEl hinf
  have hcard : Nat.card (barM M X) = p ^ n := by
    rw [barM, card_map_mk_of_isPGroup hpp _ hO2 hXsub,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv, h.card_eq]
  rw [hcard] at hle
  have h3 : p ^ 3 ≤ p ^ n := Nat.pow_le_pow_right hpp.pos h.three_le
  have h4 : p < p ^ 3 := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 3 := Nat.pow_lt_pow_right hpp.one_lt (by norm_num)
  omega

theorem stmtFiveKComponents_of (hα : KFactThreeOrFiveDvd) (hβ : KFactOutElemRank)
    (hT1 : StmtPPDElement) (hRank : StmtComponentRank) (hLift : StmtBarPRankLift) :
    StmtFiveKComponents := by
  intro G _ _ p n _ P M H R X h hp L hL2 hLK
  by_contra hXC
  have hpp : p.Prime := Fact.out
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Lb := barM M L with hLb
  set Kb := barM M (H ⊓ M) with hKb
  have hLbC : IsComponentOf Lb ⊤ := hL2.component
  have hXK : X ≤ H ⊓ M := h.le_R.trans h.ph3.le_inf
  have hMtop : M ≠ ⊤ := fun hM => h.ph3.not_le (hM ▸ le_top)
  have hcat : CatalogSimpleSections (↥M ⧸ CFSG.pCore 2 ↥M) :=
    (catalogSimpleSections_of_isKProper h.ph3.glob.kProper M hMtop).quotient _
  have hLcat := hcat.isCatalogGroup_center_quotient hLbC
  have hpL : ¬ p ∣ Nat.card Lb := by
    have hLN := h.perfect_le L hLK hL2.perfect
    have hcop : p.Coprime (Nat.card L) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hLN) (glbPrimeCore_coprime p H)
    have hdvd : Nat.card Lb ∣ Nat.card L := by
      have := Subgroup.card_map_dvd (L.subgroupOf M) mk
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL2.le).toEquiv] at this
    intro hpd
    exact (Nat.Prime.coprime_iff_not_dvd hpp).mp hcop (hpd.trans hdvd)
  have hsimple : IsSimpleGroup (↥Lb ⧸ Subgroup.center ↥Lb) := hLbC.2.2.2
  obtain ⟨q, hq, hq2, hqp, hqdvd⟩ : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q < p ∧
      q ∣ Nat.card (↥Lb ⧸ Subgroup.center ↥Lb) := by
    rcases hα _ hsimple (ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian
      _ hLbC.2.2) hLcat with h3 | h5
    · exact ⟨3, Nat.prime_three, by decide, by omega, h3⟩
    · refine ⟨5, Nat.prime_five, by decide, ?_, h5⟩
      have hdvdL : Nat.card (↥Lb ⧸ Subgroup.center ↥Lb) ∣ Nat.card Lb :=
        Subgroup.card_quotient_dvd_card _
      have hp5 : p ≠ 5 := fun he => hpL (he ▸ h5.trans hdvdL)
      omega
  obtain ⟨y, hyL, hyq, l, hlL, hyl⟩ := exists_qElement_not_central hq hqdvd
  have hLbK : Lb ≤ Kb := Subgroup.map_mono (fun z hz => Subgroup.mem_subgroupOf.mpr
    (hLK (Subgroup.mem_subgroupOf.mp hz)))
  have horbit : ∀ (m : ℕ) (g : Fin m → ↥M ⧸ CFSG.pCore 2 ↥M), (∀ j, g j ∈ Kb) →
      Function.Injective (fun j => Lb.map (MulAut.conj (g j)).toMonoidHom) → m ≤ 3 := by
    intro m g hg hinj
    have hm := le_pRank_of_injective_conj hRank hLift inf_le_right hq hq2 hLbC hLbK hyL hyq hlL
      hyl g hg hinj
    by_contra hm3
    exact h.false_of_four_le_pRank hq hq2 hqp (by omega)
  by_cases hXN : barM M X ≤ Subgroup.normalizer (Lb : Set _)
  ·
    obtain ⟨r, t, hr, -, hr2, hr3, -, -, htK, htX, -, -, -, hirr⟩ := hT1 h
    have htop : X ⊓ ((Subgroup.centralizer (Lb : Set _)).comap mk).map M.subtype ≠ X := by
      intro he
      apply hXC
      rintro _ ⟨⟨x, hxM⟩, hxX, rfl⟩
      have hxCX : x ∈ X ⊓ ((Subgroup.centralizer (Lb : Set _)).comap mk).map M.subtype := by
        rw [he]
        exact Subgroup.mem_subgroupOf.mp hxX
      obtain ⟨m, hm, hmx⟩ := hxCX.2
      have : m = ⟨x, hxM⟩ := Subtype.ext hmx
      subst this
      exact hm
    have hinj := injective_conj_pow_of_inf_preimage_centralizer htK.2 htX hirr
      (h.inf_preimage_centralizer_ne_bot hβ hp hLbC hLcat hpL hXN) htop
    have := horbit r _ (fun j => Kb.pow_mem
      (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr htK)) _) hinj
    have := hr.five_le_of_ne_two_of_ne_three hr2 hr3
    omega
  ·
    obtain ⟨xb, hxb, hxbN⟩ := Set.not_subset.mp hXN
    obtain ⟨⟨x, hxM⟩, hxX, rfl⟩ := hxb
    have hxX' : x ∈ X := Subgroup.mem_subgroupOf.mp hxX
    have hxbK : mk ⟨x, hxM⟩ ∈ Kb :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (hXK hxX'))
    have hxp : IsPGroup p (Subgroup.zpowers (mk ⟨x, hxM⟩)) := by
      refine isPGroup_zpowers_of_pow_eq_one (k := 1) ?_
      have hx1 : x ^ p = 1 := h.isElemAbelian.2 x hxX'
      have : (⟨x, hxM⟩ : M) ^ p = 1 := Subtype.ext (by simpa using hx1)
      rw [pow_one, ← map_pow, this, map_one]
    have hinj := injective_conj_pow_of_not_mem_normalizer hxp hxbN
    have := horbit p (fun j => (mk ⟨x, hxM⟩) ^ (j : ℕ)) (fun j => Kb.pow_mem hxbK _) hinj
    omega

theorem stmtFiveComponents_of (hR1 : StmtROne) (hK : StmtFiveKComponents) :
    StmtFiveComponents := by
  intro G _ _ p n _ P M H R X h hp Lbar hL
  obtain ⟨L, hL2, rfl, hL'⟩ := h.ph3.exists_weakSBlock_or_le_inf hL
  rcases hL' with hw | hle
  · exact hR1 h (Or.inr hp) L hw
  · exact hK h hp L hL2 hle

end CFSG.AGLEmbedding
