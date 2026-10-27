module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627L32Data
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open CFSG.LocalAnalysis.RankThreeTheoremC.L32Insp
open scoped MatrixGroups

variable {C : Type} [Group C] [Finite C]

theorem p622Exit_card_mulAut : Nat.card (MulAut GL32) = 336 := by
  have hInn : Nat.card Inn = 168 := by
    rw [← card_GL]
    exact Nat.card_congr (MonoidHom.ofInjective innConj_injective).symm.toEquiv
  have h := Subgroup.card_mul_index Inn
  rw [hInn, index_Inn] at h
  omega

theorem p622Exit_inf_centralizer {L : Subgroup C} (e : ↥L ≃* GL32) :
    centralizer (L : Set C) ⊓ L = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hgC, hgL⟩ := Subgroup.mem_inf.1 hg
  have hcomm : ∀ k : ↥L, k * (⟨g, hgL⟩ : ↥L) = (⟨g, hgL⟩ : ↥L) * k := fun k =>
    Subtype.ext (Subgroup.mem_centralizer_iff.1 hgC (k : C) k.2)
  have hcen : e ⟨g, hgL⟩ ∈ Subgroup.center GL32 := by
    rw [Subgroup.mem_center_iff]
    intro h
    have hk := congrArg e (hcomm (e.symm h))
    simpa only [map_mul, MulEquiv.apply_symm_apply] using hk
  rw [center_GL32, Subgroup.mem_bot] at hcen
  have h1 : (⟨g, hgL⟩ : ↥L) = 1 := e.injective (by rw [hcen, map_one])
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val h1

private def p622Prod {G : Type*} [Group G] (A B : Subgroup G)
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : Subgroup G where
  carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
  mul_mem' := by
    rintro _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
    refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
    calc a₁ * b₁ * (a₂ * b₂) = a₁ * (a₂ * b₁) * b₂ := by rw [hc a₂ ha₂ b₁ hb₁]; simp only [mul_assoc]
      _ = a₁ * a₂ * (b₁ * b₂) := by simp only [mul_assoc]
  one_mem' := ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
  inv_mem' := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    have hcom : Commute a b := hc a ha b hb
    rw [mul_inv_rev]
    exact hcom.inv_inv.eq.symm

private lemma mem_p622Prod {G : Type*} [Group G] {A B : Subgroup G}
    {hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a} {x : G} :
    x ∈ p622Prod A B hc ↔ ∃ a ∈ A, ∃ b ∈ B, x = a * b :=
  Iff.rfl

private lemma isElemAbelian_p622Prod {G : Type*} [Group G] {p : ℕ} {A B : Subgroup G}
    (hA : IsElemAbelian p A) (hB : IsElemAbelian p B)
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : IsElemAbelian p (p622Prod A B hc) := by
  obtain ⟨hAm, hAp⟩ := hA
  obtain ⟨hBm, hBp⟩ := hB
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    intro x hx y hy
    have h := hAm.is_comm.comm (⟨x, hx⟩ : ↥A) ⟨y, hy⟩
    exact congrArg Subtype.val h
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    have h := hBm.is_comm.comm (⟨x, hx⟩ : ↥B) ⟨y, hy⟩
    exact congrArg Subtype.val h
  have hcomm : ∀ x ∈ p622Prod A B hc, ∀ y ∈ p622Prod A B hc, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := mem_p622Prod.1 hx
    obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := mem_p622Prod.1 hy
    calc a₁ * b₁ * (a₂ * b₂) = a₁ * (a₂ * b₁) * b₂ := by rw [hc a₂ ha₂ b₁ hb₁]; simp only [mul_assoc]
      _ = a₁ * a₂ * (b₁ * b₂) := by simp only [mul_assoc]
      _ = a₂ * a₁ * (b₂ * b₁) := by rw [hAc a₁ ha₁ a₂ ha₂, hBc b₁ hb₁ b₂ hb₂]
      _ = a₂ * (a₁ * b₂) * b₁ := by simp only [mul_assoc]
      _ = a₂ * (b₂ * a₁) * b₁ := by rw [hc a₁ ha₁ b₂ hb₂]
      _ = a₂ * b₂ * (a₁ * b₁) := by simp only [mul_assoc]
  refine ⟨⟨⟨fun x y => Subtype.ext (hcomm x.1 x.2 y.1 y.2)⟩⟩, ?_⟩
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_p622Prod.1 hx
  have hab : Commute a b := hc a ha b hb
  rw [hab.mul_pow, hAp a ha, hBp b hb, one_mul]

private lemma card_le_card_p622Prod {G : Type*} [Group G] [Finite G] {A B : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hAB : A ⊓ B = ⊥) :
    Nat.card A * Nat.card B ≤ Nat.card (p622Prod A B hc) := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun q : ↥A × ↥B => (⟨(q.1 : G) * (q.2 : G),
      mem_p622Prod.2 ⟨(q.1 : G), q.1.2, (q.2 : G), q.2.2, rfl⟩⟩ : ↥(p622Prod A B hc))) ?_
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
  have h' : (a₁ : G) * (b₁ : G) = (a₂ : G) * (b₂ : G) := congrArg Subtype.val h
  have hu : (a₂ : G)⁻¹ * (a₁ : G) = (b₂ : G) * (b₁ : G)⁻¹ := by
    calc (a₂ : G)⁻¹ * (a₁ : G) = (a₂ : G)⁻¹ * ((a₁ : G) * (b₁ : G)) * (b₁ : G)⁻¹ := by group
      _ = (a₂ : G)⁻¹ * ((a₂ : G) * (b₂ : G)) * (b₁ : G)⁻¹ := by rw [h']
      _ = (b₂ : G) * (b₁ : G)⁻¹ := by group
  have h1 : (a₂ : G)⁻¹ * (a₁ : G) = 1 := by
    have hmem : (a₂ : G)⁻¹ * (a₁ : G) ∈ A ⊓ B :=
      ⟨A.mul_mem (A.inv_mem a₂.2) a₁.2, by rw [hu]; exact B.mul_mem b₂.2 (B.inv_mem b₁.2)⟩
    rw [hAB, Subgroup.mem_bot] at hmem
    exact hmem
  have ha : a₁ = a₂ := Subtype.ext (inv_mul_eq_one.1 h1).symm
  subst ha
  have hb : (b₁ : G) = (b₂ : G) := mul_left_cancel h'
  have hb' : b₁ = b₂ := Subtype.ext hb
  subst hb'
  rfl

private lemma p622_exists_elemAbelian_nine {R : Subgroup C} (hR : IsPGroup 3 R)
    (hnc : ¬ IsCyclic R) : ∃ A : Subgroup C, A ≤ R ∧ IsElemAbelian 3 A ∧ Nat.card A = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (IsPGroup 3 R) := ⟨hR⟩
  obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a (p := 3) (by norm_num) hnc
  refine ⟨S.map R.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · exact (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).1
      CFSG.IsElementaryAbelian.map_subtype
  · rw [← Nat.card_congr (S.equivMapOfInjective R.subtype R.subtype_injective).toEquiv]
    exact hScard.trans (by norm_num)

theorem p622Exit_cyclic {L : Subgroup C} (e : ↥L ≃* GL32)
    (hrk : ∀ E : Subgroup C, IsElemAbelian 3 E → Nat.card E ≤ 9) {R : Subgroup C}
    (hR : IsPGroup 3 R) (hRQ : R ≤ centralizer (L : Set C)) : IsCyclic ↥R := by
  by_contra hnc
  obtain ⟨A, hAR, hAel, hAcard⟩ := p622_exists_elemAbelian_nine hR hnc
  obtain ⟨z0, hz0L, hz0ord⟩ : ∃ z0 ∈ L, orderOf z0 = 3 := by
    refine ⟨((e.symm l₀ : ↥L) : C), (e.symm l₀).2, ?_⟩
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq e.symm l₀, orderOf_l₀]
  have hz0A : ∀ a ∈ A, Commute a z0 := fun a ha =>
    (Subgroup.mem_centralizer_iff.1 (hRQ (hAR ha)) z0 hz0L).symm
  have hBcard : Nat.card (Subgroup.zpowers z0) = 3 := by
    rw [Nat.card_zpowers, hz0ord]
  have hBcomm : ∀ x ∈ Subgroup.zpowers z0, ∀ y ∈ Subgroup.zpowers z0, x * y = y * x := by
    rintro _ hx _ hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_zpow_self z0 k m).eq
  have hz3 : z0 ^ 3 = 1 := by
    rw [← hz0ord]
    exact pow_orderOf_eq_one z0
  have hBpow : ∀ x ∈ Subgroup.zpowers z0, x ^ 3 = 1 := by
    rintro _ hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow]
  have hBel : IsElemAbelian 3 (Subgroup.zpowers z0) :=
    ⟨⟨⟨fun x y => Subtype.ext (hBcomm x.1 x.2 y.1 y.2)⟩⟩, hBpow⟩
  have hc : ∀ a ∈ A, ∀ b ∈ Subgroup.zpowers z0, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact ((hz0A a ha).zpow_right k).eq
  have hAB : A ⊓ Subgroup.zpowers z0 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxA, hxB⟩ := Subgroup.mem_inf.1 hx
    have hxL : x ∈ L := Subgroup.zpowers_le.2 hz0L hxB
    have hxI : x ∈ centralizer (L : Set C) ⊓ L :=
      Subgroup.mem_inf.2 ⟨hRQ (hAR hxA), hxL⟩
    rw [p622Exit_inf_centralizer e, Subgroup.mem_bot] at hxI
    exact Subgroup.mem_bot.2 hxI
  have hbig := card_le_card_p622Prod hc hAB
  have hsmall := hrk _ (isElemAbelian_p622Prod hAel hBel hc)
  rw [hAcard, hBcard] at hbig
  omega

theorem p622Exit_card_eq_three_of_cyclic {x : C} (hx3 : orderOf x = 3)
    (hcube : ∀ y : C, (∃ k : ℕ, y ^ 3 ^ k = 1) → y ^ 3 ≠ x)
    {R : Subgroup C} (hcyc : IsCyclic R) (hR : IsPGroup 3 R) (hxR : x ∈ R) :
    Nat.card R = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hR
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := R)
  have hord : orderOf g = Nat.card R := orderOf_eq_card_of_forall_mem_powers hg
  have hx3' : x ^ 3 = 1 := by
    rw [← hx3]
    exact pow_orderOf_eq_one x
  have hx3R : (⟨x, hxR⟩ : R) ^ 3 = 1 := Subtype.ext (by simpa using hx3')
  have h3dvd : 3 ∣ Nat.card R := by
    have h := orderOf_dvd_natCard (⟨x, hxR⟩ : R)
    rwa [Subgroup.orderOf_mk, hx3] at h
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [pow_zero] at ha
    rw [ha] at h3dvd
    norm_num at h3dvd
  rcases Nat.lt_or_ge a 2 with ha2 | ha2
  · have ha1 : a = 1 := by omega
    rw [ha, ha1, pow_one]
  · exfalso
    obtain ⟨c, rfl⟩ : ∃ c, a = c + 2 := ⟨a - 2, by omega⟩
    obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).mp (hg ⟨x, hxR⟩)
    have hgm : g ^ (3 * m) = 1 := by rw [pow_mul', hm, hx3R]
    have hdvd0 : orderOf g ∣ 3 * m := orderOf_dvd_of_pow_eq_one hgm
    rw [hord, ha, show 3 ^ (c + 2) = 3 * 3 ^ (c + 1) by ring] at hdvd0
    obtain ⟨t, rfl⟩ : 3 ^ (c + 1) ∣ m := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd0
    have hy3 : (g ^ (3 ^ c * t)) ^ 3 = ⟨x, hxR⟩ := by
      rw [← pow_mul, ← hm]
      congr 1
      ring
    have hg1 : g ^ (3 ^ (c + 2)) = 1 := by
      rw [← ha, ← hord]
      exact pow_orderOf_eq_one g
    have hy : (g ^ (3 ^ c * t)) ^ (3 ^ (c + 2)) = 1 := by
      rw [← pow_mul, show 3 ^ c * t * 3 ^ (c + 2) = 3 ^ (c + 2) * (3 ^ c * t) by ring,
        pow_mul, hg1, one_pow]
    have hyC3 : ((g ^ (3 ^ c * t) : R) : C) ^ 3 = x := by
      simpa using congrArg Subtype.val hy3
    have hyCo : ((g ^ (3 ^ c * t) : R) : C) ^ (3 ^ (c + 2)) = 1 := by
      simpa using congrArg Subtype.val hy
    exact hcube _ ⟨c + 2, hyCo⟩ hyC3

theorem p622Exit_centralizer_eq {L : Subgroup C} [L.Normal] (e : ↥L ≃* GL32) {x : C}
    (hx : x ∈ Subgroup.center C) (hx3 : orderOf x = 3)
    (hno : ∀ N : Subgroup C, N.Normal → Nat.Coprime 3 (Nat.card N) → N = ⊥)
    (hrk : ∀ E : Subgroup C, IsElemAbelian 3 E → Nat.card E ≤ 9)
    (hcube : ∀ y : C, (∃ k : ℕ, y ^ 3 ^ k = 1) → y ^ 3 ≠ x) :
    centralizer (L : Set C) = zpowers x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Subgroup C, Q = centralizer (L : Set C) := ⟨_, rfl⟩
  have hQn : Q.Normal := by
    rw [hQ]
    infer_instance
  have hmemQ : ∀ c : C, c ∈ Q ↔ ∀ l ∈ (L : Set C), l * c = c * l := fun c => by
    rw [hQ]
    exact Subgroup.mem_centralizer_iff
  have hxQ : x ∈ Q := (hmemQ x).mpr fun l _ => Subgroup.mem_center_iff.mp hx l
  obtain ⟨x', hx'⟩ : ∃ x' : Q, (x' : C) = x := ⟨⟨x, hxQ⟩, rfl⟩
  have hxc : ∀ g : Q, Commute x' g := by
    intro g
    show x' * g = g * x'
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hx']
    exact (Subgroup.mem_center_iff.mp hx (g : C)).symm
  have hx'ord : orderOf x' = 3 := by
    rw [← Subgroup.orderOf_coe, hx', hx3]
  have hZ3 : IsPGroup 3 (zpowers x') :=
    IsPGroup.of_card (((Nat.card_zpowers x').trans hx'ord).trans (pow_one 3).symm)
  obtain ⟨P, hP⟩ := IsPGroup.exists_le_sylow hZ3
  haveI : Finite (Sylow 3 Q) := Sylow.finite_of_finiteIndex P
  have hR0_3 : IsPGroup 3 ((P : Subgroup Q).map Q.subtype) := P.isPGroup'.map Q.subtype
  have hR0_le : (P : Subgroup Q).map Q.subtype ≤ centralizer (L : Set C) := by
    rw [← hQ]
    rintro c hc
    obtain ⟨z, _, rfl⟩ := Subgroup.mem_map.mp hc
    exact z.2
  have hcyc := p622Exit_cyclic e hrk hR0_3 hR0_le
  have hxR0 : x ∈ (P : Subgroup Q).map Q.subtype :=
    Subgroup.mem_map.mpr ⟨x', hP (Subgroup.mem_zpowers x'), hx'⟩
  have hcardR0 : Nat.card ((P : Subgroup Q).map Q.subtype) = 3 :=
    p622Exit_card_eq_three_of_cyclic hx3 hcube hcyc hR0_3 hxR0
  have hinj : Function.Injective Q.subtype := Subgroup.subtype_injective Q
  have hcardP : Nat.card (P : Subgroup Q) = 3 :=
    (Nat.card_congr (Subgroup.equivMapOfInjective (P : Subgroup Q) Q.subtype hinj).toEquiv).trans
      hcardR0
  have hPeq : (P : Subgroup Q) = zpowers x' :=
    (Subgroup.eq_of_le_of_card_ge hP (le_of_eq (by rw [hcardP, Nat.card_zpowers, hx'ord]))).symm
  have hcommP : ∀ h ∈ (P : Subgroup Q), ∀ g : Q, Commute h g := by
    intro h hh g
    rw [hPeq] at hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (hxc g).zpow_left k
  have hcentr : Subgroup.normalizer (P : Set Q) ≤ Subgroup.centralizer (P : Set Q) := by
    intro g _
    exact Subgroup.mem_centralizer_iff.mpr fun h hh => hcommP h hh g
  have hcomp := MonoidHom.ker_transferSylow_isComplement' P hcentr
  have hN0cop : Nat.Coprime 3 (Nat.card (MonoidHom.transferSylow P hcentr).ker) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      (MonoidHom.not_dvd_card_ker_transferSylow P hcentr)
  set N0 : Subgroup Q := (MonoidHom.transferSylow P hcentr).ker
  have hcrit : ∀ b : Q, ∀ m : ℕ, Nat.Coprime m 3 → b ^ m = 1 → b ∈ N0 := by
    intro b m hm hbm
    obtain ⟨⟨⟨a, haN⟩, ⟨p, hpP⟩⟩, hap⟩ := hcomp.2 b
    have hap' : a * p = b := hap
    have hcomm : Commute a p := (hcommP p hpP a).symm
    have h1 : a ^ m * p ^ m = 1 := by rw [← hcomm.mul_pow, hap', hbm]
    have hpN : p ^ m ∈ N0 := by
      rw [eq_inv_of_mul_eq_one_right h1]
      exact N0.inv_mem (N0.pow_mem haN m)
    have hpP' : p ^ m ∈ (P : Subgroup Q) := (P : Subgroup Q).pow_mem hpP m
    have hpm1 : p ^ m = 1 := by
      have hmem : p ^ m ∈ N0 ⊓ (P : Subgroup Q) := ⟨hpN, hpP'⟩
      rw [disjoint_iff.mp hcomp.disjoint] at hmem
      exact Subgroup.mem_bot.mp hmem
    have h3 : p ^ 3 = 1 := by
      have hpz : p ∈ zpowers x' := by
        rw [← hPeq]
        exact hpP
      have hdvd : orderOf p ∣ orderOf x' := orderOf_dvd_of_mem_zpowers hpz
      rw [hx'ord] at hdvd
      exact orderOf_dvd_iff_pow_eq_one.mp hdvd
    have hp1 : p = 1 := by
      have h := (pow_gcd_eq_one (a := p) (m := m) (n := 3)).mpr ⟨hpm1, h3⟩
      rwa [Nat.Coprime.gcd_eq_one hm, pow_one] at h
    rw [← hap', hp1, mul_one]
    exact haN
  have hNcard : Nat.card (N0.map Q.subtype) = Nat.card N0 :=
    (Nat.card_congr (Subgroup.equivMapOfInjective N0 Q.subtype hinj).toEquiv).symm
  have hN0cop' : Nat.Coprime (Nat.card N0) 3 := hN0cop.symm
  have hNn : (N0.map Q.subtype).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨a, haN, rfl⟩ := Subgroup.mem_map.mp hn
    have hgQ : g * (a : C) * g⁻¹ ∈ Q := hQn.conj_mem (a : C) a.2 g
    have hb : (⟨g * (a : C) * g⁻¹, hgQ⟩ : Q) ∈ N0 := by
      apply hcrit _ (Nat.card N0) hN0cop'
      have ha1 : a ^ Nat.card N0 = 1 := by
        have h2 : (⟨a, haN⟩ : N0) ^ Nat.card N0 = 1 :=
          orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_natCard _)
        have h3 := congrArg Subtype.val h2
        rw [Subgroup.coe_pow] at h3
        exact h3
      have ha1C : (a : C) ^ Nat.card N0 = 1 := by
        have h4 := congrArg Subtype.val ha1
        rw [Subgroup.coe_pow] at h4
        exact h4
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_mk, conj_pow, ha1C]
      simp
    exact Subgroup.mem_map.mpr ⟨_, hb, rfl⟩
  have hNbot : N0.map Q.subtype = ⊥ :=
    hno _ hNn (by rw [hNcard]; exact hN0cop)
  have hN0bot : ∀ a : Q, a ∈ N0 → a = 1 := by
    intro a ha
    have hmem : (a : C) ∈ N0.map Q.subtype := Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    rw [hNbot, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  rw [← hQ]
  apply le_antisymm
  · intro c hc
    obtain ⟨⟨⟨a, haN⟩, ⟨p, hpP⟩⟩, hap⟩ := hcomp.2 ⟨c, hc⟩
    have hap' : a * p = ⟨c, hc⟩ := hap
    have ha1 : a = 1 := hN0bot a haN
    have hpz : p ∈ zpowers x' := by
      rw [← hPeq]
      exact hpP
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hpz
    have hpc : (p : C) = c := by
      rw [ha1, one_mul] at hap'
      exact congrArg Subtype.val hap'
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨k, ?_⟩
    rw [← hx', ← Subgroup.coe_zpow, hk, hpc]
  · exact Subgroup.zpowers_le.mpr hxQ

private theorem p622Exit_conjNormal_eq_one_iff {L : Subgroup C} [L.Normal] (g : C) :
    (MulAut.conjNormal g : MulAut ↥L) = 1 ↔ g ∈ centralizer (L : Set C) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro hg h hh
    have h1 := congrArg Subtype.val (DFunLike.congr_fun hg ⟨h, hh⟩)
    have h2 : g * h * g⁻¹ = h := h1
    exact (mul_inv_eq_iff_eq_mul.1 h2).symm
  · intro hg
    apply MulEquiv.ext
    rintro ⟨h, hh⟩
    apply Subtype.ext
    show g * h * g⁻¹ = h
    rw [← hg h hh, mul_inv_cancel_right]

private theorem p622Exit_dvd_cases {n : ℕ} (h1 : 168 ∣ n) (h2 : n ∣ 336) :
    n = 168 ∨ n = 336 := by
  obtain ⟨k, rfl⟩ := h1
  have hle : 168 * k ≤ 336 := Nat.le_of_dvd (by norm_num) h2
  have hk : k ≤ 2 := by omega
  interval_cases k
  · norm_num at h2
  · norm_num
  · norm_num

theorem p622Exit_card {L : Subgroup C} [L.Normal] (e : ↥L ≃* GL32) {x : C} (hx3 : orderOf x = 3)
    (hcent : centralizer (L : Set C) = zpowers x) : Nat.card C = 504 ∨ Nat.card C = 1008 := by
  have hker : (MulAut.conjNormal : C →* MulAut ↥L).ker = centralizer (L : Set C) := by
    ext g
    rw [MonoidHom.mem_ker]
    exact p622Exit_conjNormal_eq_one_iff g
  have hk3 : Nat.card (MulAut.conjNormal : C →* MulAut ↥L).ker = 3 := by
    rw [hker, hcent, Nat.card_zpowers, hx3]
  have hC : Nat.card C = Nat.card (MulAut.conjNormal : C →* MulAut ↥L).ker *
      Nat.card (MulAut.conjNormal : C →* MulAut ↥L).range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  rw [hk3] at hC
  have hL : Nat.card ↥L = 168 :=
    (Nat.card_congr e.toEquiv).trans CFSG.LocalAnalysis.RankThreeTheoremC.L32Insp.card_GL
  have hA : Nat.card (MulAut ↥L) = 336 :=
    (Nat.card_congr (MulAut.congr e).toEquiv).trans p622Exit_card_mulAut
  have hdvd336 : Nat.card (MulAut.conjNormal : C →* MulAut ↥L).range ∣ 336 := by
    have h := Subgroup.card_subgroup_dvd_card (MulAut.conjNormal : C →* MulAut ↥L).range
    rwa [hA] at h
  have hψ : Function.Injective ((MulAut.conjNormal : C →* MulAut ↥L).comp L.subtype) := by
    rw [injective_iff_map_eq_one]
    intro l hl
    have hl' : (l : C) ∈ centralizer (L : Set C) := by
      rw [← hker, MonoidHom.mem_ker]
      exact hl
    have hmem : (l : C) ∈ centralizer (L : Set C) ⊓ L := Subgroup.mem_inf.2 ⟨hl', l.2⟩
    rw [p622Exit_inf_centralizer e, Subgroup.mem_bot] at hmem
    exact Subtype.ext (by simpa using hmem)
  have hle : ((MulAut.conjNormal : C →* MulAut ↥L).comp L.subtype).range ≤
      (MulAut.conjNormal : C →* MulAut ↥L).range := by
    intro y hy
    obtain ⟨l, rfl⟩ := MonoidHom.mem_range.1 hy
    exact MonoidHom.mem_range.2 ⟨(l : C), rfl⟩
  have hdvd168 : 168 ∣ Nat.card (MulAut.conjNormal : C →* MulAut ↥L).range := by
    have h1 : Nat.card ((MulAut.conjNormal : C →* MulAut ↥L).comp L.subtype).range = 168 := by
      rw [← hL]
      exact (Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv).symm
    have h2 := Subgroup.card_dvd_of_le hle
    rwa [h1] at h2
  rcases p622Exit_dvd_cases hdvd168 hdvd336 with h | h
  · left
    omega
  · right
    omega

theorem p622Exit_iso_504 {L : Subgroup C} [L.Normal] (e : ↥L ≃* GL32) {x : C}
    (hx : x ∈ Subgroup.center C) (hx3 : orderOf x = 3)
    (hcent : centralizer (L : Set C) = zpowers x) (hcard : Nat.card C = 504) :
    Nonempty (C ≃* Multiplicative (ZMod 3) × GL32) := by
  have hZ : Nat.card (zpowers x) = 3 := by rw [Nat.card_zpowers, hx3]
  have hcongr : ∀ {n m : ℕ}, n = m → Multiplicative (ZMod n) ≃* Multiplicative (ZMod m) := by
    intro n m h
    subst h
    exact MulEquiv.refl _
  obtain ⟨iso⟩ : Nonempty (Multiplicative (ZMod 3) ≃* zpowers x) :=
    ⟨(hcongr hZ).symm.trans (zmodCyclicMulEquiv inferInstance)⟩
  have hcardZ : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_congr iso.toEquiv, hZ]
  obtain ⟨emb, hembmem, hembinj⟩ : ∃ emb : Multiplicative (ZMod 3) →* C,
      (∀ a, emb a ∈ zpowers x) ∧ Function.Injective emb :=
    ⟨(zpowers x).subtype.comp iso.toMonoidHom, fun a => (iso a).2,
      Subtype.val_injective.comp iso.injective⟩
  have hzc : zpowers x ≤ Subgroup.center C := Subgroup.zpowers_le.mpr hx
  have hcomm : ∀ (a : Multiplicative (ZMod 3)) (l : ↥L), Commute (emb a) (l : C) := fun a l =>
    (Subgroup.mem_center_iff.mp (hzc (hembmem a)) (l : C)).symm
  obtain ⟨psi, hpsi⟩ : ∃ psi : Multiplicative (ZMod 3) × ↥L →* C,
      ∀ (a : Multiplicative (ZMod 3)) (l : ↥L), psi (a, l) = emb a * (l : C) :=
    ⟨MonoidHom.noncommCoprod emb L.subtype hcomm, fun a l => rfl⟩
  have hinf : zpowers x ⊓ L = ⊥ := by
    have h := p622Exit_inf_centralizer e
    rwa [hcent] at h
  have hinj : Function.Injective psi := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, l⟩ h
    rw [hpsi] at h
    have h1 : emb a = (l : C)⁻¹ := eq_inv_of_mul_eq_one_left h
    have hmem : emb a ∈ zpowers x ⊓ L :=
      Subgroup.mem_inf.mpr ⟨hembmem a, by rw [h1]; exact L.inv_mem l.2⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    have ha : a = 1 := hembinj (by rw [hmem, map_one])
    have hl : (l : C) = 1 := by
      rw [hmem, one_mul] at h
      exact h
    have hl' : l = 1 := Subtype.ext hl
    subst ha
    subst hl'
    rfl
  have hL : Nat.card ↥L = 168 := by
    rw [Nat.card_congr e.toEquiv, L32Insp.card_GL]
  have hc : Nat.card C ≤ Nat.card (Multiplicative (ZMod 3) × ↥L) := by
    rw [Nat.card_prod, hcardZ, hL]
    exact hcard.le
  have hbij : Function.Bijective psi := Function.Injective.bijective_of_nat_card_le hinj hc
  exact ⟨(MulEquiv.ofBijective psi hbij).symm.trans (MulEquiv.prodCongr (MulEquiv.refl _) e)⟩

private noncomputable def p622_zmod_equiv {G : Type} [Group G] [IsCyclic G] {n : ℕ}
    (hn : Nat.card G = n) : Multiplicative (ZMod n) ≃* G := by
  subst hn
  exact zmodCyclicMulEquiv inferInstance

private lemma p622_pow_eq_one_of_mem_zpowers {G : Type} [Group G] {z y : G} {n : ℕ}
    (hz : z ^ n = 1) (hy : y ∈ Subgroup.zpowers z) : y ^ n = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]

private lemma p622_exists_N2 {G : Type} [Group G] [Finite G] (L : Subgroup G) [L.Normal]
    (hLi : L.index = 6) (hcard : Nat.card G = 1008) :
    ∃ N : Subgroup G, Nat.card N = 336 ∧ ∀ g ∈ N, g ^ 3 = 1 → g ∈ L := by
  haveI : Fintype (G ⧸ L) := Fintype.ofFinite _
  have hQ : Nat.card (G ⧸ L) = 6 := hLi
  have hdvd : 2 ∣ Fintype.card (G ⧸ L) := by
    rw [← Nat.card_eq_fintype_card, hQ]
    norm_num
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card 2 hdvd
  have hs2 : s ^ 2 = 1 := by
    have := pow_orderOf_eq_one s
    rwa [hs] at this
  have hsidx : (Subgroup.zpowers s).index = 3 := by
    have h := Subgroup.card_mul_index (H := Subgroup.zpowers s)
    rw [Nat.card_zpowers, hs, hQ] at h
    omega
  refine ⟨(Subgroup.zpowers s).comap (QuotientGroup.mk' L), ?_, ?_⟩
  · have h1 := Subgroup.index_comap_of_surjective (Subgroup.zpowers s)
      (QuotientGroup.mk'_surjective L)
    have h2 := Subgroup.card_mul_index (H := (Subgroup.zpowers s).comap (QuotientGroup.mk' L))
    rw [h1, hsidx, hcard] at h2
    omega
  · intro g hg hg3
    have hπ : QuotientGroup.mk' L g ∈ Subgroup.zpowers s := Subgroup.mem_comap.mp hg
    have h2 : QuotientGroup.mk' L g ^ 2 = 1 := p622_pow_eq_one_of_mem_zpowers hs2 hπ
    have h3 : QuotientGroup.mk' L g ^ 3 = 1 := by
      rw [← map_pow, hg3, map_one]
    have h4 : QuotientGroup.mk' L g ^ Nat.gcd 3 2 = 1 := pow_gcd_eq_one.mpr ⟨h3, h2⟩
    have h5 : QuotientGroup.mk' L g = 1 := by
      simpa using h4
    exact (QuotientGroup.eq_one_iff g).mp h5

private lemma p622_split {G : Type} [Group G] [Finite G] {L : Subgroup G} [L.Normal]
    {z : G} (hz : z ∈ Subgroup.center G) (hz3 : orderOf z = 3)
    (hzL : Subgroup.zpowers z ⊓ L = ⊥)
    (hcent : Subgroup.centralizer (L : Set G) = Subgroup.zpowers z)
    (hcard : Nat.card G = 1008) (hA : Nat.card (MulAut L) = 336)
    {N : Subgroup G} (hNcard : Nat.card N = 336) (hN : ∀ g ∈ N, g ^ 3 = 1 → g ∈ L) :
    Nonempty (G ≃* Multiplicative (ZMod 3) × MulAut L) := by
  have hcyc : Nat.card (Subgroup.zpowers z) = 3 := by
    rw [Nat.card_zpowers, hz3]
  let E : Multiplicative (ZMod 3) ≃* ↥(Subgroup.zpowers z) := p622_zmod_equiv hcyc
  let ι : Multiplicative (ZMod 3) →* G := (Subgroup.zpowers z).subtype.comp E.toMonoidHom
  have hιmem : ∀ a, ι a ∈ Subgroup.zpowers z := fun a => (E a).2
  have hιinj : Function.Injective ι := by
    intro a b h
    exact E.injective (Subtype.ext h)
  have hz3' : z ^ 3 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz3] at this
  have hcomm : ∀ (a : Multiplicative (ZMod 3)) (n : N), Commute (ι a) (N.subtype n) := by
    intro a n
    have hc : ι a ∈ Subgroup.center G := (Subgroup.zpowers_le.mpr hz) (hιmem a)
    exact ((Subgroup.mem_center_iff.mp hc) (n : G)).symm
  let Ψ : Multiplicative (ZMod 3) × N →* G := ι.noncommCoprod N.subtype hcomm
  have hΨinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, n⟩ h
    have h' : ι a * (n : G) = 1 := h
    have hy : ι a = (n : G)⁻¹ := eq_inv_of_mul_eq_one_left h'
    have hyN : ι a ∈ N := by
      rw [hy]
      exact N.inv_mem n.2
    have hyL : ι a ∈ L := hN (ι a) hyN (p622_pow_eq_one_of_mem_zpowers hz3' (hιmem a))
    have hy1 : ι a = 1 := by
      have hmem : ι a ∈ Subgroup.zpowers z ⊓ L := ⟨hιmem a, hyL⟩
      rw [hzL, Subgroup.mem_bot] at hmem
      exact hmem
    have ha : a = 1 := hιinj (by rw [hy1, map_one])
    have hn : (n : G) = 1 := by
      rw [hy1] at hy
      exact inv_eq_one.mp hy.symm
    exact Prod.ext ha (Subtype.ext hn)
  have hM : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_congr E.toEquiv, hcyc]
  have hΨbij : Function.Bijective Ψ := by
    rw [Nat.bijective_iff_injective_and_card]
    refine ⟨hΨinj, ?_⟩
    rw [Nat.card_prod, hM, hNcard, hcard]
  let φ2 : N →* MulAut L := (MulAut.conjNormal (H := L)).comp N.subtype
  have hφinj : Function.Injective φ2 := by
    rw [injective_iff_map_eq_one]
    rintro ⟨n, hnN⟩ h
    have hconj : MulAut.conjNormal (H := L) n = 1 := h
    have hc : ∀ l ∈ (L : Set G), l * n = n * l := by
      intro l hl
      have hl' : l ∈ L := hl
      have h1 : ((MulAut.conjNormal (H := L) n) ⟨l, hl'⟩ : G) = l :=
        congrArg (fun f : MulAut L => ((f ⟨l, hl'⟩ : L) : G)) hconj
      rw [MulAut.conjNormal_apply] at h1
      exact (mul_inv_eq_iff_eq_mul.mp h1).symm
    have hnc : n ∈ Subgroup.centralizer (L : Set G) :=
      Subgroup.mem_centralizer_iff.mpr (fun l hl => hc l hl)
    rw [hcent] at hnc
    have hn3 : n ^ 3 = 1 := p622_pow_eq_one_of_mem_zpowers hz3' hnc
    have hmem : n ∈ Subgroup.zpowers z ⊓ L := ⟨hnc, hN n hnN hn3⟩
    rw [hzL, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hφbij : Function.Bijective φ2 := by
    haveI : Finite (MulAut L) := Nat.finite_of_card_ne_zero (by rw [hA]; norm_num)
    rw [Nat.bijective_iff_injective_and_card]
    exact ⟨hφinj, by rw [hNcard, hA]⟩
  exact ⟨(MulEquiv.ofBijective Ψ hΨbij).symm.trans
    (MulEquiv.prodCongr (MulEquiv.refl _) (MulEquiv.ofBijective φ2 hφbij))⟩

theorem p622Exit_iso_1008 {L : Subgroup C} [L.Normal] (e : ↥L ≃* GL32) {x : C}
    (hx : x ∈ Subgroup.center C) (hx3 : orderOf x = 3)
    (hcent : centralizer (L : Set C) = zpowers x) (hcard : Nat.card C = 1008) :
    Nonempty (C ≃* Multiplicative (ZMod 3) × MulAut GL32) := by
  have hzL : zpowers x ⊓ L = ⊥ := by
    rw [← hcent]
    exact p622Exit_inf_centralizer e
  have hL : Nat.card L = 168 := by
    rw [Nat.card_congr e.toEquiv, card_GL]
  have hLi : L.index = 6 := by
    have h := Subgroup.card_mul_index (H := L)
    rw [hL, hcard] at h
    omega
  have hA : Nat.card (MulAut L) = 336 := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv]
    exact p622Exit_card_mulAut
  obtain ⟨N, hNcard, hN⟩ := p622_exists_N2 L hLi hcard
  obtain ⟨f⟩ := p622_split hx hx3 hzL hcent hcard hA hNcard hN
  exact ⟨f.trans (MulEquiv.prodCongr (MulEquiv.refl _) (MulAut.congr e))⟩

theorem p622Exit_structure {L : Subgroup C} [L.Normal] (e : ↥L ≃* PSL(3, ZMod 2)) {x : C}
    (hx : x ∈ Subgroup.center C) (hx3 : orderOf x = 3)
    (hno : ∀ N : Subgroup C, N.Normal → Nat.Coprime 3 (Nat.card N) → N = ⊥)
    (hrk : ∀ E : Subgroup C, IsElemAbelian 3 E → Nat.card E ≤ 9)
    (hcube : ∀ y : C, (∃ k : ℕ, y ^ 3 ^ k = 1) → y ^ 3 ≠ x) :
    Nonempty (C ≃* Multiplicative (ZMod 3) × PSL(3, ZMod 2)) ∨
      Nonempty (C ≃* Multiplicative (ZMod 3) × MulAut PSL(3, ZMod 2)) := by
  have e' : ↥L ≃* GL32 := e.trans pslEquiv
  have hcent := p622Exit_centralizer_eq e' hx hx3 hno hrk hcube
  rcases p622Exit_card e' hx3 hcent with h | h
  · obtain ⟨f⟩ := p622Exit_iso_504 e' hx hx3 hcent h
    exact Or.inl ⟨f.trans (MulEquiv.prodCongr (MulEquiv.refl _) pslEquiv.symm)⟩
  · obtain ⟨f⟩ := p622Exit_iso_1008 e' hx hx3 hcent h
    exact Or.inr ⟨f.trans (MulEquiv.prodCongr (MulEquiv.refl _) (MulAut.congr pslEquiv).symm)⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
