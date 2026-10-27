module

public import CFSG.GH74.Generic.BProg.B3.LocBalJ1
public import CFSG.GH74.Generic.BProg.B2.NoSD
public import CFSG.GH74.Generic.BProg.B2.FixFourS45
public import CFSG.GH74.Generic.BProg.B1.PilotS4Facts
public import CFSG.LieType.Ree.SuzukiReeOuterTwoPart
public import CFSG.GH74.GLS.C3.Layer1.St1PumpCalc

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3
  CFSG.GH74.Generic.BProg CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalCores Subgroup

section H1a

variable {G : Type} [Group G] [Finite G] {x : G} {K A : Subgroup G} {a : G} {D J : Subgroup G}

theorem Ctx21.pRank_cxk_le_one (hNo : B2.NoJPrimeNonSD) (hc : Ctx21 G x K A a D J)
    (hP : QShape1 (↥K ⧸ pPrimeCore 2 ↥K) ∨ B1.QShape3W (↥K ⧸ pPrimeCore 2 ↥K) ∨
      QShape4 (↥K ⧸ pPrimeCore 2 ↥K) ∨ QShape5 (↥K ⧸ pPrimeCore 2 ↥K)) :
    pRank 2 ↥(CxK x K) ≤ 1 := by
  by_contra h
  have h1 : 1 < pRank 2 ↥(CxK x K) := not_le.mp h
  have hJ : IsJ2 x K := hc.circ.1
  rcases hP with hQ | hQ | hQ | hQ
  · exact hNo.1 G hc.hyp hc.noAlt x K hJ h1 hQ
  · exact hNo.2.1 G hc.hyp hc.noAlt x K hJ h1 hQ
  · exact hNo.2.2.1 G hc.hyp hc.noAlt x K hJ h1 hQ
  · exact hNo.2.2.2 G hc.hyp hc.noAlt x K hJ h1 hQ

end H1a

namespace RankC

structure E8Data (L : Type) [Group L] : Prop where
  center : ∀ z : L, (∀ g : L, g * z = z * g) → z = 1
  cert : RankCertified L 2
  abelian : ∀ P : Subgroup L, IsPGroup 2 ↥P → IsMulCommutative ↥P
  out : ∀ (φ : MulAut L) (k : ℕ), φ ^ (2 ^ k) = 1 → φ ∈ (MulAut.conj : L →* MulAut L).range

theorem isMulCommutative_of_closure_card_le_one {Q : Type} [Group Q] (s : Finset Q)
    (hs : s.card ≤ 1) (hcl : Subgroup.closure (s : Set Q) = ⊤) : IsMulCommutative Q := by
  by_cases hne : s.Nonempty
  · obtain ⟨a, ha⟩ := hne
    have hsa : (s : Set Q) = {a} := by
      ext b
      simp only [Finset.mem_coe, Set.mem_singleton_iff]
      exact ⟨fun hb => Finset.card_le_one.mp hs b hb a ha, fun hb => hb ▸ ha⟩
    rw [hsa, ← Subgroup.zpowers_eq_closure] at hcl
    refine ⟨⟨fun g h => ?_⟩⟩
    have hg : g ∈ Subgroup.zpowers a := by rw [hcl]; trivial
    have hh : h ∈ Subgroup.zpowers a := by rw [hcl]; trivial
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (Commute.zpow_zpow_self a m n).eq
  · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hs0] at hcl
    refine ⟨⟨fun g h => ?_⟩⟩
    have hg : g ∈ Subgroup.closure (((∅ : Finset Q) : Set Q)) := by rw [hcl]; trivial
    have hh : h ∈ Subgroup.closure (((∅ : Finset Q) : Set Q)) := by rw [hcl]; trivial
    simp only [Finset.coe_empty, Subgroup.closure_empty, Subgroup.mem_bot] at hg hh
    rw [hg, hh]

section Abstract

variable {X : Type} [Group X] [Finite X]

theorem isMulCommutative_of_le_centralizer (hX : Gen4 X) {L : Subgroup X} (hd : E8Data ↥L)
    {Q : Subgroup X} (hQ : IsPGroup 2 ↥Q) (hQL : Q ≤ centralizer (L : Set X)) :
    IsMulCommutative ↥Q := by
  by_contra hnc
  have hnot : ¬ SectionalTwoRankLE ↥Q 1 := by
    intro h
    obtain ⟨s, hs, hcl⟩ := h ⊤
      (hQ.of_injective (⊤ : Subgroup ↥Q).subtype (⊤ : Subgroup ↥Q).subtype_injective)
    exact hnc (isMulCommutative_of_closure_card_le_one s hs hcl)
  have hcert : RankCertified ↥Q 1 := rankCertified_of_not_sectionalTwoRankLE hnot
  have h4 : RankCertified X (2 + 1 + 1) :=
    B1.rankCertified_of_commuting_range hd.cert hcert Q.subtype (fun k hk y => ?_) (fun y hy => ?_)
  · exact h4.not_gen4 (by norm_num) hX
  · exact mem_centralizer_iff.mp (hQL y.2) k hk
  · have hcen : (⟨(y : X), hy⟩ : ↥L) = 1 := by
      refine hd.center _ (fun g => Subtype.ext ?_)
      exact mem_centralizer_iff.mp (hQL y.2) g g.2
    have h1 : (y : X) = 1 := congrArg Subtype.val hcen
    exact Subtype.ext h1

theorem normal_of_gen4 (hX : Gen4 X) {L : Subgroup X} (hL : IsComponent L) (hd : E8Data ↥L) :
    L.Normal := by
  refine ⟨fun n hn g => ?_⟩
  by_contra hng
  set Lc : Subgroup X := L.map (MulAut.conj g).toMonoidHom with hLc
  have hLcc : IsComponent Lc := isComponent_map_mulEquiv (MulAut.conj g) hL
  have hne : L ≠ Lc := by
    intro h
    exact hng (by rw [h]; exact ⟨n, hn, rfl⟩)
  have hcomm : ⁅L, Lc⁆ = ⊥ := (distinct_components_commute hL hLcc).resolve_left hne
  have hLle : L ≤ centralizer (Lc : Set X) := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hcert' : RankCertified ↥Lc 2 :=
    hd.cert.of_mulEquiv
      (L.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)
  have h5 : RankCertified X (2 + 2 + 1) :=
    B1.rankCertified_of_commuting_range hd.cert hcert' Lc.subtype (fun k hk y => ?_)
      (fun y hy => ?_)
  · exact h5.not_gen4 (by norm_num) hX
  · exact (mem_centralizer_iff.mp (hLle hk) y y.2).symm
  · have hcen : (⟨(y : X), hy⟩ : ↥L) = 1 := by
      refine hd.center _ (fun l => Subtype.ext ?_)
      exact (mem_centralizer_iff.mp (hLle l.2) y y.2).symm
    have h1 : (y : X) = 1 := congrArg Subtype.val hcen
    exact Subtype.ext h1

omit [Finite X] in
theorem exists_mul_of_two_element {L : Subgroup X} [L.Normal] (hd : E8Data ↥L) {r : X} {k : ℕ}
    (hr : r ^ (2 ^ k) = 1) : ∃ l ∈ L, ∃ y ∈ centralizer (L : Set X), r = l * y := by
  have hφ : (MulAut.conjNormal r : MulAut ↥L) ^ (2 ^ k) = 1 := by
    rw [← map_pow, hr, map_one]
  obtain ⟨l, hl⟩ := hd.out _ k hφ
  refine ⟨l, l.2, (l : X)⁻¹ * r, ?_, by group⟩
  rw [mem_centralizer_iff]
  intro m hm
  have h1 := congrArg (fun φ : MulAut ↥L => (φ ⟨m, hm⟩ : X)) hl
  simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h1
  have h2 : (l : X)⁻¹ * r * m * ((l : X)⁻¹ * r)⁻¹ = m := by
    calc (l : X)⁻¹ * r * m * ((l : X)⁻¹ * r)⁻¹ = (l : X)⁻¹ * (r * m * r⁻¹) * l := by group
      _ = (l : X)⁻¹ * (l * m * (l : X)⁻¹) * l := by rw [h1]
      _ = m := by group
  exact (mul_inv_eq_iff_eq_mul.mp h2).symm

theorem isMulCommutative_of_isPGroup (hX : Gen4 X) {L : Subgroup X} (hL : IsComponent L)
    (hd : E8Data ↥L) {R : Subgroup X} (hR : IsPGroup 2 ↥R) : IsMulCommutative ↥R := by
  have hN : L.Normal := normal_of_gen4 hX hL hd
  set Y : Subgroup X := centralizer (L : Set X) with hY
  have hLY : ∀ (l : ↥L) (y : ↥Y), Commute (l : X) (y : X) := fun l y =>
    mem_centralizer_iff.mp y.2 l l.2
  have hdisj : ∀ g : X, g ∈ L → g ∈ Y → g = 1 := fun g hgL hgY => by
    have h := hd.center ⟨g, hgL⟩ (fun h => Subtype.ext (mem_centralizer_iff.mp hgY h h.2))
    exact congrArg Subtype.val h
  let φ : ↥L × ↥Y →* X := MonoidHom.noncommCoprod L.subtype Y.subtype hLY
  have hφ : ∀ p : ↥L × ↥Y, φ p = (p.1 : X) * (p.2 : X) := fun p => rfl
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨l, y⟩ h
    have h1 : (l : X) * (y : X) = 1 := h
    have hyL : (y : X) ∈ L := by
      rw [eq_inv_of_mul_eq_one_right h1]
      exact L.inv_mem l.2
    have hy1 : (y : X) = 1 := hdisj _ hyL y.2
    have hl1 : (l : X) = 1 := by rw [hy1, mul_one] at h1; exact h1
    exact Prod.ext (Subtype.ext hl1) (Subtype.ext hy1)
  set R₀ : Subgroup (↥L × ↥Y) := R.comap φ with hR₀
  have hR₀p : IsPGroup 2 ↥R₀ := hR.comap_of_injective φ hφinj
  set π₁ : Subgroup ↥L := R₀.map (MonoidHom.fst ↥L ↥Y) with hπ₁
  have hπ₁c : IsMulCommutative ↥π₁ := hd.abelian π₁ (hR₀p.map _)
  set Q : Subgroup X := (R₀.map (MonoidHom.snd ↥L ↥Y)).map Y.subtype with hQ
  have hQp : IsPGroup 2 ↥Q := (hR₀p.map (MonoidHom.snd ↥L ↥Y)).map Y.subtype
  have hQL : Q ≤ centralizer (L : Set X) := by
    rintro _ ⟨y, _, rfl⟩
    exact y.2
  have hQc : IsMulCommutative ↥Q := isMulCommutative_of_le_centralizer hX hd hQp hQL
  have hdec : ∀ r : ↥R, ∃ (l : ↥L) (y : ↥Y), (r : X) = (l : X) * (y : X) ∧ (l, y) ∈ R₀ := by
    intro r
    obtain ⟨k, hk⟩ := hR r
    have hrk : (r : X) ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    obtain ⟨l, hl, y, hy, hry⟩ := exists_mul_of_two_element hd hrk
    refine ⟨⟨l, hl⟩, ⟨y, hy⟩, hry, ?_⟩
    show φ (⟨l, hl⟩, ⟨y, hy⟩) ∈ R
    rw [hφ]
    show l * y ∈ R
    rw [← hry]
    exact r.2
  refine ⟨⟨fun r r' => ?_⟩⟩
  obtain ⟨l, y, hry, hp⟩ := hdec r
  obtain ⟨l', y', hry', hp'⟩ := hdec r'
  have hll : (l : X) * (l' : X) = (l' : X) * (l : X) := by
    have := hπ₁c.is_comm.comm ⟨l, ⟨(l, y), hp, rfl⟩⟩ ⟨l', ⟨(l', y'), hp', rfl⟩⟩
    exact congrArg (fun z : ↥π₁ => ((z : ↥L) : X)) this
  have hyy : (y : X) * (y' : X) = (y' : X) * (y : X) := by
    have := hQc.is_comm.comm ⟨(y : X), ⟨y, ⟨(l, y), hp, rfl⟩, rfl⟩⟩
      ⟨(y' : X), ⟨y', ⟨(l', y'), hp', rfl⟩, rfl⟩⟩
    exact congrArg (fun z : ↥Q => (z : X)) this
  have hyl' : (y : X) * (l' : X) = (l' : X) * (y : X) := (hLY l' y).eq.symm
  apply Subtype.ext
  show (r : X) * (r' : X) = (r' : X) * (r : X)
  rw [hry, hry']
  calc (l : X) * y * ((l' : X) * y')
      = (l : X) * ((y : X) * (l' : X)) * y' := by simp only [mul_assoc]
    _ = (l : X) * ((l' : X) * y) * y' := by rw [hyl']
    _ = ((l : X) * l') * ((y : X) * y') := by simp only [mul_assoc]
    _ = ((l' : X) * l) * ((y' : X) * y) := by rw [hll, hyy]
    _ = (l' : X) * ((l : X) * y') * y := by simp only [mul_assoc]
    _ = (l' : X) * ((y' : X) * l) * y := by rw [(hLY l y').eq]
    _ = (l' : X) * y' * ((l : X) * y) := by simp only [mul_assoc]

end Abstract

theorem isMulCommutative_of_map {C Y : Type} [Group C] [Group Y] (π : C →* Y)
    (hker : ∀ n : C, π n = 1 → Odd (orderOf n)) {P : Subgroup C} (hP : IsPGroup 2 ↥P)
    (hc : IsMulCommutative ↥(P.map π)) : IsMulCommutative ↥P := by
  refine ⟨⟨fun u v => ?_⟩⟩
  have hc1 := hc.is_comm.comm ⟨π u, u, u.2, rfl⟩ ⟨π v, v, v.2, rfl⟩
  have h2 : π u * π v = π v * π u := congrArg (fun z : ↥(P.map π) => (z : Y)) hc1
  have h1 : π ((u : C) * v) = π ((v : C) * u) := by rw [map_mul, map_mul]; exact h2
  have hg1 : π ((u : C) * v * ((v : C) * u)⁻¹) = 1 := by
    rw [map_mul, map_inv, h1, mul_inv_cancel]
  have hgP : (u : C) * v * ((v : C) * u)⁻¹ ∈ P :=
    P.mul_mem (P.mul_mem u.2 v.2) (P.inv_mem (P.mul_mem v.2 u.2))
  obtain ⟨k, hk⟩ := hP ⟨_, hgP⟩
  have hk' : ((u : C) * v * ((v : C) * u)⁻¹) ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hord : orderOf ((u : C) * v * ((v : C) * u)⁻¹) = 1 :=
    Nat.Coprime.eq_one_of_dvd ((Nat.coprime_two_left.mpr (hker _ hg1)).pow_left k).symm
      (orderOf_dvd_of_pow_eq_one hk')
  exact Subtype.ext (mul_inv_eq_one.mp (orderOf_eq_one_iff.mp hord))

theorem E8Data.of_hasE8Sylow {L : Type} [Group L] [Finite L] (hs : B2.FixFourS45.HasE8Sylow L)
    (hcen : ∀ z : L, (∀ g : L, g * z = z * g) → z = 1)
    (hout : ∀ (φ : MulAut L) (k : ℕ), φ ^ (2 ^ k) = 1 → φ ∈ (MulAut.conj : L →* MulAut L).range) :
    E8Data L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hcen, ?_, ?_, hout⟩
  · obtain ⟨P, hPel, hP8⟩ := hs
    exact B1.rankCertified_of_isElementaryAbelian (P : Subgroup L) hPel (by rw [hP8]; norm_num)
  · intro P hP
    obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
    obtain ⟨hQel, -⟩ := hs.all Q
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    have := hQel.toIsMulCommutative.is_comm.comm ⟨a, hPQ a.2⟩ ⟨b, hPQ b.2⟩
    exact congrArg (fun z : ↥(Q : Subgroup L) => (z : L)) this

section Ree


theorem ree_aut_inner_of_two_power {T : Type} [Group T] [Finite T] (h : QShape4 T) {φ : MulAut T}
    {k : ℕ} (hφ : φ ^ (2 ^ k) = 1) : φ ∈ (MulAut.conj : T →* MulAut T).range := by
  obtain ⟨f, hf⟩ := h
  have hout := (CFSG.LieType.Ree.SuzukiReeOuterTwoPart.small_Ree_case
    (B1.PilotS4.reeTitsModel_of_lieModel hf)).1
  have : Finite (MulAut T) := MulEquiv.finite_left
  have hpos : 0 < Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer T) :=
    Nat.card_pos
  have hodd : ¬ 2 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer T) := by
    intro h2
    have h3 := Nat.Prime.factorization_pos_of_dvd Nat.prime_two hpos.ne' h2
    exact (Nat.ne_of_gt (Nat.one_lt_two_pow h3.ne')) hout
  have hx : (QuotientGroup.mk φ :
      CFSG.ComponentClassification.OuterAutomorphisms.Outer T) ^ (2 ^ k) = 1 := by
    rw [← QuotientGroup.mk_pow, hφ, QuotientGroup.mk_one]
  have hx1 : (QuotientGroup.mk φ :
      CFSG.ComponentClassification.OuterAutomorphisms.Outer T) = 1 := by
    by_contra hne
    obtain ⟨j, -, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hx)
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hne (orderOf_eq_one_iff.mp (by simpa using hj'))
    have h2 : 2 ∣ orderOf (QuotientGroup.mk φ :
        CFSG.ComponentClassification.OuterAutomorphisms.Outer T) := by
      rw [hj']
      exact dvd_pow_self 2 hj0
    exact hodd (h2.trans (orderOf_dvd_natCard _))
  obtain ⟨g, hg⟩ := (QuotientGroup.eq_one_iff φ).1 hx1
  exact ⟨g, hg⟩

theorem e8Data_of_qShape4 {L : Type} [Group L] [Finite L] (h : QShape4 L) : E8Data L :=
  E8Data.of_hasE8Sylow (B2.FixFourS45.shape4_data h).1 (B1.PilotS4.center_of_qShape4 h)
    (fun _ _ hφ => ree_aut_inner_of_two_power h hφ)

end Ree

section J1

open CFSG.Open CFSG.Walter CFSG.Walter.J1Props

theorem e8Data_of_qShape5 {L : Type} [Group L] [Finite L]
    (hq : IsQuasisimple L) (h : QShape5 L) : E8Data L := by
  obtain ⟨e0⟩ := h
  let e : L ≃* walterJ1 := e0.trans walterJ1EquivNative.symm
  have hJ : IsSimpleGroup walterJ1 := J1_simple
  have hsimple : IsSimpleGroup L := e.isSimpleGroup
  have hbot : center L = ⊥ := B1.center_eq_bot_of_simple_of_quasisimple hsimple hq
  refine E8Data.of_hasE8Sylow (B2.FixFourS45.shape5_data (T := L) ⟨e0⟩).1 (fun z hz => ?_)
    (fun φ _ _ => ?_)
  · have hzc : z ∈ center L := Subgroup.mem_center_iff.mpr hz
    rw [hbot, Subgroup.mem_bot] at hzc
    exact hzc
  · obtain ⟨g, hg⟩ := LocBalJ1.forall_mulAut_inner_of_equiv e φ
    exact ⟨g, hg.symm⟩

end J1

end RankC

section H1b

variable {G : Type} [Group G] [Finite G] {x : G} {K A : Subgroup G} {a : G} {D J : Subgroup G}


theorem Ctx21.sylow_cx_abelian_of_gen4 (hc : Ctx21 G x K A a D J)
    (hP : QShape4 (↥K ⧸ pPrimeCore 2 ↥K) ∨ QShape5 (↥K ⧸ pPrimeCore 2 ↥K)) :
    ∀ P : Sylow 2 ↥(centralizer ({x} : Set G)),
      IsMulCommutative ↥(P : Subgroup ↥(centralizer ({x} : Set G))) := by
  intro P
  have hILo : IsILo 2 x K := hc.circ.1.1.1
  have hKpc : IsPCompIn 2 (centralizer ({x} : Set G)) K := hILo.2.2
  have hgen : Gen4 (CentralizerBar x) := gen4_centralizerBar hc.hyp.gen4 x
  have hLc : IsComponent (imgBar x K) := C3.Layer1.PumpCalc.isComponent_bar hKpc
  obtain ⟨eMK⟩ := C3.Layer1.PumpCalc.kBar_equiv_bar hKpc
  have eMK' : (↥K ⧸ pPrimeCore 2 ↥K) ≃* ↥(imgBar x K) := eMK
  have hd : RankC.E8Data ↥(imgBar x K) := by
    rcases hP with h4 | h5
    · obtain ⟨f, hf⟩ := h4
      exact RankC.e8Data_of_qShape4 ⟨f, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eMK' hf⟩
    · obtain ⟨e'⟩ := h5
      exact RankC.e8Data_of_qShape5 hLc.1 ⟨eMK'.symm.trans e'⟩
  have hab : ∀ R : Subgroup (CentralizerBar x), IsPGroup 2 ↥R → IsMulCommutative ↥R :=
    fun R hR => RankC.isMulCommutative_of_isPGroup hgen hLc hd hR
  have hPbar : IsPGroup 2 ↥((P : Subgroup ↥(centralizer ({x} : Set G))).map (proj x)) :=
    P.isPGroup'.map (proj x)
  exact RankC.isMulCommutative_of_map (proj x) (fun n hn => proj_odd x n hn) P.isPGroup'
    (hab _ hPbar)

theorem Ctx21.sylow_cx_abelian (hc : Ctx21 G x K A a D J)
    (hP : QShape4 (↥K ⧸ pPrimeCore 2 ↥K) ∨ QShape5 (↥K ⧸ pPrimeCore 2 ↥K))
    (hC : pRank 2 ↥(CxK x K) ≤ 1) :
    ∀ P : Sylow 2 ↥(centralizer ({x} : Set G)),
      IsMulCommutative ↥(P : Subgroup ↥(centralizer ({x} : Set G))) := by
  have _hC := hC
  exact Ctx21.sylow_cx_abelian_of_gen4 hc hP

end H1b

end CFSG.GH74.Generic.BProg.B3
