module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P85gLiftCfg
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P85eNo
public import CFSG.GH74.GLS.Stage2.Final.ClassicalF
public import CFSG.RankThree.Coprime.InvolutionFixedRankBound
public import CFSG.RankThree.PartOne.KE.A1Group
public import CFSG.RankThree.PartOne.S10.PlaneTwoGroupLemmas

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P85

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

theorem mul_comm_of_card_le_four {Q : Type} [Group Q] [Finite Q] (h : Nat.card Q ≤ 4) (a b : Q) :
    a * b = b * a := by
  have hpos : 0 < Nat.card Q := Nat.card_pos
  by_cases h3 : Nat.card Q ≤ 3
  · exact CFSG.RankThree.PartOne.KE.mul_comm_of_card_le_three hpos h3 a b
  · have h4 : Nat.card Q = 2 ^ 2 := by omega
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := IsPGroup.isMulCommutative_of_card_eq_prime_sq h4
    exact this.is_comm.comm a b

theorem comm_mem_LC {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} (hSC : S ≤ Cen z)
    (hidx : (RC S z).relIndex S ≤ 4) {a b : G} (ha : a ∈ S) (hb : b ∈ S) :
    a * b * a⁻¹ * b⁻¹ ∈ LC z := by
  classical
  set N : Subgroup ↥S := (LC z).subgroupOf S with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn s => ?_⟩
    have h1 := Stage1.Thm6.Prod.LC_normal z
    have hn' : (⟨(n : G), hSC n.2⟩ : ↥(Cen z)) ∈ (LC z).subgroupOf (Cen z) := hn
    have := h1.conj_mem _ hn' ⟨(s : G), hSC s.2⟩
    exact this
  have hRN : (RC S z).subgroupOf S = N := by
    ext s
    simp only [Subgroup.mem_subgroupOf, RC, Subgroup.mem_inf, hN]
    exact ⟨fun h => h.2, fun h => ⟨s.2, h⟩⟩
  have hcard : Nat.card (↥S ⧸ N) ≤ 4 := by
    have : Nat.card (↥S ⧸ N) = (RC S z).relIndex S := by
      rw [Subgroup.relIndex, hRN]; rfl
    omega
  have hcomm := mul_comm_of_card_le_four hcard
  have h1 : (QuotientGroup.mk' N) ⁅(⟨a, ha⟩ : ↥S), ⟨b, hb⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm _ _
  have h2 := (QuotientGroup.eq_one_iff _).mp h1
  have h3 : ((⁅(⟨a, ha⟩ : ↥S), ⟨b, hb⟩⁆ : ↥S) : G) ∈ LC z := h2
  simpa [commutatorElement_def] using h3

theorem no_sylCfg_rank {G : Type} [Group G] [Finite G] (h3 : pRank 2 G = 3) {P E F : Subgroup G}
    (hcfg : SylCfg id P E F) : False := by
  have hcomm : IsMulCommutative ↥F := ⟨⟨fun a b => Subtype.ext (hcfg.F_comm a a.2 b b.2)⟩⟩
  have hF : CFSG.IsElementaryAbelian 2 ↥F :=
    { toIsMulCommutative := hcomm
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
        Subtype.ext (by simpa [sq] using hcfg.F_sq g g.2) }
  have := CFSG.RankThree.Coprime.le_pRank_of_isElementaryAbelian (p := 2) (by norm_num) hF (k := 4)
    (by rw [hcfg.card_F]; norm_num)
  omega

theorem no_sylCfg_two_class {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {k : Kind}
    (hctx : Stage2Ctx G z k S) (hLP : LPairCtx G z S) {L₁ L₂ : Subgroup (CentralizerBar z)} {q : ℕ}
    {x : G} (htwo : TwoClassData G z S L₁ L₂ q x) {P E F : Subgroup G} (hcfg : SylCfg id P E F)
    (hP2 : IsPGroup 2 P) : False := by
  classical
  obtain ⟨g, hg⟩ := exists_conj_le_sylow hctx.sylow_top hP2
  have hcfg1 := hcfg.map (MulAut.conj g).toMonoidHom (MulAut.conj g).injective (α := id) (α' := id)
    (fun y => rfl)
  set P₁ : Subgroup G := P.map (MulAut.conj g).toMonoidHom with hP₁
  set E₁ : Subgroup G := E.map (MulAut.conj g).toMonoidHom with hE₁
  have hP₁2 : IsPGroup 2 P₁ := hP2.map _
  have hord : ∀ y ∈ P₁, 8 * orderOf y < Nat.card P₁ := by
    intro y hy
    have h1 : orderOf y ∣ 4 := orderOf_dvd_of_pow_eq_one (hcfg1.exp_P y hy)
    have h2 : orderOf y ≤ 4 := Nat.le_of_dvd (by norm_num) h1
    have h3 := hcfg1.card_P
    omega
  have hz : z ∈ P₁ := lpair_z_mem hctx.orderOf_z hLP hctx.S_le_Cen hg hP₁2 hord
  have hzE : z ∈ E₁ := hcfg1.E_center z hz (fun y hy => (hctx.S_comm_z (hg hy)).symm)
  have hz1 : z ≠ 1 := by
    intro h
    have := hctx.orderOf_z
    rw [h, orderOf_one] at this
    omega
  obtain ⟨e, heE, hne1, hnez⟩ : ∃ e ∈ E₁, e ≠ 1 ∧ e ≠ z := by
    by_contra hno
    push Not at hno
    have hle : E₁ ≤ zpowers z := by
      intro e he
      by_cases h1 : e = 1
      · rw [h1]; exact one_mem _
      · rw [hno e he h1]; exact mem_zpowers z
    have := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hctx.orderOf_z, hcfg1.card_E] at this
    omega
  obtain ⟨n, -, hn⟩ := hcfg1.fusion z hzE hz1 e heE hne1
  have hze : IsConj z e := isConj_iff.mpr ⟨n, hn⟩
  obtain ⟨a, ha, b, hb, hab⟩ := hcfg1.E_comm e heE
  have heLC : e ∈ LC z := by
    rw [← hab]
    exact comm_mem_LC hctx.S_le_Cen hLP.index (hg ha) (hg hb)
  have he2 : orderOf e = 2 := orderOf_eq_prime (by rw [sq]; exact hcfg1.E_sq e heE) hne1
  have hxe : IsConj x e := (htwo.invol_L e heLC he2 hnez).1
  have hzx : IsConj z x := hze.trans hxe.symm
  exact htwo.x_nonCentral (CFSG.GH74.GLS.Stage2.Final.isCentralInvolution_of_isConj hctx.central hzx)

theorem zpow_eq_one_or_eq {Q : Type} [Group Q] {t : Q} (ht2 : t * t = 1) (n : ℤ) :
    t ^ n = 1 ∨ t ^ n = t := by
  have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ht2]
  have hm : n = 2 * (n / 2) + n % 2 := (Int.mul_ediv_add_emod n 2).symm
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · left
    rw [hm, h, add_zero, zpow_mul, h2, one_zpow]
  · right
    rw [hm, h, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem no_one_class {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {k : Kind}
    (hctx : Stage2Ctx G z k S) (hS128 : Nat.card S ≤ 128) {H₀ : Subgroup G}
    (H₁ : Subgroup ↥H₀) [H₁.Normal] (hodd : Odd (Nat.card H₁)) {t : ↥H₀ ⧸ H₁}
    {P E F : Subgroup (↥H₀ ⧸ H₁)} (hcfg : SylCfg (fun y => t * y * t⁻¹) P E F) (ht2 : t * t = 1)
    (htP : t ∉ P) : False := by
  classical
  have hPb2 : IsPGroup 2 P := IsPGroup.of_card (n := 6) (by rw [hcfg.card_P]; norm_num)
  have htn : t ∈ normalizer (P : Set (↥H₀ ⧸ H₁)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hcfg.alpha_P y, fun hy => ?_⟩
    have := hcfg.alpha_P _ hy
    have h2 : t * (t * y * t⁻¹) * t⁻¹ = y := by
      calc t * (t * y * t⁻¹) * t⁻¹ = (t * t) * y * (t * t)⁻¹ := by group
        _ = y := by rw [ht2]; simp
    rwa [h2] at this
  have ht1 : t ≠ 1 := fun h => htP (h ▸ P.one_mem)
  have hord : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact ht2) ht1
  have hdisj : Disjoint P (zpowers t) := by
    rw [Subgroup.disjoint_def]
    intro x hxP hxt
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxt
    rcases zpow_eq_one_or_eq ht2 n with h | h
    · exact h
    · exact absurd (h ▸ hxP) htP
  have hcardT : Nat.card ↥(P ⊔ zpowers t) = 128 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer P (zpowers t)
      (by rw [Subgroup.zpowers_le]; exact htn) hdisj, hcfg.card_P, Nat.card_zpowers, hord]
  have hT2 : IsPGroup 2 ↥(P ⊔ zpowers t) := IsPGroup.of_card (n := 7) (by rw [hcardT]; norm_num)
  obtain ⟨T, hTp, hTmap, hTinj, -⟩ := lift_two_subgroup H₁ hodd (P ⊔ zpowers t) hT2
  set mk := QuotientGroup.mk' H₁ with hmk
  have hEcent : ∀ e ∈ E, ∀ y ∈ P ⊔ zpowers t, e * y = y * e := by
    have hPc : P ≤ Subgroup.centralizer (E : Set (↥H₀ ⧸ H₁)) := fun x hx =>
      Subgroup.mem_centralizer_iff.mpr fun e he => hcfg.E_cen e he x hx
    have htc : zpowers t ≤ Subgroup.centralizer (E : Set (↥H₀ ⧸ H₁)) := by
      rw [Subgroup.zpowers_le]
      refine Subgroup.mem_centralizer_iff.mpr fun e he => ?_
      have h1 := hcfg.E_alpha e he
      have h2 : t * e * t⁻¹ = e := h1
      calc e * t = (t * e * t⁻¹) * t := by rw [h2]
        _ = t * e := by group
    intro e he y hy
    exact Subgroup.mem_centralizer_iff.mp (sup_le hPc htc hy) e he
  let Et : Subgroup ↥H₀ := T ⊓ E.comap mk
  have hmemEt : ∀ x, x ∈ Et ↔ x ∈ T ∧ mk x ∈ E := fun x => Iff.rfl
  have hEtmap : Et.map mk = E := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ((hmemEt x).mp hx).2
    · intro hy
      have : y ∈ T.map mk := hTmap ▸ (le_sup_left : P ≤ P ⊔ zpowers t) (hcfg.E_le hy)
      obtain ⟨x, hxT, rfl⟩ := this
      exact ⟨x, (hmemEt x).mpr ⟨hxT, hy⟩, rfl⟩
  have hEtT : ∀ e ∈ Et, e ∈ T := fun e he => ((hmemEt e).mp he).1
  have hinjEt : ∀ x ∈ Et, ∀ y ∈ Et, mk x = mk y → x = y := fun x hx y hy =>
    hTinj x (hEtT x hx) y (hEtT y hy)
  have hcardEt : Nat.card Et = 4 := by
    rw [← card_map_of_inj_on mk Et hinjEt, hEtmap]; exact hcfg.card_E
  have hcardTT : Nat.card T = 128 := by
    rw [← card_map_of_inj_on mk T hTinj, hTmap]; exact hcardT
  have hEtcen : ∀ e ∈ Et, ∀ x ∈ T, e * x = x * e := by
    intro e he x hx
    have hxT : mk x ∈ P ⊔ zpowers t := hTmap ▸ ⟨x, hx, rfl⟩
    apply hTinj _ (T.mul_mem (hEtT e he) hx) _ (T.mul_mem hx (hEtT e he))
    rw [map_mul, map_mul]
    exact hEcent _ ((hmemEt e).mp he).2 _ hxT
  have hEtsq : ∀ e ∈ Et, e * e = 1 := by
    intro e he
    apply hTinj _ (T.mul_mem (hEtT e he) (hEtT e he)) 1 T.one_mem
    rw [map_mul, map_one]
    exact hcfg.E_sq _ ((hmemEt e).mp he).2
  have hT'2 : IsPGroup 2 ↥(T.map H₀.subtype) := hTp.map _
  obtain ⟨g, hg⟩ := exists_conj_le_sylow hctx.sylow_top hT'2
  set f : ↥H₀ →* G := (MulAut.conj g).toMonoidHom.comp H₀.subtype with hf
  have hfinj : Function.Injective f := (MulAut.conj g).injective.comp H₀.subtype_injective
  have hmapT : T.map f = (T.map H₀.subtype).map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_map]
  have hS : T.map f = S := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [hmapT]; exact hg
    · rw [Subgroup.card_map_of_injective hfinj, hcardTT]; exact hS128
  have hz := hctx.data.base.zcen
  have hle : Et.map f ≤ zpowers z := by
    rintro _ ⟨e, he, rfl⟩
    by_cases h1 : f e = 1
    · rw [h1]; exact one_mem _
    · have hmem : f e ∈ S := hS ▸ ⟨e, hEtT e he, rfl⟩
      have hcen : ∀ s ∈ S, s * f e = f e * s := by
        intro s hs
        rw [← hS] at hs
        obtain ⟨x, hx, rfl⟩ := hs
        rw [← map_mul, ← map_mul, hEtcen e he x hx]
      have hord2 : orderOf (f e) = 2 :=
        orderOf_eq_prime (by rw [sq, ← map_mul, hEtsq e he, map_one]) h1
      rw [hz (f e) hmem hcen hord2]
      exact mem_zpowers z
  have hcardE : Nat.card (Et.map f) = 4 := by
    rw [Subgroup.card_map_of_injective hfinj, hcardEt]
  have := Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers, hctx.orderOf_z, hcardE] at this
  omega

theorem card_hasSL2Model {A : Type} [Group A] {q : ℕ} (h : HasSL2Model A (fun r => r = q)) :
    Nat.card A = q * (q ^ 2 - 1) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv,
    ← Nat.card_congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).toEquiv,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF]

theorem exists_eight_mul_odd {q : ℕ} (hq : q % 8 = 3 ∨ q % 8 = 5) :
    ∃ m : ℕ, q * (q ^ 2 - 1) = 8 * m ∧ Odd m := by
  rcases hq with h | h
  · obtain ⟨a, ha⟩ : ∃ a, q = 8 * a + 3 := ⟨q / 8, by omega⟩
    subst ha
    have h1 : (8 * a + 3) ^ 2 = (8 * a + 2) * (8 * a + 4) + 1 := by ring
    refine ⟨(8 * a + 3) * (4 * a + 1) * (2 * a + 1), ?_, ?_⟩
    · rw [h1, Nat.add_sub_cancel]; ring
    · have o1 : Odd (8 * a + 3) := ⟨4 * a + 1, by ring⟩
      have o2 : Odd (4 * a + 1) := ⟨2 * a, by ring⟩
      have o3 : Odd (2 * a + 1) := ⟨a, by ring⟩
      exact (o1.mul o2).mul o3
  · obtain ⟨a, ha⟩ : ∃ a, q = 8 * a + 5 := ⟨q / 8, by omega⟩
    subst ha
    have h1 : (8 * a + 5) ^ 2 = (8 * a + 4) * (8 * a + 6) + 1 := by ring
    refine ⟨(8 * a + 5) * (2 * a + 1) * (4 * a + 3), ?_, ?_⟩
    · rw [h1, Nat.add_sub_cancel]; ring
    · have o1 : Odd (8 * a + 5) := ⟨4 * a + 2, by ring⟩
      have o2 : Odd (2 * a + 1) := ⟨a, by ring⟩
      have o3 : Odd (4 * a + 3) := ⟨2 * a + 1, by ring⟩
      exact (o1.mul o2).mul o3

theorem card_S_le_128 {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} (hSC : S ≤ Cen z)
    (hS2 : IsPGroup 2 S) {L₁ L₂ : Subgroup (CentralizerBar z)} {q : ℕ} (hq : q % 8 = 3 ∨ q % 8 = 5)
    (hprod : IsCentralProd L₁ L₂ (LBar z)) (h₁ : HasSL2Model ↥L₁ (fun r => r = q))
    (h₂ : HasSL2Model ↥L₂ (fun r => r = q)) (hidx : (RC S z).relIndex S ≤ 4) : Nat.card S ≤ 128 := by
  classical
  obtain ⟨hsup, hcomm, hinf⟩ := hprod
  obtain ⟨m, hm, hmodd⟩ := exists_eight_mul_odd hq
  have hL₁ : Nat.card L₁ = 8 * m := by rw [card_hasSL2Model h₁, hm]
  have hL₂ : Nat.card L₂ = 8 * m := by rw [card_hasSL2Model h₂, hm]
  have hprodcard := CFSG.RankThree.PartOne.PlaneCommuting.card_sup_mul_card_inf hcomm
  rw [hsup, hinf, hL₁, hL₂] at hprodcard
  have hLB : Nat.card (LBar z) = 32 * (m * m) := by
    have : (8 * m) * (8 * m) = 64 * (m * m) := by ring
    omega
  have hR2 : IsPGroup 2 ↥(RC S z) := hS2.to_le inf_le_left
  have hRC : RC S z ≤ Cen z := inf_le_left.trans hSC
  obtain ⟨ψ, hinj, -, hrange⟩ := exists_psi hR2 hRC
  have hcardR : Nat.card (barOf z (RC S z)) = Nat.card (RC S z) := by
    rw [← hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hle : barOf z (RC S z) ≤ LBar z := by
    intro y hy
    obtain ⟨u, hu, huP, rfl⟩ := mem_barOf_iff.mp hy
    exact mem_barOf_iff.mpr ⟨u, hu, (Subgroup.mem_inf.mp huP).2, rfl⟩
  have hdvd : Nat.card (RC S z) ∣ 32 * (m * m) := by
    rw [← hLB, ← hcardR]
    exact Subgroup.card_dvd_of_le hle
  obtain ⟨j, hj⟩ := hR2.exists_card_eq
  have hj5 : j ≤ 5 := by
    by_contra hj6
    push Not at hj6
    rw [hj] at hdvd
    have h64 : 2 ^ 6 ∣ 2 ^ j := pow_dvd_pow 2 hj6
    have h2 : 64 ∣ 32 * (m * m) := h64.trans hdvd
    have h3 : 2 ∣ m * m := by omega
    have h4 : 2 ∣ m := (Nat.Prime.dvd_mul Nat.prime_two).mp h3 |>.elim id id
    obtain ⟨k, hk⟩ := hmodd
    omega
  have hRle : Nat.card (RC S z) ≤ 32 := by
    rw [hj]
    calc 2 ^ j ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) hj5
      _ = 32 := by norm_num
  have h1 := Subgroup.relIndex_mul_card (H := RC S z) (K := S)
  have hRS : RC S z ≤ S := inf_le_left
  rw [inf_eq_left.mpr hRS] at h1
  calc Nat.card S = (RC S z).relIndex S * Nat.card (RC S z) := h1.symm
    _ ≤ 4 * 32 := Nat.mul_le_mul hidx hRle
    _ = 128 := by norm_num

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P85
