module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage5
public import CFSG.CharacterTheory.Burnside
public import Certificates.Certificate17027
public import Certificates.Certificate5952
public import Certificates.Certificate12952
public import Certificates.Certificate14951

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action CFSG.QuasithinUnique.A5.Split
open scoped MatrixGroups

theorem w04_sums_four : (w04 + pact sa w04) 4 = 0 ∧ (w04 + pact sc w04) 4 = 0 ∧
    (w04 + pact s3 w04) 4 = 0 := by decide +kernel

theorem s1_mem_Vset : s1 ∈ Vset := by decide +kernel

theorem Eset_fix_g1 : ∀ σ ∈ Eset, pact σ g1 = g1 := by decide +kernel

theorem g1_ne_zero : g1 ≠ 0 := by decide +kernel

theorem g1_ne_z0 : g1 ≠ z0 := by decide +kernel

theorem zU_pow_odd {G : Type*} [Group G] {z : G} (hz : z * z = 1) {k : ℕ} (hk : Odd k) :
    z ^ k = z := by
  obtain ⟨j, rfl⟩ := hk
  rw [pow_succ, pow_mul, pow_two, hz, one_pow, one_mul]

theorem eq_of_mulVec_eq {A B : Matrix (Fin 4) (Fin 4) (ZMod 2)}
    (h : ∀ v : V4, A.mulVec v = B.mulVec v) : A = B := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

theorem conj_mem_centerOf {G : Type*} [Group G] {P : Subgroup G} {m : G}
    (hm : m ∈ Subgroup.normalizer (P : Set G)) {z : G} (hz : z ∈ centerOf P) :
    m * z * m⁻¹ ∈ centerOf P := by
  obtain ⟨hzP, hzc⟩ := Subgroup.mem_inf.mp hz
  refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hm z).mp hzP, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro p hp
  have hp' : m⁻¹ * p * m⁻¹⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (inv_mem hm) p).mp hp
  have hc : (m⁻¹ * p * m⁻¹⁻¹) * z = z * (m⁻¹ * p * m⁻¹⁻¹) :=
    Subgroup.mem_centralizer_iff.mp hzc _ hp'
  calc p * (m * z * m⁻¹) = m * ((m⁻¹ * p * m⁻¹⁻¹) * z) * m⁻¹ := by group
    _ = m * (z * (m⁻¹ * p * m⁻¹⁻¹)) * m⁻¹ := by rw [hc]
    _ = (m * z * m⁻¹) * p := by group

theorem borelP_le_M1 {G : Type*} [Group G] (T M L : Subgroup G) :
    borelP M L ≤ T ⊔ borelK M L :=
  (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _).trans le_sup_right

namespace StdCfg

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

theorem M1_le_M (C : StdCfg T M H S L) : T ⊔ borelK M L ≤ M :=
  sup_le C.hcs.setting.le (fun _ hk => (StdCfg.borelK_le M L hk).1)

theorem sylow_T_of_le (C : StdCfg T M H S L) {A : Subgroup G} (hTA : T ≤ A) :
    IsSylowTwoOf T A := by
  have hT := C.hcs.setting.sylow
  refine ⟨hTA, hT.2.1, fun hdvd => hT.2.2 ?_⟩
  have h1 := Subgroup.relIndex_mul_relIndex T A ⊤ hTA le_top
  have h2 : 2 ∣ T.relIndex ⊤ := by
    rw [← h1]
    exact Dvd.dvd.mul_right hdvd _
  exact h2

theorem M_charTwo (C : StdCfg T M H S L) :
    M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT := C.hcs.setting.sylow
  have hdvd : ¬ 2 ∣ T.index := by
    have := hT.2.2
    rwa [index_subgroupOf_top] at this
  exact C.hcs.setting.qtke.2.1 M C.hcs.setting.maxLocal.1
    ⟨hT.2.1.toSylow hdvd, C.hcs.setting.le⟩

theorem zpowers_zU_pgroup (C : StdCfg T M H S L) : IsPGroup 2 ↥(Subgroup.zpowers C.zU) := by
  refine IsPGroup.of_card (n := 1) ?_
  rw [Nat.card_zpowers, pow_one]
  exact orderOf_eq_prime C.zU_sq C.zU_ne_one

theorem zpowers_zU_ne_bot (C : StdCfg T M H S L) : Subgroup.zpowers C.zU ≠ ⊥ := by
  intro h
  apply C.zU_ne_one
  have : C.zU ∈ Subgroup.zpowers C.zU := Subgroup.mem_zpowers _
  rw [h] at this
  exact Subgroup.mem_bot.mp this

theorem normalizer_zpowers_zU (C : StdCfg T M H S L) :
    Subgroup.normalizer (Subgroup.zpowers C.zU : Set G) =
      Subgroup.centralizer ({C.zU} : Set G) := by
  ext g
  constructor
  · intro hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    have h1 := (Subgroup.mem_normalizer_iff.mp hg C.zU).mp (Subgroup.mem_zpowers _)
    rcases (mem_zpowers_two C.zU_mul_self _).mp h1 with h2 | h2
    · exfalso
      apply C.zU_ne_one
      calc C.zU = g⁻¹ * (g * C.zU * g⁻¹) * g := by group
        _ = 1 := by rw [h2]; group
    · calc C.zU * g = (g * C.zU * g⁻¹) * g := by rw [h2]
        _ = g * C.zU := by group
  · intro hg
    have hc : C.zU * g = g * C.zU := Subgroup.mem_centralizer_iff.mp hg C.zU rfl
    have hconj : g * C.zU * g⁻¹ = C.zU := by
      calc g * C.zU * g⁻¹ = C.zU * g * g⁻¹ := by rw [hc]
        _ = C.zU := by group
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rcases (mem_zpowers_two C.zU_mul_self x).mp hx with h2 | h2
      · have : g * x * g⁻¹ = 1 := by rw [h2]; group
        rw [this]
        exact one_mem _
      · rw [h2, hconj]
        exact Subgroup.mem_zpowers _
    · intro hx
      rcases (mem_zpowers_two C.zU_mul_self _).mp hx with h2 | h2
      · have : x = 1 := by
          calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
            _ = 1 := by rw [h2]; group
        rw [this]
        exact one_mem _
      · have : x = C.zU := by
          calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
            _ = g⁻¹ * C.zU * g := by rw [h2]
            _ = g⁻¹ * (C.zU * g) := by group
            _ = g⁻¹ * (g * C.zU) := by rw [hc]
            _ = C.zU := by group
        rw [this]
        exact Subgroup.mem_zpowers _

end StdCfg

namespace Sec

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {C : StdCfg T M H S L}
  (X : Sec C)

include X

theorem T_le_GZ : T ≤ Subgroup.centralizer ({C.zU} : Set G) := by
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  rw [hh]
  exact (X.T_cent_z ht).symm

theorem GZ_le_M : Subgroup.centralizer ({C.zU} : Set G) ≤ M := by
  classical
  have h2 : CFSG.Assembly.IsTwoLocal (Subgroup.centralizer ({C.zU} : Set G)) :=
    ⟨Subgroup.zpowers C.zU, C.zpowers_zU_ne_bot, C.zpowers_zU_pgroup,
      C.normalizer_zpowers_zU.symm⟩
  let 𝒮 : Set (Subgroup G) :=
    {H' | CFSG.Assembly.IsTwoLocal H' ∧ Subgroup.centralizer ({C.zU} : Set G) ≤ H'}
  obtain ⟨H₀, hH₀⟩ := (Set.toFinite 𝒮).exists_maximal ⟨_, h2, le_rfl⟩
  have hmax : CFSG.Assembly.Quasithin.quasithinIsMaxTwoLocal H₀ :=
    ⟨hH₀.1.1, fun H' hH' hle => le_antisymm (hH₀.2 ⟨hH', hH₀.1.2.trans hle⟩ hle) hle⟩
  have hM : H₀ = M := C.hcs.setting.unique H₀ hmax (X.T_le_GZ.trans hH₀.1.2)
  exact hH₀.1.2.trans hM.le

theorem trivial_action_comm {m : G} (hm : m ∈ T ⊔ borelK M L)
    (htriv : ∀ v : V4, (X.rhoM ⟨m, hm⟩).mulVec v = v) :
    ∀ p ∈ borelP M L, m * p * m⁻¹ * p⁻¹ ∈ centerOf (borelP M L) := by
  intro p hp
  let p' : ↥(borelP M L) := ⟨p, hp⟩
  let y : ↥(borelP M L) := ⟨m * p * m⁻¹, X.M1_normalizes hm hp⟩
  have h1 := X.rhoM_spec ⟨m, hm⟩ p' y rfl
  rw [htriv] at h1
  have hyp : X.thG y = X.thG p' := Multiplicative.toAdd.injective h1
  have h2 : X.thG (y * p'⁻¹) = 1 := by
    rw [map_mul, map_inv, hyp]
    exact mul_inv_cancel _
  have h3 : y * p'⁻¹ ∈ (X.thG).ker := h2
  rw [X.thG_ker] at h3
  exact h3

theorem comm_form {s f : G} (hs : s ∈ S) (hf : f ∈ S)
    (h : s * f * s⁻¹ * f⁻¹ ∈ centerOf (borelP M L)) :
    s * f = f * s ∨ s * f = f * s * C.zU := by
  rcases (X.centerOf_P_iff _).mp h with h1 | h1
  · left
    calc s * f = (s * f * s⁻¹ * f⁻¹) * (f * s) := by group
      _ = f * s := by rw [h1]; group
  · right
    have hzS : C.zU ∈ centerOf S := (X.centerOf_S_iff _).mpr (Or.inr rfl)
    have hzc : (f * s) * C.zU = C.zU * (f * s) :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hzS).2 _ (mul_mem hf hs)
    calc s * f = (s * f * s⁻¹ * f⁻¹) * (f * s) := by group
      _ = C.zU * (f * s) := by rw [h1]
      _ = f * s * C.zU := hzc.symm

theorem mem_P_of_trivial_S {s : G} (hs : s ∈ S)
    (h : ∀ p ∈ borelP M L, s * p * s⁻¹ * p⁻¹ ∈ centerOf (borelP M L)) : s ∈ borelP M L := by
  have hsH : s ∈ H := C.hcs.sylow.le hs
  let q : ↥H := ⟨s, hsH⟩
  have hcomm : ∀ f ∈ borelP M L, s * f = f * s ∨ s * f = f * s * C.zU := fun f hf =>
    X.comm_form hs (X.P_le_S hf) (h f hf)
  obtain ⟨h4a, h4b, h4c⟩ := w04_sums_four
  have c1 : commZ (X.raw q) (X.raw (C.iV (w04w + vact sa w04w))) :=
    (X.commZ_iff _ _).mpr (hcomm _ (X.iV_mem_P (e := w04w + vact sa w04w) h4a))
  have c2 : commZ (X.raw q) (X.raw (C.iV (w04w + vact sc w04w))) :=
    (X.commZ_iff _ _).mpr (hcomm _ (X.iV_mem_P (e := w04w + vact sc w04w) h4b))
  have c3 : commZ (X.raw q) (X.raw (C.iV (w04w + vact s3 w04w))) :=
    (X.commZ_iff _ _).mpr (hcomm _ (X.iV_mem_P (e := w04w + vact s3 w04w) h4c))
  have c4 : commZ (X.raw q) (X.raw (X.s s1)) :=
    (X.commZ_iff _ _).mpr (hcomm _ (X.s_mem_P s1_mem_Vset))
  rw [X.raw_iV] at c1 c2 c3
  rw [X.raw_s] at c4
  have hq := csW (X.raw q).1 (mem_Evens.mpr (X.cw q).2) (X.raw q).2
    ((mem_Dstd _).mp ((X.mem_S_iff q).mp hs)) c1 c2 c3 c4
  exact (X.raw_P_iff q).mpr ⟨⟨(X.cw q).2, hq.1⟩, hq.2⟩

@[instance_reducible] noncomputable def actN
    (N : Subgroup G) (hN : N ≤ T ⊔ borelK M L) : MulAction ↥N V4 where
  smul n v := (X.rhoM ⟨n, hN n.2⟩).mulVec v
  one_smul v := by
    show (X.rhoM ⟨((1 : ↥N) : G), hN (1 : ↥N).2⟩).mulVec v = v
    have : (⟨((1 : ↥N) : G), hN (1 : ↥N).2⟩ : ↥(T ⊔ borelK M L)) = 1 := rfl
    rw [this, X.rhoM_one, Matrix.one_mulVec]
  mul_smul a b v := by
    show (X.rhoM ⟨((a * b : ↥N) : G), hN (a * b : ↥N).2⟩).mulVec v =
      (X.rhoM ⟨(a : G), hN a.2⟩).mulVec ((X.rhoM ⟨(b : G), hN b.2⟩).mulVec v)
    have : (⟨((a * b : ↥N) : G), hN (a * b : ↥N).2⟩ : ↥(T ⊔ borelK M L)) =
        ⟨(a : G), hN a.2⟩ * ⟨(b : G), hN b.2⟩ := rfl
    rw [this, X.rhoM_mul, Matrix.mulVec_mulVec]

theorem pCoreM1_trivial
    {n : G} (hn : n ∈ pCoreOf 2 (T ⊔ borelK M L)) (v : V4) :
    (X.rhoM ⟨n, CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _ hn⟩).mulVec v = v := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup G := pCoreOf 2 (T ⊔ borelK M L) with hNdef
  have hN : N ≤ T ⊔ borelK M L := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _
  have hnorm : T ⊔ borelK M L ≤ Subgroup.normalizer (N : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _
  let What : V4 → Prop := fun v => ∀ n' : ↥N, (X.rhoM ⟨n', hN n'.2⟩).mulVec v = v
  have hzero : What 0 := fun n' => Matrix.mulVec_zero _
  have hadd : ∀ a b, What a → What b → What (a + b) := by
    intro a b ha hb n'
    rw [Matrix.mulVec_add, ha n', hb n']
  have hinv : ∀ (m : ↥(T ⊔ borelK M L)) v, What v → What ((X.rhoM m).mulVec v) := by
    intro m v hv n'
    have hn'' : (m : G)⁻¹ * n' * (m : G) ∈ N := by
      have := (Subgroup.mem_normalizer_iff.mp (hnorm (inv_mem m.2)) (n' : G)).mp n'.2
      simpa using this
    have hmul : (⟨(n' : G), hN n'.2⟩ : ↥(T ⊔ borelK M L)) * m =
        m * ⟨(m : G)⁻¹ * n' * (m : G), hN hn''⟩ := by
      apply Subtype.ext
      show (n' : G) * m = m * ((m : G)⁻¹ * n' * m)
      group
    calc (X.rhoM ⟨n', hN n'.2⟩).mulVec ((X.rhoM m).mulVec v)
        = (X.rhoM (⟨(n' : G), hN n'.2⟩ * m)).mulVec v := by
          rw [X.rhoM_mul, Matrix.mulVec_mulVec]
      _ = (X.rhoM m).mulVec ((X.rhoM ⟨(m : G)⁻¹ * n' * (m : G), hN hn''⟩).mulVec v) := by
          rw [hmul, X.rhoM_mul, Matrix.mulVec_mulVec]
      _ = (X.rhoM m).mulVec v := by rw [hv ⟨_, hn''⟩]
  have hne : ∃ v, v ≠ 0 ∧ What v := by
    by_contra hno
    push Not at hno
    let _inst : MulAction ↥N V4 := X.actN N hN
    have hpg : IsPGroup 2 ↥N := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _
    have hmod := hpg.card_modEq_card_fixedPoints (α := V4)
    have hfix : MulAction.fixedPoints ↥N V4 = {0} := by
      ext w
      constructor
      · intro hw
        by_contra hw0
        exact hno w (fun h => hw0 h) (fun n' => hw n')
      · intro hw
        rw [Set.mem_singleton_iff] at hw
        rw [hw]
        intro n'
        exact Matrix.mulVec_zero _
    rw [hfix] at hmod
    have h16 : Nat.card V4 = 16 := by
      rw [Nat.card_eq_fintype_card]
      simp
    have h1 : Nat.card ↥({0} : Set V4) = 1 := by simp
    rw [h16, h1] at hmod
    exact absurd hmod (by decide)
  have hall := X.irredV What hzero hadd hinv hne
  exact hall v ⟨n, hn⟩

theorem O2M1_eq : pCoreOf 2 (T ⊔ borelK M L) = borelP M L := by
  apply le_antisymm
  · intro n hn
    have hnM1 : n ∈ T ⊔ borelK M L := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _ hn
    have hnT : n ∈ T := (C.sylow_T_of_le (le_sup_left : T ≤ T ⊔ borelK M L)).pCoreOf_le hn
    have hcomm := X.trivial_action_comm hnM1 (fun v => X.pCoreM1_trivial hn v)
    have hnS : n ∈ S := X.mem_S_of_trivial_action hnT hcomm
    exact X.mem_P_of_trivial_S hnS hcomm
  · have hPK : borelP M L ≤ borelK M L := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _
    have hPM1 : borelP M L ≤ T ⊔ borelK M L := hPK.trans le_sup_right
    exact CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 (borelP M L)
      (T ⊔ borelK M L) hPM1
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hPM1).mpr
        (sup_le X.T_normalizes_P X.K_normalizes_P))
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _)

theorem pCore_M_eq : pCoreOf 2 M = borelP M L := by
  have hQT : pCoreOf 2 M ≤ T :=
    (C.sylow_T_of_le C.hcs.setting.le).pCoreOf_le
  have hQM1 : pCoreOf 2 M ≤ T ⊔ borelK M L := hQT.trans le_sup_left
  have hM1norm : T ⊔ borelK M L ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
    C.M1_le_M.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M)
  have hQP : pCoreOf 2 M ≤ borelP M L := by
    rw [← X.O2M1_eq]
    exact CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 (pCoreOf 2 M)
      (T ⊔ borelK M L) hQM1
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hQM1).mpr hM1norm)
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M)
  have hzQ : C.zU ∈ pCoreOf 2 M := by
    apply C.M_charTwo
    refine Subgroup.mem_inf.mpr ⟨C.hcs.setting.le ?_, ?_⟩
    · exact C.hcs.le_T (blockU_le_S C.hcs C.hj C.zU_mem)
    · rw [Subgroup.mem_centralizer_iff]
      intro q hq
      exact X.T_cent_z (hQT hq)
  have hZQ : centerOf (borelP M L) ≤ pCoreOf 2 M := by
    intro x hx
    rcases (X.centerOf_P_iff x).mp hx with rfl | rfl
    · exact one_mem _
    · exact hzQ
  rcases X.irred (pCoreOf 2 M) hZQ hQP hM1norm with h | h
  · exfalso
    have hTQ : T ≤ pCoreOf 2 M := by
      intro t ht
      apply C.M_charTwo
      refine Subgroup.mem_inf.mpr ⟨C.hcs.setting.le ht, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      rw [h] at hq
      rcases (X.centerOf_P_iff q).mp hq with rfl | rfl
      · rw [one_mul, mul_one]
      · exact (X.T_cent_z ht).symm
    have hPT : borelP M L ≤ T := (X.P_le_S).trans C.hcs.le_T
    have hPZ : borelP M L ≤ centerOf (borelP M L) := fun x hx => h ▸ hTQ (hPT hx)
    have hle := Subgroup.card_le_of_le hPZ
    rw [X.card_P, X.Z_card] at hle
    omega
  · exact h

theorem M_le_normalizer_P
    : M ≤ Subgroup.normalizer (borelP M L : Set G) := by
  rw [← X.pCore_M_eq]
  exact CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M

theorem M_le_GZ : M ≤ Subgroup.centralizer ({C.zU} : Set G) := by
  intro m hm
  have hcz : m * C.zU * m⁻¹ ∈ centerOf (borelP M L) :=
    conj_mem_centerOf (X.M_le_normalizer_P hm) ((X.centerOf_P_iff _).mpr (Or.inr rfl))
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  rcases (X.centerOf_P_iff _).mp hcz with h | h
  · exfalso
    apply C.zU_ne_one
    calc C.zU = m⁻¹ * (m * C.zU * m⁻¹) * m := by group
      _ = 1 := by rw [h]; group
  · calc C.zU * m = (m * C.zU * m⁻¹) * m := by rw [h]
      _ = m * C.zU := by group

theorem M_cent_eq
    : M = Subgroup.centralizer (centerOf (borelP M L) : Set G) := by
  apply le_antisymm
  · intro m hm
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rcases (X.centerOf_P_iff z).mp hz with rfl | rfl
    · rw [one_mul, mul_one]
    · exact Subgroup.mem_centralizer_iff.mp (X.M_le_GZ hm) C.zU rfl
  · refine le_trans (Subgroup.centralizer_le ?_) X.GZ_le_M
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact (X.centerOf_P_iff _).mpr (Or.inr rfl)

theorem exists_rho_M : ∃ ρ : ↥M →* GL (Fin 4) (ZMod 2),
    ∀ (m : ↥M) (x y : ↥(borelP M L)), (y : G) = m * x * m⁻¹ →
      Multiplicative.toAdd (X.thG y) =
        (ρ m : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec (Multiplicative.toAdd (X.thG x)) :=
  exists_rho (M₁ := M) X.thG X.thG_surj X.thG_ker
    (fun _ hm p hp => (Subgroup.mem_normalizer_iff.mp (X.M_le_normalizer_P hm) p).mp hp)
    (fun _ hm _ hz => conj_mem_centerOf (X.M_le_normalizer_P hm) hz)

@[expose] noncomputable def rho'
    : ↥M →* GL (Fin 4) (ZMod 2) := Classical.choose X.exists_rho_M

theorem rho'_spec
    : ∀ (m : ↥M) (x y : ↥(borelP M L)), (y : G) = m * x * m⁻¹ →
    Multiplicative.toAdd (X.thG y) =
      ((X.rho' m : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec
        (Multiplicative.toAdd (X.thG x)) :=
  Classical.choose_spec X.exists_rho_M

theorem rho'_eq_rho (m : ↥(T ⊔ borelK M L)) :
    ((X.rho' ⟨(m : G), C.M1_le_M m.2⟩ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      X.rhoM m := by
  have key : ∀ v : V4,
      ((X.rho' ⟨(m : G), C.M1_le_M m.2⟩ : GL (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v = (X.rhoM m).mulVec v := by
    intro v
    obtain ⟨p, hp⟩ := X.thG_surj (Multiplicative.ofAdd v)
    have hv : v = Multiplicative.toAdd (X.thG p) := by rw [hp]; rfl
    let y : ↥(borelP M L) := ⟨(m : G) * p * (m : G)⁻¹, X.M1_normalizes m.2 p.2⟩
    rw [hv, ← X.rho'_spec ⟨(m : G), C.M1_le_M m.2⟩ p y rfl, ← X.rhoM_spec m p y rfl]
  ext i j
  have := congrFun (key (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

theorem rho'_quad (m : ↥M) (v : V4) :
    quadHyp (((X.rho' m : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v) =
      quadHyp v := by
  obtain ⟨p, hp⟩ := X.thG_surj (Multiplicative.ofAdd v)
  have hv : v = Multiplicative.toAdd (X.thG p) := by rw [hp]; rfl
  have hmn : (m : G) ∈ Subgroup.normalizer (borelP M L : Set G) := X.M_le_normalizer_P m.2
  let y : ↥(borelP M L) :=
    ⟨(m : G) * p * (m : G)⁻¹, (Subgroup.mem_normalizer_iff.mp hmn p).mp p.2⟩
  have h1 := X.rho'_spec m p y rfl
  rw [hv, ← h1]
  have hmz : (m : G) * C.zU * (m : G)⁻¹ = C.zU := by
    have hc : C.zU * (m : G) = (m : G) * C.zU :=
      Subgroup.mem_centralizer_iff.mp (X.M_le_GZ m.2) C.zU rfl
    calc (m : G) * C.zU * (m : G)⁻¹ = C.zU * (m : G) * (m : G)⁻¹ := by rw [hc]
      _ = C.zU := by group
  have hyy : (y : G) * y = (m : G) * ((p : G) * p) * (m : G)⁻¹ := by
    show (m : G) * p * (m : G)⁻¹ * ((m : G) * p * (m : G)⁻¹) = _
    group
  rcases X.sq_cases p with ⟨hp1, hq1⟩ | ⟨hp1, hq1⟩ <;>
    rcases X.sq_cases y with ⟨hy1, hq2⟩ | ⟨hy1, hq2⟩
  · rw [hq1, hq2]
  · exfalso
    apply C.zU_ne_one
    calc C.zU = (y : G) * y := hy1.symm
      _ = (m : G) * ((p : G) * p) * (m : G)⁻¹ := hyy
      _ = 1 := by rw [hp1]; group
  · exfalso
    apply C.zU_ne_one
    calc C.zU = (m : G) * C.zU * (m : G)⁻¹ := hmz.symm
      _ = (m : G) * ((p : G) * p) * (m : G)⁻¹ := by rw [hp1]
      _ = (y : G) * y := hyy.symm
      _ = 1 := hy1
  · rw [hq1, hq2]

theorem ker_comm {n : ↥M} (hn : X.rho' n = 1) :
    ∀ p ∈ borelP M L, (n : G) * p * (n : G)⁻¹ * p⁻¹ ∈ centerOf (borelP M L) := by
  intro p hp
  have hmn : (n : G) ∈ Subgroup.normalizer (borelP M L : Set G) := X.M_le_normalizer_P n.2
  let p' : ↥(borelP M L) := ⟨p, hp⟩
  let y : ↥(borelP M L) :=
    ⟨(n : G) * p * (n : G)⁻¹, (Subgroup.mem_normalizer_iff.mp hmn p).mp hp⟩
  have h1 := X.rho'_spec n p' y rfl
  rw [hn, Units.val_one, Matrix.one_mulVec] at h1
  have hyp : X.thG y = X.thG p' := Multiplicative.toAdd.injective h1
  have h2 : X.thG (y * p'⁻¹) = 1 := by
    rw [map_mul, map_inv, hyp]
    exact mul_inv_cancel _
  have h3 : y * p'⁻¹ ∈ (X.thG).ker := h2
  rw [X.thG_ker] at h3
  exact h3

theorem odd_order_central
    {g : G} (hgM : g ∈ M) (hodd : Odd (orderOf g))
    (hcomm : ∀ p ∈ borelP M L, g * p * g⁻¹ * p⁻¹ ∈ centerOf (borelP M L)) :
    ∀ p ∈ borelP M L, g * p * g⁻¹ = p := by
  intro p hp
  have hgz : g * C.zU * g⁻¹ = C.zU := by
    have hc : C.zU * g = g * C.zU :=
      Subgroup.mem_centralizer_iff.mp (X.M_le_GZ hgM) C.zU rfl
    calc g * C.zU * g⁻¹ = C.zU * g * g⁻¹ := by rw [hc]
      _ = C.zU := by group
  set c : G := g * p * g⁻¹ * p⁻¹ with hc
  have hcc : g * c * g⁻¹ = c := by
    rcases (X.centerOf_P_iff _).mp (hcomm p hp) with h | h
    · rw [← hc] at h
      rw [h]
      group
    · rw [← hc] at h
      rw [h, hgz]
  have hcp : ∀ j : ℕ, g ^ j * p * (g ^ j)⁻¹ = c ^ j * p := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc g ^ (j + 1) * p * (g ^ (j + 1))⁻¹
          = g * (g ^ j * p * (g ^ j)⁻¹) * g⁻¹ := by group
        _ = g * (c ^ j * p) * g⁻¹ := by rw [ih]
        _ = (g * c ^ j * g⁻¹) * (g * p * g⁻¹) := by group
        _ = c ^ j * (c * p) := by
          have h1 : g * c ^ j * g⁻¹ = c ^ j := by
            calc g * c ^ j * g⁻¹ = (g * c * g⁻¹) ^ j := by rw [conj_pow]
              _ = c ^ j := by rw [hcc]
          have h2 : g * p * g⁻¹ = c * p := by
            rw [hc]
            group
          rw [h1, h2]
        _ = c ^ (j + 1) * p := by group
  have hk : g ^ orderOf g = 1 := pow_orderOf_eq_one g
  have h2 := hcp (orderOf g)
  rw [hk] at h2
  have hcpow : c ^ orderOf g = 1 := by
    have : (1 : G) * p * (1 : G)⁻¹ = c ^ orderOf g * p := by simpa using h2
    simpa using this.symm
  have hcz : c = 1 := by
    rcases (X.centerOf_P_iff _).mp (hcomm p hp) with h | h
    · rw [← hc] at h
      exact h
    · rw [← hc] at h
      rw [h, zU_pow_odd C.zU_mul_self hodd] at hcpow
      exact absurd hcpow C.zU_ne_one
  rw [hcz] at hc
  calc g * p * g⁻¹ = (g * p * g⁻¹ * p⁻¹) * p := by group
    _ = p := by rw [← hc]; group

theorem ker_two_element
    {n : ↥M} (hn : X.rho' n = 1) : ∃ a : ℕ, (n : G) ^ 2 ^ a = 1 := by
  have hpos : 0 < orderOf (n : G) := orderOf_pos _
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd hpos.ne'
  refine ⟨a, ?_⟩
  set g : G := (n : G) ^ 2 ^ a with hg
  have hgM : g ∈ M := M.pow_mem n.2 _
  let nM : ↥M := n ^ 2 ^ a
  have hnM : (nM : G) = g := rfl
  have hnM1 : X.rho' nM = 1 := by
    show X.rho' (n ^ 2 ^ a) = 1
    rw [map_pow, hn, one_pow]
  have hgb : g ^ b = 1 := by
    rw [hg, ← pow_mul, ← hab]
    exact pow_orderOf_eq_one _
  have hgodd : Odd (orderOf g) := by
    have hdvd : orderOf g ∣ b := orderOf_dvd_of_pow_eq_one hgb
    exact Odd.of_dvd_nat hb hdvd
  have hcentral := X.odd_order_central hgM hgodd (by
    rw [← hnM]
    exact X.ker_comm hnM1)
  have hgP : g ∈ borelP M L := by
    rw [← X.pCore_M_eq]
    apply C.M_charTwo
    refine Subgroup.mem_inf.mpr ⟨hgM, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    rw [X.pCore_M_eq] at hq
    have h := hcentral q hq
    calc q * g = (g * q * g⁻¹) * g := by rw [h]
      _ = g * q := by group
  have hg32 : g ^ 32 = 1 := by
    have h1 : (⟨g, hgP⟩ : ↥(borelP M L)) ^ Nat.card ↥(borelP M L) = 1 := pow_card_eq_one'
    rw [X.card_P] at h1
    have h2 := congrArg Subtype.val h1
    simpa using h2
  have hdvd32 : orderOf g ∣ 32 := orderOf_dvd_of_pow_eq_one hg32
  have hdvdb : orderOf g ∣ b := orderOf_dvd_of_pow_eq_one hgb
  have hcop : Nat.Coprime 32 b := by
    have h32 : (32 : ℕ) = 2 ^ 5 := by norm_num
    rw [h32]
    exact Nat.Coprime.pow_left 5 (Nat.coprime_two_left.mpr hb)
  have hone : orderOf g = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd32 hdvdb
  exact orderOf_eq_one_iff.mp hone

theorem ker_le_P
    {n : ↥M} (hn : X.rho' n = 1) : (n : G) ∈ borelP M L := by
  let K0 : Subgroup G := X.rho'.ker.map M.subtype
  have hK0M : K0 ≤ M := by
    rintro _ ⟨k, -, rfl⟩
    exact k.2
  have hK0P2 : IsPGroup 2 ↥K0 := by
    rintro ⟨_, k, hk, rfl⟩
    obtain ⟨a, ha⟩ := X.ker_two_element hk
    exact ⟨a, Subtype.ext (by simpa using ha)⟩
  have hK0norm : (K0.subgroupOf M).Normal := by
    have : K0.subgroupOf M = X.rho'.ker :=
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
    rw [this]
    infer_instance
  have hle : K0 ≤ pCoreOf 2 M :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 K0 M hK0M hK0norm hK0P2
  rw [X.pCore_M_eq] at hle
  exact hle ⟨n, hn, rfl⟩

theorem M_le_M1 :
    M ≤ T ⊔ borelK M L := by
  intro m hm
  let mM : ↥M := ⟨m, hm⟩
  have hO : X.rho' mM ∈ O4PlusTwo := fun v => X.rho'_quad mM v
  rw [← X.rho_range_eq] at hO
  obtain ⟨m₁, hm₁⟩ := hO
  let m₁M : ↥M := ⟨(m₁ : G), C.M1_le_M m₁.2⟩
  have h1 : X.rho' m₁M = X.rho m₁ := Units.ext (X.rho'_eq_rho m₁)
  have hn : X.rho' (m₁M⁻¹ * mM) = 1 := by
    rw [map_mul, map_inv, h1, hm₁]
    exact inv_mul_cancel _
  have hnP : ((m₁M⁻¹ * mM : ↥M) : G) ∈ borelP M L := X.ker_le_P hn
  have hnM1 : ((m₁M⁻¹ * mM : ↥M) : G) ∈ T ⊔ borelK M L := borelP_le_M1 T M L hnP
  have hm_eq : m = (m₁ : G) * ((m₁M⁻¹ * mM : ↥M) : G) := by
    show m = (m₁ : G) * ((m₁ : G)⁻¹ * m)
    group
  rw [hm_eq]
  exact mul_mem m₁.2 hnM1

theorem M_eq_M1
    : M = T ⊔ borelK M L := le_antisymm X.M_le_M1 C.M1_le_M

theorem rho'_range :
    X.rho'.range = O4PlusTwo := by
  apply le_antisymm
  · rintro _ ⟨m, rfl⟩
    exact fun v => X.rho'_quad m v
  · rw [← X.rho_range_eq]
    rintro _ ⟨m₁, rfl⟩
    exact ⟨⟨(m₁ : G), C.M1_le_M m₁.2⟩, Units.ext (X.rho'_eq_rho m₁)⟩

theorem rho'_ker : X.rho'.ker = (borelP M L).subgroupOf M := by
  ext n
  constructor
  · intro hn
    exact X.ker_le_P hn
  · intro hn
    have hnP : (n : G) ∈ borelP M L := hn
    have hmn : (n : G) ∈ Subgroup.normalizer (borelP M L : Set G) := X.M_le_normalizer_P n.2
    apply Units.ext
    show ((X.rho' n : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1
    apply eq_of_mulVec_eq
    intro v
    rw [Matrix.one_mulVec]
    obtain ⟨q, hq⟩ := X.thG_surj (Multiplicative.ofAdd v)
    have hv : v = Multiplicative.toAdd (X.thG q) := by rw [hq]; rfl
    let p : ↥(borelP M L) := ⟨n, hnP⟩
    let y : ↥(borelP M L) := ⟨(n : G) * q * (n : G)⁻¹, (Subgroup.mem_normalizer_iff.mp hmn q).mp q.2⟩
    have h1 := X.rho'_spec n q y rfl
    have hy : X.thG y = X.thG q := by
      have hyd : y = p * q * p⁻¹ := rfl
      rw [hyd, map_mul, map_mul, map_inv]
      exact (congrArg (· * (X.thG p)⁻¹) (mul_comm (X.thG p) (X.thG q))).trans
        (mul_inv_cancel_right _ _)
    rw [hv, ← h1, hy]

theorem M_card' :
    Nat.card M = 2 ^ 8 * 3 ^ 2 := by
  have hPM : borelP M L ≤ M := (borelP_le_M1 T M L).trans C.M1_le_M
  have hcard := Subgroup.card_ker_mul_card_range X.rho'
  rw [X.rho'_ker, X.rho'_range] at hcard
  have h1 : Nat.card ↥((borelP M L).subgroupOf M) = 32 := by
    rw [← X.card_P]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPM).toEquiv
  have h2 : Nat.card O4PlusTwo = 72 := by
    rw [← X.rho_range_eq]
    exact X.card_range_rho
  rw [h1, h2] at hcard
  rw [← hcard]
  norm_num

theorem M_solvable' :
    Group.IsSolvable ↥M := by
  have hcard := X.M_card'
  let _ : Fintype ↥M := Fintype.ofFinite _
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card]; exact hcard)

theorem exists_u' : ∃ u ∈ centerOf (baum S), u ∉ centerOf (borelP M L) := by
  let g1w : evenWeight 5 := ⟨g1, g1_even⟩
  refine ⟨((C.iV g1w : ↥H) : G), ?_, ?_⟩
  · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (X.mem_R_iff (C.iV g1w)).mpr (by rw [C.pi_iV X.hTC]; exact one_mem _)
    · rw [Subgroup.mem_centralizer_iff]
      intro r hr
      have hrH : r ∈ H := baum_le_H C.hcs hr
      let rH : ↥H := ⟨r, hrH⟩
      have hπ : C.D.π rH ∈ Estd := (X.mem_R_iff rH).mp hr
      have hfix : vact (C.D.π rH) g1w = g1w := Subtype.ext (Eset_fix_g1 _ hπ)
      have hw := X.cw_spec rH
      have hcomm : rH * C.iV g1w = C.iV g1w * rH := by
        rw [hw, X.iV_eq_emb, X.emb_mul, X.emb_mul, hfix, vact_one, mul_one, one_mul, add_comm]
      exact congrArg (fun y : ↥H => (y : G)) hcomm
  · intro h
    rcases (X.centerOf_P_iff _).mp h with h1 | h1
    · apply g1_ne_zero
      have h2 : C.iV g1w = C.iV 0 := by
        rw [C.iV_zero]
        exact Subtype.ext h1
      exact congrArg Subtype.val (C.iV_inj X.hTC h2)
    · apply g1_ne_z0
      have h2 : C.iV g1w = C.iV StdCfg.z0V := Subtype.ext h1
      exact congrArg Subtype.val (C.iV_inj X.hTC h2)

theorem step6
    (h5 : A5Step5 T M H S L) : A5Step6 T M H S L :=
  { toA5Step5 := h5
    M_eq := X.M_eq_M1
    M_cent := X.M_cent_eq
    P_core := X.pCore_M_eq
    M_card := X.M_card'
    M_solvable := X.M_solvable'
    exists_u := X.exists_u' }

end Sec

theorem lemma2_4_29_6
    (h247 : Lemma2_4_27) (h245_4 : Lemma245_4) (hC54 : LemmaC54_3)
    (h314 : A314A5Excluded) : Lemma2_4_29_6 := by
  intro G _ _ T M H S L cfg h5
  obtain ⟨C, ⟨X⟩⟩ := a5_exists_sec h247 h245_4 hC54 h314 cfg
  exact X.step6 h5

end CFSG.QuasithinUnique.A5
