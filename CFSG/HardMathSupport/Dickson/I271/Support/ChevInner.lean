module

public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeDefChar
public import CFSG.LocalAnalysis.GLTheoremA.S3.KData
public import CFSG.LocalAnalysis.GLTheoremA.PartI.Transfer
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.I27_1Gen
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.Pump
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.LocalAnalysis.GLTheoremA CFSG.Yardstones.Md0ec50421ce4

section Transfer

variable {X : Type} [Group X] [Finite X]

@[expose] noncomputable def barOfEquiv (p : ℕ) {K : Subgroup X} (hO : GLAPPrimeCore p ↥K = ⊥) :
    ↥K ≃* barOf p K :=
  MulEquiv.ofBijective (QuotientGroup.mk' (GLAPPrimeCore p ↥K))
    ⟨(MonoidHom.ker_eq_bot_iff _).1 (by rw [QuotientGroup.ker_mk', hO]),
      QuotientGroup.mk'_surjective _⟩

@[expose] noncomputable def autBarToQuot (p : ℕ) {K : Subgroup X} (hO : GLAPPrimeCore p ↥K = ⊥) :
    MulAut (barOf p K) →* MulAut (↥K ⧸ Subgroup.center ↥K) :=
  (autCenterQuot ↥K).comp (MulAut.congr (barOfEquiv p hO)).symm.toMonoidHom

theorem autBarToQuot_injective (p : ℕ) {K : Subgroup X} (hO : GLAPPrimeCore p ↥K = ⊥)
    (hperf : commutator ↥K = ⊤) : Function.Injective (autBarToQuot p hO) :=
  (autCenterQuot_injective_of_perfect hperf).comp (MulAut.congr (barOfEquiv p hO)).symm.injective

theorem autBarToQuot_conj (p : ℕ) {K : Subgroup X} (hO : GLAPPrimeCore p ↥K = ⊥) (q : barOf p K) :
    autBarToQuot p hO (MulAut.conj q) =
      MulAut.conj (QuotientGroup.mk ((barOfEquiv p hO).symm q) : ↥K ⧸ Subgroup.center ↥K) := by
  ext z
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective z
  show autCenterQuot ↥K ((MulAut.congr (barOfEquiv p hO)).symm (MulAut.conj q))
      (QuotientGroup.mk z) = _
  rw [autCenterQuot_mk]
  simp [MulAut.congr_symm_apply, MulAut.conj_apply]

theorem coreFree_of_inner {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hDC : DefCharInnerCoreFree)
    {K : Subgroup X} (hq : CFSG.Open.IsQuasisimple ↥K) (hO : GLAPPrimeCore p ↥K = ⊥)
    (hLie : ∃ idx : TauCeti.ValidLieTypeIndex,
      Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* (TauCeti.CFSGIndex.lie idx).Group) ∧
        idx.1.characteristic = p)
    {H : Subgroup (MulAut (barOf p K))} (hH : innerAut (barOf p K) ≤ H)
    {d : MulAut (barOf p K)} (hd : d ∈ innerAut (barOf p K)) (hdp : orderOf d = p) :
    GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({d} : Set (MulAut (barOf p K)))) = ⊥ := by
  obtain ⟨idx, ⟨e⟩, hchar⟩ := hLie
  set Φ := autBarToQuot p hO with hΦ
  have hΦinj : Function.Injective Φ := autBarToQuot_injective p hO hq.1
  have hinnS : innerAut (↥K ⧸ Subgroup.center ↥K) ≤ H.map Φ := by
    rintro _ ⟨s, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    refine ⟨MulAut.conj (barOfEquiv p hO x), hH ⟨_, rfl⟩, ?_⟩
    rw [hΦ, autBarToQuot_conj]
    simp
  obtain ⟨q, rfl⟩ := hd
  have hx : Φ (MulAut.conj q) ∈ innerAut (↥K ⧸ Subgroup.center ↥K) := by
    rw [hΦ, autBarToQuot_conj]
    exact ⟨_, rfl⟩
  have hxord : orderOf (Φ (MulAut.conj q)) = p := by
    rw [orderOf_injective Φ hΦinj]
    exact hdp
  have hS := hDC (↥K ⧸ Subgroup.center ↥K) hq.2 (exists_noncomm_of_isQuasisimple hq) idx ⟨e⟩ p hp
    hp2 hchar _ hx hxord (H.map Φ) hinnS
  rw [← map_inf_centralizer_of_injective Φ hΦinj,
    ← map_glaPPrimeCoreOf_of_injective p Φ hΦinj] at hS
  exact (Subgroup.map_eq_bot_iff_of_injective _ hΦinj).1 hS

theorem barAut_eq_conj_of_inner {p : ℕ} {K : Subgroup X} {a k : X} (hk : k ∈ K)
    (hc : k⁻¹ * a ∈ Subgroup.centralizer (K : Set X))
    (haN : a ∈ Subgroup.normalizer (K : Set X)) :
    barAut p K ⟨a, haN⟩ = MulAut.conj (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : barOf p K) := by
  ext z
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective z
  rw [barAut_mk]
  show QuotientGroup.mk (K.normalizerMonoidHom ⟨a, haN⟩ z) =
    (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : barOf p K) * QuotientGroup.mk z *
      (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : barOf p K)⁻¹
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  show a * (z : X) * a⁻¹ = k * (z : X) * k⁻¹
  have hcz : (k⁻¹ * a) * (z : X) = (z : X) * (k⁻¹ * a) :=
    (Subgroup.mem_centralizer_iff.1 hc z z.2).symm
  calc a * (z : X) * a⁻¹ = k * ((k⁻¹ * a) * z) * (k⁻¹ * a)⁻¹ * k⁻¹ := by group
    _ = k * (z * (k⁻¹ * a)) * (k⁻¹ * a)⁻¹ * k⁻¹ := by rw [hcz]
    _ = k * z * k⁻¹ := by group

theorem isCompLocallyBalanced_of_inner {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hDC : DefCharInnerCoreFree) {K A : Subgroup X} (hq : CFSG.Open.IsQuasisimple ↥K)
    (hO : GLAPPrimeCore p ↥K = ⊥)
    (hLie : ∃ idx : TauCeti.ValidLieTypeIndex,
      Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* (TauCeti.CFSGIndex.lie idx).Group) ∧
        idx.1.characteristic = p)
    (hAN : A ≤ Subgroup.normalizer (K : Set X))
    (hin : ∀ a ∈ A, ∃ k ∈ K, k⁻¹ * a ∈ Subgroup.centralizer (K : Set X)) :
    IsCompLocallyBalanced p 1 A K := by
  intro D hD H hH hDH
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card D = p := by simpa using hD.2.2
  have hnt : 1 < Nat.card D := by rw [hcard]; exact hp.one_lt
  obtain ⟨d, hdD, hd1⟩ : ∃ d ∈ D, d ≠ 1 := by
    have : Nontrivial D := Finite.one_lt_card_iff_nontrivial.mp hnt
    obtain ⟨⟨d, hd⟩, hne⟩ := exists_ne (1 : D)
    exact ⟨d, hd, fun h => hne (Subtype.ext h)⟩
  have hdp : orderOf d = p := orderOf_eq_prime (hD.2.1.2 d hdD) hd1
  obtain ⟨γ, hγ, rfl⟩ := hD.1 hdD
  obtain ⟨k, hk, hkc⟩ := hin (γ : X) ((Subgroup.mem_subgroupOf.1 hγ).1)
  have hdinner : barAut p K γ ∈ innerAut (barOf p K) := by
    have := barAut_eq_conj_of_inner (p := p) hk hkc γ.2
    rw [show γ = ⟨(γ : X), γ.2⟩ from rfl, this]
    exact ⟨_, rfl⟩
  have key := coreFree_of_inner hp hp2 hDC hq hO hLie hH hdinner hdp
  unfold localDeltaIn
  refine eq_bot_iff.2 ?_
  exact (iInf_le_of_le (barAut p K γ) (iInf_le_of_le hdD (iInf_le _ hd1))).trans key.le

theorem center_eq_bot_of_simple {T : Type*} [Group T] [IsSimpleGroup T]
    (hnc : ∃ a b : T, a * b ≠ b * a) : Subgroup.center T = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a)

theorem not_glaPComponent_of_inner {p : ℕ} (hp : p.Prime) (hKD : KDChevInner p)
    {K : Subgroup X} (hq : CFSG.Open.IsQuasisimple ↥K)
    (hChev : IsChevSimple p (↥K ⧸ Subgroup.center ↥K)) {a k : X} (hk : k ∈ K)
    (hc : k⁻¹ * a ∈ Subgroup.centralizer (K : Set X))
    (hkZ : (⟨k, hk⟩ : ↥K) ∉ Subgroup.center ↥K) (hkp : (⟨k, hk⟩ : ↥K) ^ p ∈ Subgroup.center ↥K)
    {J : Subgroup X} (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J) : False := by
  set k' : ↥K := ⟨k, hk⟩ with hk'
  set π : ↥K →* ↥K ⧸ Subgroup.center ↥K := QuotientGroup.mk' (Subgroup.center ↥K) with hπ
  set α : MulAut ↥K := MulAut.conj k' with hα
  set β : MulAut (↥K ⧸ Subgroup.center ↥K) := MulAut.conj (π k') with hβ
  have hker : π.ker ≤ Subgroup.center ↥K := by rw [hπ, QuotientGroup.ker_mk']
  have hαβ : ∀ y, π (α y) = β (π y) := fun y => by simp [hα, hβ, MulAut.conj_apply]
  have hfix : (K ⊓ Subgroup.centralizer ({a} : Set X)).subgroupOf K = fixSubgroup α := by
    ext y
    rw [Subgroup.mem_subgroupOf, mem_fixSubgroup, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    have hcy : (k⁻¹ * a) * (y : X) = (y : X) * (k⁻¹ * a) :=
      (Subgroup.mem_centralizer_iff.1 hc y y.2).symm
    constructor
    · rintro ⟨-, hy⟩
      apply Subtype.ext
      show k * (y : X) * k⁻¹ = (y : X)
      calc k * (y : X) * k⁻¹ = k * ((k⁻¹ * a) * y) * (k⁻¹ * a)⁻¹ * k⁻¹ := by
            rw [hcy]; group
        _ = a * (y : X) * a⁻¹ := by group
        _ = (y : X) := by rw [← hy]; group
    · intro hy
      refine ⟨y.2, ?_⟩
      have h1 : k * (y : X) * k⁻¹ = (y : X) := congrArg Subtype.val hy
      have hky : k * (y : X) = (y : X) * k := mul_inv_eq_iff_eq_mul.1 h1
      calc (y : X) * a = y * (k * (k⁻¹ * a)) := by group
        _ = (y * k) * (k⁻¹ * a) := by group
        _ = (k * y) * (k⁻¹ * a) := by rw [← hky]
        _ = k * (y * (k⁻¹ * a)) := by group
        _ = k * ((k⁻¹ * a) * y) := by rw [← hcy]
        _ = a * (y : X) := by group
  have hJ' := glaPComponent_subgroupOf hp
    (inf_le_left : K ⊓ Subgroup.centralizer ({a} : Set X) ≤ K) hJ
  rw [hfix] at hJ'
  have hnc := exists_noncomm_of_isQuasisimple hq
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2
  have hSz : Subgroup.center (↥K ⧸ Subgroup.center ↥K) = ⊥ := center_eq_bot_of_simple hnc
  have hβp : β ^ p = 1 := by
    rw [hβ, ← map_pow]
    have : π k' ^ p = 1 := by rw [← map_pow]; exact (QuotientGroup.eq_one_iff _).2 hkp
    rw [this, map_one]
  have hβ1 : β ≠ 1 := by
    intro h
    apply hkZ
    have : π k' ∈ Subgroup.center (↥K ⧸ Subgroup.center ↥K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := DFunLike.congr_fun h g
      simp only [hβ, MulAut.conj_apply, MulAut.one_apply] at this
      exact (mul_inv_eq_iff_eq_mul.1 this).symm
    rw [hSz, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff _).1 this
  have hlay := hKD (↥K ⧸ Subgroup.center ↥K) hq.2 hnc hChev β hβp hβ1 ⟨π k', rfl⟩
  have hmap := map_glaPLayer_fixSubgroup_eq π hker α β hαβ (QuotientGroup.mk'_surjective _) hp
  rw [hlay] at hmap
  have hle : J.subgroupOf K ≤ GLAPLayer p (fixSubgroup α) := le_sSup hJ'
  have hJc : J.subgroupOf K ≤ Subgroup.center ↥K := by
    intro y hy
    have : π y ∈ (GLAPLayer p (fixSubgroup α)).map π := ⟨y, hle hy, rfl⟩
    rw [hmap, Subgroup.mem_bot] at this
    exact hker ((MonoidHom.mem_ker).2 this)
  have hperf := glaPComponent_perfect hJ'
  have hbot : ⁅J.subgroupOf K, J.subgroupOf K⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hJc.trans (Subgroup.center_le_centralizer _))
  rw [hbot] at hperf
  exact glaPComponent_ne_bot' hJ' hperf.symm

end Transfer

end CFSG.HardMathSupport.Dickson.I271
