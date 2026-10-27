module

public import CFSG.LocalAnalysis.ComponentClassification.Foote47L216Config
public import CFSG.LocalAnalysis.ComponentClassification.Foote47P4Common
public import CFSG.LocalAnalysis.ComponentClassification.Foote47L216AbelianKernel

public section

namespace CFSG.ComponentClassification.Foote47L216

open scoped MatrixGroups

open CFSG Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Foote47

variable {G : Type} [Group G] [Finite G]

namespace ActualConf

variable {M T S P : Subgroup G} {t z w g : G}

omit [Finite G] in
theorem T_le_S (c : ActualConf M T S P t z) : T ≤ S := c.hT ▸ inf_le_left

omit [Finite G] in
theorem P_le_S (c : ActualConf M T S P t z) : P ≤ S := c.hP ▸ inf_le_left

omit [Finite G] in
theorem z_comm (c : ActualConf M T S P t z) {s : G} (hs : s ∈ S) : s * z = z * s :=
  mem_centralizer_singleton_iff.mp (c.hSz.le hs)

omit [Finite G] in
theorem t_comm (c : ActualConf M T S P t z) {s : G} (hs : s ∈ P) : s * t = t * s := by
  rw [c.hP] at hs
  exact mem_centralizer_singleton_iff.mp (mem_inf.mp hs).2

omit [Finite G] in
theorem t_mem_P (c : ActualConf M T S P t z) : t ∈ P := by
  rw [c.hP]
  exact mem_inf.mpr ⟨T_le_S c c.htT, mem_centralizer_singleton_iff.mpr rfl⟩

omit [Finite G] in
theorem z_mem_P (c : ActualConf M T S P t z) : z ∈ P := by
  obtain ⟨Q₀, hd⟩ := c.hd
  rw [c.hP]
  exact mem_inf.mpr ⟨T_le_S c hd.hzT,
    mem_centralizer_singleton_iff.mpr (hd.hzc t c.htT).symm⟩

omit [Finite G] in
theorem w_mem_P (c : ActualConf M T S P t z) {w : G} (hwS : w ∈ S)
    (hwc : ∀ s ∈ S, s * w = w * s) : w ∈ P := by
  rw [c.hP]
  exact mem_inf.mpr ⟨hwS,
    mem_centralizer_singleton_iff.mpr (hwc t (T_le_S c c.htT)).symm⟩

omit [Finite G] in
theorem Q_le_P (c : ActualConf M T S P t z) :
    T ⊓ centralizer ({t} : Set G) ≤ P := by
  rw [← c.hQP]
  exact inf_le_left

theorem T_le_coreActionKernel_Kz (c : ActualConf M T S P t z) (hY : YSupplier G) :
    T ≤ coreActionKernel (K z) := by
  obtain ⟨Q₀, hd⟩ := c.hd
  intro x hx
  have hzC : z ∈ coreActionKernel M := c.hTsyl.le hd.hzT
  exact coreActionKernel_inf_centralizer_le hY c.hv.hM hd.hz hzC
    (mem_inf.mpr ⟨c.hTsyl.le hx, mem_centralizer_singleton_iff.mpr (hd.hzc x hx)⟩)

theorem P_le_normalizer_Kt (c : ActualConf M T S P t z) :
    P ≤ normalizer (K t : Set G) :=
  c.hPsyl.le.trans (Sol76.le_normalizer_solomonKStarOf (centralizer ({t} : Set G)))

theorem P_le_normalizer_Q (c : ActualConf M T S P t z) :
    P ≤ normalizer ((T ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) := by
  intro p hp
  rw [← c.hQP]
  exact mem_normalizer_inf' (le_normalizer hp)
    (mem_normalizer_coreActionKernel (P_le_normalizer_Kt c hp))

theorem P_le_centralizer_z (c : ActualConf M T S P t z) :
    P ≤ centralizer ({z} : Set G) := by
  obtain ⟨Q₀, hd⟩ := c.hd
  have htt : t * t = 1 := by
    rw [← sq, ← c.hv.ht]; exact pow_orderOf_eq_one t
  exact (P_le_normalizer_Q c).trans (hd.normalizer_le_centralizer htt)

theorem P_inf_coreActionKernel_Kz (c : ActualConf M T S P t z) :
    P ⊓ coreActionKernel (K z) = T ⊓ centralizer ({t} : Set G) := by
  refine c.hQX.eq_of_le ?_ ?_ (c.hPsyl.isPGroup.to_le inf_le_left)
  · exact le_inf (Q_le_P c) (c.hQX.le.trans inf_le_right)
  · intro x hx
    have hxP : x ∈ P := (mem_inf.mp hx).1
    exact mem_inf.mpr ⟨mem_inf.mpr ⟨P_le_centralizer_z c hxP, c.hPsyl.le hxP⟩,
      (mem_inf.mp hx).2⟩

omit [Finite G] in
theorem center_eq_bot_Kt
    (eKt : K t ⧸ pPrimeCore 2 (K t) ≃* PSL(2, GaloisField 2 4)) :
    center (K t ⧸ pPrimeCore 2 (K t)) = ⊥ :=
  GorensteinWalter.center_eq_bot_of_mulEquiv eKt
    (GorensteinWalter.psl2_center_eq_bot (GaloisField 2 4))

theorem eq_one_of_mem_Q_Kt_of_center_eq_bot (c : ActualConf M T S P t z)
    (hZ : center (K t ⧸ pPrimeCore 2 (K t)) = ⊥) {x : G}
    (hxQ : x ∈ T ⊓ centralizer ({t} : Set G)) (hxF : x ∈ K t) : x = 1 := by
  have hxO := mem_oddCoreIn_of_mem_coreActionKernel hZ hxF (c.hQF hxQ)
  exact eq_one_of_mem_of_odd (c.hPsyl.isPGroup.to_le (Q_le_P c))
    (odd_card_oddCoreIn _) hxQ hxO

theorem eq_one_of_mem_Q_Kt (c : ActualConf M T S P t z)
    (eKt : K t ⧸ pPrimeCore 2 (K t) ≃* PSL(2, GaloisField 2 4)) {x : G}
    (hxQ : x ∈ T ⊓ centralizer ({t} : Set G)) (hxF : x ∈ K t) : x = 1 :=
  eq_one_of_mem_Q_Kt_of_center_eq_bot c (center_eq_bot_Kt eKt) hxQ hxF

theorem Q_inf_Kt_eq_bot (c : ActualConf M T S P t z)
    (eKt : K t ⧸ pPrimeCore 2 (K t) ≃* PSL(2, GaloisField 2 4)) :
    (T ⊓ centralizer ({t} : Set G)) ⊓ K t = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxQ, hxF⟩ := mem_inf.mp hx
  exact eq_one_of_mem_Q_Kt c eKt hxQ hxF

theorem isSylowOf_R_Kt (c : ActualConf M T S P t z)
    (hKt : IsTwoComponentAt t (K t)) :
    IsSylowOf 2 (P ⊓ K t) (K t) :=
  c.hPsyl.inf_of_le_normalizer hKt.2.1
    (Sol76.le_normalizer_solomonKStarOf (centralizer ({t} : Set G)))

theorem R_isElemAbelian_card_sixteen (c : ActualConf M T S P t z)
    (hKt : IsTwoComponentAt t (K t))
    (eKt : K t ⧸ pPrimeCore 2 (K t) ≃* PSL(2, GaloisField 2 4)) :
    CFSG.Open.IsElemAbelian 2 (P ⊓ K t) ∧ Nat.card ↥(P ⊓ K t) = 16 := by
  have hR : IsSylowOf 2 (P ⊓ K t) (K t) := isSylowOf_R_Kt c hKt
  obtain ⟨S, hS, hPS⟩ := exists_isSylowOf_ge_of_le (P_le_normalizer_Kt c) c.hPsyl.isPGroup
  have hSinf : IsSylowOf 2 (S ⊓ K t) (K t) :=
    hS.inf_of_le_normalizer le_normalizer le_rfl
  have hRle : P ⊓ K t ≤ S ⊓ K t := inf_le_inf hPS le_rfl
  have hSeq : S ⊓ K t = P ⊓ K t :=
    hR.eq_of_le hRle inf_le_right hSinf.isPGroup
  have hdata := sylow_odd_quotient_data (K t) S eKt hS
  rwa [hSeq] at hdata

theorem pRank_R_eq_four (c : ActualConf M T S P t z)
    (hKt : IsTwoComponentAt t (K t))
    (eKt : K t ⧸ pPrimeCore 2 (K t) ≃* PSL(2, GaloisField 2 4)) :
    CFSG.Open.pRank 2 (P ⊓ K t) = 4 := by
  obtain ⟨hE, hcard⟩ := R_isElemAbelian_card_sixteen c hKt eKt
  apply le_antisymm
  · refine CFSG.SectionRank.pRank_le (p := 2) (by norm_num)
      (H := P ⊓ K t) (k := 4) ?_
    intro E hER _
    calc Nat.card ↥E ≤ Nat.card ↥(P ⊓ K t) := Subgroup.card_le_of_le hER
      _ = 16 := hcard
      _ = 2 ^ 4 := by norm_num
  · have h := CFSG.SectionRank.le_pRank (p := 2) (by norm_num)
      (H := P ⊓ K t) (E := P ⊓ K t) le_rfl hE (k := 4) (by rw [hcard]; norm_num)
    simpa using h

theorem comm_QR (c : ActualConf M T S P t z) {q r : G}
    (hq : q ∈ T ⊓ centralizer ({t} : Set G)) (hr : r ∈ P ⊓ K t) : q * r = r * q :=
  GrSLit.GrS5.commute_of_mem_coreActionKernel c.hPsyl.isPGroup (Q_le_P c hq)
    (c.hQF hq) (mem_inf.mp hr).1 (mem_inf.mp hr).2

omit [Finite G] in
theorem not_isConj_t_z_of_ht2c (c : ActualConf M T S P t z)
    (ht2c : ∀ x ∈ S, (∀ s ∈ S, s * x = x * s) → ¬ IsConj t x) :
    ¬ IsConj t z := by
  obtain ⟨Q₀, hd⟩ := c.hd
  exact ht2c z (T_le_S c hd.hzT) fun s hs => z_comm c hs

theorem valid_not_mem_centralizer (c : ActualConf M T S P t z) (hY : YSupplier G)
    {w g : G} (htz : ¬ IsConj t z) (hg : Valid P t z w g) :
    g ∉ centralizer ({z} : Set G) := by
  obtain ⟨Q₀, hd⟩ := c.hd
  exact P4Data.Valid.not_mem_centralizer_of_twoData (F := K z) hd c.hv.ht c.htT
    (T_le_coreActionKernel_Kz c hY) (P_inf_coreActionKernel_Kz c)
    (centralizer_le_normalizer_K z) htz hg

theorem valid_tstar_ne (c : ActualConf M T S P t z)
    {w g : G} (htz : ¬ IsConj t z) (hg : Valid P t z w g) :
    g * t * g⁻¹ ≠ t ∧ g * t * g⁻¹ ≠ t * z := by
  obtain ⟨Q₀, hd⟩ := c.hd
  exact P4Data.Valid.tstar_ne_of_twoData (F := K t) hd c.hv.ht c.htT (t_mem_P c)
    c.hQF c.hQP (centralizer_le_normalizer_K t) htz hg

end ActualConf

end CFSG.ComponentClassification.Foote47L216
