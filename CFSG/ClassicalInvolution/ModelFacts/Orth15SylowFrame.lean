module

public import CFSG.ClassicalInvolution.Asc77.WP3LayerSec
import CFSG.ClassicalInvolution.Asc77.AscE187Img
import CFSG.ClassicalInvolution.Asc77.WP3FrameData
public import CFSG.ClassicalInvolution.Asc77.AscT7AHyp51

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

section Normalized

theorem exists_twinSylow_normalized (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K K' : Subgroup G} {z : G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K) {A : Subgroup G} (hA2 : IsPGroup 2 A)
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hAK' : A ≤ Subgroup.normalizer (K' : Set G)) :
    ∃ R R' : Subgroup G, IsSylow2In R K ∧ IsSylow2In R' K' ∧ Commutes R R' ∧
      (∀ a ∈ A, conjSub a R = R) ∧ (∀ a ∈ A, conjSub a R' = R') ∧
        IsPGroup 2 ↥((A ⊔ R) ⊔ R') := by
  have hK'Ω : K' ∈ Ω := hK'.1
  obtain ⟨R, hRsyl, hRfix⟩ := exists_sylow_normalized hA2 hAK
  have hRset : R ∈ RSet Ω := mem_RSet_of_isSylow2In hK hRsyl
  have hAnR : A ≤ Subgroup.normalizer (R : Set G) := fun t ht =>
    mem_normalizer_iff_conjSub_eq.mpr (hRfix t ht)
  have hAR2 : IsPGroup 2 ↥(A ⊔ R) := hA2.to_sup_of_normal_right' hRsyl.2.1 hAnR
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hK'
  have hKN : K ≤ Subgroup.normalizer (K' : Set G) :=
    hΩ.le_normalizer_of_twin hK hK'Ω hne.symm hz hzK'
  have hPN : A ⊔ R ≤ Subgroup.normalizer (K' : Set G) := sup_le hAK' (hRsyl.1.trans hKN)
  obtain ⟨R', hR'syl, hR'fix⟩ := exists_sylow_normalized hAR2 hPN
  have hR'set : R' ∈ RSet Ω := mem_RSet_of_isSylow2In hK'Ω hR'syl
  have hPnR' : A ⊔ R ≤ Subgroup.normalizer (R' : Set G) := fun t ht =>
    mem_normalizer_iff_conjSub_eq.mpr (hR'fix t ht)
  have hQ2 : IsPGroup 2 ↥((A ⊔ R) ⊔ R') := hAR2.to_sup_of_normal_right' hR'syl.2.1 hPnR'
  obtain ⟨S, hS⟩ := hQ2.exists_le_sylow
  have hRS : R ≤ (S : Subgroup G) := le_sup_right.trans (le_sup_left.trans hS)
  have hR'S : R' ≤ (S : Subgroup G) := le_sup_right.trans hS
  have hRR' : R ≠ R' := by
    intro h
    have := hΩ.card_le_two_of_le_inf hK hK'Ω hne.symm hRsyl.2.1 hRsyl.1 (h ▸ hR'syl.1)
    have := hΩ.eight_le_of_mem_RSet hp hRset
    omega
  exact ⟨R, R', hRsyl, hR'syl,
    l6_7_proved p f hp hq G Ω hΩ S R hRset R' hR'set hRS hR'S hRR', hRfix,
    fun a ha => hR'fix a (Subgroup.mem_sup_left ha), hQ2⟩

end Normalized

section Frame

theorem sq_eq_one_of_natCard_le_two {A : Subgroup G} (h : Nat.card A ≤ 2) {w : G} (hw : w ∈ A) :
    w * w = 1 := by
  have hd : orderOf w ∣ Nat.card A := by
    exact Subgroup.orderOf_dvd_natCard A hw
  have hpos : 0 < Nat.card A := Nat.card_pos
  have h2 : orderOf w ∣ 2 := by
    rcases (by omega : Nat.card A = 1 ∨ Nat.card A = 2) with h1 | h1
    · rw [h1] at hd
      exact hd.trans (one_dvd 2)
    · rwa [h1] at hd
  rw [← pow_two]
  exact orderOf_dvd_iff_pow_eq_one.mp h2

theorem TwinFrameData.tq_t_K (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K K' J : Subgroup G} {z u t : G} (hd : TwinFrameData Ω K K' z u J t) :
    t ∈ trivialOnQuot K := by
  have hJK : J ∈ omegaNbr Ω K := hd.hJ.2 K (mem_twinSet_self hd.mem hd.hz)
  have hKJ : K ∈ omegaNbr Ω J := T3.omegaNbr_symm (l6_2 p f) hp hq hΩ hd.mem hd.hJ.1 hJK
  obtain ⟨a, ha, hKa⟩ := tq_of_mem_omegaNbr hp hq hΩ.classical hd.hJ.1 hKJ
  have hat : a = t := (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq ha).eq hd.ht
  exact (mem_trivialOnQuot_iff_actsTrivOnQuot (J := K)).mpr (hat ▸ hKa)

theorem TwinFrameData.tq_t_K' (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K K' J : Subgroup G} {z u t : G} (hd : TwinFrameData Ω K K' z u J t) :
    t ∈ trivialOnQuot K' := by
  have hJK' : J ∈ omegaNbr Ω K' := hd.hJ.2 K' hd.hK'
  have hKJ : K' ∈ omegaNbr Ω J := T3.omegaNbr_symm (l6_2 p f) hp hq hΩ hd.hK'.1 hd.hJ.1 hJK'
  obtain ⟨a, ha, hKa⟩ := tq_of_mem_omegaNbr hp hq hΩ.classical hd.hJ.1 hKJ
  have hat : a = t := (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq ha).eq hd.ht
  exact (mem_trivialOnQuot_iff_actsTrivOnQuot (J := K')).mpr (hat ▸ hKa)

theorem TwinFrameSettingCore.exists_sylow_frame {K K' J : Subgroup G} {z u t : G}
    (hs : TwinFrameSettingCore p f Ω K K' J z u t) :
    ∃ R R' : Subgroup G, IsSylow2In R K ∧ IsSylow2In R' K' ∧ Commutes R R' ∧
      (∀ r ∈ R, r * t = t * r) ∧ (∀ r ∈ R', r * t = t * r) ∧
        ∃ x ∈ R, ∃ y ∈ R', x * x = z ∧ y * y = z ∧ x * y = u := by
  have hp : p ≠ 2 := hs.odd
  have hq : 5 ≤ p ^ f := hs.five
  have hΩ := hs.hyp
  have hd := hs.frame
  have hK : K ∈ Ω := hd.mem
  have hK'Ω : K' ∈ Ω := hd.hK'.1
  have hz := hd.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hd.hK'
  have hne : K' ≠ K := hd.hne
  have hKN' : K ≤ Subgroup.normalizer (K' : Set G) :=
    hΩ.le_normalizer_of_twin hK hK'Ω hne.symm hz hzK'
  have hK'N : K' ≤ Subgroup.normalizer (K : Set G) :=
    hΩ.le_normalizer_of_twin hK'Ω hK hne hzK' hz
  have htK : t ∈ trivialOnQuot K := hd.tq_t_K hp hq hΩ
  have htK' : t ∈ trivialOnQuot K' := hd.tq_t_K' hp hq hΩ
  have hB := twinFrame_isElemAbelian hp hΩ hd
  have hA2 : IsPGroup 2 (Subgroup.closure ({z, u, t} : Set G)) :=
    CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup 2 _ hB
  have huN : u ∈ Subgroup.normalizer (K : Set G) :=
    (sup_le (Subgroup.le_normalizer) hK'N) hd.hu
  have huN' : u ∈ Subgroup.normalizer (K' : Set G) :=
    (sup_le hKN' (Subgroup.le_normalizer)) hd.hu
  have hAK : Subgroup.closure ({z, u, t} : Set G) ≤ Subgroup.normalizer (K : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact Subgroup.le_normalizer hz.mem
    · exact huN
    · exact htK.1
  have hAK' : Subgroup.closure ({z, u, t} : Set G) ≤ Subgroup.normalizer (K' : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact Subgroup.le_normalizer hzK'.mem
    · exact huN'
    · exact htK'.1
  obtain ⟨R, R', hRsyl, hR'syl, hcomm, hRfix, hR'fix, hQ2⟩ := exists_twinSylow_normalized hp hq hΩ
    hK hz hd.hK' hne hA2 hAK hAK'
  have htA : t ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.subset_closure (by simp)
  have huA : u ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.subset_closure (by simp)
  have hRR' : IsSylow2In (R ⊔ R') (K ⊔ K') :=
    T7A.isSylow2In_sup_of_twin hp hΩ hK hK'Ω hne hz hzK' hRsyl hR'syl hcomm
  have huRR' : u ∈ R ⊔ R' := by
    set Q : Subgroup G := (Subgroup.closure ({z, u, t} : Set G) ⊔ R) ⊔ R' with hQ
    have hle : R ⊔ R' ≤ Q ⊓ (K ⊔ K') :=
      le_inf (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
        (sup_le_sup hRsyl.1 hR'syl.1)
    have h1 : Q ⊓ (K ⊔ K') = R ⊔ R' :=
      hRR'.2.2 (Q ⊓ (K ⊔ K')) inf_le_right hQ2.to_inf_left hle
    rw [← h1]
    exact ⟨(le_sup_left.trans le_sup_left : Subgroup.closure ({z, u, t} : Set G) ≤ Q) huA, hd.hu⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := AscE186.exists_mul_of_mem_sup_of_commutes hcomm huRR'
  have hcent : ∀ {L R₀ : Subgroup G}, IsSylow2In R₀ L → t ∈ trivialOnQuot L →
      (∀ a ∈ Subgroup.closure ({z, u, t} : Set G), conjSub a R₀ = R₀) →
        ∀ r ∈ R₀, r * t = t * r := by
    intro L R₀ hR₀ htL hfix r hr
    have h1 : t * r * t⁻¹ ∈ R₀ := by
      have := conj_mem_conjSub (n := t) hr
      rwa [hfix t htA] at this
    have h2 : t * r * t⁻¹ * r⁻¹ ∈ R₀ := R₀.mul_mem h1 (R₀.inv_mem hr)
    have h3 : t * r * t⁻¹ * r⁻¹ ∈ oddCoreIn L := by
      have := htL.2 r (hR₀.1 hr)
      rwa [commutatorElement_def] at this
    have h4 : IsPGroup 2 (Subgroup.zpowers (t * r * t⁻¹ * r⁻¹)) :=
      hR₀.2.1.to_le (Subgroup.zpowers_le.mpr h2)
    have h5 : t * r * t⁻¹ * r⁻¹ = 1 :=
      eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard L) h3 h4
    have h6 : t * r * t⁻¹ = r := by
      have := congrArg (fun w => w * r) h5
      simpa using this
    calc r * t = t * r * t⁻¹ * t := by rw [h6]
      _ = t * r := by group
  refine ⟨R, R', hRsyl, hR'syl, hcomm, hcent hRsyl htK hRfix, hcent hR'syl htK' hR'fix, x, hx,
    y, hy, ?_⟩
  have hu2 : u * u = 1 := hd.hu2
  have hxy2 : (x * x) * (y * y) = 1 := by
    have hc : x * y = y * x := hcomm x hx y hy
    calc (x * x) * (y * y) = x * (x * y) * y := by group
      _ = x * (y * x) * y := by rw [hc]
      _ = (x * y) * (x * y) := by group
      _ = 1 := by rw [hxy, hu2]
  have hw : x * x ∈ R ⊓ R' := by
    refine ⟨R.mul_mem hx hx, ?_⟩
    have : x * x = (y * y)⁻¹ := eq_inv_of_mul_eq_one_left hxy2
    rw [this]
    exact R'.inv_mem (R'.mul_mem hy hy)
  have hcard : Nat.card ↥(R ⊓ R') ≤ 2 :=
    hΩ.card_le_two_of_le_inf hK hK'Ω hne.symm (hRsyl.2.1.to_le inf_le_left)
      (inf_le_left.trans hRsyl.1) (inf_le_right.trans hR'syl.1)
  have hww : (x * x) * (x * x) = 1 := sq_eq_one_of_natCard_le_two hcard hw
  have hyy : y * y = x * x := by
    have : (y * y) = (x * x)⁻¹ := eq_inv_of_mul_eq_one_right hxy2
    rw [this]
    exact inv_eq_of_mul_eq_one_right hww
  rcases hz.unique (x * x) (K.mul_mem (hRsyl.1 hx) (hRsyl.1 hx)) hww with h1 | h1
  ·
    exfalso
    have hx2 : x = 1 ∨ x = z := hz.unique x (hRsyl.1 hx) h1
    have hy2 : y = 1 ∨ y = z := hzK'.unique y (hR'syl.1 hy) (by rw [hyy, h1])
    rcases hx2 with rfl | rfl <;> rcases hy2 with rfl | rfl
    · exact hd.hu1 (by rw [← hxy, one_mul])
    · exact hd.huz (by rw [← hxy, one_mul])
    · exact hd.huz (by rw [← hxy, mul_one])
    · exact hd.hu1 (by rw [← hxy]; exact hz.sq)
  · exact ⟨h1, hyy.trans h1, hxy⟩

theorem TwinFrameSetting.exists_sylow_frame {K K' J : Subgroup G} {z u t : G}
    (hs : TwinFrameSetting p f Ω K K' J z u t) :
    ∃ R R' : Subgroup G, IsSylow2In R K ∧ IsSylow2In R' K' ∧ Commutes R R' ∧
      (∀ r ∈ R, r * t = t * r) ∧ (∀ r ∈ R', r * t = t * r) ∧
        ∃ x ∈ R, ∃ y ∈ R', x * x = z ∧ y * y = z ∧ x * y = u :=
  hs.toCore.exists_sylow_frame

section CData

variable {K K' J : Subgroup G} {z u t c : G}

theorem TwinFrameSettingCore.tq_c_K (hs : TwinFrameSettingCore p f Ω K K' J z u t)
    (hc : c = t ∨ c = t * z) : c ∈ trivialOnQuot K := by
  have htK : t ∈ trivialOnQuot K := hs.frame.tq_t_K hs.odd hs.five hs.hyp
  have hzK : z ∈ trivialOnQuot K :=
    trivialOnQuot_of_isUniqueInvolution hs.odd hs.five hs.hyp hs.frame.mem hs.frame.hz
  rcases hc with hc | hc
  · rw [hc]
    exact htK
  · rw [hc]
    exact Subgroup.mul_mem _ htK hzK

theorem TwinFrameSetting.tq_c_K (hs : TwinFrameSetting p f Ω K K' J z u t)
    (hc : c = t ∨ c = t * z) : c ∈ trivialOnQuot K :=
  hs.toCore.tq_c_K hc

theorem TwinFrameSettingCore.tq_c_K' (hs : TwinFrameSettingCore p f Ω K K' J z u t)
    (hc : c = t ∨ c = t * z) : c ∈ trivialOnQuot K' := by
  have htK' : t ∈ trivialOnQuot K' := hs.frame.tq_t_K' hs.odd hs.five hs.hyp
  have hzK' : z ∈ trivialOnQuot K' :=
    trivialOnQuot_of_isUniqueInvolution hs.odd hs.five hs.hyp hs.frame.hK'.1
      (isUniqueInvolution_of_mem_twinSet hs.frame.hz hs.frame.hK')
  rcases hc with hc | hc
  · rw [hc]
    exact htK'
  · rw [hc]
    exact Subgroup.mul_mem _ htK' hzK'

theorem TwinFrameSetting.tq_c_K' (hs : TwinFrameSetting p f Ω K K' J z u t)
    (hc : c = t ∨ c = t * z) : c ∈ trivialOnQuot K' :=
  hs.toCore.tq_c_K' hc

theorem TwinFrameSettingCore.c_sq (hs : TwinFrameSettingCore p f Ω K K' J z u t)
    (hc : c = t ∨ c = t * z) : c * c = 1 := by
  rcases hc with hc | hc
  · rw [hc]
    exact hs.frame.ht.sq
  · rw [hc]
    exact mul_involution_of_commute hs.frame.ht.sq hs.frame.hz.sq
      (hs.frame.comm_zt hs.odd hs.hyp).symm

theorem TwinFrameSetting.c_sq (hs : TwinFrameSetting p f Ω K K' J z u t)
    (hc : c = t ∨ c = t * z) : c * c = 1 :=
  hs.toCore.c_sq hc

theorem TwinFrameSettingCore.isPGroup_zpowers_c (hs : TwinFrameSettingCore p f Ω K K' J z u t)
    (hc : c = t ∨ c = t * z) : IsPGroup 2 (Subgroup.zpowers c) :=
  isPGroup_zpowers_of_sq_eq_one (hs.c_sq hc)

theorem TwinFrameSetting.isPGroup_zpowers_c (hs : TwinFrameSetting p f Ω K K' J z u t)
    (hc : c = t ∨ c = t * z) : IsPGroup 2 (Subgroup.zpowers c) :=
  isPGroup_zpowers_of_sq_eq_one (hs.c_sq hc)

omit [Finite G] in
theorem mem_closure_of_eq_or_eq_mul {z u t c : G} (hc : c = t ∨ c = t * z) :
    c ∈ Subgroup.closure ({z, u, t} : Set G) := by
  have hz : z ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.subset_closure (by simp)
  have ht : t ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.subset_closure (by simp)
  rcases hc with hc | hc
  · rw [hc]
    exact ht
  · rw [hc]
    exact Subgroup.mul_mem _ ht hz

theorem TwinFrameSettingCore.c_ne_one (hs : TwinFrameSettingCore p f Ω K K' J z u t)
    (hc : c = t ∨ c = t * z) : c ≠ 1 := by
  rcases hc with hc | hc
  · rw [hc]
    exact hs.frame.ht.ne_one
  · rw [hc]
    intro h
    apply hs.frame.t_ne_z
    exact (eq_inv_of_mul_eq_one_left h).trans (inv_eq_of_mul_eq_one_right hs.frame.hz.sq)

theorem TwinFrameSetting.c_ne_one (hs : TwinFrameSetting p f Ω K K' J z u t)
    (hc : c = t ∨ c = t * z) : c ≠ 1 :=
  hs.toCore.c_ne_one hc

theorem TwinFrameSettingCore.z_ne_c (hs : TwinFrameSettingCore p f Ω K K' J z u t)
    (hc : c = t ∨ c = t * z) : z ≠ c := by
  rcases hc with hc | hc
  · rw [hc]
    exact fun h => hs.frame.t_ne_z h.symm
  · rw [hc]
    intro h
    apply hs.frame.ht.ne_one
    have : z = t * z := h
    exact (mul_eq_right.mp this.symm)

theorem TwinFrameSetting.z_ne_c (hs : TwinFrameSetting p f Ω K K' J z u t)
    (hc : c = t ∨ c = t * z) : z ≠ c :=
  hs.toCore.z_ne_c hc

theorem TwinFrameSettingCore.comm_u_c (hs : TwinFrameSettingCore p f Ω K K' J z u t)
    (hc : c = t ∨ c = t * z) : u * c = c * u := by
  have htu : t * u = u * t := hs.frame.htu
  have hzu : z * u = u * z := hs.frame.comm_zu
  rcases hc with hc | hc
  · rw [hc]
    exact htu.symm
  · rw [hc]
    calc u * (t * z) = (u * t) * z := by group
      _ = (t * u) * z := by rw [htu]
      _ = t * (u * z) := by group
      _ = t * (z * u) := by rw [hzu]
      _ = (t * z) * u := by group

theorem TwinFrameSetting.comm_u_c (hs : TwinFrameSetting p f Ω K K' J z u t)
    (hc : c = t ∨ c = t * z) : u * c = c * u :=
  hs.toCore.comm_u_c hc

theorem TwinFrameSettingCore.comm_t_c (hs : TwinFrameSettingCore p f Ω K K' J z u t)
    (hc : c = t ∨ c = t * z) : t * c = c * t := by
  have hzt : z * t = t * z := hs.frame.comm_zt hs.odd hs.hyp
  rcases hc with hc | hc
  · rw [hc]
  · rw [hc]
    calc t * (t * z) = t * (z * t) := by rw [hzt]
      _ = (t * z) * t := by group

theorem TwinFrameSetting.comm_t_c (hs : TwinFrameSetting p f Ω K K' J z u t)
    (hc : c = t ∨ c = t * z) : t * c = c * t :=
  hs.toCore.comm_t_c hc

end CData

theorem TwinFrameSettingCore.exists_sylow_frame_at {K K' J : Subgroup G} {z u t c : G}
    (hs : TwinFrameSettingCore p f Ω K K' J z u t) (hc : c = t ∨ c = t * z) :
    ∃ R R' : Subgroup G, IsSylow2In R (exactCore c K) ∧ IsSylow2In R' (exactCore c K') ∧
      Commutes R R' ∧ (∀ r ∈ R, r * c = c * r) ∧ (∀ r ∈ R', r * c = c * r) ∧
        ∃ x ∈ R, ∃ y ∈ R', x * x = z ∧ y * y = z ∧ x * y = u := by
  have hΩ := hs.hyp
  have hd := hs.frame
  have hK : K ∈ Ω := hd.mem
  have hK'Ω : K' ∈ Ω := hd.hK'.1
  have hz := hd.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hd.hK'
  have hcK : IsClassicalMember p f K z := isClassicalMember_of_twin hΩ hK hz
  have hcK' : IsClassicalMember p f K' z := isClassicalMember_of_twin hΩ hK'Ω hzK'
  have hKz : K ≤ Subgroup.centralizer ({z} : Set G) := isSubnormal_le hcK.subnormal
  have hK'z : K' ≤ Subgroup.centralizer ({z} : Set G) := isSubnormal_le hcK'.subnormal
  have hc2 := hs.isPGroup_zpowers_c hc
  obtain ⟨R, R', hRsyl, hR'syl, hcomm, hRt, hR't, x, hx, y, hy, hx2, hy2, hxy⟩ :=
    hs.exists_sylow_frame
  have hcomm_c : ∀ {L R₀ : Subgroup G}, R₀ ≤ L → L ≤ Subgroup.centralizer ({z} : Set G) →
      (∀ r ∈ R₀, r * t = t * r) → ∀ r ∈ R₀, r * c = c * r := by
    intro L R₀ hRL hLz hRt r hr
    have hrz : r * z = z * r := Subgroup.mem_centralizer_singleton_iff.mp (hLz (hRL hr))
    rcases hc with hc | hc
    · rw [hc]
      exact hRt r hr
    · rw [hc]
      calc r * (t * z) = (r * t) * z := by group
        _ = (t * r) * z := by rw [hRt r hr]
        _ = t * (r * z) := by group
        _ = t * (z * r) := by rw [hrz]
        _ = (t * z) * r := by group
  have hRc : ∀ r ∈ R, r * c = c * r := hcomm_c hRsyl.1 hKz hRt
  have hR'c : ∀ r ∈ R', r * c = c * r := hcomm_c hR'syl.1 hK'z hR't
  have hRsyl' : IsSylow2In R (exactCore c K) :=
    (isSylow2In_exactCore_iff hΩ hc2 hK (hs.tq_c_K hc)).mpr ⟨hRsyl, fun r hr =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hRc r hr)⟩
  have hR'syl' : IsSylow2In R' (exactCore c K') :=
    (isSylow2In_exactCore_iff hΩ hc2 hK'Ω (hs.tq_c_K' hc)).mpr ⟨hR'syl, fun r hr =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hR'c r hr)⟩
  exact ⟨R, R', hRsyl', hR'syl', hcomm, hRc, hR'c, x, hx, y, hy, hx2, hy2, hxy⟩

theorem TwinFrameSetting.exists_sylow_frame_at {K K' J : Subgroup G} {z u t c : G}
    (hs : TwinFrameSetting p f Ω K K' J z u t) (hc : c = t ∨ c = t * z) :
    ∃ R R' : Subgroup G, IsSylow2In R (exactCore c K) ∧ IsSylow2In R' (exactCore c K') ∧
      Commutes R R' ∧ (∀ r ∈ R, r * c = c * r) ∧ (∀ r ∈ R', r * c = c * r) ∧
        ∃ x ∈ R, ∃ y ∈ R', x * x = z ∧ y * y = z ∧ x * y = u := by
  have hΩ := hs.hyp
  have hd := hs.frame
  have hK : K ∈ Ω := hd.mem
  have hK'Ω : K' ∈ Ω := hd.hK'.1
  have hz := hd.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hd.hK'
  have hcK : IsClassicalMember p f K z := isClassicalMember_of_twin hΩ hK hz
  have hcK' : IsClassicalMember p f K' z := isClassicalMember_of_twin hΩ hK'Ω hzK'
  have hKz : K ≤ Subgroup.centralizer ({z} : Set G) := isSubnormal_le hcK.subnormal
  have hK'z : K' ≤ Subgroup.centralizer ({z} : Set G) := isSubnormal_le hcK'.subnormal
  have hc2 := hs.isPGroup_zpowers_c hc
  obtain ⟨R, R', hRsyl, hR'syl, hcomm, hRt, hR't, x, hx, y, hy, hx2, hy2, hxy⟩ :=
    hs.exists_sylow_frame
  have hcomm_c : ∀ {L R₀ : Subgroup G}, R₀ ≤ L → L ≤ Subgroup.centralizer ({z} : Set G) →
      (∀ r ∈ R₀, r * t = t * r) → ∀ r ∈ R₀, r * c = c * r := by
    intro L R₀ hRL hLz hRt r hr
    have hrz : r * z = z * r := Subgroup.mem_centralizer_singleton_iff.mp (hLz (hRL hr))
    rcases hc with hc | hc
    · rw [hc]
      exact hRt r hr
    · rw [hc]
      calc r * (t * z) = (r * t) * z := by group
        _ = (t * r) * z := by rw [hRt r hr]
        _ = t * (r * z) := by group
        _ = t * (z * r) := by rw [hrz]
        _ = (t * z) * r := by group
  have hRc : ∀ r ∈ R, r * c = c * r := hcomm_c hRsyl.1 hKz hRt
  have hR'c : ∀ r ∈ R', r * c = c * r := hcomm_c hR'syl.1 hK'z hR't
  have hRsyl' : IsSylow2In R (exactCore c K) :=
    (isSylow2In_exactCore_iff hΩ hc2 hK (hs.tq_c_K hc)).mpr ⟨hRsyl, fun r hr =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hRc r hr)⟩
  have hR'syl' : IsSylow2In R' (exactCore c K') :=
    (isSylow2In_exactCore_iff hΩ hc2 hK'Ω (hs.tq_c_K' hc)).mpr ⟨hR'syl, fun r hr =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hR'c r hr)⟩
  exact ⟨R, R', hRsyl', hR'syl', hcomm, hRc, hR'c, x, hx, y, hy, hx2, hy2, hxy⟩

theorem TwinFrameSettingCore.u_mem_exactCore_sup {K K' J : Subgroup G} {z u t c : G}
    (hs : TwinFrameSettingCore p f Ω K K' J z u t) (hc : c = t ∨ c = t * z) :
    u ∈ exactCore c K ⊔ exactCore c K' := by
  obtain ⟨R, R', hR, hR', -, -, -, x, hx, y, hy, -, -, hxy⟩ := hs.exists_sylow_frame_at hc
  rw [← hxy]
  exact Subgroup.mul_mem_sup (hR.1 hx) (hR'.1 hy)

theorem TwinFrameSetting.u_mem_exactCore_sup {K K' J : Subgroup G} {z u t c : G}
    (hs : TwinFrameSetting p f Ω K K' J z u t) (hc : c = t ∨ c = t * z) :
    u ∈ exactCore c K ⊔ exactCore c K' := by
  obtain ⟨R, R', hR, hR', -, -, -, x, hx, y, hy, -, -, hxy⟩ := hs.exists_sylow_frame_at hc
  rw [← hxy]
  exact Subgroup.mul_mem_sup (hR.1 hx) (hR'.1 hy)

end Frame

end CFSG.ClassicalInvolution.Asc77
