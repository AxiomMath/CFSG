module

public import CFSG.ClassicalInvolution.Q3.Q3TWBA01
public import CFSG.ClassicalInvolution.Q3.Q3T6DH51Twin

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_twinSylow_normalized3 (hΩ : Q3T7M.HM Ω) {K K' : Subgroup G} {z : G} (hK : K ∈ Ω)
    (hz : IsUniqueInvolution K z) (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K) {A : Subgroup G}
    (hA2 : IsPGroup 2 A) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hAK' : A ≤ Subgroup.normalizer (K' : Set G)) :
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
    have := hΩ.eight_le_of_mem_RSet hRset
    omega
  exact ⟨R, R', hRsyl, hR'syl,
    Q3T8.Asc77.l6_7_proved G Ω hΩ S R hRset R' hR'set hRS hR'S hRR', hRfix,
    fun a ha => hR'fix a (Subgroup.mem_sup_left ha), hQ2⟩

theorem sq_eq_one_of_natCard_le_two' {A : Subgroup G} (h : Nat.card A ≤ 2) {w : G} (hw : w ∈ A) :
    w * w = 1 :=
  CFSG.ClassicalInvolution.Asc77.sq_eq_one_of_natCard_le_two h hw

theorem exists_sylow_frame3 (hΩ : Q3T7M.HM Ω) {K K' J : Subgroup G} {z u t : G}
    (hd : Q3T8.Asc77.TwinFrameData Ω K K' z u J t)
    (htK : t ∈ Balance.Bootstrap.trivialOnQuot K) (htK' : t ∈ Balance.Bootstrap.trivialOnQuot K') :
    ∃ R R' : Subgroup G, IsSylow2In R K ∧ IsSylow2In R' K' ∧ Commutes R R' ∧
      (∀ r ∈ R, r * t = t * r) ∧ (∀ r ∈ R', r * t = t * r) ∧
        ∃ x ∈ R, ∃ y ∈ R', x * x = z ∧ y * y = z ∧ x * y = u := by
  have hK : K ∈ Ω := hd.mem
  have hK'Ω : K' ∈ Ω := hd.hK'.1
  have hz := hd.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hd.hK'
  have hne : K' ≠ K := hd.hne
  have hKN' : K ≤ Subgroup.normalizer (K' : Set G) :=
    hΩ.le_normalizer_of_twin hK hK'Ω hne.symm hz hzK'
  have hK'N : K' ≤ Subgroup.normalizer (K : Set G) :=
    hΩ.le_normalizer_of_twin hK'Ω hK hne hzK' hz
  have hB := twinFrame_isElemAbelian hΩ hd
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
  obtain ⟨R, R', hRsyl, hR'syl, hcomm, hRfix, hR'fix, hQ2⟩ := exists_twinSylow_normalized3 hΩ
    hK hz hd.hK' hne hA2 hAK hAK'
  have htA : t ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.subset_closure (by simp)
  have huA : u ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.subset_closure (by simp)
  have hRR' : IsSylow2In (R ⊔ R') (K ⊔ K') :=
    Q3T8.Asc77.T7A.isSylow2In_sup_of_twin hΩ hK hK'Ω hne hz hzK' hRsyl hR'syl hcomm
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
  have hcent : ∀ {L R₀ : Subgroup G}, IsSylow2In R₀ L → t ∈ Balance.Bootstrap.trivialOnQuot L →
      (∀ a ∈ Subgroup.closure ({z, u, t} : Set G), conjSub a R₀ = R₀) →
        ∀ r ∈ R₀, r * t = t * r := by
    intro L R₀ hR₀ htL hfix r hr
    have h1 : t * r * t⁻¹ ∈ R₀ := by
      have := conj_mem_conjSub (n := t) hr
      rwa [hfix t htA] at this
    have h2 : t * r * t⁻¹ * r⁻¹ ∈ R₀ := R₀.mul_mem h1 (R₀.inv_mem hr)
    have h3 : t * r * t⁻¹ * r⁻¹ ∈ Balance.oddCoreIn L := by
      have := htL.2 r (hR₀.1 hr)
      rwa [commutatorElement_def] at this
    have h4 : IsPGroup 2 (Subgroup.zpowers (t * r * t⁻¹ * r⁻¹)) :=
      hR₀.2.1.to_le (Subgroup.zpowers_le.mpr h2)
    have h5 : t * r * t⁻¹ * r⁻¹ = 1 :=
      eq_one_of_isPGroup_of_mem_odd (Balance.odd_card_oddCoreIn L) h3 h4
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
  have hww : (x * x) * (x * x) = 1 := sq_eq_one_of_natCard_le_two' hcard hw
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

section Hyp51

variable [IsSimpleGroup G]

theorem inClass3_of_twinFrameSetting {K K' J : Subgroup G} {z u t : G}
    (hs : Q3T8.Asc77.TwinFrameSettingNA Ω K K' J z u t) : InClass3 Ω where
  nonempty := ⟨K, hs.frame.mem⟩
  conjInvariant := hs.hyp.conjInvariant
  generated := by
    have hnorm := omegaGen_normal hs.hyp.conjInvariant
    have hK : K ≤ omegaGen Ω := le_omegaGen hs.frame.mem
    rcases hnorm.eq_bot_or_eq_top with h | h
    · exact absurd (hK hs.frame.hz.mem) (by rw [h]; simpa using hs.frame.hz.ne_one)
    · exact h
  classical := fun L hL => by
    obtain ⟨w, hw⟩ := hs.hyp.classical L hL
    exact ⟨w, hw.toQ3 (by norm_num)⟩

theorem mem_trivialOnQuot_of_isUniqueInvolution {L : Subgroup G} {z : G}
    (hL : IsUniqueInvolution L z) : z ∈ Balance.Bootstrap.trivialOnQuot L := by
  refine Balance.Bootstrap.mem_trivialOnQuot_iff.mpr ⟨Subgroup.le_normalizer hL.mem, fun x hx => ?_⟩
  rw [commutatorElement_eq_one_iff_mul_comm.mpr (hL.commute_of_mem hx)]
  exact (Balance.oddCoreIn L).one_mem

theorem twinFrameHyp51tC_proved : TwinFrameHyp51tC := by
  intro G _ _ _ Ω K K' J z u t hs hf
  have hΩ : Q3T7M.HM Ω := hs.hyp
  have hd := hs.frame
  have hKΩ : K ∈ Ω := hd.mem
  have hK'Ω : K' ∈ Ω := hd.hK'.1
  have hzK : IsUniqueInvolution K z := hd.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hd.hz hd.hK'
  have hJΩ : J ∈ Ω := hd.hJ.1
  have hJK : J ∈ omegaNbr Ω K := hd.hJ.2 K (mem_twinSet_self hKΩ hzK)
  have hJK' : J ∈ omegaNbr Ω K' := hd.hJ.2 K' hd.hK'
  have hKJ : K ∈ omegaNbr Ω J := Q3CL.T3.omegaNbr_symm (Q3T8.Asc77.l6_2) hΩ hKΩ hJΩ hJK
  have hK'J : K' ∈ omegaNbr Ω J := Q3CL.T3.omegaNbr_symm (Q3T8.Asc77.l6_2) hΩ hK'Ω hJΩ hJK'
  have htK : t ∈ Balance.Bootstrap.trivialOnQuot K :=
    Balance.Bootstrap.mem_trivialOnQuot_iff_actsTrivOnQuot.mpr (hf J hJΩ K hKJ t hd.ht)
  have htK' : t ∈ Balance.Bootstrap.trivialOnQuot K' :=
    Balance.Bootstrap.mem_trivialOnQuot_iff_actsTrivOnQuot.mpr (hf J hJΩ K' hK'J t hd.ht)
  have hB : IsElemAbelian 2 (Subgroup.closure ({z, u, t} : Set G)) :=
    twinFrame_isElemAbelian hΩ hd
  have hzB : z ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.subset_closure (by simp)
  have huB : u ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.subset_closure (by simp)
  have htB : t ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.subset_closure (by simp)
  have hbK : IsClassicalMember3 K z :=
    (isClassicalMember_of_twin hΩ hKΩ hzK).toQ3 (by norm_num)
  have hbK' : IsClassicalMember3 K' z :=
    (isClassicalMember_of_twin hΩ hK'Ω hzK').toQ3 (by norm_num)
  have hBelow3 : CIT3Below (Nat.card G) :=
    (Uniform.citBelowT_three_iff (p := 3) (f := 1) (by norm_num) _).mp hs.below
  have hnab : ∃ x y : G, x * y ≠ y * x := by
    obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := G)) (bot_le : ⊥ ≤ K)
    have hVR : V ∈ RSet Ω := mem_RSet_of_isSylow2In hKΩ hV
    obtain ⟨x, -, y, -, hxy⟩ := (hΩ.isQuatSub_of_mem_RSet hVR).exists_not_commute
    exact ⟨x, y, hxy⟩
  obtain ⟨R, R', hRsyl, hR'syl, -, hRt, hR't, x, hx, y, hy, -, -, hxy⟩ :=
    exists_sylow_frame3 hΩ hd htK htK'
  have hz2 : z * z = 1 := hzK.sq
  have hz1 : z ≠ 1 := hzK.ne_one
  have main : ∀ c : G, (c = t ∨ c = t * z) →
      Hyp51At (Subgroup.closure ({z, u, t} : Set G)) c := by
    intro c hc
    have hcK : c ∈ Balance.Bootstrap.trivialOnQuot K := by
      rcases hc with rfl | rfl
      · exact htK
      · exact Subgroup.mul_mem _ htK (mem_trivialOnQuot_of_isUniqueInvolution hzK)
    have hcK' : c ∈ Balance.Bootstrap.trivialOnQuot K' := by
      rcases hc with rfl | rfl
      · exact htK'
      · exact Subgroup.mul_mem _ htK' (mem_trivialOnQuot_of_isUniqueInvolution hzK')
    have hcB : c ∈ Subgroup.closure ({z, u, t} : Set G) := by
      rcases hc with rfl | rfl
      · exact htB
      · exact Subgroup.mul_mem _ htB hzB
    have hBgen : Subgroup.closure ({z, u, t} : Set G) = Subgroup.closure ({z, u, c} : Set G) := by
      rcases hc with rfl | rfl
      · rfl
      · apply le_antisymm
        · rw [Subgroup.closure_le]
          intro g hg
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
          rcases hg with rfl | rfl | rfl
          · exact Subgroup.subset_closure (by simp)
          · exact Subgroup.subset_closure (by simp)
          · have h1 : g * z ∈ Subgroup.closure ({z, u, g * z} : Set G) :=
              Subgroup.subset_closure (by simp)
            have h2 : z ∈ Subgroup.closure ({z, u, g * z} : Set G) :=
              Subgroup.subset_closure (by simp)
            have h3 := Subgroup.mul_mem _ h1 h2
            rwa [mul_assoc, hz2, mul_one] at h3
        · rw [Subgroup.closure_le]
          intro g hg
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
          rcases hg with rfl | rfl | rfl
          · exact hzB
          · exact huB
          · exact Subgroup.mul_mem _ htB hzB
    have hc1 : c ≠ 1 := by
      rcases hc with rfl | rfl
      · exact hd.ht.ne_one
      · intro h
        have h1 : t = z⁻¹ := eq_inv_of_mul_eq_one_left h
        exact hd.t_ne_z (h1.trans (inv_eq_of_mul_eq_one_right hz2))
    have hbc : z ≠ c := by
      rcases hc with rfl | rfl
      · exact hd.t_ne_z.symm
      · intro h
        have h1 : t * z = 1 * z := by rw [one_mul]; exact h.symm
        exact hd.ht.ne_one (mul_right_cancel h1)
    have hxc : x ∈ Q3NL.exactCore3 c K := by
      refine ⟨hRsyl.1 hx, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      rcases hc with rfl | rfl
      · exact hRt x hx
      · have hxz : x * z = z * x := (hzK.commute_of_mem (hRsyl.1 hx)).symm
        calc x * (t * z) = (x * t) * z := by group
          _ = (t * x) * z := by rw [hRt x hx]
          _ = t * (x * z) := by group
          _ = t * (z * x) := by rw [hxz]
          _ = (t * z) * x := by group
    have hyc : y ∈ Q3NL.exactCore3 c K' := by
      refine ⟨hR'syl.1 hy, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      rcases hc with rfl | rfl
      · exact hR't y hy
      · have hyz : y * z = z * y := (hzK'.commute_of_mem (hR'syl.1 hy)).symm
        calc y * (t * z) = (y * t) * z := by group
          _ = (t * y) * z := by rw [hR't y hy]
          _ = t * (y * z) := by group
          _ = t * (z * y) := by rw [hyz]
          _ = (t * z) * y := by group
    have hdsup : u ∈ Q3NL.exactCore3 c K ⊔ Q3NL.exactCore3 c K' := by
      rw [← hxy]
      exact Subgroup.mul_mem_sup hxc hyc
    exact Q3T6D.hyp51At_of_twin_layer3_proved (B := Subgroup.closure ({z, u, t} : Set G))
      (inClass3_of_twinFrameSetting hs) hBelow3 hnab hbK hbK' hzK hzK' ⟨hKΩ, hcK⟩ ⟨hK'Ω, hcK'⟩
      hB hzB huB hcB hBgen hc1 hbc hd.hu1 hd.huz hdsup
  exact ⟨main t (Or.inl rfl), main (t * z) (Or.inr rfl)⟩

end Hyp51

end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
