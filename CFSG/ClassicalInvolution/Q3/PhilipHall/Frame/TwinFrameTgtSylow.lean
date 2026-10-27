module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameVertex

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_twinSylow_normalized_gen (hΩ : HypOmegaGen Ω) {K K' : Subgroup G} {z : G}
    (hK : K ∈ Ω) (hz : IsUniqueInvolution K z) (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K)
    {A : Subgroup G} (hA2 : IsPGroup 2 A) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hAK' : A ≤ Subgroup.normalizer (K' : Set G)) :
    ∃ R R' : Subgroup G, IsSylow2In R K ∧ IsSylow2In R' K' ∧ Commutes R R' ∧
      (∀ a ∈ A, conjSub a R = R) ∧ (∀ a ∈ A, conjSub a R' = R') ∧
        IsPGroup 2 ↥((A ⊔ R) ⊔ R') := by
  have hK'Ω : K' ∈ Ω := hK'.1
  obtain ⟨R, hRsyl, hRfix⟩ := Asc77.exists_sylow_normalized hA2 hAK
  have hRset : R ∈ RSet Ω := mem_RSet_of_isSylow2In hK hRsyl
  have hAnR : A ≤ Subgroup.normalizer (R : Set G) := fun t ht =>
    mem_normalizer_iff_conjSub_eq.mpr (hRfix t ht)
  have hAR2 : IsPGroup 2 ↥(A ⊔ R) := hA2.to_sup_of_normal_right' hRsyl.2.1 hAnR
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hK'
  have hKN : K ≤ Subgroup.normalizer (K' : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hK hK'Ω hne.symm hz hzK'
  have hPN : A ⊔ R ≤ Subgroup.normalizer (K' : Set G) := sup_le hAK' (hRsyl.1.trans hKN)
  obtain ⟨R', hR'syl, hR'fix⟩ := Asc77.exists_sylow_normalized hAR2 hPN
  have hR'set : R' ∈ RSet Ω := mem_RSet_of_isSylow2In hK'Ω hR'syl
  have hPnR' : A ⊔ R ≤ Subgroup.normalizer (R' : Set G) := fun t ht =>
    mem_normalizer_iff_conjSub_eq.mpr (hR'fix t ht)
  have hQ2 : IsPGroup 2 ↥((A ⊔ R) ⊔ R') := hAR2.to_sup_of_normal_right' hR'syl.2.1 hPnR'
  obtain ⟨S, hS⟩ := hQ2.exists_le_sylow
  have hRS : R ≤ (S : Subgroup G) := le_sup_right.trans (le_sup_left.trans hS)
  have hR'S : R' ≤ (S : Subgroup G) := le_sup_right.trans hS
  have hRR' : R ≠ R' := by
    intro h
    have := Sec6Gen.card_le_two_of_le_inf hΩ hK hK'Ω hne.symm hRsyl.2.1 hRsyl.1 (h ▸ hR'syl.1)
    have := Sec6Gen.eight_le_of_mem_RSet hΩ hRset
    omega
  exact ⟨R, R', hRsyl, hR'syl,
    Q3.Q3CP.l67Gen G Ω hΩ S R hRset R' hR'set hRS hR'S hRR', hRfix,
    fun a ha => hR'fix a (Subgroup.mem_sup_left ha), hQ2⟩

theorem sq_eq_one_of_natCard_le_two_tgt {A : Subgroup G} (h : Nat.card A ≤ 2) {w : G}
    (hw : w ∈ A) : w * w = 1 :=
  CFSG.ClassicalInvolution.Asc77.sq_eq_one_of_natCard_le_two h hw


theorem exists_sylow_frame_gen (hΩ : HypOmegaGen Ω) {K K' J : Subgroup G} {z u t : G}
    (hd : TwinFrameData Ω K K' z u J t) (htK : t ∈ centralizerModOdd ⊤ K)
    (htK' : t ∈ centralizerModOdd ⊤ K') :
    ∃ R R' : Subgroup G, IsSylow2In R K ∧ IsSylow2In R' K' ∧ Commutes R R' ∧
      (∀ r ∈ R, r * t = t * r) ∧ (∀ r ∈ R', r * t = t * r) ∧
        ∃ x ∈ R, ∃ y ∈ R', x * x = z ∧ y * y = z ∧ x * y = u := by
  have hK : K ∈ Ω := hd.mem
  have hK'Ω : K' ∈ Ω := hd.hK'.1
  have hz := hd.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hd.hK'
  have hne : K' ≠ K := hd.hne
  have hKN' : K ≤ Subgroup.normalizer (K' : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hK hK'Ω hne.symm hz hzK'
  have hK'N : K' ≤ Subgroup.normalizer (K : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hK'Ω hK hne hzK' hz
  have hB := TwinFrame.isElemAbelian_of_frameData hΩ hd
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
    · exact htK.2.1
  have hAK' : Subgroup.closure ({z, u, t} : Set G) ≤ Subgroup.normalizer (K' : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact Subgroup.le_normalizer hzK'.mem
    · exact huN'
    · exact htK'.2.1
  obtain ⟨R, R', hRsyl, hR'syl, hcomm, hRfix, hR'fix, hQ2⟩ := exists_twinSylow_normalized_gen hΩ
    hK hz hd.hK' hne hA2 hAK hAK'
  have htA : t ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.subset_closure (by simp)
  have huA : u ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.subset_closure (by simp)
  have hRR' : IsSylow2In (R ⊔ R') (K ⊔ K') :=
    Hat2A7S.T7X.isSylow2In_sup_of_twin hΩ hK hK'Ω hne hz hzK' hRsyl hR'syl hcomm
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
  have hcent : ∀ {L R₀ : Subgroup G}, IsSylow2In R₀ L → t ∈ centralizerModOdd ⊤ L →
      (∀ a ∈ Subgroup.closure ({z, u, t} : Set G), conjSub a R₀ = R₀) →
        ∀ r ∈ R₀, r * t = t * r := by
    intro L R₀ hR₀ htL hfix r hr
    have h1 : t * r * t⁻¹ ∈ R₀ := by
      have := conj_mem_conjSub (n := t) hr
      rwa [hfix t htA] at this
    have h2 : t * r * t⁻¹ * r⁻¹ ∈ R₀ := R₀.mul_mem h1 (R₀.inv_mem hr)
    have h3 : t * r * t⁻¹ * r⁻¹ ∈ oddCoreOf L := by
      have := htL.2.2.2 r (hR₀.1 hr)
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
    Sec6Gen.card_le_two_of_le_inf hΩ hK hK'Ω hne.symm (hRsyl.2.1.to_le inf_le_left)
      (inf_le_left.trans hRsyl.1) (inf_le_right.trans hR'syl.1)
  have hww : (x * x) * (x * x) = 1 := sq_eq_one_of_natCard_le_two_tgt hcard hw
  have hyy : y * y = x * x := by
    have : (y * y) = (x * x)⁻¹ := eq_inv_of_mul_eq_one_right hxy2
    rw [this]
    exact inv_eq_of_mul_eq_one_right hww
  rcases hz.unique (x * x) (K.mul_mem (hRsyl.1 hx) (hRsyl.1 hx)) hww with h1 | h1
  · exfalso
    have hx2 : x = 1 ∨ x = z := hz.unique x (hRsyl.1 hx) h1
    have hy2 : y = 1 ∨ y = z := hzK'.unique y (hR'syl.1 hy) (by rw [hyy, h1])
    rcases hx2 with rfl | rfl <;> rcases hy2 with rfl | rfl
    · exact hd.hu1 (by rw [← hxy, one_mul])
    · exact hd.huz (by rw [← hxy, one_mul])
    · exact hd.huz (by rw [← hxy, mul_one])
    · exact hd.hu1 (by rw [← hxy]; exact hz.sq)
  · exact ⟨h1, hyy.trans h1, hxy⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
