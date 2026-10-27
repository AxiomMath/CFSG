module

public import CFSG.ClassicalInvolution.Q3.Q3T7P25U01
public import CFSG.ClassicalInvolution.Q3.Q3T7P25U03
public import CFSG.ClassicalInvolution.Q3.Q3T7M03
public import CFSG.ClassicalInvolution.Q3.Q3T7P25V03
public import CFSG.ClassicalInvolution.Q3.Q3T7P25YM01
public import CFSG.ClassicalInvolution.Asc77.AscCX9U

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

set_option linter.unusedSectionVars false
namespace Asc77.CX
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.CX
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
section Act
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

@[expose] noncomputable def actW (hc : ConjInvariant Ω) (w : G) :
    ↥(Subgroup.centralizer ({w} : Set G)) →*
      MulAut (↥(ExactLayer.exactLayer Ω w) ⧸ classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω
          w)) :=
  layerHom (ExactLayer.exactLayer Ω w) (Subgroup.centralizer ({w} : Set G)) fun _ hx =>
    ExactLayer.conjSub_exactLayer hc hx

theorem actW_apply (hc : ConjInvariant Ω) {w : G}
    (x : ↥(Subgroup.centralizer ({w} : Set G))) :
    actW hc w x = C25Y.layerAut (ExactLayer.exactLayer Ω w) (ExactLayer.conjSub_exactLayer hc x.2)
        := rfl

theorem layerAut_self (w : G) (h : conjSub w (ExactLayer.exactLayer Ω w) = ExactLayer.exactLayer Ω
    w) :
    C25Y.layerAut (ExactLayer.exactLayer Ω w) h = 1 := by
  ext y
  refine QuotientGroup.induction_on y fun y => ?_
  rw [C25Y.layerAut_mk, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  rw [C25Y.coe_conjOnSub]
  have hy := Subgroup.mem_centralizer_singleton_iff.mp (ExactLayer.exactLayer_le_centralizer Ω w
      y.2)
  rw [← hy, mul_inv_cancel_right]

theorem actW_self (hc : ConjInvariant Ω) (w : G) :
    actW hc w ⟨w, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ = 1 :=
  layerAut_self w _

theorem actW_eq_conj (hc : ConjInvariant Ω) {w x : G}
    (hx : x ∈ Subgroup.centralizer ({w} : Set G)) (hxY : x ∈ ExactLayer.exactLayer Ω w) :
    actW hc w ⟨x, hx⟩ = MulAut.conj (T7H.toBar Ω w x hxY) := by
  ext y
  refine QuotientGroup.induction_on y fun y => ?_
  rw [actW_apply, C25Y.layerAut_mk, MulAut.conj_apply]
  unfold T7H.toBar
  rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
    ← QuotientGroup.mk_mul]
  congr 1

theorem actW_mul_z (hc : ConjInvariant Ω) {w x z : G}
    (hx : x ∈ Subgroup.centralizer ({w} : Set G)) (hz : z ∈ Subgroup.centralizer ({w} : Set G))
    (hzY : z ∈ ExactLayer.exactLayer Ω w) (hxz : x * z ∈ Subgroup.centralizer ({w} : Set G)) :
    actW hc w ⟨x * z, hxz⟩ = actW hc w ⟨x, hx⟩ * MulAut.conj (T7H.toBar Ω w z hzY) := by
  rw [← actW_eq_conj hc hz hzY, ← map_mul]
  rfl

theorem actW_mem_zpowers (hc : ConjInvariant Ω) {w x e : G}
    (hx : x ∈ Subgroup.centralizer ({w} : Set G)) (he : e ∈ Subgroup.closure ({w, x} : Set G))
    (heC : e ∈ Subgroup.centralizer ({w} : Set G)) :
    actW hc w ⟨e, heC⟩ ∈ Subgroup.zpowers (actW hc w ⟨x, hx⟩) := by
  set P := (Subgroup.zpowers (actW hc w ⟨x, hx⟩)).comap (actW hc w) with hP
  have hle : Subgroup.closure ({w, x} : Set G) ≤
      P.map (Subgroup.centralizer ({w} : Set G)).subtype := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with h | h
    · refine ⟨⟨w, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩, ?_, h.symm⟩
      show actW hc w ⟨w, _⟩ ∈ Subgroup.zpowers (actW hc w ⟨x, hx⟩)
      rw [actW_self]
      exact one_mem _
    · exact ⟨⟨x, hx⟩, Subgroup.mem_zpowers _, h.symm⟩
  obtain ⟨e', he', hee'⟩ := hle he
  have he'eq : e' = ⟨e, heC⟩ := Subtype.ext hee'
  rw [he'eq] at he'
  exact he'
end Act
section Edge
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {z : G} {S : Sylow 2 G} {R R' : Subgroup G}
  {t u₁ u₂ : G}

theorem actW_fix (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {w x : G} (hw2 : w * w = 1)
    (hK₂ : K ∈ ExactLayer.tqMembers Ω w) (hK₂' : K' ∈ ExactLayer.tqMembers Ω w)
    (hO : oddCoreOf (T7H.exactImg Ω w K) = ⊥) (hO' : oddCoreOf (T7H.exactImg Ω w K') = ⊥)
    (hxA : x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hx : x ∈ Subgroup.centralizer ({w} : Set G)) :
    (∀ y ∈ T7H.exactImg Ω w K, actW hyp.std.setting.stand.modU.conjInvariant w ⟨x, hx⟩ y = y) ∧
      ∀ y ∈ T7H.exactImg Ω w K', actW hyp.std.setting.stand.modU.conjInvariant w ⟨x, hx⟩ y = y :=
  ⟨layerAut_fix_exactImg hyp.std.setting.stand.modU (isPGroup_zpowers_of_sq_eq_one hw2) hK₂ hO hx
      (mem_trivialOnQuot_of_mem_A hyp hxA).1,
    layerAut_fix_exactImg hyp.std.setting.stand.modU (isPGroup_zpowers_of_sq_eq_one hw2) hK₂' hO'
      hx (mem_trivialOnQuot_of_mem_A hyp hxA).2⟩

variable [CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.Facts25V] in
theorem actW_mul_self (h6 : Layer6Twin 3 1) (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂)
    {w x : G} (hwA : w ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hw2 : w * w = 1) (hw1 : w ≠ 1) (hwbad : z ∉ zStarOf (Subgroup.centralizer ({w} : Set G)))
    (hxA : x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hx : x ∈ Subgroup.centralizer ({w} : Set G)) :
    actW hyp.std.setting.stand.modU.conjInvariant w ⟨x, hx⟩ *
      actW hyp.std.setting.stand.modU.conjInvariant w ⟨x, hx⟩ = 1 := by
  have hΩ : HypOmegaModT Ω := hyp.std.setting.stand.modU
  obtain ⟨hzY', hK₂, hK₂', -, hO, hO', hT2, -⟩ := twinFacts_of_bad h6 hyp hwA hw2 hw1 hwbad
  set E := Subgroup.zpowers x with hE
  have hEA : E ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr hxA
  have hE2 : IsPGroup 2 E := S.isPGroup'.to_le (hEA.trans inf_le_left)
  have hEb : E ≤ Subgroup.centralizer ({w} : Set G) := Subgroup.zpowers_le.mpr hx
  set lam := layerHom (ExactLayer.exactLayer Ω w) E fun e he => ExactLayer.conjSub_exactLayer
      hΩ.conjInvariant (hEb he)
    with hlam
  have hP2 : IsPGroup 2 lam.range := by
    rw [MonoidHom.range_eq_map]
    exact (hE2.to_subgroup ⊤).map lam
  obtain ⟨hexpP, -⟩ := hT2 lam.range hP2 fun β hβ => by
    obtain ⟨e, rfl⟩ := hβ
    exact actW_fix hyp hw2 hK₂ hK₂' hO hO' (hEA e.2) (hEb e.2)
  exact hexpP (lam ⟨x, Subgroup.mem_zpowers x⟩) ⟨_, rfl⟩

variable [CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.Facts25V] in
theorem good_iff_actW (h6 : Layer6Twin 3 1) (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂)
    {w x : G} (hwA : w ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hw2 : w * w = 1) (hw1 : w ≠ 1) (hwbad : z ∉ zStarOf (Subgroup.centralizer ({w} : Set G)))
    (hxA : x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hx : x ∈ Subgroup.centralizer ({w} : Set G)) (hzY : z ∈ ExactLayer.exactLayer Ω w) :
    z ∈ zStarOf (Subgroup.centralizer ({w, x} : Set G)) ↔
      actW hyp.std.setting.stand.modU.conjInvariant w ⟨x, hx⟩ =
        MulAut.conj (T7H.toBar Ω w z hzY) := by
  classical
  have hz2 : z * z = 1 := hyp.std.setting.hz.sq
  have hz1 : z ≠ 1 := hyp.std.setting.hz.ne_one
  have hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s := hyp.hzS
  have hΩ : HypOmegaModT Ω := hyp.std.setting.stand.modU
  obtain ⟨hzY', hK₂, hK₂', hcen, hO, hO', -, hT3⟩ := twinFacts_of_bad h6 hyp hwA hw2 hw1 hwbad
  have hβ2 := actW_mul_self h6 hyp hwA hw2 hw1 hwbad hxA hx
  obtain ⟨hfixK, hfixK'⟩ := actW_fix hyp hw2 hK₂ hK₂' hO hO' hxA hx
  have hzw : z ∈ Subgroup.centralizer ({w} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hzS w hwA.1).symm
  have hzx : z ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hzS x hxA.1).symm
  have hCwx : Subgroup.centralizer ({w} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) =
      Subgroup.centralizer ({w, x} : Set G) := by
    ext g
    exact mem_centralizer_pair_iff.symm
  constructor
  · intro hgood
    by_contra hβz
    set F := Subgroup.closure ({w, x} : Set G) with hF
    have hFA : F ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) :=
      closure_pair_le hwA hxA
    have hF2 : IsPGroup 2 F := S.isPGroup'.to_le (hFA.trans inf_le_left)
    have hFb : F ≤ Subgroup.centralizer ({w} : Set G) :=
      closure_pair_le (Subgroup.mem_centralizer_singleton_iff.mpr rfl) hx
    have hzF : z ∈ Subgroup.centralizer (F : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact hzS g (hFA hg).1
    have hgoodF : z ∈ zStarOf (Subgroup.centralizer (F : Set G)) := by
      rw [hF, Subgroup.centralizer_closure]
      exact hgood
    have hpow : ∀ e (he : e ∈ F), actW hΩ.conjInvariant w ⟨e, hFb he⟩ = 1 ∨
        actW hΩ.conjInvariant w ⟨e, hFb he⟩ = actW hΩ.conjInvariant w ⟨x, hx⟩ := fun e he =>
      eq_one_or_eq_of_mem_zpowers hβ2 (actW_mem_zpowers hΩ.conjInvariant hx he (hFb he))
    by_cases hβ1 : actW hΩ.conjInvariant w ⟨x, hx⟩ = 1
    · refine not_mem_zStarOf_of_layerAut_trivial hΩ hF2 hFb hzF hzY hz2 hz1 hcen ?_ hgoodF
      intro e he y
      have h1 : actW hΩ.conjInvariant w ⟨e, hFb he⟩ = 1 := by
        rcases hpow e he with h | h
        · exact h
        · rw [h, hβ1]
      have h2 := congrArg (fun φ => φ y) h1
      simpa [actW_apply] using h2
    · obtain ⟨xb, hxbfix, hxbz, hxbc⟩ := hT3 _ hfixK hfixK' hβ2 hβ1 hβz
      refine not_mem_zStarOf_of_layerAut_fix hΩ hF2 hFb hzY hz2 (x := xb) ?_ hxbz hxbc hgoodF
      intro e he
      rcases hpow e he with h | h
      · have h2 := congrArg (fun φ => φ xb) h
        simpa [actW_apply] using h2
      · have h2 := congrArg (fun φ => φ xb) h
        simp only [actW_apply] at h2
        rw [h2]
        exact hxbfix
  · intro hβz
    have h1 := mem_zStarOf_of_layerAut_eq_conj hΩ hx hzw hzx hzY hcen fun y => by
      have h2 := congrArg (fun φ => φ y) hβz
      simpa [actW_apply, MulAut.conj_apply] using h2
    rwa [hCwx] at h1

variable [CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.Facts25V] in
theorem not_good_and_good (h6 : Layer6Twin 3 1) (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂)
    {w x : G} (hwA : w ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hw2 : w * w = 1) (hw1 : w ≠ 1) (hwbad : z ∉ zStarOf (Subgroup.centralizer ({w} : Set G)))
    (hxA : x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hx : x ∈ Subgroup.centralizer ({w} : Set G)) :
    ¬ (z ∈ zStarOf (Subgroup.centralizer ({w, x} : Set G)) ∧
      z ∈ zStarOf (Subgroup.centralizer ({w, x * z} : Set G))) := by
  rintro ⟨h₁, h₂⟩
  have hz2 : z * z = 1 := hyp.std.setting.hz.sq
  have hz1 : z ≠ 1 := hyp.std.setting.hz.ne_one
  have hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s := hyp.hzS
  have hzA := T7T.z_mem_centralizer_of_hyp hyp
  obtain ⟨hzY, -, -, hcen, -⟩ := twinFacts_of_bad h6 hyp hwA hw2 hw1 hwbad
  have hz : z ∈ Subgroup.centralizer ({w} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hzS w hwA.1).symm
  have hxz : x * z ∈ Subgroup.centralizer ({w} : Set G) := Subgroup.mul_mem _ hx hz
  have e₁ := (good_iff_actW h6 hyp hwA hw2 hw1 hwbad hxA hx hzY).mp h₁
  have e₂ := (good_iff_actW h6 hyp hwA hw2 hw1 hwbad (Subgroup.mul_mem _ hxA hzA) hxz hzY).mp h₂
  rw [actW_mul_z _ hx hz hzY hxz, e₁] at e₂
  have h1 : MulAut.conj (T7H.toBar Ω w z hzY) = 1 := by
    calc MulAut.conj (T7H.toBar Ω w z hzY) =
          (MulAut.conj (T7H.toBar Ω w z hzY))⁻¹ *
            (MulAut.conj (T7H.toBar Ω w z hzY) * MulAut.conj (T7H.toBar Ω w z hzY)) := by group
      _ = 1 := by rw [e₂, inv_mul_cancel]
  exact conj_ne_one_of_center_eq_bot hcen (mk_ne_one_of_involution hzY hz2 hz1) h1

variable [CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.Facts25V] in
theorem om6mData_of_actW (h6 : Layer6Twin 3 1) (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂)
    {w x : G} (hwA : w ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hw2 : w * w = 1) (hw1 : w ≠ 1) (hwbad : z ∉ zStarOf (Subgroup.centralizer ({w} : Set G)))
    (htyp : LayerOrthType Ω w 5 true ∨ LayerOrthType Ω w 6 (!piSign 3 1))
    (hxA : x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hx : x ∈ Subgroup.centralizer ({w} : Set G)) (hzY : z ∈ ExactLayer.exactLayer Ω w)
    (hβ1 : actW hyp.std.setting.stand.modU.conjInvariant w ⟨x, hx⟩ ≠ 1)
    (hβz : actW hyp.std.setting.stand.modU.conjInvariant w ⟨x, hx⟩ ≠
      MulAut.conj (T7H.toBar Ω w z hzY)) :
    ∃ (hu₁Y : u₁ ∈ ExactLayer.exactLayer Ω w) (hu₂Y : u₂ ∈ ExactLayer.exactLayer Ω w),
      Om6mData (↥(ExactLayer.exactLayer Ω w) ⧸ classicalInvolutionOddCore
          ↥(ExactLayer.exactLayer Ω w))
        (oddQuotientFamily (ExactLayer.exactPair Ω w)) (T7H.exactImg Ω w K) (T7H.exactImg Ω w K')
        (T7H.toBar Ω w z hzY) (T7H.toBar Ω w u₁ hu₁Y) (T7H.toBar Ω w u₂ hu₂Y) := by
  classical
  have hst := hyp.std.setting.stand
  have hΩ : HypOmegaModT Ω := hst.modU
  have hcent := Subgroup.mem_centralizer_iff.mp hwA.2
  have haR : ∀ y ∈ R, w * y = y * w := fun y hy => (hcent y (Subgroup.mem_sup_left hy)).symm
  have haR' : ∀ y ∈ R', w * y = y * w := fun y hy => (hcent y (Subgroup.mem_sup_right hy)).symm
  obtain ⟨hzY', hu₁Y, hu₂Y, hK₂, hK₂', hgen, hlt, htw⟩ :=
    C25X.layer_a_frame hyp hw2 hw1 haR haR'
  obtain ⟨hzY'', -, -, -, hO, hO', -, -⟩ := twinFacts_of_bad h6 hyp hwA hw2 hw1 hwbad
  obtain ⟨hfixK, hfixK'⟩ := actW_fix hyp hw2 hK₂ hK₂' hO hO' hxA hx
  have hΦ : ∀ J ∈ oddQuotientFamily (ExactLayer.exactPair Ω w), ∀ y : ↥(ExactLayer.exactLayer Ω w) ⧸
      classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω w),
      conjSub y J ∈ oddQuotientFamily (ExactLayer.exactPair Ω w) := by
    intro J hJ yb
    obtain ⟨M, hMtq, rfl⟩ := T7H.exists_exactImg_of_mem hJ
    obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective yb
    rw [← C25Y.exactImg_conjSub_layer x']
    exact T7H.exactImg_mem (ExactLayer.conjSub_mem_tqMembers hΩ.conjInvariant
      (ExactLayer.exactLayer_le_centralizer Ω w x'.2) hMtq)
  rcases htyp with h | h
  · exfalso
    obtain ⟨t', n, hT, D, hD1, i₀, hDt, hDn⟩ := h
    rcases C25W.cent5_proved _ _ D _ _ _ _ _ hD1
      ⟨i₀, by rw [hDt, hDn]; exact hT⟩ htw _ hfixK hfixK' with h1 | h1
    · exact hβ1 h1
    · apply hβz
      ext y
      exact h1 y
  · obtain ⟨t', n, hT, D, hD1, i₀, hDt, hDn⟩ := h
    exact ⟨hu₁Y, hu₂Y, ⟨⟨D, hD1, i₀, by rw [hDt, hDn]; exact hT⟩, htw, hΦ⟩⟩
end Edge
end Asc77.CX

end

section

set_option linter.unusedSectionVars false
namespace Asc77.CX
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.CX
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
section Twin
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {w : G} {K : Subgroup G}

@[expose] noncomputable def twinQuot (K : Subgroup G) (w : G) :
    ↥(ExactLayer.exactCore w K) →* ↥K ⧸ classicalInvolutionOddCore ↥K :=
  toOddQuot (ExactLayer.exactCore_le_left w K)

@[expose] noncomputable def twinBar (hK₂ : K ∈ ExactLayer.tqMembers Ω w) :
    ↥(ExactLayer.exactCore w K) →* ↥(T7H.exactImg Ω w K) :=
  ((QuotientGroup.mk' (classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω w))).comp
    (Subgroup.inclusion (ExactLayer.exactCore_le_exactLayer hK₂))).codRestrict (T7H.exactImg Ω w K)
    fun m => T7H.mem_exactImg (Ω := Ω) m.2 (ExactLayer.exactCore_le_exactLayer hK₂ m.2)

theorem coe_twinBar (hK₂ : K ∈ ExactLayer.tqMembers Ω w) (m : ↥(ExactLayer.exactCore w K)) :
    ((twinBar hK₂ m : ↥(T7H.exactImg Ω w K)) :
      ↥(ExactLayer.exactLayer Ω w) ⧸ classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω w)) =
      T7H.toBar Ω w m (ExactLayer.exactCore_le_exactLayer hK₂ m.2) := rfl

theorem twinBar_surjective (hK₂ : K ∈ ExactLayer.tqMembers Ω w) :
    Function.Surjective (twinBar (Ω := Ω) hK₂) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  refine ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, ?_⟩
  apply Subtype.ext
  rfl

theorem odd_natCard_ker_twinBar (hK₂ : K ∈ ExactLayer.tqMembers Ω w) :
    Odd (Nat.card (twinBar (Ω := Ω) hK₂).ker) := by
  set X := ExactLayer.exactLayer Ω w with hX
  have hle : (twinBar (Ω := Ω) hK₂).ker.map (ExactLayer.exactCore w K).subtype ≤ oddCoreOf X := by
    rintro _ ⟨m, hm, rfl⟩
    have hm' : twinBar (Ω := Ω) hK₂ m = 1 := hm
    have h1 : ((twinBar (Ω := Ω) hK₂ m : ↥(T7H.exactImg Ω w K)) :
        ↥X ⧸ classicalInvolutionOddCore ↥X) = 1 := by rw [hm']; rfl
    rw [coe_twinBar] at h1
    unfold T7H.toBar at h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact Subgroup.mem_map_of_mem X.subtype h1
  have hO : Odd (Nat.card (oddCoreOf X)) := by
    unfold oddCoreOf
    rw [Subgroup.card_map_of_injective X.subtype_injective]
    exact CFSG.ComponentClassification.OddCore.odd_card ↥X
  rw [← Subgroup.card_map_of_injective (ExactLayer.exactCore w K).subtype_injective]
  exact hO.of_dvd_nat (Subgroup.card_dvd_of_le hle)

theorem ker_twinQuot_eq (hK₂ : K ∈ ExactLayer.tqMembers Ω w)
    (hcov : ∀ x ∈ K, ∃ i ∈ ExactLayer.exactCore w K, ∃ n ∈ oddCoreIn K, x = i * n)
    (hO : oddCoreOf (T7H.exactImg Ω w K) = ⊥) :
    (twinQuot K w).ker = (twinBar (Ω := Ω) hK₂).ker := by
  have hsurj : Function.Surjective (twinQuot K w) := toOddQuot_surjective _ hcov
  have hT : classicalInvolutionOddCore ↥(T7H.exactImg Ω w K) = ⊥ := by
    unfold oddCoreOf at hO
    exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp hO
  rw [ker_eq_oddCore_of_surjective _ (twinBar_surjective hK₂) hT (odd_natCard_ker_twinBar hK₂)]
  exact (classicalInvolutionOddCore_eq_ker (ExactLayer.exactCore_le_left w K) hsurj).symm

@[expose] noncomputable def twinEquiv (hK₂ : K ∈ ExactLayer.tqMembers Ω w)
    (hcov : ∀ x ∈ K, ∃ i ∈ ExactLayer.exactCore w K, ∃ n ∈ oddCoreIn K, x = i * n)
    (hO : oddCoreOf (T7H.exactImg Ω w K) = ⊥) :
    (↥K ⧸ classicalInvolutionOddCore ↥K) ≃* ↥(T7H.exactImg Ω w K) :=
  (QuotientGroup.quotientKerEquivOfSurjective (twinQuot K w)
      (toOddQuot_surjective _ hcov)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (ker_twinQuot_eq hK₂ hcov hO)).trans
      (QuotientGroup.quotientKerEquivOfSurjective (twinBar hK₂) (twinBar_surjective hK₂)))

theorem twinEquiv_mk (hK₂ : K ∈ ExactLayer.tqMembers Ω w)
    (hcov : ∀ x ∈ K, ∃ i ∈ ExactLayer.exactCore w K, ∃ n ∈ oddCoreIn K, x = i * n)
    (hO : oddCoreOf (T7H.exactImg Ω w K) = ⊥) {m : G} (hm : m ∈ ExactLayer.exactCore w K) :
    ((twinEquiv hK₂ hcov hO (QuotientGroup.mk ⟨m, ExactLayer.exactCore_le_left w K hm⟩) :
      ↥(T7H.exactImg Ω w K)) : ↥(ExactLayer.exactLayer Ω w) ⧸ classicalInvolutionOddCore
          ↥(ExactLayer.exactLayer Ω w)) =
      T7H.toBar Ω w m (ExactLayer.exactCore_le_exactLayer hK₂ hm) := by
  have h1 : (QuotientGroup.mk ⟨m, ExactLayer.exactCore_le_left w K hm⟩ :
      ↥K ⧸ classicalInvolutionOddCore ↥K) = twinQuot K w ⟨m, hm⟩ := rfl
  have h2 : (QuotientGroup.quotientKerEquivOfSurjective (twinQuot K w)
      (toOddQuot_surjective _ hcov)).symm (twinQuot K w ⟨m, hm⟩) =
      (QuotientGroup.mk ⟨m, hm⟩ : ↥(ExactLayer.exactCore w K) ⧸ (twinQuot K w).ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [h1, twinEquiv, MulEquiv.trans_apply, MulEquiv.trans_apply, h2]
  rfl
end Twin
end Asc77.CX

end

section

set_option linter.unusedSectionVars false
namespace Asc77.CX
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.CX
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
section Pkg
variable {G : Type} [Group G] [Finite G]

structure LayerPkg (Ω : Set (Subgroup G)) (K K' : Subgroup G) (z w : G) : Prop where
  zY : z ∈ ExactLayer.exactLayer Ω w
  tq : K ∈ ExactLayer.tqMembers Ω w
  tq' : K' ∈ ExactLayer.tqMembers Ω w
  odd : oddCoreOf (T7H.exactImg Ω w K) = ⊥
  odd' : oddCoreOf (T7H.exactImg Ω w K') = ⊥
  cov : ∀ x ∈ K, ∃ i ∈ ExactLayer.exactCore w K, ∃ n ∈ oddCoreIn K, x = i * n
  cov' : ∀ x ∈ K', ∃ i ∈ ExactLayer.exactCore w K', ∃ n ∈ oddCoreIn K', x = i * n

noncomputable abbrev vtx {Ω : Set (Subgroup G)} {K K' : Subgroup G} {z w : G}
    (P : LayerPkg Ω K K' z w)
    (β : MulAut (↥(ExactLayer.exactLayer Ω w) ⧸ classicalInvolutionOddCore ↥(ExactLayer.exactLayer
        Ω w)))
    (hA : T7H.exactImg Ω w K ≤ Goldschmidt75.perfRes (fixSubgroup β))
    (hA' : T7H.exactImg Ω w K' ≤ Goldschmidt75.perfRes (fixSubgroup β)) :
    TwinGroup (↥K ⧸ classicalInvolutionOddCore ↥K) (↥K' ⧸ classicalInvolutionOddCore ↥K') :=
  (centTG _ _ β hA hA').rebase (twinEquiv P.tq P.cov P.odd) (twinEquiv P.tq' P.cov' P.odd')

theorem perfRes_normalizes {Ω : Set (Subgroup G)} (hc : ConjInvariant Ω) {w w' n h : G}
    (hn : n ∈ Goldschmidt75.perfRes (ExactLayer.exactLayer Ω w ⊓ Subgroup.centralizer ({w'} : Set
        G)))
    (hh : h ∈ Goldschmidt75.perfRes (ExactLayer.exactLayer Ω w' ⊓ Subgroup.centralizer ({w} : Set
        G))) :
    n * h * n⁻¹ ∈
      Goldschmidt75.perfRes (ExactLayer.exactLayer Ω w' ⊓ Subgroup.centralizer ({w} : Set G)) := by
  have hn' := Goldschmidt75.perfRes_le _ hn
  have hnC' : n ∈ Subgroup.centralizer ({w'} : Set G) := hn'.2
  have hnC : n ∈ Subgroup.centralizer ({w} : Set G) := ExactLayer.exactLayer_le_centralizer Ω w
      hn'.1
  have hconj : conjSub n (ExactLayer.exactLayer Ω w' ⊓ Subgroup.centralizer ({w} : Set G)) =
      ExactLayer.exactLayer Ω w' ⊓ Subgroup.centralizer ({w} : Set G) := by
    unfold conjSub
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj n).injective]
    change conjSub n (ExactLayer.exactLayer Ω w') ⊓ conjSub n (Subgroup.centralizer ({w} : Set G))
        = _
    rw [ExactLayer.conjSub_exactLayer hc hnC', conjSub_eq_self_of_mem hnC]
  have hnN := Goldschmidt75.normalizer_le_normalizer_perfRes _
    (mem_normalizer_iff_conjSub_eq.mpr hconj)
  exact (Subgroup.mem_normalizer_iff.mp hnN h).mp hh
end Pkg
section Bad
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {z : G} {S : Sylow 2 G} {R R' : Subgroup G}
  {t u₁ u₂ : G}

variable [CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.Facts25V] in
theorem layerPkg_of_bad (h6 : Layer6Twin 3 1) (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂)
    {w : G} (hwA : w ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hw2 : w * w = 1) (hw1 : w ≠ 1) (hwbad : z ∉ zStarOf (Subgroup.centralizer ({w} : Set G))) :
    LayerPkg Ω K K' z w := by
  have hs := hyp.std.setting
  have hΩ : HypOmegaModT Ω := hs.stand.modU
  obtain ⟨hzY, hK₂, hK₂', -, hO, hO', -⟩ := twinFacts_of_bad h6 hyp hwA hw2 hw1 hwbad
  have hc₁ : Generic.IsClassicalMember K z := isClassicalMember_of_twin hΩ hs.stand.mem hs.hz
  have hc₂ : Generic.IsClassicalMember K' z :=
    isClassicalMember_of_twin hΩ hs.hK'.1 (isUniqueInvolution_of_mem_twinSet hs.hz hs.hK')
  have hw2' := isPGroup_zpowers_of_sq_eq_one hw2
  exact ⟨hzY, hK₂, hK₂', hO, hO', ExactLayer.exactCore_cover hc₁ hw2' hK₂.2,
    ExactLayer.exactCore_cover hc₂ hw2' hK₂'.2⟩

theorem conj_mem_oddCoreOf_exactLayer {Ω : Set (Subgroup G)} (hc : ConjInvariant Ω) {w' n o : G}
    (hn : n ∈ Subgroup.centralizer ({w'} : Set G))
    (ho : o ∈ oddCoreOf (ExactLayer.exactLayer Ω w')) :
    n * o * n⁻¹ ∈ oddCoreOf (ExactLayer.exactLayer Ω w') := by
  have h1 : n * o * n⁻¹ ∈ conjSub n (oddCoreOf (ExactLayer.exactLayer Ω w')) :=
    Generic.conj_mem_conjSub ho
  rwa [← CFSG.ClassicalInvolution.Asc77.Thompson.oddCoreOf_conjSub_eq,
    ExactLayer.conjSub_exactLayer hc hn] at h1

theorem twinIso_vtx (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {w w' : G}
    (hwA : w ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hw'A : w' ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hw2 : w * w = 1) (hw'2 : w' * w' = 1) (hw'C : w' ∈ Subgroup.centralizer ({w} : Set G))
    (hwC : w ∈ Subgroup.centralizer ({w'} : Set G)) (P : LayerPkg Ω K K' z w)
    (P' : LayerPkg Ω K K' z w')
    {β : MulAut (↥(ExactLayer.exactLayer Ω w) ⧸ classicalInvolutionOddCore ↥(ExactLayer.exactLayer
        Ω w))}
    (hβ : β = actW hyp.std.setting.stand.modU.conjInvariant w ⟨w', hw'C⟩)
    {β' : MulAut (↥(ExactLayer.exactLayer Ω w') ⧸ classicalInvolutionOddCore
        ↥(ExactLayer.exactLayer Ω w'))}
    (hβ' : β' = actW hyp.std.setting.stand.modU.conjInvariant w' ⟨w, hwC⟩)
    (hA : T7H.exactImg Ω w K ≤ Goldschmidt75.perfRes (fixSubgroup β))
    (hA' : T7H.exactImg Ω w K' ≤ Goldschmidt75.perfRes (fixSubgroup β))
    (hB : T7H.exactImg Ω w' K ≤ Goldschmidt75.perfRes (fixSubgroup β'))
    (hB' : T7H.exactImg Ω w' K' ≤ Goldschmidt75.perfRes (fixSubgroup β'))
    (h5 : IsOm5 (centTG _ _ β hA hA')) (h5' : IsOm5 (centTG _ _ β' hB hB')) :
    TwinIso 3 (vtx P β hA hA') (vtx P' β' hB hB') := by
  classical
  subst hβ hβ'
  have hs := hyp.std.setting
  have hc : ConjInvariant Ω := hs.stand.modU.conjInvariant
  have hz2 : z * z = 1 := hs.hz.sq
  have hz1 : z ≠ 1 := hs.hz.ne_one
  have hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s := hyp.hzS
  set F := Subgroup.closure ({w, w'} : Set G) with hF
  have hFA := closure_pair_le hwA hw'A
  have hF2 : IsPGroup 2 F := S.isPGroup'.to_le (hFA.trans inf_le_left)
  have hwF : w ∈ F := Subgroup.subset_closure (Set.mem_insert w _)
  have hw'F : w' ∈ F := Subgroup.subset_closure (Set.mem_insert_of_mem w rfl)
  have hFK : F ≤ trivialOnQuot K := fun a ha => (mem_trivialOnQuot_of_mem_A hyp (hFA ha)).1
  have hFK' : F ≤ trivialOnQuot K' := fun a ha => (mem_trivialOnQuot_of_mem_A hyp (hFA ha)).2
  set N := Goldschmidt75.perfRes
    (ExactLayer.exactLayer Ω w ⊓ Subgroup.centralizer ({w'} : Set G)) with hN
  set N' := Goldschmidt75.perfRes
    (ExactLayer.exactLayer Ω w' ⊓ Subgroup.centralizer ({w} : Set G)) with hN'
  have hNX : N ≤ ExactLayer.exactLayer Ω w :=
    (Goldschmidt75.perfRes_le _).trans inf_le_left
  have hNX' : N' ≤ ExactLayer.exactLayer Ω w' :=
    (Goldschmidt75.perfRes_le _).trans inf_le_left
  have hNT : (N.subgroupOf (ExactLayer.exactLayer Ω w)).map
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω w))) =
      Goldschmidt75.perfRes (fixSubgroup (actW hc w ⟨w', hw'C⟩)) :=
    map_perfRes_fix_eq hw'2 (ExactLayer.conjSub_exactLayer hc hw'C)
  have hNT' : (N'.subgroupOf (ExactLayer.exactLayer Ω w')).map
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω w'))) =
      Goldschmidt75.perfRes (fixSubgroup (actW hc w' ⟨w, hwC⟩)) :=
    map_perfRes_fix_eq hw2 (ExactLayer.conjSub_exactLayer hc hwC)
  have hNN' : ∀ n ∈ N, ∀ h ∈ N', n * h * n⁻¹ ∈ N' := fun n hn h hh =>
    perfRes_normalizes hc hn hh
  have hN'N : ∀ n ∈ N', ∀ h ∈ N, n * h * n⁻¹ ∈ N := fun n hn h hh =>
    perfRes_normalizes (w := w') (w' := w) hc hn hh
  have hOX' : ∀ n ∈ N, ∀ o ∈ oddCoreOf (ExactLayer.exactLayer Ω w'),
      n * o * n⁻¹ ∈ oddCoreOf (ExactLayer.exactLayer Ω w') := fun n hn o ho =>
    conj_mem_oddCoreOf_exactLayer hc ((Goldschmidt75.perfRes_le _ hn).2) ho
  have hOX : ∀ n ∈ N', ∀ o ∈ oddCoreOf (ExactLayer.exactLayer Ω w),
      n * o * n⁻¹ ∈ oddCoreOf (ExactLayer.exactLayer Ω w) := fun n hn o ho =>
    conj_mem_oddCoreOf_exactLayer hc ((Goldschmidt75.perfRes_le _ hn).2) ho
  have hTs : IsSimpleGroup ↥(Goldschmidt75.perfRes (fixSubgroup (actW hc w ⟨w', hw'C⟩))) := by
    obtain ⟨Φ, z', a₀, b₀, hd⟩ := h5
    exact isSimpleGroup_of_om5Data hd
  have hT's : IsSimpleGroup ↥(Goldschmidt75.perfRes (fixSubgroup (actW hc w' ⟨w, hwC⟩))) := by
    obtain ⟨Φ, z', a₀, b₀, hd⟩ := h5'
    exact isSimpleGroup_of_om5Data hd
  have hzK : z ∈ K := hs.hz.mem
  have hzw : z ∈ ExactLayer.exactCore w K :=
    ⟨hzK, Subgroup.mem_centralizer_singleton_iff.mpr (hzS w hwA.1).symm⟩
  have hzw' : z ∈ ExactLayer.exactCore w' K :=
    ⟨hzK, Subgroup.mem_centralizer_singleton_iff.mpr (hzS w' hw'A.1).symm⟩
  have hzT : z ∈ Q3T7P25.U.preimgOdd (ExactLayer.exactLayer Ω w)
      (Goldschmidt75.perfRes (fixSubgroup (actW hc w ⟨w', hw'C⟩))) :=
    Q3T7P25.U.mem_preimgOdd.mpr ⟨P.zY, hA (T7H.mem_exactImg hzw P.zY)⟩
  have hzT' : z ∈ Q3T7P25.U.preimgOdd (ExactLayer.exactLayer Ω w')
      (Goldschmidt75.perfRes (fixSubgroup (actW hc w' ⟨w, hwC⟩))) :=
    Q3T7P25.U.mem_preimgOdd.mpr ⟨P'.zY, hB (T7H.mem_exactImg hzw' P'.zY)⟩
  obtain ⟨φ, hφ⟩ := Q3T7P25.U.exists_equiv_of_twin_layers hNX hNX' hNT hNT' hNN' hN'N hOX' hOX
    hTs hT's P.zY P'.zY hz2 hzT hzT' (mk_ne_one_of_involution P.zY hz2 hz1)
    (mk_ne_one_of_involution P'.zY hz2 hz1)
  have hFw : Subgroup.centralizer (F : Set G) ≤ Subgroup.centralizer ({w} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hwF)
  have hFw' : Subgroup.centralizer (F : Set G) ≤ Subgroup.centralizer ({w'} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hw'F)
  have hJK : K ⊓ Subgroup.centralizer (F : Set G) ≤ K := inf_le_left
  have hJK' : K' ⊓ Subgroup.centralizer (F : Set G) ≤ K' := inf_le_left
  have hsurjK := toOddQuot_surjective hJK (fun x hx => exists_mem_inf_centralizer_mul hF2 hFK hx)
  have hsurjK' := toOddQuot_surjective hJK'
    (fun x hx => exists_mem_inf_centralizer_mul hF2 hFK' hx)
  refine twinIso_of_compat φ (fun k => ?_) (fun k => ?_)
  · obtain ⟨m, rfl⟩ := hsurjK k
    have hmw : (m : G) ∈ ExactLayer.exactCore w K := ⟨m.2.1, hFw m.2.2⟩
    have hmw' : (m : G) ∈ ExactLayer.exactCore w' K := ⟨m.2.1, hFw' m.2.2⟩
    have hX : (m : G) ∈ ExactLayer.exactLayer Ω w := ExactLayer.exactCore_le_exactLayer P.tq hmw
    have hX' : (m : G) ∈ ExactLayer.exactLayer Ω w' :=
      ExactLayer.exactCore_le_exactLayer P'.tq hmw'
    let t₁ : ↥(Goldschmidt75.perfRes (fixSubgroup (actW hc w ⟨w', hw'C⟩))) :=
      ((vtx P _ hA hA').ι (toOddQuot hJK m) : (vtx P _ hA hA').X)
    let t₂ : ↥(Goldschmidt75.perfRes (fixSubgroup (actW hc w' ⟨w, hwC⟩))) :=
      ((vtx P' _ hB hB').ι (toOddQuot hJK m) : (vtx P' _ hB hB').X)
    have ht₁ : (t₁ : ↥(ExactLayer.exactLayer Ω w) ⧸
        classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω w)) =
        (QuotientGroup.mk ⟨(m : G), hX⟩ : ↥(ExactLayer.exactLayer Ω w) ⧸
          classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω w)) :=
      twinEquiv_mk P.tq P.cov P.odd hmw
    have ht₂ : (t₂ : ↥(ExactLayer.exactLayer Ω w') ⧸
        classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω w')) =
        (QuotientGroup.mk ⟨(m : G), hX'⟩ : ↥(ExactLayer.exactLayer Ω w') ⧸
          classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω w')) :=
      twinEquiv_mk P'.tq P'.cov P'.odd hmw'
    have e1 := hφ m hX hX'
      (Q3T7P25.U.mem_preimgOdd.mpr ⟨hX, hA (T7H.mem_exactImg hmw hX)⟩)
      (Q3T7P25.U.mem_preimgOdd.mpr ⟨hX', hB (T7H.mem_exactImg hmw' hX')⟩) t₁ ht₁
    exact Subtype.ext (e1.trans ht₂.symm)
  · obtain ⟨m, rfl⟩ := hsurjK' k
    have hmw : (m : G) ∈ ExactLayer.exactCore w K' := ⟨m.2.1, hFw m.2.2⟩
    have hmw' : (m : G) ∈ ExactLayer.exactCore w' K' := ⟨m.2.1, hFw' m.2.2⟩
    have hX : (m : G) ∈ ExactLayer.exactLayer Ω w := ExactLayer.exactCore_le_exactLayer P.tq' hmw
    have hX' : (m : G) ∈ ExactLayer.exactLayer Ω w' :=
      ExactLayer.exactCore_le_exactLayer P'.tq' hmw'
    let t₁ : ↥(Goldschmidt75.perfRes (fixSubgroup (actW hc w ⟨w', hw'C⟩))) :=
      ((vtx P _ hA hA').ι' (toOddQuot hJK' m) : (vtx P _ hA hA').X)
    let t₂ : ↥(Goldschmidt75.perfRes (fixSubgroup (actW hc w' ⟨w, hwC⟩))) :=
      ((vtx P' _ hB hB').ι' (toOddQuot hJK' m) : (vtx P' _ hB hB').X)
    have ht₁ : (t₁ : ↥(ExactLayer.exactLayer Ω w) ⧸
        classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω w)) =
        (QuotientGroup.mk ⟨(m : G), hX⟩ : ↥(ExactLayer.exactLayer Ω w) ⧸
          classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω w)) :=
      twinEquiv_mk P.tq' P.cov' P.odd' hmw
    have ht₂ : (t₂ : ↥(ExactLayer.exactLayer Ω w') ⧸
        classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω w')) =
        (QuotientGroup.mk ⟨(m : G), hX'⟩ : ↥(ExactLayer.exactLayer Ω w') ⧸
          classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω w')) :=
      twinEquiv_mk P'.tq' P'.cov' P'.odd' hmw'
    have e1 := hφ m hX hX'
      (Q3T7P25.U.mem_preimgOdd.mpr ⟨hX, hA' (T7H.mem_exactImg hmw hX)⟩)
      (Q3T7P25.U.mem_preimgOdd.mpr ⟨hX', hB' (T7H.mem_exactImg hmw' hX')⟩) t₁ ht₁
    exact Subtype.ext (e1.trans ht₂.symm)

end Bad
end Asc77.CX

end

section

set_option linter.unusedSectionVars false
namespace Asc77.CX
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.CX
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
section Face
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {z : G} {S : Sylow 2 G} {R R' : Subgroup G}
  {t u₁ u₂ : G}

variable [CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.Facts25V] in
theorem refl_edge (h6 : Layer6Twin 3 1) (h2 : Om6ReflDiag)
    (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {w x y : G}
    (hwA : w ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hw2 : w * w = 1) (hw1 : w ≠ 1) (hwbad : z ∉ zStarOf (Subgroup.centralizer ({w} : Set G)))
    (htyp : LayerOrthType Ω w 5 true ∨ LayerOrthType Ω w 6 (!piSign 3 1))
    (hxA : x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hyA : y ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hx : x ∈ Subgroup.centralizer ({w} : Set G)) (hy : y ∈ Subgroup.centralizer ({w} : Set G))
    (hyx : y = x * w * z) (hzY : z ∈ ExactLayer.exactLayer Ω w)
    (hbx : z ∉ zStarOf (Subgroup.centralizer ({w, x} : Set G)))
    (hby : z ∉ zStarOf (Subgroup.centralizer ({w, y} : Set G))) :
    actW hyp.std.setting.stand.modU.conjInvariant w ⟨y, hy⟩ =
        actW hyp.std.setting.stand.modU.conjInvariant w ⟨x, hx⟩ *
          MulAut.conj (T7H.toBar Ω w z hzY) ∧
      ∃ (hA : T7H.exactImg Ω w K ≤ Goldschmidt75.perfRes
          (fixSubgroup (actW hyp.std.setting.stand.modU.conjInvariant w ⟨x, hx⟩)))
        (hA' : T7H.exactImg Ω w K' ≤ Goldschmidt75.perfRes
          (fixSubgroup (actW hyp.std.setting.stand.modU.conjInvariant w ⟨x, hx⟩)))
        (hB : T7H.exactImg Ω w K ≤ Goldschmidt75.perfRes
          (fixSubgroup (actW hyp.std.setting.stand.modU.conjInvariant w ⟨x, hx⟩ *
            MulAut.conj (T7H.toBar Ω w z hzY))))
        (hB' : T7H.exactImg Ω w K' ≤ Goldschmidt75.perfRes
          (fixSubgroup (actW hyp.std.setting.stand.modU.conjInvariant w ⟨x, hx⟩ *
            MulAut.conj (T7H.toBar Ω w z hzY)))),
        IsOm5 (centTG _ _ _ hA hA') ∧ IsOm5 (centTG _ _ _ hB hB') ∧
          ¬ DiagRel 3 (centTG _ _ _ hA hA') (centTG _ _ _ hB hB') := by
  have hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s := hyp.hzS
  have hc := hyp.std.setting.stand.modU.conjInvariant
  obtain ⟨hzY', hK₂, hK₂', -, hO, hO', -⟩ := twinFacts_of_bad h6 hyp hwA hw2 hw1 hwbad
  have hz : z ∈ Subgroup.centralizer ({w} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hzS w hwA.1).symm
  have hwC : w ∈ Subgroup.centralizer ({w} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hyeq : actW hc w ⟨y, hy⟩ = actW hc w ⟨x, hx⟩ * MulAut.conj (T7H.toBar Ω w z hzY) := by
    have e : (⟨y, hy⟩ : ↥(Subgroup.centralizer ({w} : Set G))) = ⟨x, hx⟩ * ⟨w, hwC⟩ * ⟨z, hz⟩ :=
      Subtype.ext hyx
    rw [e, map_mul, map_mul, actW_self, mul_one, actW_eq_conj hc hz hzY]
  have hβz : actW hc w ⟨x, hx⟩ ≠ MulAut.conj (T7H.toBar Ω w z hzY) := fun h =>
    hbx ((good_iff_actW h6 hyp hwA hw2 hw1 hwbad hxA hx hzY).mpr h)
  have hβ1 : actW hc w ⟨x, hx⟩ ≠ 1 := by
    intro h
    apply hby
    refine (good_iff_actW h6 hyp hwA hw2 hw1 hwbad hyA hy hzY).mpr ?_
    rw [hyeq, h, one_mul]
  obtain ⟨hu₁Y, hu₂Y, hOm⟩ :=
    om6mData_of_actW h6 hyp hwA hw2 hw1 hwbad htyp hxA hx hzY hβ1 hβz
  obtain ⟨hfixK, hfixK'⟩ := actW_fix hyp hw2 hK₂ hK₂' hO hO' hxA hx
  have hββ := actW_mul_self h6 hyp hwA hw2 hw1 hwbad hxA hx
  exact ⟨hyeq, h2 _ _ _ _ _ _ _ hOm _ hfixK hfixK' hββ hβ1 hβz⟩

variable [CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.Facts25V] in
theorem false_of_face (h6 : Layer6Twin 3 1) (h1 : DiagThree) (h2 : Om6ReflDiag)
    (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {w₁ w₂ w₃ : G}
    (hA₁ : w₁ ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hA₂ : w₂ ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hA₃ : w₃ ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hs₁ : w₁ * w₁ = 1) (hs₂ : w₂ * w₂ = 1) (hs₃ : w₃ * w₃ = 1)
    (hn₁ : w₁ ≠ 1) (hn₂ : w₂ ≠ 1) (hn₃ : w₃ ≠ 1)
    (h₁₂ : w₁ * w₂ = w₂ * w₁) (h₁₃ : w₁ * w₃ = w₃ * w₁) (h₂₃ : w₂ * w₃ = w₃ * w₂)
    (hprod : w₁ * w₂ * w₃ = z)
    (hb₁ : z ∉ zStarOf (Subgroup.centralizer ({w₁} : Set G)))
    (hb₂ : z ∉ zStarOf (Subgroup.centralizer ({w₂} : Set G)))
    (hb₃ : z ∉ zStarOf (Subgroup.centralizer ({w₃} : Set G)))
    (ht₁ : LayerOrthType Ω w₁ 5 true ∨ LayerOrthType Ω w₁ 6 (!piSign 3 1))
    (ht₂ : LayerOrthType Ω w₂ 5 true ∨ LayerOrthType Ω w₂ 6 (!piSign 3 1))
    (ht₃ : LayerOrthType Ω w₃ 5 true ∨ LayerOrthType Ω w₃ 6 (!piSign 3 1))
    (hF₁₂ : z ∉ zStarOf (Subgroup.centralizer ({w₁, w₂} : Set G)))
    (hF₁₃ : z ∉ zStarOf (Subgroup.centralizer ({w₁, w₃} : Set G)))
    (hF₂₃ : z ∉ zStarOf (Subgroup.centralizer ({w₂, w₃} : Set G))) : False := by
  have hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s := hyp.hzS
  have hC : ∀ {a b : G}, a * b = b * a → b ∈ Subgroup.centralizer ({a} : Set G) := fun h =>
    Subgroup.mem_centralizer_singleton_iff.mpr h.symm
  have hC₁₂ := hC h₁₂
  have hC₂₁ := hC h₁₂.symm
  have hC₁₃ := hC h₁₃
  have hC₃₁ := hC h₁₃.symm
  have hC₂₃ := hC h₂₃
  have hC₃₂ := hC h₂₃.symm
  have e₁ : w₃ = w₂ * w₁ * z := by
    calc w₃ = w₂ * (w₁ * w₁) * w₂ * w₃ := by rw [hs₁, mul_one, hs₂, one_mul]
      _ = w₂ * w₁ * (w₁ * w₂ * w₃) := by group
      _ = w₂ * w₁ * z := by rw [hprod]
  have e₂ : w₃ = w₁ * w₂ * z := by rw [e₁, h₁₂]
  have e₃ : w₂ = w₁ * w₃ * z := by
    calc w₂ = (w₁ * w₁) * w₂ * (w₃ * w₃) := by rw [hs₁, hs₃, one_mul, mul_one]
      _ = w₁ * (w₁ * w₂ * w₃) * w₃ := by group
      _ = w₁ * w₃ * z := by rw [hprod, mul_assoc, (hzS w₃ hA₃.1).symm, ← mul_assoc]
  have P₁ := layerPkg_of_bad h6 hyp hA₁ hs₁ hn₁ hb₁
  have P₂ := layerPkg_of_bad h6 hyp hA₂ hs₂ hn₂ hb₂
  have P₃ := layerPkg_of_bad h6 hyp hA₃ hs₃ hn₃ hb₃
  obtain ⟨q₁, hA₁₂, hA₁₂', hB₁₃, hB₁₃', h5₁₂, h5₁₃, hnd₁⟩ := refl_edge h6 h2 hyp hA₁ hs₁ hn₁ hb₁
    ht₁ hA₂ hA₃ hC₁₂ hC₁₃ e₁ P₁.zY hF₁₂ hF₁₃
  obtain ⟨q₂, hA₂₁, hA₂₁', hB₂₃, hB₂₃', h5₂₁, h5₂₃, hnd₂⟩ := refl_edge h6 h2 hyp hA₂ hs₂ hn₂ hb₂
    ht₂ hA₁ hA₃ hC₂₁ hC₂₃ e₂ P₂.zY (by rw [centralizer_pair_comm]; exact hF₁₂) hF₂₃
  obtain ⟨q₃, hA₃₁, hA₃₁', hB₃₂, hB₃₂', h5₃₁, h5₃₂, hnd₃⟩ := refl_edge h6 h2 hyp hA₃ hs₃ hn₃ hb₃
    ht₃ hA₁ hA₂ hC₃₁ hC₃₂ e₃ P₃.zY (by rw [centralizer_pair_comm]; exact hF₁₃)
    (by rw [centralizer_pair_comm]; exact hF₂₃)
  have I₁₂ := twinIso_vtx hyp hA₁ hA₂ hs₁ hs₂ hC₁₂ hC₂₁ P₁ P₂ rfl rfl hA₁₂ hA₁₂' hA₂₁ hA₂₁'
    h5₁₂ h5₂₁
  have I₁₃ := twinIso_vtx hyp hA₁ hA₃ hs₁ hs₃ hC₁₃ hC₃₁ P₁ P₃ q₁.symm rfl hB₁₃ hB₁₃' hA₃₁ hA₃₁'
    h5₁₃ h5₃₁
  have I₂₃ := twinIso_vtx hyp hA₂ hA₃ hs₂ hs₃ hC₂₃ hC₃₂ P₂ P₃ q₂.symm q₃.symm hB₂₃ hB₂₃' hB₃₂
    hB₃₂' h5₂₃ h5₃₂
  rcases h1 _ _ (vtx P₁ _ hA₁₂ hA₁₂') (vtx P₁ _ hB₁₃ hB₁₃') (vtx P₂ _ hB₂₃ hB₂₃') h5₁₂ h5₁₃ h5₂₃
    with d | d | d
  · exact hnd₁ ((diagRel_rebase_iff _ _).mp d)
  · exact hnd₂ ((diagRel_rebase_iff _ _).mp (I₁₂.symm.trans_diagRel d))
  · exact hnd₃ ((diagRel_rebase_iff _ _).mp (I₁₃.symm.trans_diagRel (d.trans_twinIso I₂₃)))

variable [CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.Facts25V] in
theorem parityE4_of (h1 : DiagThree) (h2 : Om6ReflDiag) : ParityE4 := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp d₁ d₂ hd₁A hd₂A hs₁ hs₂ hc₁₂ hn₁ hn₂ hne hz₁ hz₂
    hz₁₂ hD₀ hbad htyp
  have h6 := layer6Twin_proved 3 1
  have hzA := T7T.z_mem_centralizer_of_hyp hyp
  have hz2 : z * z = 1 := hyp.std.setting.hz.sq
  have hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s := hyp.hzS
  have m₁ : d₁ ∈ ({d₁, d₂, d₁ * d₂} : Set G) := Set.mem_insert _ _
  have m₂ : d₂ ∈ ({d₁, d₂, d₁ * d₂} : Set G) := Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have m₃ : d₁ * d₂ ∈ ({d₁, d₂, d₁ * d₂} : Set G) :=
    Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)
  have C₁ : Commute d₁ z := hzS d₁ hd₁A.1
  have C₂ : Commute d₂ z := hzS d₂ hd₂A.1
  have C₁₂ : Commute d₁ d₂ := hc₁₂
  have cm : ∀ {x w : G}, Commute x w → x ∈ Subgroup.centralizer ({w} : Set G) := fun h =>
    Subgroup.mem_centralizer_singleton_iff.mpr h.eq
  have hA₃ := Subgroup.mul_mem _ hd₁A hd₂A
  have hB₁ := Subgroup.mul_mem _ hd₁A hzA
  have hB₂ := Subgroup.mul_mem _ hd₂A hzA
  have hB₃ := Subgroup.mul_mem _ hA₃ hzA
  have sq : ∀ {a b : G}, Commute a b → a * a = 1 → b * b = 1 → a * b * (a * b) = 1 :=
    fun {a b} h ha hb => by
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [h.eq]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha, hb, one_mul]
  have sa₃ : d₁ * d₂ * (d₁ * d₂) = 1 := sq C₁₂ hs₁ hs₂
  have sb₁ : d₁ * z * (d₁ * z) = 1 := sq C₁ hs₁ hz2
  have sb₂ : d₂ * z * (d₂ * z) = 1 := sq C₂ hs₂ hz2
  have sb₃ : d₁ * d₂ * z * (d₁ * d₂ * z) = 1 := sq (C₁.mul_left C₂) sa₃ hz2
  have ne : ∀ {a b : G}, a * a = 1 → a ≠ b → a * b ≠ 1 := fun {a b} ha hab h => by
    apply hab
    calc a = a * (a * b) := by rw [h, mul_one]
      _ = b := by rw [← mul_assoc, ha, one_mul]
  have na₃ : d₁ * d₂ ≠ 1 := ne hs₁ hne
  have nb₁ : d₁ * z ≠ 1 := ne hs₁ (Ne.symm hz₁)
  have nb₂ : d₂ * z ≠ 1 := ne hs₂ (Ne.symm hz₂)
  have nb₃ : d₁ * d₂ * z ≠ 1 := ne sa₃ (Ne.symm hz₁₂)
  obtain ⟨bd₁, bb₁⟩ := hbad d₁ m₁
  obtain ⟨bd₂, bb₂⟩ := hbad d₂ m₂
  obtain ⟨ba₃, bb₃⟩ := hbad _ m₃
  obtain ⟨td₁, tb₁⟩ := htyp d₁ m₁
  obtain ⟨td₂, tb₂⟩ := htyp d₂ m₂
  obtain ⟨ta₃, tb₃⟩ := htyp _ m₃
  have L₁ := not_good_and_good h6 hyp hB₁ sb₁ nb₁ bb₁ hd₂A (cm (C₁₂.symm.mul_right C₂))
  have L₂ := not_good_and_good h6 hyp hB₂ sb₂ nb₂ bb₂ hd₁A (cm (C₁₂.mul_right C₁))
  have L₃ := not_good_and_good h6 hyp hB₃ sb₃ nb₃ bb₃ hd₁A
    (cm (((Commute.refl d₁).mul_right C₁₂).mul_right C₁))
  rw [centralizer_pair_comm (d₂ * z), centralizer_pair_comm (d₂ * z)] at L₂
  have r₁ : d₁ * d₂ * z = d₁ * (d₂ * z) := mul_assoc _ _ _
  have r₂ : d₁ * d₂ * z = d₁ * z * d₂ := by
    rw [mul_assoc d₁ z, ← C₂.eq, ← mul_assoc]
  rw [centralizer_pair_comm (d₁ * d₂ * z), centralizer_pair_comm (d₁ * d₂ * z),
    centralizer_pair_eq_of r₁, centralizer_pair_eq_of r₂] at L₃
  by_cases G1 : z ∈ zStarOf (Subgroup.centralizer ({d₁, d₂ * z} : Set G))
  · have nG2 := fun h => L₃ ⟨G1, h⟩
    have nG3 := fun h => L₂ ⟨G1, h⟩
    have r₃ : d₁ * d₂ = d₁ * z * (d₂ * z) := by
      calc d₁ * d₂ = d₁ * d₂ * (z * z) := by rw [hz2, mul_one]
        _ = d₁ * (d₂ * z) * z := by group
        _ = d₁ * (z * d₂) * z := by rw [C₂.eq]
        _ = d₁ * z * (d₂ * z) := by group
    refine false_of_face h6 h1 h2 hyp hd₂A hA₃ hB₁ hs₂ sa₃ sb₁ hn₂ na₃ nb₁
      (C₁₂.symm.mul_right (Commute.refl d₂)).eq (C₁₂.symm.mul_right C₂).eq
      (Commute.mul_left ((Commute.refl d₁).mul_right C₁) (C₁₂.symm.mul_right C₂)).eq ?_
      bd₂ ba₃ bb₁ td₂ ta₃ tb₁ ?_ ?_ ?_
    · calc d₂ * (d₁ * d₂) * (d₁ * z) = d₂ * (d₂ * d₁) * (d₁ * z) := by rw [C₁₂.eq]
        _ = (d₂ * d₂) * (d₁ * d₁) * z := by group
        _ = z := by rw [hs₂, hs₁, one_mul, one_mul]
    · rw [centralizer_pair_eq_of C₁₂.eq, centralizer_pair_comm]
      exact hD₀
    · rw [centralizer_pair_comm]
      exact nG2
    · rw [centralizer_pair_comm, centralizer_pair_eq_of r₃]
      exact nG3
  · by_cases G2 : z ∈ zStarOf (Subgroup.centralizer ({d₁ * z, d₂} : Set G))
    · have nG3 := fun h => L₁ ⟨G2, h⟩
      have r₄ : d₁ * d₂ = d₂ * z * (d₁ * z) := by
        calc d₁ * d₂ = d₂ * d₁ * (z * z) := by rw [hz2, mul_one, C₁₂.eq]
          _ = d₂ * (d₁ * z) * z := by group
          _ = d₂ * (z * d₁) * z := by rw [C₁.eq]
          _ = d₂ * z * (d₁ * z) := by group
      refine false_of_face h6 h1 h2 hyp hd₁A hA₃ hB₂ hs₁ sa₃ sb₂ hn₁ na₃ nb₂
        ((Commute.refl d₁).mul_right C₁₂).eq (C₁₂.mul_right C₁).eq
        (Commute.mul_left (C₁₂.mul_right C₁) ((Commute.refl d₂).mul_right C₂)).eq ?_
        bd₁ ba₃ bb₂ td₁ ta₃ tb₂ ?_ G1 ?_
      · calc d₁ * (d₁ * d₂) * (d₂ * z) = (d₁ * d₁) * (d₂ * d₂) * z := by group
          _ = z := by rw [hs₁, hs₂, one_mul, one_mul]
      · rw [centralizer_pair_mul]
        exact hD₀
      · rw [centralizer_pair_comm, centralizer_pair_eq_of r₄, centralizer_pair_comm]
        exact nG3
    · have r₅ : d₁ * d₂ * z = d₂ * (d₁ * z) := by rw [C₁₂.eq, mul_assoc]
      refine false_of_face h6 h1 h2 hyp hd₁A hd₂A hB₃ hs₁ hs₂ sb₃ hn₁ hn₂ nb₃ C₁₂.eq
        (((Commute.refl d₁).mul_right C₁₂).mul_right C₁).eq
        ((C₁₂.symm.mul_right (Commute.refl d₂)).mul_right C₂).eq ?_
        bd₁ bd₂ bb₃ td₁ td₂ tb₃ hD₀ ?_ ?_
      · calc d₁ * d₂ * (d₁ * d₂ * z) = d₁ * (d₂ * d₁) * d₂ * z := by group
          _ = d₁ * (d₁ * d₂) * d₂ * z := by rw [← C₁₂.eq]
          _ = (d₁ * d₁) * (d₂ * d₂) * z := by group
          _ = z := by rw [hs₁, hs₂, one_mul, one_mul]
      · rw [centralizer_pair_eq_of r₁]
        exact G1
      · rw [centralizer_pair_eq_of r₅, centralizer_pair_comm]
        exact G2
end Face
end Asc77.CX

end

section

set_option linter.unusedSectionVars false
namespace Asc77.CX
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.CX
section Final

variable [CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.CX.Facts25V] in
theorem parityE4_of_om6ReflDiag (h2 : Om6ReflDiag) : ParityE4 :=
  parityE4_of diagThree_proved h2
end Final
end Asc77.CX

end

end CFSG.ClassicalInvolution.Q3.Q3T8
