module

public import CFSG.ClassicalInvolution.Asc77.AscCX6
public import CFSG.ClassicalInvolution.Asc77.AscCX9P

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.CX

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap

section Act

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem eq_one_or_eq_of_mem_zpowers {M : Type} [Group M] {β γ : M} (hβ : β * β = 1)
    (hγ : γ ∈ Subgroup.zpowers β) : γ = 1 ∨ γ = β := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hγ
  rcases Int.even_or_odd' k with ⟨k', hk | hk⟩
  · left
    rw [hk, zpow_mul, zpow_two, hβ, one_zpow]
  · right
    rw [hk, zpow_add_one, zpow_mul, zpow_two, hβ, one_zpow, one_mul]

@[expose] noncomputable def actW (hc : ConjInvariant Ω) (w : G) :
    ↥(Subgroup.centralizer ({w} : Set G)) →*
      MulAut (↥(exactLayer Ω w) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω w)) :=
  layerHom (exactLayer Ω w) (Subgroup.centralizer ({w} : Set G)) fun _ hx =>
    conjSub_exactLayer hc hx

theorem actW_apply (hc : ConjInvariant Ω) {w : G}
    (x : ↥(Subgroup.centralizer ({w} : Set G))) :
    actW hc w x = C25Y.layerAut (exactLayer Ω w) (conjSub_exactLayer hc x.2) := rfl

theorem layerAut_self (w : G) (h : conjSub w (exactLayer Ω w) = exactLayer Ω w) :
    C25Y.layerAut (exactLayer Ω w) h = 1 := by
  ext y
  refine QuotientGroup.induction_on y fun y => ?_
  rw [C25Y.layerAut_mk, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  rw [C25Y.coe_conjOnSub]
  have hy := Subgroup.mem_centralizer_singleton_iff.mp (exactLayer_le_centralizer Ω w y.2)
  rw [← hy, mul_inv_cancel_right]

theorem actW_self (hc : ConjInvariant Ω) (w : G) :
    actW hc w ⟨w, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ = 1 :=
  layerAut_self w _

theorem actW_eq_conj (hc : ConjInvariant Ω) {w x : G}
    (hx : x ∈ Subgroup.centralizer ({w} : Set G)) (hxY : x ∈ exactLayer Ω w) :
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
    (hzY : z ∈ exactLayer Ω w) (hxz : x * z ∈ Subgroup.centralizer ({w} : Set G)) :
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

theorem closure_pair_le {w x : G} {H : Subgroup G} (hw : w ∈ H) (hx : x ∈ H) :
    Subgroup.closure ({w, x} : Set G) ≤ H := by
  rw [Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with h | h
  · rw [h]
    exact hw
  · rw [h]
    exact hx

theorem mem_centralizer_pair_iff {w x g : G} :
    g ∈ Subgroup.centralizer ({w, x} : Set G) ↔
      g ∈ Subgroup.centralizer ({w} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) := by
  simp only [Subgroup.mem_centralizer_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    Subgroup.mem_inf, forall_eq_or_imp, forall_eq]

end Act

section Edge

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z : G} {S : Sylow 2 G} {R R' : Subgroup G}
  {t u₁ u₂ : G}


theorem actW_fix (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) {w x : G} (hw2 : w * w = 1)
    (hK₂ : K ∈ tqMembers Ω w) (hK₂' : K' ∈ tqMembers Ω w)
    (hO : oddCoreOf (T7H.exactImg Ω w K) = ⊥) (hO' : oddCoreOf (T7H.exactImg Ω w K') = ⊥)
    (hxA : x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hx : x ∈ Subgroup.centralizer ({w} : Set G)) :
    (∀ y ∈ T7H.exactImg Ω w K, actW hyp.std.setting.stand.hyp.conjInvariant w ⟨x, hx⟩ y = y) ∧
      ∀ y ∈ T7H.exactImg Ω w K', actW hyp.std.setting.stand.hyp.conjInvariant w ⟨x, hx⟩ y = y :=
  ⟨layerAut_fix_exactImg hyp.std.setting.stand.hyp (isPGroup_zpowers_of_sq_eq_one hw2) hK₂ hO hx
      (mem_trivialOnQuot_of_mem_A hyp hxA).1,
    layerAut_fix_exactImg hyp.std.setting.stand.hyp (isPGroup_zpowers_of_sq_eq_one hw2) hK₂' hO'
      hx (mem_trivialOnQuot_of_mem_A hyp hxA).2⟩

theorem actW_mul_self (h6 : Layer6Twin p f) (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂)
    {w x : G} (hwA : w ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hw2 : w * w = 1) (hw1 : w ≠ 1) (hwbad : z ∉ zStarOf (Subgroup.centralizer ({w} : Set G)))
    (hxA : x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hx : x ∈ Subgroup.centralizer ({w} : Set G)) :
    actW hyp.std.setting.stand.hyp.conjInvariant w ⟨x, hx⟩ *
      actW hyp.std.setting.stand.hyp.conjInvariant w ⟨x, hx⟩ = 1 := by
  have hΩ : HypOmegaMod p f Ω := hyp.std.setting.stand.hyp
  obtain ⟨hzY', hK₂, hK₂', -, hO, hO', hT2, -⟩ := twinFacts_of_bad h6 hyp hwA hw2 hw1 hwbad
  set E := Subgroup.zpowers x with hE
  have hEA : E ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr hxA
  have hE2 : IsPGroup 2 E := S.isPGroup'.to_le (hEA.trans inf_le_left)
  have hEb : E ≤ Subgroup.centralizer ({w} : Set G) := Subgroup.zpowers_le.mpr hx
  set lam := layerHom (exactLayer Ω w) E fun e he => conjSub_exactLayer hΩ.conjInvariant (hEb he)
    with hlam
  have hP2 : IsPGroup 2 lam.range := by
    rw [MonoidHom.range_eq_map]
    exact (hE2.to_subgroup ⊤).map lam
  obtain ⟨hexpP, -⟩ := hT2 lam.range hP2 fun β hβ => by
    obtain ⟨e, rfl⟩ := hβ
    exact actW_fix hyp hw2 hK₂ hK₂' hO hO' (hEA e.2) (hEb e.2)
  exact hexpP (lam ⟨x, Subgroup.mem_zpowers x⟩) ⟨_, rfl⟩

theorem good_iff_actW (h6 : Layer6Twin p f) (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂)
    {w x : G} (hwA : w ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hw2 : w * w = 1) (hw1 : w ≠ 1) (hwbad : z ∉ zStarOf (Subgroup.centralizer ({w} : Set G)))
    (hxA : x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hx : x ∈ Subgroup.centralizer ({w} : Set G)) (hzY : z ∈ exactLayer Ω w) :
    z ∈ zStarOf (Subgroup.centralizer ({w, x} : Set G)) ↔
      actW hyp.std.setting.stand.hyp.conjInvariant w ⟨x, hx⟩ =
        MulAut.conj (T7H.toBar Ω w z hzY) := by
  classical
  have hz2 : z * z = 1 := hyp.std.setting.hz.sq
  have hz1 : z ≠ 1 := hyp.std.setting.hz.ne_one
  have hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s := hyp.hzS
  have hΩ : HypOmegaMod p f Ω := hyp.std.setting.stand.hyp
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

theorem not_good_and_good (h6 : Layer6Twin p f) (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂)
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

theorem om6mData_of_actW (h6 : Layer6Twin p f) (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂)
    {w x : G} (hwA : w ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hw2 : w * w = 1) (hw1 : w ≠ 1) (hwbad : z ∉ zStarOf (Subgroup.centralizer ({w} : Set G)))
    (htyp : LayerOrthType p f Ω w 5 true ∨ LayerOrthType p f Ω w 6 (!piSign p f))
    (hxA : x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hx : x ∈ Subgroup.centralizer ({w} : Set G)) (hzY : z ∈ exactLayer Ω w)
    (hβ1 : actW hyp.std.setting.stand.hyp.conjInvariant w ⟨x, hx⟩ ≠ 1)
    (hβz : actW hyp.std.setting.stand.hyp.conjInvariant w ⟨x, hx⟩ ≠
      MulAut.conj (T7H.toBar Ω w z hzY)) :
    ∃ (hu₁Y : u₁ ∈ exactLayer Ω w) (hu₂Y : u₂ ∈ exactLayer Ω w),
      Om6mData p f (↥(exactLayer Ω w) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω w))
        (oddQuotientFamily (exactPair Ω w)) (T7H.exactImg Ω w K) (T7H.exactImg Ω w K')
        (T7H.toBar Ω w z hzY) (T7H.toBar Ω w u₁ hu₁Y) (T7H.toBar Ω w u₂ hu₂Y) := by
  classical
  have hst := hyp.std.setting.stand
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hcent := Subgroup.mem_centralizer_iff.mp hwA.2
  have haR : ∀ y ∈ R, w * y = y * w := fun y hy => (hcent y (Subgroup.mem_sup_left hy)).symm
  have haR' : ∀ y ∈ R', w * y = y * w := fun y hy => (hcent y (Subgroup.mem_sup_right hy)).symm
  obtain ⟨hzY', hu₁Y, hu₂Y, hK₂, hK₂', hgen, hlt, htw⟩ :=
    C25X.layer_a_frame hyp hw2 hw1 haR haR'
  obtain ⟨hzY'', -, -, -, hO, hO', -, -⟩ := twinFacts_of_bad h6 hyp hwA hw2 hw1 hwbad
  obtain ⟨hfixK, hfixK'⟩ := actW_fix hyp hw2 hK₂ hK₂' hO hO' hxA hx
  have hΦ : ∀ J ∈ oddQuotientFamily (exactPair Ω w), ∀ y : ↥(exactLayer Ω w) ⧸
      classicalInvolutionOddCore ↥(exactLayer Ω w),
      conjSub y J ∈ oddQuotientFamily (exactPair Ω w) := by
    intro J hJ yb
    obtain ⟨M, hMtq, rfl⟩ := T7H.exists_exactImg_of_mem hJ
    obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective yb
    rw [← C25Y.exactImg_conjSub_layer x']
    exact T7H.exactImg_mem (conjSub_mem_tqMembers hΩ.conjInvariant
      (exactLayer_le_centralizer Ω w x'.2) hMtq)
  rcases htyp with h | h
  · exfalso
    obtain ⟨t', n, hT, D, hD1, i₀, hDt, hDn⟩ := h
    rcases C25W.cent5_proved (p := p) (f := f) hst.odd hst.five _ _ D _ _ _ _ _ hD1
      ⟨i₀, by rw [hDt, hDn]; exact hT⟩ htw _ hfixK hfixK' with h1 | h1
    · exact hβ1 h1
    · apply hβz
      ext y
      exact h1 y
  · obtain ⟨t', n, hT, D, hD1, i₀, hDt, hDn⟩ := h
    exact ⟨hu₁Y, hu₂Y, ⟨hst.odd, hst.five, ⟨D, hD1, i₀, by rw [hDt, hDn]; exact hT⟩, htw, hΦ⟩⟩

end Edge

end CFSG.ClassicalInvolution.Asc77.CX
