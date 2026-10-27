module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4B3Main
public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4B3Four
public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4B3Z

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {S : Subgroup G}

theorem mem_conj_of_one (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤) (hΩne : Ω.Nonempty)
    (hdis : ¬ (CFSG.Fischer.commGraph (DBar Ω (sec4W Ω S))).Connected)
    {R U P V₀ : Subgroup G} {r d₀ : NBar (sec4W Ω S)} {tr t₀ : normalizer (sec4W Ω S : Set G)}
    (hr : ReflData Ω (sec4W Ω S) r R U tr) (h₀ : ReflData Ω (sec4W Ω S) d₀ P V₀ t₀)
    (hrd : r * d₀ ≠ d₀ * r) {z z₀ : G} (hz : IsZOf R z) (hz₀ : IsZOf P z₀)
    (hk : ∀ g ∈ DBar Ω (sec4W Ω S), g * r = r * g → g = r)
    {w : G} (hw : w ∈ omegaOne (sec4W Ω S)) (hw0 : w ∉ zZero Ω (sec4W Ω S) R z) :
    ∃ m ∈ MGrp Ω (sec4W Ω S), w = m⁻¹ * z * m := by
  have hΩ := H.hΩ
  have hR := hr.mem
  have hrD := hr.mem_dBar
  have hdr : d₀ * r ≠ r * d₀ := fun h => hrd h.symm
  have hUW : U ≤ sec4W Ω S := hr.rot_le hΩ hS
  have hV₀W : V₀ ≤ sec4W Ω S := h₀.rot_le hΩ hS
  have hgen : sec4W Ω S ≤ V₀ ⊔ U := sec4W_le_of_blocks H hS hΩne hdis hR hr.bar h₀.mem h₀.rot
    h₀.bar hdr (sup_le hV₀W hUW) le_sup_left (fun T hT V g hV hg hgr => by
      have hg' := hk g (IsBarOf.mem_dBar hT hg) hgr
      rw [hg'] at hg
      rw [DSet.rot_eq_of_bar_eq H hS hT hR hV hr.rot hg hr.bar]
      exact le_sup_right)
  have hbot : V₀ ⊓ U = ⊥ := ReflData.rot_inf_eq_bot H hS h₀ hr (fun h => hrd (by rw [h]))
  obtain ⟨hwW, hww⟩ := hw
  obtain ⟨x, u, hx, hu, rfl⟩ :=
    omegaOne_of_two hΩ hS h₀.rot hr.rot hV₀W hUW hbot hgen hz₀ hz hwW hww
  have hzM := fun {T : Subgroup G} {y : G} (hT : T ∈ DSet Ω (sec4W Ω S)) (hy : IsZOf T y) =>
    DSet.mem_conj_zOf H hS hdis hR hT hz hy
  rcases hx with hx | hx <;> rcases hu with hu | hu <;> subst x <;> subst u
  · exfalso
    apply hw0
    rw [one_mul, ← hz.mul_self]
    exact mul_mem_zZero_of_bar hΩ hS hR hR hr.bar hr.bar rfl hz
  · exact ⟨1, one_mem _, by group⟩
  · rw [mul_one]
    exact hzM h₀.mem hz₀
  · obtain ⟨hPr, -, hzPr, -⟩ := DSet.step_zOf H hS hΩne hdis hrD h₀.mem h₀.bar hz₀ hdr hr rfl hz
    exact hzM hPr hzPr

theorem mem_conj_of_two (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤) (hΩne : Ω.Nonempty)
    (hdis : ¬ (CFSG.Fischer.commGraph (DBar Ω (sec4W Ω S))).Connected)
    {R U P V₀ Tb Vb : Subgroup G} {r d₀ b : NBar (sec4W Ω S)}
    {tr t₀ tb : normalizer (sec4W Ω S : Set G)}
    (hr : ReflData Ω (sec4W Ω S) r R U tr) (h₀ : ReflData Ω (sec4W Ω S) d₀ P V₀ t₀)
    (hb : ReflData Ω (sec4W Ω S) b Tb Vb tb) (hrd : r * d₀ ≠ d₀ * r) (hbr : b * r = r * b)
    (hbne : b ≠ r) {z z₀ zb : G} (hz : IsZOf R z) (hz₀ : IsZOf P z₀) (hzb : IsZOf Tb zb)
    (hk : ∀ g ∈ DBar Ω (sec4W Ω S), g * r = r * g → g = r ∨ g = b)
    {w : G} (hw : w ∈ omegaOne (sec4W Ω S)) (hw0 : w ∉ zZero Ω (sec4W Ω S) R z) :
    ∃ m ∈ MGrp Ω (sec4W Ω S), w = m⁻¹ * z * m := by
  have hΩ := H.hΩ
  have hR := hr.mem
  have hrD := hr.mem_dBar
  have hd₀D := h₀.mem_dBar
  have hdr : d₀ * r ≠ r * d₀ := fun h => hrd h.symm
  have hbd : b * d₀ ≠ d₀ * b :=
    DBar.not_commute_of_commute H hS hΩne hdis hrD hd₀D hb.mem_dBar hdr hbr
  have hUW : U ≤ sec4W Ω S := hr.rot_le hΩ hS
  have hV₀W : V₀ ≤ sec4W Ω S := h₀.rot_le hΩ hS
  have hVbW : Vb ≤ sec4W Ω S := hb.rot_le hΩ hS
  have hgen : sec4W Ω S ≤ V₀ ⊔ U ⊔ Vb := sec4W_le_of_blocks H hS hΩne hdis hR hr.bar h₀.mem
    h₀.rot h₀.bar hdr (sup_le (sup_le hV₀W hUW) hVbW) (le_sup_left.trans le_sup_left)
    (fun T hT V g hV hg hgr => by
      rcases hk g (IsBarOf.mem_dBar hT hg) hgr with hg' | hg'
      · rw [hg'] at hg
        rw [DSet.rot_eq_of_bar_eq H hS hT hR hV hr.rot hg hr.bar]
        exact le_sup_right.trans le_sup_left
      · rw [hg'] at hg
        rw [DSet.rot_eq_of_bar_eq H hS hT hb.mem hV hb.rot hg hb.bar]
        exact le_sup_right)
  obtain ⟨hwW, hww⟩ := hw
  obtain ⟨x, u, v, hx, hu, hv, rfl⟩ := omegaOne_of_three hΩ hS h₀.rot hr.rot hb.rot hV₀W hUW
    hVbW hgen (fun x hx u hu v hv h => indep_three H hS h₀ hr hb hrd hbd hbr hbne hz₀ hz hzb
      hx hu hv h) hz₀ hz hzb hwW hww
  have hzM := fun {T : Subgroup G} {y : G} (hT : T ∈ DSet Ω (sec4W Ω S)) (hy : IsZOf T y) =>
    DSet.mem_conj_zOf H hS hdis hR hT hz hy
  rcases hx with hx | hx <;> rcases hu with hu | hu <;> rcases hv with hv | hv <;>
    subst x <;> subst u <;> subst v <;> try simp only [one_mul, mul_one] at hw0 ⊢
  · exfalso
    apply hw0
    rw [← hz.mul_self]
    exact mul_mem_zZero_of_bar hΩ hS hR hR hr.bar hr.bar rfl hz
  · exact hzM hb.mem hzb
  · exact ⟨1, one_mem _, by group⟩
  · exact absurd (mul_mem_zZero_of_bar hΩ hS hR hb.mem hr.bar hb.bar hbr hzb) hw0
  · exact hzM h₀.mem hz₀
  · obtain ⟨h1, -, h3, -⟩ := DSet.step_zOf H hS hΩne hdis hrD h₀.mem h₀.bar hz₀ hdr hb hbr hzb
    exact hzM h1 h3
  · obtain ⟨h1, -, h3, -⟩ := DSet.step_zOf H hS hΩne hdis hrD h₀.mem h₀.bar hz₀ hdr hr rfl hz
    exact hzM h1 h3
  · obtain ⟨h1, h2, h3, h4⟩ := DSet.step_zOf H hS hΩne hdis hrD h₀.mem h₀.bar hz₀ hdr hr rfl hz
    obtain ⟨h1', -, h3', -⟩ := DSet.step_zOf H hS hΩne hdis hrD h1 h2 h3 h4 hb hbr hzb
    exact hzM h1' h3'

theorem mem_conj_of_four (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤) (hΩne : Ω.Nonempty)
    (hdis : ¬ (CFSG.Fischer.commGraph (DBar Ω (sec4W Ω S))).Connected)
    {R U P V₀ Tb Vb Tc Vc Tτ Vτ : Subgroup G} {r d₀ b c τ : NBar (sec4W Ω S)}
    {tr t₀ tb tc tτ : normalizer (sec4W Ω S : Set G)}
    (hr : ReflData Ω (sec4W Ω S) r R U tr) (h₀ : ReflData Ω (sec4W Ω S) d₀ P V₀ t₀)
    (hb : ReflData Ω (sec4W Ω S) b Tb Vb tb) (hc : ReflData Ω (sec4W Ω S) c Tc Vc tc)
    (hτ : ReflData Ω (sec4W Ω S) τ Tτ Vτ tτ) (hrd : r * d₀ ≠ d₀ * r) (hbr : b * r = r * b)
    (hcr : c * r = r * c) (hτr : τ * r = r * τ) (hbne : b ≠ r) (hcne : c ≠ r) (hcb : c ≠ b)
    (hτne : τ ≠ r) (hτb : τ ≠ b) (hτc : τ ≠ c)
    (hfix : (b * c * r * τ)⁻¹ * d₀ * (b * c * r * τ) = d₀) {z z₀ zb zc zτ : G}
    (hz : IsZOf R z) (hz₀ : IsZOf P z₀) (hzb : IsZOf Tb zb) (hzc : IsZOf Tc zc)
    (hzτ : IsZOf Tτ zτ)
    (hk : ∀ g ∈ DBar Ω (sec4W Ω S), g * r = r * g → g = r ∨ g = b ∨ g = c ∨ g = τ)
    {w : G} (hw : w ∈ omegaOne (sec4W Ω S)) (hw0 : w ∉ zZero Ω (sec4W Ω S) R z) :
    ∃ m ∈ MGrp Ω (sec4W Ω S), w = m⁻¹ * z * m := by
  have hΩ := H.hΩ
  have hR := hr.mem
  have hrD := hr.mem_dBar
  have hbD := hb.mem_dBar
  have hcD := hc.mem_dBar
  have hτD := hτ.mem_dBar
  have hd₀D := h₀.mem_dBar
  have hdr : d₀ * r ≠ r * d₀ := fun h => hrd h.symm
  have hnd := fun {x : NBar (sec4W Ω S)} (hx : x ∈ DBar Ω (sec4W Ω S)) (hxr : x * r = r * x) =>
    DBar.not_commute_of_commute H hS hΩne hdis hrD hd₀D hx hdr hxr
  have hcm := fun {x y : NBar (sec4W Ω S)} (hx : x ∈ DBar Ω (sec4W Ω S))
    (hy : y ∈ DBar Ω (sec4W Ω S)) (hxr : x * r = r * x) (hyr : y * r = r * y) =>
    DBar.commute_of_commute H hS hΩne hdis hrD hx hy hxr hyr
  have hUW : U ≤ sec4W Ω S := hr.rot_le hΩ hS
  have hV₀W : V₀ ≤ sec4W Ω S := h₀.rot_le hΩ hS
  have hVbW : Vb ≤ sec4W Ω S := hb.rot_le hΩ hS
  have hVcW : Vc ≤ sec4W Ω S := hc.rot_le hΩ hS
  obtain ⟨v₀, hv₀, hv₀o⟩ := h₀.rot.exists_gen
  have hrel := mul_eq_of_four H hS h₀.mem h₀.rot h₀.bar hv₀ hv₀o hr hb hc hτ hbne.symm
    hcne.symm hτne.symm hcb.symm hτb.symm hτc.symm hbr.symm hcr.symm hτr.symm
    (hcm hbD hcD hbr hcr) (hcm hbD hτD hbr hτr) (hcm hcD hτD hcr hτr) hrd hfix
  have hv₀V : v₀ ∈ V₀ := hv₀ ▸ mem_zpowers v₀
  have hv₀W : v₀ ∈ sec4W Ω S := hV₀W hv₀V
  set X := V₀ ⊔ U ⊔ Vb ⊔ Vc with hX
  have hV₀X : V₀ ≤ X := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hUX : U ≤ X := le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hVbX : Vb ≤ X := le_sup_right.trans le_sup_left
  have hVcX : Vc ≤ X := le_sup_right
  have hVτX : Vτ ≤ X := by
    rw [← (ReflData.zpowers_eq H hS h₀.mem h₀.rot h₀.bar hτ (hnd hτD hτr) hv₀ hv₀o).1,
      zpowers_le]
    have e : v₀⁻¹ * ((tτ : G)⁻¹ * v₀ * tτ) = v₀⁻¹ * v₀⁻¹ * ((v₀⁻¹ * ((tr : G)⁻¹ * v₀ * tr)) *
        (v₀⁻¹ * ((tc : G)⁻¹ * v₀ * tc)) * (v₀⁻¹ * ((tb : G)⁻¹ * v₀ * tb)))⁻¹ := by
      rw [← hrel]
      group
    rw [e]
    refine mul_mem (mul_mem (inv_mem (hV₀X hv₀V)) (inv_mem (hV₀X hv₀V))) (inv_mem
      (mul_mem (mul_mem (hUX (hr.inv_mul_conj_mem H hS hv₀W)) (hVcX (hc.inv_mul_conj_mem H hS
        hv₀W))) (hVbX (hb.inv_mul_conj_mem H hS hv₀W))))
  have hgen : sec4W Ω S ≤ X := sec4W_le_of_blocks H hS hΩne hdis hR hr.bar h₀.mem h₀.rot
    h₀.bar hdr (sup_le (sup_le (sup_le hV₀W hUW) hVbW) hVcW) hV₀X
    (fun T hT V g hV hg hgr => by
      rcases hk g (IsBarOf.mem_dBar hT hg) hgr with hg' | hg' | hg' | hg' <;> rw [hg'] at hg
      · rw [DSet.rot_eq_of_bar_eq H hS hT hR hV hr.rot hg hr.bar]; exact hUX
      · rw [DSet.rot_eq_of_bar_eq H hS hT hb.mem hV hb.rot hg hb.bar]; exact hVbX
      · rw [DSet.rot_eq_of_bar_eq H hS hT hc.mem hV hc.rot hg hc.bar]; exact hVcX
      · rw [DSet.rot_eq_of_bar_eq H hS hT hτ.mem hV hτ.rot hg hτ.bar]; exact hVτX)
  have hzrel := zOf_mul_eq_of_four H hS h₀.mem h₀.bar hz₀ hr hb hc hτ hz hzb hzc hzτ hbne.symm
    hcne.symm hτne.symm hcb.symm hτb.symm hτc.symm hbr.symm hcr.symm hτr.symm
    (hcm hbD hcD hbr hcr) (hcm hbD hτD hbr hτr) (hcm hcD hτD hcr hτr) hrd (hnd hbD hbr)
    (hnd hcD hcr) (hnd hτD hτr) hfix
  obtain ⟨hwW, hww⟩ := hw
  obtain ⟨x, u, v, y, hx, hu, hv, hy, rfl⟩ := omegaOne_of_four hΩ hS h₀.rot hr.rot hb.rot
    hc.rot hV₀W hUW hVbW hVcW hgen (fun x hx u hu v hv y hy h => indep_four H hS h₀.mem h₀.rot
      h₀.bar hr hb hc hτ (hnd hτD hτr) hbr.symm hcr.symm (hcm hbD hcD hbr hcr) hτr.symm
      (hcm hbD hτD hbr hτr) (hcm hcD hτD hcr hτr) hbne.symm hcne.symm hcb.symm hτne.symm
      hτb.symm hτc.symm hz hzb hzc hzτ hzrel hx hu hv hy h) hz₀ hz hzb hzc hwW hww
  have hzM := fun {T : Subgroup G} {y : G} (hT : T ∈ DSet Ω (sec4W Ω S)) (hy : IsZOf T y) =>
    DSet.mem_conj_zOf H hS hdis hR hT hz hy
  have hZ0 := fun {T : Subgroup G} {s : NBar (sec4W Ω S)} {y : G} (hT : T ∈ DSet Ω (sec4W Ω S))
    (hs : IsBarOf (sec4W Ω S) T s) (hsr : s * r = r * s) (hy : IsZOf T y) =>
    mul_mem_zZero_of_bar (z := z) hΩ hS hR hT hr.bar hs hsr hy
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz.mul_self
  have hzτinv : zτ⁻¹ = zτ := inv_eq_of_mul_eq_one_right hzτ.mul_self
  rcases hx with hx | hx <;> rcases hu with hu | hu <;> rcases hv with hv | hv <;>
    rcases hy with hy | hy <;> subst x <;> subst u <;> subst v <;> subst y <;>
    try simp only [one_mul, mul_one] at hw0 ⊢
  · exfalso
    apply hw0
    rw [← hz.mul_self]
    exact hZ0 hR hr.bar rfl hz
  · exact hzM hc.mem hzc
  · exact hzM hb.mem hzb
  · exfalso
    apply hw0
    have e : zb * zc = z * zτ := by
      calc zb * zc = z⁻¹ * (z * zb * zc * zτ) * zτ⁻¹ := by group
        _ = z * zτ := by rw [hzrel, hzinv, hzτinv, mul_one]
    rw [e]
    exact hZ0 hτ.mem hτ.bar hτr hzτ
  · exact ⟨1, one_mem _, by group⟩
  · exact absurd (hZ0 hc.mem hc.bar hcr hzc) hw0
  · exact absurd (hZ0 hb.mem hb.bar hbr hzb) hw0
  · have e : z * zb * zc = zτ := by
      rw [eq_inv_of_mul_eq_one_left hzrel, hzτinv]
    rw [e]
    exact hzM hτ.mem hzτ
  · exact hzM h₀.mem hz₀
  · obtain ⟨h1, -, h3, -⟩ := DSet.step_zOf H hS hΩne hdis hrD h₀.mem h₀.bar hz₀ hdr hc hcr hzc
    exact hzM h1 h3
  · obtain ⟨h1, -, h3, -⟩ := DSet.step_zOf H hS hΩne hdis hrD h₀.mem h₀.bar hz₀ hdr hb hbr hzb
    exact hzM h1 h3
  · obtain ⟨h1, h2, h3, h4⟩ :=
      DSet.step_zOf H hS hΩne hdis hrD h₀.mem h₀.bar hz₀ hdr hb hbr hzb
    obtain ⟨h1', -, h3', -⟩ := DSet.step_zOf H hS hΩne hdis hrD h1 h2 h3 h4 hc hcr hzc
    exact hzM h1' h3'
  · obtain ⟨h1, -, h3, -⟩ := DSet.step_zOf H hS hΩne hdis hrD h₀.mem h₀.bar hz₀ hdr hr rfl hz
    exact hzM h1 h3
  · obtain ⟨h1, h2, h3, h4⟩ :=
      DSet.step_zOf H hS hΩne hdis hrD h₀.mem h₀.bar hz₀ hdr hr rfl hz
    obtain ⟨h1', -, h3', -⟩ := DSet.step_zOf H hS hΩne hdis hrD h1 h2 h3 h4 hc hcr hzc
    exact hzM h1' h3'
  · obtain ⟨h1, h2, h3, h4⟩ :=
      DSet.step_zOf H hS hΩne hdis hrD h₀.mem h₀.bar hz₀ hdr hr rfl hz
    obtain ⟨h1', -, h3', -⟩ := DSet.step_zOf H hS hΩne hdis hrD h1 h2 h3 h4 hb hbr hzb
    exact hzM h1' h3'
  · obtain ⟨h1, h2, h3, h4⟩ :=
      DSet.step_zOf H hS hΩne hdis hrD h₀.mem h₀.bar hz₀ hdr hr rfl hz
    obtain ⟨h1', h2', h3', h4'⟩ := DSet.step_zOf H hS hΩne hdis hrD h1 h2 h3 h4 hb hbr hzb
    obtain ⟨h1'', -, h3'', -⟩ := DSet.step_zOf H hS hΩne hdis hrD h1' h2' h3' h4' hc hcr hzc
    exact hzM h1'' h3''

theorem mem_conj_of_mem_diff (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤)
    (hdis : ¬ (CFSG.Fischer.commGraph (DBar Ω (sec4W Ω S))).Connected)
    {R : Subgroup G} (hR : R ∈ DSet Ω (sec4W Ω S)) {z : G} (hz : IsZOf R z) {w : G}
    (hw : w ∈ omegaOne (sec4W Ω S)) (hw0 : w ∉ zZero Ω (sec4W Ω S) R z) :
    ∃ m ∈ MGrp Ω (sec4W Ω S), w = m⁻¹ * z * m := by
  have hΩ := H.hΩ
  have hΩne : Ω.Nonempty := by
    obtain ⟨⟨J, hJ, -⟩, -⟩ := hR
    exact ⟨J, hJ⟩
  obtain ⟨U, hU⟩ := DSet.exists_rot hΩ hR
  obtain ⟨r, hrbar⟩ := IsBarOf.exists_of_mem hΩ hR
  obtain ⟨tr, hr⟩ := ReflData.exists_of_bar hΩ hS hR hU hrbar
  have hrD := hr.mem_dBar
  obtain ⟨d₀, hd₀D, hrd⟩ := DBar.exists_not_commute hdis hrD
  obtain ⟨P, V₀, t₀, h₀⟩ := DBar.exists_reflData hd₀D
  obtain ⟨z₀, hz₀⟩ := IsZOf.exists_of_rot h₀.rot
  by_cases hk1 : ∀ g ∈ DBar Ω (sec4W Ω S), g * r = r * g → g = r
  · exact mem_conj_of_one H hS hΩne hdis hr h₀ hrd hz hz₀ hk1 hw hw0
  push Not at hk1
  obtain ⟨b, hbD, hbr, hbne⟩ := hk1
  obtain ⟨Tb, Vb, tb, hb⟩ := DBar.exists_reflData hbD
  obtain ⟨zb, hzb⟩ := IsZOf.exists_of_rot hb.rot
  by_cases hk2 : ∀ g ∈ DBar Ω (sec4W Ω S), g * r = r * g → g = r ∨ g = b
  · exact mem_conj_of_two H hS hΩne hdis hr h₀ hb hrd hbr hbne hz hz₀ hzb hk2 hw hw0
  push Not at hk2
  obtain ⟨c, hcD, hcr, hcne, hcb⟩ := hk2
  have hdr : d₀ * r ≠ r * d₀ := fun h => hrd h.symm
  obtain ⟨τ, hτD, hτr, hτne, hτb, hτc, hfix⟩ := DBar.exists_fourth H hS hΩne hdis hrD hd₀D
    hrD hbD hcD hdr rfl hbr hcr (Ne.symm hbne) (Ne.symm hcne) (Ne.symm hcb)
  obtain ⟨Tc, Vc, tc, hc⟩ := DBar.exists_reflData hcD
  obtain ⟨Tτ, Vτ, tτ, hτ⟩ := DBar.exists_reflData hτD
  obtain ⟨zc, hzc⟩ := IsZOf.exists_of_rot hc.rot
  obtain ⟨zτ, hzτ⟩ := IsZOf.exists_of_rot hτ.rot
  have hk : ∀ g ∈ DBar Ω (sec4W Ω S), g * r = r * g → g = r ∨ g = b ∨ g = c ∨ g = τ :=
    fun g hg hgr => mem_of_four H hS hΩne hdis h₀.mem h₀.rot h₀.bar hrD hdr hrD hbD hcD hτD hg
      rfl hbr hcr hτr hgr (Ne.symm hbne) (Ne.symm hcne) (Ne.symm hcb) hτne hτb hτc hfix
  exact mem_conj_of_four H hS hΩne hdis hr h₀ hb hc hτ hrd hbr hcr hτr hbne hcne hcb hτne hτb
    hτc hfix hz hz₀ hzb hzc hzτ hk hw hw0

theorem conj_set_eq_omegaOne_diff (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤)
    (hdis : ¬ (CFSG.Fischer.commGraph (DBar Ω (sec4W Ω S))).Connected)
    {R : Subgroup G} (hR : R ∈ DSet Ω (sec4W Ω S)) {z : G} (hz : IsZOf R z) :
    {w | ∃ m ∈ MGrp Ω (sec4W Ω S), w = m⁻¹ * z * m} =
      omegaOne (sec4W Ω S) \ zZero Ω (sec4W Ω S) R z := by
  ext w
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact conj_mem_omegaOne_diff H hS hdis hR hz hm
  · rintro ⟨hw, hw0⟩
    exact mem_conj_of_mem_diff H hS hdis hR hz hw hw0

end CFSG.ComponentClassification.Asc76.Sec4
