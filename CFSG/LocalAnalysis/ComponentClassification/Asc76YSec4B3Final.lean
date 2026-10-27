module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4B3Two
public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4B3Defs

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {S : Subgroup G}

theorem IsZOf.exists_mul_self {T V : Subgroup G} {z : G} (hz : IsZOf T z)
    (hV : IsDihedralRot V T) : ∃ u ∈ V, u * u = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hzV, -⟩ := hz.mem_rot hV
  obtain ⟨n, hn⟩ := (hV.isPGroup.to_le hV.le).exists_card_eq
  have h4 := hV.four_le
  rw [hn] at h4
  have hn2 : 2 ≤ n := by
    by_contra h
    push Not at h
    interval_cases n <;> simp at h4
  obtain ⟨u, hu, hzu⟩ := hV.exists_sq_of_pow_half_eq_one hzV (by
    rw [hn]
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    rw [show 2 ^ (k + 2) / 2 = 2 * 2 ^ k by
      rw [pow_add, pow_succ, pow_one]; omega, pow_mul, pow_two, hz.mul_self, one_pow])
  exact ⟨u, hu, hzu.symm⟩

theorem exists_commute_of_not_commute (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤)
    (hdis : ¬ (CFSG.Fischer.commGraph (DBar Ω (sec4W Ω S))).Connected)
    {R : Subgroup G} (hR : R ∈ DSet Ω (sec4W Ω S)) {z : G} (hz : IsZOf R z)
    {T V : Subgroup G} {f : NBar (sec4W Ω S)} {x : normalizer (sec4W Ω S : Set G)}
    (hT : ReflData Ω (sec4W Ω S) f T V x) {y : G} (hy : IsZOf T y)
    (t : normalizer (sec4W Ω S : Set G)) (htt : (t : G) * t = 1)
    (hnc : f * ((t : NBar (sec4W Ω S))⁻¹ * f * t) ≠ ((t : NBar (sec4W Ω S))⁻¹ * f * t) * f) :
    ∃ m ∈ MGrp Ω (sec4W Ω S), (t : G) * (m⁻¹ * z * m) = m⁻¹ * z * m * t := by
  have hΩ := H.hΩ
  have hTt := DSet.rightConjugate_mem hΩ hT.mem t.2
  have hbar := hT.bar.rightConjugate t
  have hyt := hy.rightConjugate (t : G)
  have h1 : (x : G)⁻¹ * ((t : G)⁻¹ * y * t) * x = ((t : G)⁻¹ * y * t) * y :=
    conj_z_of_not_commute H hS hT.mem hTt hT.rot hy hyt hT.bar hbar hnc hT.memT hT.not_mem
  have hTtx := DSet.rightConjugate_mem hΩ hTt x.2
  have hytx := hyt.rightConjugate (x : G)
  rw [h1] at hytx
  obtain ⟨m, hm, hmeq⟩ := DSet.mem_conj_zOf H hS hdis hR hTtx hz hytx
  refine ⟨m, hm, ?_⟩
  rw [← hmeq]
  have htinv : (t : G)⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hyW := DSet.zOf_mem hΩ hS hT.mem hy
  have hytW := DSet.zOf_mem hΩ hS hTt hyt
  have hc : y * ((t : G)⁻¹ * y * t) = ((t : G)⁻¹ * y * t) * y := sec4W_comm hΩ hS hyW hytW
  rw [htinv] at hc ⊢
  calc (t : G) * ((t : G) * y * t * y) = (t * t) * y * t * y := by group
    _ = y * t * y := by rw [htt, one_mul]
    _ = y * (t * y * t) * t := by rw [show y * (t * y * t) * t = y * t * y * (t * t) by group,
          htt, mul_one]
    _ = (t * y * t) * y * t := by rw [hc]
    _ = (t : G) * y * t * y * t := by group

omit [Finite G] in
theorem exists_commute_of_conj_eq {z y : G} {M : Subgroup G} {t : G}
    (hy : ∃ m ∈ M, y = m⁻¹ * z * m) (hyt : t⁻¹ * y * t = y) :
    ∃ m ∈ M, t * (m⁻¹ * z * m) = m⁻¹ * z * m * t := by
  obtain ⟨m, hm, rfl⟩ := hy
  refine ⟨m, hm, ?_⟩
  calc t * (m⁻¹ * z * m) = t * (t⁻¹ * (m⁻¹ * z * m) * t) := by rw [hyt]
    _ = m⁻¹ * z * m * t := by group

theorem exists_commute_of_two (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤) (hΩne : Ω.Nonempty)
    (hdis : ¬ (CFSG.Fischer.commGraph (DBar Ω (sec4W Ω S))).Connected)
    {R U Tb Vb : Subgroup G} {r b : NBar (sec4W Ω S)} {tr tb : normalizer (sec4W Ω S : Set G)}
    (hr : ReflData Ω (sec4W Ω S) r R U tr) (hb : ReflData Ω (sec4W Ω S) b Tb Vb tb)
    (hbr : b * r = r * b) {z zb : G} (hz : IsZOf R z) (hzb : IsZOf Tb zb)
    (hk : ∀ g ∈ DBar Ω (sec4W Ω S), g * r = r * g → g = r ∨ g = b)
    (t : normalizer (sec4W Ω S : Set G)) (htt : (t : G) * t = 1)
    (htb : (t : NBar (sec4W Ω S))⁻¹ * r * t = b) :
    ∃ m ∈ MGrp Ω (sec4W Ω S), (t : G) * (m⁻¹ * z * m) = m⁻¹ * z * m * t := by
  have hΩ := H.hΩ
  have hR := hr.mem
  have hrD := hr.mem_dBar
  obtain ⟨d₀, hd₀D, hrd⟩ := DBar.exists_not_commute hdis hrD
  have hdr : d₀ * r ≠ r * d₀ := fun h => hrd h.symm
  obtain ⟨P, V₀, t₀, h₀⟩ := DBar.exists_reflData hd₀D
  obtain ⟨z₀, hz₀⟩ := IsZOf.exists_of_rot h₀.rot
  have hPt := DSet.rightConjugate_mem hΩ h₀.mem t.2
  have hbar := h₀.bar.rightConjugate t
  have hz₀t := hz₀.rightConjugate (t : G)
  by_cases hnc : d₀ * ((t : NBar (sec4W Ω S))⁻¹ * d₀ * t) ≠
      ((t : NBar (sec4W Ω S))⁻¹ * d₀ * t) * d₀
  · exact exists_commute_of_not_commute H hS hdis hR hz h₀ hz₀ t htt hnc
  push Not at hnc
  obtain ⟨d₁, hd₁⟩ : ∃ d₁, d₁ = (t : NBar (sec4W Ω S))⁻¹ * d₀ * t := ⟨_, rfl⟩
  rw [← hd₁] at hnc hbar
  have hd₁D : d₁ ∈ DBar Ω (sec4W Ω S) := IsBarOf.mem_dBar hPt hbar
  have hzM := fun {T : Subgroup G} {y : G} (hT : T ∈ DSet Ω (sec4W Ω S)) (hy : IsZOf T y) =>
    DSet.mem_conj_zOf H hS hdis hR hT hz hy
  by_cases heq : d₁ = d₀
  · rw [heq] at hbar
    exact exists_commute_of_conj_eq (hzM h₀.mem hz₀)
      (DSet.zOf_eq_of_bar_eq H hS hPt h₀.mem hz₀t hz₀ hbar h₀.bar)
  obtain ⟨hgD, hgr, hgeq⟩ := DBar.conj_eq_of_second H hS hΩne hdis hrD hd₀D hd₁D hdr hnc.symm
  obtain ⟨g, hgdef⟩ : ∃ g, g = d₁ * (r * d₀ * r) * d₁ := ⟨_, rfl⟩
  rw [← hgdef] at hgD hgr hgeq
  have hrr := DBar.mul_self hΩ hS hrD
  have hbb := DBar.mul_self hΩ hS hb.mem_dBar
  have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hrr
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  rcases hk g hgD hgr with hg | hg
  · exfalso
    apply heq
    rw [← hgeq, hg, hrr, inv_one, one_mul, mul_one]
  rw [hg] at hgeq
  obtain ⟨h1, h2, h3, h4⟩ := DSet.step_zOf H hS hΩne hdis hrD h₀.mem h₀.bar hz₀ hdr hr rfl hz
  obtain ⟨h1', h2', h3', -⟩ := DSet.step_zOf H hS hΩne hdis hrD h1 h2 h3 h4 hb hbr hzb
  have himg : b * (r * d₀ * r) * b = d₁ := by
    rw [← hgeq, mul_inv_rev, hrinv, hbinv]
    group
  rw [himg] at h2'
  have hz₀eq : (t : G)⁻¹ * z₀ * t = z₀ * z * zb :=
    DSet.zOf_eq_of_bar_eq H hS hPt h1' hz₀t h3' hbar h2'
  have hRt := DSet.rightConjugate_mem hΩ hR t.2
  have hRbar := hr.bar.rightConjugate t
  rw [htb] at hRbar
  have hzeq : (t : G)⁻¹ * z * t = zb :=
    DSet.zOf_eq_of_bar_eq H hS hRt hb.mem (hz.rightConjugate (t : G)) hzb hRbar hb.bar
  refine exists_commute_of_conj_eq (hzM h1 h3) ?_
  calc (t : G)⁻¹ * (z₀ * z) * t = ((t : G)⁻¹ * z₀ * t) * ((t : G)⁻¹ * z * t) := by group
    _ = z₀ * z * (zb * zb) := by rw [hz₀eq, hzeq]; group
    _ = z₀ * z := by rw [hzb.mul_self, mul_one]

theorem exists_commute_of_four (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤) (hΩne : Ω.Nonempty)
    (hdis : ¬ (CFSG.Fischer.commGraph (DBar Ω (sec4W Ω S))).Connected)
    {R U Te Ve : Subgroup G} {r b e : NBar (sec4W Ω S)} {tr te : normalizer (sec4W Ω S : Set G)}
    (hr : ReflData Ω (sec4W Ω S) r R U tr) (he : ReflData Ω (sec4W Ω S) e Te Ve te)
    (hbr : b * r = r * b) (hbne : b ≠ r) (her : e * r = r * e) (hene : e ≠ r) (heb : e ≠ b)
    {z ze : G} (hz : IsZOf R z) (hze : IsZOf Te ze)
    (t : normalizer (sec4W Ω S : Set G)) (htt : (t : G) * t = 1)
    (htb : (t : NBar (sec4W Ω S))⁻¹ * r * t = b) :
    ∃ m ∈ MGrp Ω (sec4W Ω S), (t : G) * (m⁻¹ * z * m) = m⁻¹ * z * m * t := by
  have hΩ := H.hΩ
  have hR := hr.mem
  have hrD := hr.mem_dBar
  have heD := he.mem_dBar
  have htinv : (t : G)⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have htt' : (t : NBar (sec4W Ω S)) * (t : NBar (sec4W Ω S)) = 1 := by
    rw [← QuotientGroup.mk_mul, show t * t = 1 from Subtype.ext htt, QuotientGroup.mk_one]
  have htbinv : (t : NBar (sec4W Ω S))⁻¹ = t := inv_eq_of_mul_eq_one_right htt'
  have hRt := DSet.rightConjugate_mem hΩ hR t.2
  have hRbar := hr.bar.rightConjugate t
  rw [htb] at hRbar
  have hbD := IsBarOf.mem_dBar hRt hRbar
  have hTet := DSet.rightConjugate_mem hΩ he.mem t.2
  have hTebar := he.bar.rightConjugate t
  obtain ⟨e', he'⟩ : ∃ e', e' = (t : NBar (sec4W Ω S))⁻¹ * e * t := ⟨_, rfl⟩
  rw [← he'] at hTebar
  have he'D := IsBarOf.mem_dBar hTet hTebar
  have hzt := hz.rightConjugate (t : G)
  have hzet := hze.rightConjugate (t : G)
  have hzM := fun {T : Subgroup G} {y : G} (hT : T ∈ DSet Ω (sec4W Ω S)) (hy : IsZOf T y) =>
    DSet.mem_conj_zOf H hS hdis hR hT hz hy
  have he'b : e' * b = b * e' := by
    rw [he', ← htb]
    calc (t : NBar (sec4W Ω S))⁻¹ * e * t * ((t : NBar (sec4W Ω S))⁻¹ * r * t)
        = (t : NBar (sec4W Ω S))⁻¹ * (e * r) * t := by group
      _ = (t : NBar (sec4W Ω S))⁻¹ * (r * e) * t := by rw [her]
      _ = (t : NBar (sec4W Ω S))⁻¹ * r * t * ((t : NBar (sec4W Ω S))⁻¹ * e * t) := by group
  have he'r : e' * r = r * e' := DBar.commute_trans H hS hΩne hdis he'D hbD hrD he'b hbr
  by_cases hee : e' = e
  · rw [hee] at hTebar
    exact exists_commute_of_conj_eq (hzM he.mem hze)
      (DSet.zOf_eq_of_bar_eq H hS hTet he.mem hzet hze hTebar he.bar)
  have he'r' : e' ≠ r := by
    intro h
    apply heb
    rw [← htb, ← h, he', htbinv, show (t : NBar (sec4W Ω S)) * ((t : NBar (sec4W Ω S)) * e *
      t) * t = ((t : NBar (sec4W Ω S)) * t) * e * ((t : NBar (sec4W Ω S)) * t) by group, htt',
      one_mul, mul_one]
  have he'b' : e' ≠ b := by
    intro h
    apply hene
    rw [← htb, he'] at h
    exact mul_left_cancel (mul_right_cancel h)
  obtain ⟨d₀, hd₀D, hrd⟩ := DBar.exists_not_commute hdis hrD
  have hdr : d₀ * r ≠ r * d₀ := fun h => hrd h.symm
  obtain ⟨P, V₀, t₀, h₀⟩ := DBar.exists_reflData hd₀D
  obtain ⟨z₀, hz₀⟩ := IsZOf.exists_of_rot h₀.rot
  obtain ⟨τ, hτD, hτr, hτne, hτb, hτe, hfix⟩ := DBar.exists_fourth H hS hΩne hdis hrD hd₀D
    hrD hbD heD hdr rfl hbr her (Ne.symm hbne) (Ne.symm hene) (Ne.symm heb)
  have he'τ : e' = τ := by
    rcases mem_of_four H hS hΩne hdis h₀.mem h₀.rot h₀.bar hrD hdr hrD hbD heD hτD he'D rfl hbr
      her hτr he'r (Ne.symm hbne) (Ne.symm hene) (Ne.symm heb) hτne hτb hτe hfix with
      h | h | h | h
    · exact absurd h he'r'
    · exact absurd h he'b'
    · exact absurd h hee
    · exact h
  rw [he'τ] at hTebar
  obtain ⟨tb, htbd⟩ := ReflData.exists_of_bar hΩ hS hRt (hr.rot.rightConjugate (t : G)) hRbar
  obtain ⟨tτ, htτd⟩ := ReflData.exists_of_bar hΩ hS hTet (he.rot.rightConjugate (t : G)) hTebar
  have hcm := fun {x y : NBar (sec4W Ω S)} (hx : x ∈ DBar Ω (sec4W Ω S))
    (hy : y ∈ DBar Ω (sec4W Ω S)) (hxr : x * r = r * x) (hyr : y * r = r * y) =>
    DBar.commute_of_commute H hS hΩne hdis hrD hx hy hxr hyr
  have hnd := fun {x : NBar (sec4W Ω S)} (hx : x ∈ DBar Ω (sec4W Ω S)) (hxr : x * r = r * x) =>
    DBar.not_commute_of_commute H hS hΩne hdis hrD hd₀D hx hdr hxr
  have hzrel := zOf_mul_eq_of_four H hS h₀.mem h₀.bar hz₀ hr htbd he htτd hz hzt hze hzet
    (Ne.symm hbne) (Ne.symm hene) (Ne.symm hτne) (Ne.symm heb) (Ne.symm hτb) (Ne.symm hτe)
    hbr.symm her.symm hτr.symm (hcm hbD heD hbr her) (hcm hbD hτD hbr hτr)
    (hcm heD hτD her hτr) hrd (hnd hbD hbr) (hnd heD her) (hnd hτD hτr) hfix
  obtain ⟨ur, hurU, hurr⟩ := hz.exists_mul_self hr.rot
  obtain ⟨ue, hueV, huee⟩ := hze.exists_mul_self he.rot
  have hurW := hr.rot_le hΩ hS hurU
  have hueW := he.rot_le hΩ hS hueV
  have hurtW := conj_mem_sec4W t.2 hurW
  have huetW := conj_mem_sec4W t.2 hueW
  have hW := fun {a c : G} (ha : a ∈ sec4W Ω S) (hc : c ∈ sec4W Ω S) => sec4W_comm hΩ hS ha hc
  obtain ⟨u, hu⟩ : ∃ u, u = ur * ((t : G)⁻¹ * ur * t) * ue * ((t : G)⁻¹ * ue * t) := ⟨_, rfl⟩
  have huW : u ∈ sec4W Ω S := hu ▸ mul_mem (mul_mem (mul_mem hurW hurtW) hueW) huetW
  have huu : u * u = 1 := by
    rw [hu, mul_mul_self_of_commute (hW (mul_mem (mul_mem hurW hurtW) hueW) huetW),
      mul_mul_self_of_commute (hW (mul_mem hurW hurtW) hueW),
      mul_mul_self_of_commute (hW hurW hurtW), hurr, huee,
      show (t : G)⁻¹ * ur * t * ((t : G)⁻¹ * ur * t) = (t : G)⁻¹ * (ur * ur) * t by group,
      show (t : G)⁻¹ * ue * t * ((t : G)⁻¹ * ue * t) = (t : G)⁻¹ * (ue * ue) * t by group,
      hurr, huee]
    exact hzrel
  have hu0 : u ∉ zZero Ω (sec4W Ω S) R z := by
    intro h0
    have h1 := zZero_commute H hS hdis hR hz h0 (DSet.le_mGrp hR hr.memT)
    have hc1 : (tr : G) * ((t : G)⁻¹ * ur * t) = ((t : G)⁻¹ * ur * t) * tr :=
      hr.commute htbd H hS hbr.symm (Ne.symm hbne) (by
        rw [mem_rightConjugate_iff]
        have e : (t : G) * ((t : G)⁻¹ * ur * t) * (t : G)⁻¹ = ur := by group
        rw [e]
        exact hurU)
    have hc2 : (tr : G) * ue = ue * tr := hr.commute he H hS her.symm (Ne.symm hene) hueV
    have hc3 : (tr : G) * ((t : G)⁻¹ * ue * t) = ((t : G)⁻¹ * ue * t) * tr :=
      hr.commute htτd H hS hτr.symm (Ne.symm hτne) (by
        rw [mem_rightConjugate_iff]
        have e : (t : G) * ((t : G)⁻¹ * ue * t) * (t : G)⁻¹ = ue := by group
        rw [e]
        exact hueV)
    have h2 : (tr : G)⁻¹ * u * tr = ur⁻¹ * ((t : G)⁻¹ * ur * t) * ue * ((t : G)⁻¹ * ue * t) := by
      rw [hu]
      calc (tr : G)⁻¹ * (ur * ((t : G)⁻¹ * ur * t) * ue * ((t : G)⁻¹ * ue * t)) * tr
          = ((tr : G)⁻¹ * ur * tr) * ((tr : G)⁻¹ * ((t : G)⁻¹ * ur * t) * tr) *
              ((tr : G)⁻¹ * ue * tr) * ((tr : G)⁻¹ * ((t : G)⁻¹ * ue * t) * tr) := by group
        _ = _ := by
          rw [hr.conj_rot hurU, ReflData.conj_eq_of_commute hc1,
            ReflData.conj_eq_of_commute hc2, ReflData.conj_eq_of_commute hc3]
    have h3 : (tr : G)⁻¹ * u * tr = u := by
      calc (tr : G)⁻¹ * u * tr = (tr : G)⁻¹ * (u * tr) := by group
        _ = (tr : G)⁻¹ * (tr * u) := by rw [h1]
        _ = u := by group
    rw [h2, hu] at h3
    have h4 : ur⁻¹ = ur := mul_right_cancel (mul_right_cancel (mul_right_cancel h3))
    apply hz.ne_one
    rw [← hurr]
    calc ur * ur = ur * ur⁻¹ := by rw [h4]
      _ = 1 := mul_inv_cancel ur
  have hzMu : ∃ m ∈ MGrp Ω (sec4W Ω S), u = m⁻¹ * z * m := by
    have h := (conj_set_eq_omegaOne_diff H hS hdis hR hz).symm ▸
      (show u ∈ omegaOne (sec4W Ω S) \ zZero Ω (sec4W Ω S) R z from ⟨⟨huW, huu⟩, hu0⟩)
    exact h
  refine exists_commute_of_conj_eq hzMu ?_
  rw [hu]
  have e1 : (t : G)⁻¹ * ((t : G)⁻¹ * ur * t) * t = ur := by
    rw [htinv, show (t : G) * ((t : G) * ur * t) * t = ((t : G) * t) * ur * ((t : G) * t) by
      group, htt, one_mul, mul_one]
  have e2 : (t : G)⁻¹ * ((t : G)⁻¹ * ue * t) * t = ue := by
    rw [htinv, show (t : G) * ((t : G) * ue * t) * t = ((t : G) * t) * ue * ((t : G) * t) by
      group, htt, one_mul, mul_one]
  calc (t : G)⁻¹ * (ur * ((t : G)⁻¹ * ur * t) * ue * ((t : G)⁻¹ * ue * t)) * t
      = ((t : G)⁻¹ * ur * t) * ((t : G)⁻¹ * ((t : G)⁻¹ * ur * t) * t) *
          ((t : G)⁻¹ * ue * t) * ((t : G)⁻¹ * ((t : G)⁻¹ * ue * t) * t) := by group
    _ = ((t : G)⁻¹ * ur * t) * ur * (((t : G)⁻¹ * ue * t) * ue) := by rw [e1, e2]; group
    _ = ur * ((t : G)⁻¹ * ur * t) * (ue * ((t : G)⁻¹ * ue * t)) := by
        rw [hW hurtW hurW, hW huetW hueW]
    _ = ur * ((t : G)⁻¹ * ur * t) * ue * ((t : G)⁻¹ * ue * t) := by group

theorem exists_commute_conj (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤)
    (hdis : ¬ (CFSG.Fischer.commGraph (DBar Ω (sec4W Ω S))).Connected)
    {R : Subgroup G} (hR : R ∈ DSet Ω (sec4W Ω S)) {z : G} (hz : IsZOf R z) {t : G}
    (ht : t ∈ normalizer (sec4W Ω S : Set G)) (htt : t * t = 1) :
    ∃ m ∈ MGrp Ω (sec4W Ω S), t * (m⁻¹ * z * m) = m⁻¹ * z * m * t := by
  have hΩ := H.hΩ
  have hΩne : Ω.Nonempty := by
    obtain ⟨⟨J, hJ, -⟩, -⟩ := hR
    exact ⟨J, hJ⟩
  obtain ⟨U, hU⟩ := DSet.exists_rot hΩ hR
  obtain ⟨r, hrbar⟩ := IsBarOf.exists_of_mem hΩ hR
  obtain ⟨tr, hr⟩ := ReflData.exists_of_bar hΩ hS hR hU hrbar
  obtain ⟨b, hbdef⟩ : ∃ b, b = ((⟨t, ht⟩ : normalizer (sec4W Ω S : Set G)) :
      NBar (sec4W Ω S))⁻¹ * r * (⟨t, ht⟩ : normalizer (sec4W Ω S : Set G)) := ⟨_, rfl⟩
  have hRt := DSet.rightConjugate_mem hΩ hR ht
  have hRbar := hr.bar.rightConjugate ⟨t, ht⟩
  rw [← hbdef] at hRbar
  by_cases hnc : r * b ≠ b * r
  · exact exists_commute_of_not_commute H hS hdis hR hz hr hz ⟨t, ht⟩ htt (by rwa [← hbdef])
  push Not at hnc
  by_cases hbr : b = r
  · rw [hbr] at hRbar
    exact exists_commute_of_conj_eq ⟨1, one_mem _, by group⟩
      (DSet.zOf_eq_of_bar_eq H hS hRt hR (hz.rightConjugate t) hz hRbar hr.bar)
  obtain ⟨tb, hb⟩ := ReflData.exists_of_bar hΩ hS hRt (hU.rightConjugate t) hRbar
  by_cases hk : ∀ g ∈ DBar Ω (sec4W Ω S), g * r = r * g → g = r ∨ g = b
  · exact exists_commute_of_two H hS hΩne hdis hr hb hnc.symm hz (hz.rightConjugate t) hk
      ⟨t, ht⟩ htt hbdef.symm
  push Not at hk
  obtain ⟨e, heD, her, hene, heb⟩ := hk
  obtain ⟨Te, Ve, te, he⟩ := DBar.exists_reflData heD
  obtain ⟨ze, hze⟩ := IsZOf.exists_of_rot he.rot
  exact exists_commute_of_four H hS hΩne hdis hr he hnc.symm hbr her hene heb hz hze ⟨t, ht⟩ htt
    hbdef.symm

theorem lemma411 : Lemma411 := by
  intro G _ _ Ω H S hS hdis R hR z hz
  exact ⟨fun T₁ hT₁ T₂ hT₂ => DSet.exists_mGrp_conj H hS hdis hT₁ hT₂,
    ⟨conj_set_eq_omegaOne_diff H hS hdis hR hz,
      fun x hx m hm => zZero_commute H hS hdis hR hz hx hm⟩,
    fun t ht htt => exists_commute_conj H hS hdis hR hz ht htt⟩

theorem b3Conclusion : B3Conclusion := b3Conclusion_of_lemma411 lemma411

end CFSG.ComponentClassification.Asc76.Sec4
