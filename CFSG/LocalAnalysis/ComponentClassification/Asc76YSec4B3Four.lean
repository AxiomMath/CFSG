module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4B3Gen

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {S : Subgroup G}

theorem DBar.commute_of_commute (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤) (hΩne : Ω.Nonempty)
    (hdis : ¬ (CFSG.Fischer.commGraph (DBar Ω (sec4W Ω S))).Connected)
    {r x y : NBar (sec4W Ω S)} (hr : r ∈ DBar Ω (sec4W Ω S)) (hx : x ∈ DBar Ω (sec4W Ω S))
    (hy : y ∈ DBar Ω (sec4W Ω S)) (hxr : x * r = r * x) (hyr : y * r = r * y) :
    x * y = y * x :=
  DBar.commute_trans H hS hΩne hdis hx hr hy hxr hyr.symm

theorem DBar.not_commute_of_commute (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤) (hΩne : Ω.Nonempty)
    (hdis : ¬ (CFSG.Fischer.commGraph (DBar Ω (sec4W Ω S))).Connected)
    {r d₀ x : NBar (sec4W Ω S)} (hr : r ∈ DBar Ω (sec4W Ω S)) (hd₀ : d₀ ∈ DBar Ω (sec4W Ω S))
    (hx : x ∈ DBar Ω (sec4W Ω S)) (hrd : d₀ * r ≠ r * d₀) (hxr : x * r = r * x) :
    x * d₀ ≠ d₀ * x := fun h =>
  hrd (DBar.commute_trans H hS hΩne hdis hd₀ hx hr h.symm hxr)

theorem mem_of_four (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤) (hΩne : Ω.Nonempty)
    (hdis : ¬ (CFSG.Fischer.commGraph (DBar Ω (sec4W Ω S))).Connected)
    {P V₀ : Subgroup G} {r d₀ a b c τ x : NBar (sec4W Ω S)}
    (hP : P ∈ DSet Ω (sec4W Ω S)) (hV₀ : IsDihedralRot V₀ P) (hd₀ : IsBarOf (sec4W Ω S) P d₀)
    (hr : r ∈ DBar Ω (sec4W Ω S)) (hrd : d₀ * r ≠ r * d₀) (ha : a ∈ DBar Ω (sec4W Ω S))
    (hb : b ∈ DBar Ω (sec4W Ω S)) (hc : c ∈ DBar Ω (sec4W Ω S))
    (hτ : τ ∈ DBar Ω (sec4W Ω S)) (hx : x ∈ DBar Ω (sec4W Ω S)) (har : a * r = r * a)
    (hbr : b * r = r * b) (hcr : c * r = r * c) (hτr : τ * r = r * τ) (hxr : x * r = r * x)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hτa : τ ≠ a) (hτb : τ ≠ b) (hτc : τ ≠ c)
    (hfix : (b * c * a * τ)⁻¹ * d₀ * (b * c * a * τ) = d₀) :
    x = a ∨ x = b ∨ x = c ∨ x = τ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hxa, hxb, hxc, hxτ⟩ := hcon
  have hΩ := H.hΩ
  have hd₀D : d₀ ∈ DBar Ω (sec4W Ω S) := IsBarOf.mem_dBar hP hd₀
  obtain ⟨τ', hτ'D, hτ'r, hτ'a, hτ'b, hτ'x, hfix'⟩ := DBar.exists_fourth H hS hΩne hdis hr hd₀D
    ha hb hx hrd har hbr hxr hab (Ne.symm hxa) (Ne.symm hxb)
  obtain ⟨v₀, hv₀, hv₀o⟩ := hV₀.exists_gen
  obtain ⟨Ta, Va, ta, hta⟩ := DBar.exists_reflData ha
  obtain ⟨Tb, Vb, tb, htb⟩ := DBar.exists_reflData hb
  obtain ⟨Tc, Vc, tc, htc⟩ := DBar.exists_reflData hc
  obtain ⟨Tτ, Vτ, tτ, htτ⟩ := DBar.exists_reflData hτ
  obtain ⟨Tx, Vx, tx, htx⟩ := DBar.exists_reflData hx
  obtain ⟨Tτ', Vτ', tτ', htτ'⟩ := DBar.exists_reflData hτ'D
  have hcm := fun {y y' : NBar (sec4W Ω S)} (hy : y ∈ DBar Ω (sec4W Ω S))
    (hy' : y' ∈ DBar Ω (sec4W Ω S)) (hyr : y * r = r * y) (hy'r : y' * r = r * y') =>
    DBar.commute_of_commute H hS hΩne hdis hr hy hy' hyr hy'r
  have R1 := mul_eq_of_four H hS hP hV₀ hd₀ hv₀ hv₀o hta htb htc htτ hab hac hτa.symm hbc
    hτb.symm hτc.symm (hcm ha hb har hbr) (hcm ha hc har hcr) (hcm ha hτ har hτr)
    (hcm hb hc hbr hcr) (hcm hb hτ hbr hτr) (hcm hc hτ hcr hτr)
    (DBar.not_commute_of_commute H hS hΩne hdis hr hd₀D ha hrd har) hfix
  have R2 := mul_eq_of_four H hS hP hV₀ hd₀ hv₀ hv₀o hta htb htx htτ' hab (Ne.symm hxa)
    (Ne.symm hτ'a) (Ne.symm hxb) (Ne.symm hτ'b) (Ne.symm hτ'x) (hcm ha hb har hbr)
    (hcm ha hx har hxr) (hcm ha hτ'D har hτ'r) (hcm hb hx hbr hxr) (hcm hb hτ'D hbr hτ'r)
    (hcm hx hτ'D hxr hτ'r) (DBar.not_commute_of_commute H hS hΩne hdis hr hd₀D ha hrd har) hfix'
  obtain ⟨ca, hca⟩ : ∃ y, y = v₀⁻¹ * ((ta : G)⁻¹ * v₀ * ta) := ⟨_, rfl⟩
  obtain ⟨cb, hcb⟩ : ∃ y, y = v₀⁻¹ * ((tb : G)⁻¹ * v₀ * tb) := ⟨_, rfl⟩
  obtain ⟨cc, hcc⟩ : ∃ y, y = v₀⁻¹ * ((tc : G)⁻¹ * v₀ * tc) := ⟨_, rfl⟩
  obtain ⟨cτ, hcτd⟩ : ∃ y, y = v₀⁻¹ * ((tτ : G)⁻¹ * v₀ * tτ) := ⟨_, rfl⟩
  obtain ⟨cx, hcx⟩ : ∃ y, y = v₀⁻¹ * ((tx : G)⁻¹ * v₀ * tx) := ⟨_, rfl⟩
  obtain ⟨cτ', hcτ'⟩ : ∃ y, y = v₀⁻¹ * ((tτ' : G)⁻¹ * v₀ * tτ') := ⟨_, rfl⟩
  rw [← hca, ← hcb, ← hcc, ← hcτd] at R1
  rw [← hca, ← hcb, ← hcx, ← hcτ'] at R2
  have hv₀V : v₀ ∈ V₀ := hv₀ ▸ mem_zpowers v₀
  have hv₀W : v₀ ∈ sec4W Ω S := DSet.rot_le hΩ hS hP hV₀ hv₀V
  have hcaV : ca ∈ Va := hca ▸ hta.inv_mul_conj_mem H hS hv₀W
  have hccV : cc ∈ Vc := hcc ▸ htc.inv_mul_conj_mem H hS hv₀W
  have hcτV : cτ ∈ Vτ := hcτd ▸ htτ.inv_mul_conj_mem H hS hv₀W
  have hcxV : cx ∈ Vx := hcx ▸ htx.inv_mul_conj_mem H hS hv₀W
  have hcτ'V : cτ' ∈ Vτ' := hcτ' ▸ htτ'.inv_mul_conj_mem H hS hv₀W
  have hcaW := hta.rot_le hΩ hS hcaV
  have hccW := htc.rot_le hΩ hS hccV
  have hcxW := htx.rot_le hΩ hS hcxV
  have key : cτ * cc = cτ' * cx := by
    have h1 : cτ * ca * cc * cb = cτ' * ca * cx * cb := R1.trans R2.symm
    have hac' : ca * cc = cc * ca := sec4W_comm hΩ hS hcaW hccW
    have hax' : ca * cx = cx * ca := sec4W_comm hΩ hS hcaW hcxW
    have h2 : (cτ * cc) * (ca * cb) = (cτ' * cx) * (ca * cb) := by
      calc (cτ * cc) * (ca * cb) = cτ * (ca * cc) * cb := by rw [hac']; group
        _ = cτ' * (ca * cx) * cb := by rw [← mul_assoc, h1]; group
        _ = (cτ' * cx) * (ca * cb) := by rw [hax']; group
    exact mul_right_cancel h2
  have hfx : ∀ {g : NBar (sec4W Ω S)} {T V : Subgroup G} {t : normalizer (sec4W Ω S : Set G)},
      ReflData Ω (sec4W Ω S) g T V t → g * x = x * g → g ≠ x → ∀ y ∈ V,
        (tx : G)⁻¹ * y * tx = y := fun h hgx hne y hy =>
    ReflData.conj_eq_of_commute (htx.commute h H hS hgx.symm hne.symm hy)
  have hxτ' : τ' ≠ x := hτ'x
  have h3 : (tx : G)⁻¹ * (cτ * cc) * tx = (tx : G)⁻¹ * (cτ' * cx) * tx := by rw [key]
  have e1 : (tx : G)⁻¹ * (cτ * cc) * tx = ((tx : G)⁻¹ * cτ * tx) * ((tx : G)⁻¹ * cc * tx) := by
    group
  have e2 : (tx : G)⁻¹ * (cτ' * cx) * tx = ((tx : G)⁻¹ * cτ' * tx) * ((tx : G)⁻¹ * cx * tx) := by
    group
  rw [e1, e2, hfx htτ (hcm hτ hx hτr hxr) (Ne.symm hxτ) cτ hcτV,
    hfx htc (hcm hc hx hcr hxr) (Ne.symm hxc) cc hccV,
    hfx htτ' (hcm hτ'D hx hτ'r hxr) hxτ' cτ' hcτ'V, htx.conj_rot hcxV, key] at h3
  have h4 : cx = cx⁻¹ := mul_left_cancel h3
  obtain ⟨-, hox⟩ := ReflData.zpowers_eq H hS hP hV₀ hd₀ htx
    (DBar.not_commute_of_commute H hS hΩne hdis hr hd₀D hx hrd hxr) hv₀ hv₀o
  rw [← hcx] at hox
  apply htx.rot.gen_mul_self_ne_one hox
  calc cx * cx = cx * cx⁻¹ := by rw [← h4]
    _ = 1 := mul_inv_cancel cx

theorem zOf_mul_eq_of_four (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤) {P : Subgroup G}
    {d₀ a b c τ : NBar (sec4W Ω S)} (hP : P ∈ DSet Ω (sec4W Ω S))
    (hd₀ : IsBarOf (sec4W Ω S) P d₀) {z₀ : G} (hz₀ : IsZOf P z₀)
    {Ta Tb Tc Tτ Va Vb Vc Vτ : Subgroup G} {ta tb tc tτ : normalizer (sec4W Ω S : Set G)}
    (ha : ReflData Ω (sec4W Ω S) a Ta Va ta) (hb : ReflData Ω (sec4W Ω S) b Tb Vb tb)
    (hc : ReflData Ω (sec4W Ω S) c Tc Vc tc) (hτ : ReflData Ω (sec4W Ω S) τ Tτ Vτ tτ)
    {za zb zc zτ : G} (hza : IsZOf Ta za) (hzb : IsZOf Tb zb) (hzc : IsZOf Tc zc)
    (hzτ : IsZOf Tτ zτ) (hab : a ≠ b) (hac : a ≠ c) (haτ : a ≠ τ) (hbc : b ≠ c) (hbτ : b ≠ τ)
    (hcτ : c ≠ τ) (hab' : a * b = b * a) (hac' : a * c = c * a) (haτ' : a * τ = τ * a)
    (hbc' : b * c = c * b) (hbτ' : b * τ = τ * b) (hcτ' : c * τ = τ * c)
    (had : a * d₀ ≠ d₀ * a) (hbd : b * d₀ ≠ d₀ * b) (hcd : c * d₀ ≠ d₀ * c)
    (hτd : τ * d₀ ≠ d₀ * τ) (hfix : (b * c * a * τ)⁻¹ * d₀ * (b * c * a * τ) = d₀) :
    za * zb * zc * zτ = 1 := by
  have hΩ := H.hΩ
  have hz₀a : (ta : G)⁻¹ * z₀ * ta = z₀ * za :=
    conj_z_of_not_commute H hS ha.mem hP ha.rot hza hz₀ ha.bar hd₀ had ha.memT ha.not_mem
  have hz₀b : (tb : G)⁻¹ * z₀ * tb = z₀ * zb :=
    conj_z_of_not_commute H hS hb.mem hP hb.rot hzb hz₀ hb.bar hd₀ hbd hb.memT hb.not_mem
  have hz₀c : (tc : G)⁻¹ * z₀ * tc = z₀ * zc :=
    conj_z_of_not_commute H hS hc.mem hP hc.rot hzc hz₀ hc.bar hd₀ hcd hc.memT hc.not_mem
  have hz₀τ : (tτ : G)⁻¹ * z₀ * tτ = z₀ * zτ :=
    conj_z_of_not_commute H hS hτ.mem hP hτ.rot hzτ hz₀ hτ.bar hd₀ hτd hτ.memT hτ.not_mem
  have hfz : ∀ {g g' : NBar (sec4W Ω S)} {T V T' V' : Subgroup G}
      {t t' : normalizer (sec4W Ω S : Set G)} {y : G}, ReflData Ω (sec4W Ω S) g T V t →
      ReflData Ω (sec4W Ω S) g' T' V' t' → IsZOf T' y → g * g' = g' * g → g ≠ g' →
      (t : G)⁻¹ * y * t = y := fun h h' hy hgg hne =>
    ReflData.conj_eq_of_commute (h.commute h' H hS hgg hne (hy.mem_rot h'.rot).1)
  set y : normalizer (sec4W Ω S : Set G) := tb * tc * ta * tτ with hy
  have hconj : (y : G)⁻¹ * z₀ * y = z₀ * zτ * za * zc * zb := by
    have e : (y : G)⁻¹ * z₀ * y = (tτ : G)⁻¹ * ((ta : G)⁻¹ * ((tc : G)⁻¹ *
        ((tb : G)⁻¹ * z₀ * tb) * tc) * ta) * tτ := by
      simp only [hy, coe_mul]
      group
    rw [e, hz₀b]
    have e1 : (tc : G)⁻¹ * (z₀ * zb) * tc = ((tc : G)⁻¹ * z₀ * tc) * ((tc : G)⁻¹ * zb * tc) := by
      group
    rw [e1, hz₀c, hfz hc hb hzb hbc'.symm hbc.symm]
    have e2 : (ta : G)⁻¹ * (z₀ * zc * zb) * ta =
        ((ta : G)⁻¹ * z₀ * ta) * ((ta : G)⁻¹ * zc * ta) * ((ta : G)⁻¹ * zb * ta) := by group
    rw [e2, hz₀a, hfz ha hc hzc hac' hac, hfz ha hb hzb hab' hab]
    have e3 : (tτ : G)⁻¹ * (z₀ * za * zc * zb) * tτ = ((tτ : G)⁻¹ * z₀ * tτ) *
        ((tτ : G)⁻¹ * za * tτ) * ((tτ : G)⁻¹ * zc * tτ) * ((tτ : G)⁻¹ * zb * tτ) := by group
    rw [e3, hz₀τ, hfz hτ ha hza haτ'.symm haτ.symm, hfz hτ hc hzc hcτ'.symm hcτ.symm,
      hfz hτ hb hzb hbτ'.symm hbτ.symm]
  have hPy : AschbacherTightEmbedding.rightConjugate P (y : G) ∈ DSet Ω (sec4W Ω S) :=
    DSet.rightConjugate_mem hΩ hP y.2
  have hPybar := hd₀.rightConjugate y
  have hyimg : (y : NBar (sec4W Ω S)) = b * c * a * τ := by
    simp only [hy, QuotientGroup.mk_mul, ha.eq, hb.eq, hc.eq, hτ.eq]
  rw [hyimg, hfix] at hPybar
  have hzeq := DSet.zOf_eq_of_bar_eq H hS hPy hP (hz₀.rightConjugate (y : G)) hz₀ hPybar hd₀
  rw [hconj] at hzeq
  have hW := fun {u v : G} (hu : u ∈ sec4W Ω S) (hv : v ∈ sec4W Ω S) => sec4W_comm hΩ hS hu hv
  have hzW : ∀ {T V : Subgroup G} {g : NBar (sec4W Ω S)} {t : normalizer (sec4W Ω S : Set G)}
      {u : G}, ReflData Ω (sec4W Ω S) g T V t → IsZOf T u → u ∈ sec4W Ω S :=
    fun h hu => h.rot_le hΩ hS (hu.mem_rot h.rot).1
  have h1 : zτ * za * zc * zb = 1 := by
    have : z₀ * (zτ * za * zc * zb) = z₀ * 1 := by
      calc z₀ * (zτ * za * zc * zb) = z₀ * zτ * za * zc * zb := by group
        _ = z₀ := hzeq
        _ = z₀ * 1 := (mul_one z₀).symm
    exact mul_left_cancel this
  have hab'' : za * zb = zb * za := hW (hzW ha hza) (hzW hb hzb)
  calc za * zb * zc * zτ = zτ * (za * zb * zc) := by
        rw [hW (mul_mem (mul_mem (hzW ha hza) (hzW hb hzb)) (hzW hc hzc)) (hzW hτ hzτ)]
    _ = zτ * za * zc * zb := by
        rw [hab'', mul_assoc zb, hW (hzW hb hzb) (mul_mem (hzW ha hza) (hzW hc hzc))]
        group
    _ = 1 := h1

end CFSG.ComponentClassification.Asc76.Sec4
