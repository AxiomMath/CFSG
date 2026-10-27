module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4B3Blocks
public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4B3Basic

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {S : Subgroup G}

structure ReflData (Ω : Set (Subgroup G)) (W : Subgroup G) (g : NBar W) (T V : Subgroup G)
    (t : normalizer (W : Set G)) : Prop where
  mem : T ∈ DSet Ω W
  rot : IsDihedralRot V T
  memT : (t : G) ∈ T
  not_mem : (t : G) ∉ V
  eq : (t : NBar W) = g

namespace ReflData

variable {W T V : Subgroup G} {g : NBar W} {t : normalizer (W : Set G)}

omit [Finite G] in
theorem bar (h : ReflData Ω W g T V t) : IsBarOf W T g := ⟨V, h.rot, t, h.memT, h.not_mem, h.eq.symm⟩

omit [Finite G] in
theorem mem_dBar (h : ReflData Ω W g T V t) : g ∈ DBar Ω W := IsBarOf.mem_dBar h.mem h.bar

omit [Finite G] in
theorem mul_self (h : ReflData Ω W g T V t) : (t : G) * t = 1 := h.rot.mul_self _ h.memT h.not_mem

omit [Finite G] in
theorem inv_eq (h : ReflData Ω W g T V t) : (t : G)⁻¹ = t :=
  inv_eq_of_mul_eq_one_right h.mul_self

omit [Finite G] in
theorem conj_rot (h : ReflData Ω W g T V t) {v : G} (hv : v ∈ V) : (t : G)⁻¹ * v * t = v⁻¹ := by
  have h1 := h.rot.conj_eq _ h.memT h.not_mem v hv
  rw [h.inv_eq] at h1 ⊢
  exact h1

theorem inv_mul_conj_mem {g : NBar (sec4W Ω S)} {t : normalizer (sec4W Ω S : Set G)}
    (h : ReflData Ω (sec4W Ω S) g T V t) (H : Sec4Hyp Ω)
    (hS : IsSylowOf 2 S ⊤) {w : G} (hw : w ∈ sec4W Ω S) : w⁻¹ * ((t : G)⁻¹ * w * t) ∈ V :=
  DSet.inv_mul_conj_mem_rot H hS h.mem h.rot h.memT hw

theorem conj_mem_of_le {g : NBar (sec4W Ω S)} {t : normalizer (sec4W Ω S : Set G)}
    (h : ReflData Ω (sec4W Ω S) g T V t) (H : Sec4Hyp Ω)
    (hS : IsSylowOf 2 S ⊤) {X : Subgroup G} (hXW : X ≤ sec4W Ω S) (hVX : V ≤ X) {w : G}
    (hw : w ∈ X) : (t : G)⁻¹ * w * t ∈ X := by
  have e : (t : G)⁻¹ * w * t = w * (w⁻¹ * ((t : G)⁻¹ * w * t)) := by group
  rw [e]
  exact mul_mem hw (hVX (h.inv_mul_conj_mem H hS (hXW hw)))

theorem rot_le {g : NBar (sec4W Ω S)} {t : normalizer (sec4W Ω S : Set G)}
    (h : ReflData Ω (sec4W Ω S) g T V t) (hΩ : Assumption41 Ω)
    (hS : IsSylowOf 2 S ⊤) : V ≤ sec4W Ω S := DSet.rot_le hΩ hS h.mem h.rot

theorem commute {T' V' : Subgroup G} {g g' : NBar (sec4W Ω S)}
    {t t' : normalizer (sec4W Ω S : Set G)} (h : ReflData Ω (sec4W Ω S) g T V t) (h' : ReflData Ω (sec4W Ω S) g' T' V' t')
    (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤) (hc : g * g' = g' * g) (hne : g ≠ g') {v : G}
    (hv : v ∈ V') : (t : G) * v = v * t :=
  DSet.commute_rot_of_commute H hS h.mem h'.mem h'.rot h.bar h'.bar hc hne h.memT hv

omit [Finite G] in
theorem conj_eq_of_commute {v : G} (hv : (t : G) * v = v * t) : (t : G)⁻¹ * v * t = v := by
  rw [mul_assoc, ← hv]
  group

end ReflData

omit [Finite G] in
theorem DBar.exists_reflData {W : Subgroup G} {g : NBar W} (hg : g ∈ DBar Ω W) :
    ∃ T V : Subgroup G, ∃ t : normalizer (W : Set G), ReflData Ω W g T V t := by
  obtain ⟨J, hJ, T, V, hTJ, hV, hTW, t, htT, htV, rfl⟩ := hg
  exact ⟨T, V, t, ⟨⟨⟨J, hJ, hTJ⟩, hTW⟩, hV, htT, htV, rfl⟩⟩

theorem ReflData.exists_of_bar (hΩ : Assumption41 Ω) (hS : IsSylowOf 2 S ⊤)
    {T V : Subgroup G} {g : NBar (sec4W Ω S)} (hT : T ∈ DSet Ω (sec4W Ω S))
    (hV : IsDihedralRot V T) (hg : IsBarOf (sec4W Ω S) T g) :
    ∃ t : normalizer (sec4W Ω S : Set G), ReflData Ω (sec4W Ω S) g T V t := by
  obtain ⟨s, hsT, hsV⟩ := hV.exists_not_mem
  have hsN : s ∈ normalizer (sec4W Ω S : Set G) := by
    obtain ⟨-, h⟩ := hT
    exact h hsT
  exact ⟨⟨s, hsN⟩, hT, hV, hsT, hsV, (IsBarOf.eq_mk hΩ hS hT hg hV (x := ⟨s, hsN⟩) hsT hsV).symm⟩

theorem ReflData.zpowers_eq {P V₀ T V : Subgroup G} {d₀ g : NBar (sec4W Ω S)}
    {t : normalizer (sec4W Ω S : Set G)} (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤)
    (hP : P ∈ DSet Ω (sec4W Ω S)) (hV₀ : IsDihedralRot V₀ P) (hd₀ : IsBarOf (sec4W Ω S) P d₀)
    (h : ReflData Ω (sec4W Ω S) g T V t) (hnc : g * d₀ ≠ d₀ * g) {v₀ : G}
    (hv₀ : zpowers v₀ = V₀) (hv₀o : orderOf v₀ = Nat.card V₀) :
    zpowers (v₀⁻¹ * ((t : G)⁻¹ * v₀ * t)) = V ∧
      orderOf (v₀⁻¹ * ((t : G)⁻¹ * v₀ * t)) = Nat.card V :=
  DSet.zpowers_inv_mul_conj_eq H hS h.mem hP h.rot hV₀ h.bar hd₀ hnc h.memT h.not_mem hv₀ hv₀o

theorem sec4W_le_of_blocks (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤) (hΩne : Ω.Nonempty)
    (hdis : ¬ (CFSG.Fischer.commGraph (DBar Ω (sec4W Ω S))).Connected)
    {R P V₀ X : Subgroup G} {r d₀ : NBar (sec4W Ω S)}
    (hR : R ∈ DSet Ω (sec4W Ω S)) (hr : IsBarOf (sec4W Ω S) R r)
    (hP : P ∈ DSet Ω (sec4W Ω S)) (hV₀ : IsDihedralRot V₀ P) (hd₀ : IsBarOf (sec4W Ω S) P d₀)
    (hrd : d₀ * r ≠ r * d₀) (hXW : X ≤ sec4W Ω S) (hV₀X : V₀ ≤ X)
    (hBX : ∀ T ∈ DSet Ω (sec4W Ω S), ∀ V : Subgroup G, ∀ g : NBar (sec4W Ω S),
      IsDihedralRot V T → IsBarOf (sec4W Ω S) T g → g * r = r * g → V ≤ X) :
    sec4W Ω S ≤ X := by
  have hrD : r ∈ DBar Ω (sec4W Ω S) := IsBarOf.mem_dBar hR hr
  have hd₀D : d₀ ∈ DBar Ω (sec4W Ω S) := IsBarOf.mem_dBar hP hd₀
  obtain ⟨Ur, hUr⟩ := DSet.exists_rot H.hΩ hR
  obtain ⟨tr, htr⟩ := ReflData.exists_of_bar H.hΩ hS hR hUr hr
  have hUrX : Ur ≤ X := hBX R hR Ur r hUr hr rfl
  have hblock : ∀ g : NBar (sec4W Ω S), g ∈ DBar Ω (sec4W Ω S) → g * r = r * g →
      ∃ T V : Subgroup G, ∃ t : normalizer (sec4W Ω S : Set G),
        ReflData Ω (sec4W Ω S) g T V t ∧ V ≤ X := by
    intro g hg hgr
    obtain ⟨T, V, t, ht⟩ := DBar.exists_reflData hg
    exact ⟨T, V, t, ht, hBX T ht.mem V g ht.rot ht.bar hgr⟩
  refine iSup_le fun U' => iSup_le fun hU'S => iSup_le fun hU' => ?_
  obtain ⟨K, hK, R₀, hR₀, hU'R₀⟩ := IsRot.exists_isDihedralRot H.hΩ hU'
  have hU'W : U' ≤ sec4W Ω S := le_sec4W hU'S hU'
  obtain ⟨T, hTK, hU'T, hTW⟩ :=
    exists_isSylowOf_le_normalizer_of_isRot H.hΩ hS hK hR₀ hU'R₀ hU'W
  have hT : T ∈ DSet Ω (sec4W Ω S) := ⟨⟨K, hK, hTK⟩, hTW⟩
  obtain ⟨f, hf⟩ := IsBarOf.exists_of_mem H.hΩ hT
  have hfD : f ∈ DBar Ω (sec4W Ω S) := IsBarOf.mem_dBar hT hf
  by_cases hfr : f * r = r * f
  · exact hBX T hT U' f hU'T hf hfr
  by_cases hfd : f * d₀ = d₀ * f
  ·
    obtain ⟨hgD, hgr, hgeq⟩ := DBar.conj_eq_of_second H hS hΩne hdis hrD hd₀D hfD hrd hfd
    obtain ⟨g, hgdef⟩ : ∃ g, g = f * (r * d₀ * r) * f := ⟨_, rfl⟩
    rw [← hgdef] at hgD hgr hgeq
    obtain ⟨Tg, Vg, tg, htg, hVgX⟩ := hblock g hgD hgr
    have hPy : AschbacherTightEmbedding.rightConjugate P ((tr * tg : normalizer _) : G) ∈
        DSet Ω (sec4W Ω S) := DSet.rightConjugate_mem H.hΩ hP (tr * tg).2
    have hPybar := hd₀.rightConjugate (tr * tg)
    rw [QuotientGroup.mk_mul, htr.eq, htg.eq, hgeq] at hPybar
    have hrot := DSet.rot_eq_of_bar_eq H hS hT hPy hU'T (hV₀.rightConjugate _) hf hPybar
    rw [hrot]
    intro u hu
    rw [mem_rightConjugate_iff] at hu
    have e : u = (tg : G)⁻¹ * ((tr : G)⁻¹ * (((tr * tg : normalizer _) : G) * u *
        ((tr * tg : normalizer _) : G)⁻¹) * tr) * tg := by
      simp only [coe_mul]
      group
    rw [e]
    exact htg.conj_mem_of_le H hS hXW hVgX (htr.conj_mem_of_le H hS hXW hUrX (hV₀X hu))
  ·
    obtain ⟨hgD, hgr, hgeq⟩ := DBar.conj_eq_of_third H hS hΩne hdis hrD hd₀D hfD hrd hfr hfd
    obtain ⟨g, hgdef⟩ : ∃ g, g = d₀ * f * d₀ := ⟨_, rfl⟩
    rw [← hgdef] at hgD hgr hgeq
    obtain ⟨Tg, Vg, tg, htg, hVgX⟩ := hblock g hgD hgr
    have hPy : AschbacherTightEmbedding.rightConjugate P (tg : G) ∈ DSet Ω (sec4W Ω S) :=
      DSet.rightConjugate_mem H.hΩ hP tg.2
    have hPybar := hd₀.rightConjugate tg
    rw [htg.eq, hgeq] at hPybar
    have hrot := DSet.rot_eq_of_bar_eq H hS hT hPy hU'T (hV₀.rightConjugate _) hf hPybar
    rw [hrot]
    intro u hu
    rw [mem_rightConjugate_iff] at hu
    have e : u = (tg : G)⁻¹ * ((tg : G) * u * (tg : G)⁻¹) * tg := by group
    rw [e]
    exact htg.conj_mem_of_le H hS hXW hVgX (hV₀X hu)

theorem mul_eq_of_four (H : Sec4Hyp Ω) (hS : IsSylowOf 2 S ⊤) {P V₀ : Subgroup G}
    {d₀ a b c τ : NBar (sec4W Ω S)} (hP : P ∈ DSet Ω (sec4W Ω S)) (hV₀ : IsDihedralRot V₀ P)
    (hd₀ : IsBarOf (sec4W Ω S) P d₀) {v₀ : G} (hv₀ : zpowers v₀ = V₀)
    (hv₀o : orderOf v₀ = Nat.card V₀) {Ta Tb Tc Tτ Va Vb Vc Vτ : Subgroup G}
    {ta tb tc tτ : normalizer (sec4W Ω S : Set G)} (ha : ReflData Ω (sec4W Ω S) a Ta Va ta)
    (hb : ReflData Ω (sec4W Ω S) b Tb Vb tb) (hc : ReflData Ω (sec4W Ω S) c Tc Vc tc)
    (hτ : ReflData Ω (sec4W Ω S) τ Tτ Vτ tτ) (hab : a ≠ b) (hac : a ≠ c) (haτ : a ≠ τ)
    (hbc : b ≠ c) (hbτ : b ≠ τ) (hcτ : c ≠ τ) (hab' : a * b = b * a) (hac' : a * c = c * a)
    (haτ' : a * τ = τ * a) (hbc' : b * c = c * b) (hbτ' : b * τ = τ * b)
    (hcτ' : c * τ = τ * c) (had : a * d₀ ≠ d₀ * a)
    (hfix : (b * c * a * τ)⁻¹ * d₀ * (b * c * a * τ) = d₀) :
    (v₀⁻¹ * ((tτ : G)⁻¹ * v₀ * tτ)) * (v₀⁻¹ * ((ta : G)⁻¹ * v₀ * ta)) *
      (v₀⁻¹ * ((tc : G)⁻¹ * v₀ * tc)) * (v₀⁻¹ * ((tb : G)⁻¹ * v₀ * tb)) = v₀⁻¹ * v₀⁻¹ := by
  have hΩ := H.hΩ
  obtain ⟨ca, hca⟩ : ∃ x, x = v₀⁻¹ * ((ta : G)⁻¹ * v₀ * ta) := ⟨_, rfl⟩
  obtain ⟨cb, hcb⟩ : ∃ x, x = v₀⁻¹ * ((tb : G)⁻¹ * v₀ * tb) := ⟨_, rfl⟩
  obtain ⟨cc, hcc⟩ : ∃ x, x = v₀⁻¹ * ((tc : G)⁻¹ * v₀ * tc) := ⟨_, rfl⟩
  obtain ⟨cτ, hcτd⟩ : ∃ x, x = v₀⁻¹ * ((tτ : G)⁻¹ * v₀ * tτ) := ⟨_, rfl⟩
  rw [← hca, ← hcb, ← hcc, ← hcτd]
  have hv₀V : v₀ ∈ V₀ := hv₀ ▸ mem_zpowers v₀
  have hv₀W : v₀ ∈ (sec4W Ω S) := DSet.rot_le hΩ hS hP hV₀ hv₀V
  have hcaV : ca ∈ Va := hca ▸ ha.inv_mul_conj_mem H hS hv₀W
  have hcbV : cb ∈ Vb := hcb ▸ hb.inv_mul_conj_mem H hS hv₀W
  have hccV : cc ∈ Vc := hcc ▸ hc.inv_mul_conj_mem H hS hv₀W
  have hcτV : cτ ∈ Vτ := hcτd ▸ hτ.inv_mul_conj_mem H hS hv₀W
  have hcaW := ha.rot_le hΩ hS hcaV
  have hcbW := hb.rot_le hΩ hS hcbV
  have hccW := hc.rot_le hΩ hS hccV
  have hcτW := hτ.rot_le hΩ hS hcτV
  have hav : (ta : G)⁻¹ * v₀ * ta = v₀ * ca := by rw [hca]; group
  have hbv : (tb : G)⁻¹ * v₀ * tb = v₀ * cb := by rw [hcb]; group
  have hcv : (tc : G)⁻¹ * v₀ * tc = v₀ * cc := by rw [hcc]; group
  have hτv : (tτ : G)⁻¹ * v₀ * tτ = v₀ * cτ := by rw [hcτd]; group
  have hfixc : ∀ {g g' : NBar (sec4W Ω S)} {T V T' V' : Subgroup G}
      {t t' : normalizer (sec4W Ω S : Set G)},
      ReflData Ω (sec4W Ω S) g T V t → ReflData Ω (sec4W Ω S) g' T' V' t' →
      g * g' = g' * g → g ≠ g' →
      ∀ x ∈ V', (t : G)⁻¹ * x * t = x := fun h h' hgg hne x hx =>
    ReflData.conj_eq_of_commute (h.commute h' H hS hgg hne hx)
  set y : normalizer (sec4W Ω S : Set G) := tb * tc * ta * tτ with hy
  have hconj : (y : G)⁻¹ * v₀ * y = v₀ * cτ * ca * cc * cb := by
    have e : (y : G)⁻¹ * v₀ * y = (tτ : G)⁻¹ * ((ta : G)⁻¹ * ((tc : G)⁻¹ *
        ((tb : G)⁻¹ * v₀ * tb) * tc) * ta) * tτ := by
      simp only [hy, coe_mul]
      group
    rw [e, hbv]
    have e1 : (tc : G)⁻¹ * (v₀ * cb) * tc = ((tc : G)⁻¹ * v₀ * tc) * ((tc : G)⁻¹ * cb * tc) := by
      group
    rw [e1, hcv, hfixc hc hb hbc'.symm hbc.symm cb hcbV]
    have e2 : (ta : G)⁻¹ * (v₀ * cc * cb) * ta =
        ((ta : G)⁻¹ * v₀ * ta) * ((ta : G)⁻¹ * cc * ta) * ((ta : G)⁻¹ * cb * ta) := by group
    rw [e2, hav, hfixc ha hc hac' hac cc hccV, hfixc ha hb hab' hab cb hcbV]
    have e3 : (tτ : G)⁻¹ * (v₀ * ca * cc * cb) * tτ = ((tτ : G)⁻¹ * v₀ * tτ) *
        ((tτ : G)⁻¹ * ca * tτ) * ((tτ : G)⁻¹ * cc * tτ) * ((tτ : G)⁻¹ * cb * tτ) := by group
    rw [e3, hτv, hfixc hτ ha haτ'.symm haτ.symm ca hcaV, hfixc hτ hc hcτ'.symm hcτ.symm cc hccV,
      hfixc hτ hb hbτ'.symm hbτ.symm cb hcbV]
  have hPy : AschbacherTightEmbedding.rightConjugate P (y : G) ∈ DSet Ω (sec4W Ω S) :=
    DSet.rightConjugate_mem hΩ hP y.2
  have hPybar := hd₀.rightConjugate y
  have hyimg : (y : NBar (sec4W Ω S)) = b * c * a * τ := by
    simp only [hy, QuotientGroup.mk_mul, ha.eq, hb.eq, hc.eq, hτ.eq]
  rw [hyimg, hfix] at hPybar
  have hrot := DSet.rot_eq_of_bar_eq H hS hPy hP (hV₀.rightConjugate _) hV₀ hPybar hd₀
  have hyv : (y : G)⁻¹ * v₀ * y ∈ V₀ := by
    rw [← hrot, mem_rightConjugate_iff]
    have e : (y : G) * ((y : G)⁻¹ * v₀ * y) * (y : G)⁻¹ = v₀ := by group
    rw [e]
    exact hv₀V
  obtain ⟨q, hq⟩ : ∃ q, q = cτ * ca * cc * cb := ⟨_, rfl⟩
  have hqV : q ∈ V₀ := by
    have : q = v₀⁻¹ * ((y : G)⁻¹ * v₀ * y) := by rw [hconj, hq]; group
    rw [this]
    exact mul_mem (inv_mem hv₀V) hyv
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hv₀ ▸ hqV : q ∈ zpowers v₀)
  have hqa : (ta : G)⁻¹ * q * ta = cτ * ca⁻¹ * cc * cb := by
    have e : (ta : G)⁻¹ * q * ta = ((ta : G)⁻¹ * cτ * ta) * ((ta : G)⁻¹ * ca * ta) *
        ((ta : G)⁻¹ * cc * ta) * ((ta : G)⁻¹ * cb * ta) := by rw [hq]; group
    rw [e, hfixc ha hτ haτ' haτ cτ hcτV, ha.conj_rot hcaV, hfixc ha hc hac' hac cc hccV,
      hfixc ha hb hab' hab cb hcbV]
  have hqa' : (ta : G)⁻¹ * q * ta = q * ca ^ k := by
    have h1 := inv_mul_conj_zpow hΩ hS ta.2 hv₀W k
    rw [hk, ← hca] at h1
    calc (ta : G)⁻¹ * q * ta = q * (q⁻¹ * ((ta : G)⁻¹ * q * ta)) := by group
      _ = q * ca ^ k := by rw [h1]
  obtain ⟨hzpa, hoa⟩ := ReflData.zpowers_eq H hS hP hV₀ hd₀ ha had hv₀ hv₀o
  rw [← hca] at hzpa hoa
  have hcard := DSet.card_rot_eq hΩ ha.mem hP ha.rot hV₀
  have hcomm : ∀ {x y : G}, x ∈ sec4W Ω S → y ∈ sec4W Ω S → x * y = y * x :=
    fun hx hy => sec4W_comm hΩ hS hx hy
  have hkey : ca ^ (k + 2) = 1 := by
    rw [hqa, hq] at hqa'
    have hm : cc * cb * ca ^ k = ca ^ k * (cc * cb) :=
      hcomm (mul_mem hccW hcbW) (zpow_mem hcaW k)
    have h2 : ca⁻¹ * (cc * cb) = ca * ca ^ k * (cc * cb) := by
      have h3 : cτ * (ca⁻¹ * (cc * cb)) = cτ * (ca * ca ^ k * (cc * cb)) := by
        calc cτ * (ca⁻¹ * (cc * cb)) = cτ * ca⁻¹ * cc * cb := by group
          _ = cτ * ca * cc * cb * ca ^ k := hqa'
          _ = cτ * (ca * (cc * cb * ca ^ k)) := by group
          _ = cτ * (ca * ca ^ k * (cc * cb)) := by rw [hm]; group
      exact mul_left_cancel h3
    have h4 : ca⁻¹ = ca * ca ^ k := mul_right_cancel h2
    calc ca ^ (k + 2) = ca * (ca * ca ^ k) := by group
      _ = 1 := by rw [← h4, mul_inv_cancel]
  have hdvd : (orderOf v₀ : ℤ) ∣ k + 2 := by
    rw [hv₀o, ← hcard, ← hoa]
    exact orderOf_dvd_iff_zpow_eq_one.mpr hkey
  have hv₀k : v₀ ^ (k + 2) = 1 := orderOf_dvd_iff_zpow_eq_one.mp hdvd
  rw [← hq]
  calc q = v₀ ^ k := hk.symm
    _ = v₀ ^ (k + 2) * v₀⁻¹ * v₀⁻¹ := by rw [zpow_add]; group
    _ = v₀⁻¹ * v₀⁻¹ := by rw [hv₀k, one_mul]

end CFSG.ComponentClassification.Asc76.Sec4
