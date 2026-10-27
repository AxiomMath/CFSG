module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerCP2

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.ABGLocalTools CFSG.LocalCores CFSG.Quasithin.B6
open scoped commutatorElement

section Abbrevs

variable {H : Type*} [Group H]

abbrev normL (L₀ : Subgroup H) : Subgroup H := Subgroup.normalizer (L₀ : Set H)

abbrev centL (L₀ : Subgroup H) : Subgroup H := Subgroup.centralizer (L₀ : Set H)

abbrev normT (T L₀ : Subgroup H) : Subgroup H := T ⊓ normL L₀

abbrev locL (T L₀ : Subgroup H) : Subgroup H := L₀ ⊔ normT T L₀

abbrev maxL (T M L₀ : Subgroup H) : Subgroup H := (M ⊓ L₀) ⊔ normT T L₀

@[expose] noncomputable def actOf (L₀ : Subgroup H) (n : H) : MulAut ↥L₀ := by
  classical
  exact if hn : n ∈ normL L₀ then L₀.normalizerMonoidHom ⟨n, hn⟩ else 1

@[expose] def actImg (L₀ Y : Subgroup H) : Subgroup (MulAut ↥L₀) :=
  (Y.subgroupOf (normL L₀)).map L₀.normalizerMonoidHom

@[expose] def innGroup (L₀ : Subgroup H) : Subgroup (MulAut ↥L₀) :=
  (MulAut.conj : ↥L₀ →* MulAut ↥L₀).range

variable {L₀ : Subgroup H}

theorem actOf_of_mem {n : H} (hn : n ∈ normL L₀) :
    actOf L₀ n = L₀.normalizerMonoidHom ⟨n, hn⟩ := by
  classical
  simp [actOf, hn]

theorem actOf_mul {a b : H} (ha : a ∈ normL L₀) (hb : b ∈ normL L₀) :
    actOf L₀ (a * b) = actOf L₀ a * actOf L₀ b := by
  rw [actOf_of_mem ha, actOf_of_mem hb, actOf_of_mem ((normL L₀).mul_mem ha hb)]
  exact map_mul L₀.normalizerMonoidHom ⟨a, ha⟩ ⟨b, hb⟩

theorem actOf_inv {a : H} (ha : a ∈ normL L₀) : actOf L₀ a⁻¹ = (actOf L₀ a)⁻¹ := by
  rw [actOf_of_mem ha, actOf_of_mem ((normL L₀).inv_mem ha)]
  exact map_inv L₀.normalizerMonoidHom ⟨a, ha⟩

theorem actOf_coe {n : H} (hn : n ∈ normL L₀) (l : ↥L₀) :
    ((actOf L₀ n l : ↥L₀) : H) = n * l * n⁻¹ := by
  rw [actOf_of_mem hn]
  simp

theorem actOf_eq_one_iff {n : H} (hn : n ∈ normL L₀) : actOf L₀ n = 1 ↔ n ∈ centL L₀ := by
  have h1 := Subgroup.normalizerMonoidHom_ker L₀
  have h2 : (⟨n, hn⟩ : ↥(normL L₀)) ∈ L₀.normalizerMonoidHom.ker ↔ n ∈ centL L₀ := by
    rw [h1]
    exact Subgroup.mem_subgroupOf
  rw [actOf_of_mem hn, ← h2, MonoidHom.mem_ker]

theorem actOf_of_mem_self {l : H} (hl : l ∈ L₀) :
    actOf L₀ l = MulAut.conj (⟨l, hl⟩ : ↥L₀) := by
  rw [actOf_of_mem (Subgroup.le_normalizer hl)]
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  simp

theorem mem_actImg {Y : Subgroup H} {a : MulAut ↥L₀} :
    a ∈ actImg L₀ Y ↔ ∃ n ∈ Y, n ∈ normL L₀ ∧ actOf L₀ n = a := by
  constructor
  · intro h
    obtain ⟨⟨n, hn⟩, hnY, rfl⟩ := Subgroup.mem_map.1 h
    exact ⟨n, hnY, hn, (actOf_of_mem hn)⟩
  · rintro ⟨n, hnY, hn, rfl⟩
    exact Subgroup.mem_map.2 ⟨⟨n, hn⟩, hnY, (actOf_of_mem hn).symm⟩

theorem actImg_mono {Y Y' : Subgroup H} (h : Y ≤ Y') : actImg L₀ Y ≤ actImg L₀ Y' :=
  Subgroup.map_mono fun _ hx => h hx

theorem actOf_mem_actImg {Y : Subgroup H} {n : H} (hn : n ∈ normL L₀) (hY : n ∈ Y) :
    actOf L₀ n ∈ actImg L₀ Y := mem_actImg.2 ⟨n, hY, hn, rfl⟩

theorem mem_innGroup {a : MulAut ↥L₀} : a ∈ innGroup L₀ ↔ ∃ l : ↥L₀, MulAut.conj l = a :=
  MonoidHom.mem_range

theorem actImg_self (L₀ : Subgroup H) : actImg L₀ L₀ = innGroup L₀ := by
  ext a
  constructor
  · intro ha
    obtain ⟨n, hnL, hn, rfl⟩ := mem_actImg.1 ha
    exact mem_innGroup.2 ⟨⟨n, hnL⟩, (actOf_of_mem_self hnL).symm⟩
  · intro ha
    obtain ⟨l, rfl⟩ := mem_innGroup.1 ha
    exact mem_actImg.2 ⟨l, l.2, Subgroup.le_normalizer l.2, actOf_of_mem_self l.2⟩

theorem actImg_conj_mem {n : H} (hn : n ∈ normL L₀) {a : MulAut ↥L₀} (ha : a ∈ innGroup L₀) :
    actOf L₀ n * a * (actOf L₀ n)⁻¹ ∈ innGroup L₀ := by
  rw [← actImg_self] at ha ⊢
  obtain ⟨l, hl, hlN, rfl⟩ := mem_actImg.1 ha
  have hconj : n * l * n⁻¹ ∈ L₀ := (Subgroup.mem_normalizer_iff.1 hn l).1 hl
  have hmem : n * l * n⁻¹ ∈ normL L₀ := Subgroup.le_normalizer hconj
  have e : actOf L₀ n * actOf L₀ l * (actOf L₀ n)⁻¹ = actOf L₀ (n * l * n⁻¹) := by
    rw [actOf_mul ((normL L₀).mul_mem hn hlN) ((normL L₀).inv_mem hn), actOf_mul hn hlN,
      actOf_inv hn]
  rw [e]
  exact mem_actImg.2 ⟨n * l * n⁻¹, hconj, hmem, rfl⟩

theorem actImg_normL_le_normalizer (L₀ : Subgroup H) :
    actImg L₀ (normL L₀) ≤ Subgroup.normalizer (innGroup L₀ : Set (MulAut ↥L₀)) := by
  intro a ha
  obtain ⟨n, -, hn, rfl⟩ := mem_actImg.1 ha
  rw [Subgroup.mem_normalizer_iff]
  intro d
  constructor
  · exact fun hd => actImg_conj_mem hn hd
  · intro hd
    have h2 := actImg_conj_mem ((normL L₀).inv_mem hn) hd
    rw [actOf_inv hn] at h2
    have e : (actOf L₀ n)⁻¹ * (actOf L₀ n * d * (actOf L₀ n)⁻¹) * ((actOf L₀ n)⁻¹)⁻¹ = d := by
      group
    rwa [e] at h2

theorem innGroup_le_actImg (L₀ : Subgroup H) : innGroup L₀ ≤ actImg L₀ (normL L₀) := by
  rw [← actImg_self]
  exact actImg_mono Subgroup.le_normalizer

theorem innGroup_normal_in_actImg (L₀ : Subgroup H) :
    ((innGroup L₀).subgroupOf (actImg L₀ (normL L₀))).Normal :=
  (Subgroup.normal_subgroupOf_iff (innGroup_le_actImg L₀)).2 fun d _ hd ha =>
    (Subgroup.mem_normalizer_iff.1 (actImg_normL_le_normalizer L₀ ha) d).1 hd

theorem eq_one_of_centralizes_inn (hperf : Group.IsPerfect ↥L₀) {β : MulAut ↥L₀}
    (hβ : β ∈ Subgroup.centralizer (innGroup L₀ : Set (MulAut ↥L₀))) : β = 1 := by
  refine eq_one_of_commute_inner hperf β fun x => ?_
  exact ((Subgroup.mem_centralizer_iff.1 hβ) (MulAut.conj x) (mem_innGroup.2 ⟨x, rfl⟩)).symm

theorem innGroup_equiv (L₀ : Subgroup H) :
    Nonempty (innGroup L₀ ≃* ↥L₀ ⧸ Subgroup.center ↥L₀) := by
  have hker : (MulAut.conj : ↥L₀ →* MulAut ↥L₀).ker = Subgroup.center ↥L₀ := by
    ext x
    rw [MonoidHom.mem_ker]
    exact conj_eq_one_iff x
  exact ⟨(QuotientGroup.quotientKerEquivRange (MulAut.conj : ↥L₀ →* MulAut ↥L₀)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)⟩

theorem opCore_inn_trivial [Finite ↥L₀] {p : ℕ} (hp : p.Prime) (hqs : CFSG.IsQuasisimple ↥L₀)
    {A Y : Subgroup (MulAut ↥L₀)} (hDA : innGroup L₀ ≤ A)
    (hAD : ∀ a ∈ A, ∀ d ∈ innGroup L₀, a * d * a⁻¹ ∈ innGroup L₀) (hYA : Y ≤ A)
    (hAY : ∀ a ∈ A, ∀ y ∈ Y, a * y * a⁻¹ ∈ Y) (hYp : IsPGroup p ↥Y) : Y = ⊥ := by
  have hperf : Group.IsPerfect ↥L₀ := hqs.1
  let W : Subgroup ↥L₀ := (Y ⊓ innGroup L₀).comap (MulAut.conj : ↥L₀ →* MulAut ↥L₀)
  have hWn : W.Normal := by
    refine ⟨fun w hw l => ?_⟩
    have hl : (MulAut.conj l : MulAut ↥L₀) ∈ innGroup L₀ := mem_innGroup.2 ⟨l, rfl⟩
    have hw1 : (MulAut.conj w : MulAut ↥L₀) ∈ Y := hw.1
    have hw2 : (MulAut.conj w : MulAut ↥L₀) ∈ innGroup L₀ := hw.2
    have e : (MulAut.conj (l * w * l⁻¹) : MulAut ↥L₀) =
        MulAut.conj l * MulAut.conj w * (MulAut.conj l)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    refine ⟨?_, ?_⟩
    · show (MulAut.conj (l * w * l⁻¹) : MulAut ↥L₀) ∈ Y
      rw [e]
      exact hAY _ (hDA hl) _ hw1
    · show (MulAut.conj (l * w * l⁻¹) : MulAut ↥L₀) ∈ innGroup L₀
      rw [e]
      exact (innGroup L₀).mul_mem ((innGroup L₀).mul_mem hl hw2) ((innGroup L₀).inv_mem hl)
  have hD : ⁅innGroup L₀, innGroup L₀⁆ = innGroup L₀ := by
    have : Group.IsPerfect ↥(innGroup L₀) := by
      have := hperf
      exact Group.IsPerfect.range (MulAut.conj : ↥L₀ →* MulAut ↥L₀)
    exact Subgroup.isPerfect_iff.1 this
  rcases quasisimple_normal_subgroups hqs hWn with hW | hW
  · exfalso
    have hDY : innGroup L₀ ≤ Y := by
      intro a ha
      obtain ⟨l, rfl⟩ := mem_innGroup.1 ha
      have : l ∈ W := by rw [hW]; trivial
      exact this.1
    have hDp : IsPGroup p ↥(innGroup L₀) := hYp.to_le hDY
    have hDbot : innGroup L₀ = ⊥ := eq_bot_of_perfect_of_isPGroup hp hD hDp
    have hcomm : ∀ x y : ↥L₀, x * y = y * x := by
      intro x y
      have h1 : (MulAut.conj x : MulAut ↥L₀) ∈ innGroup L₀ := mem_innGroup.2 ⟨x, rfl⟩
      rw [hDbot] at h1
      have h2 : MulAut.conj x = 1 := h1
      have := (conj_eq_one_iff x).1 h2
      exact (Subgroup.mem_center_iff.1 this y).symm
    have hbot : commutator ↥L₀ = ⊥ := by
      rw [_root_.commutator_def]
      refine eq_bot_iff.2 (Subgroup.commutator_le.2 fun x _ y _ => ?_)
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm x y
    have htop : commutator ↥L₀ = ⊤ := Group.isPerfect_def.1 hperf
    have hnt := isQuasisimple_nontrivial hqs
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥L₀)
    apply hx
    have : x ∈ commutator ↥L₀ := by rw [htop]; trivial
    rw [hbot] at this
    exact this
  · have hYD : Y ⊓ innGroup L₀ = ⊥ := by
      rw [eq_bot_iff]
      intro a ha
      obtain ⟨hy, hD'⟩ := ha
      obtain ⟨l, rfl⟩ := mem_innGroup.1 hD'
      have hlW : l ∈ W := ⟨hy, hD'⟩
      have := (conj_eq_one_iff l).2 (hW hlW)
      rw [Subgroup.mem_bot]
      exact this
    rw [eq_bot_iff]
    intro y hy
    have hyc : y ∈ Subgroup.centralizer (innGroup L₀ : Set (MulAut ↥L₀)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have h1 : d * y * d⁻¹ * y⁻¹ ∈ Y ⊓ innGroup L₀ := by
        refine ⟨Y.mul_mem (hAY d (hDA hd) y hy) (Y.inv_mem hy), ?_⟩
        have e : d * y * d⁻¹ * y⁻¹ = d * (y * d⁻¹ * y⁻¹) := by group
        rw [e]
        exact (innGroup L₀).mul_mem hd (hAD y (hYA hy) d⁻¹ ((innGroup L₀).inv_mem hd))
      rw [hYD, Subgroup.mem_bot] at h1
      calc d * y = (d * y * d⁻¹ * y⁻¹) * (y * d) := by group
        _ = y * d := by rw [h1, one_mul]
    exact Subgroup.mem_bot.2 (eq_one_of_centralizes_inn hperf hyc)

end Abbrevs

section Decomp

variable {H : Type*} [Group H] {p : ℕ} {T M : Subgroup H} {ι : Type*} {L : ι → Subgroup H}

theorem CPSetting.K_le_sup (hS : CPSetting p T M L) (i₀ : ι) :
    (⨆ i, L i : Subgroup H) ≤ L i₀ ⊔ centL (L i₀) := by
  refine iSup_le fun j => ?_
  by_cases hj : j = i₀
  · subst hj
    exact le_sup_left
  · exact (hS.centralizes hj).trans le_sup_right

theorem CPSetting.normL_eq (hS : CPSetting p T M L) (i₀ : ι) :
    normL (L i₀) = (⨆ i, L i : Subgroup H) ⊔ normT T (L i₀) := hS.normalizer_eq i₀

theorem CPSetting.exists_decomp (hS : CPSetting p T M L) (i₀ : ι) {n : H}
    (hn : n ∈ normL (L i₀)) :
    ∃ l ∈ L i₀, ∃ c ∈ centL (L i₀), ∃ t ∈ normT T (L i₀), n = l * c * t := by
  have hNL : n ∈ (⨆ i, L i : Subgroup H) ⊔ normT T (L i₀) := by
    rw [← hS.normL_eq i₀]
    exact hn
  have hTn : normT T (L i₀) ≤ Subgroup.normalizer ((⨆ i, L i : Subgroup H) : Set H) :=
    inf_le_left.trans hS.T_le_normalizer_K
  obtain ⟨k, hk, t, ht, rfl⟩ := exists_mul_of_mem_sup hTn hNL
  have hk' : k ∈ L i₀ ⊔ centL (L i₀) := hS.K_le_sup i₀ hk
  obtain ⟨l, hl, c, hc, rfl⟩ := exists_mul_of_mem_sup (Subgroup.centralizer_le_normalizer _) hk'
  exact ⟨l, hl, c, hc, t, ht, rfl⟩

theorem CPSetting.actImg_normL (hS : CPSetting p T M L) (i₀ : ι) :
    actImg (L i₀) (normL (L i₀)) = innGroup (L i₀) ⊔ actImg (L i₀) (normT T (L i₀)) := by
  apply le_antisymm
  · intro a ha
    obtain ⟨n, -, hn, rfl⟩ := mem_actImg.1 ha
    obtain ⟨l, hl, c, hc, t, ht, rfl⟩ := hS.exists_decomp i₀ hn
    have hlN : l ∈ normL (L i₀) := Subgroup.le_normalizer hl
    have hcN : c ∈ normL (L i₀) := Subgroup.centralizer_le_normalizer _ hc
    have htN : t ∈ normL (L i₀) := ht.2
    rw [actOf_mul ((normL _).mul_mem hlN hcN) htN, actOf_mul hlN hcN,
      (actOf_eq_one_iff hcN).2 hc, mul_one]
    have hD : actOf (L i₀) l ∈ innGroup (L i₀) := by
      rw [← actImg_self]
      exact actOf_mem_actImg hlN hl
    exact Subgroup.mul_mem_sup hD (actOf_mem_actImg htN ht)
  · exact sup_le (innGroup_le_actImg _) (actImg_mono inf_le_right)

theorem CPSetting.actImg_normL_eq_locL (hS : CPSetting p T M L) (i₀ : ι) :
    actImg (L i₀) (normL (L i₀)) = actImg (L i₀) (locL T (L i₀)) := by
  apply le_antisymm
  · intro a ha
    obtain ⟨n, -, hn, rfl⟩ := mem_actImg.1 ha
    obtain ⟨l, hl, c, hc, t, ht, rfl⟩ := hS.exists_decomp i₀ hn
    have hlN : l ∈ normL (L i₀) := Subgroup.le_normalizer hl
    have hcN : c ∈ normL (L i₀) := Subgroup.centralizer_le_normalizer _ hc
    have htN : t ∈ normL (L i₀) := ht.2
    have e : actOf (L i₀) (l * c * t) = actOf (L i₀) (l * t) := by
      rw [actOf_mul ((normL _).mul_mem hlN hcN) htN, actOf_mul hlN hcN,
        (actOf_eq_one_iff hcN).2 hc, mul_one, actOf_mul hlN htN]
    rw [e]
    exact actOf_mem_actImg ((normL _).mul_mem hlN htN) (Subgroup.mul_mem_sup hl ht)
  · exact actImg_mono (sup_le Subgroup.le_normalizer inf_le_right)

end Decomp

end CFSG.QuasithinUnique.Setup.Layer
