module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem5H
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec2Lem5
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec2Lem5E
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec2Lem5G

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem hasTwo625_twoBound_of_fieldType_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h615 : Stmt6_1_5_F4)
    {F : Subgroup G} (hFV : F ≤ V) (hF4 : Nat.card F = 4) (hF : IsFieldType M L V F 1) :
    HasTwo625 T F 2 ∧ TwoBound625 T F 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm, hSyl⟩ := h.exists_conj_sylow_ch62 (ne_bot_of_card_four_ch625 hF4) hFV
  set F' := conjSubgroup F m with hF'
  have hF'f := h.isFieldType_conjSubgroup hm hF
  have hVm : conjSubgroup V m = V := conjSubgroup_eq_iff_mem_normalizer.mpr hm.2
  have hF'V : F' ≤ V := by rw [← hVm]; exact conjSubgroup_mono_left m hFV
  have hF'4 : Nat.card F' = 4 := by rw [card_conjSubgroup, hF4]
  obtain ⟨-, -, t', ht'M, ht', ht'F⟩ := hF'f
  rw [conjSubgroup_one] at ht'M ht'
  have hcard : 2 ^ 2 ≤ Nat.card ↥(V ⊓ Subgroup.centralizer ({t'} : Set G)) := by
    refine (show 2 ^ 2 = Nat.card F' by rw [hF'4]; norm_num).le.trans
      (Subgroup.card_le_of_le fun f hf => ⟨hF'V hf, ?_⟩)
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp ht'F f hf)
  obtain ⟨t₂, ht₂M, ⟨k, hk⟩, hinv₂, hCt⟩ :=
    h.toHyp611Nat.exists_two_element_fieldAut ht'M.1 ht' hcard
  have ht₂C : t₂ ∈ Subgroup.centralizer (F' : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun f hf => ?_
    have hf' : f ∈ V ⊓ Subgroup.centralizer ({t₂} : Set G) := by
      rw [← hCt]
      exact ⟨hF'V hf, Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp ht'F f hf)⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp hf'.2
  have ht₂N : t₂ ∈ M ⊓ Subgroup.normalizer (F' : Set G) :=
    ⟨ht₂M, Subgroup.centralizer_le_normalizer _ ht₂C⟩
  have hzP : IsPGroup 2 (Subgroup.zpowers t₂) := by
    intro x
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp x.2
    refine ⟨k, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
  obtain ⟨x, hx, hle⟩ := F7.isSylowTwoOf_exists_conj_le hSyl (Subgroup.zpowers_le.mpr ht₂N) hzP
  obtain ⟨y, hy, hyt⟩ := Subgroup.mem_map.mp (hle (Subgroup.mem_zpowers t₂))
  have hyt' : y = x⁻¹ * t₂ * x := by
    rw [← hyt]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hyT : y ∈ T := hy.1
  have hyinv : IsInvolutoryFieldAut L y := hyt' ▸ hinv₂.conj_ch6 (h.normal hx.1)

  have hF'y : F' = V ⊓ Subgroup.centralizer ({y} : Set G) := by
    apply Subgroup.eq_of_le_of_card_ge
    · intro f hf
      refine ⟨hF'V hf, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have hxf : x * f * x⁻¹ ∈ F' := (Subgroup.mem_normalizer_iff.mp hx.2 f).mp hf
      have h1 := Subgroup.mem_centralizer_iff.mp ht₂C _ hxf
      rw [hyt']
      calc f * (x⁻¹ * t₂ * x) = x⁻¹ * ((x * f * x⁻¹) * t₂) * x := by group
        _ = x⁻¹ * (t₂ * (x * f * x⁻¹)) * x := by rw [h1]
        _ = x⁻¹ * t₂ * x * f := by group
    · rw [h.toHyp611Nat.card_fix_of_fieldAut hyT hyinv, hF'4]
      norm_num
  rw [hF'y] at hSyl
  obtain ⟨-, -, hNsyl⟩ := h.toHyp611Nat.lemma_6_1_14_one_F4 h432 hyT hyinv hSyl
  have hidx := h.relIndex_normalizer_fix_F4 h331 h432 h615 hyT hyinv hSyl
  rw [← hF'y] at hNsyl hidx
  have hcardN : Nat.card ↥(T ⊓ Subgroup.normalizer (F' : Set G)) * 2 = Nat.card T := by
    have h1 := Subgroup.relIndex_mul_card (H := T ⊓ Subgroup.normalizer (F' : Set G)) (K := T)
    rw [inf_of_le_left inf_le_left, hidx] at h1
    linarith
  have hF : HasTwo625 T F' 2 ∧ TwoBound625 T F' 2 := by
    refine ⟨⟨T ⊓ Subgroup.normalizer (F' : Set G), inf_le_right, h.sylow.1.to_le inf_le_left,
      hcardN⟩, fun P hPN hP2 => ?_⟩
    have := card_le_of_isSylowIn_ch62 hNsyl hPN hP2
    rw [← hcardN]
    exact Nat.mul_le_mul_right 2 this
  have e : F = conjSubgroup F' m⁻¹ := (conjSubgroup_conj_inv F m).symm
  rw [e]
  exact ⟨hasTwo625_conjSubgroup hF.1 m⁻¹, twoBound625_conjSubgroup hF.2 m⁻¹⟩

theorem twoBound625_of_type3_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h615 : Stmt6_1_5_F4)
    (h6110 : Stmt6_1_10_F4) (hE612 : Ch6InE612) {F : Subgroup G} (hFV : F ≤ V)
    (hF4 : Nat.card F = 4) (hFc : ¬ IsCentralType L V F 1) (hFf : ¬ IsFieldType M L V F 1) :
    TwoBound625 T F 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm, hSyl⟩ := h.exists_conj_sylow_ch62 (ne_bot_of_card_four_ch625 hF4) hFV
  set F' := conjSubgroup F m with hF'
  obtain ⟨hF'V, hF'4, hF'c, hF'f⟩ := h.type3_conjSubgroup hm hFV hF4 hFc hFf

  have hC : Subgroup.centralizer (F' : Set G) ≤ Subgroup.normalizer (V : Set G) := by
    by_contra hC
    obtain ⟨t, htT, ht, hF't⟩ := h.exists_fieldAut_of_not_le_F4 h432 h6110 hE612 hF'V
      (h.mQuot_eq_two_ch625 hF'V hF'4) hC hSyl
    apply hF'f
    refine ⟨?_, hF'4, t, ?_, ?_, ?_⟩
    · rw [conjSubgroup_one]; exact hF'V
    · rw [conjSubgroup_one]; exact h.T_le_MV_ch625 htT
    · rw [conjSubgroup_one]; exact ht
    · refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
      have hu' : u ∈ V ⊓ Subgroup.centralizer ({t} : Set G) := by rw [← hF't]; exact hu
      exact Subgroup.mem_centralizer_singleton_iff.mp hu'.2
  have hCM : Subgroup.centralizer (F' : Set G) ≤ M := hC.trans (h.normalizer_V_le_F4 h432)

  have hsylC : IsSylowIn 2 ((T ⊓ Subgroup.normalizer (F' : Set G)) ⊓
      (M ⊓ Subgroup.centralizer (F' : Set G))) (M ⊓ Subgroup.centralizer (F' : Set G)) :=
    A4.isSylowTwoOf_inf_normal hSyl (inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _))
      (fun x hx => A4.mem_normalizer_inf (Subgroup.le_normalizer hx.1)
        (mem_normalizer_centralizer_ch62 hx.2))
  have hTC : (T ⊓ Subgroup.normalizer (F' : Set G)) ⊓ (M ⊓ Subgroup.centralizer (F' : Set G)) =
      T ⊓ Subgroup.centralizer (F' : Set G) := by
    ext x
    simp only [Subgroup.mem_inf]
    exact ⟨fun hx => ⟨hx.1.1, hx.2.2⟩, fun hx => ⟨⟨hx.1, Subgroup.centralizer_le_normalizer _
      hx.2⟩, h.T_le hx.1, hx.2⟩⟩
  rw [hTC] at hsylC

  obtain ⟨x, y, hP⟩ := h.isPlane625_of_not_central hF'V hF'4 hF'c
  have hCT : T ⊓ Subgroup.centralizer (F' : Set G) ≤ ch6Q T V := by
    rintro t ⟨htT, htC⟩
    refine ⟨htT, ?_⟩
    have htN := h.toHyp611.T_le_normalizer htT
    by_cases hlin : h.IsLin625 ⟨t, htN⟩
    · apply h.data.mem_centralizer_of_conj_eq ⟨t, htN⟩
      intro w
      have hx := h.conj_fix_of_mem_centralizer htN htC ((hP.2 x).mpr (Or.inr (Or.inl rfl)))
      have hy := h.conj_fix_of_mem_centralizer htN htC
        ((hP.2 y).mpr (Or.inr (Or.inr (Or.inl rfl))))
      rw [eq_add_of_det2_ne_zero hP.1 w, map_add, hlin, hlin, hx, hy]
    · exact absurd ((h.isFieldType_iff_ch625 hF'V hF'4).mpr
        ⟨t, h.T_le_MV_ch625 htT, htC, htN, hlin⟩) hF'f
  have hQ8 : Nat.card (ch6Q T V) * 8 = Nat.card T := by
    have h1 := Subgroup.relIndex_mul_card (H := ch6Q T V) (K := T)
    rw [inf_of_le_left (inf_le_left : ch6Q T V ≤ T), h.relIndex_Q_T_F4 h331 h615] at h1
    linarith
  have hB : TwoBound625 T F' 4 := by
    intro P hPN hP2
    have h2 := relIndex_centralizer_le_two_ch62 hP2 hPN hF'4
      (fun u hu => h.sq_eq_one_of_mem_V (hF'V hu))
    have h3 : Nat.card ↥(P ⊓ Subgroup.centralizer (F' : Set G)) ≤
        Nat.card ↥(T ⊓ Subgroup.centralizer (F' : Set G)) :=
      card_le_of_isSylowIn_ch62 hsylC (le_inf (inf_le_right.trans hCM) inf_le_right)
        (hP2.to_le inf_le_left)
    have h4 := Subgroup.card_le_of_le hCT
    have h5 := Subgroup.relIndex_mul_card (H := P ⊓ Subgroup.centralizer (F' : Set G)) (K := P)
    rw [inf_of_le_left inf_le_left] at h5
    calc Nat.card P * 4 = (P ⊓ Subgroup.centralizer (F' : Set G)).relIndex P *
          Nat.card ↥(P ⊓ Subgroup.centralizer (F' : Set G)) * 4 := by rw [h5]
      _ ≤ 2 * Nat.card (ch6Q T V) * 4 := by
          apply Nat.mul_le_mul_right
          exact Nat.mul_le_mul h2 (h3.trans h4)
      _ = Nat.card T := by rw [← hQ8]; ring
  rw [show F = conjSubgroup F' m⁻¹ from (conjSubgroup_conj_inv F m).symm]
  exact twoBound625_conjSubgroup hB m⁻¹

theorem fusion_ch625_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h615 : Stmt6_1_5_F4)
    (h6110 : Stmt6_1_10_F4) (hE612 : Ch6InE612) {F : Subgroup G} (hFV : F ≤ V)
    (hF4 : Nat.card F = 4) {g : G} (hFg : conjSubgroup F g ≤ V) :
    ∃ x ∈ ch6MV M V, conjSubgroup F g = conjSubgroup F x := by
  have hF'4 : Nat.card (conjSubgroup F g) = 4 := by rw [card_conjSubgroup, hF4]
  have tri : ∀ U : Subgroup G, IsCentralType L V U 1 ∨ IsFieldType M L V U 1 ∨
      (¬ IsCentralType L V U 1 ∧ ¬ IsFieldType M L V U 1) := by
    intro U
    by_cases hc : IsCentralType L V U 1
    · exact Or.inl hc
    · by_cases hf : IsFieldType M L V U 1
      · exact Or.inr (Or.inl hf)
      · exact Or.inr (Or.inr ⟨hc, hf⟩)
  have back : ∀ {k : ℕ}, HasTwo625 T (conjSubgroup F g) k → HasTwo625 T F k := fun hh => by
    have := hasTwo625_conjSubgroup hh g⁻¹
    rwa [conjSubgroup_conj_inv] at this
  rcases tri F with hc | hf | ⟨hc, hf⟩ <;> rcases tri (conjSubgroup F g) with hc' | hf' | ⟨hc', hf'⟩
  · exact h.exists_conj_of_central hFV hF4 hFg hF'4 hc hc'
  · exact (false_of_hasTwo_twoBound (hasTwo625_conjSubgroup (h.hasTwo625_of_central hFV hF4 hc) g)
      (h.hasTwo625_twoBound_of_fieldType_F4 h331 h432 h615 hFg hF'4 hf').2 (by norm_num)).elim
  · exact (false_of_hasTwo_twoBound (hasTwo625_conjSubgroup (h.hasTwo625_of_central hFV hF4 hc) g)
      (h.twoBound625_of_type3_F4 h331 h432 h615 h6110 hE612 hFg hF'4 hc' hf') (by norm_num)).elim
  · exact (false_of_hasTwo_twoBound (back (h.hasTwo625_of_central hFg hF'4 hc'))
      (h.hasTwo625_twoBound_of_fieldType_F4 h331 h432 h615 hFV hF4 hf).2 (by norm_num)).elim
  · exact h.exists_conj_of_fieldType hFV hF4 hFg hF'4 hf hf'
  · exact (false_of_hasTwo_twoBound (hasTwo625_conjSubgroup
      (h.hasTwo625_twoBound_of_fieldType_F4 h331 h432 h615 hFV hF4 hf).1 g)
      (h.twoBound625_of_type3_F4 h331 h432 h615 h6110 hE612 hFg hF'4 hc' hf') (by norm_num)).elim
  · exact (false_of_hasTwo_twoBound (back (h.hasTwo625_of_central hFg hF'4 hc'))
      (h.twoBound625_of_type3_F4 h331 h432 h615 h6110 hE612 hFV hF4 hc hf) (by norm_num)).elim
  · exact (false_of_hasTwo_twoBound (back
      (h.hasTwo625_twoBound_of_fieldType_F4 h331 h432 h615 hFg hF'4 hf').1)
      (h.twoBound625_of_type3_F4 h331 h432 h615 h6110 hE612 hFV hF4 hc hf) (by norm_num)).elim
  · exact h.exists_conj_of_type3_F4 h331 h615 hFV hF4 hFg hF'4 hc hf hc' hf'

theorem commutator_eq_bot_of_card_four_ch625_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4)
    (h615 : Stmt6_1_5_F4) (h6110 : Stmt6_1_10_F4) (hE612 : Ch6InE612) {g : G}
    (hI4 : Nat.card ↥(V ⊓ conjSubgroup V g) = 4) : ⁅V, conjSubgroup V g⁆ = ⊥ := by
  set F := V ⊓ conjSubgroup V g with hF
  have hFV : F ≤ V := inf_le_left
  have hFW : F ≤ conjSubgroup V g := inf_le_right
  have hFg : conjSubgroup F g⁻¹ ≤ V := by
    have := conjSubgroup_mono_left g⁻¹ hFW
    rwa [conjSubgroup_conj_inv] at this
  obtain ⟨x, hxM, hx⟩ := h.fusion_ch625_F4 h331 h432 h615 h6110 hE612 hFV hI4 hFg

  have hnF : x * g ∈ Subgroup.normalizer (F : Set G) := by
    apply conjSubgroup_eq_iff_mem_normalizer.mp
    calc conjSubgroup F (x * g) = conjSubgroup (conjSubgroup F x) g := by
          rw [conjSubgroup_conjSubgroup]
      _ = F := by rw [← hx, conjSubgroup_inv_conj]
  have hVx : conjSubgroup V x = V := conjSubgroup_eq_iff_mem_normalizer.mpr hxM.2
  have hWn : conjSubgroup V g = conjSubgroup V (x * g) := by
    rw [← conjSubgroup_conjSubgroup, hVx]

  have hmem : conjAct F ⟨x * g, hnF⟩ ∈
      autOn (ch6MV M V ⊓ Subgroup.normalizer (F : Set G)) F := by
    rw [h.autOn_eq_top_ch625_F4 h331 h615 hFV hI4]
    exact Subgroup.mem_top _
  obtain ⟨k, hkM, hk⟩ := mem_autOn_iff.mp hmem
  set c := (k : G)⁻¹ * (x * g) with hc
  have hcC : c ∈ Subgroup.centralizer (F : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have h1 := congrArg (fun φ : MulAut ↥F => ((φ ⟨f, hf⟩ : ↥F) : G)) hk
    simp only [conjAct_apply_coe] at h1
    have e : x * g * f * (x * g)⁻¹ = k * f * (k : G)⁻¹ := h1.symm
    calc f * c = (k : G)⁻¹ * (k * f * (k : G)⁻¹) * (x * g) := by rw [hc]; group
      _ = (k : G)⁻¹ * (x * g * f * (x * g)⁻¹) * (x * g) := by rw [e]
      _ = c * f := by rw [hc]; group
  have hVk : conjSubgroup V (k : G)⁻¹ = V :=
    conjSubgroup_eq_iff_mem_normalizer.mpr ((ch6MV M V).inv_mem hkM.1).2
  have hWc : conjSubgroup V g = conjSubgroup V c := by
    rw [hWn]
    calc conjSubgroup V (x * g) = conjSubgroup (conjSubgroup V (k : G)⁻¹) (x * g) := by
          rw [hVk]
      _ = conjSubgroup V c := by rw [conjSubgroup_conjSubgroup]
  rw [hWc]
  by_cases hcV : c ∈ Subgroup.normalizer (V : Set G)
  · rw [conjSubgroup_eq_iff_mem_normalizer.mpr hcV]
    exact commutator_eq_bot_of_le_ch625 h.toHyp611.isElemAbelian.1 le_rfl le_rfl
  have hH : ¬ Subgroup.centralizer (F : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    fun hle => hcV (hle hcC)
  obtain ⟨m, hm, hFmV, hm2, hHm, hSyl⟩ :=
    h.exists_conj_fieldType_ch62 hFV (h.mQuot_eq_two_ch625 hFV hI4) hH
  obtain ⟨-, -, -, -, -, -, ⟨hab, -⟩, -⟩ :=
    h.lemma_6_2_4_one_five_F4 h331 h432 h615 h6110 hE612 hFmV hm2 hHm hSyl

  have hc'C : m⁻¹ * c * m ∈ Subgroup.centralizer (conjSubgroup F m : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hf' : m * f * m⁻¹ ∈ F := mem_conjSubgroup_iff.mp hf
    have h1 := Subgroup.mem_centralizer_iff.mp hcC _ hf'
    calc f * (m⁻¹ * c * m) = m⁻¹ * ((m * f * m⁻¹) * c) * m := by group
      _ = m⁻¹ * (c * (m * f * m⁻¹)) * m := by rw [h1]
      _ = m⁻¹ * c * m * f := by group
  have hVX : V ≤ conjClosure V (Subgroup.centralizer (conjSubgroup F m : Set G)) :=
    le_conjClosure _ _
  have hVc'X : conjSubgroup V (m⁻¹ * c * m) ≤
      conjClosure V (Subgroup.centralizer (conjSubgroup F m : Set G)) := by
    intro v hv
    have h1 := mem_conjClosure (Subgroup.inv_mem _ hc'C) (mem_conjSubgroup_iff.mp hv)
    have e : (m⁻¹ * c * m)⁻¹ * (m⁻¹ * c * m * v * (m⁻¹ * c * m)⁻¹) * (m⁻¹ * c * m)⁻¹⁻¹ = v := by
      group
    rwa [e] at h1
  have h1 := commutator_eq_bot_of_le_ch625 hab.1 hVX hVc'X

  have hVm : conjSubgroup V m⁻¹ = V :=
    conjSubgroup_eq_iff_mem_normalizer.mpr ((ch6MV M V).inv_mem hm).2
  have e : conjSubgroup (conjSubgroup V (m⁻¹ * c * m)) m⁻¹ = conjSubgroup V c := by
    calc conjSubgroup (conjSubgroup V (m⁻¹ * c * m)) m⁻¹ = conjSubgroup V (m⁻¹ * c) := by
          rw [conjSubgroup_conjSubgroup]; congr 1; group
      _ = conjSubgroup (conjSubgroup V m⁻¹) c := by rw [conjSubgroup_conjSubgroup]
      _ = conjSubgroup V c := by rw [hVm]
  have h2 : conjSubgroup ⁅V, conjSubgroup V (m⁻¹ * c * m)⁆ m⁻¹ = conjSubgroup ⊥ m⁻¹ := by
    rw [h1]
  rwa [conjSubgroup_commutator, hVm, e, conjSubgroup_bot] at h2

theorem lemma_6_2_5_five_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h615 : Stmt6_1_5_F4)
    (h6110 : Stmt6_1_10_F4) (hE612 : Ch6InE612) {g : G}
    (hnc : ¬ IsCyclic ↥(V ⊓ conjSubgroup V g)) : ⁅V, conjSubgroup V g⁆ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVab : ⁅V, V⁆ = ⊥ :=
    commutator_eq_bot_of_le_ch625 h.toHyp611.isElemAbelian.1 le_rfl le_rfl
  have hV16 : Nat.card V = 2 ^ 4 := by
    have := h.natural.card_eq
    rw [this]
    norm_num
  have hW16 : Nat.card (conjSubgroup V g) = 2 ^ 4 := by rw [card_conjSubgroup, hV16]
  have hIV : V ⊓ conjSubgroup V g ≤ V := inf_le_left
  have hIW : V ⊓ conjSubgroup V g ≤ conjSubgroup V g := inf_le_right
  have hWV : conjSubgroup V g = V → ⁅V, conjSubgroup V g⁆ = ⊥ := fun e => by rw [e]; exact hVab
  obtain ⟨i, hi4, hIi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (hV16 ▸ Subgroup.card_dvd_of_le hIV)
  interval_cases i
  · exact absurd (isCyclic_of_card_dvd_prime (p := 2) (by rw [hIi]; norm_num)) hnc
  · exact absurd (isCyclic_of_card_dvd_prime (p := 2) (by rw [hIi]; norm_num)) hnc
  · exact h.commutator_eq_bot_of_card_four_ch625_F4 h331 h432 h615 h6110 hE612
      (by rw [hIi]; norm_num)
  · apply hWV
    have hrel : (V ⊓ conjSubgroup V g).relIndex V = 2 := by
      have h1 := Subgroup.relIndex_mul_card (H := V ⊓ conjSubgroup V g) (K := V)
      rw [inf_of_le_left hIV, hIi, hV16] at h1
      omega
    exact h.lemma_6_2_5_six_F4 h331 h432 h615 h6110 hE612 hIV hrel hIW
  · apply hWV
    have hIV' : V ⊓ conjSubgroup V g = V :=
      Subgroup.eq_of_le_of_card_ge hIV (by rw [hIi, hV16])
    have hVW : V ≤ conjSubgroup V g := inf_eq_left.mp hIV'
    exact (Subgroup.eq_of_le_of_card_ge hVW (by rw [hW16, hV16])).symm

end Hyp6Sec2

theorem stmt6_2_5_of_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h615 : Stmt6_1_5_F4)
    (h6110 : Stmt6_1_10_F4) (hE612 : Ch6InE612) : Stmt6_2_5_F4 := by
  intro G _ _ T M L V h
  dsimp only
  refine ⟨fun hidx F ⟨hFV, hF4, hFc, hFf⟩ => ?_, fun hidx => ⟨h.card_type3_F4 h331 h615 hidx,
    fun F F' ⟨hFV, hF4, hFc, hFf⟩ ⟨hF'V, hF'4, hF'c, hF'f⟩ =>
      h.exists_conj_of_type3_F4 h331 h615 hFV hF4 hF'V hF'4 hFc hFf hF'c hF'f⟩,
    fun F F' hFF' => ?_,
    fun F hFV hF4 g hFg => h.fusion_ch625_F4 h331 h432 h615 h6110 hE612 hFV hF4 hFg,
    fun g hg => h.lemma_6_2_5_four_F4 h331 h432 h615 h6110 hE612 hg,
    fun g hg => h.lemma_6_2_5_five_F4 h331 h432 h615 h6110 hE612 hg,
    fun Y hYV hY g hYg => h.lemma_6_2_5_six_F4 h331 h432 h615 h6110 hE612 hYV hY hYg⟩
  · obtain ⟨x, y, hP⟩ := h.isPlane625_of_not_central hFV hF4 hFc
    exact hFf (h.isFieldType_of_isPlane625_six_F4 h331 h615 hidx hFV hF4 hP)
  · rcases hFF' with ⟨hF, hF'⟩ | ⟨hF, hF'⟩ | ⟨⟨hFV, hF4, hFc, hFf⟩, ⟨hF'V, hF'4, hF'c, hF'f⟩⟩
    · have hFV : F ≤ V := by have := hF.1; rwa [conjSubgroup_one] at this
      have hF'V : F' ≤ V := by have := hF'.1; rwa [conjSubgroup_one] at this
      exact h.exists_conj_of_central hFV hF.2.1 hF'V hF'.2.1 hF hF'
    · have hFV : F ≤ V := by have := hF.1; rwa [conjSubgroup_one] at this
      have hF'V : F' ≤ V := by have := hF'.1; rwa [conjSubgroup_one] at this
      exact h.exists_conj_of_fieldType hFV hF.2.1 hF'V hF'.2.1 hF hF'
    · exact h.exists_conj_of_type3_F4 h331 h615 hFV hF4 hF'V hF'4 hFc hFf hF'c hF'f

end CFSG.Quasithin.H13
