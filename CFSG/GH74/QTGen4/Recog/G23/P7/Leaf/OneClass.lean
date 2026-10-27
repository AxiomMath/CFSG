module

public import CFSG.Quasithin.Background.A1cTransferVariants
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.GH74.QTGen4.Recog.G23.MSylowC
public import CFSG.GH74.QTGen4.Recog.G23.MLettersD
public import CFSG.GH74.QTGen4.Recog.G23.HLettersB
public import CFSG.GH74.QTGen4.Recog.G23.P7.OpenLeaves

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable
open scoped MatrixGroups

variable {G : Type} [Group G]

theorem orderOf_conj_aux (x t : G) : orderOf (x⁻¹ * t * x) = orderOf t := by
  have h := orderOf_injective (MulAut.conj x⁻¹).toMonoidHom (MulAut.conj x⁻¹).injective t
  simpa [MulAut.conj_apply] using h

theorem exists_conj_mem_of_isPGroup [Finite G] {T : Subgroup G} (hT2 : IsPGroup 2 T)
    (hTidx : ¬ 2 ∣ T.index) {u : G} (hu : orderOf u = 2) : ∃ g : G, g⁻¹ * u * g ∈ T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Ts : Sylow 2 G := hT2.toSylow hTidx
  haveI : Finite (Sylow 2 G) := Sylow.finite_of_finiteIndex Ts
  have hu2 : IsPGroup 2 (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu]; norm_num)
  obtain ⟨Q, hQ⟩ := hu2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Ts Q
  have hmem : u ∈ ((g • Ts : Sylow 2 G) : Set G) := by
    rw [hg]
    exact hQ (Subgroup.mem_zpowers u)
  rw [Sylow.coe_smul] at hmem
  obtain ⟨y, hy, hyu⟩ := Set.mem_smul_set.1 hmem
  refine ⟨g, ?_⟩
  have hgy : g⁻¹ * u * g = y := by
    rw [← hyu, MulAut.smul_def, MulAut.conj_apply]
    group
  rw [hgy]
  exact hy

theorem exists_conj_mem_of_thompson [Finite G] {T U : Subgroup G} (hT2 : IsPGroup 2 T)
    (hTidx : ¬ 2 ∣ T.index) (hUT : U ≤ T) (hU2 : U.relIndex T = 2)
    (hO2 : CFSG.Quasithin.pResidualOf 2 (⊤ : Subgroup G) = ⊤) {t : G} (htT : t ∈ T)
    (ht : orderOf t = 2) : ∃ x : G, x⁻¹ * t * x ∈ U := by
  by_contra hno
  push Not at hno
  have hnot := CFSG.Quasithin.thompson_transfer_lemma_subgroup (X := ⊤) (P := T) (Q := U)
    le_top hT2 (by rw [Subgroup.relIndex_top_right]; exact hTidx) hUT hU2
    (Subgroup.mem_top t) ht (fun x _ => hno x)
  exact hnot (by rw [hO2]; exact Subgroup.mem_top t)

theorem pResidualOf_top_eq_top [Finite G] [IsSimpleGroup G] {x : G} (hx : Odd (orderOf x))
    (hx1 : x ≠ 1) : CFSG.Quasithin.pResidualOf 2 (⊤ : Subgroup G) = ⊤ := by
  haveI := CFSG.Quasithin.B2F.normal_pResidualOf_top (G := G)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.Quasithin.pResidualOf 2 (⊤ : Subgroup G))
    with h | h
  · exfalso
    have hmem := CFSG.Quasithin.B2F.mem_pResidualOf_top_of_odd (G := G) hx
    rw [h, Subgroup.mem_bot] at hmem
    exact hx1 hmem
  · exact h

theorem e0_ne_one_aux {H H₁ H₂ : Subgroup G} {e : Fin 6 → G} (hH : G23One H H₁ H₂)
    (hF : HFacts H H₁ H₂ e) : e 0 ≠ 1 := by
  intro h0
  have hc : Subgroup.centralizer ({1} : Set G) = ⊤ := by
    ext k
    simp [Subgroup.mem_centralizer_singleton_iff]
  have h := hF.cent₁
  rw [h0, hc, top_inf_eq, Subgroup.zpowers_one_eq_bot, bot_sup_eq] at h
  have h1 := card_H_of_G23One hH
  have h2 := card_H₂_of_G23One hH
  rw [h] at h1
  omega

theorem zOf_ne_one_aux {H H₁ H₂ : Subgroup G} {e : Fin 6 → G} (hH : G23One H H₁ H₂)
    (hF : HFacts H H₁ H₂ e) (hL : HLetters H H₁ H₂ e) (he01 : e 0 ≠ 1) : zOf e ≠ 1 := by
  intro hz1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have he0H₁ : e 0 ∈ H₁ := by
    rw [← hL.gen₁]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  have he0P : e 0 ∈ Psub e := Subgroup.subset_closure (Set.mem_insert _ _)
  have he03 : e 0 ^ 3 = 1 := hF.elem_P.2 _ he0P
  have hord3 : orderOf (e 0) = 3 := orderOf_eq_prime he03 he01
  obtain ⟨ψ⟩ := hH.iso_one
  have hdet : (-1 : Matrix (Fin 2) (Fin 2) (ZMod 3)).det = 1 := by
    rw [Matrix.det_fin_two]
    simp
  let c₀ : SL(2, ZMod 3) := ⟨-1, hdet⟩
  have hcen0 : ∀ g : SL(2, ZMod 3), g * c₀ = c₀ * g := by
    intro g
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    show (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) * (-1) = (-1) * (g : Matrix (Fin 2) (Fin 2) (ZMod 3))
    rw [Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, Matrix.one_mul]
  have hc0sq : c₀ * c₀ = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    show (-1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) * (-1) = 1
    rw [neg_one_mul, neg_neg]
  have hc0ne : c₀ ≠ 1 := by
    intro h
    have h00 := congrArg (fun A : SL(2, ZMod 3) => (A : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 0) h
    simp [c₀] at h00
    revert h00
    decide
  obtain ⟨c, hψc⟩ : ∃ c : ↥H₁, ψ c = c₀ := ⟨ψ.symm c₀, ψ.apply_symm_apply c₀⟩
  have hcen : ∀ x : ↥H₁, c * x = x * c := by
    intro x
    apply ψ.injective
    rw [map_mul, map_mul, hψc]
    exact (hcen0 (ψ x)).symm
  have hc2 : c ^ 2 = 1 := by
    apply ψ.injective
    rw [map_pow, hψc, map_one, sq, hc0sq]
  have hc1 : c ≠ 1 := by
    intro h
    apply hc0ne
    rw [← hψc, h, map_one]
  have hcG2 : (c : G) ^ 2 = 1 := by
    have := congrArg Subtype.val hc2
    simpa using this
  have hcG1 : (c : G) ≠ 1 := by
    intro h
    apply hc1
    exact Subtype.ext h
  have hcord : orderOf (c : G) = 2 := orderOf_eq_prime hcG2 hcG1
  have hcmem : (c : G) ∈ Subgroup.centralizer {e 0} ⊓ H₁ := by
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, c.2⟩
    have := congrArg Subtype.val (hcen ⟨e 0, he0H₁⟩)
    simpa using this
  rw [hF.centL₁, hz1] at hcmem
  simp only [Subgroup.zpowers_one_eq_bot, sup_bot_eq] at hcmem
  have hdvd := orderOf_dvd_of_mem_zpowers hcmem
  rw [hcord, hord3] at hdvd
  norm_num at hdvd

theorem oneClass_of_setup [Finite G] {T H H₁ H₂ M : Subgroup G} {e : Fin 6 → G}
    (hctx : G23Ctx G T H H₁ H₂ M) (hL : HLetters H H₁ H₂ e) (hF : HFacts H H₁ H₂ e)
    (hz : zOf e ∈ quasithinGenFitting M) : OneClass e := by
  haveI : IsSimpleGroup G := hctx.simple
  have hH : G23One H H₁ H₂ := hctx.one
  have hM : G23Two M := hctx.two
  obtain ⟨hT2, hTidxG⟩ : IsPGroup 2 T ∧ ¬ 2 ∣ T.index := hctx.sylow
  have hTH : T ≤ H := hctx.tH
  have hTM : T ≤ M := hctx.tM
  have hTidx : ¬ 2 ∣ (T.subgroupOf M).index := fun hd =>
    hTidxG (hd.trans (Subgroup.relIndex_dvd_index_of_le hTM))
  have hT64 : Nat.card T = 64 := G23Two.card_sylow hM hTM hT2 hTidx
  have hHc : Nat.card H = 576 := card_H_of_G23One hH
  have hKc : Nat.card ↥(H₁ ⊔ H₂) = 288 := by
    have := card_sup_mul_two_of_G23One hH
    omega
  have hTrel : T.relIndex H = 9 := by
    have h1 := Subgroup.relIndex_mul_card T H
    rw [inf_eq_left.2 hTH, hT64, hHc] at h1
    omega
  have hUT : T ⊓ (H₁ ⊔ H₂) ≤ T := inf_le_left
  have hUK : T ⊓ (H₁ ⊔ H₂) ≤ H₁ ⊔ H₂ := inf_le_right
  have hUH : T ⊓ (H₁ ⊔ H₂) ≤ H := hUT.trans hTH
  have hUc : Nat.card ↥(T ⊓ (H₁ ⊔ H₂)) = 32 := by
    have hr1 := Subgroup.relIndex_inf_le (H := T) (K := H₁ ⊔ H₂) (L := H)
    rw [hH.index, hTrel] at hr1
    have hr2 := Subgroup.relIndex_mul_card (T ⊓ (H₁ ⊔ H₂)) H
    rw [inf_eq_left.2 hUH, hHc] at hr2
    have hd1 := Subgroup.relIndex_mul_card (T ⊓ (H₁ ⊔ H₂)) T
    rw [inf_eq_left.2 hUT, hT64] at hd1
    have hd2 := Subgroup.relIndex_mul_card (T ⊓ (H₁ ⊔ H₂)) (H₁ ⊔ H₂)
    rw [inf_eq_left.2 hUK, hKc] at hd2
    have h1 : Nat.card ↥(T ⊓ (H₁ ⊔ H₂)) ∣ 64 := Dvd.intro_left _ hd1
    have h2 : Nat.card ↥(T ⊓ (H₁ ⊔ H₂)) ∣ 288 := Dvd.intro_left _ hd2
    have h3 : Nat.card ↥(T ⊓ (H₁ ⊔ H₂)) ∣ Nat.gcd 64 288 := Nat.dvd_gcd h1 h2
    have h4 : Nat.gcd 64 288 = 32 := by norm_num
    rw [h4] at h3
    have hle : Nat.card ↥(T ⊓ (H₁ ⊔ H₂)) ≤ 32 := Nat.le_of_dvd (by norm_num) h3
    have hge : 32 ≤ Nat.card ↥(T ⊓ (H₁ ⊔ H₂)) := by
      by_contra hlt
      push Not at hlt
      have hprod := Nat.mul_le_mul hr1 (show Nat.card ↥(T ⊓ (H₁ ⊔ H₂)) ≤ 31 by omega)
      linarith
    omega
  have hU2 : (T ⊓ (H₁ ⊔ H₂)).relIndex T = 2 := by
    have hd1 := Subgroup.relIndex_mul_card (T ⊓ (H₁ ⊔ H₂)) T
    rw [inf_eq_left.2 hUT, hT64, hUc] at hd1
    omega
  set V := quasithinGenFitting M
  have hV2 : IsElemAbelian 2 V := hM.elem
  have hVc : Nat.card ↥V = 8 := hM.card
  have hVT : V ≤ T := G23Two.fitting_le_T hM hTM hT2 hTidx
  have hVrel : V.relIndex T = 8 := by
    have h1 := Subgroup.relIndex_mul_card V T
    rw [inf_eq_left.2 hVT, hT64, hVc] at h1
    omega
  have hVU : 4 ≤ Nat.card ↥(V ⊓ (T ⊓ (H₁ ⊔ H₂))) := by
    have hr1 := Subgroup.relIndex_inf_le (H := V) (K := T ⊓ (H₁ ⊔ H₂)) (L := T)
    rw [hVrel, hU2] at hr1
    have hr2 := Subgroup.relIndex_mul_card (V ⊓ (T ⊓ (H₁ ⊔ H₂))) T
    rw [inf_eq_left.2 ((inf_le_right : V ⊓ (T ⊓ (H₁ ⊔ H₂)) ≤ T ⊓ (H₁ ⊔ H₂)).trans hUT), hT64] at hr2
    by_contra hlt
    push Not at hlt
    have hprod := Nat.mul_le_mul hr1 (show Nat.card ↥(V ⊓ (T ⊓ (H₁ ⊔ H₂))) ≤ 3 by omega)
    linarith
  have hz1 : zOf e ≠ 1 := zOf_ne_one_aux hH hF hL (e0_ne_one_aux hH hF)
  have he01 : e 0 ≠ 1 := e0_ne_one_aux hH hF
  have he0P : e 0 ∈ Psub e := Subgroup.subset_closure (Set.mem_insert _ _)
  have he03 : e 0 ^ 3 = 1 := hF.elem_P.2 _ he0P
  have hodd : Odd (orderOf (e 0)) := by
    rw [orderOf_eq_prime he03 he01]
    decide
  have hO2 : CFSG.Quasithin.pResidualOf 2 (⊤ : Subgroup G) = ⊤ :=
    pResidualOf_top_eq_top hodd he01
  have hu0 : ∃ u0 : G, u0 ∈ V ⊓ (T ⊓ (H₁ ⊔ H₂)) ∧ u0 ≠ 1 ∧ u0 ≠ zOf e := by
    by_contra hcon
    push Not at hcon
    classical
    have hinj : Function.Injective
        (fun v : ↥(V ⊓ (T ⊓ (H₁ ⊔ H₂))) => decide ((v : G) = zOf e)) := by
      rintro ⟨v, hv⟩ ⟨w, hw⟩ hvw
      simp only [decide_eq_decide] at hvw
      by_cases hvz : v = zOf e
      · have hwz : w = zOf e := hvw.1 hvz
        exact Subtype.ext (hvz.trans hwz.symm)
      · have hv1 : v = 1 := by
          by_contra h1
          exact hvz (hcon v hv h1)
        have hwz : ¬ w = zOf e := fun hw' => hvz (hvw.2 hw')
        have hw1 : w = 1 := by
          by_contra h1
          exact hwz (hcon w hw h1)
        exact Subtype.ext (hv1.trans hw1.symm)
    have hcard := Nat.card_le_card_of_injective _ hinj
    have hBool : Nat.card Bool = 2 := by simp
    rw [hBool] at hcard
    omega
  obtain ⟨u0, hu0VU, hu01, hu0z⟩ := hu0
  have hu0V : u0 ∈ V := (Subgroup.mem_inf.1 hu0VU).1
  have hu0U : u0 ∈ T ⊓ (H₁ ⊔ H₂) := (Subgroup.mem_inf.1 hu0VU).2
  have hu02 : orderOf u0 = 2 := orderOf_eq_prime (hV2.2 u0 hu0V) hu01
  have hzu0 : IsConj (zOf e) u0 := by
    obtain ⟨m, _, hm⟩ := G23Two.exists_conj_eq hM hz hz1 hu0V hu01
    exact isConj_iff.2 ⟨m, hm⟩
  have hUconj : ∀ v ∈ T ⊓ (H₁ ⊔ H₂), orderOf v = 2 → IsConj (zOf e) v := by
    intro v hvU hv2
    by_cases hvz : v = zOf e
    · subst hvz
      exact IsConj.refl _
    · obtain ⟨h, _, hhv⟩ := hF.invK u0 (hUK hu0U) hu02 hu0z v (hUK hvU) hv2 hvz
      exact hzu0.trans (isConj_iff.2 ⟨h, hhv⟩)
  have hTconj : ∀ t ∈ T, orderOf t = 2 → IsConj (zOf e) t := by
    intro t htT ht2
    obtain ⟨x, hx⟩ := exists_conj_mem_of_thompson hT2 hTidxG hUT hU2 hO2 htT ht2
    have hv2 : orderOf (x⁻¹ * t * x) = 2 := by
      rw [orderOf_conj_aux]
      exact ht2
    exact (hUconj _ hx hv2).trans (isConj_iff.2 ⟨x, by group⟩)
  intro u hu2
  obtain ⟨g, hg⟩ := exists_conj_mem_of_isPGroup hT2 hTidxG hu2
  have hg2 : orderOf (g⁻¹ * u * g) = 2 := by
    rw [orderOf_conj_aux]
    exact hu2
  exact (hTconj _ hg hg2).trans (isConj_iff.2 ⟨g, by group⟩)

theorem leafOneClass : LeafOneClass := by
  intro G _ _ T H H₁ H₂ M e h hF hz
  exact oneClass_of_setup h.ctx h.lets hF hz

end CFSG.GH74.QTGen4.Recog.G23.P7
