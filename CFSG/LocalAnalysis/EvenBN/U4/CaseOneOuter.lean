module

public import CFSG.LocalAnalysis.EvenBN.U4.Layers

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.EvenSmallLie.UnitarySix.YamadaD (oTwo le_oTwo)
open scoped MatrixGroups

section Transport

variable {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')

theorem mem_normalizer_iff_map_conj_eq {X : Subgroup G} {g : G} :
    g ∈ normalizer (X : Set G) ↔ X.map (MulAut.conj g).toMonoidHom = X := by
  rw [mem_normalizer_iff_conj_image_eq, ← SetLike.coe_set_eq (p := X.map _), Subgroup.coe_map]
  rfl

theorem map_conj_zpowers_of_commute {g t : G} (hgt : g * t = t * g) :
    (zpowers t).map (MulAut.conj g).toMonoidHom = zpowers t := by
  rw [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hgt,
    mul_inv_cancel_right]

theorem map_symm_map_mulEquiv (X : Subgroup G) :
    (X.map e.toMonoidHom).map e.symm.toMonoidHom = X := by
  ext x
  simp

theorem map_mulEquiv_inf (X Y : Subgroup G) :
    (X ⊓ Y).map e.toMonoidHom = X.map e.toMonoidHom ⊓ Y.map e.toMonoidHom :=
  Subgroup.map_inf _ _ _ e.injective

theorem map_mulEquiv_centralizer (S : Subgroup G) :
    (centralizer (S : Set G)).map e.toMonoidHom =
      centralizer ((S.map e.toMonoidHom : Subgroup G') : Set G') := by
  ext x
  rw [Subgroup.mem_map_equiv, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · rintro hx _ ⟨s, hs, rfl⟩
    have := congrArg e (hx s hs)
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
  · intro hx s hs
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hx (e s) ⟨s, hs, rfl⟩

theorem map_mulEquiv_centerIn (H : Subgroup G) :
    (CFSG.centerIn H).map e.toMonoidHom = CFSG.centerIn (H.map e.toMonoidHom) := by
  rw [CFSG.centerIn, CFSG.centerIn, map_mulEquiv_inf, map_mulEquiv_centralizer]

theorem map_mulEquiv_oTwo_le (X : Subgroup G) :
    (oTwo X).map e.toMonoidHom ≤ oTwo (X.map e.toMonoidHom) := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun P hP => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  refine le_oTwo (Subgroup.map_mono hP.1) ?_ (hP.2.2.map _)
  rw [← Subgroup.map_equiv_normalizer_eq]
  exact Subgroup.map_mono hP.2.1

theorem map_mulEquiv_oTwo (X : Subgroup G) :
    (oTwo X).map e.toMonoidHom = oTwo (X.map e.toMonoidHom) := by
  refine le_antisymm (map_mulEquiv_oTwo_le e X) ?_
  have h1 := map_mulEquiv_oTwo_le e.symm (X.map e.toMonoidHom)
  rw [map_symm_map_mulEquiv] at h1
  calc oTwo (X.map e.toMonoidHom)
      = ((oTwo (X.map e.toMonoidHom)).map e.symm.toMonoidHom).map e.toMonoidHom :=
        (map_symm_map_mulEquiv e.symm _).symm
    _ ≤ (oTwo X).map e.toMonoidHom := Subgroup.map_mono h1

theorem map_mulEquiv_pCoreIn (p : ℕ) (H : Subgroup G) :
    (CFSG.ABGTheoremB.pCoreIn p H).map e.toMonoidHom =
      CFSG.ABGTheoremB.pCoreIn p (H.map e.toMonoidHom) := by
  let e' : H ≃* H.map e.toMonoidHom := H.equivMapOfInjective e.toMonoidHom e.injective
  have hcomm : (H.map e.toMonoidHom).subtype.comp e'.toMonoidHom = e.toMonoidHom.comp H.subtype :=
    MonoidHom.ext fun _ => rfl
  rw [CFSG.ABGTheoremB.pCoreIn, CFSG.ABGTheoremB.pCoreIn, ← CFSG.pCore_map_iso p e',
    Subgroup.map_map, Subgroup.map_map, hcomm]

theorem map_mulEquiv_normalClosure_subgroupOf {N H : Subgroup G} {N' H' : Subgroup G'}
    (hN : N.map e.toMonoidHom = N') (hH : H.map e.toMonoidHom = H') :
    ((normalClosure ((N.subgroupOf H : Subgroup H) : Set H)).map H.subtype).map e.toMonoidHom =
      (normalClosure ((N'.subgroupOf H' : Subgroup H') : Set H')).map H'.subtype := by
  subst hN hH
  let e' : H ≃* H.map e.toMonoidHom := H.equivMapOfInjective e.toMonoidHom e.injective
  have hcomm : (H.map e.toMonoidHom).subtype.comp e'.toMonoidHom = e.toMonoidHom.comp H.subtype :=
    MonoidHom.ext fun _ => rfl
  have himg : e'.toMonoidHom '' ((N.subgroupOf H : Subgroup H) : Set H) =
      (((N.map e.toMonoidHom).subgroupOf (H.map e.toMonoidHom) : Subgroup _) : Set _) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨n, hn, hny⟩
      obtain ⟨k, hk, hky⟩ := y.2
      have hnk : n = k := e.injective (hny.trans hky.symm)
      exact ⟨⟨n, hnk ▸ hk⟩, hn, Subtype.ext hny⟩
  rw [Subgroup.map_map, ← hcomm, ← Subgroup.map_map,
    Subgroup.map_normalClosure _ e'.toMonoidHom e'.surjective, himg]

end Transport

section Model

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem miyamotoBarEquiv_mul_self : miyamotoBarEquiv h * miyamotoBarEquiv h = 1 :=
  RingEquiv.ext fun c => h.bar_bar c

theorem glAut_bar_bar (g : GL (Fin 4) K) :
    glAut (miyamotoBarEquiv h) (glAut (miyamotoBarEquiv h) g) = g := by
  rw [← MulAut.mul_apply, ← map_mul, miyamotoBarEquiv_mul_self, map_one, MulAut.one_apply]

theorem glAut_bar_eq_iff_mem_Cu {g : GL (Fin 4) K} :
    glAut (miyamotoBarEquiv h) g = g ↔ g ∈ miyamotoCu h := by
  rw [mem_miyamotoCu, ← Units.val_inj, coe_glAut]
  rfl

theorem glAut_mem_miyamotoUnipotent (φ : K ≃+* K) (za zb : Bool) :
    ∀ g ∈ miyamotoUnipotent h za zb, glAut φ g ∈ miyamotoUnipotent h za zb := by
  intro g hg
  obtain ⟨a, b, c, d, ha, hb0, hb, hd, rfl⟩ := (mem_miyamotoUnipotent h).1 hg
  rw [glAut_miyamotoXGL, miyamotoXGL_mem_miyamotoUnipotent]
  refine ⟨fun hz => by rw [ha hz, map_zero], fun hz => by rw [hb0 hz, map_zero],
    by rw [← map_bar_comm, hb], ?_⟩
  have := congrArg φ hd
  simpa [map_bar_comm h φ] using this

theorem glAut_mem_miyamotoI (φ : K ≃+* K) : ∀ g ∈ miyamotoI h, glAut φ g ∈ miyamotoI h := by
  rintro _ ⟨p, hp, rfl⟩
  have hp' := (miyamotoIParam_eq_one_iff h p).1 (MonoidHom.mem_ker.1 hp)
  rw [glAut_miyamotoIHom]
  refine (miyamotoIHom_mem_miyamotoI_iff h _).2 ((miyamotoIParam_eq_one_iff h _).2 ?_)
  simp only [Units.coe_map, MonoidHom.coe_ofClass]
  rw [← map_mul, ← map_bar_comm, hp']

theorem glAut_mem_miyamotoI1 (φ : K ≃+* K) : ∀ g ∈ miyamotoI1 h, glAut φ g ∈ miyamotoI1 h := by
  intro g hg
  obtain ⟨t, ht, rfl⟩ := (mem_miyamotoI1 h).1 hg
  refine (mem_miyamotoI1 h).2 ⟨Units.map (φ : K →* K) t, ?_, glAut_miyamotoIHom h φ (t, t)⟩
  simp only [Units.coe_map, MonoidHom.coe_ofClass]
  rw [← map_bar_comm, ht]

theorem glAut_mem_miyamotoI2 (φ : K ≃+* K) : ∀ g ∈ miyamotoI2 h, glAut φ g ∈ miyamotoI2 h := by
  rintro _ ⟨b, rfl⟩
  exact ⟨Units.map (φ : K →* K) b, (glAut_miyamotoI2Hom h φ b).symm⟩

omit h in
theorem glAut_miyamotoR1 (φ : K ≃+* K) : glAut φ (miyamotoR1 K) = miyamotoR1 K := by
  apply Units.ext
  rw [coe_glAut]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [miyamotoR1]

theorem glAut_mem_miyamotoZ (φ : K ≃+* K) : ∀ g ∈ miyamotoZ h, glAut φ g ∈ miyamotoZ h := by
  rintro _ ⟨d, hd, rfl⟩
  refine ⟨φ d, by rw [← map_bar_comm, hd], ?_⟩
  rw [glAut_miyamotoXGL, map_zero]

theorem miyamotoR1_mem_Cu : miyamotoR1 K ∈ miyamotoCu h :=
  (glAut_bar_eq_iff_mem_Cu h).1 (glAut_miyamotoR1 _)

theorem card_miyamotoRootA_inf_Cu :
    Nat.card (miyamotoRootA h ⊓ miyamotoCu h : Subgroup (GL (Fin 4) K)) = 2 ^ f := by
  rw [← h.card_fixedField]
  refine (Nat.card_eq_of_bijective (fun a : h.fixedField =>
    (⟨miyamotoXGL h a 0 0 0, ⟨a, rfl⟩, (miyamotoXGL_mem_Cu h).2
      ⟨(h.mem_fixedField).1 a.2, map_zero _, map_zero _, map_zero _⟩⟩ :
        (miyamotoRootA h ⊓ miyamotoCu h : Subgroup (GL (Fin 4) K))))
    ⟨fun a b e => ?_, fun x => ?_⟩).symm
  · exact Subtype.ext ((miyamotoXGL_inj h).1 (congrArg Subtype.val e)).1
  · obtain ⟨⟨a, ha⟩, hc⟩ := mem_inf.1 x.2
    rw [ha, miyamotoXGL_mem_Cu] at hc
    exact ⟨⟨a, (h.mem_fixedField).2 hc.1⟩, Subtype.ext ha.symm⟩

theorem exists_specialLinearGroup_bar_orderOf :
    ∃ m : SL(2, K), (∀ i j, h.bar ((m : Matrix (Fin 2) (Fin 2) K) i j) =
      (m : Matrix (Fin 2) (Fin 2) K) i j) ∧ orderOf m = 2 ^ f + 1 := by
  have : Finite K := h.finite
  have : CharP K 2 := h.charP
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥(Units.map h.normHom).ker)
  set β : Kˣ := (g : Kˣ) with hβ
  have hβo : orderOf β = 2 ^ f + 1 := by
    rw [hβ, Subgroup.orderOf_coe, hg, h.card_ker_normUnits_and_surjective.1]
  have hβN : (β : K) * h.bar β = 1 := (h.mem_ker_normUnits).1 g.2
  have hβ0 : (β : K) ≠ 0 := β.ne_zero
  have hinv : (β : K) * (β : K)⁻¹ = 1 := mul_inv_cancel₀ hβ0
  have hbar : h.bar (β : K) = (β : K)⁻¹ := eq_inv_of_mul_eq_one_right hβN
  set s : K := (β : K) + (β : K)⁻¹ with hs
  have hsbar : h.bar s = s := by rw [hs, map_add, map_inv₀, hbar, inv_inv, add_comm]
  have hs0 : s ≠ 0 := by
    intro hs0
    have hsq : β ^ 2 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      have e : (β : K) * s = 0 := by rw [hs0, mul_zero]
      rw [hs, mul_add, hinv] at e
      linear_combination e - h2
    have hdvd := orderOf_dvd_of_pow_eq_one hsq
    rw [hβo] at hdvd
    have h4 : 2 ≤ 2 ^ f := Nat.le_self_pow (by have := h.one_le; omega) 2
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hmdet : (!![0, 1; 1, s] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination (-1 : K) * h2
  have hDdet : (Matrix.diagonal ![(β : K), (β : K)⁻¹]).det = 1 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_two]
    simp
  have hPdet : (!![1, 1; (β : K), (β : K)⁻¹] : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    have e : (1 : K) * (β : K)⁻¹ - 1 * β = s := by
      rw [hs]
      linear_combination (-(β : K)) * h2
    rw [e]
    exact hs0
  let m : SL(2, K) := ⟨!![0, 1; 1, s], hmdet⟩
  let D : SL(2, K) := ⟨Matrix.diagonal ![(β : K), (β : K)⁻¹], hDdet⟩
  let P : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hPdet
  have key : Matrix.SpecialLinearGroup.toGL m * P = P * Matrix.SpecialLinearGroup.toGL D := by
    apply Units.ext
    change !![0, 1; 1, s] * !![1, 1; (β : K), (β : K)⁻¹] =
      !![1, 1; (β : K), (β : K)⁻¹] * Matrix.diagonal ![(β : K), (β : K)⁻¹]
    ext i j
    rw [Matrix.mul_diagonal]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination (β : K) * hs + hinv + h2
    · linear_combination (β : K)⁻¹ * hs + hinv + h2
  have hconj : Matrix.SpecialLinearGroup.toGL m =
      MulAut.conj P (Matrix.SpecialLinearGroup.toGL D) := by
    rw [MulAut.conj_apply, ← key, mul_inv_cancel_right]
  have hmD : orderOf m = orderOf D := by
    rw [← orderOf_injective Matrix.SpecialLinearGroup.toGL
      Matrix.SpecialLinearGroup.toGL_injective m, hconj, MulEquiv.orderOf_eq,
      orderOf_injective Matrix.SpecialLinearGroup.toGL Matrix.SpecialLinearGroup.toGL_injective D]
  have hDo : orderOf D = orderOf β := by
    refine orderOf_eq_orderOf_iff.2 fun n => ?_
    have hDc : ((D : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
        Matrix.diagonal ![(β : K), (β : K)⁻¹] := rfl
    rw [Matrix.SpecialLinearGroup.ext_iff, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one]
    simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, hDc,
      Matrix.diagonal_pow]
    simp [Fin.forall_fin_two, Matrix.one_apply, Matrix.diagonal_apply, inv_pow]
  refine ⟨m, fun i j => ?_, by rw [hmD, hDo, hβo]⟩
  fin_cases i <;> fin_cases j <;> simp [m, hsbar]

end Model

section Ambient

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} {G : Type} [Group G]
  {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {u : G} (hu : u ∈ normalizer (L : Set G))
  (hact : miyamotoAct h L η ⟨u, hu⟩ = miyamotoFieldAut h (miyamotoBarEquiv h))
include hact

theorem conj_symm_of_act_eq_bar (g : gramSU h (miyamotoJ4 K)) :
    u * (η.symm g : G) * u⁻¹ = (η.symm (miyamotoFieldAut h (miyamotoBarEquiv h) g) : G) := by
  rw [← hact, coe_symm_miyamotoAct_apply]

theorem commute_symm_iff_of_act_eq_bar (g : gramSU h (miyamotoJ4 K)) :
    u * (η.symm g : G) = (η.symm g : G) * u ↔ (g : GL (Fin 4) K) ∈ miyamotoCu h := by
  rw [← mul_inv_eq_iff_eq_mul, conj_symm_of_act_eq_bar hu hact, SetLike.coe_eq_coe,
    EmbeddingLike.apply_eq_iff_eq, ← SetLike.coe_eq_coe, coe_miyamotoFieldAut_apply,
    glAut_bar_eq_iff_mem_Cu]

theorem miyamotoPull_inf_centralizer_of_act_eq_bar (M : Subgroup (GL (Fin 4) K)) :
    miyamotoPull h L η M ⊓ centralizer ({u} : Set G) =
      miyamotoPull h L η (M ⊓ miyamotoCu h) := by
  ext x
  rw [mem_inf, mem_miyamotoPull, mem_miyamotoPull, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨⟨g, hg, rfl⟩, hc⟩
    exact ⟨g, ⟨hg, (commute_symm_iff_of_act_eq_bar hu hact g).1 hc.symm⟩, rfl⟩
  · rintro ⟨g, ⟨hg, hc⟩, rfl⟩
    exact ⟨⟨g, hg, rfl⟩, ((commute_symm_iff_of_act_eq_bar hu hact g).2 hc).symm⟩

theorem mem_normalizer_miyamotoPull_of_act_eq_bar {M : Subgroup (GL (Fin 4) K)}
    (hM : ∀ g ∈ M, glAut (miyamotoBarEquiv h) g ∈ M) :
    u ∈ normalizer (miyamotoPull h L η M : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨g, hg, rfl⟩ := (mem_miyamotoPull h L η).1 hx
    rw [conj_symm_of_act_eq_bar hu hact]
    exact (symm_mem_miyamotoPull_iff h L η).2 (hM _ hg)
  · intro hx
    obtain ⟨g, hg, hgx⟩ := (mem_miyamotoPull h L η).1 hx
    have e := conj_symm_of_act_eq_bar hu hact (miyamotoFieldAut h (miyamotoBarEquiv h) g)
    have hbb : miyamotoFieldAut h (miyamotoBarEquiv h)
        (miyamotoFieldAut h (miyamotoBarEquiv h) g) = g :=
      Subtype.ext (by rw [coe_miyamotoFieldAut_apply, coe_miyamotoFieldAut_apply, glAut_bar_bar])
    rw [hbb, hgx] at e
    rw [← mul_left_cancel (mul_right_cancel e)]
    exact (symm_mem_miyamotoPull_iff h L η).2 (hM _ hg)

theorem map_conj_miyamotoPull_of_act_eq_bar {M : Subgroup (GL (Fin 4) K)}
    (hM : ∀ g ∈ M, glAut (miyamotoBarEquiv h) g ∈ M) :
    (miyamotoPull h L η M).map (MulAut.conj u).toMonoidHom = miyamotoPull h L η M :=
  mem_normalizer_iff_map_conj_eq.1 (mem_normalizer_miyamotoPull_of_act_eq_bar hu hact hM)

theorem mul_miyamotoR1G_of_act_eq_bar : u * miyamotoR1G h L η = miyamotoR1G h L η * u :=
  (commute_symm_iff_of_act_eq_bar hu hact _).2 (miyamotoR1_mem_Cu h)

theorem conj_miyamotoDHom_of_act_eq_bar (α : Kˣ) :
    u * miyamotoDHom h L η α * u⁻¹ = miyamotoDHom h L η α ^ (2 ^ f) := by
  have hα : Units.map (miyamotoBarEquiv h : K →* K) α = α ^ 2 ^ f :=
    Units.ext (by simp [UnitaryFieldData.bar_apply])
  have e : miyamotoFieldAut h (miyamotoBarEquiv h) (miyamotoDHomSU h α) =
      miyamotoDHomSU h (α ^ 2 ^ f) := by
    apply Subtype.ext
    rw [coe_miyamotoFieldAut_apply, coe_miyamotoDHomSU, coe_miyamotoDHomSU, glAut_miyamotoIHom]
    simp only [map_inv, hα]
  rw [← map_pow]
  change u * ((η.symm (miyamotoDHomSU h α) : L) : G) * u⁻¹ =
    ((η.symm (miyamotoDHomSU h (α ^ 2 ^ f)) : L) : G)
  rw [← e]
  exact conj_symm_of_act_eq_bar hu hact _

theorem card_rootA_inf_centralizer_of_act_eq_bar :
    Nat.card (miyamotoPull h L η (miyamotoRootA h) ⊓ centralizer ({u} : Set G) : Subgroup G) =
      2 ^ f := by
  rw [miyamotoPull_inf_centralizer_of_act_eq_bar hu hact, card_miyamotoPull h L η
    (inf_le_left.trans ((miyamotoRootA_le_A2 h).trans (miyamotoUnipotent_le_SU h false true))),
    card_miyamotoRootA_inf_Cu]

theorem exists_mem_N1G_orderOf_of_act_eq_bar :
    ∃ n ∈ miyamotoN1G h L η, u * n = n * u ∧ orderOf n = 2 ^ f + 1 := by
  have : CharP K 2 := h.charP
  obtain ⟨m, hmF, hm⟩ := exists_specialLinearGroup_bar_orderOf h
  have hmem := miyamotoN1Hom_mem_N1_inf_Cu h hmF
  refine ⟨((η.symm ⟨miyamotoN1Hom h m, miyamotoN1_le_gramSU h hmem.1⟩ : L) : G),
    (symm_mem_miyamotoPull_iff h L η).2 hmem.1, (commute_symm_iff_of_act_eq_bar hu hact _).2 hmem.2,
    ?_⟩
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk,
    orderOf_injective _ (miyamotoN1Hom_injective h), hm]

end Ambient

theorem t_mul_mul_t_of_commute {G : Type*} [Group G] {t u : G} (hut : u * t = t * u) :
    t * u * t = t * (t * u) := by
  rw [mul_assoc, hut]

section Local

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} {G : Type} [Group G]
  {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t u : G}
  (hu : u ∈ normalizer (L : Set G))
  (hact : miyamotoAct h L η ⟨u, hu⟩ = miyamotoFieldAut h (miyamotoBarEquiv h))
  (hut : u * t = t * u)
include hact hut

theorem mem_normalizer_B1_of_act_eq_bar : u ∈ normalizer (miyamotoB1 h L η t : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq, miyamotoB1, Subgroup.map_sup,
    map_conj_zpowers_of_commute hut,
    map_conj_miyamotoPull_of_act_eq_bar hu hact (glAut_mem_miyamotoUnipotent h _ true false)]

theorem mem_normalizer_D1_of_act_eq_bar : u ∈ normalizer (miyamotoD1 h L η t : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq, miyamotoD1, map_mulEquiv_pCoreIn,
    Subgroup.map_equiv_normalizer_eq,
    mem_normalizer_iff_map_conj_eq.1 (mem_normalizer_B1_of_act_eq_bar hu hact hut)]

theorem mem_normalizer_F1G_of_act_eq_bar : u ∈ normalizer (miyamotoF1G h L η t : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq, miyamotoF1G, Subgroup.map_sup, Subgroup.map_commutator,
    map_conj_miyamotoPull_of_act_eq_bar hu hact (glAut_mem_miyamotoI1 h _),
    mem_normalizer_iff_map_conj_eq.1 (mem_normalizer_D1_of_act_eq_bar hu hact hut),
    map_conj_miyamotoPull_of_act_eq_bar hu hact (glAut_mem_miyamotoUnipotent h _ true false)]

theorem mem_normalizer_H1G_of_act_eq_bar : u ∈ normalizer (miyamotoH1G h L η t : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq, miyamotoH1G, map_mulEquiv_inf,
    Subgroup.map_equiv_normalizer_eq, map_mulEquiv_centralizer,
    mem_normalizer_iff_map_conj_eq.1 (mem_normalizer_F1G_of_act_eq_bar hu hact hut),
    map_conj_miyamotoPull_of_act_eq_bar hu hact (glAut_mem_miyamotoI1 h _)]

theorem mem_normalizer_M1G_of_act_eq_bar : u ∈ normalizer (miyamotoM1G h L η t : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq, miyamotoM1G]
  exact map_mulEquiv_normalClosure_subgroupOf _
    (map_conj_miyamotoPull_of_act_eq_bar hu hact fun g hg => glAut_mem_miyamotoN1 h _ hg)
    (mem_normalizer_iff_map_conj_eq.1 (mem_normalizer_H1G_of_act_eq_bar hu hact hut))

end Local

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

theorem t_mul_mem_normalizer (hS : Setting h L η t Q T) {u : G}
    (hu : u ∈ normalizer (L : Set G)) : t * u ∈ normalizer (L : Set G) :=
  mul_mem (hS.centralizer_le_normalizer hS.t_mem_centralizer) hu

theorem act_t_mul_of_act_eq_bar (hS : Setting h L η t Q T) {u : G}
    (hu : u ∈ normalizer (L : Set G))
    (hact : miyamotoAct h L η ⟨u, hu⟩ = miyamotoFieldAut h (miyamotoBarEquiv h)) :
    miyamotoAct h L η ⟨t * u, hS.t_mul_mem_normalizer hu⟩ =
      miyamotoFieldAut h (miyamotoBarEquiv h) := by
  have e : (⟨t * u, hS.t_mul_mem_normalizer hu⟩ : normalizer (L : Set G)) =
      ⟨t, hS.centralizer_le_normalizer hS.t_mem_centralizer⟩ * ⟨u, hu⟩ := rfl
  rw [e, map_mul, hact, (miyamotoAct_eq_one_iff h L η
    ⟨t, hS.centralizer_le_normalizer hS.t_mem_centralizer⟩).2 hS.t_mem, one_mul]

theorem t_mul_mul_self (hS : Setting h L η t Q T) {u : G} (hut : u * t = t * u) :
    t * u * (t * u) = u * u := by
  calc t * u * (t * u) = t * (u * t) * u := by group
    _ = t * t * (u * u) := by rw [hut]; group
    _ = u * u := by rw [hS.t_mul_t, one_mul]

section Outer

variable {u : G} (hu : u ∈ normalizer (L : Set G))
  (hact : miyamotoAct h L η ⟨u, hu⟩ = miyamotoFieldAut h (miyamotoBarEquiv h))
  (hut : u * t = t * u)
include hact hut

theorem mem_normalizer_Q_of_act_eq_bar (hS : Setting h L η t Q T) :
    u ∈ normalizer (Q : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq, hS.Q_eq, Subgroup.map_sup,
    map_conj_miyamotoPull_of_act_eq_bar hu hact (glAut_mem_miyamotoUnipotent h _ false false),
    map_conj_zpowers_of_commute hut]

theorem mem_normalizer_M0_of_act_eq_bar (hS : Setting h L η t Q T) :
    u ∈ normalizer (miyamotoM0 Q : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq, miyamotoM0, map_mulEquiv_pCoreIn,
    Subgroup.map_equiv_normalizer_eq, map_mulEquiv_centerIn,
    mem_normalizer_iff_map_conj_eq.1 (hS.mem_normalizer_Q_of_act_eq_bar hu hact hut)]

theorem mem_normalizer_S_of_act_eq_bar (hS : Setting h L η t Q T) :
    u ∈ normalizer (miyamotoS h L η t Q : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq, miyamotoS, map_mulEquiv_oTwo,
    Subgroup.map_equiv_normalizer_eq, Subgroup.map_sup,
    mem_normalizer_iff_map_conj_eq.1 (mem_normalizer_F1G_of_act_eq_bar hu hact hut),
    mem_normalizer_iff_map_conj_eq.1 (hS.mem_normalizer_Q_of_act_eq_bar hu hact hut)]

theorem mem_normalizer_RG_of_act_eq_bar (hS : Setting h L η t Q T) :
    u ∈ normalizer (miyamotoRG h L η t Q : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq, miyamotoRG, Subgroup.map_sup, Subgroup.map_commutator,
    Subgroup.map_sup, map_conj_miyamotoPull_of_act_eq_bar hu hact (glAut_mem_miyamotoI h _),
    mem_normalizer_iff_map_conj_eq.1 (hS.mem_normalizer_S_of_act_eq_bar hu hact hut),
    mem_normalizer_iff_map_conj_eq.1 (mem_normalizer_F1G_of_act_eq_bar hu hact hut),
    map_conj_miyamotoPull_of_act_eq_bar hu hact (glAut_mem_miyamotoUnipotent h _ false false)]

theorem mem_normalizer_YG_of_act_eq_bar (hS : Setting h L η t Q T) :
    u ∈ normalizer (miyamotoYG h L η Q : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq, miyamotoYG, map_mulEquiv_inf, map_mulEquiv_centralizer,
    mem_normalizer_iff_map_conj_eq.1 (hS.mem_normalizer_M0_of_act_eq_bar hu hact hut),
    map_conj_miyamotoPull_of_act_eq_bar hu hact (glAut_mem_miyamotoUnipotent h _ false true)]

theorem mem_normalizer_EG_of_act_eq_bar (hS : Setting h L η t Q T) :
    u ∈ normalizer (miyamotoEG h L η Q : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq, miyamotoEG, Subgroup.map_sup, Subgroup.map_commutator,
    map_conj_miyamotoPull_of_act_eq_bar hu hact (glAut_mem_miyamotoI2 h _),
    mem_normalizer_iff_map_conj_eq.1 (hS.mem_normalizer_YG_of_act_eq_bar hu hact hut),
    map_conj_miyamotoPull_of_act_eq_bar hu hact (glAut_mem_miyamotoZ h _)]

theorem mem_normalizer_W_of_act_eq_bar (hS : Setting h L η t Q T) :
    u ∈ normalizer ((miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G) :
      Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq, map_mulEquiv_inf, map_mulEquiv_centralizer,
    mem_normalizer_iff_map_conj_eq.1 (hS.mem_normalizer_RG_of_act_eq_bar hu hact hut),
    map_conj_miyamotoPull_of_act_eq_bar hu hact (glAut_mem_miyamotoI1 h _)]

end Outer

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
