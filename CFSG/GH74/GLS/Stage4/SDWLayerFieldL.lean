module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3
public import CFSG.GH74.GLS.Stage4.SDWLayerAbs

public section

open Subgroup CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.Stage4.Rest.FieldL3

section Matrices

variable {F : Type} [Field F]

theorem mem_statedSL_iff (A : GL (Fin 2) F) :
    A ∈ StatedSL 2 F ↔ (A : Matrix (Fin 2) (Fin 2) F).det = 1 :=
  CFSG.Open.StatedAPI.mem_statedSL_iff

theorem statedSL_eq_ker_det :
    StatedSL 2 F = (Matrix.GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ).ker :=
  CFSG.Open.StatedAPI.statedSL_eq_ker_det 2 F

instance statedSL_normal : (StatedSL 2 F).Normal := by
  rw [statedSL_eq_ker_det]
  infer_instance

theorem commutator_mem_statedSL (x y : GL (Fin 2) F) : ⁅x, y⁆ ∈ StatedSL 2 F := by
  rw [statedSL_eq_ker_det, MonoidHom.mem_ker, map_commutatorElement]
  simp [commutatorElement_def]

theorem exists_scalar_of_commute {g : GL (Fin 2) F}
    (hg : ∀ s ∈ StatedSL 2 F, g * s = s * g) :
    ∃ c : F, Matrix.scalar (Fin 2) c = (g : Matrix (Fin 2) (Fin 2) F) := by
  refine Matrix.mem_range_scalar_of_commute_transvectionStruct ?_
  intro t
  have hs : (Matrix.SpecialLinearGroup.toGL t.toSpecialLinearGroup) ∈ StatedSL 2 F := by
    rw [mem_statedSL_iff]
    exact t.toSpecialLinearGroup.prop
  have h := congrArg (fun x : GL (Fin 2) F => (x : Matrix (Fin 2) (Fin 2) F)) (hg _ hs)
  simp at h
  exact h.symm

theorem sq_eq_one_of_central {t : GL (Fin 2) F} (ht : t ∈ StatedSL 2 F)
    (hc : ∀ s ∈ StatedSL 2 F, t * s = s * t) : t * t = 1 := by
  obtain ⟨c, hc⟩ := exists_scalar_of_commute hc
  have hdet := (mem_statedSL_iff t).1 ht
  rw [← hc, Matrix.scalar_apply, Matrix.det_diagonal] at hdet
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
  apply Units.ext
  rw [Units.val_mul, ← hc, ← map_mul, Units.val_one]
  have : c * c = 1 := by rw [← pow_two]; exact hdet
  rw [this, map_one]

theorem centralizes_of_commute_statedSL (g h : GL (Fin 2) F)
    (hg : ∀ s ∈ StatedSL 2 F, g * s = s * g) (_hh : ∀ s ∈ StatedSL 2 F, h * s = s * h) :
    g * h = h * g := by
  obtain ⟨c, hc⟩ := exists_scalar_of_commute hg
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ← hc]
  exact Matrix.scalar_commute c (fun r => Commute.all _ _) _

theorem toGL_mem_statedSL (g : SL(2, F)) : Matrix.SpecialLinearGroup.toGL g ∈ StatedSL 2 F := by
  rw [mem_statedSL_iff]
  exact g.prop

theorem field_cond_of_four_le_card [Finite F] (hF : 4 ≤ Nat.card F) :
    ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
  obtain ⟨x, hx⟩ : IsCyclic Fˣ := by infer_instance
  refine ⟨x, Units.ne_zero x, fun h ↦ ?_⟩
  grw [Nat.card_eq_card_units_add_one F, ← orderOf_eq_card_of_forall_mem_zpowers hx,
    orderOf_le_of_pow_eq_one zero_lt_two (Units.ext <| by simpa using h)] at hF
  omega

theorem statedSL_perfect [Finite F] (hF : 4 ≤ Nat.card F) :
    ⁅StatedSL 2 F, StatedSL 2 F⁆ = StatedSL 2 F := by
  obtain ⟨a, ha, hasq⟩ := field_cond_of_four_le_card hF
  have hP : Group.IsPerfect SL(2, F) := ⟨Matrix.SL2.commutator_eq_top ha hasq⟩
  have h2 : Group.IsPerfect (StatedSL 2 F) :=
    Group.IsPerfect.ofSurjective (f := (specialLinearGroupEquivStatedSL 2 F).toMonoidHom)
      (specialLinearGroupEquivStatedSL 2 F).surjective
  exact Subgroup.isPerfect_iff.1 h2

theorem comm_mul_central_left {G : Type*} [Group G] {g h c : G} (hc : c ∈ center G) :
    ⁅g * c, h⁆ = ⁅g, h⁆ := by
  have hch : c * h * c⁻¹ = h := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_center_iff.1 hc h).symm
  rw [commutatorElement_def, commutatorElement_def]
  calc g * c * h * (g * c)⁻¹ * h⁻¹ = g * (c * h * c⁻¹) * g⁻¹ * h⁻¹ := by group
    _ = g * h * g⁻¹ * h⁻¹ := by rw [hch]

theorem comm_mul_central_right {G : Type*} [Group G] {g h c : G} (hc : c ∈ center G) :
    ⁅g, h * c⁆ = ⁅g, h⁆ := by
  have hcg : c * g⁻¹ * c⁻¹ = g⁻¹ := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_center_iff.1 hc g⁻¹).symm
  rw [commutatorElement_def, commutatorElement_def]
  calc g * (h * c) * g⁻¹ * (h * c)⁻¹ = g * h * (c * g⁻¹ * c⁻¹) * h⁻¹ := by group
    _ = g * h * g⁻¹ * h⁻¹ := by rw [hcg]

theorem statedSL_hq [Finite F] (hF : 4 ≤ Nat.card F) (T : Subgroup (GL (Fin 2) F))
    (hTS : T ≤ StatedSL 2 F) (hTn : ∀ s ∈ StatedSL 2 F, ∀ t ∈ T, s * t * s⁻¹ ∈ T) :
    (∀ t ∈ T, ∀ s ∈ StatedSL 2 F, t * s = s * t) ∨ T = StatedSL 2 F := by
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF
  let ψ : SL(2, F) →* GL (Fin 2) F := Matrix.SpecialLinearGroup.toGL
  let T₀ : Subgroup SL(2, F) := T.comap ψ
  have hT₀n : T₀.Normal := ⟨fun a ha g => by
    show ψ (g * a * g⁻¹) ∈ T
    rw [map_mul, map_mul, map_inv]
    exact hTn _ (toGL_mem_statedSL g) _ ha⟩
  let π : SL(2, F) →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    QuotientGroup.mk' (center SL(2, F))
  have : (T₀.map π).Normal := hT₀n.map π (QuotientGroup.mk'_surjective _)
  rcases Subgroup.Normal.eq_bot_or_eq_top (T₀.map π) with hbot | htop
  · left
    intro t ht s hs
    obtain ⟨a, rfl⟩ : t ∈ ψ.range := by rw [← statedSL_eq_range_toGL]; exact hTS ht
    obtain ⟨b, rfl⟩ : s ∈ ψ.range := by rw [← statedSL_eq_range_toGL]; exact hs
    have ha : a ∈ T₀ := ht
    have : π a ∈ T₀.map π := ⟨a, ha, rfl⟩
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 this b).symm]
  · right
    apply le_antisymm hTS
    intro s hs
    obtain ⟨b, rfl⟩ : s ∈ ψ.range := by rw [← statedSL_eq_range_toGL]; exact hs
    show b ∈ T₀
    have key : ∀ a : SL(2, F), ∃ t ∈ T₀, ∃ c ∈ center SL(2, F), a = t * c := by
      intro a
      have : π a ∈ T₀.map π := by rw [htop]; trivial
      obtain ⟨t, ht, hta⟩ := this
      refine ⟨t, ht, t⁻¹ * a, ?_, by group⟩
      exact QuotientGroup.eq.1 hta
    have hcomm : commutator SL(2, F) ≤ T₀ := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ a' _
      obtain ⟨t₁, ht₁, c₁, hc₁, rfl⟩ := key a
      obtain ⟨t₂, ht₂, c₂, hc₂, rfl⟩ := key a'
      rw [comm_mul_central_left hc₁, comm_mul_central_right hc₂, commutatorElement_def]
      exact T₀.mul_mem (T₀.mul_mem (T₀.mul_mem ht₁ ht₂) (T₀.inv_mem ht₁)) (T₀.inv_mem ht₂)
    obtain ⟨a, ha, hasq⟩ := field_cond_of_four_le_card hF
    have hperf : commutator SL(2, F) = ⊤ := Matrix.SL2.commutator_eq_top ha hasq
    have : b ∈ commutator SL(2, F) := by rw [hperf]; trivial
    exact hcomm this

theorem card_statedSL2 [Finite F] :
    Nat.card (StatedSL 2 F) = Nat.card F * (Nat.card F ^ 2 - 1) :=
  CFSG.Open.StatedAPI.card_statedSL_two F

theorem card_GL2 [Finite F] :
    Nat.card (GL (Fin 2) F) = (Nat.card F ^ 2 - 1) * (Nat.card F ^ 2 - Nat.card F) := by
  have := Fintype.ofFinite F
  rw [Matrix.card_GL_field, Fin.prod_univ_two, Nat.card_eq_fintype_card (α := F)]
  simp

theorem statedSL_nonabelian : ∃ a ∈ StatedSL 2 F, ∃ b ∈ StatedSL 2 F, a * b ≠ b * a := by
  let A : SL(2, F) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩
  let B : SL(2, F) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two_of]⟩
  refine ⟨Matrix.SpecialLinearGroup.toGL A, toGL_mem_statedSL A,
    Matrix.SpecialLinearGroup.toGL B, toGL_mem_statedSL B, ?_⟩
  intro h
  have h' := congrArg (fun x : GL (Fin 2) F => (x : Matrix (Fin 2) (Fin 2) F) 0 0) h
  have key : (!![1, 1; 0, 1] * !![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) 0 0 =
      (!![1, 0; 1, 1] * !![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) 0 0 := h'
  simp [Matrix.mul_apply, Fin.sum_univ_two] at key

theorem statedSL_involution_central (h2 : (2 : F) ≠ 0) {t : GL (Fin 2) F}
    (ht : t ∈ StatedSL 2 F) (htt : t * t = 1) : ∀ s ∈ StatedSL 2 F, t * s = s * t := by
  have hdet := (mem_statedSL_iff t).1 ht
  have hm : (t : Matrix (Fin 2) (Fin 2) F) * t = 1 := by
    have := congrArg (fun x : GL (Fin 2) F => (x : Matrix (Fin 2) (Fin 2) F)) htt
    simpa using this
  have e00 := congrFun (congrFun hm 0) 0
  have e01 := congrFun (congrFun hm 0) 1
  have e10 := congrFun (congrFun hm 1) 0
  have e11 := congrFun (congrFun hm 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq, Matrix.one_apply_ne,
    ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true] at e00 e01 e10 e11
  rw [Matrix.det_fin_two] at hdet
  obtain ⟨a, ha⟩ : ∃ a, (t : Matrix (Fin 2) (Fin 2) F) 0 0 = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, (t : Matrix (Fin 2) (Fin 2) F) 0 1 = b := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, (t : Matrix (Fin 2) (Fin 2) F) 1 0 = c := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, (t : Matrix (Fin 2) (Fin 2) F) 1 1 = d := ⟨_, rfl⟩
  simp only [ha, hb, hc, hd] at e00 e01 e10 e11 hdet
  have hscalar : (t : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) a := by
    by_cases had : a + d = 0
    · exfalso
      apply h2
      have hd' : d = -a := by linear_combination had
      rw [hd'] at hdet
      linear_combination -hdet - e00
    · have hb0 : b = 0 := by
        have : b * (a + d) = 0 := by linear_combination e01
        exact (mul_eq_zero.1 this).resolve_right had
      have hc0 : c = 0 := by
        have : c * (a + d) = 0 := by linear_combination e10
        exact (mul_eq_zero.1 this).resolve_right had
      have haa : a * a = 1 := by rw [hb0] at e00; linear_combination e00
      have hdd : d = a := by
        have h1 : a * d = 1 := by rw [hb0] at hdet; linear_combination hdet
        have ha0 : a ≠ 0 := fun h0 => by rw [h0] at haa; simp at haa
        apply mul_left_cancel₀ ha0
        rw [h1, haa]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, ha, hb, hc, hd, hb0, hc0, hdd]
  intro s _
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hscalar]
  exact Matrix.scalar_commute a (fun r => Commute.all _ _) _

end Matrices

section Abstract

variable {Γ Q : Type*} [Group Γ] [Group Q]

theorem comap_perfect (π : Γ →* Q) (hπ : Function.Surjective π) (M₀ : Subgroup Q)
    (h : ⁅M₀, M₀⁆ = M₀) : ⁅M₀.comap π, M₀.comap π⁆ ⊔ π.ker = M₀.comap π := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rw [Subgroup.commutator_le]
      intro a ha b hb
      exact (M₀.comap π).mul_mem ((M₀.comap π).mul_mem ((M₀.comap π).mul_mem ha hb)
        ((M₀.comap π).inv_mem ha)) ((M₀.comap π).inv_mem hb)
    · intro x hx
      rw [MonoidHom.mem_ker] at hx
      show π x ∈ M₀
      rw [hx]
      exact M₀.one_mem
  · intro x hx
    have hx' : π x ∈ M₀ := hx
    rw [← h] at hx'
    have hmap : (M₀.comap π).map π = M₀ := Subgroup.map_comap_eq_self_of_surjective hπ M₀
    rw [← hmap, ← Subgroup.map_commutator] at hx'
    obtain ⟨y, hy, hyx⟩ := hx'
    have hker : y⁻¹ * x ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
    have : x = y * (y⁻¹ * x) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hy hker

theorem nonabelian_comap (π : Γ →* Q) (hπ : Function.Surjective π) {M₀ : Subgroup Q}
    (h : ∃ x ∈ M₀, ∃ y ∈ M₀, x * y ≠ y * x) :
    ∃ a ∈ M₀.comap π, ∃ b ∈ M₀.comap π, a * b ≠ b * a := by
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  obtain ⟨a, rfl⟩ := hπ x
  obtain ⟨b, rfl⟩ := hπ y
  exact ⟨a, hx, b, hy, fun hab => hxy (by rw [← map_mul, ← map_mul, hab])⟩

theorem card_comap_mk (N : Subgroup Γ) [N.Normal] (M₀ : Subgroup (Γ ⧸ N)) :
    Nat.card (M₀.comap (QuotientGroup.mk' N)) = Nat.card N * Nat.card M₀ :=
  QuotientGroup.card_preimage_mk N (M₀ : Set (Γ ⧸ N))

theorem exists_normal_model {E : Type} [Group E] {C K : Subgroup E} (hKC : K ≤ C)
    (Φ : ↥C ≃* Q) (hCK : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K) :
    ∃ M₀ : Subgroup Q, M₀.Normal ∧ Nonempty (↥K ≃* ↥M₀) := by
  refine ⟨(K.subgroupOf C).map Φ.toMonoidHom, ?_,
    ⟨(Subgroup.subgroupOfEquivOfLe hKC).symm.trans
      (Subgroup.equivMapOfInjective _ Φ.toMonoidHom Φ.injective)⟩⟩
  constructor
  rintro _ ⟨x, hx, rfl⟩ g
  obtain ⟨c, rfl⟩ := Φ.surjective g
  refine ⟨c * x * c⁻¹, ?_, by simp⟩
  show ((c * x * c⁻¹ : ↥C) : E) ∈ K
  simpa using hCK c c.2 x hx

end Abstract

section Layer

variable {F : Type} [Field F] [Finite F]

theorem inf_eq_bot_of_card (hF : 4 ≤ Nat.card F) (N : Subgroup (GL (Fin 2) F)) [N.Normal]
    (hN : Nat.card N = 1 ∨ Nat.card N = 3) : N ⊓ StatedSL 2 F = ⊥ := by
  have hTn : ∀ s ∈ StatedSL 2 F, ∀ t ∈ N ⊓ StatedSL 2 F, s * t * s⁻¹ ∈ N ⊓ StatedSL 2 F :=
    fun s hs t ht => ⟨Subgroup.Normal.conj_mem inferInstance t ht.1 s,
      (StatedSL 2 F).mul_mem ((StatedSL 2 F).mul_mem hs ht.2) ((StatedSL 2 F).inv_mem hs)⟩
  rcases statedSL_hq hF (N ⊓ StatedSL 2 F) inf_le_right hTn with hcen | heq
  · rw [eq_bot_iff]
    intro t ht
    have h2 : t * t = 1 := sq_eq_one_of_central ht.2 (hcen t ht)
    have h3 : t ^ 3 = 1 := by
      have h := pow_card_eq_one' (G := ↥N) (x := (⟨t, ht.1⟩ : ↥N))
      rcases hN with hN | hN
      · rw [hN, pow_one] at h
        have : t = 1 := congrArg Subtype.val h
        rw [this]; simp
      · rw [hN] at h
        exact congrArg Subtype.val h
    have : t = 1 := by
      calc t = t ^ 3 := by rw [pow_succ, pow_two, h2, one_mul]
        _ = 1 := h3
    rw [this]
    exact Subgroup.one_mem _
  · exfalso
    have hle : StatedSL 2 F ≤ N := by rw [← heq]; exact inf_le_left
    have h1 := Subgroup.card_le_of_le hle
    rw [card_statedSL2] at h1
    have h16 : 16 ≤ Nat.card F ^ 2 := by nlinarith [hF]
    have h4 : 4 * 15 ≤ Nat.card F * (Nat.card F ^ 2 - 1) :=
      Nat.mul_le_mul hF (by omega)
    rcases hN with hN | hN <;> omega

theorem card_le_of_nonabelian (hF : 4 ≤ Nat.card F) (N : Subgroup (GL (Fin 2) F)) [N.Normal]
    (M₀ : Subgroup (GL (Fin 2) F ⧸ N)) [M₀.Normal]
    (hnc : ∃ x ∈ M₀, ∃ y ∈ M₀, x * y ≠ y * x) :
    Nat.card F * (Nat.card F ^ 2 - 1) ≤ Nat.card N * Nat.card M₀ := by
  have hMnc := nonabelian_comap (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) hnc
  have hS : StatedSL 2 F ≤ M₀.comap (QuotientGroup.mk' N) :=
    CFSG.GH74.GLS.Stage4.Rest.nonabelian_normal_contains (StatedSL 2 F) (statedSL_perfect hF)
      (fun T hTS hTn => statedSL_hq hF T hTS hTn) centralizes_of_commute_statedSL _ hMnc
  have h := Subgroup.card_le_of_le hS
  rwa [card_comap_mk, card_statedSL2] at h

theorem card_eq_of_perfect (hF : 4 ≤ Nat.card F) (N : Subgroup (GL (Fin 2) F)) [N.Normal]
    (hN : Nat.card N = 1 ∨ Nat.card N = 3)
    (M₀ : Subgroup (GL (Fin 2) F ⧸ N)) [M₀.Normal] (hperf : ⁅M₀, M₀⁆ = M₀)
    (hnc : ∃ x ∈ M₀, ∃ y ∈ M₀, x * y ≠ y * x) :
    Nat.card M₀ = Nat.card F * (Nat.card F ^ 2 - 1) := by
  have hMnc := nonabelian_comap (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) hnc
  have hMperf := comap_perfect (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) M₀ hperf
  rw [QuotientGroup.ker_mk'] at hMperf
  have hNM : N ≤ M₀.comap (QuotientGroup.mk' N) := by
    intro x hx
    show QuotientGroup.mk' N x ∈ M₀
    rw [show QuotientGroup.mk' N x = 1 from (QuotientGroup.eq_one_iff x).2 hx]
    exact M₀.one_mem
  obtain ⟨-, hcard⟩ := CFSG.GH74.GLS.Stage4.Rest.card_eq_of_perfect_normal (StatedSL 2 F) N
    (inf_eq_bot_of_card hF N hN) commutator_mem_statedSL (statedSL_perfect hF)
    (fun T hTS hTn => statedSL_hq hF T hTS hTn) centralizes_of_commute_statedSL
    (M₀.comap (QuotientGroup.mk' N)) hNM hMperf hMnc
  rw [card_comap_mk, card_statedSL2] at hcard
  have hNpos : 0 < Nat.card N := Nat.card_pos
  rw [mul_comm (Nat.card F * _)] at hcard
  exact (Nat.eq_of_mul_eq_mul_left hNpos hcard)

end Layer

section KSide

theorem two_ne_zero_of_odd_card {F₂ : Type} [Field F₂] [Finite F₂] (hodd : Odd (Nat.card F₂)) :
    (2 : F₂) ≠ 0 := by
  refine Ring.two_ne_zero fun h => ?_
  have := Fintype.ofFinite F₂
  have h1 : Fintype.card F₂ % 2 = 0 := FiniteField.even_card_of_char_two h
  rw [← Nat.card_eq_fintype_card] at h1
  have := Nat.odd_iff.mp hodd
  omega

theorem le_centralizer_of_involution {E : Type} [Group E] {K : Subgroup E} {F₂ : Type} [Field F₂]
    (h2 : (2 : F₂) ≠ 0) (e : ↥K ≃* StatedSL 2 F₂) {z : E} (hzK : z ∈ K) (hz : orderOf z = 2) :
    K ≤ Subgroup.centralizer {z} := by
  intro k hk
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hzz : (⟨z, hzK⟩ : ↥K) * ⟨z, hzK⟩ = 1 := by
    apply Subtype.ext
    have : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
    simpa [pow_two] using this
  have ht : e ⟨z, hzK⟩ * e ⟨z, hzK⟩ = 1 := by rw [← map_mul, hzz, map_one]
  have htt : ((e ⟨z, hzK⟩ : StatedSL 2 F₂) : GL (Fin 2) F₂) *
      ((e ⟨z, hzK⟩ : StatedSL 2 F₂) : GL (Fin 2) F₂) = 1 := by
    simpa using congrArg Subtype.val ht
  have hcomm := statedSL_involution_central h2 (e ⟨z, hzK⟩).2 htt
    ((e ⟨k, hk⟩ : StatedSL 2 F₂) : GL (Fin 2) F₂) (e ⟨k, hk⟩).2
  have h1 : e ⟨z, hzK⟩ * e ⟨k, hk⟩ = e ⟨k, hk⟩ * e ⟨z, hzK⟩ := Subtype.ext hcomm
  have h3 : (⟨k, hk⟩ : ↥K) * ⟨z, hzK⟩ = ⟨z, hzK⟩ * ⟨k, hk⟩ :=
    e.injective (by rw [map_mul, map_mul]; exact h1.symm)
  exact congrArg Subtype.val h3

theorem nonabelian_of_equiv {Q : Type*} [Group Q] {F₂ : Type} [Field F₂] {M₀ : Subgroup Q}
    (eMS : ↥M₀ ≃* StatedSL 2 F₂) : ∃ x ∈ M₀, ∃ y ∈ M₀, x * y ≠ y * x := by
  obtain ⟨a, ha, b, hb, hab⟩ := statedSL_nonabelian (F := F₂)
  refine ⟨(eMS.symm ⟨a, ha⟩ : Q), (eMS.symm ⟨a, ha⟩).2, (eMS.symm ⟨b, hb⟩ : Q),
    (eMS.symm ⟨b, hb⟩).2, ?_⟩
  intro h
  apply hab
  have h1 : eMS.symm ⟨a, ha⟩ * eMS.symm ⟨b, hb⟩ = eMS.symm ⟨b, hb⟩ * eMS.symm ⟨a, ha⟩ :=
    Subtype.ext h
  have h2 := congrArg eMS h1
  simpa using congrArg Subtype.val h2

end KSide

section Arith

theorem sl2_card_strictMono {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    a * (a ^ 2 - 1) < b * (b ^ 2 - 1) := by
  have h1 : a ^ 2 - 1 < b ^ 2 - 1 := by
    have : a ^ 2 < b ^ 2 := Nat.pow_lt_pow_left hab (by norm_num)
    have : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ ha
    omega
  calc a * (a ^ 2 - 1) ≤ b * (a ^ 2 - 1) := Nat.mul_le_mul_right _ hab.le
    _ < b * (b ^ 2 - 1) := Nat.mul_lt_mul_of_pos_left h1 (by omega)

theorem eq_of_sl2_card_eq {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : a * (a ^ 2 - 1) = b * (b ^ 2 - 1)) : a = b := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact absurd h (sl2_card_strictMono ha hlt).ne
  · exact absurd h.symm (sl2_card_strictMono hb hlt).ne

end Arith

end CFSG.GH74.GLS.Stage4.Rest.FieldL3

namespace CFSG.GH74.GLS.Stage4.Rest

open CFSG.GH74.GLS.Stage4.Rest.FieldL3

theorem field_eq_of_component_L3 {E : Type} [Group E] [Finite E] {p' f p n : ℕ}
    (hp' : p'.Prime) (hp'2 : p' ≠ 2) (hE : CFSG.GH74.GLS.IVK.IsLnEps 3 E 1 (p' ^ f))
    (hp : p.Prime) (hp2 : p ≠ 2) {K : Subgroup E}
    (hK : CFSG.GH74.GLS.HasSL2Model ↥K (fun q => q = p ^ n)) (h3 : 3 ≤ p ^ n)
    {z : E} (hzK : z ∈ K) (hz : orderOf z = 2)
    (hCK : ∀ c : E, c * z = z * c → ∀ k ∈ K, c * k * c⁻¹ ∈ K) : p' ^ f = p ^ n := by
  obtain ⟨F, hFf, hFin, N, hNn, hFcard, hN, ⟨Φ⟩⟩ :=
    CFSG.GH74.GLS.IVK.Proofs2.ivk_4_1a_L3 E p' f hp' hp'2 hE z hz
  obtain ⟨F₂, hF₂f, hF₂fin, hF₂card, ⟨e⟩⟩ := hK
  have hF₂card' : Nat.card F₂ = p ^ n := hF₂card
  have hodd : Odd (Nat.card F) := by
    rw [hFcard]; exact (hp'.eq_two_or_odd'.resolve_left hp'2).pow
  have hodd₂ : Odd (Nat.card F₂) := by
    rw [hF₂card']; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have h2 : (2 : F₂) ≠ 0 := two_ne_zero_of_odd_card hodd₂
  have hKC : K ≤ Subgroup.centralizer {z} := le_centralizer_of_involution h2 e hzK hz
  obtain ⟨M₀, hM₀n, ⟨eM⟩⟩ := exists_normal_model hKC Φ
    (fun c hc k hk => hCK c (Subgroup.mem_centralizer_singleton_iff.1 hc) k hk)
  let eMS : ↥M₀ ≃* StatedSL 2 F₂ := eM.symm.trans e
  have hMcard : Nat.card M₀ = Nat.card F₂ * (Nat.card F₂ ^ 2 - 1) := by
    rw [Nat.card_congr eMS.toEquiv, card_statedSL2]
  have hnc : ∃ x ∈ M₀, ∃ y ∈ M₀, x * y ≠ y * x := nonabelian_of_equiv eMS
  have hF2 : 2 ≤ Nat.card F := Finite.one_lt_card
  have hq2 : 3 ≤ Nat.card F₂ := by rw [hF₂card']; exact h3
  rw [← hFcard, ← hF₂card']
  obtain ⟨k, hk⟩ := hodd
  by_cases hF3 : Nat.card F = 3
  ·
    have hΓ : Nat.card (GL (Fin 2) F) = 48 := by rw [card_GL2, hF3]; norm_num
    have hQ : Nat.card (GL (Fin 2) F ⧸ N) ≤ 48 := by
      have := Subgroup.card_quotient_dvd_card N
      rw [hΓ] at this
      exact Nat.le_of_dvd (by norm_num) this
    have hM : Nat.card M₀ ≤ Nat.card (GL (Fin 2) F ⧸ N) := Subgroup.card_le_card_group M₀
    have hq3 : Nat.card F₂ = 3 := by
      by_contra hne
      have h4 : 4 ≤ Nat.card F₂ := by omega
      have h16 : 16 ≤ Nat.card F₂ ^ 2 := by nlinarith [h4]
      have : 4 * 15 ≤ Nat.card F₂ * (Nat.card F₂ ^ 2 - 1) := Nat.mul_le_mul h4 (by omega)
      omega
    rw [hF3, hq3]
  · have hF4 : 4 ≤ Nat.card F := by omega
    by_cases hq3 : Nat.card F₂ = 3
    ·
      exfalso
      have hle := card_le_of_nonabelian hF4 N M₀ hnc
      have hN3 : Nat.card N ≤ 3 := by omega
      have h5 : 5 ≤ Nat.card F := by omega
      have h25 : 25 ≤ Nat.card F ^ 2 := by nlinarith [h5]
      have h120 : 5 * 24 ≤ Nat.card F * (Nat.card F ^ 2 - 1) := Nat.mul_le_mul h5 (by omega)
      have hM24 : Nat.card M₀ = 24 := by rw [hMcard, hq3]; norm_num
      have : Nat.card N * Nat.card M₀ ≤ 3 * 24 := by
        rw [hM24]; exact Nat.mul_le_mul_right _ hN3
      omega
    ·
      have hq4 : 4 ≤ Nat.card F₂ := by omega
      have hperf : ⁅M₀, M₀⁆ = M₀ := by
        have hS : Group.IsPerfect (StatedSL 2 F₂) :=
          Subgroup.isPerfect_iff.2 (statedSL_perfect hq4)
        have : Group.IsPerfect ↥M₀ :=
          Group.IsPerfect.ofSurjective (f := eMS.symm.toMonoidHom) eMS.symm.surjective
        exact Subgroup.isPerfect_iff.1 this
      have hcard := card_eq_of_perfect hF4 N hN M₀ hperf hnc
      rw [hMcard] at hcard
      exact (eq_of_sl2_card_eq (by omega) (by omega) hcard).symm

end CFSG.GH74.GLS.Stage4.Rest
