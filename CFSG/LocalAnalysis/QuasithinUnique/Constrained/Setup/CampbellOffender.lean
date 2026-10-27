module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellGamma

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Matrix Module CFSG.SL2MinimalFaithful CFSG.QuasithinUnique.Setup.Offender
open scoped LinearAlgebra.Projectivization

section Offender

variable {k : Type*} [Field k]

@[expose] def fixSet (A : Subgroup (Equiv.Perm (Fin 2 → k))) : Set (Fin 2 → k) :=
  {w | ∀ a ∈ A, a w = w}

omit [Field k] in
theorem mem_fixSet {A : Subgroup (Equiv.Perm (Fin 2 → k))} {w : Fin 2 → k} :
    w ∈ fixSet A ↔ ∀ a ∈ A, a w = w := Iff.rfl

theorem card_eq_two_pow [Finite k] [CharP k 2] : ∃ n : ℕ, 1 ≤ n ∧ Nat.card k = 2 ^ n := by
  classical
  have : Fintype k := Fintype.ofFinite k
  obtain ⟨n, -, hn⟩ := FiniteField.card k 2
  exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card]; exact hn⟩

@[expose] def affPerm (b : k) (σ : k ≃+* k) : Equiv.Perm (Fin 2 → k) :=
  semilinPerm (unipotent b) σ

theorem affPerm_apply (b : k) (σ : k ≃+* k) (w : Fin 2 → k) :
    affPerm b σ w = ![σ (w 0) + b * σ (w 1), σ (w 1)] := by
  rw [affPerm, semilinPerm_apply, smul_unipotent_vec]

theorem affPerm_mem_Gamma (b : k) (σ : k ≃+* k) : affPerm b σ ∈ Gamma k := semilinPerm_mem _ _

theorem affPerm_mul (b b' : k) (σ σ' : k ≃+* k) :
    affPerm b σ * affPerm b' σ' = affPerm (b + σ b') (σ * σ') := by
  ext w : 1
  funext i
  fin_cases i
  · simp [affPerm_apply]; ring
  · simp [affPerm_apply]

theorem affPerm_zero_one : affPerm (0 : k) 1 = 1 := by
  ext w : 1
  funext i
  fin_cases i <;> simp [affPerm_apply]

theorem affPerm_inj {b b' : k} {σ σ' : k ≃+* k} (h : affPerm b σ = affPerm b' σ') :
    b = b' ∧ σ = σ' := by
  have h2 : ∀ x : k, σ x = σ' x := fun x => by
    have := congrFun (congrArg (fun e : Equiv.Perm (Fin 2 → k) => e (Pi.single 0 x)) h) 0
    simpa [affPerm_apply] using this
  refine ⟨?_, RingEquiv.ext h2⟩
  have := congrFun (congrArg (fun e : Equiv.Perm (Fin 2 → k) => e (Pi.single 1 1)) h) 0
  simpa [affPerm_apply] using this

theorem affPerm_one_eq (b : k) : affPerm b 1 = slPerm k (unipotent b) := rfl

theorem exists_affPerm_of_fix {a : Equiv.Perm (Fin 2 → k)} (ha : a ∈ Gamma k)
    (h : a (Pi.single 0 1) = Pi.single 0 1) : ∃ (b : k) (σ : k ≃+* k), a = affPerm b σ := by
  obtain ⟨B, σ, rfl⟩ := ha
  have hσe : (fun i => σ ((Pi.single 0 1 : Fin 2 → k) i)) = Pi.single 0 1 := by
    funext i; fin_cases i <;> simp
  have hB : B • (Pi.single 0 1 : Fin 2 → k) = Pi.single 0 1 := by
    have := h
    rwa [semilinPerm_apply, hσe] at this
  have hv : (Pi.single 0 1 : Fin 2 → k) ≠ 0 := by simp [Pi.single_eq_zero_iff]
  have hmem := mem_rootGrp_mk_of_smul_eq hv hB
  have h0 : Projectivization.mk k (Pi.single 0 1 : Fin 2 → k) hv = pt0 := rfl
  rw [h0, rootGrp_pt0] at hmem
  obtain ⟨t, ht⟩ := hmem
  refine ⟨t.toAdd, σ, ?_⟩
  rw [affPerm]
  congr 1
  exact ht.symm

theorem mem_rootPerm_pt0 {a : Equiv.Perm (Fin 2 → k)} :
    a ∈ rootPerm (pt0 : ℙ k (Fin 2 → k)) ↔ ∃ t : k, a = affPerm t 1 := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [rootGrp_pt0] at hu
    obtain ⟨t, rfl⟩ := hu
    exact ⟨t.toAdd, rfl⟩
  · rintro ⟨t, rfl⟩
    refine ⟨unipotent t, ?_, rfl⟩
    rw [rootGrp_pt0]
    exact ⟨Multiplicative.ofAdd t, rfl⟩

omit [Field k] in
theorem mem_map_conj {A : Subgroup (Equiv.Perm (Fin 2 → k))} {c x : Equiv.Perm (Fin 2 → k)} :
    x ∈ A.map (MulAut.conj c).toMonoidHom ↔ c⁻¹ * x * c ∈ A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using ha
  · intro h
    refine ⟨c⁻¹ * x * c, h, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

omit [Field k] in
theorem card_fixSet_map_conj (A : Subgroup (Equiv.Perm (Fin 2 → k))) (c : Equiv.Perm (Fin 2 → k)) :
    Nat.card (fixSet (A.map (MulAut.conj c).toMonoidHom)) = Nat.card (fixSet A) := by
  apply Nat.card_congr
  refine Equiv.subtypeEquiv c⁻¹ ?_
  intro w
  show (∀ a ∈ A.map (MulAut.conj c).toMonoidHom, a w = w) ↔ ∀ a ∈ A, a (c⁻¹ w) = c⁻¹ w
  constructor
  · intro h a ha
    have h2 : (c * a * c⁻¹) w = w := h _ ⟨a, ha, rfl⟩
    have h3 : c (a (c⁻¹ w)) = w := h2
    have := congrArg (fun x => c⁻¹ x) h3
    simpa using this
  · intro h a ha
    obtain ⟨a', ha', rfl⟩ := ha
    show (c * a' * c⁻¹) w = w
    show c (a' (c⁻¹ w)) = w
    rw [h a' ha']
    exact c.apply_symm_apply w

theorem rootPerm_smul (g : SpecialLinearGroup (Fin 2) k) (ℓ : ℙ k (Fin 2 → k)) :
    rootPerm (g • ℓ) = (rootPerm ℓ).map (MulAut.conj (slPerm k g)).toMonoidHom := by
  unfold rootPerm
  rw [rootGrp_smul_eq_map, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext u
  simp [MulAut.conj_apply]

theorem exists_smul_e0 {w : Fin 2 → k} (hw : w ≠ 0) :
    ∃ g : SpecialLinearGroup (Fin 2) k, g • (Pi.single 0 1 : Fin 2 → k) = w := by
  by_cases h0 : w 0 = 0
  · have h1 : w 1 ≠ 0 := by
      intro h1; apply hw; funext i; fin_cases i <;> simp [h0, h1]
    obtain ⟨g, hg⟩ : ∃ g : SpecialLinearGroup (Fin 2) k,
        (g : Matrix (Fin 2) (Fin 2) k) = !![0, -(w 1)⁻¹; w 1, 0] :=
      ⟨⟨_, by simp [Matrix.det_fin_two, h1]⟩, rfl⟩
    refine ⟨g, ?_⟩
    rw [Matrix.SpecialLinearGroup.smul_def, hg]
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0]
  · obtain ⟨g, hg⟩ : ∃ g : SpecialLinearGroup (Fin 2) k,
        (g : Matrix (Fin 2) (Fin 2) k) = !![w 0, 0; w 1, (w 0)⁻¹] :=
      ⟨⟨_, by simp [Matrix.det_fin_two, h0]⟩, rfl⟩
    refine ⟨g, ?_⟩
    rw [Matrix.SpecialLinearGroup.smul_def, hg]
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem exists_fixed_vec_of_isPGroup [Finite k] [CharP k 2]
    (A : Subgroup (Equiv.Perm (Fin 2 → k))) (hA : A ≤ Gamma k) (hp : IsPGroup 2 A) :
    ∃ w : Fin 2 → k, w ≠ 0 ∧ ∀ a ∈ A, a w = w := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hp.card_modEq_card_fixedPoints (Fin 2 → k)
  obtain ⟨n, hn1, hn⟩ := card_eq_two_pow (k := k)
  have heven : 2 ∣ Nat.card (Fin 2 → k) := by
    rw [card_fin_two_pi, hn, ← pow_mul]
    exact dvd_pow_self 2 (by omega)
  have hfix2 : 2 ∣ Nat.card (MulAction.fixedPoints A (Fin 2 → k)) :=
    (Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr heven)))
  by_contra hall
  push Not at hall
  have h0 : (0 : Fin 2 → k) ∈ MulAction.fixedPoints A (Fin 2 → k) := by
    rw [MulAction.mem_fixedPoints]
    intro a
    exact Gamma_apply_zero (hA a.2)
  have hsub : (MulAction.fixedPoints A (Fin 2 → k) : Set (Fin 2 → k)) = {0} := by
    ext w
    constructor
    · intro hw
      by_contra hw0
      rw [Set.mem_singleton_iff] at hw0
      obtain ⟨a, ha, hne⟩ := hall w hw0
      have := (MulAction.mem_fixedPoints.mp hw) ⟨a, ha⟩
      exact hne this
    · intro hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]; exact h0
  have : Nat.card (MulAction.fixedPoints A (Fin 2 → k)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => ?_⟩, ⟨⟨0, h0⟩⟩⟩
    apply Subtype.ext
    have hx : (x : Fin 2 → k) ∈ ({0} : Set (Fin 2 → k)) := hsub ▸ x.2
    have hy : (y : Fin 2 → k) ∈ ({0} : Set (Fin 2 → k)) := hsub ▸ y.2
    rw [Set.mem_singleton_iff] at hx hy
    rw [hx, hy]
  rw [this] at hfix2
  omega

theorem exists_fixed_vec [Finite k] [CharP k 2] (A : Subgroup (Equiv.Perm (Fin 2 → k)))
    (hA : A ≤ Gamma k) (hsq : ∀ a ∈ A, a * a = 1) :
    ∃ w : Fin 2 → k, w ≠ 0 ∧ ∀ a ∈ A, a w = w :=
  exists_fixed_vec_of_isPGroup A hA (fun a => ⟨1, by
    have h1 : a * a = 1 := Subtype.ext (hsq a a.2)
    rw [pow_one, pow_two]; exact h1⟩)

theorem card_rootPerm [Finite k] (ℓ : ℙ k (Fin 2 → k)) : Nat.card (rootPerm ℓ) = Nat.card k := by
  unfold rootPerm
  rw [Subgroup.card_map_of_injective slPerm_injective, card_rootGrp]

theorem fixSet_rootPerm [Finite k] (ℓ : ℙ k (Fin 2 → k)) :
    fixSet (rootPerm ℓ) = (ℓ.submodule : Set (Fin 2 → k)) := by
  ext w
  constructor
  · intro hw
    obtain ⟨u, hu, hu1⟩ := exists_ne_one_mem_rootGrp ℓ
    have := hw (slPerm k u) ⟨u, hu, rfl⟩
    exact (smul_eq_self_iff_mem_of_mem_rootGrp hu hu1 w).mp this
  · intro hw a ha
    obtain ⟨u, hu, rfl⟩ := ha
    by_cases hu1 : u = 1
    · simp [hu1]
    · exact (smul_eq_self_iff_mem_of_mem_rootGrp hu hu1 w).mpr hw

theorem card_fixSet_rootPerm [Finite k] (ℓ : ℙ k (Fin 2 → k)) :
    Nat.card (fixSet (rootPerm ℓ)) = Nat.card k := by
  rw [fixSet_rootPerm]
  exact card_submodule_line ℓ

theorem offender_normal_form [Finite k] [CharP k 2] (A : Subgroup (Equiv.Perm (Fin 2 → k)))
    (hA : A ≤ Gamma k) (hsq : ∀ a ∈ A, a * a = 1) (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hfix : ∀ a ∈ A, a (Pi.single 0 1) = Pi.single 0 1) (hne : A ≠ ⊥) :
    Nat.card A * Nat.card (fixSet A) ≤ Nat.card k ^ 2 ∧
      (Nat.card A * Nat.card (fixSet A) = Nat.card k ^ 2 → A = rootPerm (pt0 : ℙ k (Fin 2 → k))) := by
  classical
  set q := Nat.card k with hq
  have hqpos : 0 < q := Nat.card_pos
  have hrep : ∀ a ∈ A, ∃ (b : k) (σ : k ≃+* k), a = affPerm b σ :=
    fun a ha => exists_affPerm_of_fix (hA ha) (hfix a ha)
  by_cases hlin : ∀ a ∈ A, ∃ b : k, a = affPerm b 1
  ·
    choose! bf hbf using hlin
    have hinj : Function.Injective (fun a : A => bf a) := fun a a' h =>
      Subtype.ext (by rw [hbf a a.2, hbf a' a'.2]; exact congrArg (fun t => affPerm t 1) h)
    have hAq : Nat.card A ≤ q := Nat.card_le_card_of_injective _ hinj
    obtain ⟨⟨a₁, ha₁⟩, h1ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have hb₁ : bf a₁ ≠ 0 := fun h0 => h1ne (Subtype.ext (by
      show a₁ = 1
      rw [hbf a₁ ha₁, h0, affPerm_zero_one]))
    have hw1 : ∀ w ∈ fixSet A, w 1 = 0 := by
      intro w hw
      have h := hw a₁ ha₁
      rw [hbf a₁ ha₁, affPerm_apply] at h
      have := congrFun h 0
      simp at this
      exact this.resolve_left hb₁
    have hFq : Nat.card (fixSet A) ≤ q := by
      have : Function.Injective (fun w : fixSet A => (w : Fin 2 → k) 0) := by
        intro w w' h
        apply Subtype.ext
        funext i
        fin_cases i
        · exact h
        · simp [hw1 _ w.2, hw1 _ w'.2]
      exact Nat.card_le_card_of_injective _ this
    have hW : Nat.card A * Nat.card (fixSet A) ≤ q ^ 2 := by nlinarith
    refine ⟨hW, fun heq => ?_⟩
    have hAeq : Nat.card A = q := by
      by_contra hlt
      have : Nat.card A < q := lt_of_le_of_ne hAq hlt
      nlinarith
    have hbij : Function.Bijective (fun a : A => bf a) :=
      hinj.bijective_of_nat_card_le (le_of_eq hAeq.symm)
    ext a
    constructor
    · intro ha
      exact mem_rootPerm_pt0.mpr ⟨bf a, hbf a ha⟩
    · intro ha
      obtain ⟨t, rfl⟩ := mem_rootPerm_pt0.mp ha
      obtain ⟨⟨a', ha'⟩, ha't⟩ := hbij.2 t
      have : a' = affPerm t 1 := by
        rw [hbf a' ha']
        exact congrArg (fun t => affPerm t 1) ha't
      rw [← this]
      exact ha'
  ·
    push Not at hlin
    obtain ⟨a₀, ha₀, hn⟩ := hlin
    obtain ⟨b₀, σ₀, rfl⟩ := hrep a₀ ha₀
    have hσ₀1 : σ₀ ≠ 1 := fun h => hn b₀ (by rw [h])
    have hsq₀ := hsq _ ha₀
    rw [affPerm_mul] at hsq₀
    obtain ⟨hb₀, hσ₀2⟩ := affPerm_inj (hsq₀.trans affPerm_zero_one.symm)
    obtain ⟨n₀, hqn, hn₀2, hk₀⟩ := card_eq_sq_of_involution σ₀ hσ₀1 hσ₀2
    rw [← hq] at hqn
    have hform : ∀ a ∈ A, ∃ b : k, a = affPerm b 1 ∨ a = affPerm b σ₀ := by
      intro a ha
      obtain ⟨b, σ, rfl⟩ := hrep a ha
      have h2 := hsq _ ha
      rw [affPerm_mul] at h2
      obtain ⟨-, hσ2⟩ := affPerm_inj (h2.trans affPerm_zero_one.symm)
      by_cases hσ1 : σ = 1
      · exact ⟨b, Or.inl (by rw [hσ1])⟩
      · exact ⟨b, Or.inr (by rw [aut_involution_unique σ σ₀ hσ2 hσ₀2 hσ1 hσ₀1])⟩
    have hfixa₀ : Nat.card {w : Fin 2 → k // affPerm b₀ σ₀ w = w} = q := by
      have hsem : IsSemilinearWith (affPerm b₀ σ₀) σ₀ := semilinPerm_isSemilinear _ _
      have htr : ∃ x : k, σ₀ x + x = 1 := exists_trace_eq_one σ₀ hσ₀1 hσ₀2
      have ha2 : ∀ w, affPerm b₀ σ₀ (affPerm b₀ σ₀ w) = w := fun w => by
        have := congrArg (fun e : Equiv.Perm (Fin 2 → k) => e w) (hsq _ ha₀)
        simpa using this
      have h := card_eq_sq_fixed (affPerm b₀ σ₀)
        (Gamma_apply_add (affPerm_mem_Gamma b₀ σ₀)) ha2 (neg_eq_self_of_char_two_module k)
        (semilinear_involution_fixed_image hsem htr)
      rw [card_fin_two_pi] at h
      exact (Nat.pow_left_injective (by norm_num : 2 ≠ 0) h).symm
    have hFA_le : Nat.card (fixSet A) ≤ q := by
      have hsub : fixSet A ⊆ {w | affPerm b₀ σ₀ w = w} := fun w hw => hw _ ha₀
      rw [← hfixa₀]
      exact Nat.card_mono (Set.toFinite _) hsub
    set K : Subgroup (Equiv.Perm (Fin 2 → k)) := A ⊓ rootPerm (pt0 : ℙ k (Fin 2 → k)) with hK
    have hmemK : ∀ a, a ∈ K ↔ a ∈ A ∧ ∃ t : k, a = affPerm t 1 := fun a => by
      rw [hK, Subgroup.mem_inf, mem_rootPerm_pt0]
    have hKA : K ≤ A := inf_le_left
    have hK' : ∀ a ∈ A, a ∉ K → affPerm b₀ σ₀ * a ∈ K := by
      intro a ha haK
      obtain ⟨b, h | h⟩ := hform a ha
      · exact absurd ((hmemK a).mpr ⟨ha, b, h⟩) haK
      · rw [hmemK]
        refine ⟨mul_mem ha₀ ha, b₀ + σ₀ b, ?_⟩
        rw [h, affPerm_mul, hσ₀2]
    have hAK : Nat.card A ≤ 2 * Nat.card K := by
      have hsub : (A : Set (Equiv.Perm (Fin 2 → k))) ⊆
          (K : Set _) ∪ (fun x => affPerm b₀ σ₀ * x) '' (K : Set _) := by
        intro a ha
        by_cases haK : a ∈ K
        · exact Or.inl haK
        · refine Or.inr ⟨affPerm b₀ σ₀ * a, hK' a ha haK, ?_⟩
          show affPerm b₀ σ₀ * (affPerm b₀ σ₀ * a) = a
          rw [← mul_assoc, hsq _ ha₀, one_mul]
      have hAn : Nat.card A = (A : Set (Equiv.Perm (Fin 2 → k))).ncard := Nat.card_coe_set_eq _
      have h1 : Nat.card A ≤ ((K : Set _) ∪ (fun x => affPerm b₀ σ₀ * x) '' (K : Set _)).ncard := by
        rw [hAn]
        exact Set.ncard_le_ncard hsub (Set.toFinite _)
      have h2 := Set.ncard_union_le (K : Set (Equiv.Perm (Fin 2 → k)))
        ((fun x => affPerm b₀ σ₀ * x) '' (K : Set _))
      have h3 : ((fun x => affPerm b₀ σ₀ * x) '' (K : Set (Equiv.Perm (Fin 2 → k)))).ncard =
          (K : Set (Equiv.Perm (Fin 2 → k))).ncard :=
        Set.ncard_image_of_injective _ (mul_right_injective _)
      have h4 : (K : Set (Equiv.Perm (Fin 2 → k))).ncard = Nat.card K :=
        (Nat.card_coe_set_eq (K : Set (Equiv.Perm (Fin 2 → k)))).symm
      omega
    have hKn : Nat.card K ≤ n₀ := by
      have hσt : ∀ a ∈ K, ∃ t : k, a = affPerm t 1 ∧ σ₀ t = t := by
        intro a ha
        obtain ⟨haA, t, rfl⟩ := (hmemK a).mp ha
        refine ⟨t, rfl, ?_⟩
        have hc := hcomm _ ha₀ _ haA
        rw [affPerm_mul, affPerm_mul] at hc
        have := (affPerm_inj hc).1
        have e : (1 : k ≃+* k) b₀ = b₀ := rfl
        rw [e] at this
        linear_combination this
      choose! tf htf hσtf using hσt
      have hinj : Function.Injective (fun a : K => (⟨tf a, hσtf a a.2⟩ : {c : k // σ₀ c = c})) := by
        intro a a' h
        apply Subtype.ext
        have h1 : tf a = tf a' := congrArg Subtype.val h
        rw [htf a a.2, htf a' a'.2, h1]
      calc Nat.card K ≤ Nat.card {c : k // σ₀ c = c} := Nat.card_le_card_of_injective _ hinj
        _ = n₀ := hk₀
    have hFA_n : K ≠ ⊥ → Nat.card (fixSet A) ≤ n₀ := by
      intro hKne
      obtain ⟨⟨a₁, ha₁K⟩, h1ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hKne
      obtain ⟨ha₁A, t₁, ht₁⟩ := (hmemK a₁).mp ha₁K
      have ht₁0 : t₁ ≠ 0 := fun h0 => h1ne (Subtype.ext (by
        show a₁ = 1
        rw [ht₁, h0, affPerm_zero_one]))
      have hw1 : ∀ w ∈ fixSet A, w 1 = 0 := by
        intro w hw
        have h := hw a₁ ha₁A
        rw [ht₁, affPerm_apply] at h
        have := congrFun h 0
        simp at this
        exact this.resolve_left ht₁0
      have hσw : ∀ w ∈ fixSet A, σ₀ (w 0) = w 0 := by
        intro w hw
        have h := hw _ ha₀
        have := congrFun h 0
        rw [affPerm_apply] at this
        simpa [hw1 w hw] using this
      have hinj : Function.Injective
          (fun w : fixSet A => (⟨(w : Fin 2 → k) 0, hσw w w.2⟩ : {c : k // σ₀ c = c})) := by
        intro w w' h
        apply Subtype.ext
        funext i
        fin_cases i
        · exact congrArg Subtype.val h
        · simp [hw1 _ w.2, hw1 _ w'.2]
      calc Nat.card (fixSet A) ≤ Nat.card {c : k // σ₀ c = c} := Nat.card_le_card_of_injective _ hinj
        _ = n₀ := hk₀
    have hprod : Nat.card A * Nat.card (fixSet A) ≤ 2 * q := by
      by_cases hKbot : K = ⊥
      · have h1 : Nat.card K = 1 := by rw [hKbot]; exact Subgroup.card_bot
        have : Nat.card A ≤ 2 := by omega
        nlinarith
      · have h1 := hFA_n hKbot
        have h2 : Nat.card A ≤ 2 * n₀ := by omega
        calc Nat.card A * Nat.card (fixSet A) ≤ (2 * n₀) * n₀ := Nat.mul_le_mul h2 h1
          _ = 2 * q := by rw [hqn]; ring
    have hlt : 2 * q < q ^ 2 := by
      rw [hqn]
      have h4 : 4 ≤ n₀ ^ 2 := by nlinarith
      generalize n₀ ^ 2 = m at h4 ⊢
      nlinarith
    exact ⟨by omega, fun heq => absurd heq (by omega)⟩

theorem offender_dichotomy [Finite k] [CharP k 2] (A : Subgroup (Equiv.Perm (Fin 2 → k)))
    (hA : A ≤ Gamma k) (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hsq : ∀ a ∈ A, a * a = 1)
    (hne : A ≠ ⊥) :
    Nat.card A * Nat.card (fixSet A) ≤ Nat.card k ^ 2 ∧
      (Nat.card A * Nat.card (fixSet A) = Nat.card k ^ 2 →
        ∃ ℓ : ℙ k (Fin 2 → k), A = rootPerm ℓ) := by
  obtain ⟨w₀, hw₀, hfixw⟩ := exists_fixed_vec A hA hsq
  obtain ⟨g, hg⟩ := exists_smul_e0 hw₀
  set c := slPerm k g with hc
  have hcΓ : c ∈ Gamma k := slPerm_mem_Gamma g
  have hce : c (Pi.single 0 1) = w₀ := hg
  set f : Equiv.Perm (Fin 2 → k) →* Equiv.Perm (Fin 2 → k) := (MulAut.conj c⁻¹).toMonoidHom with hf
  set A' := A.map f with hA'
  have hA'Γ : A' ≤ Gamma k := by
    rintro _ ⟨a, ha, rfl⟩
    exact mul_mem (mul_mem (inv_mem hcΓ) (hA ha)) (by simpa using hcΓ)
  have hsq' : ∀ a ∈ A', a * a = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, hsq a ha, map_one]
  have hcomm' : ∀ a ∈ A', ∀ b ∈ A', a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hcomm a ha b hb]
  have hfix' : ∀ a ∈ A', a (Pi.single 0 1) = Pi.single 0 1 := by
    rintro _ ⟨a, ha, rfl⟩
    show (c⁻¹ * a * c⁻¹⁻¹) (Pi.single 0 1) = Pi.single 0 1
    show c⁻¹ (a (c (Pi.single 0 1))) = _
    rw [hce, hfixw a ha]
    rw [← hce]
    exact c.symm_apply_apply _
  have hfinj : Function.Injective f := (MulAut.conj c⁻¹).injective
  have hne' : A' ≠ ⊥ := by
    intro h
    apply hne
    exact Subgroup.map_injective hfinj (h.trans (Subgroup.map_bot f).symm)
  have hcard : Nat.card A' = Nat.card A := Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective
  have hfixc : Nat.card (fixSet A') = Nat.card (fixSet A) := card_fixSet_map_conj A c⁻¹
  obtain ⟨h1, h2⟩ := offender_normal_form A' hA'Γ hsq' hcomm' hfix' hne'
  rw [hcard, hfixc] at h1 h2
  refine ⟨h1, fun heq => ⟨g • (pt0 : ℙ k (Fin 2 → k)), ?_⟩⟩
  have hA'eq := h2 heq
  have hcomp : (MulAut.conj c).toMonoidHom.comp f = MonoidHom.id _ := by
    refine MonoidHom.ext fun x => ?_
    show c * (c⁻¹ * x * c⁻¹⁻¹) * c⁻¹ = x
    group
  rw [rootPerm_smul, ← hA'eq, hA', Subgroup.map_map]
  change A = Subgroup.map ((MulAut.conj c).toMonoidHom.comp f) A
  rw [hcomp, Subgroup.map_id]

theorem mem_rootPerm_smul_iff {x : Equiv.Perm (Fin 2 → k)} (g : SpecialLinearGroup (Fin 2) k)
    (ℓ : ℙ k (Fin 2 → k)) :
    x ∈ rootPerm (g • ℓ) ↔ (slPerm k g)⁻¹ * x * slPerm k g ∈ rootPerm ℓ := by
  rw [rootPerm_smul, mem_map_conj]

theorem e0_mem_pt0 : (Pi.single 0 1 : Fin 2 → k) ∈ (pt0 : ℙ k (Fin 2 → k)).submodule := by
  rw [mem_span_e0_iff]
  simp

theorem mem_rootPerm_of_fixes_line [Finite k] {g : Equiv.Perm (Fin 2 → k)} (hg : g ∈ Gamma k)
    (ℓ : ℙ k (Fin 2 → k)) (h : ∀ w ∈ ℓ.submodule, g w = w) : g ∈ rootPerm ℓ := by
  obtain ⟨u, rfl⟩ := exists_smul_pt0 ℓ
  rw [mem_rootPerm_smul_iff]
  set c := slPerm k u with hc
  have hcΓ : c ∈ Gamma k := slPerm_mem_Gamma u
  have hg' : c⁻¹ * g * c ∈ Gamma k := mul_mem (mul_mem (inv_mem hcΓ) hg) hcΓ
  have hcline : ∀ x : k, c (Pi.single 0 x) ∈ (u • (pt0 : ℙ k (Fin 2 → k))).submodule := by
    intro x
    have h1 : c (Pi.single 0 x) = x • (u • (Pi.single 0 1 : Fin 2 → k)) := by
      show u • (Pi.single 0 x : Fin 2 → k) = _
      have : (Pi.single 0 x : Fin 2 → k) = x • (Pi.single 0 1 : Fin 2 → k) := by
        funext i; fin_cases i <;> simp
      rw [this]
      rw [Matrix.SpecialLinearGroup.smul_def, Matrix.SpecialLinearGroup.smul_def]
      simp [Matrix.mulVec_smul]
    rw [h1]
    refine Submodule.smul_mem _ _ ?_
    rw [PSL.smul_submodule]
    exact Submodule.smul_mem_pointwise_smul _ _ _ e0_mem_pt0
  have hfixx : ∀ x : k, (c⁻¹ * g * c) (Pi.single 0 x) = Pi.single 0 x := by
    intro x
    show c⁻¹ (g (c (Pi.single 0 x))) = _
    rw [h _ (hcline x)]
    exact c.symm_apply_apply _
  obtain ⟨b, σ, hbσ⟩ := exists_affPerm_of_fix hg' (by simpa using hfixx 1)
  have hσ : σ = 1 := by
    refine RingEquiv.ext fun x => ?_
    have := congrFun (hfixx x) 0
    rw [hbσ, affPerm_apply] at this
    simpa using this
  rw [hbσ, hσ]
  exact mem_rootPerm_pt0.mpr ⟨b, rfl⟩

@[expose] def rootGamma (ℓ : ℙ k (Fin 2 → k)) : Subgroup (Gamma k) :=
  (rootPerm ℓ).subgroupOf (Gamma k)

theorem map_subtype_rootGamma (ℓ : ℙ k (Fin 2 → k)) :
    (rootGamma ℓ).map (Gamma k).subtype = rootPerm ℓ :=
  Subgroup.map_subgroupOf_eq_of_le (rootPerm_le_Gamma ℓ)

theorem mem_rootGamma {ℓ : ℙ k (Fin 2 → k)} {g : Gamma k} :
    g ∈ rootGamma ℓ ↔ (g : Equiv.Perm (Fin 2 → k)) ∈ rootPerm ℓ := Iff.rfl

theorem exists_slPerm_orderOf_three [CharP k 2] :
    ∃ t : SpecialLinearGroup (Fin 2) k, orderOf t = 3 := by
  have h2 : (2 : k) = 0 := by exact_mod_cast CharP.cast_eq_zero k 2
  obtain ⟨t, ht⟩ : ∃ t : SpecialLinearGroup (Fin 2) k,
      (t : Matrix (Fin 2) (Fin 2) k) = !![0, 1; 1, 1] :=
    ⟨⟨_, by simp [Matrix.det_fin_two]; linear_combination (-1 : k) * h2⟩, rfl⟩
  have ht1 : t ≠ 1 := by
    intro h
    have := congrArg (fun A : SpecialLinearGroup (Fin 2) k => (A : Matrix (Fin 2) (Fin 2) k) 0 0) h
    simp [ht] at this
  have ht3 : t ^ 3 = 1 := by
    have e : t ^ 3 = t * t * t := by rw [pow_succ, pow_two]
    rw [e]
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ht,
      Matrix.SpecialLinearGroup.coe_one]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | rfl | linear_combination h2
  exact ⟨t, orderOf_eq_prime ht3 ht1⟩

theorem rootPerm_eq_of_le_two_group [CharP k 2] [Finite k] {P : Subgroup (Equiv.Perm (Fin 2 → k))}
    (hP : IsPGroup 2 P) {ℓ₁ ℓ₂ : ℙ k (Fin 2 → k)} (h₁ : rootPerm ℓ₁ ≤ P) (h₂ : rootPerm ℓ₂ ≤ P) :
    ℓ₁ = ℓ₂ := by
  by_contra hne
  obtain ⟨t, ht⟩ := exists_slPerm_orderOf_three (k := k)
  have hsup : rootGrp ℓ₁ ⊔ rootGrp ℓ₂ = ⊤ := rootGrp_sup_rootGrp hne
  have hmem : t ∈ rootGrp ℓ₁ ⊔ rootGrp ℓ₂ := by rw [hsup]; trivial
  have hmap : slPerm k t ∈ rootPerm ℓ₁ ⊔ rootPerm ℓ₂ := by
    have : slPerm k t ∈ (rootGrp ℓ₁ ⊔ rootGrp ℓ₂).map (slPerm k) := ⟨t, hmem, rfl⟩
    rwa [Subgroup.map_sup] at this
  have hP' : slPerm k t ∈ P := sup_le h₁ h₂ hmap
  obtain ⟨m, hm⟩ := hP ⟨slPerm k t, hP'⟩
  have h3 : orderOf (slPerm k t) = 3 := by
    rw [orderOf_injective _ slPerm_injective, ht]
  have hdvd : orderOf (slPerm k t) ∣ 2 ^ m := by
    apply orderOf_dvd_of_pow_eq_one
    have := congrArg Subtype.val hm
    simpa using this
  rw [h3] at hdvd
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
  omega

theorem rootPerm_injective [Finite k] {ℓ ℓ' : ℙ k (Fin 2 → k)} (h : rootPerm ℓ = rootPerm ℓ') :
    ℓ = ℓ' := by
  by_contra hne
  have h1 : rootGrp ℓ = rootGrp ℓ' := by
    apply Subgroup.map_injective (slPerm_injective (k := k))
    exact h
  obtain ⟨u, hu, hu1⟩ := exists_ne_one_mem_rootGrp ℓ
  have hmem : u ∈ rootGrp ℓ ⊓ rootGrp ℓ' := ⟨hu, h1 ▸ hu⟩
  rw [rootGrp_inf_rootGrp hne, Subgroup.mem_bot] at hmem
  exact hu1 hmem

theorem card_le_of_isPGroup_of_le_slGamma [Finite k] [CharP k 2] (A : Subgroup (Gamma k))
    (hA : A ≤ slGamma k) (hp : IsPGroup 2 A) : Nat.card A ≤ Nat.card k := by
  classical
  set Ap : Subgroup (Equiv.Perm (Fin 2 → k)) := A.map (Gamma k).subtype with hAp
  have hApΓ : Ap ≤ Gamma k := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  have hApp : IsPGroup 2 Ap :=
    hp.of_equiv (A.equivMapOfInjective (Gamma k).subtype (Gamma k).subtype_injective)
  obtain ⟨w₀, hw₀, hfix⟩ := exists_fixed_vec_of_isPGroup Ap hApΓ hApp
  have hle : Ap ≤ rootPerm (Projectivization.mk k w₀ hw₀) := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨B, hB⟩ := mem_slGamma_iff.mp (hA ha)
    refine ⟨B, mem_rootGrp_mk_of_smul_eq hw₀ ?_, hB.symm⟩
    have := hfix _ ⟨a, ha, rfl⟩
    rw [show ((Gamma k).subtype a : Equiv.Perm (Fin 2 → k)) = slPerm k B from hB] at this
    exact this
  calc Nat.card A = Nat.card Ap :=
        (Nat.card_congr (A.equivMapOfInjective (Gamma k).subtype
          (Gamma k).subtype_injective).toEquiv)
    _ ≤ Nat.card (rootPerm (Projectivization.mk k w₀ hw₀)) := Subgroup.card_le_of_le hle
    _ = Nat.card k := card_rootPerm _

theorem rootGamma_le_slGamma (ℓ : ℙ k (Fin 2 → k)) : rootGamma ℓ ≤ slGamma k := by
  intro g hg
  obtain ⟨u, hu, hug⟩ := mem_rootGamma.mp hg
  exact mem_slGamma_iff.mpr ⟨u, hug.symm⟩

theorem isPGroup_rootGamma [Finite k] [CharP k 2] (ℓ : ℙ k (Fin 2 → k)) :
    IsPGroup 2 (rootGamma ℓ) := by
  intro g
  refine ⟨1, ?_⟩
  obtain ⟨u, hu, hug⟩ := mem_rootGamma.mp g.2
  have h1 : u * u = 1 := mul_self_eq_one_of_mem_rootGrp hu
  have hg : ((g : Gamma k) : Equiv.Perm (Fin 2 → k)) = slPerm k u := hug.symm
  rw [pow_one, pow_two]
  apply Subtype.ext
  apply Subtype.ext
  show ((g : Gamma k) : Equiv.Perm (Fin 2 → k)) * ((g : Gamma k) : Equiv.Perm (Fin 2 → k)) = 1
  rw [hg, ← map_mul, h1, map_one]

theorem submodule_sup_eq_top {p m : ℙ k (Fin 2 → k)} (h : p ≠ m) :
    p.submodule ⊔ m.submodule = ⊤ := by
  have hinf : p.submodule ⊓ m.submodule = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    exact (Submodule.mem_bot k).mpr (submodule_inf_eq_bot h hw.1 hw.2)
  have hrank := Submodule.finrank_sup_add_finrank_inf_eq p.submodule m.submodule
  rw [hinf, finrank_bot, p.finrank_submodule, m.finrank_submodule] at hrank
  apply Submodule.eq_top_of_finrank_eq
  rw [Module.finrank_fin_fun]
  omega

theorem card_rootGamma [Finite k] (ℓ : ℙ k (Fin 2 → k)) :
    Nat.card (rootGamma ℓ) = Nat.card k := by
  rw [← card_rootPerm ℓ, ← map_subtype_rootGamma ℓ,
    Subgroup.card_map_of_injective (Gamma k).subtype_injective]

theorem card_eq_two_pow_factorization_slGamma [Finite k] [CharP k 2] :
    Nat.card k = 2 ^ (Nat.card (slGamma k)).factorization 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ℓ⟩ : Nonempty (ℙ k (Fin 2 → k)) := ⟨pt0⟩
  set U : Subgroup (slGamma k) := (rootGamma ℓ).subgroupOf (slGamma k) with hU
  have hUp : IsPGroup 2 U :=
    (isPGroup_rootGamma ℓ).of_equiv ((rootGamma ℓ).subgroupOfEquivOfLe
      (rootGamma_le_slGamma ℓ)).symm
  obtain ⟨P₀, hP₀⟩ := hUp.exists_le_sylow
  have hcard := Sylow.card_eq_multiplicity P₀
  have hlow : Nat.card k ≤ Nat.card P₀ := by
    calc Nat.card k = Nat.card (rootGamma ℓ) := by
          rw [← card_rootPerm ℓ, ← map_subtype_rootGamma ℓ,
            Subgroup.card_map_of_injective (Gamma k).subtype_injective]
      _ = Nat.card U := (Nat.card_congr ((rootGamma ℓ).subgroupOfEquivOfLe
            (rootGamma_le_slGamma ℓ)).toEquiv).symm
      _ ≤ Nat.card P₀ := Subgroup.card_le_of_le hP₀
  have hup : Nat.card P₀ ≤ Nat.card k := by
    have hP0 : IsPGroup 2 (P₀ : Subgroup (slGamma k)) := P₀.isPGroup'
    have := card_le_of_isPGroup_of_le_slGamma ((P₀ : Subgroup (slGamma k)).map (slGamma k).subtype)
      (by rintro _ ⟨x, -, rfl⟩; exact x.2)
      (hP0.of_equiv (((P₀ : Subgroup (slGamma k)).equivMapOfInjective (slGamma k).subtype
        (slGamma k).subtype_injective)))
    rwa [Subgroup.card_map_of_injective (slGamma k).subtype_injective] at this
  rw [← hcard]
  omega

end Offender

end CFSG.QuasithinUnique.Setup.Campbell
