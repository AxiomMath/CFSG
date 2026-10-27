module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Inner
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81Cent

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.Q81

open CFSG Subgroup CFSG.ABGLocalTools

section Sylow

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem isSylowOf_subgroupOf {P K M : Subgroup G} (h : IsSylowOf p P K) (hKM : K ≤ M) :
    IsSylowOf p (P.subgroupOf M) (K.subgroupOf M) := by
  rw [← isSylowOf_map_subtype_iff M, map_subgroupOf_eq_of_le (h.le.trans hKM),
    map_subgroupOf_eq_of_le hKM]
  exact h

omit [Finite G] [Fact p.Prime] in
theorem exists_isSylowOf_ge {P K : Subgroup G} (hP : IsPGroup p P) (hPK : P ≤ K) :
    ∃ Q : Subgroup G, IsSylowOf p Q K ∧ P ≤ Q := by
  obtain ⟨R, hR⟩ := (hP.comap_subtype : IsPGroup p (P.subgroupOf K)).exists_le_sylow
  exact ⟨(R : Subgroup K).map K.subtype, ⟨R, rfl⟩,
    fun x hx => ⟨⟨x, hPK hx⟩, hR (mem_subgroupOf.mpr hx), rfl⟩⟩

theorem isSylowOf_of_normalizer_le {R M K : Subgroup G} (hRM : IsSylowOf p R M) (hMK : M ≤ K)
    (hN : K ⊓ normalizer (R : Set G) ≤ M) : IsSylowOf p R K := by
  have hRK : R ≤ K := hRM.le.trans hMK
  obtain ⟨Q, hQ⟩ := (hRM.isPGroup.comap_subtype (K := K)).exists_le_sylow
  set S : Subgroup G := (Q : Subgroup K).map K.subtype with hSdef
  have hRS : R ≤ S := fun x hx => ⟨⟨x, hRK hx⟩, hQ (mem_subgroupOf.mpr hx), rfl⟩
  have hSK : S ≤ K := map_subtype_le _
  have hS : IsPGroup p S := Q.isPGroup'.map K.subtype
  have hNS : S ⊓ normalizer (R : Set G) = R :=
    hRM.eq_of_le (le_inf hRS le_normalizer) ((inf_le_inf_right _ hSK).trans hN)
      (hS.to_le inf_le_left)
  have hSR : S ≤ R := by
    have hnil : Group.IsNilpotent S := hS.isNilpotent
    have htop := (normalizerCondition_iff_only_full_group_self_normalizing.mp
      (Group.normalizerCondition_of_isNilpotent (G := S))) (R.subgroupOf S) (by
        refine le_antisymm (fun s hs => ?_) le_normalizer
        rw [mem_subgroupOf, ← hNS]
        refine ⟨s.2, mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
        · have h := (mem_normalizer_iff.mp hs ⟨x, hRS hx⟩).mp (mem_subgroupOf.mpr hx)
          exact mem_subgroupOf.mp h
        · have hxS : x ∈ S := by
            have h1 : (s : G) * x * (s : G)⁻¹ ∈ S := hRS hx
            have h2 : x = (s : G)⁻¹ * ((s : G) * x * (s : G)⁻¹) * s := by group
            rw [h2]
            exact S.mul_mem (S.mul_mem (S.inv_mem s.2) h1) s.2
          have h := (mem_normalizer_iff.mp hs ⟨x, hxS⟩).mpr (mem_subgroupOf.mpr hx)
          exact mem_subgroupOf.mp h)
    intro x hx
    have : (⟨x, hx⟩ : S) ∈ R.subgroupOf S := htop ▸ mem_top _
    exact mem_subgroupOf.mp this
  have hRS' : R = S := le_antisymm hRS hSR
  rw [hRS']
  exact ⟨Q, rfl⟩

end Sylow

theorem sl2_three_quaternion {F : Type} [Field F] (h3 : (3 : F) = 0) :
    ∃ A B : Matrix.SpecialLinearGroup (Fin 2) F,
      ((A * A : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = -1 ∧
      ((B * B : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = -1 ∧
      ((A * B : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        -((B * A : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
  let A₀ : Matrix (Fin 2) (Fin 2) F := !![0, 1; -1, 0]
  let B₀ : Matrix (Fin 2) (Fin 2) F := !![1, 1; 1, -1]
  have hA : A₀.det = 1 := by simp [A₀, Matrix.det_fin_two]
  have hB : B₀.det = 1 := by
    simp only [B₀, Matrix.det_fin_two_of]
    linear_combination -h3
  refine ⟨⟨A₀, hA⟩, ⟨B₀, hB⟩, ?_, ?_, ?_⟩
  · change A₀ * A₀ = -1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A₀, Matrix.mul_apply, Fin.sum_univ_two]
  · change B₀ * B₀ = -1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [B₀, Matrix.mul_apply, Fin.sum_univ_two] <;>
      linear_combination h3
  · change A₀ * B₀ = -(B₀ * A₀)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A₀, B₀, Matrix.mul_apply, Fin.sum_univ_two]

variable {G : Type} [Group G]

theorem exists_quaternion_pair {Y : Subgroup G} (hY : IsSLTwoOver 3 ↥Y) {c : G} (hcY : c ∈ Y)
    (hc1 : c ≠ 1) (hcZ : ∀ y ∈ Y, y * c = c * y) :
    ∃ a ∈ Y, ∃ b ∈ Y, a * a = c ∧ b * b = c ∧ a * b = c * (b * a) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hY
  have h3 : (3 : F) = 0 := by
    have h := FiniteField.cast_card_eq_zero F
    rw [hF] at h
    exact_mod_cast h
  obtain ⟨A, B, hAA, hBB, hAB⟩ := sl2_three_quaternion h3
  have hcen : e ⟨c, hcY⟩ ∈ center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcZ y y.2)
  obtain ⟨r, hr, hrc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcen
  rw [Fintype.card_fin, sq, mul_self_eq_one_iff] at hr
  have hcm : ((e ⟨c, hcY⟩ : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = -1 := by
    rcases hr with rfl | rfl
    · exfalso
      apply hc1
      have h1 : e ⟨c, hcY⟩ = 1 := by
        apply Subtype.ext
        rw [← hrc]
        simp
      have h2 := e.injective (h1.trans (map_one e).symm)
      exact congrArg Subtype.val h2
    · rw [← hrc, map_neg, map_one]
  have key : ∀ u v : ↥Y, ((e u : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = (e v : Matrix (Fin 2) (Fin 2) F) → (u : G) = v := by
    intro u v huv
    exact congrArg Subtype.val (e.injective (Subtype.ext huv))
  refine ⟨e.symm A, (e.symm A).2, e.symm B, (e.symm B).2, ?_, ?_, ?_⟩
  · have := key (e.symm A * e.symm A) ⟨c, hcY⟩ (by
      rw [map_mul, e.apply_symm_apply, hAA, hcm])
    exact this
  · have := key (e.symm B * e.symm B) ⟨c, hcY⟩ (by
      rw [map_mul, e.apply_symm_apply, hBB, hcm])
    exact this
  · have := key (e.symm A * e.symm B) (⟨c, hcY⟩ * (e.symm B * e.symm A)) (by
      rw [map_mul, map_mul, map_mul, e.apply_symm_apply, e.apply_symm_apply, hAB,
        Matrix.SpecialLinearGroup.coe_mul (e ⟨c, hcY⟩) (B * A), hcm, neg_one_mul])
    exact this

theorem mem_inf_of_mul_mem {X₁ X₂ : Subgroup G} {x₁ x₂ : G} (h₁ : x₁ ∈ X₁) (h₂ : x₂ ∈ X₂)
    (h : x₁ * x₂ ∈ X₁ ⊓ X₂) : x₁ ∈ X₁ ⊓ X₂ := by
  refine mem_inf.mpr ⟨h₁, ?_⟩
  have h3 : x₁ = x₁ * x₂ * x₂⁻¹ := by group
  rw [h3]
  exact mul_mem (mem_inf.mp h).2 (inv_mem h₂)

variable [Finite G]

theorem exists_elemTwo_eight {X₁ X₂ : Subgroup G} (hc : X₁ ≤ centralizer (X₂ : Set G)) {c : G}
    (hi : X₁ ⊓ X₂ = zpowers c) (hc2 : orderOf c = 2) (hX₁ : IsSLTwoOver 3 ↥X₁)
    (hX₂ : IsSLTwoOver 3 ↥X₂) :
    ∃ E : Subgroup G, E ≤ X₁ ⊔ X₂ ∧ GrSLit.IsElemTwo E ∧ Nat.card E = 8 := by
  have hcm : c ∈ X₁ ⊓ X₂ := by rw [hi]; exact mem_zpowers c
  have hc1 : c ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hc2; exact absurd hc2 (by decide)
  have hcc : c * c = 1 := by rw [← sq, ← hc2, pow_orderOf_eq_one]
  have hcomm : ∀ a ∈ X₁, ∀ b ∈ X₂, a * b = b * a := fun a ha b hb =>
    (mem_centralizer_iff.mp (hc ha) b hb).symm
  obtain ⟨a₁, ha₁, b₁, hb₁, haa₁, hbb₁, hab₁⟩ := exists_quaternion_pair hX₁ hcm.1 hc1
    (fun y hy => (hcomm y hy c hcm.2))
  obtain ⟨a₂, ha₂, b₂, hb₂, haa₂, hbb₂, hab₂⟩ := exists_quaternion_pair hX₂ hcm.2 hc1
    (fun y hy => (hcomm c hcm.1 y hy).symm)
  have hcX₁ : ∀ y ∈ X₁, y * c = c * y := fun y hy => hcomm y hy c hcm.2
  have hcX₂ : ∀ y ∈ X₂, y * c = c * y := fun y hy => (hcomm c hcm.1 y hy).symm
  have hsq : ∀ y ∈ zpowers c, y * y = 1 := by
    intro y hy
    rcases eq_one_or_eq_of_mem_zpowers_two hc2 hy with rfl | rfl
    · exact mul_one 1
    · exact hcc
  set u := a₁ * a₂ with hu
  set v := b₁ * b₂ with hv
  have huu : u * u = 1 := by
    rw [hu, show a₁ * a₂ * (a₁ * a₂) = a₁ * (a₂ * a₁) * a₂ by group, ← hcomm a₁ ha₁ a₂ ha₂,
      show a₁ * (a₁ * a₂) * a₂ = (a₁ * a₁) * (a₂ * a₂) by group, haa₁, haa₂, hcc]
  have hvv : v * v = 1 := by
    rw [hv, show b₁ * b₂ * (b₁ * b₂) = b₁ * (b₂ * b₁) * b₂ by group, ← hcomm b₁ hb₁ b₂ hb₂,
      show b₁ * (b₁ * b₂) * b₂ = (b₁ * b₁) * (b₂ * b₂) by group, hbb₁, hbb₂, hcc]
  have huv : u * v = v * u := by
    have e1 : u * v = (a₁ * b₁) * (a₂ * b₂) := by
      rw [hu, hv, show a₁ * a₂ * (b₁ * b₂) = a₁ * (a₂ * b₁) * b₂ by group,
        ← hcomm b₁ hb₁ a₂ ha₂]
      group
    have e2 : v * u = (b₁ * a₁) * (b₂ * a₂) := by
      rw [hu, hv, show b₁ * b₂ * (a₁ * a₂) = b₁ * (b₂ * a₁) * a₂ by group,
        ← hcomm a₁ ha₁ b₂ hb₂]
      group
    rw [e1, e2, hab₁, hab₂, show c * (b₁ * a₁) * (c * (b₂ * a₂)) =
      (b₁ * a₁) * c * c * (b₂ * a₂) by
        rw [← hcX₁ (b₁ * a₁) (mul_mem hb₁ ha₁)]; group, mul_assoc (b₁ * a₁) c c, hcc, mul_one]
  have hcu : ∀ y ∈ zpowers c, y * u = u * y := by
    intro y hy
    rcases eq_one_or_eq_of_mem_zpowers_two hc2 hy with rfl | rfl
    · rw [one_mul, mul_one]
    · rw [hu, ← mul_assoc, ← hcX₁ a₁ ha₁, mul_assoc, ← hcX₂ a₂ ha₂, mul_assoc]
  have hE₁ : GrSLit.IsElemTwo (zpowers c) := ⟨fun x hx y hy => by
    rcases eq_one_or_eq_of_mem_zpowers_two hc2 hx with rfl | rfl <;>
      rcases eq_one_or_eq_of_mem_zpowers_two hc2 hy with rfl | rfl <;> simp, hsq⟩
  have hu1 : u ∉ zpowers c := by
    intro h1
    have h2 := mem_inf_of_mul_mem ha₁ ha₂ (hi ▸ h1)
    rw [hi] at h2
    have h3 := hsq a₁ h2
    rw [haa₁] at h3
    exact hc1 h3
  have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact huu)
    (fun h1 => hu1 (by rw [h1]; exact one_mem _))
  have hE₂ := Lemma47.isElemTwo_sup_zpowers hE₁ (fun y hy => hcu y hy) huu
  have hE₂c := Lemma47.card_sup_zpowers (fun y hy => hcu y hy) hu2 hu1
  have hcv : ∀ y ∈ (zpowers c ⊔ zpowers u : Subgroup G), y * v = v * y := by
    intro y hy
    obtain ⟨y', hy', rfl | rfl⟩ := Lemma47.mem_sup_zpowers_two (fun y hy => hcu y hy) hu2 hy
    · rcases eq_one_or_eq_of_mem_zpowers_two hc2 hy' with rfl | rfl
      · rw [one_mul, mul_one]
      · rw [hv, ← mul_assoc, ← hcX₁ b₁ hb₁, mul_assoc, ← hcX₂ b₂ hb₂, mul_assoc]
    · have h1 : y' * v = v * y' := by
        rcases eq_one_or_eq_of_mem_zpowers_two hc2 hy' with rfl | rfl
        · rw [one_mul, mul_one]
        · rw [hv, ← mul_assoc, ← hcX₁ b₁ hb₁, mul_assoc, ← hcX₂ b₂ hb₂, mul_assoc]
      rw [mul_assoc, huv, ← mul_assoc, h1, mul_assoc]
  have hv1 : v ∉ (zpowers c ⊔ zpowers u : Subgroup G) := by
    intro h1
    obtain ⟨y', hy', h2 | h2⟩ := Lemma47.mem_sup_zpowers_two (fun y hy => hcu y hy) hu2 h1
    · have h3 := mem_inf_of_mul_mem hb₁ hb₂ (by rw [hi, ← hv, h2]; exact hy')
      rw [hi] at h3
      have h4 := hsq b₁ h3
      rw [hbb₁] at h4
      exact hc1 h4
    ·
      have hy'a : a₁ * y' = y' * a₁ := by
        rcases eq_one_or_eq_of_mem_zpowers_two hc2 hy' with rfl | rfl
        · rw [one_mul, mul_one]
        · exact hcX₁ a₁ ha₁
      have h3 : a₁⁻¹ * b₁ * (b₂ * a₂⁻¹) = y' := by
        calc a₁⁻¹ * b₁ * (b₂ * a₂⁻¹) = a₁⁻¹ * (b₁ * b₂) * a₂⁻¹ := by group
          _ = a₁⁻¹ * (y' * (a₁ * a₂)) * a₂⁻¹ := by rw [← hv, h2]
          _ = a₁⁻¹ * (y' * a₁) := by group
          _ = a₁⁻¹ * (a₁ * y') := by rw [hy'a]
          _ = y' := by group
      have h4 := mem_inf_of_mul_mem (mul_mem (inv_mem ha₁) hb₁) (mul_mem hb₂ (inv_mem ha₂))
        (by rw [h3, hi]; exact hy')
      rw [hi] at h4
      have h5 : a₁ * b₁ = b₁ * a₁ := by
        have h6 : b₁ = a₁ * (a₁⁻¹ * b₁) := by group
        rcases eq_one_or_eq_of_mem_zpowers_two hc2 h4 with h7 | h7 <;> rw [h6, h7]
        · group
        · rw [mul_assoc a₁ c a₁, ← hcX₁ a₁ ha₁]
      rw [h5] at hab₁
      apply hc1
      have h8 : 1 * (b₁ * a₁) = c * (b₁ * a₁) := by rw [one_mul]; exact hab₁
      exact (mul_right_cancel h8).symm
  have hv2 : orderOf v = 2 := orderOf_eq_prime (by rw [sq]; exact hvv)
    (fun h1 => hv1 (by rw [h1]; exact one_mem _))
  refine ⟨(zpowers c ⊔ zpowers u) ⊔ zpowers v, ?_,
    Lemma47.isElemTwo_sup_zpowers hE₂ hcv hvv, ?_⟩
  · refine sup_le (sup_le ?_ ?_) ?_ <;> rw [zpowers_le]
    · exact mem_sup_left hcm.1
    · exact mul_mem (mem_sup_left ha₁) (mem_sup_right ha₂)
    · exact mul_mem (mem_sup_left hb₁) (mem_sup_right hb₂)
  · rw [Lemma47.card_sup_zpowers hcv hv2 hv1, hE₂c, Nat.card_zpowers, hc2]

theorem exists_elemTwo_thirtyTwo_of {tb bb : G} (hbbZ : bb ∈ center G) (hbb2 : orderOf bb = 2)
    (htb2 : orderOf tb = 2) {A : Subgroup G} (hA : GrSLit.IsElemTwo A) (hA8 : Nat.card A = 8)
    (hAt : A ≤ centralizer {tb}) (hbbA : bb ∉ A) (htbA : tb ∉ (A ⊔ zpowers bb : Subgroup G)) :
    ∃ E : Subgroup G, E ≤ centralizer {tb} ∧ GrSLit.IsElemTwo E ∧ Nat.card E = 32 := by
  have hbbc : ∀ g : G, g * bb = bb * g := fun g => (mem_center_iff.mp hbbZ g)
  have hE1c : ∀ a ∈ A, a * bb = bb * a := fun a _ => hbbc a
  have hE1 := Lemma47.isElemTwo_sup_zpowers hA hE1c (by rw [← sq, ← hbb2, pow_orderOf_eq_one])
  have hE1card := Lemma47.card_sup_zpowers hE1c hbb2 hbbA
  have htbA' : ∀ a ∈ A, a * tb = tb * a := fun a ha => mem_centralizer_singleton_iff.mp (hAt ha)
  have hE2c : ∀ a ∈ (A ⊔ zpowers bb : Subgroup G), a * tb = tb * a := by
    intro a ha
    obtain ⟨a', ha', h3 | h3⟩ := Lemma47.mem_sup_zpowers_two hE1c hbb2 ha
    · rw [h3]; exact htbA' a' ha'
    · rw [h3, mul_assoc, ← hbbc tb, ← mul_assoc, htbA' a' ha', mul_assoc]
  refine ⟨(A ⊔ zpowers bb : Subgroup G) ⊔ zpowers tb, ?_,
    Lemma47.isElemTwo_sup_zpowers hE1 hE2c (by rw [← sq, ← htb2, pow_orderOf_eq_one]), ?_⟩
  · refine sup_le (sup_le hAt ?_) ?_
    · rw [zpowers_le]
      exact mem_centralizer_singleton_iff.mpr (hbbc tb).symm
    · rw [zpowers_le]
      exact mem_centralizer_singleton_iff.mpr rfl
  · rw [Lemma47.card_sup_zpowers hE2c htb2 htbA, hE1card, hA8]

end CFSG.ComponentClassification.HarrisLit.Q81
