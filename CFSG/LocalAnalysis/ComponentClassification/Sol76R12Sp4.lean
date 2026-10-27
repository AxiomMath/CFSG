module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76R12Local
public import CFSG.LieType.Steinberg.CentralExt.Families
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticModelOuterTwoPart

public section

namespace CFSG.ComponentClassification.Sol76T13.R12

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Matrices

variable (k : Type) [Field k]

@[expose] noncomputable def sp4D : Matrix (Fin 2) (Fin 2) k := diagonal ![-1, 1]

theorem sp4D_mul_self : sp4D k * sp4D k = 1 := by
  rw [sp4D, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

theorem sp4D_transpose : (sp4D k)ᵀ = sp4D k := diagonal_transpose _

@[expose] noncomputable def sp4J : GL (Fin 2 ⊕ Fin 2) k :=
  ⟨fromBlocks 0 1 (-1) 0, fromBlocks 0 (-1) 1 0, by rw [fromBlocks_multiply]; simp,
    by rw [fromBlocks_multiply]; simp⟩

@[expose] noncomputable def sp4T : GL (Fin 2 ⊕ Fin 2) k :=
  ⟨fromBlocks (sp4D k) 0 0 (sp4D k), fromBlocks (sp4D k) 0 0 (sp4D k),
    by rw [fromBlocks_multiply]; simp [sp4D_mul_self],
    by rw [fromBlocks_multiply]; simp [sp4D_mul_self]⟩

theorem sp4J_mem : sp4J k ∈ StatedSp 2 k := by
  rw [LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff]
  change (fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k)ᵀ *
    fromBlocks 0 1 (-1) 0 * fromBlocks 0 1 (-1) 0 = fromBlocks 0 1 (-1) 0
  rw [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp

theorem sp4T_mem : sp4T k ∈ StatedSp 2 k := by
  rw [LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff]
  change (fromBlocks (sp4D k) 0 0 (sp4D k) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k)ᵀ *
    fromBlocks 0 1 (-1) 0 * fromBlocks (sp4D k) 0 0 (sp4D k) = fromBlocks 0 1 (-1) 0
  rw [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp [sp4D_transpose, sp4D_mul_self]

@[expose] noncomputable def spJ : StatedSp 2 k := ⟨sp4J k, sp4J_mem k⟩

@[expose] noncomputable def spT : StatedSp 2 k := ⟨sp4T k, sp4T_mem k⟩

theorem spT_mul_self : spT k * spT k = 1 := by
  apply Subtype.ext
  apply Units.ext
  change fromBlocks (sp4D k) 0 0 (sp4D k) * fromBlocks (sp4D k) 0 0 (sp4D k) = 1
  rw [fromBlocks_multiply]
  simp [sp4D_mul_self]

theorem spJ_mul_spT : spJ k * spT k = spT k * spJ k := by
  apply Subtype.ext
  apply Units.ext
  change fromBlocks 0 1 (-1) 0 * fromBlocks (sp4D k) 0 0 (sp4D k) =
    fromBlocks (sp4D k) 0 0 (sp4D k) * fromBlocks 0 1 (-1) 0
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp

theorem spJ_sq_mem_center : spJ k * spJ k ∈ center (StatedSp 2 k) := by
  rw [LieType.Universal.Symplectic.center_eq 2 k, mem_subgroupOf]
  refine ⟨-1, Units.ext ?_⟩
  rw [GeneralLinearGroup.coe_scalar]
  change Matrix.scalar (Fin 2 ⊕ Fin 2) (-1 : k) =
    fromBlocks 0 1 (-1) 0 * fromBlocks 0 1 (-1) 0
  rw [fromBlocks_multiply, map_neg, map_one, ← fromBlocks_one, fromBlocks_neg]
  simp

variable {k}

theorem spJ_sq_ne_one (hk : ringChar k ≠ 2) : spJ k * spJ k ≠ 1 := by
  intro h
  have h1 := congrArg (fun x : StatedSp 2 k =>
    ((x : GL (Fin 2 ⊕ Fin 2) k) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k)
      (Sum.inl 0) (Sum.inl 0)) h
  change (fromBlocks 0 1 (-1) 0 * fromBlocks 0 1 (-1) 0 :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) (Sum.inl 0) (Sum.inl 0) =
      (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) (Sum.inl 0) (Sum.inl 0) at h1
  rw [fromBlocks_multiply] at h1
  simp at h1
  exact Ring.neg_one_ne_one_of_char_ne_two hk h1

theorem spT_not_mem_center (hk : ringChar k ≠ 2) : spT k ∉ center (StatedSp 2 k) := by
  rw [LieType.Universal.Symplectic.center_eq 2 k, mem_subgroupOf]
  rintro ⟨c, hc⟩
  have h0 := congrArg (fun x : GL (Fin 2 ⊕ Fin 2) k =>
    (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) (Sum.inl 0) (Sum.inl 0)) hc
  have h1 := congrArg (fun x : GL (Fin 2 ⊕ Fin 2) k =>
    (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) (Sum.inl 1) (Sum.inl 1)) hc
  change (Matrix.scalar (Fin 2 ⊕ Fin 2) (c : k)) (Sum.inl 0) (Sum.inl 0) =
    fromBlocks (sp4D k) 0 0 (sp4D k) (Sum.inl 0) (Sum.inl 0) at h0
  change (Matrix.scalar (Fin 2 ⊕ Fin 2) (c : k)) (Sum.inl 1) (Sum.inl 1) =
    fromBlocks (sp4D k) 0 0 (sp4D k) (Sum.inl 1) (Sum.inl 1) at h1
  simp [sp4D] at h0 h1
  have h2 : ((-1 : kˣ) : k) = ((1 : kˣ) : k) := congrArg Units.val (h0.symm.trans h1)
  rw [Units.val_neg, Units.val_one] at h2
  exact Ring.neg_one_ne_one_of_char_ne_two hk h2

theorem card_center_sp4 [Finite k] (hk : ringChar k ≠ 2) :
    Nat.card (center (StatedSp 2 k)) = 2 := by
  have := Fintype.ofFinite k
  rw [LieType.Universal.Symplectic.center_eq 2 k,
    show (StatedScalars (Fin 2 ⊕ Fin 2) k).subgroupOf (StatedSp 2 k) =
      LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars 2 k from rfl,
    LocalAnalysis.ComponentInitial.card_spScalars_eq_gcd k (r := 2) (by norm_num)]
  have hodd : Fintype.card k % 2 = 1 := by
    have h := (FiniteField.even_card_iff_char_two (F := k)).not.mp hk
    omega
  rw [Nat.card_eq_fintype_card]
  have hpos : 0 < Fintype.card k := Fintype.card_pos
  exact Nat.gcd_eq_left (by omega)

end Matrices

theorem isPGroup_center_of_pPrimeCore_eq_bot {Q : Type} [Group Q] [Finite Q]
    (hO : pPrimeCore 2 Q = ⊥) : IsPGroup 2 (center Q) := by
  intro c
  obtain ⟨a, m, hm2, hcm⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos (c : Q)).ne' 2 (by norm_num)
  set c' := (c : Q) ^ (2 ^ a) with hc'
  have hoc' : orderOf c' = m := by
    rw [hc', orderOf_pow' _ (pow_ne_zero _ two_ne_zero), hcm, Nat.gcd_mul_right_left,
      Nat.mul_div_cancel_left _ (by positivity)]
  have hc'Z : c' ∈ center Q := pow_mem c.2 _
  have hnorm : (zpowers c').Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hnZ : n ∈ center Q := (zpowers_le.mpr hc'Z) hn
    rw [mem_center_iff.mp hnZ g, mul_inv_cancel_right]
    exact hn
  have hle : zpowers c' ≤ pPrimeCore 2 Q := le_sSup ⟨hnorm, by
    rw [Nat.card_zpowers, hoc']
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hm2⟩
  rw [hO, le_bot_iff, zpowers_eq_bot] at hle
  exact ⟨a, Subtype.ext (by simpa [hc'] using hle)⟩

theorem commutatorElement_mul_central {Q : Type} [Group Q] {a b c d : Q} (hc : c ∈ center Q)
    (hd : d ∈ center Q) : ⁅a * c, b * d⁆ = ⁅a, b⁆ := by
  have hc' := mem_center_iff.mp hc
  have hd' := mem_center_iff.mp hd
  rw [commutatorElement_def, commutatorElement_def]
  calc a * c * (b * d) * (a * c)⁻¹ * (b * d)⁻¹
      = a * (c * b) * d * c⁻¹ * a⁻¹ * d⁻¹ * b⁻¹ := by group
    _ = a * (b * c) * d * c⁻¹ * a⁻¹ * d⁻¹ * b⁻¹ := by rw [hc' b]
    _ = a * b * (c * d * c⁻¹) * a⁻¹ * d⁻¹ * b⁻¹ := by group
    _ = a * b * d * a⁻¹ * d⁻¹ * b⁻¹ := by rw [← hc' d]; group
    _ = a * b * (d * a⁻¹) * d⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * d) * d⁻¹ * b⁻¹ := by rw [← hd' a⁻¹]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem rankTwoCentral_of_sp4 {Q : Type} [Group Q] [Finite Q] (hQ : IsQuasisimple Q)
    (hO : pPrimeCore 2 Q = ⊥) {k : Type} [Field k] [Finite k] (hk : ringChar k ≠ 2)
    (e : Q ⧸ center Q ≃* StatedProj (StatedSp 2 k)) {z : Q} (hzZ : z ∈ center Q)
    (hz2 : orderOf z = 2) :
    (∀ w ∈ center Q, w ^ 4 = 1 → w = 1 ∨ w = z) ∧
      ∃ s t : Q, t * t = 1 ∧ t ∉ center Q ∧ s * s = z ∧ s * t = t * s := by
  classical
  set Sp := StatedSp 2 k with hSp
  set Z := (StatedScalars (Fin 2 ⊕ Fin 2) k).subgroupOf Sp with hZdef
  set proj : Sp →* StatedProj Sp := QuotientGroup.mk' Z with hproj
  set ρ : Q →* StatedProj Sp := e.toMonoidHom.comp (QuotientGroup.mk' (center Q)) with hρdef
  have hρ1 : ∀ y : Q, ρ y = 1 ↔ y ∈ center Q := by
    intro y
    rw [hρdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hproj1 : ∀ x : Sp, proj x = 1 ↔ x ∈ center Sp := by
    intro x
    rw [hproj, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hZdef,
      ← LieType.Universal.Symplectic.center_eq 2 k]
  have hZcard : Nat.card Z = 2 := by
    rw [hZdef, ← LieType.Universal.Symplectic.center_eq 2 k]
    exact card_center_sp4 hk
  set E : Subgroup (Sp × Q) :=
    (proj.comp (MonoidHom.fst Sp Q)).eqLocus (ρ.comp (MonoidHom.snd Sp Q)) with hEdef
  have hmemE : ∀ p : Sp × Q, p ∈ E ↔ proj p.1 = ρ p.2 := fun _ => Iff.rfl
  set πE : ↥E →* Sp := (MonoidHom.fst Sp Q).comp E.subtype with hπEdef
  have hπE : Function.Surjective πE := by
    intro x
    obtain ⟨y, hy⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (center Q))) (proj x)
    exact ⟨⟨(x, y), (hmemE _).mpr hy.symm⟩, rfl⟩
  have hkerE : ∀ g : ↥E, πE g = 1 → (g : Sp × Q).2 ∈ center Q := by
    intro g hg
    have h1 : (g : Sp × Q).1 = 1 := hg
    have h2 := (hmemE _).mp g.2
    rw [h1, map_one] at h2
    exact (hρ1 _).mp h2.symm
  have hker : πE.ker ≤ center ↥E := by
    intro g hg
    rw [mem_center_iff]
    intro h
    have h1 : (g : Sp × Q).1 = 1 := hg
    have h2 := mem_center_iff.mp (hkerE g hg) (h : Sp × Q).2
    apply Subtype.ext
    apply Prod.ext
    · change (h : Sp × Q).1 * (g : Sp × Q).1 = (g : Sp × Q).1 * (h : Sp × Q).1
      rw [h1, one_mul, mul_one]
    · exact h2
  have h2 : IsPGroup 2 πE.ker := by
    intro g
    obtain ⟨n, hn⟩ := isPGroup_center_of_pPrimeCore_eq_bot hO
      ⟨((g : ↥E) : Sp × Q).2, hkerE g g.2⟩
    have h1 : ((g : ↥E) : Sp × Q).1 = 1 := g.2
    refine ⟨n, Subtype.ext (Subtype.ext (Prod.ext ?_ ?_))⟩
    · change ((g : ↥E) : Sp × Q).1 ^ 2 ^ n = 1
      rw [h1, one_pow]
    · change ((g : ↥E) : Sp × Q).2 ^ 2 ^ n = 1
      exact congrArg Subtype.val hn
  obtain ⟨σ, hσ, -, -⟩ :=
    LieType.Steinberg.odd_symplectic_central_two_extension_splitting hk 2 hπE hker h2
  set τ : Sp →* Q := (MonoidHom.snd Sp Q).comp (E.subtype.comp σ) with hτdef
  have hτρ : ∀ x : Sp, ρ (τ x) = proj x := by
    intro x
    have h1 := (hmemE _).mp (σ x).2
    have h2 : ((σ x : ↥E) : Sp × Q).1 = x := hσ x
    rw [h2] at h1
    exact h1.symm
  have hτZ : ∀ y : Q, ∃ x : Sp, ∃ c ∈ center Q, y = τ x * c := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective Z (ρ y)
    have hx' : proj x = ρ y := hx
    refine ⟨x, (τ x)⁻¹ * y, (hρ1 _).mp ?_, by group⟩
    rw [map_mul, map_inv, hτρ, hx', inv_mul_cancel]
  have hτ : Function.Surjective τ := by
    have hperf : Group.IsPerfect Q := hQ.1
    have hle : commutator Q ≤ τ.range := by
      refine commutator_le.mpr fun y₁ _ y₂ _ => ?_
      obtain ⟨x₁, c₁, hc₁, rfl⟩ := hτZ y₁
      obtain ⟨x₂, c₂, hc₂, rfl⟩ := hτZ y₂
      rw [commutatorElement_mul_central hc₁ hc₂, ← map_commutatorElement]
      exact ⟨_, rfl⟩
    rw [Group.IsPerfect.commutator_eq_top, top_le_iff] at hle
    exact MonoidHom.range_eq_top.mp hle
  have hcardSp : Nat.card Sp = Nat.card (StatedProj Sp) * 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
    rw [hZcard] at h
    exact h
  have hcardQ : Nat.card Q = Nat.card (StatedProj Sp) * Nat.card (center Q) := by
    rw [← Nat.card_congr e.toEquiv]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup (center Q)
  have hle : Nat.card Q ≤ Nat.card Sp := Nat.card_le_card_of_surjective τ hτ
  have hPpos : 0 < Nat.card (StatedProj Sp) := Nat.card_pos
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz2
    norm_num at hz2
  have hzcard : Nat.card (zpowers z) = 2 := by rw [Nat.card_zpowers, hz2]
  have hZQ : center Q = zpowers z := by
    refine (eq_of_le_of_card_ge (zpowers_le.mpr hzZ) ?_).symm
    rw [hzcard]
    have : Nat.card (center Q) ≤ 2 := by
      by_contra h
      have h3 : Nat.card (StatedProj Sp) * 3 ≤ Nat.card (StatedProj Sp) * Nat.card (center Q) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    exact this
  have hzz : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have hzpow : ∀ w ∈ zpowers z, w = 1 ∨ w = z := by
    intro w hw
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hw
    have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two, hzz]
    rw [← Int.mul_ediv_add_emod i 2, _root_.zpow_add, _root_.zpow_mul, h2, _root_.one_zpow, one_mul]
    rcases Int.emod_two_eq_zero_or_one i with h | h
    · left
      rw [h, _root_.zpow_zero]
    · right
      rw [h, _root_.zpow_one]
  have hJ2 : τ (spJ k * spJ k) = z := by
    have hcen : τ (spJ k * spJ k) ∈ center Q := by
      rw [mem_center_iff]
      intro y
      obtain ⟨x, rfl⟩ := hτ y
      rw [← map_mul, ← map_mul, (mem_center_iff.mp (spJ_sq_mem_center k) x)]
    rcases hzpow _ (hZQ ▸ hcen) with h | h
    · exfalso
      apply hz1
      have hker2 : 2 ≤ Nat.card τ.ker := by
        have h1 : (spJ k * spJ k) ∈ τ.ker := h
        have h3 : (1 : Sp) ∈ τ.ker := one_mem _
        have hne : (⟨spJ k * spJ k, h1⟩ : ↥τ.ker) ≠ ⟨1, h3⟩ := fun h4 =>
          spJ_sq_ne_one hk (congrArg Subtype.val h4)
        exact Finite.one_lt_card_iff_nontrivial.mpr ⟨⟨_, _, hne⟩⟩
      have hcard : Nat.card Sp = Nat.card Q * Nat.card τ.ker := by
        rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective τ hτ).toEquiv]
        exact Subgroup.card_eq_card_quotient_mul_card_subgroup τ.ker
      have hZ1 : Nat.card (center Q) ≤ 1 := by
        by_contra h5
        have h6 : Nat.card Q * 2 ≤ Nat.card Q * Nat.card τ.ker := Nat.mul_le_mul_left _ hker2
        have h7 : Nat.card (StatedProj Sp) * 2 ≤ Nat.card (StatedProj Sp) * Nat.card (center Q) :=
          Nat.mul_le_mul_left _ (by omega)
        nlinarith
      have hbot : center Q = ⊥ := (eq_bot_iff_card _).mpr (le_antisymm hZ1 Nat.card_pos)
      rw [hbot] at hzZ
      exact (mem_bot.mp hzZ)
    · exact h
  refine ⟨fun w hw _ => hzpow w (hZQ ▸ hw), τ (spJ k), τ (spT k), ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, spT_mul_self, map_one]
  · intro h
    apply spT_not_mem_center hk
    rw [← hproj1, ← hτρ]
    exact (hρ1 _).mpr h
  · rw [← map_mul, hJ2]
  · rw [← map_mul, ← map_mul, spJ_mul_spT]

@[expose] def QuasisimpleRankTwoSymplecticInput : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsQuasisimple Q → pPrimeCore 2 Q = ⊥ →
    Blueprint.Catalog (Q ⧸ center Q) → CFSG.pRank 2 Q = 2 → (∃ z ∈ center Q, orderOf z = 2) →
      ∃ (k : Type) (_ : Field k) (_ : Finite k), ringChar k ≠ 2 ∧
        Nonempty (Q ⧸ center Q ≃* StatedProj (StatedSp 2 k))

theorem quasisimpleRankTwoCentralInput_of_symplectic (h : QuasisimpleRankTwoSymplecticInput) :
    QuasisimpleRankTwoCentralInput := by
  intro Q _ _ hQ hO hcat hr z hz hz2
  obtain ⟨k, _, _, hk, ⟨e⟩⟩ := h Q hQ hO hcat hr ⟨z, hz, hz2⟩
  exact rankTwoCentral_of_sp4 hQ hO hk e hz hz2

end CFSG.ComponentClassification.Sol76T13.R12
