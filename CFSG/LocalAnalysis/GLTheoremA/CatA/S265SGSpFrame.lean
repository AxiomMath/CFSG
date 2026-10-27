module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitSpNsDiag
import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitSpNsCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open
open CFSG.StandardType.WitSpNs (planeMat planeMat_apply planeMat_injective planeMat_mul
  planeMat_one exists_symplecticPlaneFrame)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)

private theorem frameM_pow_three {F : Type} [Field F]
    {M : Matrix (Fin 2) (Fin 2) F} (hM : M * M + M + 1 = 0) : M ^ 3 = 1 := by
  have : M ^ 3 - 1 = (M - 1) * (M * M + M + 1) := by noncomm_ring
  rwa [hM, mul_zero, sub_eq_zero] at this

private theorem frameM_natCast_eq_of_pow_eq {F : Type} [Field F] [CharP F 2]
    {M : Matrix (Fin 2) (Fin 2) F} (hM : M * M + M + 1 = 0) {a b : ℕ} (h : M ^ a = M ^ b) :
    (a : ZMod 3) = b := by
  have hM3 := frameM_pow_three hM
  let u : (Matrix (Fin 2) (Fin 2) F)ˣ :=
    ⟨M, M ^ 2, by rw [← pow_succ', hM3], by rw [← pow_succ, hM3]⟩
  have hu1 : u ≠ 1 := fun h1 => by
    have hM1 : M = 1 := congrArg Units.val h1
    rw [hM1, mul_one, CharTwo.add_self_eq_zero, zero_add] at hM
    exact one_ne_zero hM
  have hu3 : u ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hM3)
  have hab : u ^ a = u ^ b :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]; exact h)
  rw [pow_eq_pow_iff_modEq, orderOf_eq_prime hu3 hu1] at hab
  exact (ZMod.natCast_eq_natCast_iff _ _ _).2 hab

private theorem exists_planeChar {F : Type} [Field F] [CharP F 2] {ℓ : ℕ}
    {M : Matrix (Fin 2) (Fin 2) F} (hM : M * M + M + 1 = 0) (E : Subgroup (StatedSp ℓ F))
    (A₀ : StatedSp ℓ F)
    (he : ∀ g : ↥E, ∃ e : Fin ℓ → ℕ, mat ℓ F (A₀⁻¹ * g * A₀) = planeMat fun j => M ^ e j) :
    ∃ k : Fin ℓ → ↥E →* Multiplicative (ZMod 3), ∀ g : ↥E,
      mat ℓ F (A₀⁻¹ * g * A₀) = planeMat fun j => M ^ (Multiplicative.toAdd (k j g)).val := by
  choose e he using he
  have hM3 := frameM_pow_three hM
  have hmod : ∀ a : ℕ, M ^ a = M ^ (a % 3) := fun a => by
    conv_lhs => rw [← Nat.div_add_mod a 3, pow_add, pow_mul, hM3, one_pow, one_mul]
  refine ⟨fun j => {
    toFun := fun g => Multiplicative.ofAdd ((e g j : ℕ) : ZMod 3)
    map_one' := ?_
    map_mul' := fun g h => ?_ }, fun g => ?_⟩
  · have h1 := he 1
    rw [Subgroup.coe_one, mul_one, inv_mul_cancel, map_one, ← planeMat_one] at h1
    have h2 := congrFun (planeMat_injective h1) j
    rw [← pow_zero M] at h2
    rw [frameM_natCast_eq_of_pow_eq hM h2.symm, Nat.cast_zero, ofAdd_zero]
  · have h1 := he (g * h)
    rw [Subgroup.coe_mul, show A₀⁻¹ * (↑g * ↑h) * A₀ = (A₀⁻¹ * g * A₀) * (A₀⁻¹ * h * A₀) by
      group, map_mul, he g, he h, planeMat_mul] at h1
    have h2 := congrFun (planeMat_injective h1) j
    rw [← pow_add] at h2
    rw [frameM_natCast_eq_of_pow_eq hM h2.symm, Nat.cast_add, ofAdd_add]
  · rw [he g]
    congr 1
    funext j
    rw [MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, ZMod.val_natCast, ← hmod]

private theorem diagonal_sumElim_eq_planeMat {F : Type} [Field F] {ℓ : ℕ} (x y : Fin ℓ → F) :
    Matrix.diagonal (Sum.elim x y) = planeMat fun j => Matrix.diagonal ![x j, y j] := by
  ext a b
  rw [planeMat_apply]
  rcases a with i | i <;> rcases b with j | j <;> by_cases hij : i = j <;>
    simp [hij, Matrix.diagonal_apply]

private theorem cube_root_quad {F : Type} [Field F] {x : F} (h3 : x ^ 3 = 1) (h1 : x ≠ 1) :
    x * x + x + 1 = 0 := by
  have : (x - 1) * (x * x + x + 1) = 0 := by rw [← sub_eq_zero.2 h3]; ring
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 h1)

private theorem exists_frame_split {F : Type} [Field F] [Finite F] [CharP F 2] {ℓ : ℕ}
    (h3 : 3 ∣ Nat.card F - 1) (E : Subgroup (StatedSp ℓ F))
    (hEc : ∀ g ∈ E, ∀ g' ∈ E, Commute g g') (hE3 : ∀ g ∈ E, g ^ 3 = 1) :
    ∃ (A₀ : StatedSp ℓ F) (M : Matrix (Fin 2) (Fin 2) F), M.det = 1 ∧ M * M + M + 1 = 0 ∧
      ∀ g : ↥E, ∃ e : Fin ℓ → ℕ, mat ℓ F (A₀⁻¹ * g * A₀) = planeMat fun j => M ^ e j := by
  classical
  haveI := Fintype.ofFinite F
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Fˣ, orderOf ζ = 3 := exists_prime_orderOf_dvd_card 3
    (by rw [Fintype.card_units, ← Nat.card_eq_fintype_card]; exact h3)
  have hζp : IsPrimitiveRoot (ζ : F) 3 := IsPrimitiveRoot.coe_units_iff.2 (hζ ▸ .orderOf ζ)
  have hζ1 : (ζ : F) ≠ 1 := hζp.ne_one (by norm_num)
  have h30 : ((3 : ℕ) : F) ≠ 0 := by
    rw [show ((3 : ℕ) : F) = 1 + 1 + 1 by push_cast; ring, CharTwo.add_self_eq_zero, zero_add]
    exact one_ne_zero
  set E' : Subgroup (GL (Fin ℓ ⊕ Fin ℓ) F) := E.map (StatedSp ℓ F).subtype
  have hE'Sp : E' ≤ CFSG.Assembly.LargeEvenSpGroup F ℓ := by rintro _ ⟨g, -, rfl⟩; exact g.2
  have hE'el : IsElemAbelian 3 E' := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨a, ha, rfl⟩⟩ := a
      obtain ⟨_, ⟨b, hb, rfl⟩⟩ := b
      show (a : GL (Fin ℓ ⊕ Fin ℓ) F) * b = b * a
      exact congrArg Subtype.val (hEc a ha b hb).eq
    · rintro _ ⟨g, hg, rfl⟩
      rw [← map_pow, hE3 g hg, map_one]
  obtain ⟨P, hP, u, hu⟩ := CFSG.StandardType.TableBSymp.exists_symplectic_weight_basis_GL
    h30 hζ hE'Sp hE'el
  refine ⟨⟨P, hP⟩, Matrix.diagonal ![(ζ : F), (ζ : F)⁻¹], ?_, ?_, fun g => ?_⟩
  · simp [Matrix.det_diagonal, Fin.prod_univ_two, hζp.ne_zero (by norm_num)]
  · have h0 := cube_root_quad (hζp.pow_eq_one) hζ1
    have h1 := cube_root_quad (x := (ζ : F)⁻¹) (by rw [inv_pow, hζp.pow_eq_one, inv_one])
      (inv_ne_one.2 hζ1)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h0, h1]
  · set g' : ↥E' := ⟨g, Subgroup.mem_map_of_mem _ g.2⟩
    have hg'3 : g' ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      show ((g : StatedSp ℓ F) : GL (Fin ℓ ⊕ Fin ℓ) F) ^ 3 = 1
      rw [← Subgroup.coe_pow, hE3 g g.2, Subgroup.coe_one])
    choose e hue using fun i => (hζp.eq_pow_of_pow_eq_one (ξ := ((u i g' : Fˣ) : F))
      (by rw [← Units.val_pow_eq_pow_val, ← map_pow, hg'3, map_one, Units.val_one])).imp
        fun _ h => h.2
    refine ⟨e, ?_⟩
    have hu' : ((g : StatedSp ℓ F) : GL (Fin ℓ ⊕ Fin ℓ) F) * P =
        P * TauCeti.diagGL (CFSG.StandardType.TableBSymp.pairedUnits fun i => u i g') := hu g'
    have hPg : P⁻¹ * ((g : StatedSp ℓ F) : GL (Fin ℓ ⊕ Fin ℓ) F) * P =
        TauCeti.diagGL (CFSG.StandardType.TableBSymp.pairedUnits fun i => u i g') := by
      rw [mul_assoc, hu', inv_mul_cancel_left]
    have hmat : mat ℓ F ((⟨P, hP⟩ : StatedSp ℓ F)⁻¹ * g * ⟨P, hP⟩) =
        ((P⁻¹ * ((g : StatedSp ℓ F) : GL (Fin ℓ ⊕ Fin ℓ) F) * P : GL (Fin ℓ ⊕ Fin ℓ) F) :
          Matrix (Fin ℓ ⊕ Fin ℓ) (Fin ℓ ⊕ Fin ℓ) F) := rfl
    rw [hmat, hPg, TauCeti.diagGL_coe]
    rw [show (fun a => ((CFSG.StandardType.TableBSymp.pairedUnits (fun i => u i g') a : Fˣ) : F))
        = Sum.elim (fun i => (ζ : F) ^ e i) (fun i => (ζ : F)⁻¹ ^ e i) by
      funext a
      rcases a with i | i
      · simp [CFSG.StandardType.TableBSymp.pairedUnits, hue i]
      · simp [CFSG.StandardType.TableBSymp.pairedUnits, ← hue i, inv_pow]]
    rw [diagonal_sumElim_eq_planeMat]
    congr 1
    funext j
    rw [Matrix.diagonal_pow]
    congr 1
    funext i
    fin_cases i <;> rfl

private theorem exists_frame_nonsplit {F : Type} [Field F] [Finite F] [CharP F 2] {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) (h3 : 3 ∣ Nat.card F + 1) (E : Subgroup (StatedSp ℓ F))
    (hEc : ∀ g ∈ E, ∀ g' ∈ E, Commute g g') (hE3 : ∀ g ∈ E, g ^ 3 = 1) :
    ∃ (A₀ : StatedSp ℓ F) (M : Matrix (Fin 2) (Fin 2) F), M.det = 1 ∧ M * M + M + 1 = 0 ∧
      ∀ g : ↥E, ∃ e : Fin ℓ → ℕ, mat ℓ F (A₀⁻¹ * g * A₀) = planeMat fun j => M ^ e j := by
  set s : Set (Set (StatedSp ℓ F)) :=
    {X | (∀ a ∈ X, ∀ b ∈ X, Commute a b) ∧ ∀ a ∈ X, a ^ 3 = 1}
  obtain ⟨X, hEX, hXmax⟩ := (Set.toFinite s).exists_le_maximal (a := (E : Set (StatedSp ℓ F)))
    ⟨hEc, hE3⟩
  obtain ⟨hXc, hX3⟩ := hXmax.prop
  obtain ⟨A₀, T, hT3, hTu, -, hfr⟩ := exists_symplecticPlaneFrame hℓ Nat.prime_three h3 (· ∈ X)
    (fun a b ha hb => hXc a ha b hb) hX3 fun Y hY hY3 => by
      have hins : insert Y X ∈ s := by
        refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
        · rcases ha with rfl | ha <;> rcases hb with rfl | hb
          · exact Commute.refl _
          · exact hY b hb
          · exact (hY a ha).symm
          · exact hXc a ha b hb
        · rcases ha with rfl | ha
          · exact hY3
          · exact hX3 a ha
      exact hXmax.2 hins (Set.subset_insert Y X) (Set.mem_insert Y X)
  refine ⟨A₀, T, T.det_coe, ?_, fun g => ?_⟩
  · have hu := hTu 1 (by norm_num) 1
    rw [pow_one, one_smul] at hu
    have : ((T : Matrix (Fin 2) (Fin 2) F) - 1) * (T * T + T + 1) = 0 := by
      rw [← sub_eq_zero.2 hT3]; noncomm_ring
    exact (hu.mul_right_eq_zero).1 this
  · obtain ⟨k, Dk, hDk, hg⟩ := hfr g (hEX g.2)
    exact ⟨k, by rw [hg, show A₀⁻¹ * (A₀ * Dk * A₀⁻¹) * A₀ = Dk by group, hDk]⟩

theorem SG.exists_planeFrame_three {F : Type} [Field F] [Finite F] [CharP F 2] {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) (E : Subgroup (StatedSp ℓ F)) (hEc : ∀ g ∈ E, ∀ g' ∈ E, Commute g g')
    (hE3 : ∀ g ∈ E, g ^ 3 = 1) :
    ∃ (A₀ : StatedSp ℓ F) (M : Matrix (Fin 2) (Fin 2) F)
      (k : Fin ℓ → ↥E →* Multiplicative (ZMod 3)), M.det = 1 ∧ M * M + M + 1 = 0 ∧
      ∀ g : ↥E, mat ℓ F (A₀⁻¹ * g * A₀) =
        planeMat fun j => M ^ (Multiplicative.toAdd (k j g)).val := by
  haveI := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  have h3 : ¬ 3 ∣ Nat.card F := fun h => by
    rw [Nat.card_eq_fintype_card, hn] at h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  obtain ⟨A₀, M, hdet, hM, he⟩ := (show 3 ∣ Nat.card F - 1 ∨ 3 ∣ Nat.card F + 1 by omega).elim
    (fun h => exists_frame_split h E hEc hE3) (fun h => exists_frame_nonsplit hℓ h E hEc hE3)
  obtain ⟨k, hk⟩ := exists_planeChar hM E A₀ he
  exact ⟨A₀, M, k, hdet, hM, hk⟩

end CFSG.LocalAnalysis.GLTheoremA.S265

end
