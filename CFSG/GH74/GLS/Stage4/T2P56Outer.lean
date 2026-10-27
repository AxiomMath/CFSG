module

public import CFSG.GH74.GLS.IVK.L2.TorusGeneral
public import CFSG.GH74.GLS.Stage4.T2Ctx

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.IVK
  CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Matrix

variable {G : Type} [Group G]

theorem actsAsConj_iff {t : G} {K : Subgroup G} {F : Type} [Field F]
    {e : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F} {g : GL (Fin 2) F} :
    ActsAsConj t K e g ↔ ∀ x : ↥K, ∃ y : ↥K, (y : G) = t * (x : G) * t⁻¹ ∧
      Matrix.SpecialLinearGroup.toGL (e y) = g * Matrix.SpecialLinearGroup.toGL (e x) * g⁻¹ := by
  unfold ActsAsConj
  refine forall_congr' fun x => exists_congr fun y => and_congr_right fun _ => ?_
  constructor
  · intro h
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    simpa using h
  · intro h
    have := congrArg Units.val h
    rw [Units.val_mul, Units.val_mul] at this
    simpa using this

theorem no_outer_involution_commuting_torus {K : Subgroup G} {F : Type} [Field F] [Finite F]
    (hF : L2Field F) (hq4 : Nat.card F % 4 = 1)
    (e : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F) {D : Subgroup G} (hDK : D ≤ K)
    (hD : Nat.card ↥D = Nat.card F - 1) {x : G} {g : GL (Fin 2) F} (hx : ActsAsConj x K e g)
    (hdet : ¬ IsSquare ((Matrix.GeneralLinearGroup.det g : Fˣ) : F)) (hx2 : x * x = 1)
    (hxD : ∀ d ∈ D, x * d = d * x) : False := by
  rw [actsAsConj_iff] at hx
  have hgs : ∀ s : Matrix.SpecialLinearGroup (Fin 2) F,
      Matrix.SpecialLinearGroup.toGL s * (g * g) = (g * g) * Matrix.SpecialLinearGroup.toGL s := by
    intro s
    obtain ⟨y₁, hy₁, hy₁e⟩ := hx (e.symm s)
    obtain ⟨y₂, hy₂, hy₂e⟩ := hx y₁
    have hy₂eq : y₂ = e.symm s := by
      apply Subtype.ext
      rw [hy₂, hy₁]
      calc x * (x * ((e.symm s : ↥K) : G) * x⁻¹) * x⁻¹
          = (x * x) * ((e.symm s : ↥K) : G) * (x * x)⁻¹ := by group
        _ = ((e.symm s : ↥K) : G) := by rw [hx2]; group
    rw [hy₂eq, MulEquiv.apply_symm_apply] at hy₂e
    rw [hy₁e, MulEquiv.apply_symm_apply] at hy₂e
    calc Matrix.SpecialLinearGroup.toGL s * (g * g)
        = (g * (g * Matrix.SpecialLinearGroup.toGL s * g⁻¹) * g⁻¹) * (g * g) := by rw [← hy₂e]
      _ = (g * g) * Matrix.SpecialLinearGroup.toGL s := by group
  have hg2 : ∃ c : F, (g : Matrix (Fin 2) (Fin 2) F) * g = c • (1 : Matrix (Fin 2) (Fin 2) F) := by
    obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_transvectionStruct
      (M := (g : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F)) (fun t => by
        have h1 := hgs ⟨t.toMatrix, t.det⟩
        have h2 := congrArg Units.val h1
        have h3 : t.toMatrix * ((g : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F)) =
            ((g : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F)) * t.toMatrix := by
          have hc : ((Matrix.SpecialLinearGroup.toGL (⟨t.toMatrix, t.det⟩ : Matrix.SpecialLinearGroup (Fin 2) F) :
              GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = t.toMatrix := rfl
          simpa only [Units.val_mul, hc] using h2
        exact h3)
    exact ⟨c, by rw [← hc]; simp [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩
  have hns : ¬ ∃ s : F, (g : Matrix (Fin 2) (Fin 2) F) = s • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rintro ⟨s, hs⟩
    apply hdet
    refine ⟨s, ?_⟩
    have : ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) = (g : Matrix (Fin 2) (Fin 2) F).det := rfl
    rw [this, hs, Matrix.det_smul, Matrix.det_one]
    simp [sq]
  have hq : (Nat.card F : ℤ) ≡ 1 [ZMOD 4] := by
    unfold Int.ModEq; omega
  obtain ⟨-, hcard⟩ := slCentralizer_outer_involution hF 1 (Or.inl rfl) hq (Nat.card F + 1)
    (by push_cast; ring) g hg2 hns hdet
  let φ : ↥K →* SL2 F := (specialLinearGroupEquivStatedSL 2 F).toMonoidHom.comp e.toMonoidHom
  have hφinj : Function.Injective φ :=
    (specialLinearGroupEquivStatedSL 2 F).injective.comp e.injective
  have hD'card : Nat.card ↥((D.subgroupOf K).map φ) = Nat.card F - 1 := by
    rw [Subgroup.card_map_of_injective hφinj, ← hD]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDK).toEquiv
  have hle : (D.subgroupOf K).map φ ≤ slCentralizer g := by
    rintro _ ⟨d, hd, rfl⟩
    have hdD : (d : G) ∈ D := hd
    obtain ⟨y, hy, hye⟩ := hx d
    have hyd : y = d := by
      apply Subtype.ext
      rw [hy, hxD _ hdD]; group
    rw [hyd] at hye
    show ((φ d : SL2 F) : GL (Fin 2) F) ∈ Subgroup.centralizer ({g} : Set (GL (Fin 2) F))
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc : ((φ d : SL2 F) : GL (Fin 2) F) = Matrix.SpecialLinearGroup.toGL (e d) :=
      Units.ext (by simp [φ, specialLinearGroupEquivStatedSL_coe])
    rw [hc]
    calc Matrix.SpecialLinearGroup.toGL (e d) * g = (g * Matrix.SpecialLinearGroup.toGL (e d) * g⁻¹) * g := by
          rw [← hye]
      _ = g * Matrix.SpecialLinearGroup.toGL (e d) := by group
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [hD'card, hcard] at hdvd
  have hq5 : 3 < Nat.card F := hF.2
  have h2 : Nat.card F + 1 = (Nat.card F - 1) + 2 := by omega
  rw [h2] at hdvd
  have h3 : (Nat.card F - 1) ∣ 2 := (Nat.dvd_add_right (dvd_refl _)).1 hdvd
  have := Nat.le_of_dvd (by norm_num) h3
  omega


theorem actsAsConj_mul_left {t k₁ k₂ : G} {K : Subgroup G} {F : Type} [Field F]
    (e : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F) {g : GL (Fin 2) F}
    (ht : ActsAsConj t K e g) (hk₂ : k₂ ∈ K) (hk₁ : ∀ y ∈ K, k₁ * y = y * k₁) :
    ActsAsConj (k₁ * k₂ * t) K e (Matrix.SpecialLinearGroup.toGL (e ⟨k₂, hk₂⟩) * g) := by
  rw [actsAsConj_iff] at ht ⊢
  intro y'
  obtain ⟨y₀, hy₀, hy₀e⟩ := ht y'
  have hmem : k₂ * (y₀ : G) * k₂⁻¹ ∈ K := K.mul_mem (K.mul_mem hk₂ y₀.2) (K.inv_mem hk₂)
  refine ⟨⟨k₂ * (y₀ : G) * k₂⁻¹, hmem⟩, ?_, ?_⟩
  · show k₂ * (y₀ : G) * k₂⁻¹ = k₁ * k₂ * t * (y' : G) * (k₁ * k₂ * t)⁻¹
    have hk₁c : k₁ * (k₂ * (y₀ : G) * k₂⁻¹) = (k₂ * (y₀ : G) * k₂⁻¹) * k₁ := hk₁ _ hmem
    calc k₂ * (y₀ : G) * k₂⁻¹ = k₁ * (k₂ * (y₀ : G) * k₂⁻¹) * k₁⁻¹ := by rw [hk₁c]; group
      _ = k₁ * k₂ * (t * (y' : G) * t⁻¹) * k₂⁻¹ * k₁⁻¹ := by rw [hy₀]; group
      _ = k₁ * k₂ * t * (y' : G) * (k₁ * k₂ * t)⁻¹ := by group
  · have h1 : (⟨k₂ * (y₀ : G) * k₂⁻¹, hmem⟩ : ↥K) = ⟨k₂, hk₂⟩ * y₀ * ⟨k₂, hk₂⟩⁻¹ := Subtype.ext rfl
    rw [h1, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hy₀e]
    group


end Matrix

section Invol

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {q₁ q₂ : ℕ} {z t : G}
  {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem no_invol_outside_K
    (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t) {N : T2N1 G} {u : G}
    (hLoc : Ch6Loc5 N u) (hz : N.z = z) (hK₁ : N.K₁ = K₁) (hK₂ : N.K₂ = K₂) (hq₁ : N.q₁ = q₁)
    (hq₂ : N.q₂ = q₂) (h₂ : q₂ % 4 = 1) {x : G} (hxH : x ∈ N.H) (hxK : x ∉ K₁ ⊔ K₂)
    (hx2 : x * x = 1) : False := by
  have ctx := t2Ctx_of hSet hRem hLoc hz hK₁ hK₂ hq₁ hq₂
  subst hz hK₁ hK₂ hq₁ hq₂
  have hxC₁ : x ∈ oPrimeResidualOf 2 (centralizer ({N.z} : Set G)) := by
    rw [← ctx.KS]; exact hLoc.H_le hxH
  have htC₁ : t ∈ oPrimeResidualOf 2 (centralizer ({N.z} : Set G)) := by
    rw [← hRem.gen]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have htK : t ∉ N.K₁ ⊔ N.K₂ := by
    intro htK
    apply hxK
    have h1 : x ∈ N.K₁ ⊔ N.K₂ ⊔ Subgroup.zpowers t := by rw [hRem.gen]; exact hxC₁
    have hle : Subgroup.zpowers t ≤ N.K₁ ⊔ N.K₂ := Subgroup.zpowers_le.2 htK
    rwa [sup_eq_left.2 hle] at h1
  have hxt : x * t ∈ N.K₁ ⊔ N.K₂ := by
    have hidx : ((N.K₁ ⊔ N.K₂).subgroupOf (oPrimeResidualOf 2 (centralizer ({N.z} : Set G)))).index = 2 :=
      hSet.index_two
    have : (⟨x, hxC₁⟩ : ↥(oPrimeResidualOf 2 (centralizer ({N.z} : Set G)))) * ⟨t, htC₁⟩ ∈
        (N.K₁ ⊔ N.K₂).subgroupOf (oPrimeResidualOf 2 (centralizer ({N.z} : Set G))) := by
      rw [Subgroup.mul_mem_iff_of_index_two hidx]
      exact iff_of_false (by rwa [Subgroup.mem_subgroupOf]) (by rwa [Subgroup.mem_subgroupOf])
    exact this
  obtain ⟨k₁, hk₁, k₂, hk₂, hkk⟩ := (mem_sup_iff_of_comm hSet.comm (x * t)).1 hxt
  have htt : t * t = 1 := hRem.sq
  have hxe : x = k₁ * k₂ * t := by
    rw [← hkk]
    calc x = x * (t * t) := by rw [htt, mul_one]
      _ = x * t * t := by group
  obtain ⟨e₂, g, hdet, hAct⟩ := hRem.diag₂
  have hk₁comm : ∀ y ∈ N.K₂, k₁ * y = y * k₁ := fun y hy => hSet.comm k₁ hk₁ y hy
  have hActx := actsAsConj_mul_left e₂ hAct hk₂ hk₁comm
  rw [← hxe] at hActx
  have := hSet.finite₂
  have hq₂5 : 5 ≤ N.q₂ := by
    have := hLoc.q₂_ge
    omega
  have hF : L2Field F₂ := ⟨by rw [hSet.card₂]; exact hSet.odd₂, by rw [hSet.card₂]; omega⟩
  have hdet₀ : ¬ IsSquare ((Matrix.GeneralLinearGroup.det
      (Matrix.SpecialLinearGroup.toGL (e₂ ⟨k₂, hk₂⟩) * g) : F₂ˣ) : F₂) := by
    have h1 : Matrix.GeneralLinearGroup.det
        (Matrix.SpecialLinearGroup.toGL (e₂ ⟨k₂, hk₂⟩)) = 1 := by
      ext; simp
    rw [map_mul, h1, one_mul]
    exact hdet
  have hD : Nat.card ↥(N.H ⊓ N.K₂) = Nat.card F₂ - 1 := by rw [hLoc.card_H_K₂, hSet.card₂]
  have hxD : ∀ d ∈ N.H ⊓ N.K₂, x * d = d * x := fun d hd => hLoc.H_comm x hxH d hd.1
  exact no_outer_involution_commuting_torus hF (by rw [hSet.card₂]; exact h₂) e₂ inf_le_right hD
    hActx hdet₀ hx2 hxD

end Invol

end CFSG.GH74.GLS.Stage4.Rest
