module

public import CFSG.GH74.GLS.IVK.Prod32.LangDefs
public import CFSG.GH74.GLS.IVK.Prod32.Out
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Core

public section

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.GorensteinWalter Matrix

namespace CFSG.GH74.GLS.IVK.Prod3.PglQ

variable {F : Type} [Field F]

theorem mem_statedSL_det {A : GL (Fin 2) F} :
    A ∈ StatedSL 2 F ↔ (A : Matrix (Fin 2) (Fin 2) F).det = 1 :=
  CFSG.Open.StatedAPI.mem_statedSL_iff

theorem statedSL_normal' : (StatedSL 2 F).Normal := by
  constructor
  intro A hA g
  rw [mem_statedSL_det] at hA ⊢
  simp only [Units.val_mul, Matrix.det_mul, hA, mul_one]
  rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]

@[expose] noncomputable def glAct : GL (Fin 2) F →* MulAut (SL2 F) :=
  haveI := statedSL_normal' (F := F)
  MulAut.conjNormal (H := StatedSL 2 F)

theorem glAct_apply (g : GL (Fin 2) F) (s : SL2 F) :
    ((glAct g s : SL2 F) : GL (Fin 2) F) = g * (s : GL (Fin 2) F) * g⁻¹ := by
  simp [glAct]


theorem glAct_eq_one_iff (g : GL (Fin 2) F) : glAct g = 1 ↔ g ∈ center (GL (Fin 2) F) := by
  constructor
  · intro h
    have hc : ∀ s : SL2 F, g * (s : GL (Fin 2) F) = (s : GL (Fin 2) F) * g := by
      intro s
      have := congrArg (fun φ : MulAut (SL2 F) => ((φ s : SL2 F) : GL (Fin 2) F)) h
      simp only [glAct_apply, MulAut.one_apply] at this
      calc g * (s : GL (Fin 2) F) = (g * (s : GL (Fin 2) F) * g⁻¹) * g := by group
        _ = (s : GL (Fin 2) F) * g := by rw [this]
    have h1 := congrArg (fun x : GL (Fin 2) F => (x : Matrix (Fin 2) (Fin 2) F))
      (hc (specialLinearGroupEquivStatedSL 2 F (uSL 1)))
    have h2 := congrArg (fun x : GL (Fin 2) F => (x : Matrix (Fin 2) (Fin 2) F))
      (hc (specialLinearGroupEquivStatedSL 2 F (vSL 1)))
    simp only [Units.val_mul] at h1 h2
    obtain ⟨μ, hμ⟩ := scalar_of_commute_two (g : Matrix (Fin 2) (Fin 2) F) h1 h2
    rw [GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
    exact ⟨μ, by rw [hμ, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩
  · intro hg
    apply MulEquiv.ext
    intro s
    apply Subtype.ext
    show ((glAct g s : SL2 F) : GL (Fin 2) F) = (s : GL (Fin 2) F)
    rw [glAct_apply]
    have := Subgroup.mem_center_iff.1 hg (s : GL (Fin 2) F)
    rw [← this]
    group

@[expose] noncomputable def glActBar : PGL2 F →* MulAut (SL2 F) :=
  QuotientGroup.lift (center (GL (Fin 2) F)) glAct (fun g hg => (glAct_eq_one_iff g).2 hg)

theorem glActBar_mk (g : GL (Fin 2) F) : glActBar (ProjGenLinGroup.mk g) = glAct g := rfl

theorem glActBar_injective : Function.Injective (glActBar : PGL2 F →* MulAut (SL2 F)) := by
  rw [injective_iff_map_eq_one]
  intro p hp
  induction p using ProjGenLinGroup.induction_on with
  | mk g =>
    rw [glActBar_mk] at hp
    exact ProjGenLinGroup.mk_eq_one.2 ((glAct_eq_one_iff g).1 hp)

theorem isSquare_det_of_mem_center [Finite F] {g : GL (Fin 2) F} (hg : g ∈ center (GL (Fin 2) F)) :
    IsSquare ((g : Matrix (Fin 2) (Fin 2) F).det) := by
  rw [GeneralLinearGroup.center_eq_range_scalar] at hg
  obtain ⟨u, rfl⟩ := hg
  refine ⟨(u : F), ?_⟩
  simp [pow_two]

theorem isSquare_mul_of_not_isSquare [Finite F] (hodd : Odd (Nat.card F)) {a b : F}
    (ha : ¬ IsSquare a) (hb : ¬ IsSquare b) : IsSquare (a * b) := by
  classical
  have := Fintype.ofFinite F
  have hF : ringChar F ≠ 2 := by
    intro h
    have h1 := (FiniteField.even_card_iff_char_two (F := F)).1 h
    rw [← Nat.card_eq_fintype_card] at h1
    obtain ⟨k, hk⟩ := hodd
    omega
  have ha0 : a ≠ 0 := fun h => ha (h ▸ ⟨0, by simp⟩)
  have hb0 : b ≠ 0 := fun h => hb (h ▸ ⟨0, by simp⟩)
  have h1 : quadraticChar F (a * b) = 1 := by
    rw [map_mul, quadraticChar_neg_one_iff_not_isSquare.2 ha, quadraticChar_neg_one_iff_not_isSquare.2 hb]
    norm_num
  exact (quadraticChar_one_iff_isSquare (mul_ne_zero ha0 hb0)).1 h1

theorem exists_sl_of_isSquare_det (g : GL (Fin 2) F)
    (hg : IsSquare ((g : Matrix (Fin 2) (Fin 2) F).det)) : ∃ s : SL2 F, glAct g = glAct s := by
  obtain ⟨c, hc⟩ := hg
  have hdet : (g : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det (g : Matrix (Fin 2) (Fin 2) F)).1 (Units.isUnit g)
    exact this.ne_zero
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hdet
    rw [hc]; simp
  let u : Fˣ := Units.mk0 c hc0
  have hmem : g * GeneralLinearGroup.scalar (Fin 2) u⁻¹ ∈ StatedSL 2 F := by
    rw [mem_statedSL_det]
    simp only [Units.val_mul, Matrix.det_mul]
    rw [GeneralLinearGroup.coe_scalar]
    simp [hc, u, pow_two]
    field_simp
  refine ⟨⟨g * GeneralLinearGroup.scalar (Fin 2) u⁻¹, hmem⟩, ?_⟩
  have h1 : g = (g * GeneralLinearGroup.scalar (Fin 2) u⁻¹) * GeneralLinearGroup.scalar (Fin 2) u := by
    rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
  have h2 : glAct (GeneralLinearGroup.scalar (Fin 2) u) = 1 := by
    rw [glAct_eq_one_iff, GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨u, rfl⟩
  conv_lhs => rw [h1]
  rw [map_mul, h2, mul_one]

section Grp

variable {H : Type} [Group H] {Kn Ka X : Subgroup H}

@[expose] noncomputable def psi (hXN : X ≤ normalizer (Ka : Set H)) (e : ↥Ka ≃* SL2 F) :
    ↥X →* MulAut (SL2 F) :=
  (MulAut.congr e).toMonoidHom.comp (Ka.normalizerMonoidHom.comp (Subgroup.inclusion hXN))

theorem psi_apply_e (hXN : X ≤ normalizer (Ka : Set H)) (e : ↥Ka ≃* SL2 F) (x : ↥X) (k : ↥Ka)
    (hk : (x : H) * k * (x : H)⁻¹ ∈ Ka) :
    psi hXN e x (e k) = e ⟨(x : H) * k * (x : H)⁻¹, hk⟩ := by
  show e (Ka.normalizerMonoidHom (Subgroup.inclusion hXN x) (e.symm (e k))) = _
  rw [MulEquiv.symm_apply_apply]
  congr 1

theorem psi_eq_glAct (hXN : X ≤ normalizer (Ka : Set H)) (e : ↥Ka ≃* SL2 F) (x : ↥X)
    (g : GL (Fin 2) F)
    (h : ∀ (k : ↥Ka) (hk : (x : H) * k * (x : H)⁻¹ ∈ Ka),
      ((e ⟨(x : H) * k * (x : H)⁻¹, hk⟩ : SL2 F) : GL (Fin 2) F) =
        g * ((e k : SL2 F) : GL (Fin 2) F) * g⁻¹) :
    psi hXN e x = glAct g := by
  apply MulEquiv.ext
  intro s
  obtain ⟨k, rfl⟩ := e.surjective s
  have hk : (x : H) * k * (x : H)⁻¹ ∈ Ka := ((Subgroup.mem_normalizer_iff.1 (hXN x.2)) (k : H)).1 k.2
  rw [psi_apply_e hXN e x k hk]
  apply Subtype.ext
  rw [glAct_apply]
  exact h k hk

theorem mem_X_decomp (hcomm : ∀ a ∈ Kn, ∀ b ∈ Ka, a * b = b * a) {y : H}
    (hyK : y ∈ normalizer ((Kn ⊔ Ka : Subgroup H) : Set H)) (hy2 : y * y ∈ Kn ⊔ Ka)
    {x : H} (hx : x ∈ Kn ⊔ Ka ⊔ zpowers y) :
    (∃ k₁ ∈ Kn, ∃ k₂ ∈ Ka, x = k₁ * k₂) ∨ (∃ k₁ ∈ Kn, ∃ k₂ ∈ Ka, x = k₁ * k₂ * y) := by
  rcases CFSG.GH74.GLS.Stage1.Thm3.Sec5.mem_or_mul_inv_mem hyK hy2 hx with h | h
  · left
    exact (mem_sup_of_comm hcomm x).1 h
  · right
    obtain ⟨k₁, hk₁, k₂, hk₂, hk⟩ := (mem_sup_of_comm hcomm _).1 h
    exact ⟨k₁, hk₁, k₂, hk₂, by rw [← hk]; group⟩

theorem psi_mk_eq_glAct (hXN : X ≤ normalizer (Ka : Set H)) (e : ↥Ka ≃* SL2 F) {x : H} (hx : x ∈ X)
    (g : GL (Fin 2) F)
    (h : ∀ (k : ↥Ka) (hk : x * k * x⁻¹ ∈ Ka),
      ((e ⟨x * k * x⁻¹, hk⟩ : SL2 F) : GL (Fin 2) F) =
        g * ((e k : SL2 F) : GL (Fin 2) F) * g⁻¹) :
    psi hXN e ⟨x, hx⟩ = glAct g := psi_eq_glAct hXN e ⟨x, hx⟩ g h

theorem pgl_quot [Finite H] [Finite F] {y : H} (hX : X = Kn ⊔ Ka ⊔ zpowers y)
    (e : ↥Ka ≃* SL2 F)
    (hcomm : ∀ a ∈ Kn, ∀ b ∈ Ka, a * b = b * a)
    (hZ : ∀ w : ↥Ka, w ∈ Subgroup.center ↥Ka → (w : H) ∈ Kn)
    (hyKa : DiagOutE Ka e y) (hyKn : ∀ x ∈ Kn, y * x * y⁻¹ ∈ Kn) (hy2 : y * y ∈ Kn ⊔ Ka)
    (hodd : Odd (Nat.card F)) :
    ∃ θ : ↥X →* PGL2 F, Function.Surjective θ ∧ ∀ x : ↥X, θ x = 1 ↔ (x : H) ∈ Kn := by
  obtain ⟨hyKa1, d, hd, hdy⟩ := hyKa
  have hyKaN : y ∈ normalizer (Ka : Set H) := mem_normalizer_of_conj_le hyKa1
  have hyK1 : ∀ x ∈ Kn ⊔ Ka, y * x * y⁻¹ ∈ Kn ⊔ Ka := by
    intro x hx
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := (mem_sup_of_comm hcomm x).1 hx
    have : y * (k₁ * k₂) * y⁻¹ = (y * k₁ * y⁻¹) * (y * k₂ * y⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem_sup (hyKn k₁ hk₁) (hyKa1 k₂ hk₂)
  have hyK : y ∈ normalizer ((Kn ⊔ Ka : Subgroup H) : Set H) := mem_normalizer_of_conj_le hyK1
  have hKnN : Kn ≤ normalizer (Ka : Set H) := by
    intro n hn
    refine mem_normalizer_of_conj_le (fun x hx => ?_)
    have h1 : n * x * n⁻¹ = x := by rw [hcomm n hn x hx]; group
    rw [h1]
    exact hx
  have hXN : X ≤ normalizer (Ka : Set H) := by
    rw [hX]
    exact sup_le (sup_le hKnN le_normalizer) (zpowers_le.2 hyKaN)
  have hKaX : Ka ≤ X := by rw [hX]; exact le_sup_right.trans le_sup_left
  have hKnX : Kn ≤ X := by rw [hX]; exact le_sup_left.trans le_sup_left
  have hyX : y ∈ X := by rw [hX]; exact mem_sup_right (mem_zpowers y)
  have psi_kn : ∀ (k₁ : H) (hk₁ : k₁ ∈ Kn), psi hXN e ⟨k₁, hKnX hk₁⟩ = 1 := by
    intro k₁ hk₁
    rw [← map_one (glAct (F := F))]
    apply psi_mk_eq_glAct
    intro k hk
    have h1 : k₁ * (k : H) * k₁⁻¹ = k := by rw [hcomm k₁ hk₁ k k.2]; group
    have h2 : (⟨k₁ * (k : H) * k₁⁻¹, hk⟩ : ↥Ka) = k := Subtype.ext h1
    rw [h2]
    simp
  have psi_ka : ∀ (k₂ : H) (hk₂ : k₂ ∈ Ka), psi hXN e ⟨k₂, hKaX hk₂⟩ =
      glAct ((e ⟨k₂, hk₂⟩ : SL2 F) : GL (Fin 2) F) := by
    intro k₂ hk₂
    apply psi_mk_eq_glAct
    intro k hk
    have h2 : (⟨k₂ * (k : H) * k₂⁻¹, hk⟩ : ↥Ka) = ⟨k₂, hk₂⟩ * k * ⟨k₂, hk₂⟩⁻¹ := rfl
    rw [h2, map_mul, map_mul, map_inv]
    rfl
  have psi_y : psi hXN e ⟨y, hyX⟩ = glAct d := by
    apply psi_mk_eq_glAct
    intro k hk
    exact hdy k hk
  have hdec : ∀ x : ↥X,
      (∃ k₂ : ↥Ka, (∃ k₁ ∈ Kn, (x : H) = k₁ * k₂) ∧
        psi hXN e x = glAct ((e k₂ : SL2 F) : GL (Fin 2) F)) ∨
      (∃ k₂ : ↥Ka, (∃ k₁ ∈ Kn, (x : H) = k₁ * k₂ * y) ∧
        psi hXN e x = glAct (((e k₂ : SL2 F) : GL (Fin 2) F) * d)) := by
    intro x
    have hx : (x : H) ∈ Kn ⊔ Ka ⊔ zpowers y := hX ▸ x.2
    rcases mem_X_decomp hcomm hyK hy2 hx with ⟨k₁, hk₁, k₂, hk₂, hx⟩ | ⟨k₁, hk₁, k₂, hk₂, hx⟩
    · left
      refine ⟨⟨k₂, hk₂⟩, ⟨k₁, hk₁, hx⟩, ?_⟩
      have : x = ⟨k₁, hKnX hk₁⟩ * ⟨k₂, hKaX hk₂⟩ := Subtype.ext hx
      rw [this, map_mul, psi_kn k₁ hk₁, psi_ka k₂ hk₂, one_mul]
    · right
      refine ⟨⟨k₂, hk₂⟩, ⟨k₁, hk₁, hx⟩, ?_⟩
      have : x = ⟨k₁, hKnX hk₁⟩ * ⟨k₂, hKaX hk₂⟩ * ⟨y, hyX⟩ := Subtype.ext hx
      rw [this, map_mul, map_mul, psi_kn k₁ hk₁, psi_ka k₂ hk₂, psi_y, one_mul, map_mul]
  have hker : ∀ x : ↥X, psi hXN e x = 1 ↔ (x : H) ∈ Kn := by
    intro x
    constructor
    · intro h1
      rcases hdec x with ⟨k₂, ⟨k₁, hk₁, hx⟩, hψx⟩ | ⟨k₂, ⟨k₁, hk₁, hx⟩, hψx⟩
      · have hcen : ((e k₂ : SL2 F) : GL (Fin 2) F) ∈ center (GL (Fin 2) F) :=
          (glAct_eq_one_iff _).1 (hψx.symm.trans h1)
        have hck : k₂ ∈ Subgroup.center ↥Ka := by
          rw [Subgroup.mem_center_iff]
          intro k
          apply e.injective
          rw [map_mul, map_mul]
          apply Subtype.ext
          have := Subgroup.mem_center_iff.1 hcen ((e k : SL2 F) : GL (Fin 2) F)
          simpa using this
        rw [hx]
        exact Kn.mul_mem hk₁ (hZ k₂ hck)
      · exfalso
        have hcen : ((e k₂ : SL2 F) : GL (Fin 2) F) * d ∈ center (GL (Fin 2) F) :=
          (glAct_eq_one_iff _).1 (hψx.symm.trans h1)
        have hsq := isSquare_det_of_mem_center hcen
        rw [Units.val_mul, Matrix.det_mul] at hsq
        have hdet1 : (((e k₂ : SL2 F) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 :=
          mem_statedSL_det.1 (e k₂).2
        rw [hdet1, one_mul] at hsq
        exact hd hsq
    · intro hx
      exact psi_kn _ hx
  have hsurj : ∀ g : GL (Fin 2) F, ∃ x : ↥X, psi hXN e x = glAct g := by
    intro g
    by_cases hg : IsSquare ((g : Matrix (Fin 2) (Fin 2) F).det)
    · obtain ⟨s, hs⟩ := exists_sl_of_isSquare_det g hg
      refine ⟨⟨(e.symm s : H), hKaX (e.symm s).2⟩, ?_⟩
      rw [psi_ka _ (e.symm s).2, hs]
      simp
    · have hg' : IsSquare (((g * d⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det) := by
        rw [Units.val_mul, Matrix.det_mul]
        apply isSquare_mul_of_not_isSquare hodd hg
        have h1 : ((d⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det =
            ((d : Matrix (Fin 2) (Fin 2) F).det)⁻¹ := by
          have := congrArg (fun x : GL (Fin 2) F => (x : Matrix (Fin 2) (Fin 2) F).det)
            (mul_inv_cancel d)
          simp only [Units.val_mul, Matrix.det_mul, Units.val_one, Matrix.det_one] at this
          exact eq_inv_of_mul_eq_one_right this
        rw [h1]
        simpa using hd
      obtain ⟨s, hs⟩ := exists_sl_of_isSquare_det _ hg'
      refine ⟨⟨(e.symm s : H), hKaX (e.symm s).2⟩ * ⟨y, hyX⟩, ?_⟩
      rw [map_mul, psi_ka _ (e.symm s).2, psi_y]
      have h2 : glAct g = glAct (g * d⁻¹) * glAct d := by
        rw [← map_mul]
        congr 1
        group
      rw [h2, hs]
      simp
  have hle : ∀ x : ↥X, psi hXN e x ∈ (glActBar : PGL2 F →* MulAut (SL2 F)).range := by
    intro x
    rcases hdec x with ⟨k₂, _, hψx⟩ | ⟨k₂, _, hψx⟩
    · exact ⟨ProjGenLinGroup.mk ((e k₂ : SL2 F) : GL (Fin 2) F), by rw [glActBar_mk, hψx]⟩
    · exact ⟨ProjGenLinGroup.mk (((e k₂ : SL2 F) : GL (Fin 2) F) * d), by rw [glActBar_mk, hψx]⟩
  let θ : ↥X →* PGL2 F :=
    ((MonoidHom.ofInjective glActBar_injective).symm.toMonoidHom).comp
      ((psi hXN e).codRestrict _ hle)
  have hθ : ∀ x : ↥X, glActBar (θ x) = psi hXN e x := fun x =>
    MonoidHom.apply_ofInjective_symm glActBar_injective ⟨psi hXN e x, hle x⟩
  refine ⟨θ, ?_, ?_⟩
  · intro p
    induction p using ProjGenLinGroup.induction_on with
    | mk g =>
      obtain ⟨x, hx⟩ := hsurj g
      refine ⟨x, ?_⟩
      apply glActBar_injective
      rw [hθ, hx, glActBar_mk]
  · intro x
    constructor
    · intro h1
      apply (hker x).1
      rw [← hθ x, h1, map_one]
    · intro h1
      apply glActBar_injective
      rw [hθ, (hker x).2 h1, map_one]

section Main

variable {Kn Ka X : Subgroup H}

theorem pgl_quot_iso [Finite H] [Finite F] {y : H} (hX : X = Kn ⊔ Ka ⊔ zpowers y)
    (e : ↥Ka ≃* SL2 F) (hcomm : ∀ a ∈ Kn, ∀ b ∈ Ka, a * b = b * a)
    (hZ : ∀ w : ↥Ka, w ∈ Subgroup.center ↥Ka → (w : H) ∈ Kn)
    (hyKa : DiagOutE Ka e y) (hyKn : ∀ x ∈ Kn, y * x * y⁻¹ ∈ Kn) (hy2 : y * y ∈ Kn ⊔ Ka)
    (hodd : Odd (Nat.card F)) (P : ℕ → Prop) (hP : P (Nat.card F)) :
    ∃ _ : (Kn.subgroupOf X).Normal, IsPGL2 (↥X ⧸ Kn.subgroupOf X) P := by
  obtain ⟨θ, hsurj, hker⟩ := pgl_quot hX e hcomm hZ hyKa hyKn hy2 hodd
  have hker' : θ.ker = Kn.subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  have hN : (Kn.subgroupOf X).Normal := hker' ▸ θ.normal_ker
  refine ⟨hN, F, inferInstance, inferInstance, hP, ⟨?_⟩⟩
  exact (QuotientGroup.quotientMulEquivOfEq hker'.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective θ hsurj)

end Main

end Grp

end CFSG.GH74.GLS.IVK.Prod3.PglQ

namespace CFSG.GH74.GLS.IVK.Prod3

open CFSG.GH74.GLS.IVK.Prod3.PglQ

variable {H : Type} [Group H] [Finite H] {K₁ K₂ : Subgroup H} {z : H}
  {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁] [Finite F₂]

theorem prod3_Cc_pgl (hS : Setting H K₁ K₂ z) (e₁ : ↥K₁ ≃* SL2 F₁) (e₂ : ↥K₂ ≃* SL2 F₂) {r : ℕ}
    (hr₁ : Nat.card F₁ = r ^ 4) (hr₂ : Nat.card F₂ = r ^ 4) (hodd : Odd r) {y : H}
    (hy₁ : DiagOutE K₁ e₁ y) (hy₂ : DiagOutE K₂ e₂ y) (hy2 : y * y ∈ K₁ ⊔ K₂) :
    ∀ K ∈ ({K₁, K₂} : Set (Subgroup H)), ∃ _ : (K.subgroupOf (K₁ ⊔ K₂ ⊔ zpowers y)).Normal,
      IsPGL2 (↥(K₁ ⊔ K₂ ⊔ zpowers y) ⧸ K.subgroupOf (K₁ ⊔ K₂ ⊔ zpowers y))
        (fun q => q = r ^ 4) := by
  intro K hK
  have hodd₁ : Odd (Nat.card F₁) := by rw [hr₁]; exact hodd.pow
  have hodd₂ : Odd (Nat.card F₂) := by rw [hr₂]; exact hodd.pow
  rcases hK with hK | hK
  · rw [hK]
    refine pgl_quot_iso (Kn := K₁) (Ka := K₂) rfl e₂ hS.comm (fun w hw => ?_) hy₂ hy₁.1 hy2 hodd₂
      (fun q => q = r ^ 4) hr₂
    exact (Subgroup.zpowers_le.2 hS.z_mem₁) (hS.symm.center_mem₁ hw)
  · rw [Set.mem_singleton_iff] at hK
    rw [hK]
    have hy2' : y * y ∈ K₂ ⊔ K₁ := by rw [sup_comm]; exact hy2
    refine pgl_quot_iso (Kn := K₂) (Ka := K₁) (by rw [sup_comm K₂ K₁]) e₁
      (fun a ha b hb => (hS.comm b hb a ha).symm) (fun w hw => ?_) hy₁ hy₂.1 hy2' hodd₁
      (fun q => q = r ^ 4) hr₁
    exact (Subgroup.zpowers_le.2 hS.z_mem₂) (hS.center_mem₁ hw)

end CFSG.GH74.GLS.IVK.Prod3
