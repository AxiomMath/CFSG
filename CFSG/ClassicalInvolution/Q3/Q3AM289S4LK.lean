module

public import CFSG.ClassicalInvolution.Q3.Q3AM289S4LCfg
public import CFSG.ClassicalInvolution.ModelFacts.TG3Lift
public import CFSG.ClassicalInvolution.Generic.Frame

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM.S4L

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Balance.StrongBalance.Orth CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

structure CoverData (Q : QuadraticForm F V) {K : Type} [Group K] (θ : K →* (V ≃ₗ[F] V))
    (𝓕 : Set (Subgroup K)) (z₀ : K) : Prop where
  range : θ.range = elementaryGroup Q
  ker_le : θ.ker ≤ Subgroup.center K
  ker_two : ∀ x ∈ θ.ker, x = 1 ∨ x = z₀
  z_sq : z₀ * z₀ = 1
  z_mem : z₀ ∈ θ.ker
  map_mem : ∀ R ∈ 𝓕, ∃ Fr : Frame Q, R.map θ = Fr.La.range
  inj : ∀ R ∈ 𝓕, ∀ r ∈ R, θ r = 1 → r = 1
  map_inj : ∀ R ∈ 𝓕, ∀ R' ∈ 𝓕, R.map θ = R'.map θ → R = R'
  surj : ∀ Fr : Frame Q, ∃ R ∈ 𝓕, R.map θ = Fr.La.range
  center_le : ∀ z ∈ Subgroup.center K, θ z ∈ scalars F V
  conj : ∀ R ∈ 𝓕, ∀ g : K, conjSub g R ∈ 𝓕

section Abstract

variable {K E : Type} [Group K] [Group E]

theorem isUniqueInvolution_of_map (θ : K →* E) {R : Subgroup K}
    (hinj : ∀ r ∈ R, θ r = 1 → r = 1) {i : E} (hi : IsUniqueInvolution (R.map θ) i) :
    ∃ r, IsUniqueInvolution R r ∧ θ r = i := by
  obtain ⟨r, hr, hθ⟩ := hi.mem
  have hinj' : ∀ x ∈ R, ∀ y ∈ R, θ x = θ y → x = y := fun x hx y hy h => by
    have : x * y⁻¹ = 1 := hinj _ (R.mul_mem hx (R.inv_mem hy)) (by rw [map_mul, map_inv, h]; simp)
    exact mul_inv_eq_one.mp this
  refine ⟨r, ⟨hr, ?_, ?_, ?_⟩, hθ⟩
  · intro h1
    apply hi.ne_one
    rw [← hθ, h1, map_one]
  · exact hinj' _ (R.mul_mem hr hr) 1 R.one_mem (by rw [map_mul, hθ, hi.sq, map_one])
  · intro y hy hy2
    have h1 : θ y * θ y = 1 := by rw [← map_mul, hy2, map_one]
    rcases hi.unique (θ y) ⟨y, hy, rfl⟩ h1 with h | h
    · exact Or.inl (hinj' y hy 1 R.one_mem (by rw [h, map_one]))
    · exact Or.inr (hinj' y hy r hr (by rw [h, hθ]))

theorem map_conjSub (θ : K →* E) (g : K) (R : Subgroup K) :
    (conjSub g R).map θ = conjSub (θ g) (R.map θ) := by
  ext x
  simp only [conjSub, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨θ r, ⟨r, hr, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨g * r * g⁻¹, ⟨r, hr, rfl⟩, by simp⟩

end Abstract

variable [Finite F]

theorem isUniqueInvolution_range (hodd : Odd (Nat.card F)) {L : Subgroup (V ≃ₗ[F] V)}
    {i : V ≃ₗ[F] V} (h : IsFundamental Q L i) : IsUniqueInvolution L i where
  mem := h.mem
  ne_one := h.ne_one hodd
  sq := h.mul_self
  unique := fun y hy hy2 => by
    by_cases h1 : y = 1
    · exact Or.inl h1
    · exact Or.inr (h.eq_of_orderOf_eq_two hodd hy (orderOf_eq_prime (by rwa [pow_two]) h1))

theorem Jmat_ne_one (F : Type) [Field F] : Jmat F ≠ 1 := by
  intro h
  have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp [Jmat] at this

theorem Jmat_ne_neg_one (F : Type) [Field F] : Jmat F ≠ -1 := by
  intro h
  have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp [Jmat] at this

theorem conjSub_range_La_eq (hodd : Odd (Nat.card F)) (Fb : Frame Q) {g : V ≃ₗ[F] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hu : g * Fb.La (Jmat F) = Fb.La (Jmat F) * g) :
    conjSub g Fb.La.range = Fb.La.range := by
  have h2 : (2 : F) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have hLa : ∀ A, (Fb.map hg).La A = g * Fb.La A * g⁻¹ := Frame.map_La Fb hg
  have hJ : g * Fb.La (Jmat F) * g⁻¹ = Fb.La (Jmat F) := by
    rw [hu]; group
  have hi : (Fb.map hg).La (-1) = Fb.La (-1) := by
    rw [hLa, ← Jmat_mul_self F, map_mul]
    calc g * (Fb.La (Jmat F) * Fb.La (Jmat F)) * g⁻¹ =
        (g * Fb.La (Jmat F) * g⁻¹) * (g * Fb.La (Jmat F) * g⁻¹) := by group
      _ = Fb.La (Jmat F) * Fb.La (Jmat F) := by rw [hJ]
  have hrange : conjSub g Fb.La.range = (Fb.map hg).La.range := by
    ext x
    simp only [conjSub, Subgroup.mem_map, MonoidHom.mem_range, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, hLa]
    constructor
    · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
      exact ⟨A, rfl⟩
    · rintro ⟨A, rfl⟩
      exact ⟨_, ⟨A, rfl⟩, rfl⟩
  rw [hrange]
  rcases Frame.La_range_eq_or_eq_swap h2 hi with h | h
  · exact h
  · exfalso
    have hmem : Fb.La (Jmat F) ∈ (Fb.map hg).La.range := ⟨Jmat F, by rw [hLa, hJ]⟩
    rw [h] at hmem
    rcases (Frame.La_mem_swap_range_iff Fb (Jmat F)).mp hmem with h1 | h1
    · exact Jmat_ne_one F h1
    · exact Jmat_ne_neg_one F h1

theorem elemOn_le_centralizer_of_sign {s : V ≃ₗ[F] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {S : Submodule F V} {ε : F}
    (hε : ε * ε = 1) (hsS : ∀ x ∈ S, s x = ε • x) :
    elemOn Q S ≤ Subgroup.centralizer ({s} : Set (V ≃ₗ[F] V)) := fun _ hh =>
  Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_scalar_elemOn hs hε hsS hh).symm

theorem La_neg_one_of_mem_span (Fr : Frame Q) {x : V} (hx : x ∈ Fr.span) :
    Fr.La (-1) x = (-1 : F) • x := by
  have hx' : x = Fr.incl (Fr.coords x) := (Frame.mem_span_iff Fr).mp hx
  rw [Frame.La_neg_one_apply, ← hx']
  module

theorem La_neg_one_of_mem_perp_gen (Fr : Frame Q) {x : V} (hx : x ∈ Fr.perp) :
    Fr.La (-1) x = (1 : F) • x := by
  rw [one_smul]
  exact Frame.La_apply_of_coords_eq_zero _ _ ((Frame.mem_perp_iff Fr).mp hx)

theorem elemOn_span_le_centralizer (Fr : Frame Q) :
    elemOn Q Fr.span ≤ Subgroup.centralizer ({Fr.La (-1)} : Set (V ≃ₗ[F] V)) :=
  elemOn_le_centralizer_of_sign (Frame.La_mem_orthogonalGroup Fr _) (ε := -1) (by simp)
    fun _ hx => La_neg_one_of_mem_span Fr hx

theorem elemOn_perp_le_centralizer (Fr : Frame Q) :
    elemOn Q Fr.perp ≤ Subgroup.centralizer ({Fr.La (-1)} : Set (V ≃ₗ[F] V)) :=
  elemOn_le_centralizer_of_sign (Frame.La_mem_orthogonalGroup Fr _) (ε := 1) (by simp)
    fun _ hx => La_neg_one_of_mem_perp_gen Fr hx

section Main

variable [FiniteDimensional F V] {K : Type} [Group K] {θ : K →* (V ≃ₗ[F] V)}
  {𝓕 : Set (Subgroup K)} {z₀ : K}

theorem inj_eq (D : CoverData Q θ 𝓕 z₀) {R : Subgroup K} (hR : R ∈ 𝓕) {x y : K} (hx : x ∈ R)
    (hy : y ∈ R) (h : θ x = θ y) : x = y := by
  have : x * y⁻¹ = 1 := D.inj R hR _ (R.mul_mem hx (R.inv_mem hy)) (by
    rw [map_mul, map_inv, h]; simp)
  exact mul_inv_eq_one.mp this

theorem exists_involution (hodd : Odd (Nat.card F)) (D : CoverData Q θ 𝓕 z₀) {R : Subgroup K}
    (hR : R ∈ 𝓕) {Fr : Frame Q} (hmap : R.map θ = Fr.La.range) :
    ∃ r, IsUniqueInvolution R r ∧ θ r = Fr.La (-1) :=
  isUniqueInvolution_of_map θ (D.inj R hR)
    (hmap ▸ isUniqueInvolution_range hodd (IsFundamental.of_frame Fr))

theorem exists_kframe (hodd : Odd (Nat.card F)) (D : CoverData Q θ 𝓕 z₀) (hV : VFrames Q) :
    ∃ (Ra Rb Rc : Subgroup K) (a b u c : K), Ra ∈ 𝓕 ∧ Rb ∈ 𝓕 ∧ Rc ∈ 𝓕 ∧
      IsUniqueInvolution Ra a ∧ IsUniqueInvolution Rb b ∧ IsUniqueInvolution Rc c ∧
      u ∈ Rb ∧ orderOf u = 4 ∧ u * u = b ∧ a * u = u * a ∧ a * b = b * a ∧
      (c = a * b ∨ a * b = c * z₀) ∧ b * a⁻¹ ∉ Subgroup.center K ∧
      Subgroup.centralizer ({a} : Set K) ⊔ Subgroup.centralizer ({b} : Set K) ⊔
        Subgroup.centralizer ({a * b} : Set K) = ⊤ := by
  obtain ⟨Fa, Fb, Fc, hcomm, hc, hnsc, hgen⟩ := hV
  have h2 : (2 : F) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨Ra, hRa, hmapa⟩ := D.surj Fa
  obtain ⟨Rb, hRb, hmapb⟩ := D.surj Fb
  obtain ⟨Rc, hRc, hmapc⟩ := D.surj Fc
  obtain ⟨a, hUa, hθa⟩ := exists_involution hodd D hRa hmapa
  obtain ⟨b, hUb, hθb⟩ := exists_involution hodd D hRb hmapb
  obtain ⟨c, hUc, hθc⟩ := exists_involution hodd D hRc hmapc
  obtain ⟨u, huR, hθu⟩ : Fb.La (Jmat F) ∈ Rb.map θ := by rw [hmapb]; exact ⟨_, rfl⟩
  have huu : u * u = b := by
    refine inj_eq D hRb (Rb.mul_mem huR huR) hUb.mem ?_
    rw [map_mul, hθu, hθb, ← map_mul, Jmat_mul_self]
  have hu4 : orderOf u = 4 := by
    have h1 : ¬ u ^ 2 ^ 1 = 1 := by
      rw [pow_one, pow_two, huu]; exact hUb.ne_one
    have h2' : u ^ 2 ^ (1 + 1) = 1 := by
      rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, pow_two u, huu, pow_two, hUb.sq]
    simpa using orderOf_eq_prime_pow h1 h2'
  have hnorm : conjSub a Rb = Rb := by
    refine D.map_inj _ (D.conj Rb hRb a) Rb hRb ?_
    rw [map_conjSub, hmapb, hθa]
    exact conjSub_range_La_eq hodd Fb (Frame.La_mem_orthogonalGroup Fa _) hcomm
  have hau : a * u = u * a := by
    have h1 : a * u * a⁻¹ ∈ Rb := hnorm ▸ conj_mem_conjSub huR
    have h2' : a * u * a⁻¹ = u := by
      refine inj_eq D hRb h1 huR ?_
      rw [map_mul, map_mul, map_inv, hθa, hθu]
      calc Fa.La (-1) * Fb.La (Jmat F) * (Fa.La (-1))⁻¹ =
          Fb.La (Jmat F) * Fa.La (-1) * (Fa.La (-1))⁻¹ := by rw [hcomm]
        _ = Fb.La (Jmat F) := by group
    calc a * u = a * u * a⁻¹ * a := by group
      _ = u * a := by rw [h2']
  have hab : a * b = b * a := by
    rw [← huu]
    calc a * (u * u) = (a * u) * u := by group
      _ = (u * a) * u := by rw [hau]
      _ = u * (a * u) := by group
      _ = u * (u * a) := by rw [hau]
      _ = u * u * a := by group
  have hθab : θ (a * b) = Fc.La (-1) := by rw [map_mul, hθa, hθb, hc]
  refine ⟨Ra, Rb, Rc, a, b, u, c, hRa, hRb, hRc, hUa, hUb, hUc, huR, hu4, huu, hau, hab, ?_, ?_,
    ?_⟩
  · have hk : c⁻¹ * (a * b) ∈ θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hθc, hθab, inv_mul_cancel]
    rcases D.ker_two _ hk with h | h
    · exact Or.inl (inv_mul_eq_one.mp h)
    · right
      calc a * b = c * (c⁻¹ * (a * b)) := by group
        _ = c * z₀ := by rw [h]
  · intro hcen
    have hs := D.center_le _ hcen
    apply hnsc
    have hia : (Fa.La (-1))⁻¹ = Fa.La (-1) := inv_eq_of_mul_eq_one_right Fa.La_neg_one_mul_self
    have hbb : Fb.La (-1) = Fb.La (Jmat F) * Fb.La (Jmat F) := by
      rw [← map_mul, Jmat_mul_self]
    have hcb : Fa.La (-1) * Fb.La (-1) = Fb.La (-1) * Fa.La (-1) := by
      rw [hbb]
      calc Fa.La (-1) * (Fb.La (Jmat F) * Fb.La (Jmat F)) =
          (Fa.La (-1) * Fb.La (Jmat F)) * Fb.La (Jmat F) := by group
        _ = (Fb.La (Jmat F) * Fa.La (-1)) * Fb.La (Jmat F) := by rw [hcomm]
        _ = Fb.La (Jmat F) * (Fa.La (-1) * Fb.La (Jmat F)) := by group
        _ = Fb.La (Jmat F) * (Fb.La (Jmat F) * Fa.La (-1)) := by rw [hcomm]
        _ = Fb.La (Jmat F) * Fb.La (Jmat F) * Fa.La (-1) := by group
    have : θ (b * a⁻¹) = Fc.La (-1) := by
      rw [map_mul, map_inv, hθa, hθb, hia, hc, hcb]
    rw [← this]
    exact hs
  · have hker2 : ∀ x ∈ θ.ker, x * x = 1 := fun x hx => by
      rcases D.ker_two x hx with rfl | rfl
      · simp
      · exact D.z_sq
    have hHO : (Subgroup.centralizer ({a} : Set K) ⊔ Subgroup.centralizer ({b} : Set K) ⊔
        Subgroup.centralizer ({a * b} : Set K)).map θ ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
      (Subgroup.map_le_range θ _).trans
        (by rw [D.range]; exact elementaryGroup_le_orthogonalGroup Q)
    have h₁ := CFSG.ClassicalInvolution.ModelFacts.TG3.elemOn_le_map_centralizer h2 θ D.range
      D.ker_le hker2 (S := Fa.span) (w := a) (by rw [hθa]; exact elemOn_span_le_centralizer Fa)
    have h₂ := CFSG.ClassicalInvolution.ModelFacts.TG3.elemOn_le_map_centralizer h2 θ D.range
      D.ker_le hker2 (S := Fc.span) (w := a * b)
      (by rw [hθab]; exact elemOn_span_le_centralizer Fc)
    have h₃ := CFSG.ClassicalInvolution.ModelFacts.TG3.elemOn_le_map_centralizer h2 θ D.range
      D.ker_le hker2 (S := Fa.perp) (w := a) (by rw [hθa]; exact elemOn_perp_le_centralizer Fa)
    have hE := hgen _ hHO (h₁.trans (Subgroup.map_mono (le_sup_left.trans le_sup_left)))
      (h₂.trans (Subgroup.map_mono le_sup_right))
      (h₃.trans (Subgroup.map_mono (le_sup_left.trans le_sup_left)))
    rw [eq_top_iff]
    intro g _
    have hg : θ g ∈ (Subgroup.centralizer ({a} : Set K) ⊔ Subgroup.centralizer ({b} : Set K) ⊔
        Subgroup.centralizer ({a * b} : Set K)).map θ :=
      hE (by rw [← D.range]; exact ⟨g, rfl⟩)
    obtain ⟨h, hh, hθh⟩ := hg
    have hk : h⁻¹ * g ∈ θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hθh, inv_mul_cancel]
    have hcen : h⁻¹ * g ∈ Subgroup.centralizer ({a} : Set K) :=
      Subgroup.center_le_centralizer _ (D.ker_le hk)
    have e : g = h * (h⁻¹ * g) := by group
    rw [e]
    exact Subgroup.mul_mem _ hh
      ((le_sup_left.trans le_sup_left : Subgroup.centralizer ({a} : Set K) ≤ _) hcen)

end Main

end CFSG.ClassicalInvolution.Q3.Q3AM.S4L
