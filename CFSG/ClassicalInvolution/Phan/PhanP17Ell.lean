module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthConj

public section

namespace CFSG.ClassicalInvolution.PhanP

open QuadraticMap CliffordAlgebra CFSG.ClassicalInvolution.ModelFacts MulChar

variable {F : Type} [Field F] [Invertible (2 : F)] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V}

theorem isSquare_mul_of_not_isSquare {K : Type} [Field K] [Fintype K] [DecidableEq K] {a b : K}
    (ha : ¬IsSquare a) (hb : ¬IsSquare b) : IsSquare (a * b) := by
  have ha0 : a ≠ 0 := fun h => ha ⟨0, by rw [h]; ring⟩
  have hb0 : b ≠ 0 := fun h => hb ⟨0, by rw [h]; ring⟩
  have h1 : quadraticChar K a = -1 := quadraticChar_neg_one_iff_not_isSquare.2 ha
  have h2 : quadraticChar K b = -1 := quadraticChar_neg_one_iff_not_isSquare.2 hb
  have : quadraticChar K (a * b) = 1 := by
    rw [map_mul, h1, h2]
    norm_num
  exact (quadraticChar_one_iff_isSquare (mul_ne_zero ha0 hb0)).1 this

omit [FiniteDimensional F V] in
theorem nondegenerate_restrict_of_forall (P : Submodule F V)
    (h : ∀ x ∈ P, (∀ y ∈ P, polar Q x y = 0) → x = 0) : (Q.restrict P).Nondegenerate := by
  refine QuadraticMap.nondegenerate_polar_iff.mp ?_
  have key : ∀ x y : P, polarBilin (Q.restrict P) x y = polar Q (x : V) (y : V) := fun x y => by
    rw [polarBilin_apply_apply]
    rfl
  have hsep : ∀ x : P, (∀ y : P, polarBilin (Q.restrict P) x y = 0) → x = 0 := by
    intro x hx
    refine Subtype.ext (h x x.2 fun y hy => ?_)
    have := hx ⟨y, hy⟩
    rwa [key] at this
  refine ⟨hsep, fun x hx => hsep x fun y => ?_⟩
  have := hx y
  rw [key] at this ⊢
  rw [QuadraticMap.polar_comm]
  exact this

theorem exists_elliptic_pair [Finite F] (hodd : Odd (Nat.card F)) {ε : F}
    (hε' : ¬IsSquare (-ε)) {S : Submodule F V} (hS4 : 4 ≤ Module.finrank F S)
    (hT : ∀ T : Submodule F V, T ≤ S → (∀ x ∈ T, Q x = 0) → Module.finrank F T ≤ 2) :
    ∃ u ∈ S, ∃ v ∈ S, Q u = 1 ∧ Q v = ε ∧ polar Q u v = 0 := by
  classical
  have h2 : (2 : F) ≠ 0 := Invertible.ne_zero 2
  set R : Submodule F V := S ⊓ LinearMap.BilinForm.orthogonal Q.polarBilin S with hR
  have hRS : R ≤ S := inf_le_left
  have hRperp : ∀ x ∈ R, ∀ y ∈ S, polar Q x y = 0 := by
    intro x hx y hy
    have : Q.polarBilin y x = 0 := hx.2 y hy
    rw [polarBilin_apply_apply] at this
    rw [QuadraticMap.polar_comm]
    exact this
  have hRts : ∀ x ∈ R, Q x = 0 := by
    intro x hx
    have h := hRperp x hx x (hRS hx)
    rw [QuadraticMap.polar_self, two_smul] at h
    have : (2 : F) * Q x = 0 := by rw [two_mul]; exact h
    exact (mul_eq_zero.1 this).resolve_left h2
  have hr : Module.finrank F R ≤ 2 := hT R hRS hRts
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl R
  set S₀ : Submodule F V := C ⊓ S with hS₀
  have hsup : R ⊔ S₀ = S := by
    rw [hS₀, ← sup_inf_assoc_of_le C hRS, hC.sup_eq_top, top_inf_eq]
  have hinf : R ⊓ S₀ = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have := hC.inf_eq_bot
    have h1 : x ∈ R ⊓ C := ⟨hx.1, hx.2.1⟩
    rw [hC.inf_eq_bot] at h1
    exact h1
  have hd : Module.finrank F R + Module.finrank F S₀ = Module.finrank F S := by
    have := Submodule.finrank_sup_add_finrank_inf_eq R S₀
    rw [hsup, hinf, finrank_bot] at this
    omega
  have hS₀sep : ∀ x ∈ S₀, (∀ y ∈ S₀, polar Q x y = 0) → x = 0 := by
    intro x hx hxperp
    have hxS : x ∈ S := hx.2
    have hxR : x ∈ R := by
      refine ⟨hxS, fun y hy => ?_⟩
      rw [← hsup] at hy
      obtain ⟨r, hr, s, hs, rfl⟩ := Submodule.mem_sup.1 hy
      rw [map_add, LinearMap.add_apply]
      have h1 : Q.polarBilin r x = 0 := by
        rw [polarBilin_apply_apply]; exact hRperp r hr x hxS
      have h2' : Q.polarBilin s x = 0 := by
        rw [polarBilin_apply_apply, QuadraticMap.polar_comm]; exact hxperp s hs
      rw [h1, h2', add_zero]
    have : x ∈ R ⊓ S₀ := ⟨hxR, hx⟩
    rw [hinf] at this
    exact (Submodule.mem_bot F).1 this
  have hS₀reg : (Q.restrict S₀).Nondegenerate := nondegenerate_restrict_of_forall S₀ hS₀sep
  have hd2 : 2 ≤ Module.finrank F S₀ := by omega
  have hε0 : ε ≠ 0 := fun h => hε' ⟨0, by rw [h]; ring⟩
  obtain ⟨u, huS₀, hu⟩ := exists_mem_eq_unit hodd hS₀reg hd2 1
  have hu1 : Q u = 1 := by simpa using hu
  have hu0 : u ≠ 0 := fun h => by rw [h, QuadraticMap.map_zero] at hu1; exact zero_ne_one hu1
  have hpu : polar Q u u = 2 := by
    rw [QuadraticMap.polar_self, hu1, two_smul, one_add_one_eq_two]
  set S₁ : Submodule F V := S₀ ⊓ LinearMap.ker (Q.polarBilin u) with hS₁
  have hS₁mem : ∀ x, x ∈ S₁ ↔ x ∈ S₀ ∧ polar Q u x = 0 := fun x => by
    rw [hS₁, Submodule.mem_inf, LinearMap.mem_ker, polarBilin_apply_apply]
  have hdecomp : ∀ s ∈ S₀, ∃ c : F, s - c • u ∈ S₁ := by
    intro s hs
    refine ⟨polar Q u s / 2, (hS₁mem _).2 ⟨S₀.sub_mem hs (S₀.smul_mem _ huS₀), ?_⟩⟩
    rw [QuadraticMap.polar_sub_right, QuadraticMap.polar_smul_right, hpu, smul_eq_mul,
      div_mul_cancel₀ _ h2, sub_self]
  have hS₁sep : ∀ x ∈ S₁, (∀ y ∈ S₁, polar Q x y = 0) → x = 0 := by
    intro x hx hxperp
    refine hS₀sep x ((hS₁mem x).1 hx).1 fun y hy => ?_
    obtain ⟨c, hc⟩ := hdecomp y hy
    have : y = c • u + (y - c • u) := by abel
    rw [this, QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right, hxperp _ hc,
      QuadraticMap.polar_comm, ((hS₁mem x).1 hx).2]
    ring
  have hS₁reg : (Q.restrict S₁).Nondegenerate := nondegenerate_restrict_of_forall S₁ hS₁sep
  have hspan : Submodule.span F {u} ⊔ S₁ = S₀ := by
    refine le_antisymm (sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 huS₀) inf_le_left) ?_
    intro s hs
    obtain ⟨c, hc⟩ := hdecomp s hs
    have : s = c • u + (s - c • u) := by abel
    rw [this]
    exact Submodule.add_mem_sup (Submodule.mem_span_singleton.2 ⟨c, rfl⟩) hc
  have hspanbot : Submodule.span F {u} ⊓ S₁ = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx.1
    have := ((hS₁mem _).1 hx.2).2
    rw [QuadraticMap.polar_smul_right, hpu] at this
    have hc : c = 0 := by
      have : c * 2 = 0 := by simpa using this
      exact (mul_eq_zero.1 this).resolve_right h2
    rw [hc, zero_smul]
    exact Submodule.zero_mem _
  have hd1 : Module.finrank F S₁ + 1 = Module.finrank F S₀ := by
    have := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span F {u}) S₁
    rw [hspan, hspanbot, finrank_bot, finrank_span_singleton hu0] at this
    omega
  have hS₀S : S₀ ≤ S := inf_le_right
  by_cases hA : 2 ≤ Module.finrank F S₁
  · obtain ⟨v, hvS₁, hv⟩ := exists_mem_eq_unit hodd hS₁reg hA (Units.mk0 ε hε0)
    have hvε : Q v = ε := by simpa using hv
    have := (hS₁mem v).1 hvS₁
    exact ⟨u, hS₀S huS₀, v, hS₀S this.1, hu1, hvε, this.2⟩
  · have hS₁1 : Module.finrank F S₁ = 1 := by omega
    have hR2 : Module.finrank F R = 2 := by omega
    obtain ⟨x₀, hx₀⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := F) (M := S₁)).1 (by omega)
    set v₀ : V := (x₀ : V) with hv₀def
    have hv₀S₁ : v₀ ∈ S₁ := x₀.2
    have hv₀0 : v₀ ≠ 0 := fun h => hx₀ (Subtype.ext h)
    have hone := (finrank_eq_one_iff_of_nonzero' x₀ hx₀).1 hS₁1
    have hQv₀ : Q v₀ ≠ 0 := by
      intro hQ0
      refine hv₀0 (hS₁sep v₀ hv₀S₁ fun y hy => ?_)
      obtain ⟨c, hc⟩ := hone ⟨y, hy⟩
      have : y = c • v₀ := (congrArg Subtype.val hc).symm
      rw [this, QuadraticMap.polar_smul_right, QuadraticMap.polar_self, hQ0]
      simp
    have hu_v₀ : polar Q u v₀ = 0 := ((hS₁mem v₀).1 hv₀S₁).2
    have hsq : IsSquare (Q v₀ / ε) := by
      by_contra hns
      have : Fintype F := Fintype.ofFinite F
      have hnegsq : IsSquare (-Q v₀) := by
        have := isSquare_mul_of_not_isSquare (K := F) hε' hns
        have e : -ε * (Q v₀ / ε) = -Q v₀ := by field_simp
        rwa [e] at this
      obtain ⟨s, hs⟩ := hnegsq
      set x : V := s • u + v₀ with hxdef
      have hxS₀ : x ∈ S₀ := S₀.add_mem (S₀.smul_mem _ huS₀) ((hS₁mem v₀).1 hv₀S₁).1
      have hQx : Q x = 0 := by
        rw [hxdef, QuadraticMap.map_add Q, QuadraticMap.map_smul, hu1, QuadraticMap.polar_smul_left,
          hu_v₀]
        simp only [smul_eq_mul, mul_one, mul_zero, add_zero]
        linear_combination -hs
      have hx0 : x ≠ 0 := by
        intro h
        have h1 : v₀ = -(s • u) := by rw [hxdef] at h; exact eq_neg_of_add_eq_zero_right h
        have h3 : polar Q u v₀ = -(s * 2) := by
          rw [h1, QuadraticMap.polar_neg_right, QuadraticMap.polar_smul_right, hpu, smul_eq_mul]
        rw [hu_v₀] at h3
        have : s = 0 := by
          have : s * 2 = 0 := by linear_combination h3
          exact (mul_eq_zero.1 this).resolve_right h2
        rw [this, zero_smul, neg_zero] at h1
        exact hv₀0 h1
      set T : Submodule F V := R ⊔ Submodule.span F {x} with hTdef
      have hTS : T ≤ S := sup_le hRS ((Submodule.span_singleton_le_iff_mem _ _).2 (hS₀S hxS₀))
      have hTts : ∀ y ∈ T, Q y = 0 := by
        intro y hy
        obtain ⟨r, hr, z, hz, rfl⟩ := Submodule.mem_sup.1 hy
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
        rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, hQx, hRts r hr,
          hRperp r hr (c • x) (S.smul_mem _ (hS₀S hxS₀))]
        simp
      have hRx : R ⊓ Submodule.span F {x} = ⊥ := by
        refine eq_bot_iff.2 fun y hy => ?_
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy.2
        have hcx : c • x ∈ R ⊓ S₀ := ⟨hy.1, S₀.smul_mem _ hxS₀⟩
        rw [hinf] at hcx
        have := (Submodule.mem_bot F).1 hcx
        rcases smul_eq_zero.1 this with hc | hc
        · rw [hc, zero_smul]; exact Submodule.zero_mem _
        · exact absurd hc hx0
      have h3 : Module.finrank F T ≤ 2 := hT T hTS hTts
      have := Submodule.finrank_sup_add_finrank_inf_eq R (Submodule.span F {x})
      rw [← hTdef, hRx, finrank_bot, finrank_span_singleton hx0, hR2] at this
      omega
    obtain ⟨c, hc⟩ := hsq
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hQv₀
      have : Q v₀ / ε = 0 := by rw [hc]; ring
      rcases div_eq_zero_iff.1 this with h | h
      · exact h
      · exact absurd h hε0
    refine ⟨u, hS₀S huS₀, c⁻¹ • v₀, S.smul_mem _ (hS₀S ((hS₁mem v₀).1 hv₀S₁).1), hu1, ?_, ?_⟩
    · rw [QuadraticMap.map_smul, smul_eq_mul]
      have : Q v₀ = ε * (c * c) := by rw [← hc]; field_simp
      rw [this]
      field_simp
    · rw [QuadraticMap.polar_smul_right, hu_v₀, smul_zero]

end CFSG.ClassicalInvolution.PhanP
