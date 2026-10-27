module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1LinCoreCnt

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Planes

open CFSG.Open

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem sub_mem_of_pieces {k : ℕ} {X : Fin k → Submodule (ZMod 2) V} (hsup : iSup X = ⊤)
    (g : V ≃ₗ[ZMod 2] V) (Y : Submodule (ZMod 2) V) (hY : ∀ j, ∀ x ∈ X j, g x - x ∈ Y) :
    ∀ v, g v - v ∈ Y := by
  intro v
  have hv : v ∈ ⨆ j, X j := by rw [hsup]; trivial
  refine Submodule.iSup_induction X (motive := fun v => g v - v ∈ Y) hv ?_ ?_ ?_
  · intro j x hx
    exact hY j x hx
  · simp
  · intro x y hx hy
    have : g (x + y) - (x + y) = (g x - x) + (g y - y) := by
      rw [map_add]; abel
    rw [this]
    exact Y.add_mem hx hy

theorem surj_of_plane {X : Submodule (ZMod 2) V} (hfr : Module.finrank (ZMod 2) X = 2)
    {ρ : V ≃ₗ[ZMod 2] V} (hinv : ∀ x ∈ X, ρ x ∈ X) (hfix : ∀ x ∈ X, ρ x = x → x = 0) :
    ∀ x ∈ X, ∃ y ∈ X, ρ y - y = x := by
  let T : X →ₗ[ZMod 2] X :=
    { toFun := fun y => ⟨ρ y - y, X.sub_mem (hinv y y.2) y.2⟩
      map_add' := fun a b => by
        apply Subtype.ext
        simp only [Submodule.coe_add, Submodule.coe_mk, map_add]
        abel
      map_smul' := fun c a => by
        apply Subtype.ext
        simp only [Submodule.coe_smul, Submodule.coe_mk, map_smul, RingHom.id_apply, smul_sub] }
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro y hy
    rw [LinearMap.mem_ker] at hy
    have h1 : ρ (y : V) - (y : V) = 0 := by
      have := congrArg Subtype.val hy
      simpa [T] using this
    have h2 : ρ (y : V) = (y : V) := sub_eq_zero.1 h1
    have h3 := hfix _ y.2 h2
    rw [Submodule.mem_bot]
    exact Subtype.ext h3
  have hsurj : Function.Surjective T := by
    have hfin : Module.finrank (ZMod 2) X = Module.finrank (ZMod 2) X := rfl
    exact (LinearMap.injective_iff_surjective.1 hinj)
  intro x hx
  obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
  refine ⟨y, y.2, ?_⟩
  have := congrArg Subtype.val hy
  simpa [T] using this

structure PieceData (E : Subgroup (V ≃ₗ[ZMod 2] V)) {k : ℕ} (X : Fin k → Submodule (ZMod 2) V)
    (ρf : Fin k → (V ≃ₗ[ZMod 2] V)) : Prop where
  ab : IsElemAbelian 3 E
  inv : ∀ i, Inv2 E (X i)
  irr : ∀ i, IsIrrE E (X i)
  ind : iSupIndep X
  sup : iSup X = ⊤
  gen : ∀ i, ρf i ∈ E ∧
    ((Module.finrank (ZMod 2) (X i) = 1 ∧ ∀ g ∈ E, ∀ x ∈ X i, g x = x) ∨
      (Module.finrank (ZMod 2) (X i) = 2 ∧ (∀ x ∈ X i, ρf i x = x → x = 0) ∧
        (∀ x ∈ X i, ρf i (ρf i x) + ρf i x + x = 0) ∧
        (∀ g ∈ E, ∃ k : Fin 3, ∀ x ∈ X i, g x = (ρf i ^ (k : ℕ)) x)))

variable {E : Subgroup (V ≃ₗ[ZMod 2] V)} {k : ℕ} {X : Fin k → Submodule (ZMod 2) V}
  {ρf : Fin k → (V ≃ₗ[ZMod 2] V)}

theorem PieceData.line_triv (D : PieceData E X ρf) {i : Fin k}
    (hi : Module.finrank (ZMod 2) (X i) ≠ 2) : ∀ g ∈ E, ∀ x ∈ X i, g x = x := by
  rcases (D.gen i).2 with h | h
  · exact h.2
  · exact absurd h.1 hi

theorem PieceData.plane_fixed (D : PieceData E X ρf) {i : Fin k}
    (hi : Module.finrank (ZMod 2) (X i) = 2) : ∀ x ∈ X i, ρf i x = x → x = 0 := by
  rcases (D.gen i).2 with h | h
  · exact absurd h.1 (by omega)
  · exact h.2.1

theorem PieceData.plane_quad (D : PieceData E X ρf) {i : Fin k}
    (hi : Module.finrank (ZMod 2) (X i) = 2) : ∀ x ∈ X i, ρf i (ρf i x) + ρf i x + x = 0 := by
  rcases (D.gen i).2 with h | h
  · exact absurd h.1 (by omega)
  · exact h.2.2.1

theorem PieceData.gen_mem (D : PieceData E X ρf) (i : Fin k) : ρf i ∈ E := (D.gen i).1

theorem range_sub_eq_plane (D : PieceData E X ρf) {p : Fin k}
    (hp : Module.finrank (ZMod 2) (X p) = 2) {e : V ≃ₗ[ZMod 2] V} (he : e ∈ E)
    (hep : ∀ x ∈ X p, e x = ρf p x)
    (hfix : ∀ j, j ≠ p → ∀ x ∈ X j, e x = x) :
    LinearMap.range ((e : V →ₗ[ZMod 2] V) - LinearMap.id) = X p := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    have hsub := sub_mem_of_pieces D.sup e (X p) (fun j x hx => by
      by_cases hjp : j = p
      · subst hjp
        rw [hep x hx]
        exact (X j).sub_mem ((D.inv j) (ρf j) (D.gen_mem j) x hx) hx
      · rw [hfix j hjp x hx, sub_self]
        exact (X p).zero_mem)
    simpa using hsub v
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := surj_of_plane hp (D.inv p (ρf p) (D.gen_mem p)) (D.plane_fixed hp) x hx
    refine ⟨y, ?_⟩
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe]
    rw [hep y hy, hyx]

abbrev DualData (E : Subgroup (V ≃ₗ[ZMod 2] V)) (X : Fin k → Submodule (ZMod 2) V)
    (ρf : Fin k → (V ≃ₗ[ZMod 2] V)) : Prop :=
  ∀ j, Module.finrank (ZMod 2) (X j) = 2 → ∃ e ∈ E, (∀ x ∈ X j, e x = ρf j x) ∧
    (∀ l, l ≠ j → ∀ x ∈ X l, e x = x)

theorem map_range_le_of_comm (g h : V ≃ₗ[ZMod 2] V) (hgh : g * h = h * g) :
    (LinearMap.range ((h : V →ₗ[ZMod 2] V) - LinearMap.id)).map (g : V →ₗ[ZMod 2] V) ≤
      LinearMap.range ((h : V →ₗ[ZMod 2] V) - LinearMap.id) := by
  rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
  refine ⟨g v, ?_⟩
  have hc : ∀ w, g (h w) = h (g w) := fun w => by
    rw [← LinearEquiv.mul_apply, hgh, LinearEquiv.mul_apply]
  simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe, LinearMap.coe_coe]
  rw [← hc]
  simp

theorem sup_pair_eq (X : Fin k → Submodule (ZMod 2) V) (p₁ p₂ : Fin k) :
    (⨆ i ∈ ({p₁, p₂} : Set (Fin k)), X i) = X p₁ ⊔ X p₂ := by
  apply le_antisymm
  · refine iSup₂_le fun i hi => ?_
    rcases hi with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  · exact sup_le (le_iSup₂_of_le p₁ (by simp) le_rfl) (le_iSup₂_of_le p₂ (by simp) le_rfl)

theorem isCompl_pair (D : PieceData E X ρf) {p₁ p₂ : Fin k} (hne : p₁ ≠ p₂) :
    IsCompl (⨆ i ∈ ({p₁, p₂} : Set (Fin k)), X i) (⨆ i ∈ ({p₁, p₂} : Set (Fin k))ᶜ, X i) := by
  have hdisj : Disjoint (⨆ i ∈ ({p₁, p₂} : Set (Fin k)), X i)
      (⨆ i ∈ ({p₁, p₂} : Set (Fin k))ᶜ, X i) :=
    D.ind.disjoint_biSup_biSup' disjoint_compl_right (Set.toFinite _)
  refine ⟨hdisj, codisjoint_iff.2 (eq_top_iff.2 ?_)⟩
  rw [← D.sup]
  refine iSup_le fun i => ?_
  by_cases hi : i ∈ ({p₁, p₂} : Set (Fin k))
  · exact le_sup_of_le_left (le_iSup₂_of_le i hi le_rfl)
  · exact le_sup_of_le_right (le_iSup₂_of_le i hi le_rfl)

theorem expo_eq_of_pow (D : PieceData E X ρf) {i : Fin k}
    (hi : Module.finrank (ZMod 2) (X i) = 2) {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ E) {c : Fin 3}
    (h : ∀ x ∈ X i, g x = (ρf i ^ (c : ℕ)) x) : expo ρf X i g = c := by
  have hpow : ∀ g ∈ E, ∃ k : Fin 3, ∀ x ∈ X i, g x = (ρf i ^ (k : ℕ)) x := by
    rcases (D.gen i).2 with h' | h'
    · exact absurd h'.1 (by omega)
    · exact h'.2.2.2
  exact expo_unique D.ab (D.irr i) (D.gen_mem i) (D.plane_fixed hi)
    (fun x hx => (expo_spec (hpow g hg) x hx).symm.trans (h x hx))

theorem expo_add (D : PieceData E X ρf) {i : Fin k}
    (hi : Module.finrank (ZMod 2) (X i) = 2) {g h : V ≃ₗ[ZMod 2] V} (hg : g ∈ E) (hh : h ∈ E) :
    expo ρf X i (g * h) = expo ρf X i g + expo ρf X i h := by
  have hpow : ∀ g ∈ E, ∃ k : Fin 3, ∀ x ∈ X i, g x = (ρf i ^ (k : ℕ)) x := by
    rcases (D.gen i).2 with h' | h'
    · exact absurd h'.1 (by omega)
    · exact h'.2.2.2
  exact expo_mul D.ab D.inv (D.irr i) (D.gen_mem i) (D.plane_fixed hi) hpow hg hh

theorem expo_eq_zero_of_fix (D : PieceData E X ρf) {i : Fin k}
    (hi : Module.finrank (ZMod 2) (X i) = 2) {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ E)
    (h : ∀ x ∈ X i, g x = x) : expo ρf X i g = 0 :=
  expo_eq_of_pow D hi hg (c := 0) (fun x hx => by
    show g x = (ρf i ^ (0 : ℕ)) x
    rw [pow_zero]
    exact h x hx)

abbrev Pres (Y : Submodule (ZMod 2) V) (g : V ≃ₗ[ZMod 2] V) : Prop := ∀ x ∈ Y, g x ∈ Y

theorem pres_iSup {ι : Sort*} (Y : ι → Submodule (ZMod 2) V) (g : V ≃ₗ[ZMod 2] V)
    (h : ∀ i, Pres (Y i) g) : Pres (⨆ i, Y i) g := by
  intro x hx
  refine Submodule.iSup_induction Y (motive := fun x => g x ∈ ⨆ i, Y i) hx
    (fun i y hy => Submodule.mem_iSup_of_mem i (h i y hy)) (by simp)
    (fun a b ha hb => by rw [map_add]; exact Submodule.add_mem _ ha hb)

theorem pres_Uc (S : Set (Fin k)) (g : V ≃ₗ[ZMod 2] V) (h : ∀ i ∈ Sᶜ, Pres (X i) g) :
    Pres (⨆ i ∈ Sᶜ, X i) g := by
  apply pres_iSup
  intro i
  by_cases hi : i ∈ Sᶜ
  · simp only [hi, iSup_pos]
    exact h i hi
  · simp only [hi, iSup_neg]
    intro x hx
    simpa using hx

theorem range_pair (D : PieceData E X ρf) {p₁ p₂ : Fin k} (hp₁ : Module.finrank (ZMod 2) (X p₁) = 2)
    (hp₂ : Module.finrank (ZMod 2) (X p₂) = 2) (hne : p₁ ≠ p₂)
    {e₁ e₂ : V ≃ₗ[ZMod 2] V} (h₁ : ∀ x ∈ X p₁, e₁ x = ρf p₁ x)
    (h₁' : ∀ j, j ≠ p₁ → ∀ x ∈ X j, e₁ x = x)
    (h₂ : ∀ x ∈ X p₂, e₂ x = ρf p₂ x) (h₂' : ∀ j, j ≠ p₂ → ∀ x ∈ X j, e₂ x = x) :
    LinearMap.range (((e₁ * e₂ : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) - LinearMap.id) =
      X p₁ ⊔ X p₂ := by
  have f1 : ∀ x ∈ X p₁, (e₁ * e₂) x = ρf p₁ x := by
    intro x hx
    rw [LinearEquiv.mul_apply, h₂' p₁ hne x hx, h₁ x hx]
  have f2 : ∀ x ∈ X p₂, (e₁ * e₂) x = ρf p₂ x := by
    intro x hx
    rw [LinearEquiv.mul_apply, h₂ x hx, h₁' p₂ (Ne.symm hne) _
      (D.inv p₂ (ρf p₂) (D.gen_mem p₂) x hx)]
  have f3 : ∀ j, j ≠ p₁ → j ≠ p₂ → ∀ x ∈ X j, (e₁ * e₂) x = x := by
    intro j hj1 hj2 x hx
    rw [LinearEquiv.mul_apply, h₂' j hj2 x hx, h₁' j hj1 x hx]
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    have hsub := sub_mem_of_pieces D.sup (e₁ * e₂) (X p₁ ⊔ X p₂) (fun j x hx => by
      by_cases hj1 : j = p₁
      · subst hj1
        have := f1 x hx
        rw [this]
        exact Submodule.mem_sup_left ((D.inv j) (ρf j) (D.gen_mem j) x hx |> fun hh =>
          (X j).sub_mem hh hx)
      · by_cases hj2 : j = p₂
        · subst hj2
          rw [f2 x hx]
          exact Submodule.mem_sup_right ((X j).sub_mem ((D.inv j) (ρf j) (D.gen_mem j) x hx) hx)
        · rw [f3 j hj1 hj2 x hx, sub_self]
          exact Submodule.zero_mem _)
    simpa using hsub v
  · refine sup_le ?_ ?_
    · intro x hx
      obtain ⟨y, hy, hyx⟩ := surj_of_plane hp₁ (D.inv p₁ (ρf p₁) (D.gen_mem p₁)) (D.plane_fixed hp₁) x hx
      refine ⟨y, ?_⟩
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe]
      rw [f1 y hy, hyx]
    · intro x hx
      obtain ⟨y, hy, hyx⟩ := surj_of_plane hp₂ (D.inv p₂ (ρf p₂) (D.gen_mem p₂)) (D.plane_fixed hp₂) x hx
      refine ⟨y, ?_⟩
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe]
      rw [f2 y hy, hyx]

theorem fixed_pair (D : PieceData E X ρf) {p₁ p₂ : Fin k} (hp₁ : Module.finrank (ZMod 2) (X p₁) = 2)
    (hp₂ : Module.finrank (ZMod 2) (X p₂) = 2) (hne : p₁ ≠ p₂)
    {f : V ≃ₗ[ZMod 2] V} (hf₁ : ∀ x ∈ X p₁, f x = ρf p₁ x) (hf₂ : ∀ x ∈ X p₂, f x = ρf p₂ x)
    {u : V} (hu : u ∈ X p₁ ⊔ X p₂) (hfu : f u = u) : u = 0 := by
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.1 hu
  rw [map_add, hf₁ u₁ hu₁, hf₂ u₂ hu₂] at hfu
  have h1 : ρf p₁ u₁ - u₁ = u₂ - ρf p₂ u₂ := by
    have h0 : ρf p₁ u₁ + ρf p₂ u₂ - (u₁ + u₂) = 0 := sub_eq_zero.2 hfu
    rw [← sub_eq_zero, ← h0]
    abel
  have hdisj : Disjoint (X p₁) (X p₂) := D.ind.pairwiseDisjoint hne
  have ha : ρf p₁ u₁ - u₁ ∈ X p₁ ⊓ X p₂ := by
    refine ⟨(X p₁).sub_mem (D.inv p₁ (ρf p₁) (D.gen_mem p₁) u₁ hu₁) hu₁, ?_⟩
    rw [h1]
    exact (X p₂).sub_mem hu₂ ((D.inv p₂ (ρf p₂) (D.gen_mem p₂) u₂ hu₂))
  have ha0 : ρf p₁ u₁ - u₁ = 0 := by
    have hbot : X p₁ ⊓ X p₂ = ⊥ := disjoint_iff.1 hdisj
    rw [hbot] at ha
    exact (Submodule.mem_bot _).1 ha
  have hb0 : u₂ - ρf p₂ u₂ = 0 := by
    rw [← h1]
    exact ha0
  have hu1 : u₁ = 0 := D.plane_fixed hp₁ u₁ hu₁ (sub_eq_zero.1 ha0)
  have hu2 : u₂ = 0 := D.plane_fixed hp₂ u₂ hu₂ (sub_eq_zero.1 hb0).symm
  rw [hu1, hu2, add_zero]

theorem pres_range_of_comm (E : Subgroup (V ≃ₗ[ZMod 2] V)) (hE : IsElemAbelian 3 E)
    {f₁ f : V ≃ₗ[ZMod 2] V} (hf₁ : f₁ ∈ E) (hf : f ∈ E) :
    Pres (LinearMap.range ((f₁ : V →ₗ[ZMod 2] V) - LinearMap.id)) f := by
  intro x hx
  have hc : f * f₁ = f₁ * f := comm_of_mem hE hf hf₁
  have := map_range_le_of_comm f f₁ hc
  exact this ⟨x, hx, rfl⟩

theorem pres_Uc_of_dual (D : PieceData E X ρf) (hdual : DualData E X ρf) {p₁ p₂ : Fin k}
    (f : V ≃ₗ[ZMod 2] V) (hf : f ∈ E) :
    Pres (⨆ i ∈ ({p₁, p₂} : Set (Fin k))ᶜ, X i) f := by
  apply pres_Uc ({p₁, p₂} : Set (Fin k)) f
  intro j _
  by_cases hpl : Module.finrank (ZMod 2) (X j) = 2
  · obtain ⟨e, he, hep, hefix⟩ := hdual j hpl
    have hc : f * e = e * f := comm_of_mem D.ab hf he
    have hr := range_sub_eq_plane D hpl he hep hefix
    intro x hx
    have hx' : x ∈ LinearMap.range ((e : V →ₗ[ZMod 2] V) - LinearMap.id) := by
      rw [hr]
      exact hx
    have hfx := map_range_le_of_comm f e hc (Submodule.mem_map_of_mem hx')
    rw [hr] at hfx
    exact hfx
  · intro x hx
    rw [D.line_triv hpl f hf x hx]
    exact hx

theorem iSup_map_le {ι : Sort*} (Y : ι → Submodule (ZMod 2) V) (Z : Submodule (ZMod 2) V)
    (g : V ≃ₗ[ZMod 2] V) (h : ∀ i, ∀ x ∈ Y i, g x ∈ Z) : ∀ x ∈ ⨆ i, Y i, g x ∈ Z := by
  intro x hx
  refine Submodule.iSup_induction Y (motive := fun x => g x ∈ Z) hx (fun i y hy => h i y hy)
    (by simp) (fun a b ha hb => by rw [map_add]; exact Z.add_mem ha hb)

theorem pres_Uc_of_mem (S : Set (Fin k)) (g : V ≃ₗ[ZMod 2] V)
    (h : ∀ j, j ∈ Sᶜ → ∀ x ∈ X j, g x ∈ ⨆ i ∈ Sᶜ, X i) :
    Pres (⨆ i ∈ Sᶜ, X i) g := by
  intro x hx
  refine iSup_map_le (fun i => ⨆ (_ : i ∈ Sᶜ), X i) (⨆ i ∈ Sᶜ, X i) g ?_ x hx
  intro i y hy
  by_cases hi : i ∈ Sᶜ
  · rw [iSup_pos hi] at hy
    exact h i hi y hy
  · rw [iSup_neg hi] at hy
    rw [(Submodule.mem_bot _).1 hy, map_zero]
    exact Submodule.zero_mem _

theorem fix_mem_Uc (D : PieceData E X ρf) {p₁ p₂ : Fin k}
    (hp₁ : Module.finrank (ZMod 2) (X p₁) = 2) (hp₂ : Module.finrank (ZMod 2) (X p₂) = 2)
    (hne : p₁ ≠ p₂)
    {f₁ : V ≃ₗ[ZMod 2] V} (hf₁a : ∀ x ∈ X p₁, f₁ x = ρf p₁ x)
    (hf₁b : ∀ x ∈ X p₂, f₁ x = ρf p₂ x)
    (F : Set (V ≃ₗ[ZMod 2] V)) (hf₁F : f₁ ∈ F)
    (hFU : ∀ f ∈ F, Pres (X p₁ ⊔ X p₂) f)
    (hFUc : ∀ f ∈ F, Pres (⨆ i ∈ ({p₁, p₂} : Set (Fin k))ᶜ, X i) f)
    (v : V) (hv : ∀ f ∈ F, f v = v) :
    v ∈ ⨆ i ∈ ({p₁, p₂} : Set (Fin k))ᶜ, X i := by
  have hc : IsCompl (X p₁ ⊔ X p₂) (⨆ i ∈ ({p₁, p₂} : Set (Fin k))ᶜ, X i) :=
    (sup_pair_eq X p₁ p₂) ▸ isCompl_pair D hne
  have hv' : v ∈ (X p₁ ⊔ X p₂) ⊔ (⨆ i ∈ ({p₁, p₂} : Set (Fin k))ᶜ, X i) := by
    rw [hc.sup_eq_top]
    trivial
  obtain ⟨u, hu, u', hu', rfl⟩ := Submodule.mem_sup.1 hv'
  have hfix : ∀ f ∈ F, f u = u := by
    intro f hf
    have h1 := hv f hf
    rw [map_add] at h1
    have hmemU : f u - u ∈ X p₁ ⊔ X p₂ := (X p₁ ⊔ X p₂).sub_mem (hFU f hf u hu) hu
    have hmemUc : f u - u ∈ ⨆ i ∈ ({p₁, p₂} : Set (Fin k))ᶜ, X i := by
      have heq : f u - u = u' - f u' := by
        rw [← sub_eq_zero] at h1 ⊢
        rw [← h1]
        abel
      rw [heq]
      exact (⨆ i ∈ ({p₁, p₂} : Set (Fin k))ᶜ, X i).sub_mem hu' (hFUc f hf u' hu')
    have hzero : f u - u ∈ (X p₁ ⊔ X p₂) ⊓ (⨆ i ∈ ({p₁, p₂} : Set (Fin k))ᶜ, X i) :=
      ⟨hmemU, hmemUc⟩
    rw [hc.disjoint.eq_bot] at hzero
    exact sub_eq_zero.1 ((Submodule.mem_bot _).1 hzero)
  have hu0 : u = 0 := fixed_pair D hp₁ hp₂ hne hf₁a hf₁b hu (hfix f₁ hf₁F)
  rw [hu0, zero_add]
  exact hu'

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Planes

end
