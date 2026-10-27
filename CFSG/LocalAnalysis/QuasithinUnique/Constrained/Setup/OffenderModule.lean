module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderGroup
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderField

public section

namespace CFSG.QuasithinUnique.Setup.Offender

open scoped commutatorElement

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
variable {A : Type*} [Group A]

theorem mem_commSub_of {ρ : A →* (V ≃ₗ[k] V)} {B : Subgroup A} {U : Submodule k V} {b : A}
    (hb : b ∈ B) {u : V} (hu : u ∈ U) : ρ b u - u ∈ commSub ρ B U :=
  Submodule.subset_span ⟨b, hb, u, hu, rfl⟩

theorem map_mem_commSub_top (ρ : A →* (V ≃ₗ[k] V)) (g : A) {u : V}
    (hu : u ∈ commSub ρ ⊤ ⊤) : ρ g u ∈ commSub ρ ⊤ ⊤ := by
  induction hu using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨b, -, u0, -, rfl⟩ := hw
    have : ρ g (ρ b u0 - u0) = ρ (g * b * g⁻¹) (ρ g u0) - ρ g u0 := by
      rw [map_sub, ρ_mul_apply, ρ_mul_apply, ρ_inv_apply]
    rw [this]
    exact mem_commSub_of (Subgroup.mem_top _) Submodule.mem_top
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

theorem commSub_commSub_of_perfect (ρ : A →* (V ≃ₗ[k] V)) (hA : Group.IsPerfect A) :
    commSub ρ ⊤ (commSub ρ ⊤ ⊤) = commSub ρ ⊤ ⊤ := by
  set U := commSub ρ ⊤ ⊤ with hU
  set K := commSub ρ ⊤ U with hK
  have hKU : K ≤ U := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, -, u, hu, rfl⟩
    exact Submodule.sub_mem _ (map_mem_commSub_top ρ b hu) hu
  refine le_antisymm hKU ?_
  let S : Subgroup A :=
    { carrier := {g | ∀ v, ρ g v - v ∈ K}
      one_mem' := fun v => by simp
      mul_mem' := fun {a b} ha hb v => by
        have := Submodule.add_mem K (ha (ρ b v)) (hb v)
        rw [sub_add_sub_cancel] at this
        rwa [ρ_mul_apply]
      inv_mem' := fun {a} ha v => by
        have := K.neg_mem (ha (ρ a⁻¹ v))
        rw [ρ_apply_inv, neg_sub] at this
        exact this }
  have hS : S = ⊤ := by
    rw [eq_top_iff, ← hA.commutator_eq_top, commutator_def, Subgroup.commutator_le]
    intro g1 _ g2 _ v
    obtain ⟨w, hw⟩ : ∃ w, w = ρ (g1⁻¹ * g2⁻¹) v := ⟨_, rfl⟩
    have hv : v = ρ g2 (ρ g1 w) := by
      rw [hw, ← ρ_mul_apply, ← ρ_mul_apply, ← mul_assoc]; simp
    have hρc : ρ ⁅g1, g2⁆ v = ρ g1 (ρ g2 w) := by
      rw [hw, commutatorElement_def, ← ρ_mul_apply, ← ρ_mul_apply]
      simp only [mul_assoc]
    show ρ ⁅g1, g2⁆ v - v ∈ K
    have hc : ρ g1 (ρ g2 w) - v =
        (ρ g1 (ρ g2 w - w) - (ρ g2 w - w)) - (ρ g2 (ρ g1 w - w) - (ρ g1 w - w)) := by
      rw [hv]; simp only [map_sub]; abel
    rw [hρc, hc]
    exact K.sub_mem
      (mem_commSub_of (Subgroup.mem_top _) (mem_commSub_of (Subgroup.mem_top _) Submodule.mem_top))
      (mem_commSub_of (Subgroup.mem_top _) (mem_commSub_of (Subgroup.mem_top _) Submodule.mem_top))
  refine Submodule.span_le.2 ?_
  rintro _ ⟨b, -, u, -, rfl⟩
  have : b ∈ S := by rw [hS]; trivial
  exact this u

abbrev fixGL (H : Subgroup (V ≃ₗ[k] V)) : Submodule k V :=
  fixSub (MonoidHom.id (V ≃ₗ[k] V)) H

abbrev commGL (H : Subgroup (V ≃ₗ[k] V)) (U : Submodule k V) : Submodule k V :=
  commSub (MonoidHom.id (V ≃ₗ[k] V)) H U

theorem mem_fixGL {H : Subgroup (V ≃ₗ[k] V)} {v : V} : v ∈ fixGL H ↔ ∀ h ∈ H, h v = v := Iff.rfl

@[expose] def trivMod (Z : Submodule k V) : Subgroup (V ≃ₗ[k] V) where
  carrier := {x | ∀ w, x w - w ∈ Z}
  one_mem' := fun w => by simp
  mul_mem' := fun {a b} ha hb w => by
    have := Z.add_mem (ha (b w)) (hb w)
    rw [sub_add_sub_cancel] at this
    exact this
  inv_mem' := fun {a} ha w => by
    have := Z.neg_mem (ha (a⁻¹ w))
    have h2 : a (a⁻¹ w) = w := by
      rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl
    rw [h2, neg_sub] at this
    exact this

theorem mem_trivMod {Z : Submodule k V} {x : V ≃ₗ[k] V} :
    x ∈ trivMod Z ↔ ∀ w, x w - w ∈ Z := Iff.rfl

theorem conj_mem_trivMod {Z : Submodule k V} {g x : V ≃ₗ[k] V} (hg : ∀ z ∈ Z, g z ∈ Z)
    (hx : x ∈ trivMod Z) : g * x * g⁻¹ ∈ trivMod Z := by
  intro w
  have h2 : g (g⁻¹ w) = w := by
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl
  have := hg _ (hx (g⁻¹ w))
  rw [map_sub, h2] at this
  simpa [LinearEquiv.mul_apply, h2] using this

theorem trivMod_commute {Z : Submodule k V} {x y : V ≃ₗ[k] V} (hxZ : ∀ z ∈ Z, x z = z)
    (hyZ : ∀ z ∈ Z, y z = z) (hx : x ∈ trivMod Z) (hy : y ∈ trivMod Z) : x * y = y * x := by
  ext w
  have h1 : x (y w) = (y w - w) + x w := by
    have : x (y w - w) = y w - w := hxZ _ (hy w)
    rw [map_sub] at this
    exact sub_eq_iff_eq_add.1 this
  have h2 : y (x w) = (x w - w) + y w := by
    have : y (x w - w) = x w - w := hyZ _ (hx w)
    rw [map_sub] at this
    exact sub_eq_iff_eq_add.1 this
  show x (y w) = y (x w)
  rw [h1, h2]
  abel

theorem trivMod_pow {Z : Submodule k V} {x : V ≃ₗ[k] V} (hxZ : ∀ z ∈ Z, x z = z)
    (hx : x ∈ trivMod Z) (m : ℕ) (w : V) : (x ^ m) w = w + m • (x w - w) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', LinearEquiv.mul_apply, ih, map_add, map_nsmul, hxZ _ (hx w), succ_nsmul]
    abel

theorem trivMod_pow_char {p : ℕ} [CharP k p] {Z : Submodule k V} {x : V ≃ₗ[k] V}
    (hxZ : ∀ z ∈ Z, x z = z) (hx : x ∈ trivMod Z) : x ^ p = 1 := by
  ext w
  rw [trivMod_pow hxZ hx, ← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul, add_zero]
  rfl

theorem trivMod_inf_elementary {p : ℕ} [CharP k p] (H : Subgroup (V ≃ₗ[k] V)) :
    CFSG.IsElementaryAbelian p ((H ⊓ trivMod (fixGL H)).subgroupOf H) := by
  have hfix : ∀ x ∈ H, ∀ z ∈ fixGL H, x z = z := fun x hx z hz => hz x hx
  refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
  · apply Subtype.ext
    apply Subtype.ext
    have ha : (a.1 : V ≃ₗ[k] V) ∈ H ⊓ trivMod (fixGL H) := a.2
    have hb : (b.1 : V ≃ₗ[k] V) ∈ H ⊓ trivMod (fixGL H) := b.2
    exact trivMod_commute (hfix _ ha.1) (hfix _ hb.1) ha.2 hb.2
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun a => ?_
    apply Subtype.ext
    apply Subtype.ext
    have ha : (a.1 : V ≃ₗ[k] V) ∈ H ⊓ trivMod (fixGL H) := a.2
    exact trivMod_pow_char (hfix _ ha.1) ha.2

theorem commutatorModule_fixedQuotient_detects {p : ℕ} [CharP k p]
    (H : Subgroup (V ≃ₗ[k] V)) (hno : NoPQuotient p H)
    (hcent : ∀ E : Subgroup H, E.Normal → CFSG.IsElementaryAbelian p E → E ≤ Subgroup.center H)
    (hV : commGL H ⊤ = ⊤) :
    (∀ b ∈ Subgroup.normalizer (H : Set (V ≃ₗ[k] V)), ∀ z ∈ fixGL H, b z ∈ fixGL H) ∧
    (∀ b ∈ Subgroup.normalizer (H : Set (V ≃ₗ[k] V)), (∀ w, b w - w ∈ fixGL H) → b = 1) := by
  have hfix : ∀ x ∈ H, ∀ z ∈ fixGL H, x z = z := fun x hx z hz => hz x hx
  have hinv : ∀ b ∈ Subgroup.normalizer (H : Set (V ≃ₗ[k] V)), ∀ z ∈ fixGL H, b z ∈ fixGL H := by
    intro b hb z hz h hh
    have hb' : b⁻¹ * h * b ∈ H := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hb) h).1 hh
      simpa using this
    have h1 : (b⁻¹ * h * b) z = z := hz _ hb'
    have e1 : b ((b⁻¹ * h * b) z) = h (b z) := by
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, gl_apply_inv_apply]
    show h (b z) = b z
    rw [← e1, h1]
  refine ⟨hinv, fun b hb hbt => ?_⟩
  set K : Subgroup H := (H ⊓ trivMod (fixGL H)).subgroupOf H with hK
  have hKn : K.Normal := ⟨fun x hx g => by
    rw [hK, Subgroup.mem_subgroupOf] at hx ⊢
    refine ⟨(g * x * g⁻¹).2, ?_⟩
    exact conj_mem_trivMod (fun z hz => by rw [hfix _ g.2 z hz]; exact hz) hx.2⟩
  have hKc : K ≤ Subgroup.center H := hcent K hKn (trivMod_inf_elementary H)
  have hbTr : b ∈ trivMod (fixGL H) := hbt
  let c : H → (V ≃ₗ[k] V) := fun h => (h : V ≃ₗ[k] V)⁻¹ * b⁻¹ * (h : V ≃ₗ[k] V) * b
  have hcH : ∀ h : H, c h ∈ H := by
    intro h
    have hb' : b⁻¹ * (h : V ≃ₗ[k] V) * b ∈ H := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hb) h).1 h.2
      simpa using this
    have : c h = (h : V ≃ₗ[k] V)⁻¹ * (b⁻¹ * (h : V ≃ₗ[k] V) * b) := by simp [c, mul_assoc]
    rw [this]
    exact H.mul_mem (H.inv_mem h.2) hb'
  have hcTr : ∀ h : H, c h ∈ trivMod (fixGL H) := by
    intro h
    have hhinv : (h : V ≃ₗ[k] V)⁻¹ ∈ H := H.inv_mem h.2
    have h1 := conj_mem_trivMod (g := (h : V ≃ₗ[k] V)⁻¹) (x := b⁻¹)
      (fun z hz => by rw [hfix _ hhinv z hz]; exact hz) ((trivMod (fixGL H)).inv_mem hbTr)
    have := (trivMod (fixGL H)).mul_mem h1 hbTr
    simpa [c, mul_assoc] using this
  have hcK : ∀ h : H, (⟨c h, hcH h⟩ : H) ∈ K := fun h => ⟨hcH h, hcTr h⟩
  have hccent : ∀ h h' : H, c h * (h' : V ≃ₗ[k] V) = (h' : V ≃ₗ[k] V) * c h := fun h h' => by
    have := Subgroup.mem_center_iff.1 (hKc (hcK h)) h'
    exact (congrArg Subtype.val this).symm
  let φ : H →* (V ≃ₗ[k] V) :=
    { toFun := c
      map_one' := by simp [c]
      map_mul' := fun h h' => by
        have key : (h' : V ≃ₗ[k] V)⁻¹ * c h = c h * (h' : V ≃ₗ[k] V)⁻¹ := by
          have := hccent h h'
          calc (h' : V ≃ₗ[k] V)⁻¹ * c h
              = (h' : V ≃ₗ[k] V)⁻¹ * (c h * (h' : V ≃ₗ[k] V)) * (h' : V ≃ₗ[k] V)⁻¹ := by group
            _ = (h' : V ≃ₗ[k] V)⁻¹ * ((h' : V ≃ₗ[k] V) * c h) * (h' : V ≃ₗ[k] V)⁻¹ := by
                rw [this]
            _ = c h * (h' : V ≃ₗ[k] V)⁻¹ := by group
        show ((h : V ≃ₗ[k] V) * (h' : V ≃ₗ[k] V))⁻¹ * b⁻¹ * ((h : V ≃ₗ[k] V) * (h' : V ≃ₗ[k] V)) * b
          = c h * c h'
        calc ((h : V ≃ₗ[k] V) * (h' : V ≃ₗ[k] V))⁻¹ * b⁻¹ *
              ((h : V ≃ₗ[k] V) * (h' : V ≃ₗ[k] V)) * b
            = (h' : V ≃ₗ[k] V)⁻¹ * c h * (b⁻¹ * (h' : V ≃ₗ[k] V) * b) := by simp only [c]; group
          _ = c h * (h' : V ≃ₗ[k] V)⁻¹ * (b⁻¹ * (h' : V ≃ₗ[k] V) * b) := by rw [key]
          _ = c h * c h' := by simp only [c]; group }
  have hpg : IsPGroup p (H ⧸ φ.ker) := by
    intro g
    induction g using QuotientGroup.induction_on with | _ h =>
    refine ⟨1, ?_⟩
    rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, MonoidHom.mem_ker, map_pow]
    exact trivMod_pow_char (fun z hz => hfix _ (hcH h) z hz) (hcTr h)
  have hker : φ.ker = ⊤ := hno φ.ker hpg
  have hbcomm : ∀ h ∈ H, b * h = h * b := by
    intro h hh
    have h1 : φ ⟨h, hh⟩ = 1 := MonoidHom.mem_ker.1 (by rw [hker]; trivial)
    have h2 : (h⁻¹ * b⁻¹ * h * b : V ≃ₗ[k] V) = 1 := h1
    have h3 : b⁻¹ * h * b = h := by
      have := congrArg (fun x : V ≃ₗ[k] V => h * x) h2
      simpa [mul_assoc] using this
    calc b * h = b * (b⁻¹ * h * b) := by rw [h3]
      _ = h * b := by group
  have hbfix : ∀ v ∈ commGL H ⊤, b v = v := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨h, hh, u, -, rfl⟩ := hw
      show b (h u - u) = h u - u
      have hz : b u - u ∈ fixGL H := hbt u
      have e1 : b (h u) = h (b u) := by
        rw [← LinearEquiv.mul_apply, hbcomm h hh]; rfl
      have e2 : h (b u - u) = b u - u := hfix h hh _ hz
      rw [map_sub] at e2
      rw [map_sub, e1]
      exact sub_eq_sub_iff_sub_eq_sub.2 e2
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | smul r x _ hx => rw [map_smul, hx]
  exact LinearEquiv.ext fun v => hbfix v (by rw [hV]; trivial)

end CFSG.QuasithinUnique.Setup.Offender
