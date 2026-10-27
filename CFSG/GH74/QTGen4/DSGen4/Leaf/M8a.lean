module

public import CFSG.GH74.QTGen4.DSGen4.OpenLeaves

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

private theorem card_hom_units_eq (A : Type) [CommGroup A] [Finite A] :
    Nat.card (A →* ℂˣ) = Nat.card A := by
  haveI : NeZero (Monoid.exponent A) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity A ℂ

theorem leafM8a : LeafM8a := by
  classical
  intro G _ _ V Z hs hZ hc hz
  obtain ⟨-, -, -⟩ := hs
  intro g hg hgZ
  have hZ2 : ∀ a ∈ Z, ∀ b ∈ Z, a ≠ 1 → b ≠ 1 → a = b := by
    intro a ha b hb ha1 hb1
    obtain ⟨x, y, -, hall⟩ := Nat.card_eq_two_iff.mp hZ
    have hmem : ∀ w : Z, w = x ∨ w = y := fun w => by
      have : w ∈ ({x, y} : Set Z) := by rw [hall]; exact Set.mem_univ w
      simpa using this
    have hA : (⟨a, ha⟩ : Z) ≠ ⟨1, Z.one_mem⟩ := fun h => ha1 (congrArg Subtype.val h)
    have hB : (⟨b, hb⟩ : Z) ≠ ⟨1, Z.one_mem⟩ := fun h => hb1 (congrArg Subtype.val h)
    rcases hmem ⟨1, Z.one_mem⟩ with h1 | h1
    · have ea := (hmem ⟨a, ha⟩).resolve_left (fun h => hA (h.trans h1.symm))
      have eb := (hmem ⟨b, hb⟩).resolve_left (fun h => hB (h.trans h1.symm))
      exact congrArg Subtype.val (ea.trans eb.symm)
    · have ea := (hmem ⟨a, ha⟩).resolve_right (fun h => hA (h.trans h1.symm))
      have eb := (hmem ⟨b, hb⟩).resolve_right (fun h => hB (h.trans h1.symm))
      exact congrArg Subtype.val (ea.trans eb.symm)
  have hZcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := by
    intro a ha b hb
    by_cases h1 : a = 1
    · simp [h1]
    by_cases h2 : b = 1
    · simp [h2]
    rw [hZ2 a ha b hb h1 h2]
  have hsq1 : ∀ a ∈ Z, a * a = 1 := by
    intro a ha
    by_cases h1 : a = 1
    · rw [h1, mul_one]
    · by_contra h2
      have h3 : a * a = a := hZ2 _ (Z.mul_mem ha ha) a ha h2 h1
      have h4 : a * a = a * 1 := by rw [mul_one]; exact h3
      exact h1 (mul_left_cancel h4)
  have hneg : (-1 : ℂˣ) * (-1) = 1 := by ext; simp
  have hneg1 : (-1 : ℂˣ) ≠ 1 := by
    intro h
    have := congrArg Units.val h
    norm_num at this
  obtain ⟨ζ, hζ1, hζne⟩ : ∃ ζ : G → ℂˣ, ζ 1 = 1 ∧ ∀ x : G, x ≠ 1 → ζ x = -1 :=
    ⟨fun x => if x = 1 then 1 else -1, by simp, fun x hx => by simp [hx]⟩
  have hζiff : ∀ x : G, ζ x = 1 ↔ x = 1 := by
    intro x
    by_cases hx : x = 1
    · subst hx; exact ⟨fun _ => rfl, fun _ => hζ1⟩
    · rw [hζne x hx]
      exact ⟨fun h => absurd h hneg1, fun h => absurd h hx⟩
  have hζmul : ∀ a ∈ Z, ∀ b ∈ Z, ζ (a * b) = ζ a * ζ b := by
    intro a ha b hb
    by_cases h1 : a = 1
    · rw [h1, one_mul, hζ1, one_mul]
    by_cases h2 : b = 1
    · rw [h2, mul_one, hζ1, mul_one]
    have hab : b = a := (hZ2 a ha b hb h1 h2).symm
    rw [hab, hsq1 a ha, hζ1, hζne a h1]
    exact hneg.symm
  have hζinj : ∀ a ∈ Z, ∀ b ∈ Z, ζ a = ζ b → a = b := by
    intro a ha b hb hab
    by_cases h1 : a = 1
    · have hb1 : b = 1 := (hζiff b).mp (by rw [← hab, h1, hζ1])
      rw [h1, hb1]
    by_cases h2 : b = 1
    · exact absurd ((hζiff a).mp (by rw [hab, h2, hζ1])) h1
    exact hZ2 a ha b hb h1 h2
  have hconjZ : ∀ h ∈ Subgroup.normalizer (V : Set G), ∀ z ∈ Z, h * z * h⁻¹ = z := by
    intro h hh z hz'
    have hmap : ⁅V, V⁆ ≤ Z.comap (MulAut.conj h).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have e : h * ⁅a, b⁆ * h⁻¹ = ⁅h * a * h⁻¹, h * b * h⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [e, ← hc]
      exact Subgroup.commutator_mem_commutator
        ((Subgroup.mem_normalizer_iff.mp hh a).mp ha)
        ((Subgroup.mem_normalizer_iff.mp hh b).mp hb)
    have hz'' : z ∈ ⁅V, V⁆ := by rw [hc]; exact hz'
    have hc' : h * z * h⁻¹ ∈ Z := by
      have := hmap hz''
      simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using this
    by_cases h1 : z = 1
    · rw [h1]; simp
    · have hne : h * z * h⁻¹ ≠ 1 := by
        intro e
        apply h1
        have e' : h⁻¹ * (h * z * h⁻¹) * h = z := by group
        rw [← e', e]; group
      exact hZ2 _ hc' z hz' hne h1
  have hVN : ∀ x ∈ V, x ∈ Subgroup.normalizer (V : Set G) := fun x hx =>
    Subgroup.mem_normalizer_iff.mpr fun y =>
      ⟨fun hy => V.mul_mem (V.mul_mem hx hy) (V.inv_mem hx),
        fun hy => by
          have e : x⁻¹ * (x * y * x⁻¹) * x = y := by group
          rw [← e]
          exact V.mul_mem (V.mul_mem (V.inv_mem hx) hy) hx⟩
  have hcentZ : ∀ x ∈ V, ∀ z ∈ Z, x * z = z * x := fun x hx z hz' =>
    mul_inv_eq_iff_eq_mul.mp (hconjZ x (hVN x hx) z hz')
  have hcomm_mem : ∀ a ∈ V, ∀ b ∈ V, ⁅a, b⁆ ∈ Z := fun a ha b hb => by
    rw [← hc]; exact Subgroup.commutator_mem_commutator ha hb
  have comm_mul_left : ∀ a b c : G, ⁅a * b, c⁆ = a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆ :=
    fun a b c => by simp only [commutatorElement_def]; group
  have hbilL : ∀ v : G, (∀ y ∈ V, ⁅v, y⁆ ∈ Z) → ∀ x ∈ V, ∀ y ∈ V,
      ⁅v, x * y⁆ = ⁅v, x⁆ * ⁅v, y⁆ := by
    intro v hv x hx y hy
    have hc1 : x * ⁅v, y⁆ = ⁅v, y⁆ * x := hcentZ x hx _ (hv y hy)
    calc ⁅v, x * y⁆ = ⁅v, x⁆ * (x * ⁅v, y⁆ * x⁻¹) := by simp only [commutatorElement_def]; group
      _ = ⁅v, x⁆ * ⁅v, y⁆ := by rw [hc1]; group
  have hbil2 : ∀ a ∈ V, ∀ b ∈ V, ∀ x ∈ V, ⁅a * b, x⁆ = ⁅a, x⁆ * ⁅b, x⁆ := by
    intro a ha b hb x hx
    have hc1 : a * ⁅b, x⁆ = ⁅b, x⁆ * a := hcentZ a ha _ (hcomm_mem b hb x hx)
    rw [comm_mul_left, hc1]
    simp only [mul_inv_cancel_right]
    exact hZcomm _ (hcomm_mem b hb x hx) _ (hcomm_mem a ha x hx)
  have hf : ∀ v : V, ∃ f : V →* ℂˣ, ∀ x : V, f x = ζ ⁅(v : G), (x : G)⁆ := by
    intro v
    refine ⟨{ toFun := fun x => ζ ⁅(v : G), (x : G)⁆
              map_one' := by simp [hζ1]
              map_mul' := fun x y => ?_ }, fun x => rfl⟩
    show ζ ⁅(v : G), ((x * y : V) : G)⁆ = ζ ⁅(v : G), (x : G)⁆ * ζ ⁅(v : G), (y : G)⁆
    rw [Subgroup.coe_mul, hbilL (v : G) (fun y hy => hcomm_mem _ v.2 y hy) _ x.2 _ y.2]
    exact hζmul _ (hcomm_mem _ v.2 _ x.2) _ (hcomm_mem _ v.2 _ y.2)
  choose f hf using hf
  have hVtop : (⊤ : Subgroup V).map V.subtype = V := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
  have hmapc : (commutator V).map V.subtype = Z := by
    rw [← hc, commutator_def, Subgroup.map_commutator, hVtop]
  have hZmem : ∀ v : V, (v : G) ∈ Z → v ∈ commutator V := by
    intro v hv
    have hmem' : (v : G) ∈ (commutator V).map V.subtype := by rw [hmapc]; exact hv
    obtain ⟨y, hy, hyv⟩ := Subgroup.mem_map.mp hmem'
    obtain rfl : y = v := Subtype.ext hyv
    exact hy
  have hof : ∀ a : Abelianization V, ∃ v : V, Abelianization.of v = a := fun a =>
    QuotientGroup.mk_surjective a
  have hfin : Finite (Abelianization V) :=
    Finite.of_surjective (fun v : V => (Abelianization.of v : Abelianization V)) hof
  have hcardEq : Nat.card (Abelianization V →* ℂˣ) = Nat.card (Abelianization V) :=
    card_hom_units_eq _
  haveI : Finite (Abelianization V →* ℂˣ) :=
    Nat.finite_of_card_ne_zero (by rw [hcardEq]; exact (Nat.card_pos).ne')
  haveI : IsMulCommutative (Abelianization V →* ℂˣ) :=
    ⟨⟨fun φ ψ => MonoidHom.ext fun x => mul_comm (φ x) (ψ x)⟩⟩
  have hΦ1 : Abelianization.lift (f 1) = 1 := by
    apply Abelianization.hom_ext
    refine MonoidHom.ext fun x => ?_
    simp [hf, hζ1]
  have hΦmul : ∀ v w : V, Abelianization.lift (f (v * w)) =
      Abelianization.lift (f v) * Abelianization.lift (f w) := by
    intro v w
    apply Abelianization.hom_ext
    refine MonoidHom.ext fun x => ?_
    simp only [MonoidHom.comp_apply, Abelianization.lift_apply_of, MonoidHom.mul_apply, hf,
      Subgroup.coe_mul]
    rw [hbil2 _ v.2 _ w.2 _ x.2]
    exact hζmul _ (hcomm_mem _ v.2 _ x.2) _ (hcomm_mem _ w.2 _ x.2)
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Abelianization V →* (Abelianization V →* ℂˣ),
      ∀ v : V, Ψ (Abelianization.of v) = Abelianization.lift (f v) :=
    ⟨Abelianization.lift
      { toFun := fun v => Abelianization.lift (f v), map_one' := hΦ1, map_mul' := hΦmul },
      fun v => rfl⟩
  have hinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    obtain ⟨v, rfl⟩ := hof a
    rw [hΨ v] at ha
    have hvx : ∀ x : V, ζ ⁅(v : G), (x : G)⁆ = 1 := fun x => by
      have := congrArg (fun F : Abelianization V →* ℂˣ => F (Abelianization.of x)) ha
      simpa [hf] using this
    have hcen : (v : G) ∈ V ⊓ Subgroup.centralizer (V : Set G) := by
      refine ⟨v.2, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
      exact (commutatorElement_eq_one_iff_mul_comm.mp ((hζiff _).mp (hvx ⟨x, hx⟩))).symm
    apply MonoidHom.mem_ker.mp
    rw [Abelianization.ker_of]
    exact hZmem v (hz hcen)
  have hbij : Function.Bijective Ψ := hinj.bijective_of_nat_card_le hcardEq.le
  obtain ⟨lam, hlam⟩ : ∃ lam : V →* ℂˣ, ∀ x : V, lam x = ζ ⁅g, (x : G)⁆ := by
    refine ⟨{ toFun := fun x => ζ ⁅g, (x : G)⁆
              map_one' := by simp [hζ1]
              map_mul' := fun x y => ?_ }, fun x => rfl⟩
    show ζ ⁅g, ((x * y : V) : G)⁆ = ζ ⁅g, (x : G)⁆ * ζ ⁅g, (y : G)⁆
    rw [Subgroup.coe_mul, hbilL g hgZ _ x.2 _ y.2]
    exact hζmul _ (hgZ _ x.2) _ (hgZ _ y.2)
  obtain ⟨a, ha⟩ := hbij.2 (Abelianization.lift lam)
  obtain ⟨v, rfl⟩ := hof a
  have hvx : ∀ x : V, ζ ⁅(v : G), (x : G)⁆ = ζ ⁅g, (x : G)⁆ := fun x => by
    have := congrArg (fun F : Abelianization V →* ℂˣ => F (Abelianization.of x)) ha
    simpa [hΨ, hf, hlam] using this
  have hvg : ∀ x ∈ V, ⁅(v : G), x⁆ = ⁅g, x⁆ := fun x hx =>
    hζinj _ (hcomm_mem _ v.2 x hx) _ (hgZ x hx) (hvx ⟨x, hx⟩)
  refine ⟨(v : G), v.2, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hv' : (v : G)⁻¹ ∈ V := V.inv_mem v.2
  have e1 : ⁅g * (v : G)⁻¹, x⁆ = 1 := by
    rw [comm_mul_left, hconjZ g hg _ (hcomm_mem _ hv' x hx), ← hvg x hx,
      ← hbil2 _ hv' _ v.2 x hx, inv_mul_cancel, commutatorElement_one_left]
  exact (commutatorElement_eq_one_iff_mul_comm.mp e1).symm

end CFSG.GH74.QTGen4.DSGen4
