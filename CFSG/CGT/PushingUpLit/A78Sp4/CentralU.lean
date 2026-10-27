module

public import CFSG.CGT.PushingUpLit.A78Sp4.Loc

public section

namespace CFSG.CGT.PushingUpLit.A78Sp4

open CFSG.ABGLocalTools

variable {G : Type} [Group G] {L L₂ V V₂ Z Z₂ J T S M M₂ : Subgroup G} {e : ℕ}

theorem Sp4Cross.conj_Z_mem (hc : Sp4Cross G L L₂ V V₂ Z Z₂ J T S e)
    {s : G} (hs : s ∈ S) {x : G} (hx : x ∈ Z) : s * x * s⁻¹ ∈ Z ∨ s * x * s⁻¹ ∈ Z₂ := by
  by_cases hsT : s ∈ T
  · exact Or.inl ((hc.T_normZ s hsT).1 ▸ mul_mem_cj' s hx)
  · exact Or.inr ((hc.swap_Z s hs hsT).1 ▸ mul_mem_cj' s hx)

theorem Sp4Cross.conj_Z₂_mem (hc : Sp4Cross G L L₂ V V₂ Z Z₂ J T S e)
    {s : G} (hs : s ∈ S) {x : G} (hx : x ∈ Z₂) : s * x * s⁻¹ ∈ Z ∨ s * x * s⁻¹ ∈ Z₂ := by
  by_cases hsT : s ∈ T
  · exact Or.inr ((hc.T_normZ s hsT).2 ▸ mul_mem_cj' s hx)
  · exact Or.inl ((hc.swap_Z s hs hsT).2 ▸ mul_mem_cj' s hx)

theorem Sp4Loc.uType_conj [Finite G] (h : Sp4Loc G L L₂ V V₂ Z Z₂ J T S M M₂ e) {s : G} (hs : s ∈ S)
    {u : G} (hu : UType V V₂ Z Z₂ u) : UType V V₂ Z Z₂ (s * u * s⁻¹) := by
  obtain ⟨huVV, huZ, huZ₂⟩ := hu
  have hs' : s⁻¹ ∈ S := S.inv_mem hs
  have hback : s⁻¹ * (s * u * s⁻¹) * s⁻¹⁻¹ = u := by group
  refine ⟨?_, fun hZ => ?_, fun hZ => ?_⟩
  · by_cases hsT : s ∈ T
    · obtain ⟨h1, h2⟩ := h.base.T_norm s hsT
      exact ⟨h1 ▸ mul_mem_cj' s huVV.1, h2 ▸ mul_mem_cj' s huVV.2⟩
    · obtain ⟨h1, h2⟩ := h.base.swap s hs hsT
      exact ⟨h2 ▸ mul_mem_cj' s huVV.2, h1 ▸ mul_mem_cj' s huVV.1⟩
  · rcases h.cross.conj_Z_mem hs' hZ with h1 | h1
    · rw [hback] at h1; exact huZ h1
    · rw [hback] at h1; exact huZ₂ h1
  · rcases h.cross.conj_Z₂_mem hs' hZ with h1 | h1
    · rw [hback] at h1; exact huZ h1
    · rw [hback] at h1; exact huZ₂ h1

theorem Sp4Loc.uType_iff [Finite G] (h : Sp4Loc G L L₂ V V₂ Z Z₂ J T S M M₂ e)
    (c : Cls2Coord (GaloisField 2 e) J) (hV : ∀ x ∈ J, (x ∈ V ↔ (c.π x).2 = 0))
    (hV₂ : ∀ x ∈ J, (x ∈ V₂ ↔ (c.π x).1 = 0))
    (hZ : ∀ x ∈ J, (x ∈ Z ↔ c.π x = 0 ∧ (c.ζ x).1 = 0))
    (hZ₂ : ∀ x ∈ J, (x ∈ Z₂ ↔ c.π x = 0 ∧ (c.ζ x).2 = 0)) {x : G} :
    UType V V₂ Z Z₂ x ↔ x ∈ J ∧ c.π x = 0 ∧ (c.ζ x).1 ≠ 0 ∧ (c.ζ x).2 ≠ 0 := by
  constructor
  · rintro ⟨⟨hxV, hxV₂⟩, hxZ, hxZ₂⟩
    have hxJ : x ∈ J := h.base.sup ▸ (le_sup_left : V ≤ V ⊔ V₂) hxV
    have h1 := (hV x hxJ).1 hxV
    have h2 := (hV₂ x hxJ).1 hxV₂
    have hπ : c.π x = 0 := Prod.ext h2 h1
    refine ⟨hxJ, hπ, fun h0 => hxZ ((hZ x hxJ).2 ⟨hπ, h0⟩), fun h0 => hxZ₂ ((hZ₂ x hxJ).2 ⟨hπ, h0⟩)⟩
  · rintro ⟨hxJ, hπ, h1, h2⟩
    have hπ1 : (c.π x).1 = 0 := by rw [hπ]; rfl
    have hπ2 : (c.π x).2 = 0 := by rw [hπ]; rfl
    exact ⟨⟨(hV x hxJ).2 hπ2, (hV₂ x hxJ).2 hπ1⟩, fun hx => h1 ((hZ x hxJ).1 hx).2,
      fun hx => h2 ((hZ₂ x hxJ).1 hx).2⟩

theorem Sp4Loc.card_uType [Finite G] (h : Sp4Loc G L L₂ V V₂ Z Z₂ J T S M M₂ e) :
    Nat.card {x : G // UType V V₂ Z Z₂ x} = (2 ^ e - 1) * (2 ^ e - 1) := by
  obtain ⟨c, hV, hV₂, hZ, hZ₂⟩ := exists_cls2 h.coords
  let f : {x : G // UType V V₂ Z Z₂ x} →
      {p : GaloisField 2 e × GaloisField 2 e // p.1 ≠ 0 ∧ p.2 ≠ 0} :=
    fun x => ⟨c.ζ x.1, ((h.uType_iff c hV hV₂ hZ hZ₂).1 x.2).2.2⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro x y hxy
      have hx := (h.uType_iff c hV hV₂ hZ hZ₂).1 x.2
      have hy := (h.uType_iff c hV hV₂ hZ hZ₂).1 y.2
      exact Subtype.ext (c.ζ_inj x.1 hx.1 hx.2.1 y.1 hy.1 hy.2.1 (congrArg Subtype.val hxy))
    · rintro ⟨p, hp1, hp2⟩
      obtain ⟨x, hxJ, hπ, hζ⟩ := c.ζ_surj p
      refine ⟨⟨x, (h.uType_iff c hV hV₂ hZ hZ₂).2 ⟨hxJ, hπ, by rw [hζ]; exact hp1,
        by rw [hζ]; exact hp2⟩⟩, Subtype.ext hζ⟩
  rw [Nat.card_congr (Equiv.ofBijective f hbij),
    Nat.card_congr (Equiv.subtypeProdEquivProd (p := fun a : GaloisField 2 e => a ≠ 0)
      (q := fun b : GaloisField 2 e => b ≠ 0)), Nat.card_prod]
  have hF : Nat.card (GaloisField 2 e) = 2 ^ e := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact GaloisField.card 2 e (by have := h.base.two_le; omega)
  have hu : Nat.card {a : GaloisField 2 e // a ≠ 0} = 2 ^ e - 1 := by
    rw [← Nat.card_congr (unitsEquivNeZero : (GaloisField 2 e)ˣ ≃ {a : GaloisField 2 e // a ≠ 0}),
      Nat.card_units, hF]
  rw [hu]

theorem Sp4Base.isPGroup_S [Finite G] (h : Sp4Base G V V₂ J T S M M₂ e) : IsPGroup 2 S := by
  obtain ⟨Q, hQ⟩ := h.sylow
  have : IsPGroup 2 ((Q : Subgroup (⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype) :=
    Q.isPGroup'.map _
  rwa [hQ] at this

theorem exists_central_uType [Finite G] (h : Sp4Loc G L L₂ V V₂ Z Z₂ J T S M M₂ e) :
    ∃ u : G, UType V V₂ Z Z₂ u ∧ ∀ s ∈ S, s * u = u * s := by
  have hS2 : IsPGroup 2 S := h.base.isPGroup_S
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let sm : SMul S {x : G // UType V V₂ Z Z₂ x} :=
    ⟨fun s x => ⟨s.1 * x.1 * s.1⁻¹, h.uType_conj s.2 x.2⟩⟩
  let act : MulAction S {x : G // UType V V₂ Z Z₂ x} :=
    { sm with
      one_smul := fun x => Subtype.ext (by
        show (1 : S).1 * x.1 * (1 : S).1⁻¹ = x.1
        simp)
      mul_smul := fun s s' x => Subtype.ext (by
        show (s * s').1 * x.1 * (s * s').1⁻¹ = s.1 * (s'.1 * x.1 * s'.1⁻¹) * s.1⁻¹
        simp [mul_assoc]) }
  have hfin : Finite {x : G // UType V V₂ Z Z₂ x} := inferInstance
  have hmod := @IsPGroup.card_modEq_card_fixedPoints _ _ _ hS2 _ {x : G // UType V V₂ Z Z₂ x} act
    hfin
  have hodd : Nat.card {x : G // UType V V₂ Z Z₂ x} % 2 = 1 := by
    rw [h.card_uType]
    have h2 : 2 ∣ 2 ^ e := dvd_pow_self 2 (by have := h.base.two_le; omega)
    have h1 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    have : (2 ^ e - 1) % 2 = 1 := by omega
    rw [Nat.mul_mod, this]
  have hne : Nonempty (@MulAction.fixedPoints S {x : G // UType V V₂ Z Z₂ x} _ act) := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    have h0 : Nat.card (@MulAction.fixedPoints S {x : G // UType V V₂ Z Z₂ x} _ act) = 0 :=
      Nat.card_of_isEmpty
    rw [h0] at hmod
    have := hmod
    unfold Nat.ModEq at this
    omega
  obtain ⟨⟨u, hu⟩, hfix⟩ := hne
  refine ⟨u, hu, fun s hs => ?_⟩
  have := hfix ⟨s, hs⟩
  have h1 : s * u * s⁻¹ = u := congrArg Subtype.val this
  calc s * u = s * u * s⁻¹ * s := by group
    _ = u * s := by rw [h1]

end CFSG.CGT.PushingUpLit.A78Sp4
