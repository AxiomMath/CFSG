module

public import CFSG.LocalAnalysis.SectionRank.OddCover.PrimeThree
public import CFSG.RankThree.SubgroupLists.SL3Involutions

public section

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG.Assembly.LowTwoRank CFSG.SectionRank CFSG.SectionRank.OddCover

section Cover

variable {p : ℕ} {ε : ℤ} {K : Type} [Field K] [Finite K] {H : Subgroup (GL (Fin 3) K)}
  {L : Type} [Group L] [Finite L]

theorem exists_cover_hom (hp : p.Prime) (hp2 : p ≠ 2)
    (hH : (ε = 1 ∧ Nat.card K = p ∧ H = StatedSL 3 K) ∨
      (ε = -1 ∧ Nat.card K = p ^ 2 ∧ H = StatedSU 3 p K))
    (hLperf : Group.IsPerfect L) (hodd : Odd (Nat.card (Subgroup.center L)))
    (θ : L ⧸ Subgroup.center L ≃* StatedProj H) :
    ∃ φ : H →* L, Function.Surjective φ ∧
      (∀ h : H, QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf H) h =
        θ (QuotientGroup.mk' (Subgroup.center L) (φ h))) ∧
      φ.ker ≤ (StatedScalars (Fin 3) K).subgroupOf H := by
  have : Fact p.Prime := ⟨hp⟩
  set D := (StatedScalars (Fin 3) K).subgroupOf H with hDdef
  set Z := Subgroup.center L with hZdef
  set F : Subgroup (H × L) := MonoidHom.eqLocus ((QuotientGroup.mk' D).comp (MonoidHom.fst H L))
    (θ.toMonoidHom.comp ((QuotientGroup.mk' Z).comp (MonoidHom.snd H L))) with hFdef
  have hmemF : ∀ x : H × L,
      x ∈ F ↔ QuotientGroup.mk' D x.1 = θ (QuotientGroup.mk' Z x.2) := fun x => Iff.rfl
  set π₁ : F →* H := (MonoidHom.fst H L).comp F.subtype with hπ₁def
  have hπ₁ : Function.Surjective π₁ := by
    intro h
    obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective Z (θ.symm (QuotientGroup.mk' D h))
    refine ⟨⟨(h, l), ?_⟩, rfl⟩
    rw [hmemF, hl, MulEquiv.apply_symm_apply]
  have hkerZ : ∀ x : F, x ∈ π₁.ker → (x : H × L).2 ∈ Z := by
    intro x hx
    have h1 := (hmemF x).1 x.2
    have hx1 : (x : H × L).1 = 1 := hx
    rw [hx1, map_one] at h1
    have h2 : QuotientGroup.mk' Z (x : H × L).2 = 1 := θ.injective (by rw [← h1, map_one])
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  have hC₁ : π₁.ker ≤ Subgroup.center F := by
    intro x hx
    have hx1 : (x : H × L).1 = 1 := hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    apply Prod.ext
    · change (y : H × L).1 * (x : H × L).1 = (x : H × L).1 * (y : H × L).1
      rw [hx1, mul_one, one_mul]
    · exact Subgroup.mem_center_iff.1 (hkerZ x hx) (y : H × L).2
  have hodd₁ : Odd (Nat.card π₁.ker) := by
    have hZmem : ∀ z ∈ Z, ((1 : H), z) ∈ F := fun z hz => by
      rw [hmemF, map_one]
      have : QuotientGroup.mk' Z z = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hz
      rw [this, map_one]
    have hcard : Nat.card π₁.ker = Nat.card Z := Nat.card_congr
      { toFun := fun x => ⟨((x : F) : H × L).2, hkerZ x x.2⟩
        invFun := fun z => ⟨⟨(1, z), hZmem z z.2⟩, rfl⟩
        left_inv := fun x => by
          apply Subtype.ext
          apply Subtype.ext
          apply Prod.ext
          · exact (x.2 : ((x : F) : H × L).1 = 1).symm
          · rfl
        right_inv := fun z => rfl }
    rw [hcard]
    exact hodd
  obtain ⟨⟨s, hs, -⟩, -⟩ :=
    prime_classical_three_central_odd_extension_splitting hp hp2 hH π₁ hπ₁ hC₁ hodd₁
  set φ : H →* L := (MonoidHom.snd H L).comp (F.subtype.comp s) with hφdef
  have hsfst : ∀ h : H, ((s h : F) : H × L).1 = h := fun h => DFunLike.congr_fun hs h
  have hφ : ∀ h : H, QuotientGroup.mk' D h = θ (QuotientGroup.mk' Z (φ h)) := by
    intro h
    have h1 := (hmemF _).1 (s h).2
    rw [hsfst] at h1
    exact h1
  have hHperf : Group.IsPerfect H := isPerfect_prime_three hp hp2 hH
  have hφsurj : Function.Surjective φ := by
    have hsup : φ.range ⊔ Z = ⊤ := by
      rw [eq_top_iff]
      intro l _
      obtain ⟨h, hh⟩ := QuotientGroup.mk'_surjective D (θ (QuotientGroup.mk' Z l))
      have h2 : QuotientGroup.mk' Z (φ h) = QuotientGroup.mk' Z l :=
        θ.injective (by rw [← hφ, hh])
      have hz : (φ h)⁻¹ * l ∈ Z := QuotientGroup.eq.1 h2
      rw [show l = φ h * ((φ h)⁻¹ * l) by group]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨h, rfl⟩) (Subgroup.mem_sup_right hz)
    exact MonoidHom.range_eq_top.1 ((perfect_central_supplement hLperf).1 φ.range hsup)
  refine ⟨φ, hφsurj, hφ, ?_⟩
  intro h hh
  have h1 := hφ h
  rw [(MonoidHom.mem_ker).1 hh, map_one, map_one, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at h1
  exact h1

end Cover


section Lifts

variable {H L : Type*} [Group H] [Group L]

theorem eq_one_of_sq_of_pow {x : H} {k : ℕ} (hx : x * x = 1) (hk : x ^ k = 1) (hodd : Odd k) :
    x = 1 := by
  obtain ⟨m, rfl⟩ := hodd
  have h2 : x ^ 2 = 1 := by rw [pow_two]; exact hx
  calc x = x ^ (2 * m + 1) := by
        rw [pow_succ, pow_mul, h2, one_pow, one_mul]
    _ = 1 := hk

theorem exists_involution_lift [Finite H] (φ : H →* L) (hodd : Odd (Nat.card φ.ker)) {t : L}
    (ht : t * t = 1) (hr : t ∈ φ.range) : ∃ g : H, g * g = 1 ∧ φ g = t := by
  obtain ⟨g₀, rfl⟩ := hr
  have hg2 : g₀ * g₀ ∈ φ.ker := by rw [MonoidHom.mem_ker, map_mul]; exact ht
  refine ⟨g₀ ^ Nat.card φ.ker, ?_, ?_⟩
  · have h1 : (⟨g₀ * g₀, hg2⟩ : φ.ker) ^ Nat.card φ.ker = 1 := pow_card_eq_one'
    have h2 : (g₀ * g₀) ^ Nat.card φ.ker = 1 := congrArg Subtype.val h1
    calc g₀ ^ Nat.card φ.ker * g₀ ^ Nat.card φ.ker
        = g₀ ^ (Nat.card φ.ker + Nat.card φ.ker) := (pow_add g₀ _ _).symm
      _ = g₀ ^ (2 * Nat.card φ.ker) := by rw [two_mul]
      _ = (g₀ ^ 2) ^ Nat.card φ.ker := pow_mul g₀ 2 _
      _ = (g₀ * g₀) ^ Nat.card φ.ker := by rw [pow_two]
      _ = 1 := h2
  · rw [map_pow]
    obtain ⟨m, hm⟩ := hodd
    rw [hm, pow_succ, pow_mul, show φ g₀ ^ 2 = 1 by rw [pow_two]; exact ht, one_pow, one_mul]

theorem involution_lift_comm [Finite H] (φ : H →* L) (hker : ∀ g ∈ φ.ker, ∀ h : H, g * h = h * g)
    (hodd : Odd (Nat.card φ.ker)) {a b : H} (hb : b * b = 1)
    (hab : φ a * φ b = φ b * φ a) : a * b = b * a := by
  set c : H := a * b * (b * a)⁻¹ with hc
  have hcker : c ∈ φ.ker := by
    rw [MonoidHom.mem_ker, hc, map_mul, map_mul, map_inv, map_mul, hab, mul_inv_cancel]
  have hcc : ∀ h : H, c * h = h * c := hker c hcker
  have h1 : a * b = c * (b * a) := by rw [hc]; group
  have h2 : b * a * b = c * a := by
    calc b * a * b = b * (a * b) := by group
      _ = b * (c * (b * a)) := by rw [h1]
      _ = (b * c) * (b * a) := by group
      _ = (c * b) * (b * a) := by rw [← hcc b]
      _ = c * ((b * b) * a) := by group
      _ = c * a := by rw [hb, one_mul]
  have h3 : c * c = 1 := by
    have : a = c * c * a := by
      calc a = b * (b * a * b) * b := by
            calc a = (b * b) * a * (b * b) := by rw [hb]; group
              _ = b * (b * a * b) * b := by group
        _ = b * (c * a) * b := by rw [h2]
        _ = c * (b * a * b) := by
            calc b * (c * a) * b = (b * c) * (a * b) := by group
              _ = (c * b) * (a * b) := by rw [← hcc b]
              _ = c * (b * a * b) := by group
        _ = c * (c * a) := by rw [h2]
        _ = c * c * a := by group
    have h4 : c * c = 1 := by
      have := congrArg (fun x => x * a⁻¹) this
      simpa using this.symm
    exact h4
  have hc1 : c = 1 := by
    have hpow : (⟨c, hcker⟩ : φ.ker) ^ Nat.card φ.ker = 1 := pow_card_eq_one'
    have := eq_one_of_sq_of_pow (x := (⟨c, hcker⟩ : φ.ker)) (Subtype.ext h3) hpow hodd
    exact congrArg Subtype.val this
  rw [h1, hc1, one_mul]

theorem card_le_of_lifts [Finite H] (φ : H →* L) (hker : ∀ g ∈ φ.ker, ∀ h : H, g * h = h * g)
    (hodd : Odd (Nat.card φ.ker)) (m : ℕ)
    (hm : ∀ T : Subgroup H, (∀ x ∈ T, x * x = 1) → Nat.card T ≤ m) (E : Subgroup L)
    (hEφ : E ≤ φ.range) (hE2 : ∀ x ∈ E, x * x = 1) (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) :
    Nat.card E ≤ m := by
  classical
  choose ℓ hℓ using fun x : E =>
    exists_involution_lift φ hodd (hE2 x x.2) (hEφ x.2)
  have hcomm : ∀ x y : E, ℓ x * ℓ y = ℓ y * ℓ x := fun x y =>
    involution_lift_comm φ hker hodd (hℓ y).1 (by
      rw [(hℓ x).2, (hℓ y).2]; exact hEc x x.2 y y.2)
  set T : Subgroup H := Subgroup.closure (Set.range ℓ) with hT
  have hcommS : ∀ x ∈ Set.range ℓ, ∀ y ∈ Set.range ℓ, x * y = y * x := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact hcomm x y
  have hcommS' : (Set.range ℓ).Pairwise Commute := fun x hx y hy _ => hcommS x hx y hy
  have := Subgroup.isMulCommutative_closure hcommS'
  have hTcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : T) ⟨y, hy⟩)
  have hT2 : ∀ z ∈ T, z * z = 1 := by
    intro z hz
    induction hz using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨y, rfl⟩ := hx
      exact (hℓ y).1
    | one => simp
    | mul x y hx hy ihx ihy =>
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [hTcomm y hy x hx]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [ihx, ihy, one_mul]
    | inv x hx ih =>
      rw [← mul_inv_rev, ih, inv_one]
  have hle : Nat.card E ≤ Nat.card T := by
    refine Nat.card_le_card_of_injective
      (fun x : E => (⟨ℓ x, Subgroup.subset_closure ⟨x, rfl⟩⟩ : T)) ?_
    intro x y hxy
    have h1 : ℓ x = ℓ y := congrArg Subtype.val hxy
    apply Subtype.ext
    rw [← (hℓ x).2, ← (hℓ y).2, h1]
  exact hle.trans (hm T hT2)

end Lifts

section Exp2

theorem card_le_four_of_det_one {K : Type} [Field K] (h2 : (2 : K) ≠ 0)
    {H : Subgroup (GL (Fin 3) K)} (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K).det = 1)
    (T : Subgroup ↥H) (hT : ∀ x ∈ T, x * x = 1) : Nat.card T ≤ 4 := by
  have h := CFSG.RankThree.SubgroupLists.card_le_four_of_sq_eq_one_sl3 h2 (T.map H.subtype)
    (by
      rintro _ ⟨x, hx, rfl⟩
      have := hT x hx
      exact congrArg Subtype.val this)
    (by
      rintro _ ⟨x, hx, rfl⟩
      exact hdet x x.2)
  rwa [Subgroup.card_map_of_injective H.subtype_injective] at h

end Exp2

end CFSG.QuasithinUnique.Setup.Family
