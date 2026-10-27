module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.XFiveLemma

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
open Subgroup

section Odd

variable {G : Type*} [Group G]

theorem exists_conj_of_mul_mem_odd [Finite G] (O : Subgroup G) [O.Normal]
    (hO : Odd (Nat.card O)) {a b : G} (ha : a * a = 1) (hb : b * b = 1) (h : a⁻¹ * b ∈ O) :
    ∃ o ∈ O, o * a * o⁻¹ = b := by
  obtain ⟨j, hj⟩ := hO
  set m : G := a⁻¹ * b with hm
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbm : b = a * m := by rw [hm, ha', ← mul_assoc, ha, one_mul]
  have hmo : m ^ Nat.card O = 1 := orderOf_dvd_iff_pow_eq_one.1 (O.orderOf_dvd_natCard h)
  have ham : a * m * a = m⁻¹ := by
    have h1 : a * m * a * m = 1 := by
      have : (a * m) * (a * m) = 1 := hbm ▸ hb
      simpa [mul_assoc] using this
    exact eq_inv_of_mul_eq_one_left h1
  have hak : ∀ k : ℕ, a * m ^ k * a = (m ^ k)⁻¹ := by
    intro k
    have := map_pow (MulAut.conj a) m k
    simp only [MulAut.conj_apply, ha'] at this
    rw [← inv_pow, ← ham, ← this]
  refine ⟨(m ^ (j + 1))⁻¹, O.inv_mem (O.pow_mem h _), ?_⟩
  have h2 : (m ^ (j + 1))⁻¹ * (m ^ (j + 1))⁻¹ = m⁻¹ := by
    rw [← mul_inv_rev, ← pow_add]
    have : j + 1 + (j + 1) = Nat.card O + 1 := by omega
    rw [this, pow_succ, hmo, one_mul]
  have h3 : a * m ^ (j + 1) = (m ^ (j + 1))⁻¹ * a := by
    calc a * m ^ (j + 1) = a * m ^ (j + 1) * a * a := by rw [mul_assoc _ a a, ha, mul_one]
      _ = _ := by rw [hak]
  calc (m ^ (j + 1))⁻¹ * a * (m ^ (j + 1))⁻¹⁻¹
      = (m ^ (j + 1))⁻¹ * (a * m ^ (j + 1)) := by rw [inv_inv, mul_assoc]
    _ = (m ^ (j + 1))⁻¹ * ((m ^ (j + 1))⁻¹ * a) := by rw [h3]
    _ = m⁻¹ * a := by rw [← mul_assoc, h2]
    _ = a * m * a * a := by rw [ham]
    _ = a * m := by rw [mul_assoc _ a a, ha, mul_one]
    _ = b := hbm.symm

theorem map_centralizer_eq_of_odd [Finite G] (O : Subgroup G) [O.Normal]
    (hO : Odd (Nat.card O)) {t : G} (ht : t * t = 1) :
    (centralizer ({t} : Set G)).map (QuotientGroup.mk' O) =
      centralizer ({(QuotientGroup.mk' O t)} : Set (G ⧸ O)) := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_iff] at hg
    rw [mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have := hg t rfl
    simp only [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul]
    exact congrArg _ this
  · intro x hx
    obtain ⟨g, rfl⟩ := (QuotientGroup.mk'_surjective O) x
    rw [mem_centralizer_iff] at hx
    have hx' : (t : G ⧸ O) * (g : G ⧸ O) = (g : G ⧸ O) * (t : G ⧸ O) := hx _ rfl
    have hinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    have hmem : t⁻¹ * (g⁻¹ * t * g) ∈ O := by
      rw [← QuotientGroup.eq_one_iff]
      have hc : (g : G ⧸ O)⁻¹ * (t : G ⧸ O) * (g : G ⧸ O) = (t : G ⧸ O) := by
        calc (g : G ⧸ O)⁻¹ * (t : G ⧸ O) * (g : G ⧸ O)
            = (g : G ⧸ O)⁻¹ * ((t : G ⧸ O) * (g : G ⧸ O)) := mul_assoc _ _ _
          _ = (g : G ⧸ O)⁻¹ * ((g : G ⧸ O) * (t : G ⧸ O)) := by rw [hx']
          _ = (t : G ⧸ O) := inv_mul_cancel_left _ _
      have htq : (t : G ⧸ O) * (t : G ⧸ O) = 1 := by
        rw [← QuotientGroup.mk_mul, ht, QuotientGroup.mk_one]
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv, hc]
      rw [inv_eq_of_mul_eq_one_right htq]
      exact htq
    have hb : g⁻¹ * t * g * (g⁻¹ * t * g) = 1 := by
      calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
        _ = 1 := by rw [ht]; group
    rw [hinv] at hmem
    obtain ⟨o, ho, hoc⟩ := exists_conj_of_mul_mem_odd O hO (a := t) (b := g⁻¹ * t * g) ht hb
      (by simpa [hinv] using hmem)
    refine ⟨g * o, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      have h5 : y * g = g * (o * y * o⁻¹) := by rw [hoc]; group
      calc y * (g * o) = (y * g) * o := by rw [mul_assoc]
        _ = g * (o * y * o⁻¹) * o := by rw [h5]
        _ = g * o * y := by group
    · simp [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff o).2 ho]

end Odd

section Fixed

theorem exists_fixed_of_card_prime {G : Type*} [Group G] {X : Type*} [MulAction G X] [Finite X]
    (p : ℕ) [Fact p.Prime] (hG : Nat.card G = p) (h : ¬ p ∣ Nat.card X) :
    ∃ x : X, ∀ g : G, g • x = x := by
  have hp : IsPGroup p G := IsPGroup.of_card (n := 1) (by simpa using hG)
  have hmod := hp.card_modEq_card_fixedPoints X
  by_contra hne
  push Not at hne
  have hempty : MulAction.fixedPoints G X = ∅ := by
    ext x
    simp only [MulAction.mem_fixedPoints, Set.mem_empty_iff_false, iff_false]
    intro hx
    obtain ⟨g, hg⟩ := hne x
    exact hg (hx g)
  rw [hempty] at hmod
  have h0 : Nat.card (∅ : Set X) = 0 := by simp
  rw [h0] at hmod
  exact h ((Nat.modEq_zero_iff_dvd).1 hmod)

end Fixed

section Inversion

variable {G : Type*} [Group G] [Finite G]

theorem inv_of_centralizer_eq_bot {O : Subgroup G} {t : G} (ht : t * t = 1)
    (hn : ∀ o ∈ O, t * o * t⁻¹ ∈ O) (hfix : ∀ o ∈ O, t * o = o * t → o = 1) :
    (∀ o ∈ O, t * o * t⁻¹ = o⁻¹) ∧ ∀ a ∈ O, ∀ b ∈ O, a * b = b * a := by
  have hinv : ∀ o ∈ O, MulAut.conj t o = o⁻¹ :=
    aut_inv_of_fixed_point_free (MulAut.conj t) O hn (conj_mul_self_eq_one ht) (fun o ho h =>
      hfix o ho (by
        rw [MulAut.conj_apply] at h
        calc t * o = t * o * t⁻¹ * t := by group
          _ = o * t := by rw [h]))
  exact ⟨fun o ho => by simpa [MulAut.conj_apply] using hinv o ho, commute_of_aut_inv hinv⟩

end Inversion

section CompleteAut

variable {S : Type*} [Group S]

theorem eq_one_of_forall_commute [IsSimpleGroup S] (hS : ∃ a b : S, a * b ≠ b * a) {z : S}
    (hz : ∀ s : S, z * s = s * z) : z = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · have : z ∈ Subgroup.center S := Subgroup.mem_center_iff.2 fun g => (hz g).symm
    rw [h] at this
    simpa using this
  · obtain ⟨a, b, hab⟩ := hS
    have ha : a ∈ Subgroup.center S := h ▸ Subgroup.mem_top a
    exact absurd (Subgroup.mem_center_iff.1 ha b).symm hab

theorem conj_injective_of_simple [IsSimpleGroup S] (hS : ∃ a b : S, a * b ≠ b * a) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  intro a b h
  have h' : ∀ x : S, a * x * a⁻¹ = b * x * b⁻¹ := fun x => by
    simpa [MulAut.conj_apply] using congrArg (fun f : MulAut S => f x) h
  have : b⁻¹ * a = 1 := eq_one_of_forall_commute hS fun s => by
    calc b⁻¹ * a * s = b⁻¹ * (a * s * a⁻¹) * a := by group
      _ = b⁻¹ * (b * s * b⁻¹) * a := by rw [h']
      _ = s * (b⁻¹ * a) := by group
  exact (inv_mul_eq_one.1 this).symm

theorem mul_conj_mul_inv (x : MulAut S) (s : S) :
    x * MulAut.conj s * x⁻¹ = MulAut.conj (x s) := by
  ext y
  simp [MulAut.conj_apply]

theorem eq_one_of_commute_conj [IsSimpleGroup S] (hS : ∃ a b : S, a * b ≠ b * a) (f : MulAut S)
    (h : ∀ s : S, f * MulAut.conj s = MulAut.conj s * f) : f = 1 := by
  ext s
  have h1 : MulAut.conj (f s) = MulAut.conj s := by
    rw [← mul_conj_mul_inv, h s]; group
  have := conj_injective_of_simple hS h1
  simpa using this

def innAut (S : Type*) [Group S] : Subgroup (MulAut S) := (MulAut.conj : S →* MulAut S).range

instance innAut_normal : (innAut S).Normal where
  conj_mem := by
    rintro _ ⟨s, rfl⟩ x
    exact ⟨x s, (mul_conj_mul_inv x s).symm⟩

theorem innAut_le_map [IsSimpleGroup S] (hS : ∃ a b : S, a * b ≠ b * a) (φ : MulAut (MulAut S)) :
    innAut S ≤ (innAut S).map (φ : MulAut S →* MulAut S) := by
  set N := (innAut S).map (φ : MulAut S →* MulAut S) with hN
  have : N.Normal := Subgroup.Normal.map inferInstance _ φ.surjective
  have : (N ⊓ innAut S).Normal := inferInstance
  have : ((N ⊓ innAut S).comap (MulAut.conj : S →* MulAut S)).Normal := inferInstance
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((N ⊓ innAut S).comap (MulAut.conj : S →* MulAut S)) with h | h
  · exfalso
    have hcomm : ∀ s : S, φ (MulAut.conj s) = 1 := by
      intro s
      have hn : φ (MulAut.conj s) ∈ N := ⟨_, ⟨s, rfl⟩, rfl⟩
      apply eq_one_of_commute_conj hS
      intro t
      have hi : (MulAut.conj t : MulAut S) ∈ innAut S := ⟨t, rfl⟩
      have hc : φ (MulAut.conj s) * MulAut.conj t * (φ (MulAut.conj s))⁻¹ *
          (MulAut.conj t)⁻¹ ∈ N ⊓ innAut S := by
        refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
        · have h1 : MulAut.conj t * (φ (MulAut.conj s))⁻¹ * (MulAut.conj t)⁻¹ ∈ N :=
            Normal.conj_mem inferInstance _ (N.inv_mem hn) _
          have := N.mul_mem hn h1
          have e : φ (MulAut.conj s) * MulAut.conj t * (φ (MulAut.conj s))⁻¹ *
              (MulAut.conj t)⁻¹ = φ (MulAut.conj s) * (MulAut.conj t *
              (φ (MulAut.conj s))⁻¹ * (MulAut.conj t)⁻¹) := by group
          rw [e]
          exact this
        · have h1 : φ (MulAut.conj s) * MulAut.conj t * (φ (MulAut.conj s))⁻¹ ∈ innAut S :=
            Normal.conj_mem inferInstance _ hi _
          exact (innAut S).mul_mem h1 ((innAut S).inv_mem hi)
      have hone : φ (MulAut.conj s) * MulAut.conj t * (φ (MulAut.conj s))⁻¹ *
          (MulAut.conj t)⁻¹ = 1 := by
        obtain ⟨r, hr⟩ := hc.2
        have hr' : r ∈ (N ⊓ innAut S).comap (MulAut.conj : S →* MulAut S) := by
          show (MulAut.conj r : MulAut S) ∈ N ⊓ innAut S
          rw [hr]; exact hc
        rw [h] at hr'
        have hr1 : r = 1 := by simpa using hr'
        rw [← hr, hr1]
        simp
      have : φ (MulAut.conj s) * MulAut.conj t * (φ (MulAut.conj s))⁻¹ *
          (MulAut.conj t)⁻¹ = 1 := hone
      calc φ (MulAut.conj s) * MulAut.conj t
          = (φ (MulAut.conj s) * MulAut.conj t * (φ (MulAut.conj s))⁻¹ *
              (MulAut.conj t)⁻¹) * (MulAut.conj t * φ (MulAut.conj s)) := by group
        _ = MulAut.conj t * φ (MulAut.conj s) := by rw [this, one_mul]
    obtain ⟨a, b, hab⟩ := hS
    have h1 : (MulAut.conj a : MulAut S) = 1 := φ.injective (by simpa using hcomm a)
    apply hab
    have := congrArg (fun f : MulAut S => f b) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc a * b = a * b * a⁻¹ * a := by group
      _ = b * a := by rw [this]
  · rintro _ ⟨s, rfl⟩
    have : s ∈ (N ⊓ innAut S).comap (MulAut.conj : S →* MulAut S) := h ▸ Subgroup.mem_top s
    exact this.1

theorem innAut_map_le [IsSimpleGroup S] (hS : ∃ a b : S, a * b ≠ b * a) (φ : MulAut (MulAut S))
    {x : MulAut S} (hx : x ∈ innAut S) : φ x ∈ innAut S := by
  obtain ⟨y, hy, hyx⟩ := innAut_le_map hS φ⁻¹ hx
  have : φ x = y := by
    rw [← hyx]; simp
  rw [this]
  exact hy

theorem mulAut_mulAut_eq_conj [Finite S] [IsSimpleGroup S] (hS : ∃ a b : S, a * b ≠ b * a)
    (φ : MulAut (MulAut S)) : ∃ a : MulAut S, φ = MulAut.conj a := by
  have hex : ∀ s : S, ∃ s' : S, MulAut.conj s' = φ (MulAut.conj s) := fun s =>
    innAut_map_le hS φ ⟨s, rfl⟩
  choose θ0 hθ0 using hex
  have hinj := conj_injective_of_simple hS
  have hmul : ∀ s t : S, θ0 (s * t) = θ0 s * θ0 t := by
    intro s t
    apply hinj
    rw [hθ0, map_mul, map_mul, map_mul, hθ0, hθ0]
  have hθinj : Function.Injective θ0 := by
    intro s t h
    apply hinj
    apply φ.injective
    rw [← hθ0, ← hθ0, h]
  let θ : MulAut S := MulEquiv.ofBijective (MonoidHom.mk' θ0 hmul)
    ⟨hθinj, Finite.injective_iff_surjective.1 hθinj⟩
  have hθ : ∀ s : S, θ s = θ0 s := fun s => rfl
  have hinn : ∀ s : S, φ (MulAut.conj s) = θ * MulAut.conj s * θ⁻¹ := by
    intro s
    rw [mul_conj_mul_inv, hθ, hθ0]
  refine ⟨θ, ?_⟩
  ext x : 1
  have hf : θ⁻¹ * φ x * θ = x := by
    have h1 : x⁻¹ * (θ⁻¹ * φ x * θ) = 1 := by
      apply eq_one_of_commute_conj hS
      intro s
      have e1 : φ x * (θ * MulAut.conj s * θ⁻¹) * (φ x)⁻¹ =
          θ * (x * MulAut.conj s * x⁻¹) * θ⁻¹ := by
        rw [← hinn s]
        calc φ x * φ (MulAut.conj s) * (φ x)⁻¹ = φ (x * MulAut.conj s * x⁻¹) := by
              simp [map_mul, map_inv]
          _ = φ (MulAut.conj (x s)) := by rw [mul_conj_mul_inv]
          _ = θ * MulAut.conj (x s) * θ⁻¹ := hinn _
          _ = _ := by rw [mul_conj_mul_inv x s]
      have e2 : (θ⁻¹ * φ x * θ) * MulAut.conj s * (θ⁻¹ * φ x * θ)⁻¹ =
          x * MulAut.conj s * x⁻¹ := by
        calc (θ⁻¹ * φ x * θ) * MulAut.conj s * (θ⁻¹ * φ x * θ)⁻¹
            = θ⁻¹ * (φ x * (θ * MulAut.conj s * θ⁻¹) * (φ x)⁻¹) * θ := by group
          _ = θ⁻¹ * (θ * (x * MulAut.conj s * x⁻¹) * θ⁻¹) * θ := by rw [e1]
          _ = _ := by group
      calc x⁻¹ * (θ⁻¹ * φ x * θ) * MulAut.conj s
          = x⁻¹ * ((θ⁻¹ * φ x * θ) * MulAut.conj s * (θ⁻¹ * φ x * θ)⁻¹) * (θ⁻¹ * φ x * θ) := by
            group
        _ = x⁻¹ * (x * MulAut.conj s * x⁻¹) * (θ⁻¹ * φ x * θ) := by rw [e2]
        _ = MulAut.conj s * (x⁻¹ * (θ⁻¹ * φ x * θ)) := by group
    exact (inv_mul_eq_one.1 h1).symm
  rw [MulAut.conj_apply]
  calc φ x = θ * (θ⁻¹ * φ x * θ) * θ⁻¹ := by group
    _ = θ * x * θ⁻¹ := by rw [hf]

theorem center_mulAut_eq_bot [IsSimpleGroup S] (hS : ∃ a b : S, a * b ≠ b * a) :
    Subgroup.center (MulAut S) = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  have := eq_one_of_commute_conj hS f fun s => (Subgroup.mem_center_iff.1 hf _).symm
  simp [this]

end CompleteAut

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
