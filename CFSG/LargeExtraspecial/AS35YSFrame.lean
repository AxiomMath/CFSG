module

public import CFSG.LargeExtraspecial.AS35YRFrameX
public import CFSG.LargeExtraspecial.AS35YRFrameE

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.ClassicalGroups.Orthogonal
  AS35YR

namespace AS35YS

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}

theorem t_ne_one_YS (F : Frame q) : F.t ≠ 1 := by
  intro e
  have h4 := F.t_c
  rw [e, LinearEquiv.coe_one, id] at h4
  apply F.a_ne_zero
  have h5 := congrArg (· - F.c) h4
  simpa using h5.symm

theorem tau_t_c'_YS (F : Frame q) : F.tau F.t F.c' = 0 := by
  rw [Frame.tau_def, F.t_c', add_sub_cancel_left, F.proj_b]

structure RadHyp0 (F : Frame q) (P : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop where
  inU : ∀ p ∈ P, F.InU p
  s₁_conj : ∀ p ∈ P, F.s₁ * p * F.s₁⁻¹ ∈ P
  s₂_conj : ∀ p ∈ P, F.s₂ * p * F.s₂⁻¹ ∈ P

namespace RadHyp0

variable {F : Frame q} {P : Subgroup (V ≃ₗ[ZMod 2] V)} (h : RadHyp0 F P)
include h

theorem exists_zero_left {y : V} (hy : y ∈ F.Y P h.inU) :
    ∃ p ∈ P, F.tau p F.c = 0 ∧ F.tau p F.c' = y := by
  obtain ⟨r, hr, hrc, hrc'⟩ := hy
  obtain ⟨hU₁, h₁c, h₁c'⟩ := Frame.tau_conj_s₁ (h.inU r hr)
  have hm := h.s₁_conj r hr
  refine ⟨F.s₁ * r * F.s₁⁻¹ * r⁻¹, mul_mem hm (inv_mem hr), ?_, ?_⟩
  · rw [Frame.tau_mul hU₁ (h.inU _ (inv_mem hr)),
      Frame.tau_inv (h.inU r hr) (h.inU _ (inv_mem hr)), h₁c, add_self_YR]
  · rw [Frame.tau_mul hU₁ (h.inU _ (inv_mem hr)),
      Frame.tau_inv (h.inU r hr) (h.inU _ (inv_mem hr)), h₁c', hrc', hrc, zero_add, add_zero]

theorem tau_mem_Y {p : V ≃ₗ[ZMod 2] V} (hp : p ∈ P) :
    F.tau p F.c ∈ F.Y P h.inU ∧ F.tau p F.c' ∈ F.Y P h.inU := by
  have hU := h.inU p hp
  have hpi := h.inU _ (inv_mem hp)
  obtain ⟨hU₂, h₂c, h₂c'⟩ := Frame.tau_conj_s₂ hU
  have hm₂ := h.s₂_conj p hp
  have hY₂ : F.tau p F.c' ∈ F.Y P h.inU := by
    refine ⟨F.s₂ * p * F.s₂⁻¹ * p⁻¹, mul_mem hm₂ (inv_mem hp), ?_, ?_⟩
    · rw [Frame.tau_mul hU₂ hpi, Frame.tau_inv hU hpi, h₂c,
        add_comm (F.tau p F.c) (F.tau p F.c'), add_assoc, add_self_YR, add_zero]
    · rw [Frame.tau_mul hU₂ hpi, Frame.tau_inv hU hpi, h₂c', add_self_YR]
  refine ⟨?_, hY₂⟩
  obtain ⟨hU₁, h₁c, h₁c'⟩ := Frame.tau_conj_s₁ hU
  have hm₁ := h.s₁_conj p hp
  set r := F.s₁ * p * F.s₁⁻¹ * p⁻¹ with hr
  have hrP : r ∈ P := mul_mem hm₁ (inv_mem hp)
  have hrU := h.inU r hrP
  have hrc : F.tau r F.c = 0 := by
    rw [hr, Frame.tau_mul hU₁ hpi, Frame.tau_inv hU hpi, h₁c, add_self_YR]
  have hrc' : F.tau r F.c' = F.tau p F.c := by
    rw [hr, Frame.tau_mul hU₁ hpi, Frame.tau_inv hU hpi, h₁c',
      add_comm (F.tau p F.c') (F.tau p F.c), add_assoc, add_self_YR, add_zero]
  obtain ⟨hU₃, h₃c, h₃c'⟩ := Frame.tau_conj_s₂ hrU
  have hm₃ := h.s₂_conj r hrP
  refine ⟨F.s₂ * r * F.s₂⁻¹ * r⁻¹, mul_mem hm₃ (inv_mem hrP), ?_, ?_⟩
  · rw [Frame.tau_mul hU₃ (h.inU _ (inv_mem hrP)), Frame.tau_inv hrU (h.inU _ (inv_mem hrP)),
      h₃c, hrc, hrc', zero_add, add_zero]
  · rw [Frame.tau_mul hU₃ (h.inU _ (inv_mem hrP)), Frame.tau_inv hrU (h.inU _ (inv_mem hrP)),
      h₃c', add_self_YR]

theorem exists_tau_eq {y₁ y₂ : V} (hy₁ : y₁ ∈ F.Y P h.inU) (hy₂ : y₂ ∈ F.Y P h.inU) :
    ∃ p ∈ P, F.tau p F.c = y₁ ∧ F.tau p F.c' = y₂ := by
  obtain ⟨p₁, hp₁, h₁c, h₁c'⟩ := hy₁
  obtain ⟨p₂, hp₂, h₂c, h₂c'⟩ := h.exists_zero_left hy₂
  refine ⟨p₁ * p₂, mul_mem hp₁ hp₂, ?_, ?_⟩
  · rw [Frame.tau_mul (h.inU _ hp₁) (h.inU _ hp₂), h₁c, h₂c, add_zero]
  · rw [Frame.tau_mul (h.inU _ hp₁) (h.inU _ hp₂), h₁c', h₂c', zero_add]

theorem exists_ne_zero_mem_Y {p : V ≃ₗ[ZMod 2] V} (hp : p ∈ P) (hp1 : p ≠ 1) (hpt : p ≠ F.t) :
    ∃ y ∈ F.Y P h.inU, y ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have h1 := hcon _ (h.tau_mem_Y hp).1
  have h2 := hcon _ (h.tau_mem_Y hp).2
  rcases Frame.eq_one_or_eq_t (h.inU p hp) h1 h2 with h' | h'
  · exact hp1 h'
  · exact hpt h'

theorem apply_mem_Y {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup q)
    (ga : g F.a = F.a) (gb : g F.b = F.b) (gc : g F.c = F.c) (gc' : g F.c' = F.c')
    (hgP : ∀ p ∈ P, g * p * g⁻¹ ∈ P) {y : V} (hy : y ∈ F.Y P h.inU) : g y ∈ F.Y P h.inU := by
  obtain ⟨p, hp, hpc, hpc'⟩ := hy
  obtain ⟨-, hτ⟩ := Frame.tau_conj_of_fix hg ga gb gc gc' (h.inU p hp)
  refine ⟨g * p * g⁻¹, hgP p hp, ?_, ?_⟩
  · rw [hτ _ gc, hpc]
  · rw [hτ _ gc', hpc', map_zero]

theorem mem_Xp {y : V} (hy : y ∈ F.Y P h.inU) : y ∈ F.Xp := by
  obtain ⟨p, hp, rfl, -⟩ := hy
  exact Frame.mem_Xp.mpr ⟨Frame.polar_tau_a (h.inU p hp) _, Frame.polar_tau_b (h.inU p hp) _,
    Frame.polar_tau_c _ _, Frame.polar_tau_c' _ _⟩

theorem card_Y_mul_le [Finite P] :
    Nat.card (F.Y P h.inU) * Nat.card (F.Y P h.inU) ≤ Nat.card P := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_surjective
    (fun p : P => (⟨F.tau p F.c, (h.tau_mem_Y p.2).1⟩, ⟨F.tau p F.c', (h.tau_mem_Y p.2).2⟩)) ?_
  rintro ⟨⟨y₁, hy₁⟩, ⟨y₂, hy₂⟩⟩
  obtain ⟨p, hp, h₁, h₂⟩ := h.exists_tau_eq hy₁ hy₂
  exact ⟨⟨p, hp⟩, by simp [h₁, h₂]⟩

theorem two_mul_card_Y_le [Finite P] (ht : F.t ∈ P) :
    2 * (Nat.card (F.Y P h.inU) * Nat.card (F.Y P h.inU)) ≤ Nat.card P := by
  classical
  have hsec : ∀ z : F.Y P h.inU × F.Y P h.inU, ∃ p ∈ P,
      F.tau p F.c = z.1 ∧ F.tau p F.c' = z.2 := fun z => h.exists_tau_eq z.1.2 z.2.2
  choose s hsP hs₁ hs₂ using hsec
  have hb : Nat.card ((F.Y P h.inU × F.Y P h.inU) × Bool) =
      Nat.card (F.Y P h.inU) * Nat.card (F.Y P h.inU) * 2 := by
    rw [Nat.card_prod, Nat.card_prod]
    simp
  have htP : ∀ β : Bool, (if β then F.t else 1) ∈ P := fun β => by
    cases β
    · exact one_mem P
    · exact ht
  have htau : ∀ (w : F.Y P h.inU × F.Y P h.inU) (β : Bool),
      F.tau (s w * (if β then F.t else 1)) F.c = w.1 ∧
        F.tau (s w * (if β then F.t else 1)) F.c' = w.2 := by
    intro w β
    rw [Frame.tau_mul (h.inU _ (hsP w)) (h.inU _ (htP β)),
      Frame.tau_mul (h.inU _ (hsP w)) (h.inU _ (htP β)), hs₁, hs₂]
    cases β
    · simp only [Bool.false_eq_true, ↓reduceIte, Frame.tau_one, add_zero, and_self]
    · simp only [↓reduceIte, Frame.tau_t_c, tau_t_c'_YS, add_zero, and_self]
  rw [mul_comm, ← hb]
  refine Nat.card_le_card_of_injective
    (fun x : (F.Y P h.inU × F.Y P h.inU) × Bool =>
      (⟨s x.1 * (if x.2 then F.t else 1), mul_mem (hsP _) (htP _)⟩ : P)) ?_
  rintro ⟨z, b⟩ ⟨z', b'⟩ hzz
  have e : s z * (if b then F.t else 1) = s z' * (if b' then F.t else 1) :=
    congrArg Subtype.val hzz
  have hz : z = z' := by
    obtain ⟨h1, h2⟩ := htau z b
    obtain ⟨h1', h2'⟩ := htau z' b'
    rw [e] at h1 h2
    exact Prod.ext (Subtype.ext (h1.symm.trans h1')) (Subtype.ext (h2.symm.trans h2'))
  subst hz
  have e' := mul_left_cancel e
  have hbb : b = b' := by
    cases b <;> cases b'
    · rfl
    · exact absurd e'.symm (by simpa using t_ne_one_YS F)
    · exact absurd e' (by simpa using t_ne_one_YS F)
    · rfl
  rw [hbb]

theorem commute_of_le_span {y : V} (hY : ∀ z ∈ F.Y P h.inU, z = 0 ∨ z = y) {p p' : V ≃ₗ[ZMod 2] V}
    (hp : p ∈ P) (hp' : p' ∈ P) : p * p' = p' * p := by
  have hzero : ∀ z ∈ F.Y P h.inU, ∀ z' ∈ F.Y P h.inU, polar q z z' = 0 := by
    intro z hz z' hz'
    rcases hY z hz with rfl | rfl
    · exact polar_zero_left _ _
    · rcases hY z' hz' with rfl | rfl
      · exact polar_zero_right _ _
      · exact polar_self_YR _
  refine Frame.commute_of_polar (h.inU p hp) (h.inU p' hp') ?_
  rw [hzero _ (h.tau_mem_Y hp').1 _ (h.tau_mem_Y hp).2,
    hzero _ (h.tau_mem_Y hp).1 _ (h.tau_mem_Y hp').2]

end RadHyp0

theorem card_le_of_inU (F : Frame q) {P : Subgroup (V ≃ₗ[ZMod 2] V)} [Finite V]
    (hU : ∀ p ∈ P, F.InU p) : Nat.card P ≤ 2 * (Nat.card F.Xp * Nat.card F.Xp) := by
  classical
  have hX : ∀ p ∈ P, ∀ v, F.tau p v ∈ F.Xp := fun p hp v =>
    Frame.mem_Xp.mpr ⟨Frame.polar_tau_a (hU p hp) _, Frame.polar_tau_b (hU p hp) _,
      Frame.polar_tau_c _ _, Frame.polar_tau_c' _ _⟩
  set Θ : P → F.Xp × F.Xp := fun p =>
    (⟨F.tau p F.c, hX p p.2 _⟩, ⟨F.tau p F.c', hX p p.2 _⟩) with hΘ
  have hfib : ∀ p p' : P, Θ p = Θ p' → (p' : V ≃ₗ[ZMod 2] V) = p ∨
      (p' : V ≃ₗ[ZMod 2] V) = p * F.t := by
    intro p p' e
    have hc := congrArg (fun z => ((z.1 : F.Xp) : V)) e
    have hc' := congrArg (fun z => ((z.2 : F.Xp) : V)) e
    simp only [hΘ] at hc hc'
    have hpi := hU _ (inv_mem p.2)
    have hq : F.InU ((p : V ≃ₗ[ZMod 2] V)⁻¹ * p') := hU _ (mul_mem (inv_mem p.2) p'.2)
    have h1 : F.tau ((p : V ≃ₗ[ZMod 2] V)⁻¹ * p') F.c = 0 := by
      rw [Frame.tau_mul hpi (hU _ p'.2), Frame.tau_inv (hU _ p.2) hpi, hc, add_self_YR]
    have h2 : F.tau ((p : V ≃ₗ[ZMod 2] V)⁻¹ * p') F.c' = 0 := by
      rw [Frame.tau_mul hpi (hU _ p'.2), Frame.tau_inv (hU _ p.2) hpi, hc', add_self_YR]
    rcases Frame.eq_one_or_eq_t hq h1 h2 with h3 | h3
    · left
      calc (p' : V ≃ₗ[ZMod 2] V) = p * ((p : V ≃ₗ[ZMod 2] V)⁻¹ * p') := by group
        _ = p := by rw [h3, mul_one]
    · right
      calc (p' : V ≃ₗ[ZMod 2] V) = p * ((p : V ≃ₗ[ZMod 2] V)⁻¹ * p') := by group
        _ = p * F.t := by rw [h3]
  have hsec : ∀ z : F.Xp × F.Xp, ∃ r : P, z ∈ Set.range Θ → Θ r = z := by
    intro z
    by_cases hz : z ∈ Set.range Θ
    · obtain ⟨r, hr⟩ := hz
      exact ⟨r, fun _ => hr⟩
    · exact ⟨1, fun h' => absurd h' hz⟩
  choose s hs using hsec
  have hfib' : ∀ p : P, (p : V ≃ₗ[ZMod 2] V) = s (Θ p) ∨
      (p : V ≃ₗ[ZMod 2] V) = s (Θ p) * F.t := fun p => hfib _ _ (hs (Θ p) ⟨p, rfl⟩)
  have hb : Nat.card ((F.Xp × F.Xp) × Bool) = Nat.card F.Xp * Nat.card F.Xp * 2 := by
    rw [Nat.card_prod, Nat.card_prod]
    simp
  rw [mul_comm, ← hb]
  refine Nat.card_le_card_of_injective
    (fun p : P => (Θ p, decide ((p : V ≃ₗ[ZMod 2] V) = s (Θ p)))) ?_
  intro p p' e
  simp only [Prod.mk.injEq] at e
  obtain ⟨e1, e2⟩ := e
  have ht1 := t_ne_one_YS F
  apply Subtype.ext
  rcases hfib' p with h1 | h1 <;> rcases hfib' p' with h2 | h2
  · rw [h1, h2, e1]
  · exfalso
    have hd : decide ((p' : V ≃ₗ[ZMod 2] V) = s (Θ p')) = true := by
      rw [← e2]
      exact decide_eq_true h1
    have h3 := of_decide_eq_true hd
    rw [h3] at h2
    exact ht1 (mul_left_cancel (h2.symm.trans (mul_one _).symm))
  · exfalso
    have hd : decide ((p : V ≃ₗ[ZMod 2] V) = s (Θ p)) = true := by
      rw [e2]
      exact decide_eq_true h2
    have h3 := of_decide_eq_true hd
    rw [h3] at h1
    exact ht1 (mul_left_cancel (h1.symm.trans (mul_one _).symm))
  · rw [h1, h2, e1]

end AS35YS

end CFSG.LargeExtraspecial
