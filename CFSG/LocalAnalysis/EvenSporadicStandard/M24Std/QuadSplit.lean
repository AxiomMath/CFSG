module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.QuadBasic

public section

namespace CFSG.EvenSporadicStandard.M24Std

namespace Quad

open Subgroup

variable {G : Type} [Group G] [Finite G] {L A : Subgroup G} {z w : G}

structure SplitHyp (G : Type) [Group G] [Finite G] (L A : Subgroup G) (z w : G) : Prop where
  hs : LocalSetting G L z
  hAL : A ≤ L
  hF : SextetFacts L A
  hT : TranslationData A z
  wN : w ∈ egNL L A
  w3 : w * w * w = 1
  wfix : ∀ a ∈ A, w * a * w⁻¹ = a → a = 1
  omega : ∀ n ∈ egNL L A, ∃ b ∈ A, n * w * n⁻¹ = w * b ∨ n * w * n⁻¹ = w⁻¹ * b

omit [Finite G] in
theorem card_of_fibres {C A : Subgroup G} (f : G → G) (hAC : A ≤ C) (hfA : ∀ c ∈ C, f c ∈ A)
    (hsurj : ∀ a ∈ A, ∃ c ∈ C, f c = a)
    (hfib : ∀ c ∈ C, ∀ d ∈ C, f c = f d ↔ c⁻¹ * d ∈ A) :
    Nat.card C = Nat.card A * Nat.card A := by
  have hex : ∀ a : G, ∃ c : G, a ∈ A → c ∈ C ∧ f c = a := by
    intro a
    by_cases ha : a ∈ A
    · obtain ⟨c, hc, hfc⟩ := hsurj a ha
      exact ⟨c, fun _ => ⟨hc, hfc⟩⟩
    · exact ⟨1, fun h => absurd h ha⟩
  choose s hs using hex
  have hmem : ∀ c ∈ C, (s (f c))⁻¹ * c ∈ A := fun c hc =>
    (hfib _ (hs _ (hfA c hc)).1 c hc).1 (hs _ (hfA c hc)).2
  have hf1 : ∀ x ∈ A, ∀ a ∈ A, f (s x * a) = x := by
    intro x hx a ha
    have h2 := (hfib _ (hs x hx).1 _ (C.mul_mem (hs x hx).1 (hAC ha))).2 (by simpa using ha)
    rw [(hs x hx).2] at h2
    exact h2.symm
  let e : C ≃ A × A :=
    { toFun := fun c => (⟨f c, hfA c c.2⟩, ⟨(s (f c))⁻¹ * c, hmem c c.2⟩)
      invFun := fun p => ⟨s p.1 * p.2, C.mul_mem (hs _ p.1.2).1 (hAC p.2.2)⟩
      left_inv := fun c => by
        ext
        simp
      right_inv := fun p => by
        obtain ⟨⟨x, hx⟩, ⟨a, ha⟩⟩ := p
        ext
        · simp [hf1 x hx a ha]
        · simp [hf1 x hx a ha] }
  rw [Nat.card_congr e, Nat.card_prod]

namespace SplitHyp

variable (H : SplitHyp G L A z w)
include H

theorem wz : w * z = z * w := nl_comm_z H.hs H.wN

theorem lam_conj {t : G} (ht : t ∈ egLam A z) : w * t * w⁻¹ ∈ egLam A z :=
  conj_mem_lam H.hs H.hAL H.wN ht

theorem k_mem {u : G} (hu : u ∈ egLam A z) : u * w * u⁻¹ * w⁻¹ ∈ egLam A z := by
  have := (egLam A z).mul_mem hu (H.lam_conj ((egLam A z).inv_mem hu))
  simpa [mul_assoc] using this

theorem norm_eq {b : G} (hb : b ∈ A) :
    b * (w * b * w⁻¹) * (w * w * b * (w * w)⁻¹) = 1 := by
  have hb1 : w * b * w⁻¹ ∈ A := nl_conj_mem H.wN hb
  have hb2 : w * w * b * (w * w)⁻¹ ∈ A := by
    have := nl_conj_mem H.wN hb1
    convert this using 1
    group
  have hy : b * (w * b * w⁻¹) * (w * w * b * (w * w)⁻¹) ∈ A :=
    A.mul_mem (A.mul_mem hb hb1) hb2
  apply H.wfix _ hy
  have e3 : w * (w * w * b * (w * w)⁻¹) * w⁻¹ = b := by
    calc w * (w * w * b * (w * w)⁻¹) * w⁻¹ = (w * w * w) * b * (w * w * w)⁻¹ := by group
      _ = b := by rw [H.w3]; group
  have e2 : w * (w * b * w⁻¹) * w⁻¹ = w * w * b * (w * w)⁻¹ := by group
  calc w * (b * (w * b * w⁻¹) * (w * w * b * (w * w)⁻¹)) * w⁻¹
        = (w * b * w⁻¹) * (w * (w * b * w⁻¹) * w⁻¹) *
            (w * (w * w * b * (w * w)⁻¹) * w⁻¹) := by group
    _ = (w * b * w⁻¹) * (w * w * b * (w * w)⁻¹) * b := by rw [e2, e3]
    _ = b * (w * b * w⁻¹) * (w * w * b * (w * w)⁻¹) := by
        rw [H.hF.elem.1 _ (A.mul_mem hb1 hb2) b hb, ← mul_assoc]

theorem cube_eq {b : G} (hb : b ∈ A) : (b * w) * (b * w) * (b * w) = 1 := by
  have h := H.norm_eq hb
  calc (b * w) * (b * w) * (b * w)
        = b * (w * b * w⁻¹) * (w * w * b * (w * w)⁻¹) * (w * w * w) := by group
    _ = 1 := by rw [h, H.w3, one_mul]

theorem z_ne {u a : G} (ha : a ∈ A) :
    z ≠ u * w * u⁻¹ * w⁻¹ * a := by
  intro hz
  obtain ⟨p, hp⟩ : ∃ p, p = a⁻¹ * w := ⟨_, rfl⟩
  have hpz : p * z = z * p := by
    have h1 : a⁻¹ * z = z * a⁻¹ := (z_comm_A H.hs H.hAL (A.inv_mem ha)).symm
    rw [hp, mul_assoc, H.wz, ← mul_assoc, h1, mul_assoc]
  have h3 : p * p * p = 1 := by
    rw [hp]
    exact H.cube_eq (A.inv_mem ha)
  have huw : u * w * u⁻¹ = z * p := by
    rw [hp, hz]
    group
  have hcube : (u * w * u⁻¹) * (u * w * u⁻¹) * (u * w * u⁻¹) = 1 := by
    calc (u * w * u⁻¹) * (u * w * u⁻¹) * (u * w * u⁻¹) = u * (w * w * w) * u⁻¹ := by group
      _ = 1 := by rw [H.w3]; group
  rw [huw] at hcube
  have e : (z * p) * (z * p) * (z * p) = z * (z * z) * (p * p * p) := by
    calc (z * p) * (z * p) * (z * p) = z * (p * z) * (p * z) * p := by group
      _ = z * (z * p) * (z * p) * p := by rw [hpz]
      _ = z * z * (p * z) * p * p := by group
      _ = z * z * (z * p) * p * p := by rw [hpz]
      _ = z * (z * z) * (p * p * p) := by group
  rw [e, z_mul_self H.hs, h3, mul_one, mul_one] at hcube
  exact z_ne_one H.hs hcube

theorem exists_subgroup : ∃ C : Subgroup G,
    ∀ c, c ∈ C ↔ ∃ u ∈ egLam A z, ∃ a ∈ A, c = u * w * u⁻¹ * w⁻¹ * a := by
  have hs := H.hs
  have hAL := H.hAL
  have hF := H.hF
  have hT := H.hT
  refine ⟨{ carrier := {c | ∃ u ∈ egLam A z, ∃ a ∈ A, c = u * w * u⁻¹ * w⁻¹ * a},
            mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, fun c => Iff.rfl⟩
  · rintro c d ⟨u, hu, a, ha, rfl⟩ ⟨u', hu', a', ha', rfl⟩
    have hx := H.k_mem hu
    have hy := H.k_mem hu'
    obtain ⟨x, hx'⟩ : ∃ x, u * w * u⁻¹ * w⁻¹ = x := ⟨_, rfl⟩
    obtain ⟨y, hy'⟩ : ∃ y, u' * w * u'⁻¹ * w⁻¹ = y := ⟨_, rfl⟩
    rw [hx'] at hx ⊢
    rw [hy'] at hy ⊢
    refine ⟨u * u', (egLam A z).mul_mem hu hu',
      (u * u' * w * (u * u')⁻¹ * w⁻¹)⁻¹ * (x * a * (y * a')), ?_, by group⟩
    have hk : u * u' * w * (u * u')⁻¹ * w⁻¹ = u * y * u⁻¹ * x := by
      rw [← hx', ← hy']
      group
    have hγ : u * y⁻¹ * u⁻¹ * y ∈ A := by
      simpa using comm_mem hs hAL hF hT hu ((egLam A z).inv_mem hy)
    have hδ : x⁻¹ * y⁻¹ * x * y ∈ A := by
      simpa using comm_mem hs hAL hF hT ((egLam A z).inv_mem hx) ((egLam A z).inv_mem hy)
    have hay : a * y = y * a := (lam_comm hy ha).symm
    have hγx : x⁻¹ * (u * y⁻¹ * u⁻¹ * y) * x = u * y⁻¹ * u⁻¹ * y := by
      rw [mul_assoc, ← lam_comm hx hγ, inv_mul_cancel_left]
    have e : (u * u' * w * (u * u')⁻¹ * w⁻¹)⁻¹ * (x * a * (y * a')) =
        (u * y⁻¹ * u⁻¹ * y) * (x⁻¹ * y⁻¹ * x * y) * (a * a') := by
      calc (u * u' * w * (u * u')⁻¹ * w⁻¹)⁻¹ * (x * a * (y * a'))
            = x⁻¹ * u * y⁻¹ * u⁻¹ * x * (a * y) * a' := by rw [hk]; group
        _ = x⁻¹ * u * y⁻¹ * u⁻¹ * x * (y * a) * a' := by rw [hay]
        _ = (x⁻¹ * (u * y⁻¹ * u⁻¹ * y) * x) * (x⁻¹ * y⁻¹ * x * y) * (a * a') := by group
        _ = (u * y⁻¹ * u⁻¹ * y) * (x⁻¹ * y⁻¹ * x * y) * (a * a') := by rw [hγx]
    rw [e]
    exact A.mul_mem (A.mul_mem hγ hδ) (A.mul_mem ha ha')
  · exact ⟨1, (egLam A z).one_mem, 1, A.one_mem, by group⟩
  · rintro c ⟨u, hu, a, ha, rfl⟩
    have hv := H.k_mem ((egLam A z).inv_mem hu)
    obtain ⟨v, hv'⟩ : ∃ v, u⁻¹ * w * u⁻¹⁻¹ * w⁻¹ = v := ⟨_, rfl⟩
    rw [hv'] at hv
    refine ⟨u⁻¹, (egLam A z).inv_mem hu, v⁻¹ * (u * w * u⁻¹ * w⁻¹ * a)⁻¹, ?_, ?_⟩
    · have hxinv : (u * w * u⁻¹ * w⁻¹ * a)⁻¹ = a⁻¹ * (u * v * u⁻¹) := by
        rw [← hv']
        group
      have hva : v⁻¹ * a⁻¹ * v = a⁻¹ := by
        rw [lam_comm ((egLam A z).inv_mem hv) (A.inv_mem ha), inv_mul_cancel_right]
      have hc : v⁻¹ * u * v * u⁻¹ ∈ A := by
        simpa using comm_mem hs hAL hF hT ((egLam A z).inv_mem hv) hu
      have e : v⁻¹ * (a⁻¹ * (u * v * u⁻¹)) = (v⁻¹ * a⁻¹ * v) * (v⁻¹ * u * v * u⁻¹) := by group
      rw [hxinv, e, hva]
      exact A.mul_mem (A.inv_mem ha) hc
    · rw [hv']
      group

theorem tau_inv {t : G} (ht : t ∈ egLam A z) :
    z * t⁻¹ * z⁻¹ * t⁻¹⁻¹ = (z * t * z⁻¹ * t⁻¹)⁻¹ := by
  have h := tau_mul H.hs H.hAL H.hT ht ((egLam A z).inv_mem ht)
  have h1 : z * 1 * z⁻¹ * (1 : G)⁻¹ = 1 := by group
  rw [mul_inv_cancel, h1] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem tau_A {a : G} (ha : a ∈ A) : z * a * z⁻¹ * a⁻¹ = 1 := by
  rw [z_comm_A H.hs H.hAL ha]
  group

theorem exists_C : ∃ C : Subgroup G, A ≤ C ∧ C ≤ egLam A z ∧
    (∀ m ∈ egM A z, ∀ c ∈ C, m * c * m⁻¹ ∈ C) ∧ z ∉ C ∧ Nat.card C = 4096 ∧
    (∀ t ∈ egLam A z, t ∈ C ∨ z * t ∈ C) ∧ (∀ a ∈ A, ∃ c ∈ C, z * c * z⁻¹ * c⁻¹ = a) ∧
    ∀ n ∈ egNL L A, ∀ c ∈ C, n * c * n⁻¹ ∈ C := by
  have hs := H.hs
  have hAL := H.hAL
  have hF := H.hF
  have hT := H.hT
  obtain ⟨C, hC⟩ := H.exists_subgroup
  have hAC : A ≤ C := fun a ha => (hC a).2 ⟨1, (egLam A z).one_mem, a, ha, by group⟩
  have hCΛ : C ≤ egLam A z := by
    intro c hc
    obtain ⟨u, hu, a, ha, rfl⟩ := (hC c).1 hc
    exact (egLam A z).mul_mem (H.k_mem hu) (le_lam hF ha)
  have hzC : z ∉ C := by
    intro hz
    obtain ⟨u, hu, a, ha, h⟩ := (hC z).1 hz
    exact H.z_ne ha h
  have hnormΛ : ∀ t ∈ egLam A z, ∀ c ∈ C, t * c * t⁻¹ ∈ C := by
    intro t ht c hc
    have h1 := comm_mem hs hAL hF hT ht (hCΛ hc)
    have : t * c * t⁻¹ = (t * c * t⁻¹ * c⁻¹) * c := by group
    rw [this]
    exact C.mul_mem (hAC h1) hc
  have hnormN : ∀ n ∈ egNL L A, ∀ c ∈ C, n * c * n⁻¹ ∈ C := by
    intro n hn c hc
    obtain ⟨u, hu, a, ha, rfl⟩ := (hC c).1 hc
    have hu' := conj_mem_lam hs hAL hn hu
    obtain ⟨u', hu'd⟩ : ∃ u', n * u * n⁻¹ = u' := ⟨_, rfl⟩
    rw [hu'd] at hu'
    have hk : n * (u * w * u⁻¹ * w⁻¹ * a) * n⁻¹ =
        u' * (n * w * n⁻¹) * u'⁻¹ * (n * w * n⁻¹)⁻¹ * (n * a * n⁻¹) := by
      rw [← hu'd]
      group
    rw [hk]
    refine C.mul_mem ?_ (hAC (nl_conj_mem hn ha))
    obtain ⟨b, hb, hw' | hw'⟩ := H.omega n hn
    · rw [hw']
      have hbu : b * u'⁻¹ = u'⁻¹ * b := (lam_comm ((egLam A z).inv_mem hu') hb).symm
      have : u' * (w * b) * u'⁻¹ * (w * b)⁻¹ = u' * w * u'⁻¹ * w⁻¹ * 1 := by
        calc u' * (w * b) * u'⁻¹ * (w * b)⁻¹ = u' * w * (b * u'⁻¹) * b⁻¹ * w⁻¹ := by group
          _ = u' * w * (u'⁻¹ * b) * b⁻¹ * w⁻¹ := by rw [hbu]
          _ = u' * w * u'⁻¹ * w⁻¹ * 1 := by group
      rw [this]
      exact (hC _).2 ⟨u', hu', 1, A.one_mem, rfl⟩
    · rw [hw']
      have hbu : b * u'⁻¹ = u'⁻¹ * b := (lam_comm ((egLam A z).inv_mem hu') hb).symm
      have hv : w⁻¹ * u' * w ∈ egLam A z := by
        have := conj_mem_lam hs hAL ((egNL L A).inv_mem H.wN) hu'
        simpa using this
      have : u' * (w⁻¹ * b) * u'⁻¹ * (w⁻¹ * b)⁻¹ =
          ((w⁻¹ * u' * w) * w * (w⁻¹ * u' * w)⁻¹ * w⁻¹ * 1)⁻¹ := by
        calc u' * (w⁻¹ * b) * u'⁻¹ * (w⁻¹ * b)⁻¹ = u' * w⁻¹ * (b * u'⁻¹) * b⁻¹ * w := by group
          _ = u' * w⁻¹ * (u'⁻¹ * b) * b⁻¹ * w := by rw [hbu]
          _ = ((w⁻¹ * u' * w) * w * (w⁻¹ * u' * w)⁻¹ * w⁻¹ * 1)⁻¹ := by group
      rw [this]
      exact C.inv_mem ((hC _).2 ⟨_, hv, 1, A.one_mem, rfl⟩)
  have hτC : ∀ c ∈ C, z * c * z⁻¹ * c⁻¹ ∈ A := fun c hc => tau_mem hs hAL hT (hCΛ hc)
  have honto : ∀ a ∈ A, ∃ c ∈ C, z * c * z⁻¹ * c⁻¹ = a := by
    intro a ha
    have hxa : w * a * w⁻¹ ∈ A := nl_conj_mem H.wN ha
    obtain ⟨u, hu, hux⟩ := surj_tau hs hAL hT hxa
    obtain ⟨x, hx'⟩ : ∃ x, w * a * w⁻¹ = x := ⟨_, rfl⟩
    rw [hx'] at hxa hux
    refine ⟨u * w * u⁻¹ * w⁻¹, (hC _).2 ⟨u, hu, 1, A.one_mem, by group⟩, ?_⟩
    have hwu : w * u⁻¹ * w⁻¹ ∈ egLam A z := H.lam_conj ((egLam A z).inv_mem hu)
    have e1 : u * w * u⁻¹ * w⁻¹ = u * (w * u⁻¹ * w⁻¹) := by group
    rw [e1, tau_mul hs hAL hT hu hwu, tau_conj H.wz, H.tau_inv hu, hux]
    have hxx : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hF.elem.2 x hxa)
    have hn := H.norm_eq hxa
    have hwa : w * w * x * (w * w)⁻¹ = a := by
      rw [← hx']
      calc w * w * (w * a * w⁻¹) * (w * w)⁻¹ = (w * w * w) * a * (w * w * w)⁻¹ := by group
        _ = a := by rw [H.w3]; group
    rw [hwa] at hn
    rw [hxx, eq_inv_of_mul_eq_one_left hn]
    exact inv_eq_of_mul_eq_one_right (hF.elem.2 a ha)
  refine ⟨C, hAC, hCΛ, ?_, hzC, ?_, ?_, honto, hnormN⟩
  · intro m hm c hc
    have hzc : z * c * z⁻¹ ∈ C := hnormΛ z (z_mem_lam hs hAL) c hc
    obtain ⟨t, ht, l, hl, rfl | rfl⟩ := exists_decomp hs hAL hT hm
    · have : t * l * c * (t * l)⁻¹ = t * (l * c * l⁻¹) * t⁻¹ := by group
      rw [this]
      exact hnormΛ t ht _ (hnormN l hl c hc)
    · have : t * l * z * c * (t * l * z)⁻¹ = t * (l * (z * c * z⁻¹) * l⁻¹) * t⁻¹ := by group
      rw [this]
      exact hnormΛ t ht _ (hnormN l hl _ hzc)
  · have hfib : ∀ c ∈ C, ∀ d ∈ C,
        z * c * z⁻¹ * c⁻¹ = z * d * z⁻¹ * d⁻¹ ↔ c⁻¹ * d ∈ A := by
      intro c hc d hd
      constructor
      · intro h
        have hcd : c⁻¹ * d ∈ egLam A z := (egLam A z).mul_mem ((egLam A z).inv_mem (hCΛ hc))
          (hCΛ hd)
        have h1 : z * (c⁻¹ * d) * z⁻¹ * (c⁻¹ * d)⁻¹ = 1 := by
          rw [tau_mul hs hAL hT ((egLam A z).inv_mem (hCΛ hc)) (hCΛ hd), H.tau_inv (hCΛ hc), h,
            inv_mul_cancel]
        rcases ker_tau hs hAL hF hcd (comm_of_tau_eq_one h1) with h2 | h2
        · exact h2
        · exfalso
          apply hzC
          have : z = (z * (c⁻¹ * d)) * (c⁻¹ * d)⁻¹ := by group
          rw [this]
          exact C.mul_mem (hAC h2) (C.inv_mem (C.mul_mem (C.inv_mem hc) hd))
      · intro h
        have hd' : d = c * (c⁻¹ * d) := by group
        rw [hd', tau_mul hs hAL hT (hCΛ hc) (le_lam hF h), H.tau_A h, mul_one]
    rw [card_of_fibres (fun c => z * c * z⁻¹ * c⁻¹) hAC hτC honto hfib, hF.card_A]
  · intro t ht
    obtain ⟨c, hc, hct⟩ := honto _ (tau_mem hs hAL hT ht)
    have hcd : c⁻¹ * t ∈ egLam A z := (egLam A z).mul_mem ((egLam A z).inv_mem (hCΛ hc)) ht
    have h1 : z * (c⁻¹ * t) * z⁻¹ * (c⁻¹ * t)⁻¹ = 1 := by
      rw [tau_mul hs hAL hT ((egLam A z).inv_mem (hCΛ hc)) ht, H.tau_inv (hCΛ hc), hct,
        inv_mul_cancel]
    rcases ker_tau hs hAL hF hcd (comm_of_tau_eq_one h1) with h2 | h2
    · left
      have : t = c * (c⁻¹ * t) := by group
      rw [this]
      exact C.mul_mem hc (hAC h2)
    · right
      have : z * t = (z * c * z⁻¹) * (z * (c⁻¹ * t)) := by group
      rw [this]
      exact C.mul_mem (hnormΛ z (z_mem_lam hs hAL) c hc) (hAC h2)

end SplitHyp

end Quad

end CFSG.EvenSporadicStandard.M24Std
