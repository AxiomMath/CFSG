module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.EgawaDefs

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup

variable {G : Type} [Group G]

private def quadTau (z c : G) : G := z * c * z⁻¹ * c⁻¹

private structure QuadHyp (L A C : Subgroup G) (z : G) : Prop where
  AC : A ≤ C
  Aab : EgElemAb A
  cA : ∀ c ∈ C, ∀ a ∈ A, c * a = a * c
  sq : ∀ c ∈ C, c * c ∈ A
  comm : ∀ c ∈ C, ∀ d ∈ C, c * d * c⁻¹ * d⁻¹ ∈ A
  tauA : ∀ c ∈ C, quadTau z c ∈ A
  ker : ∀ c ∈ C, z * c = c * z → c ∈ A
  surj : ∀ a ∈ A, ∃ c ∈ C, quadTau z c = a
  zN : ∀ n ∈ egNL L A, n * z = z * n
  CN : ∀ n ∈ egNL L A, ∀ c ∈ C, n * c * n⁻¹ ∈ C

variable {L A C : Subgroup G} {z : G}

private lemma quadTau_one : quadTau z (1 : G) = 1 := by simp [quadTau]

private lemma quadTau_eq_one_iff {x : G} : quadTau z x = 1 ↔ z * x = x * z := by
  unfold quadTau
  constructor
  · intro h
    calc z * x = z * x * z⁻¹ * x⁻¹ * (x * z) := by group
      _ = x * z := by rw [h, one_mul]
  · intro h
    calc z * x * z⁻¹ * x⁻¹ = (z * x) * z⁻¹ * x⁻¹ := rfl
      _ = (x * z) * z⁻¹ * x⁻¹ := by rw [h]
      _ = 1 := by group

private lemma tau_mul (h : QuadHyp L A C z) {c d : G} (hc : c ∈ C) (hd : d ∈ C) :
    quadTau z (c * d) = quadTau z c * quadTau z d := by
  have h1 : c * quadTau z d = quadTau z d * c := h.cA c hc _ (h.tauA d hd)
  unfold quadTau at h1 ⊢
  calc z * (c * d) * z⁻¹ * (c * d)⁻¹
      = (z * c * z⁻¹ * c⁻¹) * (c * (z * d * z⁻¹ * d⁻¹)) * c⁻¹ := by group
    _ = (z * c * z⁻¹ * c⁻¹) * ((z * d * z⁻¹ * d⁻¹) * c) * c⁻¹ := by rw [h1]
    _ = (z * c * z⁻¹ * c⁻¹) * (z * d * z⁻¹ * d⁻¹) := by group

private lemma tau_inv (h : QuadHyp L A C z) {c : G} (hc : c ∈ C) :
    quadTau z c⁻¹ = (quadTau z c)⁻¹ := by
  have h1 := tau_mul h hc (C.inv_mem hc)
  rw [mul_inv_cancel, quadTau_one] at h1
  exact eq_inv_of_mul_eq_one_right h1.symm

private lemma tau_conj (h : QuadHyp L A C z) {n : G} (hn : n ∈ egNL L A) (c : G) :
    quadTau z (n * c * n⁻¹) = n * quadTau z c * n⁻¹ := by
  have hzn : n * z * n⁻¹ = z := by rw [h.zN n hn]; group
  unfold quadTau
  have e : z * (n * c * n⁻¹) * z⁻¹ * (n * c * n⁻¹)⁻¹ =
      (n * z * n⁻¹) * (n * c * n⁻¹) * (n * z * n⁻¹)⁻¹ * (n * c * n⁻¹)⁻¹ := by rw [hzn]
  rw [e]
  group

private lemma inv_mul_mem_of_tau_eq (h : QuadHyp L A C z) {c c' : G} (hc : c ∈ C) (hc' : c' ∈ C)
    (heq : quadTau z c = quadTau z c') : c⁻¹ * c' ∈ A := by
  apply h.ker _ (C.mul_mem (C.inv_mem hc) hc')
  rw [← quadTau_eq_one_iff, tau_mul h (C.inv_mem hc) hc', tau_inv h hc, heq, inv_mul_cancel]

private lemma sq_eq_of_tau_eq (h : QuadHyp L A C z) {c c' : G} (hc : c ∈ C) (hc' : c' ∈ C)
    (heq : quadTau z c = quadTau z c') : c' * c' = c * c := by
  obtain ⟨a, ha, rfl⟩ : ∃ a ∈ A, c' = c * a :=
    ⟨c⁻¹ * c', inv_mul_mem_of_tau_eq h hc hc' heq, by group⟩
  have hca : c * a = a * c := h.cA c hc a ha
  calc c * a * (c * a) = c * (a * c) * a := by group
    _ = c * (c * a) * a := by rw [hca]
    _ = c * c * (a * a) := by group
    _ = c * c := by rw [h.Aab.2 a ha, mul_one]

private lemma tau_eq_one_of_mem (h : QuadHyp L A C z)
    (hfix : ∀ x ∈ A, x ≠ 1 → ∀ w ∈ A,
      (∀ n ∈ egNL L A, n * x * n⁻¹ = x → n * w * n⁻¹ = w) → w = 1 ∨ w = x)
    {a : G} (ha : a ∈ A) : quadTau z a = 1 := by
  by_cases ha1 : a = 1
  · rw [ha1]; exact quadTau_one
  · rcases hfix a ha ha1 (quadTau z a) (h.tauA a (h.AC ha)) (fun n hn hna => by
        rw [← tau_conj h hn, hna]) with h1 | h1
    · exact h1
    · exfalso
      apply ha1
      have h2 : z * a * z⁻¹ = 1 := by
        calc z * a * z⁻¹ = (quadTau z a) * a := by unfold quadTau; group
          _ = a * a := by rw [h1]
          _ = 1 := h.Aab.2 a ha
      calc a = z⁻¹ * (z * a * z⁻¹) * z := by group
        _ = 1 := by rw [h2]; group

private lemma sq_dichotomy (h : QuadHyp L A C z)
    (hfix : ∀ x ∈ A, x ≠ 1 → ∀ w ∈ A,
      (∀ n ∈ egNL L A, n * x * n⁻¹ = x → n * w * n⁻¹ = w) → w = 1 ∨ w = x)
    {c : G} (hc : c ∈ C) (hx1 : quadTau z c ≠ 1) : c * c = 1 ∨ c * c = quadTau z c := by
  refine hfix _ (h.tauA c hc) hx1 (c * c) (h.sq c hc) (fun n hn hnx => ?_)
  have hnc : n * c * n⁻¹ ∈ C := h.CN n hn c hc
  have h1 : quadTau z c = quadTau z (n * c * n⁻¹) := by rw [tau_conj h hn, hnx]
  calc n * (c * c) * n⁻¹ = (n * c * n⁻¹) * (n * c * n⁻¹) := by group
    _ = c * c := sq_eq_of_tau_eq h hc hnc h1

private lemma sq_orbit (h : QuadHyp L A C z) (e : G →* G)
    (he : ∀ n ∈ egNL L A, ∀ x, e (n * x * n⁻¹) = n * e x * n⁻¹) {a₁ c₁ : G} (hc₁ : c₁ ∈ C)
    (hτ₁ : quadTau z c₁ = a₁) (hsq₁ : c₁ * c₁ = e a₁) {c : G} (hc : c ∈ C)
    (hcx : quadTau z c ∈ egOrb L A a₁) : c * c = e (quadTau z c) := by
  obtain ⟨n, hn, hnx⟩ := hcx
  have hnc : n * c₁ * n⁻¹ ∈ C := h.CN n hn c₁ hc₁
  have h1 : quadTau z (n * c₁ * n⁻¹) = quadTau z c := by rw [tau_conj h hn, hτ₁, hnx]
  calc c * c = (n * c₁ * n⁻¹) * (n * c₁ * n⁻¹) := sq_eq_of_tau_eq h hnc hc h1
    _ = n * (c₁ * c₁) * n⁻¹ := by group
    _ = n * e a₁ * n⁻¹ := by rw [hsq₁]
    _ = e (n * a₁ * n⁻¹) := (he n hn a₁).symm
    _ = e (quadTau z c) := by rw [hnx]

private lemma gen_lemma (h : QuadHyp L A C z) {a₁ : G}
    (hgen : Subgroup.closure
      {x : G | x ∈ A ∧ x ∈ egOrb L A a₁ ∧ a₁ * x ∈ egOrb L A a₁} = A)
    {H : Subgroup G} (hAH : A ≤ H) (hHC : H ≤ C)
    (hY : ∀ d ∈ C, quadTau z d ∈ egOrb L A a₁ → a₁ * quadTau z d ∈ egOrb L A a₁ → d ∈ H) :
    ∀ c ∈ C, c ∈ H := by
  obtain ⟨T, hTmem⟩ : ∃ T : Subgroup G, ∀ x, x ∈ T ↔ ∃ k ∈ H, quadTau z k = x :=
    ⟨{ carrier := {x | ∃ k ∈ H, quadTau z k = x}
       mul_mem' := by
         rintro _ _ ⟨k, hk, rfl⟩ ⟨l, hl, rfl⟩
         exact ⟨k * l, H.mul_mem hk hl, tau_mul h (hHC hk) (hHC hl)⟩
       one_mem' := ⟨1, H.one_mem, quadTau_one⟩
       inv_mem' := by
         rintro _ ⟨k, hk, rfl⟩
         exact ⟨k⁻¹, H.inv_mem hk, tau_inv h (hHC hk)⟩ }, fun x => Iff.rfl⟩
  have hT : A ≤ T := by
    have hcl : Subgroup.closure
        {x : G | x ∈ A ∧ x ∈ egOrb L A a₁ ∧ a₁ * x ∈ egOrb L A a₁} ≤ T := by
      rw [Subgroup.closure_le]
      rintro x ⟨hxA, hx1, hx2⟩
      obtain ⟨c, hc, rfl⟩ := h.surj x hxA
      exact (hTmem _).2 ⟨c, hY c hc hx1 hx2, rfl⟩
    rwa [hgen] at hcl
  intro c hc
  obtain ⟨k, hk, hkτ⟩ := (hTmem _).1 (hT (h.tauA c hc))
  have hmem := H.mul_mem hk (hAH (inv_mul_mem_of_tau_eq h (hHC hk) hc hkτ))
  simpa using hmem

private lemma quad_main (h : QuadHyp L A C z) (e : G →* G)
    (he : ∀ n ∈ egNL L A, ∀ x, e (n * x * n⁻¹) = n * e x * n⁻¹)
    (hfix : ∀ x ∈ A, x ≠ 1 → ∀ w ∈ A,
      (∀ n ∈ egNL L A, n * x * n⁻¹ = x → n * w * n⁻¹ = w) → w = 1 ∨ w = x)
    {a₁ c₁ : G}
    (hgen : Subgroup.closure
      {x : G | x ∈ A ∧ x ∈ egOrb L A a₁ ∧ a₁ * x ∈ egOrb L A a₁} = A)
    (hc₁ : c₁ ∈ C) (hτ₁ : quadTau z c₁ = a₁) (hsq₁ : c₁ * c₁ = e a₁) :
    (∀ c ∈ C, ∀ d ∈ C, c * d = d * c) ∧ ∀ c ∈ C, c * c = e (quadTau z c) := by
  have horb : ∀ c ∈ C, quadTau z c ∈ egOrb L A a₁ → c * c = e (quadTau z c) :=
    fun c hc hx => sq_orbit h e he hc₁ hτ₁ hsq₁ hc hx
  have hcomm₁ : ∀ d ∈ C, quadTau z d ∈ egOrb L A a₁ → a₁ * quadTau z d ∈ egOrb L A a₁ →
      c₁ * d = d * c₁ := by
    intro d hd hx hy
    have hk : d * c₁ * d⁻¹ * c₁⁻¹ ∈ A := h.comm d hd c₁ hc₁
    have hkc : c₁ * (d * c₁ * d⁻¹ * c₁⁻¹) = (d * c₁ * d⁻¹ * c₁⁻¹) * c₁ := h.cA c₁ hc₁ _ hk
    have hcd : c₁ * d ∈ C := C.mul_mem hc₁ hd
    have hτcd : quadTau z (c₁ * d) = a₁ * quadTau z d := by rw [tau_mul h hc₁ hd, hτ₁]
    have h1 : (c₁ * d) * (c₁ * d) = c₁ * c₁ * (d * d) := by
      have h3 := horb _ hcd (by rw [hτcd]; exact hy)
      rw [hτcd, map_mul, ← horb d hd hx, ← hsq₁] at h3
      exact h3
    have hid : (c₁ * d) * (c₁ * d) = (d * c₁ * d⁻¹ * c₁⁻¹) * (c₁ * c₁) * (d * d) := by
      calc (c₁ * d) * (c₁ * d) = c₁ * (d * c₁) * d := by group
        _ = c₁ * ((d * c₁ * d⁻¹ * c₁⁻¹) * c₁ * d) * d := by group
        _ = (c₁ * (d * c₁ * d⁻¹ * c₁⁻¹)) * c₁ * d * d := by group
        _ = ((d * c₁ * d⁻¹ * c₁⁻¹) * c₁) * c₁ * d * d := by rw [hkc]
        _ = (d * c₁ * d⁻¹ * c₁⁻¹) * (c₁ * c₁) * (d * d) := by group
    have h4 := mul_right_cancel (hid.symm.trans h1)
    have hK := mul_eq_right.mp h4
    calc c₁ * d = (d * c₁ * d⁻¹ * c₁⁻¹)⁻¹ * (d * c₁) := by group
      _ = d * c₁ := by rw [hK]; group
  have hAH₁ : A ≤ centralizer ({c₁} : Set G) ⊓ C := fun a ha =>
    ⟨mem_centralizer_iff.2 fun x hx => by
        rw [Set.mem_singleton_iff.1 hx]; exact h.cA c₁ hc₁ a ha, h.AC ha⟩
  have hc₁C : ∀ d ∈ C, c₁ * d = d * c₁ := by
    have key := gen_lemma h hgen hAH₁ inf_le_right fun d hd hx hy =>
      ⟨mem_centralizer_iff.2 fun x hx' => by
        rw [Set.mem_singleton_iff.1 hx']; exact hcomm₁ d hd hx hy, hd⟩
    intro d hd
    exact mem_centralizer_iff.1 (key d hd).1 c₁ rfl
  have hconjC : ∀ n ∈ egNL L A, ∀ d ∈ C, (n * c₁ * n⁻¹) * d = d * (n * c₁ * n⁻¹) := by
    intro n hn d hd
    have hd' : n⁻¹ * d * n ∈ C := by
      simpa using h.CN n⁻¹ ((egNL L A).inv_mem hn) d hd
    have h1 := hc₁C _ hd'
    calc (n * c₁ * n⁻¹) * d = n * (c₁ * (n⁻¹ * d * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * d * n) * c₁) * n⁻¹ := by rw [h1]
      _ = d * (n * c₁ * n⁻¹) := by group
  have hcentral : ∀ c ∈ C, quadTau z c ∈ egOrb L A a₁ → ∀ d ∈ C, c * d = d * c := by
    intro c hc hx d hd
    obtain ⟨n, hn, hnx⟩ := hx
    have hnc : n * c₁ * n⁻¹ ∈ C := h.CN n hn c₁ hc₁
    have h1 : quadTau z (n * c₁ * n⁻¹) = quadTau z c := by rw [tau_conj h hn, hτ₁, hnx]
    have ha : (n * c₁ * n⁻¹)⁻¹ * c ∈ A := inv_mul_mem_of_tau_eq h hnc hc h1
    have hca : c = (n * c₁ * n⁻¹) * ((n * c₁ * n⁻¹)⁻¹ * c) := by group
    have hfin : ∀ c' a : G, (∀ d ∈ C, c' * d = d * c') → a ∈ A → c = c' * a → c * d = d * c := by
      intro c' a h1 ha hca
      rw [hca]
      calc c' * a * d = c' * (a * d) := by group
        _ = c' * (d * a) := by rw [← h.cA d hd a ha]
        _ = (c' * d) * a := by group
        _ = (d * c') * a := by rw [h1 d hd]
        _ = d * (c' * a) := by group
    exact hfin (n * c₁ * n⁻¹) _ (hconjC n hn) ha hca
  have habel : ∀ c ∈ C, ∀ d ∈ C, c * d = d * c := by
    have hAH₂ : A ≤ centralizer (C : Set G) ⊓ C := fun a ha =>
      ⟨mem_centralizer_iff.2 fun d hd => h.cA d hd a ha, h.AC ha⟩
    have key := gen_lemma h hgen hAH₂ inf_le_right fun d hd hx _ =>
      ⟨mem_centralizer_iff.2 fun x hx' => (hcentral d hd hx x hx').symm, hd⟩
    intro c hc d hd
    exact (mem_centralizer_iff.1 (key c hc).1 d hd).symm
  refine ⟨habel, ?_⟩
  obtain ⟨H₃, hH₃⟩ : ∃ H : Subgroup G, ∀ x, x ∈ H ↔ x ∈ C ∧ x * x = e (quadTau z x) :=
    ⟨{ carrier := {x | x ∈ C ∧ x * x = e (quadTau z x)}
       mul_mem' := by
         rintro x y ⟨hx, hx2⟩ ⟨hy, hy2⟩
         refine ⟨C.mul_mem hx hy, ?_⟩
         have hxy := habel x hx y hy
         calc x * y * (x * y) = x * (y * x) * y := by group
           _ = x * (x * y) * y := by rw [hxy]
           _ = (x * x) * (y * y) := by group
           _ = e (quadTau z x) * e (quadTau z y) := by rw [hx2, hy2]
           _ = e (quadTau z (x * y)) := by rw [← map_mul, ← tau_mul h hx hy]
       one_mem' := ⟨C.one_mem, by simp [quadTau_one]⟩
       inv_mem' := by
         rintro x ⟨hx, hx2⟩
         refine ⟨C.inv_mem hx, ?_⟩
         calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
           _ = (e (quadTau z x))⁻¹ := by rw [hx2]
           _ = e (quadTau z x⁻¹) := by rw [tau_inv h hx, map_inv] }, fun x => Iff.rfl⟩
  have key := gen_lemma h hgen (H := H₃)
    (fun a ha => (hH₃ a).2 ⟨h.AC ha, by
      rw [h.Aab.2 a ha, tau_eq_one_of_mem h hfix ha, map_one]⟩)
    (fun x hx => ((hH₃ x).1 hx).1)
    (fun d hd hx _ => (hH₃ d).2 ⟨hd, horb d hd hx⟩)
  exact fun c hc => ((hH₃ c).1 (key c hc)).2

theorem quad_prop14 {G : Type} [Group G] [Finite G] {L A C : Subgroup G} {z a₁ : G}
    (hAC : A ≤ C) (hAab : EgElemAb A) (hcA : ∀ c ∈ C, ∀ a ∈ A, c * a = a * c)
    (hsq : ∀ c ∈ C, c * c ∈ A) (hcomm : ∀ c ∈ C, ∀ d ∈ C, c * d * c⁻¹ * d⁻¹ ∈ A)
    (hτA : ∀ c ∈ C, z * c * z⁻¹ * c⁻¹ ∈ A)
    (hker : ∀ c ∈ C, z * c = c * z → c ∈ A)
    (hsurj : ∀ a ∈ A, ∃ c ∈ C, z * c * z⁻¹ * c⁻¹ = a)
    (hN : ∀ n ∈ egNL L A, n * z = z * n ∧ ∀ c ∈ C, n * c * n⁻¹ ∈ C)
    (ha₁ : a₁ ∈ A) (ha₁1 : a₁ ≠ 1)
    (hgen : Subgroup.closure {x : G | x ∈ A ∧ x ∈ egOrb L A a₁ ∧ a₁ * x ∈ egOrb L A a₁} = A)
    (hfix : ∀ x ∈ A, x ≠ 1 → ∀ w ∈ A,
      (∀ n ∈ egNL L A, n * x * n⁻¹ = x → n * w * n⁻¹ = w) → w = 1 ∨ w = x) :
    (∀ c ∈ C, ∀ d ∈ C, c * d = d * c) ∧
      ((∀ c ∈ C, c * c = 1) ∨ ∀ c ∈ C, z * c * z⁻¹ = c⁻¹) := by
  have h : QuadHyp L A C z :=
    { AC := hAC, Aab := hAab, cA := hcA, sq := hsq, comm := hcomm, tauA := hτA, ker := hker,
      surj := hsurj, zN := fun n hn => (hN n hn).1, CN := fun n hn => (hN n hn).2 }
  obtain ⟨c₁, hc₁, hτ₁⟩ := hsurj a₁ ha₁
  have hτ₁' : quadTau z c₁ = a₁ := hτ₁
  have hne : quadTau z c₁ ≠ 1 := by rw [hτ₁']; exact ha₁1
  rcases sq_dichotomy h hfix hc₁ hne with h1 | h1
  · obtain ⟨hab, hsq'⟩ := quad_main h 1 (fun n _ x => by simp) hfix hgen hc₁ hτ₁'
      (by simpa using h1)
    exact ⟨hab, Or.inl fun c hc => by simpa using hsq' c hc⟩
  · rw [hτ₁'] at h1
    obtain ⟨hab, hsq'⟩ := quad_main h (MonoidHom.id G) (fun n _ x => by simp) hfix hgen hc₁ hτ₁'
      (by simpa using h1)
    refine ⟨hab, Or.inr fun c hc => ?_⟩
    have h2 : c * c = z * c * z⁻¹ * c⁻¹ := by simpa [quadTau] using hsq' c hc
    have h3 : (c * c) * (c * c) = 1 := hAab.2 _ (hsq c hc)
    calc z * c * z⁻¹ = (z * c * z⁻¹ * c⁻¹) * c := by group
      _ = (c * c) * c := by rw [← h2]
      _ = c⁻¹ * ((c * c) * (c * c)) := by group
      _ = c⁻¹ := by rw [h3, mul_one]

end CFSG.EvenSporadicStandard.M24Std
