module

public import CFSG.LargeExtraspecial.DWSm77Transfer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith

namespace Sm77

section Conj

variable {G : Type*} [Group G]

theorem mem_map_conj {H : Subgroup G} {g y : G} :
    y ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ H := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    simpa [mul_assoc] using hh
  · intro hy
    exact ⟨g⁻¹ * y * g, hy, by simp [mul_assoc]⟩

theorem conj_mem_map_conj {H : Subgroup G} (g : G) {h : G} (hh : h ∈ H) :
    g * h * g⁻¹ ∈ H.map (MulAut.conj g).toMonoidHom :=
  ⟨h, hh, rfl⟩

theorem mem_conjBy_M_iff (S : Setting G) {g m : G} :
    m ∈ (S.conjBy g).M ↔ g⁻¹ * m * g ∈ S.M := by
  rw [(S.conjBy g).mem_M_iff, S.mem_M_iff, Setting.conjBy_z]
  constructor
  · intro h
    calc g⁻¹ * m * g * S.z = g⁻¹ * (m * (g * S.z * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * S.z * g⁻¹ * m) * g := by rw [h]
      _ = S.z * (g⁻¹ * m * g) := by group
  · intro h
    calc m * (g * S.z * g⁻¹) = g * (g⁻¹ * m * g * S.z) * g⁻¹ := by group
      _ = g * (S.z * (g⁻¹ * m * g)) * g⁻¹ := by rw [h]
      _ = g * S.z * g⁻¹ * m := by group

theorem mem_conjBy_QG_iff [Finite G] (S : Setting G) {g x : G} :
    x ∈ (S.conjBy g).QG ↔ g⁻¹ * x * g ∈ S.QG := by
  rw [show (S.conjBy g).QG = S.Qa g from rfl, S.Qa_eq_map, mem_map_conj]

theorem mem_normalizer_of_conj_mem {H : Subgroup G} {m : G} (h : ∀ x ∈ H, m * x * m⁻¹ ∈ H)
    (h' : ∀ x ∈ H, m⁻¹ * x * m⁻¹⁻¹ ∈ H) : m ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have := h' _ hx
  simpa [mul_assoc] using this

theorem cover_of_not_commute [Finite G] (S : Setting G) {F : Subgroup G} (hFQ : F ≤ S.QG)
    {e c : G} (he : e ∈ S.QG) (hcF : c ∈ F) (hce : c * e ≠ e * c) :
    ∀ f ∈ F, f ∈ F ⊓ centralizer ({e} : Set G) ∨ c⁻¹ * f ∈ F ⊓ centralizer ({e} : Set G) := by
  intro f hf
  have hfQ := hFQ hf
  have hcQ := hFQ hcF
  by_cases hfe : f * e = e * f
  · exact Or.inl ⟨hf, mem_centralizer_singleton_iff.mpr hfe⟩
  right
  refine ⟨F.mul_mem (F.inv_mem hcF) hf, mem_centralizer_singleton_iff.mpr ?_⟩
  have h1 := (S.polar_cl_eq_one_iff hcQ he).mpr hce
  have h2 := (S.polar_cl_eq_one_iff hfQ he).mpr hfe
  have h3 : polar S.q (S.cl (c⁻¹ * f)) (S.cl e) = 0 := by
    rw [S.cl_mul (S.QG.inv_mem hcQ) hfQ, S.cl_inv hcQ, polar_add_left, h1, h2]
    decide
  exact (S.polar_cl_eq_zero_iff (S.QG.mul_mem (S.QG.inv_mem hcQ) hfQ) he).mp h3

end Conj

structure Decomp {G : Type*} [Group G] (S : Setting G) where
  A : Subgroup G
  B : Subgroup G
  A_le : A ≤ S.QG
  B_le : B ≤ S.QG
  conj_A : ∀ m ∈ S.M, ∀ a ∈ A, m * a * m⁻¹ ∈ A
  conj_B : ∀ m ∈ S.M, ∀ b ∈ B, m * b * m⁻¹ ∈ B
  comm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a
  mul : ∀ x ∈ S.QG, ∃ a ∈ A, ∃ b ∈ B, x = a * b
  inter : ∀ x ∈ A, x ∈ B → x = 1 ∨ x = S.z
  z_mem_A : S.z ∈ A
  z_mem_B : S.z ∈ B
  ne_A : ∃ a ∈ A, a ≠ 1 ∧ a ≠ S.z
  ne_B : ∃ b ∈ B, b ≠ 1 ∧ b ≠ S.z

namespace Decomp

variable {G : Type*} [Group G] {S : Setting G} (D : Decomp S)

@[expose] def swap : Decomp S where
  A := D.B
  B := D.A
  A_le := D.B_le
  B_le := D.A_le
  conj_A := D.conj_B
  conj_B := D.conj_A
  comm := fun b hb a ha => (D.comm a ha b hb).symm
  mul := fun x hx => by
    obtain ⟨a, ha, b, hb, rfl⟩ := D.mul x hx
    exact ⟨b, hb, a, ha, D.comm a ha b hb⟩
  inter := fun x hb ha => D.inter x ha hb
  z_mem_A := D.z_mem_B
  z_mem_B := D.z_mem_A
  ne_A := D.ne_B
  ne_B := D.ne_A

@[simp] theorem swap_A : D.swap.A = D.B := rfl

@[simp] theorem swap_B : D.swap.B = D.A := rfl

@[expose] noncomputable def conj [Finite G] (g : G) : Decomp (S.conjBy g) where
  A := D.A.map (MulAut.conj g).toMonoidHom
  B := D.B.map (MulAut.conj g).toMonoidHom
  A_le := fun x hx => (mem_conjBy_QG_iff S).mpr (D.A_le (mem_map_conj.mp hx))
  B_le := fun x hx => (mem_conjBy_QG_iff S).mpr (D.B_le (mem_map_conj.mp hx))
  conj_A := fun m hm a ha => by
    rw [mem_map_conj] at ha ⊢
    have h := D.conj_A _ ((mem_conjBy_M_iff S).mp hm) _ ha
    convert h using 1
    group
  conj_B := fun m hm b hb => by
    rw [mem_map_conj] at hb ⊢
    have h := D.conj_B _ ((mem_conjBy_M_iff S).mp hm) _ hb
    convert h using 1
    group
  comm := fun a ha b hb => by
    have h := D.comm _ (mem_map_conj.mp ha) _ (mem_map_conj.mp hb)
    calc a * b = g * (g⁻¹ * a * g * (g⁻¹ * b * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * b * g * (g⁻¹ * a * g)) * g⁻¹ := by rw [h]
      _ = b * a := by group
  mul := fun x hx => by
    obtain ⟨a, ha, b, hb, h⟩ := D.mul _ ((mem_conjBy_QG_iff S).mp hx)
    refine ⟨g * a * g⁻¹, conj_mem_map_conj g ha, g * b * g⁻¹, conj_mem_map_conj g hb, ?_⟩
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = g * a * g⁻¹ * (g * b * g⁻¹) := by rw [h]; group
  inter := fun x ha hb => by
    rcases D.inter _ (mem_map_conj.mp ha) (mem_map_conj.mp hb) with h | h
    · left
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
    · right
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = g * S.z * g⁻¹ := by rw [h]
  z_mem_A := conj_mem_map_conj g D.z_mem_A
  z_mem_B := conj_mem_map_conj g D.z_mem_B
  ne_A := by
    obtain ⟨a, ha, h1, hz⟩ := D.ne_A
    refine ⟨g * a * g⁻¹, conj_mem_map_conj g ha, fun h => h1 ?_, fun h => hz ?_⟩
    · calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    · calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
        _ = S.z := by rw [h, Setting.conjBy_z]; group
  ne_B := by
    obtain ⟨b, hb, h1, hz⟩ := D.ne_B
    refine ⟨g * b * g⁻¹, conj_mem_map_conj g hb, fun h => h1 ?_, fun h => hz ?_⟩
    · calc b = g⁻¹ * (g * b * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    · calc b = g⁻¹ * (g * b * g⁻¹) * g := by group
        _ = S.z := by rw [h, Setting.conjBy_z]; group

theorem mem_conj_A [Finite G] {g y : G} : y ∈ (D.conj g).A ↔ g⁻¹ * y * g ∈ D.A :=
  mem_map_conj

theorem mem_conj_B [Finite G] {g y : G} : y ∈ (D.conj g).B ↔ g⁻¹ * y * g ∈ D.B :=
  mem_map_conj

theorem conj_A_eq [Finite G] {g h : G} (hgh : g * S.z * g⁻¹ = h * S.z * h⁻¹) :
    (D.conj g).A = (D.conj h).A := by
  have hM : h⁻¹ * g ∈ S.M := by
    rw [S.mem_M_iff]
    calc h⁻¹ * g * S.z = h⁻¹ * (g * S.z * g⁻¹) * g := by group
      _ = h⁻¹ * (h * S.z * h⁻¹) * g := by rw [hgh]
      _ = S.z * (h⁻¹ * g) := by group
  ext y
  rw [mem_conj_A, mem_conj_A]
  constructor
  · intro hy
    have := D.conj_A _ hM _ hy
    convert this using 1
    group
  · intro hy
    have := D.conj_A _ (S.M.inv_mem hM) _ hy
    convert this using 1
    group

theorem conj_B_eq [Finite G] {g h : G} (hgh : g * S.z * g⁻¹ = h * S.z * h⁻¹) :
    (D.conj g).B = (D.conj h).B :=
  D.swap.conj_A_eq hgh

theorem card_conj_A [Finite G] (g : G) : Nat.card (D.conj g).A = Nat.card D.A :=
  card_map_of_injective (MulAut.conj g).injective

theorem card_conj_B [Finite G] (g : G) : Nat.card (D.conj g).B = Nat.card D.B :=
  card_map_of_injective (MulAut.conj g).injective

theorem exists_not_commute_B {b : G} (hb : b ∈ D.B) (h1 : b ≠ 1) (hz : b ≠ S.z) :
    ∃ b' ∈ D.B, b * b' ≠ b' * b := by
  by_contra h
  push Not at h
  have hall : ∀ y ∈ S.QG, b * y = y * b := fun y hy => by
    obtain ⟨a, ha, b', hb', rfl⟩ := D.mul y hy
    calc b * (a * b') = a * (b * b') := by rw [← mul_assoc, ← D.comm a ha b hb, mul_assoc]
      _ = a * (b' * b) := by rw [h b' hb']
      _ = a * b' * b := by rw [mul_assoc]
  rcases S.eq_one_or_z_of_commute (D.B_le hb) hall with h' | h'
  exacts [h1 h', hz h']

theorem exists_not_commute_A {a : G} (ha : a ∈ D.A) (h1 : a ≠ 1) (hz : a ≠ S.z) :
    ∃ a' ∈ D.A, a * a' ≠ a' * a :=
  D.swap.exists_not_commute_B ha h1 hz

theorem mem_A_of_commute {x : G} (hx : x ∈ S.QG) (h : ∀ b ∈ D.B, x * b = b * x) : x ∈ D.A := by
  obtain ⟨a, ha, b, hb, rfl⟩ := D.mul x hx
  have hbB : ∀ b' ∈ D.B, b * b' = b' * b := fun b' hb' => by
    have e := h b' hb'
    have e' : a * (b * b') = a * (b' * b) := by
      calc a * (b * b') = a * b * b' := by rw [mul_assoc]
        _ = b' * (a * b) := e
        _ = a * (b' * b) := by rw [← mul_assoc, ← D.comm a ha b' hb', mul_assoc]
    exact mul_left_cancel e'
  by_cases hb1 : b = 1
  · rw [hb1, mul_one]
    exact ha
  by_cases hbz : b = S.z
  · rw [hbz]
    exact D.A.mul_mem ha D.z_mem_A
  obtain ⟨b', hb', hne⟩ := D.exists_not_commute_B hb hb1 hbz
  exact absurd (hbB b' hb') hne

theorem exists_conj_eq_mul_z_A {a : G} (ha : a ∈ D.A) (h1 : a ≠ 1) (hz : a ≠ S.z) :
    ∃ a' ∈ D.A, a' * a * a'⁻¹ = a * S.z := by
  obtain ⟨a', ha', hne⟩ := D.exists_not_commute_A ha h1 hz
  refine ⟨a', ha', ?_⟩
  rcases S.mul_comm_or (D.A_le ha') (D.A_le ha) with h | h
  · exact absurd h.symm hne
  · calc a' * a * a'⁻¹ = S.z * (a * a') * a'⁻¹ := by rw [h]
      _ = S.z * a := by group
      _ = a * S.z := (S.z_comm (S.QG_le_M (D.A_le ha))).symm

theorem z_mem_of_normalized {N : Subgroup G} (hN : ∀ b ∈ D.B, ∀ t ∈ N, b * t * b⁻¹ ∈ N)
    {t : G} (htN : t ∈ N) (htB : t ∈ D.B) (ht1 : t ≠ 1) : S.z ∈ N := by
  by_cases htz : t = S.z
  · exact htz ▸ htN
  obtain ⟨b, hb, hne⟩ := D.exists_not_commute_B htB ht1 htz
  have hmem : b * t * b⁻¹ * t⁻¹ ∈ N := N.mul_mem (hN b hb t htN) (N.inv_mem htN)
  rcases S.commutator_eq_one_or_z (D.B_le hb) (D.B_le htB) with h | h
  · exfalso
    apply hne
    calc t * b = b * t * b⁻¹ * t⁻¹ * (t * b) := by rw [h, one_mul]
      _ = b * t := by group
  · exact h ▸ hmem

theorem exists_commutator_eq_z_A : ∃ t₁ ∈ D.A, ∃ t₂ ∈ D.A, t₁ * t₂ * t₁⁻¹ * t₂⁻¹ = S.z := by
  obtain ⟨a, ha, h1, hz⟩ := D.ne_A
  obtain ⟨a', ha', hne⟩ := D.exists_not_commute_A ha h1 hz
  refine ⟨a, ha, a', ha', ?_⟩
  rcases S.commutator_eq_one_or_z (D.A_le ha) (D.A_le ha') with h | h
  · exfalso
    apply hne
    calc a * a' = a * a' * a⁻¹ * a'⁻¹ * (a' * a) := by group
      _ = a' * a := by rw [h, one_mul]
  · exact h

theorem exists_sq_eq_z_A [Finite G] : ∃ k ∈ D.A, k ^ 2 = S.z := by
  obtain ⟨a, ha, h1, hz⟩ := D.ne_A
  obtain ⟨a', ha', hne⟩ := D.exists_not_commute_A ha h1 hz
  have haQ := D.A_le ha
  have ha'Q := D.A_le ha'
  by_contra h
  push Not at h
  have hsq : ∀ k ∈ D.A, k ∈ S.QG → S.q (S.cl k) = 0 := fun k hk hkQ =>
    (S.q_cl_eq_zero_iff hkQ).mpr ((S.sq_eq_one_or_z hkQ).resolve_right (h k hk))
  have e := Sm77.q_add S (S.cl a) (S.cl a')
  rw [← S.cl_mul haQ ha'Q, hsq _ (D.A.mul_mem ha ha') (S.QG.mul_mem haQ ha'Q), hsq a ha haQ,
    hsq a' ha' ha'Q, (S.polar_cl_eq_one_iff haQ ha'Q).mpr hne] at e
  exact absurd e (by decide)

theorem polar_A_B [Finite G] {u v : S.Qt} (hu : u ∈ S.clSub D.A) (hv : v ∈ S.clSub D.B) :
    polar S.q u v = 0 := by
  obtain ⟨a, ha, haQ, rfl⟩ := S.mem_clSub_iff.mp hu
  obtain ⟨b, hb, hbQ, rfl⟩ := S.mem_clSub_iff.mp hv
  exact (S.polar_cl_eq_zero_iff haQ hbQ).mpr (D.comm a ha b hb)

theorem clSub_inf : S.clSub D.A ⊓ S.clSub D.B = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨a, ha, haQ, rfl⟩ := S.mem_clSub_iff.mp hv.1
  obtain ⟨b, hb, hbQ, hab⟩ := S.mem_clSub_iff.mp hv.2
  have haB : a ∈ D.B := by
    rcases (S.cl_eq_cl_iff hbQ haQ).mp hab with h | h
    · exact h ▸ hb
    · exact h ▸ D.B.mul_mem hb D.z_mem_B
  rw [Submodule.mem_bot, S.cl_eq_zero_iff haQ]
  exact D.inter a ha haB

theorem clSub_sup : S.clSub D.A ⊔ S.clSub D.B = ⊤ := by
  rw [eq_top_iff]
  intro v _
  obtain ⟨x, hx, rfl⟩ := S.exists_cl v
  obtain ⟨a, ha, b, hb, rfl⟩ := D.mul x hx
  rw [S.cl_mul (D.A_le ha) (D.B_le hb)]
  exact Submodule.add_mem_sup (S.cl_mem_clSub ha (D.A_le ha)) (S.cl_mem_clSub hb (D.B_le hb))

theorem finrank_add [Finite G] :
    finrank (ZMod 2) (S.clSub D.A) + finrank (ZMod 2) (S.clSub D.B) = 2 * S.width := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (S.clSub D.A) (S.clSub D.B)
  rw [D.clSub_sup, D.clSub_inf, finrank_bot, add_zero, finrank_top,
    S.finrank_Qt_eq_two_mul_width] at h
  exact h.symm

theorem card_A [Finite G] : Nat.card D.A = 2 * 2 ^ finrank (ZMod 2) (S.clSub D.A) := by
  rw [← S.card_submodule, ← S.card_clPre, S.clPre_clSub D.A_le D.z_mem_A]

theorem card_B [Finite G] : Nat.card D.B = 2 * 2 ^ finrank (ZMod 2) (S.clSub D.B) :=
  D.swap.card_A

theorem card_le_eight_of_commute [Finite G] {X : Subgroup G} (hXA : X ≤ D.A) {c : G}
    (hcA : c ∈ D.A) (hcov : ∀ f ∈ D.A, f ∈ X ∨ c⁻¹ * f ∈ X)
    (hX : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) : Nat.card D.A ≤ 8 := by
  set Xt := S.clSub X with hXt
  have hXQ : X ≤ S.QG := hXA.trans D.A_le
  have hXAt : Xt ≤ S.clSub D.A := S.clSub_mono hXA
  have hiso : ∀ u ∈ Xt, ∀ v ∈ Xt, polar S.q u v = 0 := fun u hu v hv => by
    obtain ⟨x, hx, hxQ, rfl⟩ := S.mem_clSub_iff.mp hu
    obtain ⟨y, hy, hyQ, rfl⟩ := S.mem_clSub_iff.mp hv
    exact (S.polar_cl_eq_zero_iff hxQ hyQ).mpr (hX x hx y hy)
  have hU : Xt ⊔ S.clSub D.B ≤ LinearMap.BilinForm.orthogonal S.q.polarBilin Xt := by
    intro w hw
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hw
    rw [polarBilin_apply_apply, polar_add_right, hiso u hu x hx, D.polar_A_B (hXAt hu) hy,
      add_zero]
  have hinf : Xt ⊓ S.clSub D.B = ⊥ :=
    eq_bot_iff.mpr (le_trans (inf_le_inf_right _ hXAt) D.clSub_inf.le)
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq Xt (S.clSub D.B)
  rw [hinf, finrank_bot, add_zero] at h1
  have h2 := Submodule.finrank_mono hU
  have h3 := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate Xt
  rw [S.finrank_Qt_eq_two_mul_width] at h3
  have h4 := D.finrank_add
  have h5 := Submodule.finrank_le Xt
  rw [S.finrank_Qt_eq_two_mul_width] at h5
  have hcov' : S.clSub D.A ≤ Xt ⊔ (ZMod 2 ∙ S.cl c) := by
    intro v hv
    obtain ⟨a, ha, haQ, rfl⟩ := S.mem_clSub_iff.mp hv
    rcases hcov a ha with h | h
    · exact Submodule.mem_sup_left (S.cl_mem_clSub h haQ)
    · have e : S.cl a = S.cl c + S.cl (c⁻¹ * a) := by
        rw [← S.cl_mul (D.A_le hcA) (hXQ h)]
        congr 1
        group
      rw [e, add_comm]
      exact Submodule.add_mem_sup (S.cl_mem_clSub h (hXQ h)) (Submodule.mem_span_singleton_self _)
  have h6 := Submodule.finrank_mono hcov'
  have h7 := Submodule.finrank_add_le_finrank_add_finrank Xt (ZMod 2 ∙ S.cl c)
  have h8 : finrank (ZMod 2) (ZMod 2 ∙ S.cl c) ≤ 1 := by
    by_cases hc0 : S.cl c = 0
    · rw [hc0, Submodule.span_singleton_eq_bot.mpr rfl, finrank_bot]
      exact zero_le_one
    · rw [finrank_span_singleton hc0]
  have hdim : finrank (ZMod 2) (S.clSub D.A) ≤ 2 := by omega
  rw [D.card_A]
  calc 2 * 2 ^ finrank (ZMod 2) (S.clSub D.A) ≤ 2 * 2 ^ 2 :=
        Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by norm_num) hdim)
    _ = 8 := by norm_num

theorem exists_commutator_eq_z_of_cover [Finite G] {X : Subgroup G} (hXA : X ≤ D.A) {c : G}
    (hcA : c ∈ D.A) (hcov : ∀ f ∈ D.A, f ∈ X ∨ c⁻¹ * f ∈ X) (h8 : 8 < Nat.card D.A) :
    ∃ t₁ ∈ X, ∃ t₂ ∈ X, t₁ * t₂ * t₁⁻¹ * t₂⁻¹ = S.z := by
  by_contra h
  push Not at h
  refine absurd (D.card_le_eight_of_commute hXA hcA hcov fun x hx y hy => ?_) (not_le.mpr h8)
  rcases S.commutator_eq_one_or_z (D.A_le (hXA hx)) (D.A_le (hXA hy)) with e | e
  · calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = y * x := by rw [e, one_mul]
  · exact absurd e (h x hx y hy)

theorem exists_sq_eq_z_of_cover [Finite G] {X : Subgroup G} (hXA : X ≤ D.A) {c : G}
    (hcA : c ∈ D.A) (hcov : ∀ f ∈ D.A, f ∈ X ∨ c⁻¹ * f ∈ X) (h8 : 8 < Nat.card D.A) :
    ∃ k ∈ X, k ^ 2 = S.z := by
  by_contra h
  push Not at h
  have h1 : ∀ k ∈ X, k * k = 1 := fun k hk => by
    rw [← pow_two]
    exact (S.sq_eq_one_or_z (D.A_le (hXA hk))).resolve_right (h k hk)
  refine absurd (D.card_le_eight_of_commute hXA hcA hcov fun x hx y hy => ?_) (not_le.mpr h8)
  have hxy := h1 _ (X.mul_mem hx hy)
  calc x * y = x * y * (y * x) * (y * x) := by rw [mul_assoc (x * y), h1 _ (X.mul_mem hy hx),
        mul_one]
    _ = x * (y * y) * x * (y * x) := by group
    _ = y * x := by rw [h1 y hy, mul_one, h1 x hx, one_mul]

end Decomp

end Sm77

end CFSG.LargeExtraspecial.DW
