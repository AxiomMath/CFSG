module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR4Basic
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.SeitzReduction.EPilot

open Subgroup CFSG.EvenSmallLie CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)

section Elementary

variable {G : Type*} [Group G]

theorem mem_centralizer_singleton_comm {x a : G} :
    x ∈ centralizer ({a} : Set G) ↔ a ∈ centralizer ({x} : Set G) := by
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff, eq_comm]

theorem mem_centralizer_singleton_mul_inv {x a b : G} (ha : x ∈ centralizer ({a} : Set G))
    (hb : x ∈ centralizer ({b} : Set G)) : x ∈ centralizer ({a * b⁻¹} : Set G) :=
  mem_centralizer_singleton_comm.2 (mul_mem (mem_centralizer_singleton_comm.1 ha)
    (inv_mem (mem_centralizer_singleton_comm.1 hb)))

theorem mem_centralizer_singleton_inv_mul {x a b : G} (ha : x ∈ centralizer ({a} : Set G))
    (hb : x ∈ centralizer ({b} : Set G)) : x ∈ centralizer ({a⁻¹ * b} : Set G) :=
  mem_centralizer_singleton_comm.2 (mul_mem (inv_mem (mem_centralizer_singleton_comm.1 ha))
    (mem_centralizer_singleton_comm.1 hb))

theorem conjugate_le_centralizer_conj {L : Subgroup G} {t : G}
    (htC : t ∈ centralizer (L : Set G)) (g : G) :
    CFSG.conjugate L g ≤ centralizer ({g⁻¹ * t * g} : Set G) := by
  rintro _ ⟨l, hl, rfl⟩
  rw [mem_centralizer_singleton_iff]
  have h := mem_centralizer_iff.1 htC l hl
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  calc g⁻¹ * l * g * (g⁻¹ * t * g) = g⁻¹ * (l * t) * g := by group
    _ = g⁻¹ * (t * l) * g := by rw [h]
    _ = g⁻¹ * t * g * (g⁻¹ * l * g) := by group

theorem conj_mem_conjugate {L : Subgroup G} {l : G} (hl : l ∈ L) (g : G) :
    g⁻¹ * l * g ∈ CFSG.conjugate L g :=
  ⟨l, hl, by simp⟩

theorem inv_mul_mem_centralizer_of_conj_eq {H : Subgroup G} {t w' : G}
    (hact : ∀ l ∈ H, t * l * t⁻¹ = w' * l * w'⁻¹) : w'⁻¹ * t ∈ centralizer (H : Set G) := by
  rw [mem_centralizer_iff]
  intro l hl
  have h := hact l hl
  calc l * (w'⁻¹ * t) = w'⁻¹ * (w' * l * w'⁻¹) * t := by group
    _ = w'⁻¹ * (t * l * t⁻¹) * t := by rw [h]
    _ = w'⁻¹ * t * l := by group

theorem mem_centralizer_of_eq_or_eq_mul {L : Subgroup G} {t : G}
    (htC : t ∈ centralizer (L : Set G)) {w : G} (hwL : w ∈ L) {t' : G}
    (h : t' = w ∨ t' = t * w) : t ∈ centralizer ({t'} : Set G) := by
  have htw : t ∈ centralizer ({w} : Set G) :=
    mem_centralizer_singleton_comm.2 (le_centralizer_of_mem_centralizer htC hwL)
  rcases h with rfl | rfl
  · exact htw
  · exact mem_centralizer_singleton_comm.2 (mul_mem (mem_centralizer_singleton_iff.2 rfl)
      (mem_centralizer_singleton_comm.1 htw))

theorem conj_mul_inv_eq_or_eq_mul {L : Subgroup G} {t : G} (htC : t ∈ centralizer (L : Set G))
    {c : G} (hc : c ∈ L) {w g : G} (hg : g⁻¹ * t * g = w ∨ g⁻¹ * t * g = t * w) :
    (g * c⁻¹)⁻¹ * t * (g * c⁻¹) = c * w * c⁻¹ ∨
      (g * c⁻¹)⁻¹ * t * (g * c⁻¹) = t * (c * w * c⁻¹) := by
  have e : (g * c⁻¹)⁻¹ * t * (g * c⁻¹) = c * (g⁻¹ * t * g) * c⁻¹ := by group
  have htc : c * t = t * c := mem_centralizer_iff.1 htC c hc
  rcases hg with h | h
  · left
    rw [e, h]
  · right
    rw [e, h, ← mul_assoc, htc]
    group

theorem orderOf_eq_two_of_eq_or_eq_mul {t t' w' : G} (ht : orderOf t = 2) (ht' : orderOf t' = 2)
    (hcomm : t * t' = t' * t) (hne : t' ≠ t) (h : t = w' ∨ t = w' * t') : orderOf w' = 2 := by
  rcases h with rfl | h
  · exact ht
  · have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
    have ht'2 : t' * t' = 1 := by rw [← sq, ← ht', pow_orderOf_eq_one]
    have hw' : w' = t * t' := by
      rw [h, mul_assoc, ht'2, mul_one]
    rw [hw']
    exact F4Pilot.orderOf_mul_eq_two_of_commute ht2 ht'2 hcomm.symm hne

private theorem map_centralizer_singleton_of_injective' {A : Type*} [Group A] {φ : A →* G}
    (hφ : Function.Injective φ) (a : A) :
    (centralizer ({a} : Set A)).map φ = φ.range ⊓ centralizer ({φ a} : Set G) := by
  ext x
  constructor
  · rintro ⟨b, hb, rfl⟩
    refine mem_inf.2 ⟨⟨b, rfl⟩, ?_⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hb
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hb]
  · intro hx
    obtain ⟨⟨b, rfl⟩, hb⟩ := mem_inf.1 hx
    refine ⟨b, ?_, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul] at hb
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    exact hφ hb

end Elementary

section LemmaBStar

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem exists_involution_of_conj_mem_sup_zpowers {t : G} (ht : orderOf t = 2)
    (htC : t ∈ centralizer (L : Set G)) {g : G} (hne : g⁻¹ * t * g ≠ t)
    (hmem : g⁻¹ * t * g ∈ L ⊔ zpowers t) :
    ∃ y ∈ L, orderOf y = 2 ∧ (g⁻¹ * t * g = y ∨ g⁻¹ * t * g = t * y) := by
  obtain ⟨y, hyL, hy⟩ := F4Pilot.exists_eq_or_eq_mul_of_mem_sup_zpowers ht htC hmem
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hso : orderOf (g⁻¹ * t * g) = 2 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) t
    rw [MulAut.conj_apply, inv_inv] at h
    rw [h, ht]
  refine ⟨y, hyL, ?_, hy⟩
  rcases hy with h | h
  · rw [← h, hso]
  · have hs2 : (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1 := by
      rw [← sq, ← hso, pow_orderOf_eq_one]
    have hc : (g⁻¹ * t * g) * t = t * (g⁻¹ * t * g) := by
      rw [h, mul_assoc, ← mem_centralizer_iff.1 htC y hyL]
    have hy' : y = t * (g⁻¹ * t * g) := by
      rw [h, ← mul_assoc, ht2, one_mul]
    rw [hy']
    exact F4Pilot.orderOf_mul_eq_two_of_commute ht2 hs2 hc hne

theorem perfectCore_inf_centralizer_eq_of_inv_mul_mem (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {w g : G} (hg : g⁻¹ * t * g = w ∨ g⁻¹ * t * g = t * w) {w' : G}
    (hw' : w'⁻¹ * t ∈ centralizer (CFSG.conjugate L g : Set G)) :
    perfectCore (L ⊓ centralizer ({w} : Set G)) =
      perfectCore (CFSG.conjugate L g ⊓ centralizer ({w'} : Set G)) := by
  set Λ := perfectCore (L ⊓ centralizer ({w} : Set G)) with hΛdef
  set Λ' := perfectCore (CFSG.conjugate L g ⊓ centralizer ({w'} : Set G)) with hΛ'def
  have hLt : L ≤ centralizer ({t} : Set G) := le_centralizer_of_mem_centralizer htC
  have hL't' : CFSG.conjugate L g ≤ centralizer ({g⁻¹ * t * g} : Set G) :=
    conjugate_le_centralizer_conj htC g
  have hk : ∀ x ∈ CFSG.conjugate L g, x ∈ centralizer ({w'⁻¹ * t} : Set G) := fun x hx =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hw' x hx)
  have hΛp : ⁅Λ, Λ⁆ = Λ := perfectCore_perfect _
  have hΛL : Λ ≤ L := (perfectCore_le _).trans inf_le_left
  have hΛw : Λ ≤ centralizer ({w} : Set G) := (perfectCore_le _).trans inf_le_right
  have hΛt : Λ ≤ centralizer ({t} : Set G) := hΛL.trans hLt
  have hΛt' : Λ ≤ centralizer ({g⁻¹ * t * g} : Set G) := by
    rcases hg with h | h <;> rw [h]
    · exact hΛw
    · exact fun x hx => mem_centralizer_singleton_comm.2 (mul_mem
        (mem_centralizer_singleton_comm.1 (hΛt hx)) (mem_centralizer_singleton_comm.1 (hΛw hx)))
  have hΛL' : Λ ≤ CFSG.conjugate L g :=
    (std_perfect_le_inf_conjugate hset hOut htC ht g hΛp hΛt hΛt').trans inf_le_right
  have hΛw' : Λ ≤ centralizer ({w'} : Set G) := fun x hx => by
    have := mem_centralizer_singleton_mul_inv (hΛt hx) (hk x (hΛL' hx))
    simpa using this
  have h1 : Λ ≤ Λ' := le_perfectCore_of_perfect (le_inf hΛL' hΛw') hΛp
  have hΛ'p : ⁅Λ', Λ'⁆ = Λ' := perfectCore_perfect _
  have hΛ'L' : Λ' ≤ CFSG.conjugate L g := (perfectCore_le _).trans inf_le_left
  have hΛ'w' : Λ' ≤ centralizer ({w'} : Set G) := (perfectCore_le _).trans inf_le_right
  have hΛ't : Λ' ≤ centralizer ({t} : Set G) := fun x hx => by
    have := mem_centralizer_singleton_comm.2 (mul_mem
      (mem_centralizer_singleton_comm.1 (hΛ'w' hx))
      (mem_centralizer_singleton_comm.1 (hk x (hΛ'L' hx))))
    simpa using this
  have hΛ'L : Λ' ≤ L := std_perfect_le hset hOut htC ht hΛ'p hΛ't
  have hΛ't' : Λ' ≤ centralizer ({g⁻¹ * t * g} : Set G) := hΛ'L'.trans hL't'
  have hΛ'w : Λ' ≤ centralizer ({w} : Set G) := by
    rcases hg with h | h
    · rw [← h]
      exact hΛ't'
    · intro x hx
      have := mem_centralizer_singleton_inv_mul (hΛ't hx) (hΛ't' hx)
      rw [h] at this
      simpa using this
  have h2 : Λ' ≤ Λ := le_perfectCore_of_perfect (le_inf hΛ'L hΛ'w) hΛ'p
  exact le_antisymm h1 h2

omit [Finite G] in
theorem eq_or_eq_mul_conj_of_inner {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {w : G} (hwL : w ∈ L) {g : G} (hg : g⁻¹ * t * g = w ∨ g⁻¹ * t * g = t * w)
    {w' : G} (hw'L : w' ∈ CFSG.conjugate L g)
    (hact : ∀ l ∈ CFSG.conjugate L g, t * l * t⁻¹ = w' * l * w'⁻¹) :
    t = w' ∨ t = w' * (g⁻¹ * t * g) := by
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  have hw' : w'⁻¹ * t ∈ centralizer (CFSG.conjugate L g : Set G) :=
    inv_mul_mem_centralizer_of_conj_eq hact
  set t' := g⁻¹ * t * g with ht'def
  have htt' : t ∈ centralizer ({t'} : Set G) := mem_centralizer_of_eq_or_eq_mul htC hwL hg
  have hw't' : w' ∈ centralizer ({t'} : Set G) := conjugate_le_centralizer_conj htC g hw'L
  have hkt' : w'⁻¹ * t ∈ centralizer ({t'} : Set G) := mul_mem (inv_mem hw't') htt'
  set k := w'⁻¹ * t with hkdef
  have hxL : g * k * g⁻¹ ∈ centralizer (L : Set G) := by
    rw [mem_centralizer_iff]
    intro l hl
    have h := mem_centralizer_iff.1 hw' _ (conj_mem_conjugate hl g)
    calc l * (g * k * g⁻¹) = g * ((g⁻¹ * l * g) * k) * g⁻¹ := by group
      _ = g * (k * (g⁻¹ * l * g)) * g⁻¹ := by rw [h]
      _ = g * k * g⁻¹ * l := by group
  have hxt : g * k * g⁻¹ ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have h := mem_centralizer_singleton_iff.1 hkt'
    rw [ht'def] at h
    calc g * k * g⁻¹ * t = g * (k * (g⁻¹ * t * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * t * g) * k) * g⁻¹ := by rw [h]
      _ = t * (g * k * g⁻¹) := by group
  have hx : g * k * g⁻¹ ∈ zpowers t := hKt ▸ mem_inf.2 ⟨hxL, hxt⟩
  rcases F4Pilot.eq_one_or_eq_of_mem_zpowers ht hx with h | h
  · left
    have hk1 : k = 1 := by
      have : k = g⁻¹ * (g * k * g⁻¹) * g := by group
      rw [this, h]
      group
    calc t = w' * k := by rw [hkdef]; group
      _ = w' := by rw [hk1, mul_one]
  · right
    have hkt : k = t' := by
      have : k = g⁻¹ * (g * k * g⁻¹) * g := by group
      rw [this, h]
    calc t = w' * k := by rw [hkdef]; group
      _ = w' * t' := by rw [hkt]

omit [Finite G] in
theorem orderOf_eq_two_of_inner {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {w : G} (hwL : w ∈ L) {g : G} (hg : g⁻¹ * t * g = w ∨ g⁻¹ * t * g = t * w)
    (hne : g⁻¹ * t * g ≠ t) {w' : G} (hw'L : w' ∈ CFSG.conjugate L g)
    (hact : ∀ l ∈ CFSG.conjugate L g, t * l * t⁻¹ = w' * l * w'⁻¹) : orderOf w' = 2 := by
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  have ht' : orderOf (g⁻¹ * t * g) = 2 := by
    have h := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective t
    simpa [MulAut.conj_apply, ht] using h
  exact orderOf_eq_two_of_eq_or_eq_mul ht ht'
    (mem_centralizer_singleton_iff.1 (mem_centralizer_of_eq_or_eq_mul htC hwL hg)) hne
    (eq_or_eq_mul_conj_of_inner ht hKt hwL hg hw'L hact)

theorem perfectCore_inf_centralizer_eq_of_inner (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {w : G} (hwL : w ∈ L) {g : G} (hg : g⁻¹ * t * g = w ∨ g⁻¹ * t * g = t * w)
    {w' : G} (hw'L : w' ∈ CFSG.conjugate L g)
    (hact : ∀ l ∈ CFSG.conjugate L g, t * l * t⁻¹ = w' * l * w'⁻¹) :
    (t = w' ∨ t = w' * (g⁻¹ * t * g)) ∧
      perfectCore (L ⊓ centralizer ({w} : Set G)) =
        perfectCore (CFSG.conjugate L g ⊓ centralizer ({w'} : Set G)) := by
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  exact ⟨eq_or_eq_mul_conj_of_inner ht hKt hwL hg hw'L hact,
    perfectCore_inf_centralizer_eq_of_inv_mul_mem hset hOut htC ht hg
      (inv_mul_mem_centralizer_of_conj_eq hact)⟩

theorem map_perfectCore_centralizer_eq_of_inner (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {g : G} {C C' : Type*} [Group C] [Group C'] {φ : C →* G}
    {φ' : C' →* G} (hφ : Function.Injective φ) (hφr : φ.range = L)
    (hφ' : Function.Injective φ') (hφ'r : φ'.range = CFSG.conjugate L g) {y : C} {y' : C'}
    (hg : g⁻¹ * t * g = φ y ∨ g⁻¹ * t * g = t * φ y)
    (hact : ∀ l ∈ CFSG.conjugate L g, t * l * t⁻¹ = φ' y' * l * (φ' y')⁻¹) :
    (perfectCore (centralizer ({y} : Set C))).map φ =
      (perfectCore (centralizer ({y'} : Set C'))).map φ' := by
  have : Finite C := Finite.of_injective φ hφ
  have : Finite C' := Finite.of_injective φ' hφ'
  rw [CFSG.Quasithin.map_perfectCore, CFSG.Quasithin.map_perfectCore,
    map_centralizer_singleton_of_injective' hφ, map_centralizer_singleton_of_injective' hφ', hφr,
    hφ'r]
  exact perfectCore_inf_centralizer_eq_of_inv_mul_mem hset hOut htC ht hg
    (inv_mul_mem_centralizer_of_conj_eq hact)

end LemmaBStar

end CFSG.SeitzReduction.EPilot
