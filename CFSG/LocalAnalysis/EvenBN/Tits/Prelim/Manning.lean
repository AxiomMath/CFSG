module

public import CFSG.Holt.Fixed
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits

open MulAction Subgroup

section General

variable {G Ω Ψ : Type*} [Group G] [MulAction G Ω] [MulAction G Ψ]

theorem manning_mem_orbit_iff (α : Ω) (ψ : Ψ) (g g' : G) :
    g' • α ∈ orbit (stabilizer G ψ) (g • α) ↔
      g'⁻¹ • ψ ∈ orbit (stabilizer G α) (g⁻¹ • ψ) := by
  constructor
  · rintro ⟨⟨k, hk⟩, hkα⟩
    have hk' : k • ψ = ψ := hk
    have hkα' : k • g • α = g' • α := hkα
    refine ⟨⟨g'⁻¹ * k * g, ?_⟩, ?_⟩
    · rw [mem_stabilizer_iff, mul_smul, mul_smul, hkα', inv_smul_smul]
    · change (g'⁻¹ * k * g) • g⁻¹ • ψ = g'⁻¹ • ψ
      rw [mul_smul, mul_smul, smul_inv_smul, hk']
  · rintro ⟨⟨h, hh⟩, hhψ⟩
    have hh' : h • α = α := hh
    have hhψ' : h • g⁻¹ • ψ = g'⁻¹ • ψ := hhψ
    refine ⟨⟨g' * h * g⁻¹, ?_⟩, ?_⟩
    · rw [mem_stabilizer_iff, mul_smul, mul_smul, hhψ', smul_inv_smul]
    · change (g' * h * g⁻¹) • g • α = g' • α
      rw [mul_smul, mul_smul, inv_smul_smul, hh']

noncomputable def manningStabEquiv (α : Ω) (ψ : Ψ) (g : G) :
    stabilizer (stabilizer G ψ) (g • α) ≃ stabilizer (stabilizer G α) (g⁻¹ • ψ) where
  toFun k := ⟨⟨g⁻¹ * k.1.1 * g, by
      have h1 : k.1.1 • g • α = g • α := k.2
      rw [mem_stabilizer_iff, mul_smul, mul_smul, h1, inv_smul_smul]⟩, by
      have h2 : k.1.1 • ψ = ψ := k.1.2
      change (g⁻¹ * k.1.1 * g) • g⁻¹ • ψ = g⁻¹ • ψ
      rw [mul_smul, mul_smul, smul_inv_smul, h2]⟩
  invFun h := ⟨⟨g * h.1.1 * g⁻¹, by
      have h2 : h.1.1 • g⁻¹ • ψ = g⁻¹ • ψ := h.2
      rw [mem_stabilizer_iff, mul_smul, mul_smul, h2, smul_inv_smul]⟩, by
      have h1 : h.1.1 • α = α := h.1.2
      change (g * h.1.1 * g⁻¹) • g • α = g • α
      rw [mul_smul, mul_smul, inv_smul_smul, h1]⟩
  left_inv k := by
    apply Subtype.ext; apply Subtype.ext
    change g * (g⁻¹ * k.1.1 * g) * g⁻¹ = k.1.1
    group
  right_inv h := by
    apply Subtype.ext; apply Subtype.ext
    change g⁻¹ * (g * h.1.1 * g⁻¹) * g = h.1.1
    group

theorem manning_card_orbit_mul_card_stabilizer {M β : Type*} [Group M] [MulAction M β] [Finite M]
    (b : β) : Nat.card (orbit M b) * Nat.card (stabilizer M b) = Nat.card M := by
  rw [Nat.card_coe_set_eq, ← index_stabilizer, mul_comm]
  exact (stabilizer M b).card_mul_index

variable (r : Ω → Ψ → Prop)

theorem manning_transitive [IsPretransitive G Ω] (α : Ω) (ψ : Ψ)
    (hr : ∀ (g : G) (β : Ω) (φ : Ψ), r (g • β) (g • φ) ↔ r β φ)
    (hX : ∀ g : G, r α (g • ψ) → g • ψ ∈ orbit (stabilizer G α) ψ) {β : Ω} (hβ : r β ψ) :
    β ∈ orbit (stabilizer G ψ) α := by
  obtain ⟨g, rfl⟩ := exists_smul_eq G α β
  have h1 : r α (g⁻¹ • ψ) := by rw [← hr g⁻¹, inv_smul_smul] at hβ; exact hβ
  have h2 := hX g⁻¹ h1
  rw [show ψ = (1 : G)⁻¹ • ψ by simp] at h2
  have h3 := (manning_mem_orbit_iff α ψ 1 g).2 (by simpa using h2)
  simpa using h3

end General

section Setwise

open scoped Pointwise

variable {G Ω : Type*} [Group G] [MulAction G Ω]

private theorem map_conj_le_stabilizer_smul_iff (g : G) (β : Ω) (Y : Subgroup G) :
    Y.map (MulAut.conj g).toMonoidHom ≤ stabilizer G (g • β) ↔ Y ≤ stabilizer G β := by
  rw [stabilizer_smul_eq_stabilizer_map_conj]
  exact Subgroup.map_le_map_iff_of_injective (MulAut.conj g).injective

variable [IsPretransitive G Ω]

theorem manning_normalizer_transitive (α : Ω) {X : Subgroup G}
    (hX : ∀ g : G, X.map (MulAut.conj g).toMonoidHom ≤ stabilizer G α →
      ∃ h ∈ stabilizer G α, X.map (MulAut.conj h).toMonoidHom = X.map (MulAut.conj g).toMonoidHom)
    {β : Ω} (hβ : β ∈ CFSG.Holt.fixSet Ω X) : ∃ n ∈ normalizer (X : Set G), n • α = β := by
  let _ : MulAction G (Subgroup G) :=
    MulAction.compHom (Subgroup G) (MulAut.conj : G →* MulAut G)
  have hsmul : ∀ (g : G) (Y : Subgroup G), g • Y = Y.map (MulAut.conj g).toMonoidHom :=
    fun _ _ => rfl
  have hK : stabilizer G X = normalizer (X : Set G) := by
    ext g
    rw [mem_stabilizer_iff, hsmul]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.symm
  have hr : ∀ (g : G) (β : Ω) (Y : Subgroup G),
      g • Y ≤ stabilizer G (g • β) ↔ Y ≤ stabilizer G β := fun g β Y => by
    rw [hsmul]; exact map_conj_le_stabilizer_smul_iff g β Y
  have h := manning_transitive (fun β (Y : Subgroup G) => Y ≤ stabilizer G β) α X hr
    (fun g hg => by
      obtain ⟨h, hh, hhg⟩ := hX g (by rw [← hsmul]; exact hg)
      refine ⟨⟨h, hh⟩, ?_⟩
      change (h : G) • X = g • X
      rw [hsmul, hsmul, hhg])
    (show X ≤ stabilizer G β from hβ)
  rw [hK] at h
  obtain ⟨⟨n, hn⟩, hnα⟩ := h
  exact ⟨n, hn, hnα⟩

end Setwise

section Pointwise

variable {G Ω : Type*} [Group G] [MulAction G Ω]

private def PointMaps (X : Subgroup G) : Type _ := X → G

private instance pointConjAction (X : Subgroup G) : MulAction G (PointMaps X) where
  smul g φ := fun x => g * φ x * g⁻¹
  one_smul φ := funext fun x => by
    change (1 : G) * φ x * (1 : G)⁻¹ = φ x
    simp
  mul_smul g h φ := funext fun x => by
    change g * h * φ x * (g * h)⁻¹ = g * (h * φ x * h⁻¹) * g⁻¹
    group

private theorem pointMaps_stabilizer (X : Subgroup G) :
    stabilizer G (show PointMaps X from fun x => (x : G)) = centralizer (X : Set G) := by
  ext g
  rw [mem_stabilizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h x hx
    have := congrFun h ⟨x, hx⟩
    change g * x * g⁻¹ = x at this
    calc x * g = g * x * g⁻¹ * g := by rw [this]
      _ = g * x := by group
  · intro h
    funext x
    change g * x * g⁻¹ = x
    rw [← h x x.2]; group

private theorem pointMaps_rel (X : Subgroup G) (g : G) (β : Ω) (φ : PointMaps X) :
    (∀ x, (g • φ) x • (g • β) = g • β) ↔ ∀ x, φ x • β = β := by
  change (∀ x, (g * φ x * g⁻¹) • (g • β) = g • β) ↔ _
  simp only [mul_smul, inv_smul_smul, smul_left_cancel_iff]

variable [IsPretransitive G Ω]

theorem manning_centralizer_transitive (α : Ω) {X : Subgroup G}
    (hX : ∀ g : G, (∀ x ∈ X, g * x * g⁻¹ ∈ stabilizer G α) →
      ∃ h ∈ stabilizer G α, ∀ x ∈ X, h * x * h⁻¹ = g * x * g⁻¹)
    {β : Ω} (hβ : β ∈ CFSG.Holt.fixSet Ω X) : ∃ c ∈ centralizer (X : Set G), c • α = β := by
  let ι : PointMaps X := fun x => x
  have h := manning_transitive (fun β (φ : PointMaps X) => ∀ x, φ x • β = β) α ι
    (pointMaps_rel X) (fun g hg => by
      obtain ⟨h, hh, hhg⟩ := hX g fun x hx => hg ⟨x, hx⟩
      refine ⟨⟨h, hh⟩, funext fun x => ?_⟩
      exact hhg x x.2)
    (show ∀ x : X, ι x • β = β from fun x => hβ x x.2)
  rw [pointMaps_stabilizer X] at h
  obtain ⟨⟨c, hc⟩, hcα⟩ := h
  exact ⟨c, hc, hcα⟩

end Pointwise

section Conjugation

variable {G : Type*} [Group G]

private theorem commute_conj_iff (a b c : G) :
    c⁻¹ * a * c * b = b * (c⁻¹ * a * c) ↔ a * (c * b * c⁻¹) = c * b * c⁻¹ * a := by
  constructor
  · intro h
    calc a * (c * b * c⁻¹) = c * (c⁻¹ * a * c * b) * c⁻¹ := by group
      _ = c * (b * (c⁻¹ * a * c)) * c⁻¹ := by rw [h]
      _ = c * b * c⁻¹ * a := by group
  · intro h
    calc c⁻¹ * a * c * b = c⁻¹ * (a * (c * b * c⁻¹)) * c := by group
      _ = c⁻¹ * (c * b * c⁻¹ * a) * c := by rw [h]
      _ = b * (c⁻¹ * a * c) := by group

theorem smul_coset_centralizer_eq_iff (t y g : G) :
    y • ((g : G) : G ⧸ centralizer ({t} : Set G)) = (g : G ⧸ centralizer ({t} : Set G)) ↔
      y ∈ centralizer ({g * t * g⁻¹} : Set G) := by
  rw [MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq, mem_centralizer_singleton_iff,
    mem_centralizer_singleton_iff, show (y * g)⁻¹ * g = g⁻¹ * y⁻¹ * g by group, commute_conj_iff]
  constructor
  · intro h
    calc y * (g * t * g⁻¹) = y * ((g * t * g⁻¹) * y⁻¹) * y := by group
      _ = y * (y⁻¹ * (g * t * g⁻¹)) * y := by rw [h]
      _ = g * t * g⁻¹ * y := by group
  · intro h
    calc y⁻¹ * (g * t * g⁻¹) = y⁻¹ * ((g * t * g⁻¹) * y) * y⁻¹ := by group
      _ = y⁻¹ * (y * (g * t * g⁻¹)) * y⁻¹ := by rw [h]
      _ = g * t * g⁻¹ * y⁻¹ := by group

private theorem conj_eq_of_coset_eq {t c g : G}
    (h : ((c : G) : G ⧸ centralizer ({t} : Set G)) = (g : G ⧸ centralizer ({t} : Set G))) :
    c * t * c⁻¹ = g * t * g⁻¹ := by
  rw [QuotientGroup.eq, mem_centralizer_singleton_iff] at h
  calc c * t * c⁻¹ = c * (t * (c⁻¹ * g)) * (c⁻¹ * g)⁻¹ * c⁻¹ := by group
    _ = c * (c⁻¹ * g * t) * (c⁻¹ * g)⁻¹ * c⁻¹ := by rw [h]
    _ = g * t * g⁻¹ := by group

theorem manning_conj_centralizer {t x : G}
    (hfus : ∀ g : G, g * x * g⁻¹ ∈ centralizer ({t} : Set G) →
      ∃ h ∈ centralizer ({t} : Set G), h * x * h⁻¹ = g * x * g⁻¹)
    {g : G} (hg : g * t * g⁻¹ ∈ centralizer ({x} : Set G)) :
    ∃ c ∈ centralizer ({x} : Set G), c * t * c⁻¹ = g * t * g⁻¹ := by
  have hxT : x ∈ centralizer ({g * t * g⁻¹} : Set G) := by
    rw [mem_centralizer_singleton_iff] at hg ⊢
    exact hg.symm
  have hstab : stabilizer G ((1 : G) : G ⧸ centralizer ({t} : Set G)) =
      centralizer ({t} : Set G) := stabilizer_quotient _
  have hβ : ((g : G) : G ⧸ centralizer ({t} : Set G)) ∈
      CFSG.Holt.fixSet (G ⧸ centralizer ({t} : Set G)) (zpowers x) := by
    intro y hy
    rw [smul_coset_centralizer_eq_iff]
    exact (zpowers_le.mpr hxT) hy
  obtain ⟨c, hc, hcα⟩ := manning_centralizer_transitive
    ((1 : G) : G ⧸ centralizer ({t} : Set G)) (X := zpowers x) (fun g' hg' => by
      rw [hstab] at hg' ⊢
      obtain ⟨h, hh, hhx⟩ := hfus g' (hg' x (mem_zpowers x))
      refine ⟨h, hh, fun y hy => ?_⟩
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
      rw [← conj_zpow, hhx, conj_zpow]) hβ
  rw [zpowers_eq_closure, centralizer_closure] at hc
  refine ⟨c, hc, conj_eq_of_coset_eq ?_⟩
  rw [← hcα, MulAction.Quotient.smul_coe, smul_eq_mul, mul_one]

theorem manning_conj_normalizer {t : G} {X : Subgroup G}
    (hfus : ∀ g : G, X.map (MulAut.conj g).toMonoidHom ≤ centralizer ({t} : Set G) →
      ∃ h ∈ centralizer ({t} : Set G),
        X.map (MulAut.conj h).toMonoidHom = X.map (MulAut.conj g).toMonoidHom)
    {g : G} (hg : X ≤ centralizer ({g * t * g⁻¹} : Set G)) :
    ∃ n ∈ normalizer (X : Set G), n * t * n⁻¹ = g * t * g⁻¹ := by
  have hstab : stabilizer G ((1 : G) : G ⧸ centralizer ({t} : Set G)) =
      centralizer ({t} : Set G) := stabilizer_quotient _
  have hβ : ((g : G) : G ⧸ centralizer ({t} : Set G)) ∈
      CFSG.Holt.fixSet (G ⧸ centralizer ({t} : Set G)) X := by
    intro y hy
    rw [smul_coset_centralizer_eq_iff]
    exact hg hy
  obtain ⟨n, hn, hnα⟩ := manning_normalizer_transitive
    ((1 : G) : G ⧸ centralizer ({t} : Set G)) (X := X) (fun g' hg' => by
      rw [hstab] at hg' ⊢
      exact hfus g' hg') hβ
  refine ⟨n, hn, conj_eq_of_coset_eq ?_⟩
  rw [← hnα, MulAction.Quotient.smul_coe, smul_eq_mul, mul_one]

end Conjugation

end CFSG.LocalAnalysis.EvenBN.Tits
