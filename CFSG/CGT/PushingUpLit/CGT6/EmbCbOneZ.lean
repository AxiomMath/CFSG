module

public import CFSG.CGT.PushingUpLit.CGT6.EmbCbNatStab
import CFSG.CGT.PushingUpLit.CGT6.EmbCbPerm
import CFSG.CGT.PushingUpLit.CGT6.EmbAltCAp
public import CFSG.CGT.PushingUpLit.CGT6.EmbCbApi
public import CFSG.CGT.PushingUpLit.CGT6.EmbCbOneBase

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUp CFSG.Open Equiv

section PermLemmas

variable {k : ℕ}

theorem cbz_comm_swap {a b : Fin k} {ρ : Equiv.Perm (Fin k)} (ha : ρ a = a) (hb : ρ b = b) :
    ρ * Equiv.swap a b = Equiv.swap a b * ρ := by
  have h := Equiv.swap_apply_apply ρ a b
  rw [ha, hb] at h
  calc ρ * Equiv.swap a b = (ρ * Equiv.swap a b * ρ⁻¹) * ρ := by group
    _ = Equiv.swap a b * ρ := by rw [← h]

theorem cbz_mem_pair_of_comm {a b : Fin k} (hab : a ≠ b) {σ : Equiv.Perm (Fin k)}
    (h : σ * Equiv.swap a b = Equiv.swap a b * σ) : σ a = a ∨ σ a = b := by
  by_contra hcon
  push Not at hcon
  have h1 := congrArg (fun f : Equiv.Perm (Fin k) => f a) h
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] at h1
  rw [Equiv.swap_apply_of_ne_of_ne hcon.1 hcon.2] at h1
  exact hab (σ.injective h1.symm)

theorem cbz_swap_comm {a b p q : Fin k} (hpa : p ≠ a) (hpb : p ≠ b) (hqa : q ≠ a) (hqb : q ≠ b) :
    Equiv.swap a b * Equiv.swap p q = Equiv.swap p q * Equiv.swap a b := by
  have h := Equiv.swap_apply_apply (Equiv.swap a b) p q
  rw [Equiv.swap_apply_of_ne_of_ne hpa hpb, Equiv.swap_apply_of_ne_of_ne hqa hqb] at h
  calc Equiv.swap a b * Equiv.swap p q
      = (Equiv.swap a b * Equiv.swap p q * (Equiv.swap a b)⁻¹) * Equiv.swap a b := by group
    _ = Equiv.swap p q * Equiv.swap a b := by rw [← h]

theorem cbz_conj_fix {a b p q : Fin k} (hab : a ≠ b) (hpq : p ≠ q) {σ ρ : Equiv.Perm (Fin k)}
    (hτ : σ * Equiv.swap a b = Equiv.swap a b * σ)
    (hπ : σ * Equiv.swap p q = Equiv.swap p q * σ)
    (hρ : ∀ r ∈ ({a, b, p, q} : Finset (Fin k)), ρ r = r) :
    ∀ r ∈ ({a, b, p, q} : Finset (Fin k)), (σ * ρ * σ⁻¹) r = r := by
  classical
  have hτ' : σ⁻¹ * Equiv.swap a b = Equiv.swap a b * σ⁻¹ := (Commute.inv_left hτ : _)
  have hπ' : σ⁻¹ * Equiv.swap p q = Equiv.swap p q * σ⁻¹ := (Commute.inv_left hπ : _)
  have hτ'' : σ⁻¹ * Equiv.swap b a = Equiv.swap b a * σ⁻¹ := by rwa [Equiv.swap_comm b a]
  have hπ'' : σ⁻¹ * Equiv.swap q p = Equiv.swap q p * σ⁻¹ := by rwa [Equiv.swap_comm q p]
  have hmem : ∀ r ∈ ({a, b, p, q} : Finset (Fin k)), σ⁻¹ r ∈ ({a, b, p, q} : Finset (Fin k)) := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl
    · rcases cbz_mem_pair_of_comm hab hτ' with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases cbz_mem_pair_of_comm hab.symm hτ'' with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
    · rcases cbz_mem_pair_of_comm hpq hπ' with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
    · rcases cbz_mem_pair_of_comm hpq.symm hπ'' with h | h
      · exact Or.inr (Or.inr (Or.inr h))
      · exact Or.inr (Or.inr (Or.inl h))
  intro r hr
  have h1 := hρ _ (hmem r hr)
  simp only [Equiv.Perm.mul_apply]
  rw [h1]
  exact σ.apply_symm_apply r

end PermLemmas

section Sub

variable {V : Type} [CommGroup V] {Y X : Subgroup (MulAut V)} {t : MulAut V} {m : ℕ}

@[expose] def cbzSub (D : CbData Y t m X) (S : Subgroup (alternatingGroup (Fin (m + 2)))) :
    Subgroup (MulAut V) :=
  (S.comap D.θ.toMonoidHom).map X.subtype

theorem mem_cbzSub {D : CbData Y t m X} {S : Subgroup (alternatingGroup (Fin (m + 2)))}
    {x : MulAut V} : x ∈ cbzSub D S ↔ ∃ hx : x ∈ X, D.θ ⟨x, hx⟩ ∈ S := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem cbzSub_le (D : CbData Y t m X) (S : Subgroup (alternatingGroup (Fin (m + 2)))) :
    cbzSub D S ≤ X := fun _ hx => (mem_cbzSub.mp hx).1

theorem cbzSub_map_eq (D : CbData Y t m X) (S : Subgroup (alternatingGroup (Fin (m + 2)))) :
    ((cbzSub D S).subgroupOf X).map D.θ.toMonoidHom = S := by
  ext σ
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_cbzSub.mp hy).2
  · intro hσ
    obtain ⟨y, rfl⟩ := D.θ.surjective σ
    exact ⟨y, mem_cbzSub.mpr ⟨y.2, hσ⟩, rfl⟩

theorem cbz_even {k : ℕ} {a b p q : Fin k} (hab : a ≠ b) (hpq : p ≠ q) :
    Equiv.swap a b * Equiv.swap p q ∈ alternatingGroup (Fin k) := by
  rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap hab,
    Equiv.Perm.sign_swap hpq]
  decide

theorem cbz_eq_of_perm_eq {D : CbData Y t m X} {x y : MulAut V} (hx : x ∈ X) (hy : y ∈ X)
    (h : (D.θ ⟨x, hx⟩ : Equiv.Perm (Fin (m + 2))) = D.θ ⟨y, hy⟩) : x = y :=
  congrArg Subtype.val (D.θ.injective (Subtype.ext h))

section ZFacts

variable (D : CbData Y t m X) {p q : Fin (m + 2)} (hpa : p ≠ D.a) (hpb : p ≠ D.b)
  (hqa : q ≠ D.a) (hqb : q ≠ D.b) {z : ↥X}
  (hz : (D.θ z : Equiv.Perm (Fin (m + 2))) = Equiv.swap D.a D.b * Equiv.swap p q)

include hpa hpb hqa hqb hz in
theorem cbz_t_comm : t * (z : MulAut V) = z * t := by
  have hc := cbz_swap_comm hpa hpb hqa hqb
  have h2 : (D.θ ⟨t * (z : MulAut V) * t⁻¹, D.hn z z.2⟩ : Equiv.Perm (Fin (m + 2))) =
      D.θ ⟨(z : MulAut V), z.2⟩ := by
    rw [D.hconj z z.2]
    show Equiv.swap D.a D.b * (D.θ z : Equiv.Perm (Fin (m + 2))) * (Equiv.swap D.a D.b)⁻¹ = _
    rw [hz]
    calc Equiv.swap D.a D.b * (Equiv.swap D.a D.b * Equiv.swap p q) * (Equiv.swap D.a D.b)⁻¹
        = Equiv.swap D.a D.b * (Equiv.swap p q * Equiv.swap D.a D.b) *
            (Equiv.swap D.a D.b)⁻¹ := by rw [hc]
      _ = Equiv.swap D.a D.b * Equiv.swap p q := by group
  have h3 := cbz_eq_of_perm_eq (D := D) (D.hn z z.2) z.2 h2
  calc t * (z : MulAut V) = t * z * t⁻¹ * t := by group
    _ = z * t := by rw [h3]

include hpa hqa hz in
theorem cbz_ne_one : (z : MulAut V) ≠ 1 := by
  intro h
  have h1 : (D.θ z : Equiv.Perm (Fin (m + 2))) = 1 := by
    have : z = 1 := Subtype.ext h
    rw [this]
    simp
  rw [hz] at h1
  have h2 := congrArg (fun f : Equiv.Perm (Fin (m + 2)) => f D.a) h1
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] at h2
  rw [Equiv.swap_apply_of_ne_of_ne hpa.symm hqa.symm, Equiv.swap_apply_left] at h2
  exact D.hab h2.symm

include hpa hpb hqa hqb hz in
theorem cbz_sq : (z : MulAut V) ^ 2 = 1 := by
  have hc := cbz_swap_comm hpa hpb hqa hqb
  have h : z * z = 1 := by
    apply D.θ.injective
    apply Subtype.ext
    rw [map_mul, map_one]
    show (D.θ z : Equiv.Perm (Fin (m + 2))) * (D.θ z : Equiv.Perm (Fin (m + 2))) = 1
    rw [hz]
    calc Equiv.swap D.a D.b * Equiv.swap p q * (Equiv.swap D.a D.b * Equiv.swap p q)
        = Equiv.swap D.a D.b * (Equiv.swap p q * Equiv.swap D.a D.b) * Equiv.swap p q := by group
      _ = Equiv.swap D.a D.b * (Equiv.swap D.a D.b * Equiv.swap p q) * Equiv.swap p q := by
          rw [← hc]
      _ = (Equiv.swap D.a D.b * Equiv.swap D.a D.b) * (Equiv.swap p q * Equiv.swap p q) := by
          group
      _ = 1 := by rw [Equiv.swap_mul_self, Equiv.swap_mul_self, mul_one]
  rw [pow_two]
  exact congrArg Subtype.val h

include hz in
theorem cbz_comm_of_mem {x : MulAut V}
    (hx : x ∈ cbzSub D (altStabilizer (m + 2) ({D.a, D.b, p, q} : Finset (Fin (m + 2))))) :
    z * x = x * z ∧ t * x = x * t := by
  classical
  obtain ⟨hxX, hS⟩ := mem_cbzSub.mp hx
  have hfix := mem_altStabilizer_iff.mp hS
  have ha : (D.θ ⟨x, hxX⟩ : Equiv.Perm (Fin (m + 2))) D.a = D.a := hfix _ (by simp)
  have hb : (D.θ ⟨x, hxX⟩ : Equiv.Perm (Fin (m + 2))) D.b = D.b := hfix _ (by simp)
  have hp : (D.θ ⟨x, hxX⟩ : Equiv.Perm (Fin (m + 2))) p = p := hfix _ (by simp)
  have hq : (D.θ ⟨x, hxX⟩ : Equiv.Perm (Fin (m + 2))) q = q := hfix _ (by simp)
  have hρτ := cbz_comm_swap ha hb
  have hρπ := cbz_comm_swap hp hq
  constructor
  · have h : (z * ⟨x, hxX⟩ : ↥X) = ⟨x, hxX⟩ * z := by
      apply D.θ.injective
      apply Subtype.ext
      rw [map_mul, map_mul]
      show (D.θ z : Equiv.Perm (Fin (m + 2))) * (D.θ ⟨x, hxX⟩ : Equiv.Perm (Fin (m + 2))) =
        (D.θ ⟨x, hxX⟩ : Equiv.Perm (Fin (m + 2))) * (D.θ z : Equiv.Perm (Fin (m + 2)))
      rw [hz]
      calc Equiv.swap D.a D.b * Equiv.swap p q * (D.θ ⟨x, hxX⟩ : Equiv.Perm (Fin (m + 2)))
          = Equiv.swap D.a D.b * (Equiv.swap p q * (D.θ ⟨x, hxX⟩ : Equiv.Perm (Fin (m + 2)))) := by
            group
        _ = Equiv.swap D.a D.b * ((D.θ ⟨x, hxX⟩ : Equiv.Perm (Fin (m + 2))) * Equiv.swap p q) := by
            rw [hρπ]
        _ = (Equiv.swap D.a D.b * (D.θ ⟨x, hxX⟩ : Equiv.Perm (Fin (m + 2)))) * Equiv.swap p q := by
            group
        _ = ((D.θ ⟨x, hxX⟩ : Equiv.Perm (Fin (m + 2))) * Equiv.swap D.a D.b) * Equiv.swap p q := by
            rw [hρτ]
        _ = (D.θ ⟨x, hxX⟩ : Equiv.Perm (Fin (m + 2))) * (Equiv.swap D.a D.b * Equiv.swap p q) := by
            group
    exact congrArg Subtype.val h
  · have h2 : (D.θ ⟨t * x * t⁻¹, D.hn x hxX⟩ : Equiv.Perm (Fin (m + 2))) =
        D.θ ⟨x, hxX⟩ := by
      rw [D.hconj x hxX]
      calc Equiv.swap D.a D.b * (D.θ ⟨x, hxX⟩ : Equiv.Perm (Fin (m + 2))) *
            (Equiv.swap D.a D.b)⁻¹
          = ((D.θ ⟨x, hxX⟩ : Equiv.Perm (Fin (m + 2))) * Equiv.swap D.a D.b) *
              (Equiv.swap D.a D.b)⁻¹ := by rw [hρτ]
        _ = (D.θ ⟨x, hxX⟩ : Equiv.Perm (Fin (m + 2))) := by group
    have h3 := cbz_eq_of_perm_eq (D := D) (D.hn x hxX) hxX h2
    calc t * x = t * x * t⁻¹ * t := by group
      _ = x * t := by rw [h3]

end ZFacts

theorem cbz_card_four {k : ℕ} {a b p q : Fin k} (hab : a ≠ b) (hpq : p ≠ q) (hpa : p ≠ a)
    (hpb : p ≠ b) (hqa : q ≠ a) (hqb : q ≠ b) : ({a, b, p, q} : Finset (Fin k)).card = 4 := by
  classical
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hpq]
  · simp [hpb.symm, hqb.symm]
  · simp [hab, hpa.symm, hqa.symm]

end Sub

section Norm

variable {V : Type} [CommGroup V] [Finite V] {Y X G T : Subgroup (MulAut V)} {t : MulAut V}
  {m : ℕ}

namespace OneCfg

variable (c : OneCfg G T Y t m X) (D : CbData Y t m X)

include c in
theorem normalizes_cbzSub {p q : Fin (m + 2)} (hpq : p ≠ q) {z : ↥X}
    (hz : (D.θ z : Equiv.Perm (Fin (m + 2))) = Equiv.swap D.a D.b * Equiv.swap p q)
    {g : MulAut V} (hg : g ∈ G) (hgt : g * t = t * g) (hgz : g * (z : MulAut V) = z * g) :
    ∀ x ∈ cbzSub D (altStabilizer (m + 2) ({D.a, D.b, p, q} : Finset (Fin (m + 2)))),
      g * x * g⁻¹ ∈ cbzSub D (altStabilizer (m + 2) ({D.a, D.b, p, q} : Finset (Fin (m + 2)))) := by
  classical
  have hm5 : 5 ≤ m + 2 := by have := c.hm; omega
  have hm6 : m + 2 ≠ 6 := by have := c.hm; omega
  have hgX := c.normalizes_X_of_comm hg hgt
  obtain ⟨σ, hσ⟩ := exists_perm_of_normalizes hm5 hm6 D.θ hgX
  have hgt' : ∀ y : MulAut V, g * (t * y * t⁻¹) * g⁻¹ = t * (g * y * g⁻¹) * t⁻¹ := by
    intro y
    calc g * (t * y * t⁻¹) * g⁻¹ = (g * t) * y * (g * t)⁻¹ := by group
      _ = (t * g) * y * (t * g)⁻¹ := by rw [hgt]
      _ = t * (g * y * g⁻¹) * t⁻¹ := by group
  have hτ : σ * Equiv.swap D.a D.b = Equiv.swap D.a D.b * σ := by
    refine perm_unique hm5 (fun ρ => ?_)
    obtain ⟨y, rfl⟩ := D.θ.surjective ρ
    have e1 := hσ (t * (y : MulAut V) * t⁻¹) (D.hn y y.2)
    have e2 := D.hconj (g * (y : MulAut V) * g⁻¹) (hgX y y.2)
    have e3 := hσ y y.2
    have e4 := D.hconj y y.2
    have e5 : (⟨g * (t * (y : MulAut V) * t⁻¹) * g⁻¹, hgX _ (D.hn y y.2)⟩ : ↥X) =
        ⟨t * (g * (y : MulAut V) * g⁻¹) * t⁻¹, D.hn _ (hgX y y.2)⟩ := Subtype.ext (hgt' y)
    have key : σ * (Equiv.swap D.a D.b * (D.θ y : Equiv.Perm (Fin (m + 2))) *
          (Equiv.swap D.a D.b)⁻¹) * σ⁻¹ =
        Equiv.swap D.a D.b * (σ * (D.θ y : Equiv.Perm (Fin (m + 2))) * σ⁻¹) *
          (Equiv.swap D.a D.b)⁻¹ := by
      have h6 := congrArg
        (fun w : alternatingGroup (Fin (m + 2)) => (w : Equiv.Perm (Fin (m + 2))))
        (congrArg D.θ e5)
      rw [e1, e4, e2, e3] at h6
      exact h6
    calc σ * Equiv.swap D.a D.b * (D.θ y : Equiv.Perm (Fin (m + 2))) *
          (σ * Equiv.swap D.a D.b)⁻¹
        = σ * (Equiv.swap D.a D.b * (D.θ y : Equiv.Perm (Fin (m + 2))) *
            (Equiv.swap D.a D.b)⁻¹) * σ⁻¹ := by group
      _ = Equiv.swap D.a D.b * (σ * (D.θ y : Equiv.Perm (Fin (m + 2))) * σ⁻¹) *
            (Equiv.swap D.a D.b)⁻¹ := key
      _ = Equiv.swap D.a D.b * σ * (D.θ y : Equiv.Perm (Fin (m + 2))) *
            (Equiv.swap D.a D.b * σ)⁻¹ := by group
  have hζ : σ * (Equiv.swap D.a D.b * Equiv.swap p q) * σ⁻¹ =
      Equiv.swap D.a D.b * Equiv.swap p q := by
    have e := hσ z z.2
    have e' : (⟨g * (z : MulAut V) * g⁻¹, hgX z z.2⟩ : ↥X) = z :=
      Subtype.ext (by
        calc g * (z : MulAut V) * g⁻¹ = z * g * g⁻¹ := by rw [hgz]
          _ = z := by group)
    rw [e'] at e
    rw [← hz]
    exact e.symm
  have hστ : σ * Equiv.swap D.a D.b * σ⁻¹ = Equiv.swap D.a D.b := by rw [hτ]; group
  have h3 : Equiv.swap D.a D.b * (σ * Equiv.swap p q * σ⁻¹) =
      Equiv.swap D.a D.b * Equiv.swap p q := by
    calc Equiv.swap D.a D.b * (σ * Equiv.swap p q * σ⁻¹)
        = (σ * Equiv.swap D.a D.b * σ⁻¹) * (σ * Equiv.swap p q * σ⁻¹) := by rw [hστ]
      _ = σ * (Equiv.swap D.a D.b * Equiv.swap p q) * σ⁻¹ := by group
      _ = Equiv.swap D.a D.b * Equiv.swap p q := hζ
  have h4 : σ * Equiv.swap p q * σ⁻¹ = Equiv.swap p q := mul_left_cancel h3
  have hπ : σ * Equiv.swap p q = Equiv.swap p q * σ := by
    calc σ * Equiv.swap p q = (σ * Equiv.swap p q * σ⁻¹) * σ := by group
      _ = Equiv.swap p q * σ := by rw [h4]
  intro x hx
  obtain ⟨hxX, hS⟩ := mem_cbzSub.mp hx
  refine mem_cbzSub.mpr ⟨hgX x hxX, mem_altStabilizer_iff.mpr fun r hr => ?_⟩
  have h5 := cbz_conj_fix D.hab hpq hτ hπ (mem_altStabilizer_iff.mp hS) r hr
  have h6 := congrArg (fun f : Equiv.Perm (Fin (m + 2)) => f r) (hσ x hxX)
  exact h6.trans h5

include c in
theorem exists_zZ :
    ∃ (z : MulAut V) (Z : Subgroup (MulAut V)) (b : ℕ), z ∈ X ∧ z ≠ 1 ∧ z ^ 2 = 1 ∧
      t * z = z * t ∧ Z ≤ X ∧ (∀ x ∈ Z, z * x = x * z) ∧ (∀ x ∈ Z, t * x = x * t) ∧ 2 ≤ b ∧
      (∃ θZ : ↥Z ≃* alternatingGroup (Fin (2 * b + 1)),
        IsNatSectionWith (altAct (2 * b + 1)) θZ (commV Z) ⊥) ∧
      (∀ g ∈ G, g * z = z * g → g * t = t * g → ∀ x ∈ Z, g * x * g⁻¹ ∈ Z) := by
  classical
  obtain ⟨D⟩ := c.hX.toCbAlg.nonempty_data c.hm c.hodd
  have hm := c.hm
  obtain ⟨p, q, -, -, hp, hq, -, -, hpq, -, -, -, -, -⟩ :=
    cbp_four_points ({D.a, D.b} : Finset (Fin (m + 2)))
      (by rw [Finset.card_pair D.hab]; omega)
  have hpa : p ≠ D.a := fun h => hp (by simp [h])
  have hpb : p ≠ D.b := fun h => hp (by simp [h])
  have hqa : q ≠ D.a := fun h => hq (by simp [h])
  have hqb : q ≠ D.b := fun h => hq (by simp [h])
  obtain ⟨z, hz⟩ : ∃ z : ↥X, D.θ z = ⟨Equiv.swap D.a D.b * Equiv.swap p q,
      cbz_even D.hab hpq⟩ := D.θ.surjective _
  have hz' : (D.θ z : Equiv.Perm (Fin (m + 2))) = Equiv.swap D.a D.b * Equiv.swap p q :=
    congrArg Subtype.val hz
  have hcard := cbz_card_four D.hab hpq hpa hpb hqa hqb
  obtain ⟨k, hk⟩ := c.hodd
  subst hk
  have hnat : ∃ θZ : ↥(cbzSub D (altStabilizer (2 * k + 1 + 2)
        ({D.a, D.b, p, q} : Finset (Fin (2 * k + 1 + 2))))) ≃*
        alternatingGroup (Fin (2 * (k - 1) + 1)),
      IsNatSectionWith (altAct (2 * (k - 1) + 1)) θZ (commV (cbzSub D (altStabilizer
        (2 * k + 1 + 2) ({D.a, D.b, p, q} : Finset (Fin (2 * k + 1 + 2)))))) ⊥ :=
    natSection_stab_natural c.hV (a := k + 1) (b := k - 1) (by omega) (by omega) (by omega)
      D.θ D.hnat ({D.a, D.b, p, q} : Finset (Fin (2 * k + 1 + 2))) (by rw [hcard]; omega)
      (cbzSub_le D _) (cbzSub_map_eq D _)
  exact ⟨z, _, k - 1, z.2, cbz_ne_one D hpa hqa hz', cbz_sq D hpa hpb hqa hqb hz',
    cbz_t_comm D hpa hpb hqa hqb hz', cbzSub_le D _,
    fun x hx => (cbz_comm_of_mem D hz' hx).1, fun x hx => (cbz_comm_of_mem D hz' hx).2,
    by omega, hnat, fun g hg hgz hgt x hx => c.normalizes_cbzSub D hpq hz' hg hgt hgz x hx⟩

end OneCfg

end Norm

end CFSG.CGT.PushingUpLit.CGT6
