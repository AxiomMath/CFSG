module

public import CFSG.CGT.PushingUpLit.A78Sp4.Coord
public import Mathlib.Tactic.Group

public section

namespace CFSG.CGT.PushingUpLit.A78Sp4

open scoped commutatorElement

variable {K : Type*} [Field K] {G : Type*} [Group G] {J : Subgroup G}

namespace Cls2Coord
variable (c : Cls2Coord K J)

theorem ker_of_central {x : G} (hx : x ∈ J) (hcen : ∀ y ∈ J, x * y = y * x) : c.π x = 0 := by
  have h : ∀ w : K × K, beta (c.π x) w = 0 := by
    intro w
    obtain ⟨y, hy, hyw⟩ := c.π_surj w
    have h1 : ⁅x, y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (hcen y hy)
    have h2 := (c.comm x hx y hy).2
    rw [h1, c.ζ_one, hyw] at h2
    exact h2.symm
  have h1 := h (0, 1)
  have h2 := h (1, 0)
  simp only [beta] at h1 h2
  obtain ⟨hr, _⟩ := Prod.ext_iff.1 h1
  obtain ⟨hs, _⟩ := Prod.ext_iff.1 h2
  ext
  · simpa using hr
  · simpa using hs

variable {s : G} (hs : ∀ x ∈ J, s * x * s⁻¹ ∈ J) (hs' : ∀ x ∈ J, s⁻¹ * x * s ∈ J)
include hs hs'

theorem conj_ker {z : G} (hz : z ∈ J) (h0 : c.π z = 0) : c.π (s * z * s⁻¹) = 0 := by
  apply c.ker_of_central (hs z hz)
  intro y hy
  have hy' := hs' y hy
  have h := c.ker_central hz h0 hy'
  calc s * z * s⁻¹ * y = s * (z * (s⁻¹ * y * s)) * s⁻¹ := by group
    _ = s * ((s⁻¹ * y * s) * z) * s⁻¹ := by rw [h]
    _ = y * (s * z * s⁻¹) := by group

theorem π_conj_congr {x x' : G} (hx : x ∈ J) (hx' : x' ∈ J) (h : c.π x = c.π x') :
    c.π (s * x * s⁻¹) = c.π (s * x' * s⁻¹) := by
  have hz : x⁻¹ * x' ∈ J := J.mul_mem (J.inv_mem hx) hx'
  have hz0 : c.π (x⁻¹ * x') = 0 := by
    rw [c.π_mul _ (J.inv_mem hx) _ hx', c.π_inv hx, h]; simp
  have h1 := c.conj_ker hs hs' hz hz0
  have e : s * x' * s⁻¹ = (s * x * s⁻¹) * (s * (x⁻¹ * x') * s⁻¹) := by group
  rw [e, c.π_mul _ (hs x hx) _ (hs _ hz), h1, add_zero]

end Cls2Coord

structure ActsAs (c : Cls2Coord K J) (s : G) (gb Γ : K × K →+ K × K) : Prop where
  π_conj : ∀ x ∈ J, c.π (s * x * s⁻¹) = gb (c.π x)
  ζ_conj : ∀ z ∈ J, c.π z = 0 → c.ζ (s * z * s⁻¹) = Γ (c.ζ z)

namespace Cls2Coord
variable (c : Cls2Coord K J) {s : G} (hs : ∀ x ∈ J, s * x * s⁻¹ ∈ J)
  (hs' : ∀ x ∈ J, s⁻¹ * x * s ∈ J)
include hs hs'

theorem exists_actsAs : ∃ gb Γ : K × K →+ K × K, ActsAs c s gb Γ := by
  classical
  choose xs hxsJ hxsπ using c.π_surj
  have key : ∀ x ∈ J, c.π (s * xs (c.π x) * s⁻¹) = c.π (s * x * s⁻¹) := fun x hx =>
    c.π_conj_congr hs hs' (hxsJ _) hx (hxsπ _)
  let gb : K × K →+ K × K :=
    { toFun := fun w => c.π (s * xs w * s⁻¹)
      map_zero' := by
        have h := key 1 J.one_mem
        rw [c.π_one] at h
        simpa [c.π_one] using h
      map_add' := by
        intro w w'
        have h1 := key (xs w * xs w') (J.mul_mem (hxsJ w) (hxsJ w'))
        rw [c.π_mul _ (hxsJ w) _ (hxsJ w'), hxsπ, hxsπ] at h1
        rw [h1]
        have e : s * (xs w * xs w') * s⁻¹ = (s * xs w * s⁻¹) * (s * xs w' * s⁻¹) := by group
        rw [e, c.π_mul _ (hs _ (hxsJ w)) _ (hs _ (hxsJ w'))] }
  choose zs hzsJ hzsπ hzsζ using c.ζ_surj
  have keyζ : ∀ z ∈ J, c.π z = 0 → c.ζ (s * zs (c.ζ z) * s⁻¹) = c.ζ (s * z * s⁻¹) := by
    intro z hz h0
    have : zs (c.ζ z) = z := c.ζ_inj _ (hzsJ _) (hzsπ _) z hz h0 (hzsζ _)
    rw [this]
  let Γ : K × K →+ K × K :=
    { toFun := fun w => c.ζ (s * zs w * s⁻¹)
      map_zero' := by
        have h := keyζ 1 J.one_mem c.π_one
        rw [c.ζ_one] at h
        simpa [c.ζ_one] using h
      map_add' := by
        intro w w'
        have hm : c.π (zs w * zs w') = 0 := by
          rw [c.π_mul _ (hzsJ w) _ (hzsJ w'), hzsπ, hzsπ, add_zero]
        have h1 := keyζ (zs w * zs w') (J.mul_mem (hzsJ w) (hzsJ w')) hm
        rw [c.ζ_mul _ (hzsJ w) (hzsπ w) _ (hzsJ w') (hzsπ w'), hzsζ, hzsζ] at h1
        rw [h1]
        have e : s * (zs w * zs w') * s⁻¹ = (s * zs w * s⁻¹) * (s * zs w' * s⁻¹) := by group
        rw [e, c.ζ_mul _ (hs _ (hzsJ w)) (c.conj_ker hs hs' (hzsJ w) (hzsπ w)) _
          (hs _ (hzsJ w')) (c.conj_ker hs hs' (hzsJ w') (hzsπ w'))] }
  refine ⟨gb, Γ, ⟨fun x hx => ?_, fun z hz h0 => ?_⟩⟩
  · exact (key x hx).symm
  · exact (keyζ z hz h0).symm

end Cls2Coord

namespace ActsAs

variable {c : Cls2Coord K J} {s : G} {gb Γ : K × K →+ K × K}

theorem hcomp (h : ActsAs c s gb Γ) (hs : ∀ x ∈ J, s * x * s⁻¹ ∈ J) (x y : K × K) :
    Γ (beta x y) = beta (gb x) (gb y) := by
  obtain ⟨a, ha, hax⟩ := c.π_surj x
  obtain ⟨b, hb, hby⟩ := c.π_surj y
  have hcab := c.comm a ha b hb
  have haJ : ⁅a, b⁆ ∈ J := by
    rw [commutatorElement_def]
    exact J.mul_mem (J.mul_mem (J.mul_mem ha hb) (J.inv_mem ha)) (J.inv_mem hb)
  have e : s * ⁅a, b⁆ * s⁻¹ = ⁅s * a * s⁻¹, s * b * s⁻¹⁆ := by
    simp only [commutatorElement_def]; group
  have h1 := h.ζ_conj ⁅a, b⁆ haJ hcab.1
  have h2 := (c.comm _ (hs a ha) _ (hs b hb)).2
  rw [← e, h1, hcab.2, hax, hby, h.π_conj a ha, h.π_conj b hb, hax, hby] at h2
  exact h2

theorem bijective {gb' Γ' : K × K →+ K × K} (h : ActsAs c s gb Γ) (h' : ActsAs c s⁻¹ gb' Γ')
    (hs : ∀ x ∈ J, s * x * s⁻¹ ∈ J) (hs' : ∀ x ∈ J, s⁻¹ * x * s ∈ J) : Function.Bijective gb := by
  have hl : Function.LeftInverse gb' gb := by
    intro w
    obtain ⟨x, hx, rfl⟩ := c.π_surj w
    have e1 : gb (c.π x) = c.π (s * x * s⁻¹) := (h.π_conj x hx).symm
    have e2 := h'.π_conj _ (hs x hx)
    have e3 : s⁻¹ * (s * x * s⁻¹) * s⁻¹⁻¹ = x := by group
    rw [e3] at e2
    rw [e1, ← e2]
  have hr : Function.RightInverse gb' gb := by
    intro w
    obtain ⟨x, hx, rfl⟩ := c.π_surj w
    have e1 : gb' (c.π x) = c.π (s⁻¹ * x * s⁻¹⁻¹) := (h'.π_conj x hx).symm
    have e0 : s⁻¹ * x * s⁻¹⁻¹ = s⁻¹ * x * s := by group
    rw [e0] at e1
    have e2 := h.π_conj _ (hs' x hx)
    have e3 : s * (s⁻¹ * x * s) * s⁻¹ = x := by group
    rw [e3] at e2
    rw [e1, ← e2]
  exact ⟨hl.injective, hr.surjective⟩

theorem commSet_eq_range [CharP K 2] (h : ActsAs c s gb Γ) (hs : ∀ x ∈ J, s * x * s⁻¹ ∈ J) :
    commSet c s = Set.range (gb + AddMonoidHom.id (K × K)) := by
  have key : ∀ y ∈ J, c.π ⁅s, y⁆ = gb (c.π y) + c.π y := by
    intro y hy
    have e : ⁅s, y⁆ = (s * y * s⁻¹) * y⁻¹ := by simp [commutatorElement_def, mul_assoc]
    rw [e, c.π_mul _ (hs y hy) _ (J.inv_mem hy), h.π_conj y hy, c.π_inv hy]
    congr 1
    exact Prod.ext (CharTwo.neg_eq _) (CharTwo.neg_eq _)
  ext w
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨c.π y, by simp [key y hy]⟩
  · rintro ⟨u, rfl⟩
    obtain ⟨y, hy, rfl⟩ := c.π_surj u
    exact ⟨y, hy, by simp [key y hy]⟩

end ActsAs

@[expose] def WDiag (c : Cls2Coord K J) (s : G) : Prop :=
  ∀ x ∈ J, ((c.π x).2 = 0 → (c.π (s * x * s⁻¹)).2 = 0) ∧
    ((c.π x).1 = 0 → (c.π (s * x * s⁻¹)).1 = 0)

@[expose] def WSwap (c : Cls2Coord K J) (s : G) : Prop :=
  ∀ x ∈ J, ((c.π x).2 = 0 → (c.π (s * x * s⁻¹)).1 = 0) ∧
    ((c.π x).1 = 0 → (c.π (s * x * s⁻¹)).2 = 0)

namespace ActsAs

variable {c : Cls2Coord K J} {s : G} {gb Γ : K × K →+ K × K}

theorem axes_diag (h : ActsAs c s gb Γ) (hd : WDiag c s) :
    (∀ r, (gb (r, 0)).2 = 0) ∧ ∀ t, (gb (0, t)).1 = 0 := by
  constructor
  · intro r
    obtain ⟨x, hx, hxr⟩ := c.π_surj (r, 0)
    have := (hd x hx).1 (by rw [hxr])
    rwa [h.π_conj x hx, hxr] at this
  · intro t
    obtain ⟨x, hx, hxr⟩ := c.π_surj (0, t)
    have := (hd x hx).2 (by rw [hxr])
    rwa [h.π_conj x hx, hxr] at this

theorem axes_swap (h : ActsAs c s gb Γ) (hd : WSwap c s) :
    (∀ r, (gb (r, 0)).1 = 0) ∧ ∀ t, (gb (0, t)).2 = 0 := by
  constructor
  · intro r
    obtain ⟨x, hx, hxr⟩ := c.π_surj (r, 0)
    have := (hd x hx).1 (by rw [hxr])
    rwa [h.π_conj x hx, hxr] at this
  · intro t
    obtain ⟨x, hx, hxr⟩ := c.π_surj (0, t)
    have := (hd x hx).2 (by rw [hxr])
    rwa [h.π_conj x hx, hxr] at this

end ActsAs

end CFSG.CGT.PushingUpLit.A78Sp4
