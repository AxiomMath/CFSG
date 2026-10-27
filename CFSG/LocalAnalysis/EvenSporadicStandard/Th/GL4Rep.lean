module

public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Singer

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Matrix

variable {G : Type*} [Group G] {A : Subgroup G} {c : G → (Fin 4 → ZMod 2)}

structure IsCoord (A : Subgroup G) (c : G → (Fin 4 → ZMod 2)) : Prop where
  mul : ∀ a ∈ A, ∀ b ∈ A, c (a * b) = c a + c b
  inj : ∀ a ∈ A, ∀ b ∈ A, c a = c b → a = b
  onto : ∀ u, ∃ a ∈ A, c a = u

@[expose] def IsRep (A : Subgroup G) (c : G → (Fin 4 → ZMod 2)) (r : G)
    (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Prop :=
  ∀ a ∈ A, c (r * a * r⁻¹) = M *ᵥ c a

theorem IsRep.one : IsRep A c 1 1 := fun a _ => by simp

theorem IsRep.mul {r s : G} {M M' : Matrix (Fin 4) (Fin 4) (ZMod 2)} (h : IsRep A c r M)
    (h' : IsRep A c s M') (hs : ∀ a ∈ A, s * a * s⁻¹ ∈ A) : IsRep A c (r * s) (M * M') := by
  intro a ha
  have e : r * s * a * (r * s)⁻¹ = r * (s * a * s⁻¹) * r⁻¹ := by group
  rw [e, h _ (hs a ha), h' a ha, mulVec_mulVec]

theorem IsRep.pow {r : G} {M : Matrix (Fin 4) (Fin 4) (ZMod 2)} (h : IsRep A c r M)
    (hr : ∀ a ∈ A, r * a * r⁻¹ ∈ A) (n : ℕ) : IsRep A c (r ^ n) (M ^ n) := by
  induction n with
  | zero => simpa using IsRep.one
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul h hr

theorem IsRep.conj_mem {r : G} {M : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hc : IsCoord A c)
    (h : IsRep A c r M) (hr : ∀ a ∈ A, r * a * r⁻¹ ∈ A) {s : G} (hs : ∀ a ∈ A, s * a * s⁻¹ ∈ A)
    (h' : IsRep A c s M) {a : G} (ha : a ∈ A) : r * a * r⁻¹ = s * a * s⁻¹ :=
  hc.inj _ (hr a ha) _ (hs a ha) (by rw [h a ha, h' a ha])

theorem IsCoord.rep_unique (hc : IsCoord A c) {r : G} {M M' : Matrix (Fin 4) (Fin 4) (ZMod 2)}
    (h : IsRep A c r M) (h' : IsRep A c r M') : M = M' := by
  have hall : ∀ u, M *ᵥ u = M' *ᵥ u := fun u => by
    obtain ⟨a, ha, rfl⟩ := hc.onto u
    rw [← h a ha, ← h' a ha]
  ext i j
  have := congrFun (hall (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

theorem IsCoord.exists_rep (hc : IsCoord A c) {r : G} (hr : ∀ a ∈ A, r * a * r⁻¹ ∈ A) :
    ∃ M, IsRep A c r M := by
  classical
  choose d hdA hdc using hc.onto
  have hd : ∀ a ∈ A, d (c a) = a := fun a ha => hc.inj _ (hdA _) a ha (hdc _)
  let g : (Fin 4 → ZMod 2) → (Fin 4 → ZMod 2) := fun u => c (r * d u * r⁻¹)
  have hg : ∀ u v, g (u + v) = g u + g v := by
    intro u v
    have h1 : d (u + v) = d u * d v := by
      apply hc.inj _ (hdA _) _ (A.mul_mem (hdA u) (hdA v))
      rw [hdc, hc.mul _ (hdA u) _ (hdA v), hdc, hdc]
    simp only [g, h1]
    have e : r * (d u * d v) * r⁻¹ = (r * d u * r⁻¹) * (r * d v * r⁻¹) := by group
    rw [e, hc.mul _ (hr _ (hdA u)) _ (hr _ (hdA v))]
  let f : (Fin 4 → ZMod 2) →+ (Fin 4 → ZMod 2) := AddMonoidHom.mk' g hg
  refine ⟨LinearMap.toMatrix' (f.toZModLinearMap 2), fun a ha => ?_⟩
  have h2 : (LinearMap.toMatrix' (f.toZModLinearMap 2)) *ᵥ c a = g (c a) := by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    rfl
  rw [h2]
  simp only [g, hd a ha]

theorem IsCoord.exists_matHom (hc : IsCoord A c) (N : Subgroup G)
    (hN : ∀ q ∈ N, ∀ a ∈ A, q * a * q⁻¹ ∈ A) :
    ∃ m : N →* Matrix (Fin 4) (Fin 4) (ZMod 2), ∀ q : N, IsRep A c q (m q) := by
  choose M hM using fun q : N => hc.exists_rep (hN q q.2)
  refine ⟨{ toFun := M, map_one' := ?_, map_mul' := ?_ }, hM⟩
  · exact hc.rep_unique (hM 1) (by rw [Subgroup.coe_one]; exact IsRep.one)
  · intro q q'
    have h : IsRep A c ((q : G) * q') (M q * M q') := (hM q).mul (hM q') (hN q' q'.2)
    exact hc.rep_unique (hM (q * q')) h

theorem IsCoord.exists_lift {L : Subgroup G} (hc : IsCoord A c)
    (hsurj : ∀ f : G → G, (∀ a ∈ A, f a ∈ A) → (∀ a ∈ A, ∀ b ∈ A, f (a * b) = f a * f b) →
      (∀ a ∈ A, ∀ b ∈ A, f a = f b → a = b) → ∃ n ∈ L, ∀ a ∈ A, n * a * n⁻¹ = f a)
    {M : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hM : Function.Injective M.mulVec) :
    ∃ n ∈ L, (∀ x ∈ A, n * x * n⁻¹ ∈ A) ∧ IsRep A c n M := by
  classical
  choose d hdA hdc using hc.onto
  have hd : ∀ a ∈ A, d (c a) = a := fun a ha => hc.inj _ (hdA _) a ha (hdc _)
  let f : G → G := fun y => if y ∈ A then d (M *ᵥ c y) else 1
  have hf : ∀ a ∈ A, f a = d (M *ᵥ c a) := fun a ha => by simp [f, ha]
  obtain ⟨n, hnL, hn⟩ := hsurj f (fun a ha => by rw [hf a ha]; exact hdA _)
    (fun a ha b hb => by
      rw [hf _ (A.mul_mem ha hb), hf a ha, hf b hb]
      apply hc.inj _ (hdA _) _ (A.mul_mem (hdA _) (hdA _))
      rw [hdc, hc.mul _ (hdA _) _ (hdA _), hdc, hdc, hc.mul _ ha _ hb, mulVec_add])
    (fun a ha b hb hab => by
      rw [hf a ha, hf b hb] at hab
      have := congrArg c hab
      rw [hdc, hdc] at this
      exact hc.inj _ ha _ hb (hM this))
  have hnA : ∀ x ∈ A, n * x * n⁻¹ ∈ A := fun x hx => by rw [hn x hx, hf x hx]; exact hdA _
  refine ⟨n, hnL, hnA, fun a ha => ?_⟩
  rw [hn a ha, hf a ha, hdc]

end CFSG.EvenSporadicStandard.ThStd
