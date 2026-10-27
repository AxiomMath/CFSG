module

public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.UpperBound

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

open CFSG.Open

theorem pRank_le_of_torus_normalizer {X W : Type} [Group X] [Finite X] [Group W]
    {p : ℕ} (hp : p.Prime) (N H : Subgroup X)
    (hHc : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (hidx : ¬ p ∣ N.index)
    (φ : N →* W) (hker : ∀ n : N, φ n = 1 ↔ (n : X) ∈ H) {k : ℕ}
    (hW : ∀ (F : Subgroup W) (S : Subgroup X), IsElemAbelian p F → IsElemAbelian p S →
      S ≤ H → (∀ h ∈ S, ∀ e : N, φ e ∈ F → (e : X) * h * (e : X)⁻¹ = h) →
        Nat.card S * Nat.card F ≤ p ^ k) :
    pRank p (⊤ : Subgroup X) ≤ k := by
  classical
  have := Fact.mk hp
  have hNfin : Finite N := inferInstance
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow p N))
  set P : Subgroup X := (Q : Subgroup N).map N.subtype with hPdef
  have hPcard : Nat.card P = p ^ (Nat.card X).factorization p := by
    have h1 : Nat.card P = Nat.card (Q : Subgroup N) :=
      Subgroup.card_map_of_injective N.subtype_injective
    rw [h1, Sylow.card_eq_multiplicity]
    have h2 : Nat.card X = N.index * Nat.card N := by
      rw [mul_comm]; exact Subgroup.card_mul_index N |>.symm
    have hX0 : N.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hN0 : Nat.card N ≠ 0 := Nat.card_pos.ne'
    rw [h2, Nat.factorization_mul hX0 hN0]
    simp [Nat.factorization_eq_zero_of_not_dvd hidx]
  refine SporadicRank.pRank_le_of_sylow hp P hPcard fun E hEP hE => ?_
  have hEN : E ≤ N := hEP.trans (by rintro _ ⟨x, _, rfl⟩; exact x.2)
  let ψ : E →* W := φ.comp (Subgroup.inclusion hEN)
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy => by
    have := hE.1.is_comm.comm (⟨x, hx⟩ : E) ⟨y, hy⟩
    exact congrArg Subtype.val this
  have hker' : ∀ e : E, ψ e = 1 ↔ (e : X) ∈ H := fun e => hker ⟨e, hEN e.2⟩
  have hF : IsElemAbelian p ψ.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨x, hx⟩ := a.2
      obtain ⟨z, hz⟩ := b.2
      apply Subtype.ext
      change (a : W) * b = b * a
      rw [← hx, ← hz, ← map_mul, ← map_mul]
      exact congrArg (fun w : E => ψ w) (Subtype.ext (hEc _ x.2 _ z.2))
    · obtain ⟨x, rfl⟩ := hy
      rw [← map_pow]
      have : (x : X) ^ p = 1 := hE.2 x x.2
      have hx : x ^ p = 1 := Subtype.ext this
      rw [hx, map_one]
  set S : Subgroup X := E ⊓ H with hSdef
  have hSE : S ≤ E := inf_le_left
  have hS : IsElemAbelian p S := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => hE.2 x (hSE hx)⟩
    exact Subtype.ext (hEc _ (hSE a.2) _ (hSE b.2))
  have hfix : ∀ h ∈ S, ∀ e : N, φ e ∈ ψ.range → (e : X) * h * (e : X)⁻¹ = h := by
    intro h hh e ⟨x, hx⟩
    have hxN : (x : X) ∈ N := hEN x.2
    have hke : ((⟨x, hxN⟩ : N)⁻¹ * e) ∈ (φ.ker) := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      have : φ ⟨x, hxN⟩ = φ e := hx
      rw [this, inv_mul_cancel]
    have hkH : ((x : X)⁻¹ * (e : X)) ∈ H := (hker _).1 hke
    have he : (e : X) = (x : X) * ((x : X)⁻¹ * (e : X)) := by group
    set k : X := (x : X)⁻¹ * (e : X) with hk
    have hxh : (x : X) * h = h * x := hEc _ x.2 _ (hSE hh)
    have hkh : k * h = h * k := hHc _ hkH _ hh.2
    calc (e : X) * h * (e : X)⁻¹ = (x : X) * (k * h) * k⁻¹ * (x : X)⁻¹ := by
          rw [he]; group
      _ = h := by
          rw [hkh]
          calc (x : X) * (h * k) * k⁻¹ * (x : X)⁻¹ = (x : X) * h * (x : X)⁻¹ := by group
            _ = h := by rw [hxh]; group
  have hbound := hW ψ.range S hF hS inf_le_right hfix
  have hcard : Nat.card E = Nat.card S * Nat.card ψ.range := by
    have hkerS : ψ.ker = S.subgroupOf E := by
      ext x
      simp [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hSdef, hker' x]
    have h1 := Subgroup.card_ker_mul_card_range ψ
    have h2 : Nat.card (S.subgroupOf E) = Nat.card S :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSE).toEquiv
    rw [hkerS, h2] at h1
    exact h1.symm
  rw [hcard]
  exact hbound

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
