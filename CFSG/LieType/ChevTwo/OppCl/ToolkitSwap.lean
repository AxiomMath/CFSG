module

public import CFSG.LieType.ChevTwo.OppCl.ToolkitSwapCore

public section

namespace CFSG.LieType.ChevTwo.OppCl.TK

open CFSG.Open CFSG.LieType.BorelTits

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

private theorem exists_split_ker [CharP F 2] [Finite V] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (Rh : Subgroup (Equiv.Perm V)) (hs : Rh ≤ semilinGroup F V) (hR : IsPGroup p Rh)
    (A : Submodule F V) (hA : ∀ r ∈ Rh, ∀ v ∈ A, r v ∈ A)
    (f : V →ₗ[F] V) (hfc : ∀ r ∈ Rh, ∀ v, r (f v) = f (r v)) :
    ∃ A₁ : Submodule F V, A₁ ≤ A ∧ (∀ r ∈ Rh, ∀ v ∈ A₁, r v ∈ A₁) ∧
      (∀ a ∈ A₁, f a = 0 → a = 0) ∧ ∀ v ∈ A, ∃ c ∈ A₁, f c = f v := by
  obtain ⟨K, hKmem⟩ : ∃ K : Submodule F V, ∀ v, v ∈ K ↔ f v = 0 ∧ v ∈ A :=
    ⟨LinearMap.ker f ⊓ A, fun v => by rw [Submodule.mem_inf, LinearMap.mem_ker]⟩
  have hK : ∀ r ∈ Rh, ∀ v ∈ K, r v ∈ K := by
    intro r hr v hv
    obtain ⟨hfv, hvA⟩ := (hKmem v).1 hv
    refine (hKmem (r v)).2 ⟨?_, hA r hr v hvA⟩
    rw [← hfc r hr v, hfv]
    exact semilin_map_zero (hs hr)
  obtain ⟨C₀, hC₀, hC₀inv⟩ := exists_invariant_compl p hp2 Rh hs hR K hK
  refine ⟨C₀ ⊓ A, inf_le_right, ?_, ?_, ?_⟩
  · intro r hr v hv
    rw [Submodule.mem_inf] at hv ⊢
    exact ⟨hC₀inv r hr v hv.1, hA r hr v hv.2⟩
  · intro a ha hfa
    rw [Submodule.mem_inf] at ha
    have haK : a ∈ K := (hKmem a).2 ⟨hfa, ha.2⟩
    exact Submodule.disjoint_def.1 hC₀.disjoint a haK ha.1
  · intro v hv
    have hvtop : v ∈ K ⊔ C₀ := by
      rw [hC₀.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨κ, hκK, c, hcC, hκc⟩ := Submodule.mem_sup.1 hvtop
    obtain ⟨hfκ, hκA⟩ := (hKmem κ).1 hκK
    have hcv : c = v - κ := by
      rw [← hκc]
      abel
    have hcA : c ∈ A := by
      rw [hcv]
      exact A.sub_mem hv hκA
    refine ⟨c, Submodule.mem_inf.2 ⟨hcC, hcA⟩, ?_⟩
    rw [hcv, map_sub, hfκ, sub_zero]

theorem exists_equivariant_swap [CharP F 2] [Finite V] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (Rh : Subgroup (Equiv.Perm V)) (hs : Rh ≤ semilinGroup F V) (hR : IsPGroup p Rh)
    (A B D : Submodule F V) (hA : ∀ r ∈ Rh, ∀ v ∈ A, r v ∈ A) (hB : ∀ r ∈ Rh, ∀ v ∈ B, r v ∈ B)
    (hD : ∀ r ∈ Rh, ∀ v ∈ D, r v ∈ D) (hDB : Disjoint D B)
    (f : V →ₗ[F] V) (hfc : ∀ r ∈ Rh, ∀ v, r (f v) = f (r v)) (hfAB : ∀ v ∈ A, f v ∈ B)
    (hf0 : ∃ v ∈ A, f v ≠ 0) :
    ∃ g : V →ₗ[F] V, (∀ r ∈ Rh, ∀ v, r (g v) = g (r v)) ∧ (∀ v, g v ∈ A) ∧ (∀ v ∈ D, g v = 0) ∧
      ∃ v ∈ B, g v ≠ 0 := by
  obtain ⟨A₁, hA₁A, hA₁inv, hfinj, hdec⟩ := exists_split_ker p hp2 Rh hs hR A hA f hfc
  have hmapB : A₁.map f ≤ B := by
    rintro _ ⟨a, ha, rfl⟩
    exact hfAB a (hA₁A ha)
  obtain ⟨g, hgc, hgA₁, hgD, hgf⟩ :=
    exists_equivariant_left_inv p hp2 Rh hs hR A₁ D hA₁inv hD f hfc hfinj
      (Disjoint.mono_right hmapB hDB)
  refine ⟨g, hgc, fun v => hA₁A (hgA₁ v), hgD, ?_⟩
  obtain ⟨v₀, hv₀A, hfv₀⟩ := hf0
  obtain ⟨c, hcA₁, hfc_eq⟩ := hdec v₀ hv₀A
  refine ⟨f c, hfAB c (hA₁A hcA₁), ?_⟩
  rw [hgf c hcA₁]
  intro hc
  apply hfv₀
  rw [← hfc_eq, hc, map_zero]

theorem exists_raising [CharP F 2] [Finite V] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (Rh : Subgroup (Equiv.Perm V)) (hs : Rh ≤ semilinGroup F V) (hR : IsPGroup p Rh)
    (Fl : ℕ → Submodule F V) (hFl0 : Fl 0 = ⊥) (hmono : Monotone Fl)
    (hinv : ∀ r ∈ Rh, ∀ k, ∀ v ∈ Fl k, r v ∈ Fl k) (W D : Submodule F V) (hFW : ∀ k, Fl k ≤ W)
    (hD : ∀ r ∈ Rh, ∀ v ∈ D, r v ∈ D) (hWD : Disjoint W D)
    (N : V →ₗ[F] V) (hN : ∀ k, ∀ v ∈ Fl (k + 1), N v ∈ Fl k)
    (hNc : ∀ r ∈ Rh, ∀ v, r (N v) = N (r v)) (hN0 : ∃ k, ∃ v ∈ Fl k, N v ≠ 0) :
    ∃ (g : V →ₗ[F] V) (k : ℕ), (∀ r ∈ Rh, ∀ v, r (g v) = g (r v)) ∧ (∀ v, g (g v) = 0) ∧
      (∀ v, g v ∈ W) ∧ (∀ v ∈ D, g v = 0) ∧ ∃ v ∈ Fl k, g v ∉ Fl k := by
  classical
  obtain ⟨k₀, hk₀, hmin⟩ : ∃ k₀, (∃ v ∈ Fl k₀, N v ≠ 0) ∧ ∀ m < k₀, ∀ v ∈ Fl m, N v = 0 :=
    ⟨Nat.find hN0, Nat.find_spec hN0, fun m hm v hv => by
      by_contra hne
      exact Nat.find_min hN0 hm ⟨v, hv, hne⟩⟩
  have hk₀ne : k₀ ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv, hne⟩ := hk₀
    rw [hFl0, Submodule.mem_bot] at hv
    exact hne (by rw [hv, map_zero])
  obtain ⟨k₁, rfl⟩ : ∃ k₁, k₀ = k₁ + 1 := ⟨k₀ - 1, by omega⟩
  have hFinv : ∀ r ∈ Rh, ∀ v ∈ Fl (k₁ + 1), r v ∈ Fl (k₁ + 1) :=
    fun r hr v hv => hinv r hr (k₁ + 1) v hv
  obtain ⟨A₁, hA₁A, hA₁inv, hNinj, hNdec⟩ :=
    exists_split_ker p hp2 Rh hs hR (Fl (k₁ + 1)) hFinv N hNc
  have hD'inv : ∀ r ∈ Rh, ∀ v ∈ A₁ ⊔ D, r v ∈ A₁ ⊔ D := by
    intro r hr v hv
    obtain ⟨a, ha, d, hd, rfl⟩ := Submodule.mem_sup.1 hv
    rw [semilin_map_add (hs hr)]
    exact Submodule.add_mem_sup (hA₁inv r hr a ha) (hD r hr d hd)
  have hdisj : Disjoint (A₁ ⊔ D) (A₁.map N) := by
    rw [Submodule.disjoint_def]
    intro x hx hxN
    obtain ⟨b, hb, hbx⟩ := Submodule.mem_map.1 hxN
    obtain ⟨a, ha, d, hd, hadx⟩ := Submodule.mem_sup.1 hx
    have hxFl : x ∈ Fl k₁ := by
      rw [← hbx]
      exact hN k₁ b (hA₁A hb)
    have haW : a ∈ W := hFW (k₁ + 1) (hA₁A ha)
    have hdW : d ∈ W := by
      have hd' : d = x - a := by
        rw [← hadx]
        abel
      rw [hd']
      exact W.sub_mem (hFW k₁ hxFl) haW
    have hd0 : d = 0 := Submodule.disjoint_def.1 hWD d hdW hd
    have hxa : x = a := by
      rw [← hadx, hd0, add_zero]
    have hNx : N x = 0 := hmin k₁ (by omega) x hxFl
    have hxA₁ : x ∈ A₁ := by
      rw [hxa]
      exact ha
    exact hNinj x hxA₁ hNx
  obtain ⟨g, hgc, hgA₁, hgD', hgN⟩ :=
    exists_equivariant_left_inv p hp2 Rh hs hR A₁ (A₁ ⊔ D) hA₁inv hD'inv N hNc hNinj hdisj
  obtain ⟨v₀, hv₀, hNv₀⟩ := hk₀
  obtain ⟨c, hcA₁, hNc_eq⟩ := hNdec v₀ hv₀
  have hNc0 : N c ≠ 0 := by
    rw [hNc_eq]
    exact hNv₀
  refine ⟨g, k₁, hgc, fun v => hgD' (g v) (Submodule.mem_sup_left (hgA₁ v)),
    fun v => hFW (k₁ + 1) (hA₁A (hgA₁ v)), fun v hv => hgD' v (Submodule.mem_sup_right hv), ?_⟩
  refine ⟨N c, hN k₁ c (hA₁A hcA₁), ?_⟩
  rw [hgN c hcA₁]
  intro hc
  exact hNc0 (hmin k₁ (by omega) c hc)

end CFSG.LieType.ChevTwo.OppCl.TK
