module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.SL2BoundGrp
public import CFSG.GH74.GLS.SP.Local.SPLFitA
public import CFSG.GH74.GLS.Stage2.Local.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2012

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final.Thm6.SL2Bound

section Fit

variable {G : Type} [Group G] [Finite G]

theorem fit_G {K : Subgroup G} {r : ℕ} (hr : Odd r) (hr3 : 3 < r) (hm : HasSL2Model ↥K (fun q => q = r))
    {a : G} (ha : a ∈ K) (ha2 : a * a ≠ 1) (hsq : ∀ c ∈ K, c * (a * a) = (a * a) * c)
    (M : Subgroup G) (hMN : M ≤ normalizer (K : Set G))
    (hM : ∀ m ∈ M, ∀ c ∈ K, c * (m * a * m⁻¹ * a⁻¹) = (m * a * m⁻¹ * a⁻¹) * c)
    (W : Subgroup G) (hWM : W ≤ M) (hWodd : Odd (Nat.card ↥W))
    (hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)
    (hX : ∀ k ∈ K, Odd (orderOf k) → k * a = a * k →
      ∃ m ∈ M, (∀ x ∈ K, m * x * m⁻¹ = k * x * k⁻¹) ∧ ∀ w ∈ W, m * w * m⁻¹ ∈ W) :
    ∀ w ∈ W, ∃ k ∈ K, Odd (orderOf k) ∧ k * a = a * k ∧ ∀ x ∈ K, w * x * w⁻¹ = k * x * k⁻¹ := by
  obtain ⟨F, hF, hFin, hq, ⟨e⟩⟩ := hm
  have hq' : Nat.card F = r := hq
  have hL2 : CFSG.GH74.GLS.IVK.L2Field F := ⟨hq' ▸ hr, hq' ▸ hr3⟩
  let u₁ : ↥K := ⟨a, ha⟩
  have hu₁c : u₁ ^ 2 ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro c
    apply Subtype.ext
    simpa [u₁, pow_two] using hsq c.1 c.2
  have hu₁1 : u₁ ^ 2 ≠ 1 := by
    intro h
    apply ha2
    have := congrArg Subtype.val h
    simpa [u₁, pow_two] using this
  let α : ↥M →* MulAut ↥K :=
    MonoidHom.mk' (fun m => conjAut K (m : G) (hMN m.2)) (fun m m' => by
      ext k
      simp [conjAut_apply, mul_assoc])
  have hα : ∀ m : ↥M, α m u₁ * u₁⁻¹ ∈ Subgroup.center ↥K := by
    intro m
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    simpa [α, u₁, conjAut_apply] using hM m.1 m.2 g.1 g.2
  have hWodd' : Odd (Nat.card ↥(W.subgroupOf M)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWM).toEquiv]
  have hWab' : ∀ x ∈ W.subgroupOf M, ∀ y ∈ W.subgroupOf M, x * y = y * x := by
    intro x hx y hy
    apply Subtype.ext
    exact hWab x.1 hx y.1 hy
  have hX' : ∀ k : ↥K, Odd (orderOf k) → k * u₁ = u₁ * k →
      ∃ m : ↥M, α m = MulAut.conj k ∧ ∀ w ∈ W.subgroupOf M, m * w * m⁻¹ ∈ W.subgroupOf M := by
    intro k hk hkc
    have hko : Odd (orderOf (k : G)) := by rwa [Subgroup.orderOf_coe]
    have hka : (k : G) * a = a * k := by
      have := congrArg Subtype.val hkc
      simpa [u₁] using this
    obtain ⟨m, hmM, hmx, hmW⟩ := hX k.1 k.2 hko hka
    refine ⟨⟨m, hmM⟩, ?_, ?_⟩
    · ext x
      have := hmx x.1 x.2
      simpa [α, conjAut_apply] using this
    · intro w hw
      rw [Subgroup.mem_subgroupOf] at hw ⊢
      exact hmW w.1 hw
  have hmain := CFSG.GH74.GLS.SP.Local.spl_fit_A1 F hL2 ↥K e u₁ hu₁c hu₁1 ↥M α hα
    (W.subgroupOf M) hWodd' hWab' hX'
  intro w hw
  obtain ⟨k, hkodd, hkc, hαk⟩ := hmain ⟨w, hWM hw⟩ (by rw [Subgroup.mem_subgroupOf]; exact hw)
  refine ⟨k.1, k.2, ?_, ?_, ?_⟩
  · rwa [Subgroup.orderOf_coe]
  · have := congrArg Subtype.val hkc
    simpa [u₁] using this
  · intro x hx
    have := congrArg (fun φ => ((φ ⟨x, hx⟩ : ↥K) : G)) hαk
    simpa [α, conjAut_apply] using this

end Fit

section Cyc

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem isCyclic_centralizer_sq [Finite F] {Q : Type} [Group Q] (e : Q ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hodd : Odd (Nat.card F)) {a : Q} (ha : a * a ∈ center Q) (hna : a ∉ center Q) :
    IsCyclic ↥(centralizer ({a} : Set Q)) := by
  have hea := sq_eq_minusIdentity e hodd ha hna
  obtain ⟨hcyc, -, -⟩ := IVK.L2Torus.centralizer_cyclic_card hodd (e a) hea
  have h : (centralizer ({a} : Set Q)).map e.toMonoidHom = centralizer ({e a} : Set (Matrix.SpecialLinearGroup (Fin 2) F)) := by
    ext x
    rw [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hy
      show e y * e a = e a * e y
      rw [← map_mul, ← map_mul, hy]
    · intro hx
      refine ⟨e.symm x, ?_, by simp⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hx
  rw [← h] at hcyc
  exact (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).isCyclic.2 hcyc

end Cyc

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2012
