module

public import CFSG.LargeExtraspecial.AS35ZSNtA
public import CFSG.LargeExtraspecial.AS35ZMOrth

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35ZS

open Module CFSG.RankThree.OrthogonalInvolutions CFSG.Fischer.Classification.Unitary
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary QuadraticMap
open CFSG.Blueprint.Fischer (K)

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : PG n →* (V ≃ₗ[ZMod 2] V)} {q : QuadraticForm (ZMod 2) V}

noncomputable abbrev blkAt (ρ : PG n →* (V ≃ₗ[ZMod 2] V)) (b : ℕ) : Submodule (ZMod 2) V :=
  if hb : b + 1 < n then blk ρ ⟨b, by omega⟩ ⟨b + 1, hb⟩ else ⊥

@[expose] noncomputable def Ysum (ρ : PG n →* (V ≃ₗ[ZMod 2] V)) (a : ℕ) :
    ℕ → Submodule (ZMod 2) V
  | 0 => ⊥
  | l + 1 => Ysum ρ a l ⊔ blkAt ρ (a + 2 * l)

theorem Ysum_zero (a : ℕ) : Ysum ρ a 0 = ⊥ := rfl

theorem Ysum_succ (a l : ℕ) : Ysum ρ a (l + 1) = Ysum ρ a l ⊔ blkAt ρ (a + 2 * l) := rfl

theorem blkAt_eq {b : ℕ} (hb : b + 1 < n) : blkAt ρ b = blk ρ ⟨b, by omega⟩ ⟨b + 1, hb⟩ := by
  rw [blkAt, dite_eq_left hb]

theorem le_orth_sup {X A B : Submodule (ZMod 2) V}
    (hA : X ≤ LinearMap.BilinForm.orthogonal (polarBilin q) A)
    (hB : X ≤ LinearMap.BilinForm.orthogonal (polarBilin q) B) :
    X ≤ LinearMap.BilinForm.orthogonal (polarBilin q) (A ⊔ B) := by
  intro v hv
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro w hw
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw
  have h1 := LinearMap.BilinForm.mem_orthogonal_iff.1 (hA hv) a ha
  have h2 := LinearMap.BilinForm.mem_orthogonal_iff.1 (hB hv) b hb
  show polar q (a + b) v = 0
  rw [polar_add_left]
  change polar q a v = 0 at h1
  change polar q b v = 0 at h2
  rw [h1, h2, add_zero]

namespace ZSHyp

variable [FiniteDimensional (ZMod 2) V] (h : ZSHyp n q ρ)
include h

theorem Ysum_props (a : ℕ) : ∀ l : ℕ, a + 2 * l ≤ n →
    Ysum ρ a l ⊓ LinearMap.BilinForm.orthogonal (polarBilin q) (Ysum ρ a l) = ⊥ ∧
      finrank (ZMod 2) (Ysum ρ a l) = 4 * l ∧
      ∀ b : ℕ, a + 2 * l ≤ b → b + 1 < n →
        blkAt ρ b ≤ LinearMap.BilinForm.orthogonal (polarBilin q) (Ysum ρ a l) := by
  intro l
  induction l with
  | zero =>
    intro _
    refine ⟨by simp [Ysum_zero], by rw [Ysum_zero, finrank_bot], fun b _ _ => ?_⟩
    rw [Ysum_zero]
    intro v _
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    rw [Submodule.mem_bot] at hw
    rw [hw]
    show polar q 0 v = 0
    exact polar_zero_left _ v
  | succ l ih =>
    intro hal
    obtain ⟨hnd, hdim, horth⟩ := ih (by omega)
    have hb1 : a + 2 * l + 1 < n := by omega
    have hblk := blkAt_eq (ρ := ρ) hb1
    have hij : (⟨a + 2 * l, by omega⟩ : Fin n) ≠ ⟨a + 2 * l + 1, hb1⟩ := by simp [Fin.ext_iff]
    have hnew := horth (a + 2 * l) le_rfl hb1
    rw [hblk] at hnew
    obtain ⟨hnd', hdim'⟩ := AS35ZM.nondeg_sup q hnd (h.nondeg_blk hij) hnew
    refine ⟨?_, ?_, fun b hb hbn => ?_⟩
    · rw [Ysum_succ, hblk]
      exact hnd'
    · rw [Ysum_succ, hblk, hdim', hdim, h.finrank_blk hij]
      ring
    · rw [Ysum_succ]
      refine le_orth_sup (horth b (by omega) hbn) ?_
      rw [blkAt_eq hbn, hblk]
      exact h.blk_le_orth hij (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]; omega)
        (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega)
        (by simp [Fin.ext_iff]; omega)

theorem lineA_le_orth_Ysum (a : ℕ) {x : Fin n → K} (hx0 : x ≠ 0) (hx : herm frob x x = 0)
    (hsupp : ∀ i : Fin n, a ≤ (i : ℕ) → x i = 0) : ∀ l : ℕ,
    lineA ρ x ≤ LinearMap.BilinForm.orthogonal (polarBilin q) (Ysum ρ a l) := by
  intro l
  induction l with
  | zero =>
    intro v _
    rw [Ysum_zero, LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    rw [Submodule.mem_bot] at hw
    rw [hw]
    show polar q 0 v = 0
    exact polar_zero_left _ v
  | succ l ih =>
    rw [Ysum_succ]
    refine le_orth_sup ih ?_
    by_cases hb : a + 2 * l + 1 < n
    · rw [blkAt_eq hb]
      have hij : (⟨a + 2 * l, by omega⟩ : Fin n) ≠ ⟨a + 2 * l + 1, hb⟩ := by
        simp [Fin.ext_iff]
      have hperp : ∀ c : K, herm frob x (pp ⟨a + 2 * l, by omega⟩ ⟨a + 2 * l + 1, hb⟩ c) = 0 :=
        fun c => by
          rw [herm_add_right, herm_single_right, herm_single_right,
            hsupp _ (by simp), hsupp _ (by simp; omega)]
          simp
      refine le_orth_of_polar fun v hv w hw => ?_
      obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := Submodule.mem_sup.1 hw
      rw [polar_add_right,
        h.polar_eq_zero_of_perp hx0 hx (pp_ne_zero hij 1) (pp_iso hij one_ne_zero) (hperp 1)
          hv hb₁,
        h.polar_eq_zero_of_perp hx0 hx (pp_ne_zero hij ω) (pp_iso hij omega_ne_zero) (hperp ω)
          hv hb₂, add_zero]
    · rw [blkAt, dite_eq_right hb]
      intro v _
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro w hw
      rw [Submodule.mem_bot] at hw
      rw [hw]
      show polar q 0 v = 0
      exact polar_zero_left _ v

theorem Ysum_apply_eq_self (H₀ : ∀ x : IsoVec n, ∀ a ∈ lineA ρ x.1, oLine ρ x.1 a = a)
    {g : SUid frob n} (hg3 : g ^ 3 = 1) (a : ℕ)
    (hg : ∀ l : ℕ, (hb : a + 2 * l + 1 < n) → ∃ μ : K, μ ≠ 0 ∧ ∀ c : K,
      g • pp ⟨a + 2 * l, by omega⟩ ⟨a + 2 * l + 1, hb⟩ c =
        μ • pp ⟨a + 2 * l, by omega⟩ ⟨a + 2 * l + 1, hb⟩ c) :
    ∀ l : ℕ, ∀ v ∈ Ysum ρ a l, rs ρ g v = v := by
  intro l
  induction l with
  | zero =>
    intro v hv
    rw [Ysum_zero, Submodule.mem_bot] at hv
    rw [hv, map_zero]
  | succ l ih =>
    intro v hv
    rw [Ysum_succ] at hv
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add, ih y hy]
    congr 1
    by_cases hb : a + 2 * l + 1 < n
    · rw [blkAt_eq hb] at hz
      obtain ⟨μ, hμ, hgμ⟩ := hg l hb
      exact h.blk_apply_eq_self H₀ (by simp [Fin.ext_iff]) hg3 hμ hgμ hz
    · rw [blkAt, dite_eq_right hb, Submodule.mem_bot] at hz
      rw [hz, map_zero]

end ZSHyp

end CFSG.LargeExtraspecial.AS35ZS
