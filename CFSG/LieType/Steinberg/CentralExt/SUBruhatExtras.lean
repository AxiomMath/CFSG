module

public import CFSG.LieType.Universal.Unitary.Extras
public import CFSG.LieType.Universal.Unitary.Extras.Unipotent
public import CFSG.LieType.Universal.Unitary.Extras.Torus
public import CFSG.LieType.Steinberg.Bruhat

public section

open Matrix CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.BorelTits
open scoped Pointwise

namespace CFSG.LieType.Steinberg.CentralExt.SUBruhat

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

variable (hF : Nat.card F = (p ^ f) ^ 2) {n : ℕ}

theorem bruhatExtras (hn : 2 ≤ n) (ζ : traceZero (unitaryInvolution F p f))
    (hζ : (ζ : F) ≠ 0) :
    BruhatExtras (rootDatum hF n) (levelTorus (unitaryInvolution F p f)) := by
  have hσ := unitaryInvolution_involutive hF
  have hct := isCTGroupDatum hF n hn ζ hζ
  refine ⟨eq_bot_iff.2 fun x hx => ?_⟩
  obtain ⟨hxB, hxN⟩ := Subgroup.mem_inf.1 hx
  rw [Subgroup.mem_bot]
  have hneg : IdBelow (lvl (-1)) 1 (mat (unitaryInvolution F p f) n x) :=
    idBelow_of_mem_iSup hσ (-1) _ (fun γ hγ => by
      have h : ht (ι := Fin (n / 2)) γ < 0 := hγ.2
      omega) hxN
  have hxB' : x ∈ (borel (rootDatum hF n) (levelTorus (unitaryInvolution F p f)) :
      Set (SU (unitaryInvolution F p f) n)) := hxB
  have hxB'' := (Set.ext_iff.1 (coe_borel hct) x).1 hxB'
  obtain ⟨t, htT, u, hu, rfl⟩ := hxB''
  obtain ⟨d, hd⟩ : ∃ d : Fin n → F, mat (unitaryInvolution F p f) n t = diagonal d :=
    Subgroup.iSup_induction (C := fun y => ∃ d : Fin n → F,
      mat (unitaryInvolution F p f) n y = diagonal d) _ htT
      (fun k y hy => exists_diagonal_of_mem_levelTorus hy)
      ⟨1, by rw [map_one]; exact diagonal_one.symm⟩ fun y z ⟨d, hd⟩ ⟨d', hd'⟩ =>
        ⟨d * d', by rw [map_mul, hd, hd', diagonal_mul_diagonal]; rfl⟩
  have hu' : IdBelow (lvl 1) 1 (mat (unitaryInvolution F p f) n u) :=
    idBelow_of_mem_iSup hσ 1 _ (fun γ hγ => by
      have h : 0 < ht (ι := Fin (n / 2)) γ := hγ.2
      omega) hu
  have hmat : mat (unitaryInvolution F p f) n (t * u) =
      diagonal d * mat (unitaryInvolution F p f) n u := by
    rw [map_mul, hd]
  refine eq_one_of_idBelow (fun a b hab => ?_) hneg
  simp only [lvl] at hab
  rw [hmat, diagonal_mul]
  rcases lt_or_eq_of_le (show b.val ≤ a.val by omega) with h | h
  · rw [hu' a b (by simp only [lvl]; omega), one_apply_ne (fun e => by rw [e] at h; omega),
      mul_zero]
  · obtain rfl : b = a := Fin.ext h
    have h1 := hneg b b (by simp only [lvl]; omega)
    rw [hmat, diagonal_mul] at h1
    exact h1

end CFSG.LieType.Steinberg.CentralExt.SUBruhat
