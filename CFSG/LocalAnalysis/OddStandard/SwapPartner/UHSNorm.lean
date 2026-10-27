module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UHSKhat
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UComp

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

open scoped commutatorElement

variable {G : Type} [Group G] {z : G} {ι ιd : Perm (Fin 10) →* G} {Kh : Subgroup G}

private theorem u_y_sq (F : UFrame z ι ιd) : yElt ιd * yElt ιd = 1 := by
  rw [yElt, ← map_mul, ← map_one ιd]
  congr 1
  decide

theorem HSCtx.conj_y_mem (C : HSCtx z ι ιd Kh) [Finite G]
    (hg : ∀ k ∈ Kh, gElt ιd * k = k * gElt ιd) {k : G} (hk : k ∈ Kh) :
    yElt ιd * k * (yElt ιd)⁻¹ ∈ Kh := by
  let y : G := yElt ιd
  let g : G := gElt ιd
  let x2 : G := z * ι τ₀
  change y * k * y⁻¹ ∈ Kh
  have hy_sq : y * y = 1 := by simpa [y] using u_y_sq C.frame
  have hy_inv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy_sq
  have hy_conj : y * x2 * y⁻¹ = g := by
    simpa [y, x2, g] using C.frame.y_conj
  have h1 : y * x2 * y = g := by simpa [hy_inv] using hy_conj
  have hygy : y * g * y = x2 := by
    calc y * g * y = y * (y * x2 * y) * y := by rw [← h1]
      _ = (y * y) * x2 * (y * y) := by group
      _ = x2 := by simp [hy_sq]
  have h_x2g : y⁻¹ * x2 * y = g := by simpa [hy_inv] using h1
  have h_gx2 : y⁻¹ * g * y = x2 := by simpa [hy_inv] using hygy
  have hgg : ∀ k ∈ Kh, g * k = k * g := fun k hk => hg k hk
  have hgk : ∀ k ∈ Kh, k * g * k⁻¹ = g := by
    intro k hk
    rw [← hgg k hk]
    group
  have hx2k : ∀ k ∈ Kh, k * x2 * k⁻¹ = x2 := by
    intro k hk
    change k * (z * ι τ₀) * k⁻¹ = z * ι τ₀
    rw [mem_centralizer_singleton_iff.mp (C.khat.le hk)]
    group
  let Ky : Subgroup G := Kh.map (MulAut.conj y).toMonoidHom
  let M : Subgroup G := centralizer ({x2} : Set G) ⊓ centralizer ({g} : Set G)
  have hKhM : Kh ≤ M := by
    intro q hq
    exact ⟨C.khat.le hq, mem_centralizer_singleton_iff.mpr (hgg q hq).symm⟩
  have hKyM : Ky ≤ M := by
    intro q hq
    rw [Subgroup.mem_map] at hq
    obtain ⟨a, ha, rfl⟩ := hq
    change (MulAut.conj y) a ∈ M
    refine ⟨?_, ?_⟩
    · refine mem_centralizer_singleton_iff.mpr ?_
      have h : (MulAut.conj y) a * x2 * ((MulAut.conj y) a)⁻¹ = x2 := by
        rw [MulAut.conj_apply]
        calc (y * a * y⁻¹) * x2 * (y * a * y⁻¹)⁻¹
            = y * a * (y⁻¹ * x2 * y) * a⁻¹ * y⁻¹ := by group
          _ = y * a * g * a⁻¹ * y⁻¹ := by rw [h_x2g]
          _ = y * (a * g * a⁻¹) * y⁻¹ := by group
          _ = y * g * y⁻¹ := by rw [hgk a ha]
          _ = x2 := by rw [hy_inv]; exact hygy
      calc (MulAut.conj y) a * x2
          = ((MulAut.conj y) a * x2 * ((MulAut.conj y) a)⁻¹) * (MulAut.conj y) a := by
            group
        _ = x2 * (MulAut.conj y) a := by rw [h]
    · refine mem_centralizer_singleton_iff.mpr ?_
      have h : (MulAut.conj y) a * g * ((MulAut.conj y) a)⁻¹ = g := by
        rw [MulAut.conj_apply]
        calc (y * a * y⁻¹) * g * (y * a * y⁻¹)⁻¹
            = y * a * (y⁻¹ * g * y) * a⁻¹ * y⁻¹ := by group
          _ = y * a * x2 * a⁻¹ * y⁻¹ := by rw [h_gx2]
          _ = y * (a * x2 * a⁻¹) * y⁻¹ := by group
          _ = y * x2 * y⁻¹ := by rw [hx2k a ha]
          _ = g := hy_conj
      calc (MulAut.conj y) a * g
          = ((MulAut.conj y) a * g * ((MulAut.conj y) a)⁻¹) * (MulAut.conj y) a := by
            group
        _ = g * (MulAut.conj y) a := by rw [h]
  have nKh : (Kh.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff hKhM).mpr fun a m ha hmM => C.conj_mem hmM.1 ha
  have nKy : (Ky.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff hKyM).mpr fun q m hq hm => by
      rw [Subgroup.mem_map] at hq
      obtain ⟨a, ha, rfl⟩ := hq
      change m * (MulAut.conj y) a * m⁻¹ ∈ Ky
      have hm2 : m * g * m⁻¹ = g := by
        rw [mem_centralizer_singleton_iff.mp hm.2]
        group
      let c : G := (MulAut.conj y) m
      have hc : c ∈ centralizer ({x2} : Set G) := by
        refine mem_centralizer_singleton_iff.mpr ?_
        have h : c * x2 * c⁻¹ = x2 := by
          change (MulAut.conj y) m * x2 * ((MulAut.conj y) m)⁻¹ = x2
          rw [MulAut.conj_apply]
          calc (y * m * y⁻¹) * x2 * (y * m * y⁻¹)⁻¹
              = y * m * (y⁻¹ * x2 * y) * m⁻¹ * y⁻¹ := by group
            _ = y * m * g * m⁻¹ * y⁻¹ := by rw [h_x2g]
            _ = y * (m * g * m⁻¹) * y⁻¹ := by group
            _ = y * g * y⁻¹ := by rw [hm2]
            _ = x2 := by rw [hy_inv]; exact hygy
        calc c * x2
            = (c * x2 * c⁻¹) * c := by group
          _ = x2 * c := by rw [h]
      have hca : c * a * c⁻¹ ∈ Kh := C.conj_mem hc ha
      have hconj_sq : (MulAut.conj y) * (MulAut.conj y) = 1 := by
        rw [← map_mul, hy_sq, map_one]
      have hconj_invol : (MulAut.conj y) c = m := by
        have hh := congrArg (fun f : MulAut G => f m) hconj_sq
        simpa [c] using hh
      have hgoal : m * (MulAut.conj y) a * m⁻¹ = (MulAut.conj y) (c * a * c⁻¹) := by
        rw [← hconj_invol, ← map_mul, ← map_inv, ← map_mul]
      rw [hgoal]
      exact Subgroup.mem_map_of_mem (MulAut.conj y).toMonoidHom hca
  have qKy : CFSG.IsQuasisimple ↥Ky :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Kh.equivMapOfInjective (MulAut.conj y).toMonoidHom (MulAut.conj y).injective)
      C.isQuasisimple
  rcases eq_or_commute_of_normal_quasisimple hKyM hKhM nKy nKh qKy C.isQuasisimple with
    hEq | hComm
  · have hmem : (MulAut.conj y) k ∈ Ky := Subgroup.mem_map_of_mem _ hk
    rw [hEq] at hmem
    simpa only [MulAut.conj_apply] using hmem
  · exfalso
    have hKy_cent : Ky ≤ centralizer (Kh : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hComm
    obtain ⟨Q0, hQ0card⟩ :=
      Sylow.exists_subgroup_card_pow_prime (G := ↥Kh) 2 C.two_pow_nine_dvd_card
    let Q : Subgroup G := Q0.map Kh.subtype
    have hQcard : Nat.card Q = 2 ^ 9 := by
      rw [Subgroup.card_subtype, hQ0card]
    have hQp : IsPGroup 2 Q := IsPGroup.of_card hQcard
    let Q' : Subgroup G := Q.map (MulAut.conj y).toMonoidHom
    have hQ'card : Nat.card Q' = 2 ^ 9 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj y).injective, hQcard]
    have hQ'p : IsPGroup 2 Q' := hQp.map (MulAut.conj y).toMonoidHom
    have hQ'leKy : Q' ≤ Ky := Subgroup.map_mono (Subgroup.map_subtype_le Q0)
    have hQ'A : Q' ≤ centralizer (Agrp ι : Set G) :=
      hQ'leKy.trans (hKy_cent.trans (Subgroup.centralizer_le C.khat.agrp_le))
    have hQ'x2 : Q' ≤ centralizer ({x2} : Set G) :=
      hQ'leKy.trans (hKyM.trans inf_le_left)
    have hle8 := C.h8 Q' hQ'p hQ'A hQ'x2
    rw [hQ'card] at hle8
    norm_num at hle8

end CFSG.OddStandard.AltStdSec.SwapPartner
