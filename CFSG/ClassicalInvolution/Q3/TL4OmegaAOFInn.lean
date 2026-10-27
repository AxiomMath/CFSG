module

public import CFSG.ClassicalInvolution.Q3.Q3NMAut
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBasic

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Q3.Q3NM

variable {P : Type} [Group P] [Finite P]

theorem oddCoreIn_fixed_eq_bot_of_inn
    (hinj : Function.Injective (MulAut.conj : P →* MulAut P)) (t : MulAut P)
    (h : CFSG.ComponentClassification.Burgoyne.oddCoreIn (MulAut.conj : P →* MulAut P).range t =
      ⊥) : oddCoreIn (fixedSubgroup t) = ⊥ := by
  classical
  set D := (MulAut.conj : P →* MulAut P).range ⊓ Subgroup.centralizer ({t} : Set (MulAut P))
    with hD
  set N := oddCoreIn (fixedSubgroup t) with hN
  have hcomm : ∀ x : P, t x = x → MulAut.conj x * t = t * MulAut.conj x := fun x hx =>
    MulEquiv.ext fun y => by simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hx]
  have hfix : ∀ y : P, MulAut.conj y * t = t * MulAut.conj y → t y = y := by
    intro y hy
    apply hinj
    ext w
    obtain ⟨z, rfl⟩ := t.surjective w
    have := congrArg (fun f : MulAut P => f z) hy
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv] at this
    simp only [MulAut.conj_apply]
    exact this.symm
  have hND : ∀ x ∈ N, MulAut.conj x ∈ D := fun x hx =>
    Subgroup.mem_inf.2 ⟨⟨x, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2
      (hcomm x (Q3NM.mem_fixedSubgroup_iff.1 (oddCoreIn_le _ hx)))⟩
  set K := (N.map (MulAut.conj : P →* MulAut P)).subgroupOf D with hK
  have hKn : K.Normal := by
    refine ⟨fun k hk d => ?_⟩
    rw [hK, Subgroup.mem_subgroupOf] at hk ⊢
    obtain ⟨x, hx, hxk⟩ := hk
    obtain ⟨⟨y, hy⟩, hyc⟩ := Subgroup.mem_inf.1 d.2
    have hyt : t y = y :=
      hfix y (by rw [hy]; exact Subgroup.mem_centralizer_singleton_iff.1 hyc)
    refine ⟨y * x * y⁻¹, conj_mem_oddCoreIn (Q3NM.mem_fixedSubgroup_iff.2 hyt) hx, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hy, hxk]
  have hKodd : Nat.Coprime 2 (Nat.card K) := by
    rw [Nat.coprime_two_left]
    have hle : N.map (MulAut.conj : P →* MulAut P) ≤ D := by
      rintro _ ⟨x, hx, rfl⟩
      exact hND x hx
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      Subgroup.card_map_of_injective hinj]
    exact odd_card_oddCoreIn _
  have hKle : K ≤ CFSG.pPrimeCore 2 D := le_sSup ⟨hKn, hKodd⟩
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have h1 : MulAut.conj x ∈
      CFSG.ComponentClassification.Burgoyne.oddCoreIn (MulAut.conj : P →* MulAut P).range t :=
    ⟨⟨MulAut.conj x, hND x hx⟩, hKle (Subgroup.mem_subgroupOf.2 ⟨x, hx, rfl⟩), rfl⟩
  rw [h, Subgroup.mem_bot] at h1
  exact hinj (by rw [h1, map_one])

end CFSG.ClassicalInvolution.Q3.TL4
