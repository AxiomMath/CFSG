module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888End4a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888YPl

public section

open CFSG.Open CFSG.Goldschmidt CFSG.GH74.GLS.Th2.P412 Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

private theorem s888_psiAut_mul {X : Type} [Group X] {M : Subgroup X} [M.Normal] (g h : X) :
    psiAut M (g * h) = psiAut M g * psiAut M h := by
  apply MulEquiv.ext
  intro y
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (goldschmidtOddCore ↥M) y
  simp only [QuotientGroup.mk'_apply, psiAut_mk, MulAut.mul_apply]
  congr 1
  exact Subtype.ext (by rw [map_mul]; rfl)

private theorem s888_psiAut_one {X : Type} [Group X] {M : Subgroup X} [M.Normal] :
    psiAut M (1 : X) = 1 := by
  ext y
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (goldschmidtOddCore ↥M) y
  simp [psiAut_mk]

private theorem s888_psiAut_pow {X : Type} [Group X] {M : Subgroup X} [M.Normal] (g : X)
    (n : ℕ) : psiAut M (g ^ n) = psiAut M g ^ n := by
  induction n with
  | zero => simpa using s888_psiAut_one (M := M)
  | succ n ih => rw [pow_succ, s888_psiAut_mul, ih, pow_succ]

theorem mbarMk_injOn_V {X : Type} [Group X] [Finite X] {S : Sylow 2 X} {V : Subgroup X}
    {W : Fin 4 → Subgroup X} {ρ : Fin 4 → X} (hX : XData S V W ρ) {M : Subgroup X}
    (hVM : V ≤ M) (hB : IsCaseB S V M) :
    ∀ x ∈ V.subgroupOf M, ∀ y ∈ V.subgroupOf M, mbarMk M x = mbarMk M y → x = y := by
  intro x hx y hy hxy
  exact hB.inj x (Subgroup.mem_subgroupOf.mpr (hX.le_S (Subgroup.mem_subgroupOf.mp hx)))
    y (Subgroup.mem_subgroupOf.mpr (hX.le_S (Subgroup.mem_subgroupOf.mp hy))) hxy

theorem isPlanes_image {X : Type} [Group X] [Finite X] {S : Sylow 2 X} {V : Subgroup X}
    {W : Fin 4 → Subgroup X} {ρ : Fin 4 → X} (hX : XData S V W ρ) {M : Subgroup X} [M.Normal]
    (hVM : V ≤ M) (hB : IsCaseB S V M) :
    IsPlanes ((V.subgroupOf M).map (mbarMk M))
      (fun i => ((W i).subgroupOf M).map (mbarMk M)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
    have hxV : (x : X) ∈ V := Subgroup.mem_subgroupOf.mp hx
    have hyV : (y : X) ∈ V := Subgroup.mem_subgroupOf.mp hy
    have hxy : (x * y : ↥M) = y * x :=
      Subtype.ext (by simpa using hX.comm (x : X) hxV (y : X) hyV)
    rw [← map_mul, ← map_mul, hxy]
  · intro a ha
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    have hxV : (x : X) ∈ V := Subgroup.mem_subgroupOf.mp hx
    have hxx : (x * x : ↥M) = 1 :=
      Subtype.ext (by simpa using hX.sq (x : X) hxV)
    rw [← map_mul, hxx, map_one]
  · rw [card_map_eq_of_injOn (mbarMk M) (V.subgroupOf M) (mbarMk_injOn_V hX hVM hB)]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVM).toEquiv, hX.planes.card_V]
  · intro i
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono M (hX.planes.le i))
  · intro i
    rw [card_map_eq_of_injOn (mbarMk M) ((W i).subgroupOf M) ?_]
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_trans (hX.planes.le i) hVM)).toEquiv,
        hX.planes.card i]
    · intro a ha b hb hab
      exact mbarMk_injOn_V hX hVM hB a
        (Subgroup.mem_subgroupOf.mpr
          (hX.planes.le i (Subgroup.mem_subgroupOf.mp ha))) b
        (Subgroup.mem_subgroupOf.mpr
          (hX.planes.le i (Subgroup.mem_subgroupOf.mp hb))) hab
  · intro d hd
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hd
    have hxV : (x : X) ∈ V := Subgroup.mem_subgroupOf.mp hx
    obtain ⟨w, hw, hwx⟩ := hX.planes.decomp (x : X) hxV
    let w' : Fin 4 → ↥M := fun i => ⟨w i, hVM (hX.planes.le i (hw i))⟩
    refine ⟨fun i => mbarMk M (w' i), ?_, ?_⟩
    · intro i
      exact Subgroup.mem_map.mpr ⟨w' i, Subgroup.mem_subgroupOf.mpr (hw i), rfl⟩
    · have hprod : w' 0 * w' 1 * w' 2 * w' 3 = x := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subtype.coe_mk, w']
        exact hwx.symm
      calc
        mbarMk M x = mbarMk M (w' 0 * w' 1 * w' 2 * w' 3) := by rw [hprod]
        _ = mbarMk M (w' 0) * mbarMk M (w' 1) * mbarMk M (w' 2) * mbarMk M (w' 3) := by
              rw [map_mul, map_mul, map_mul]

theorem isPlaneAuts_psi {X : Type} [Group X] [Finite X] {S : Sylow 2 X} {V : Subgroup X}
    {W : Fin 4 → Subgroup X} {ρ : Fin 4 → X} (hX : XData S V W ρ) {M : Subgroup X} [M.Normal]
    (hVM : V ≤ M) (hB : IsCaseB S V M) :
    IsPlaneAuts ((V.subgroupOf M).map (mbarMk M))
      (fun i => ((W i).subgroupOf M).map (mbarMk M)) (fun i => psiAut M (ρ i)) := by
  have h3g : ∀ i, (ρ i) ^ 3 = 1 := by
    intro i
    have h := pow_orderOf_eq_one (ρ i)
    rwa [hX.planes.rho_order i] at h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i y
    have h3 : psiAut M (ρ i) ^ 3 = 1 := by
      rw [← s888_psiAut_pow, h3g i]
      exact s888_psiAut_one
    have := congrArg (fun e : Mbar M ≃* Mbar M => e y) h3
    simpa [pow_succ, pow_two, MulAut.mul_apply] using this
  · intro i d hd
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hd
    have hmV : (m : X) ∈ V := Subgroup.mem_subgroupOf.mp hm
    have hconjV : ((MulAut.conjNormal (ρ i) m : ↥M) : X) ∈ V := by
      rw [MulAut.conjNormal_apply]
      exact (Subgroup.mem_set_normalizer_iff.mp (hX.planes.rho_mem i) (m : X)).mp hmV
    change psiAut M (ρ i) (QuotientGroup.mk m) ∈ (V.subgroupOf M).map (mbarMk M)
    rw [psiAut_mk]
    exact Subgroup.mem_map.mpr ⟨MulAut.conjNormal (ρ i) m,
      Subgroup.mem_subgroupOf.mpr hconjV, rfl⟩
  · intro i w hw
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hw
    have hmW : (m : X) ∈ W i := Subgroup.mem_subgroupOf.mp hm
    have hconjW : ((MulAut.conjNormal (ρ i) m : ↥M) : X) ∈ W i := by
      rw [MulAut.conjNormal_apply]
      exact hX.planes.rho_inv i (m : X) hmW
    change psiAut M (ρ i) (QuotientGroup.mk m) ∈ ((W i).subgroupOf M).map (mbarMk M)
    rw [psiAut_mk]
    exact Subgroup.mem_map.mpr ⟨MulAut.conjNormal (ρ i) m,
      Subgroup.mem_subgroupOf.mpr hconjW, rfl⟩
  · intro i j hij w hw
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hw
    have hmW : (m : X) ∈ W j := Subgroup.mem_subgroupOf.mp hm
    change psiAut M (ρ i) (QuotientGroup.mk m) = QuotientGroup.mk m
    rw [psiAut_mk]
    congr 1
    exact Subtype.ext (by
      rw [MulAut.conjNormal_apply, hX.planes.rho_triv i j hij (m : X) hmW]
      simp)
  · intro i w hw hw1 hfix
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hw
    have hmW : (m : X) ∈ W i := Subgroup.mem_subgroupOf.mp hm
    have hm1 : (m : X) ≠ 1 := by
      intro h
      apply hw1
      rw [show (m : ↥M) = 1 from Subtype.ext h, map_one]
    change psiAut M (ρ i) (QuotientGroup.mk m) = QuotientGroup.mk m at hfix
    rw [psiAut_mk] at hfix
    have hconjW : ((MulAut.conjNormal (ρ i) m : ↥M) : X) ∈ W i := by
      rw [MulAut.conjNormal_apply]
      exact hX.planes.rho_inv i (m : X) hmW
    have heq : MulAut.conjNormal (ρ i) m = m :=
      mbarMk_injOn_V hX hVM hB (MulAut.conjNormal (ρ i) m)
        (Subgroup.mem_subgroupOf.mpr (hX.planes.le i hconjW)) m
        (Subgroup.mem_subgroupOf.mpr (hX.planes.le i hmW)) hfix
    have hXeq : ρ i * (m : X) * (ρ i)⁻¹ = (m : X) := by
      have := congrArg Subtype.val heq
      simpa [MulAut.conjNormal_apply] using this
    exact hX.planes.rho_fpf i (m : X) hmW hm1 hXeq

end CFSG.OddStandard.SmallF3.Omega
