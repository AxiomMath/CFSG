module

public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import CFSG.CharacterTheory.Semidihedral.KleinFourOddKernel
public import CFSG.LinearAlgebra.LinearGroups.PSL2NineCoverKernelAction

public section

namespace CFSG.Semidihedral.CentralKernelTorusSplit

noncomputable section

open Matrix

theorem exists_fixed_lift {K : Type*} [Group K] [Finite K] {J E : Subgroup K} [J.Normal]
    [E.Normal] (hEJ : E ≤ J) (hEodd : Odd (Nat.card E)) {s : K} (hs : orderOf s = 2)
    {j : K} (hj : j ∈ J) (hjs : s * j * s⁻¹ * j⁻¹ ∈ E) :
    ∃ c ∈ J, c * s = s * c ∧ c⁻¹ * j ∈ E := by
  classical
  let Z := Subgroup.zpowers s
  let α : Z →* MulAut J := (MulAut.conjNormal : K →* MulAut J).comp Z.subtype
  let E' := E.subgroupOf J
  have : E'.Normal := Subgroup.normal_subgroupOf
  have hN : ∀ z : Z, ∀ n ∈ E', α z n ∈ E' := by
    intro z n hn
    change (z : K) * (n : K) * (z : K)⁻¹ ∈ E
    exact (inferInstance : E.Normal).conj_mem _ hn _
  have hZ2 : IsPGroup 2 Z :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs, pow_one])
  have hcop : ¬ 2 ∣ Nat.card E' := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEJ).toEquiv]
    exact hEodd.not_two_dvd_nat
  have hlift := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting 2 hZ2 α E' hN hcop
  have hfixed : (QuotientGroup.mk (⟨j, hj⟩ : J) : J ⧸ E') ∈
      {q : J ⧸ E' | ∀ z : Z, CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction
        α E' hN z q = q} := by
    intro z
    rw [CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk]
    rcases (CFSG.Semidihedral.KleinFourOddKernel.mem_zpowers_involution s z hs).mp z.2 with
      h1 | hzs
    · have hz1 : z = 1 := Subtype.ext h1
      rw [hz1, map_one, MulAut.one_apply]
    · apply QuotientGroup.eq.mpr
      change (((z : K) * j * (z : K)⁻¹)⁻¹ * j : K) ∈ E
      rw [hzs]
      have h := (inferInstance : E.Normal).conj_mem _ (E.inv_mem hjs) j⁻¹
      convert h using 1
      group
  rw [hlift] at hfixed
  obtain ⟨c, hc, hceq⟩ := hfixed
  have hcs : (c : K) * s = s * c := by
    have h := congrArg Subtype.val (hc ⟨s, Subgroup.mem_zpowers s⟩)
    change s * (c : K) * s⁻¹ = c at h
    calc (c : K) * s = s * c * s⁻¹ * s := by rw [h]
      _ = s * c := by group
  refine ⟨c, c.2, hcs, ?_⟩
  have h := QuotientGroup.eq.mp hceq
  exact h

theorem mem_of_pow_two_pow_eq_one {K : Type*} [Group K] [Finite K] {J N : Subgroup K}
    [J.Normal] (hcomm : ∀ x ∈ J, ∀ y ∈ N, Commute x y) (hNodd : Odd (Nat.card N))
    {d : K} (hd : d ∈ J ⊔ N) {k : ℕ} (hdk : d ^ 2 ^ k = 1) : d ∈ J := by
  obtain ⟨j, hj, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hd
  have hpow : j ^ 2 ^ k * n ^ 2 ^ k = 1 := by
    rw [← (hcomm j hj n hn).mul_pow, hdk]
  have hnJ : n ^ 2 ^ k ∈ J := by
    rw [eq_inv_of_mul_eq_one_right hpow]
    exact J.inv_mem (J.pow_mem hj _)
  have hodd : Odd (orderOf n) :=
    hNodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard N hn)
  have hgcd : (2 ^ k).gcd (orderOf n) = 1 :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have hn' : n ∈ Subgroup.zpowers (n ^ 2 ^ k) := mem_zpowers_pow_iff.mpr hgcd
  exact J.mul_mem hj (Subgroup.zpowers_le.mpr hnJ hn')

theorem inverts_kernel_of_card_nine {J : Type*} [Group J] [Finite J] [Group.IsPerfect J]
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 9)
    (π : J →* SpecialLinearGroup (Fin 2) F) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center J) (hkerodd : Odd (Nat.card π.ker))
    (t : J) (ht : t ∈ Subgroup.center J) (hπt : π t = -1)
    (hkert : π.ker ⊓ Subgroup.zpowers t = ⊥)
    (g : GL (Fin 2) F) (hg : ¬ IsSquare (g : Matrix (Fin 2) (Fin 2) F).det)
    (α : J ≃* J) (hαt : α t = t)
    (hα : ∀ x, π (α x) = CFSG.LinearGroups.slSemilinearAut g (RingEquiv.refl F) (π x)) :
    ∀ e ∈ π.ker, α e = e⁻¹ := by
  classical
  let Z := Subgroup.zpowers t
  have : Z.Normal := Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr ht)
  let q := QuotientGroup.mk' Z
  have hZker : Z ≤ (CFSG.SectionRank.OddCover.pslMk.comp π).ker := by
    rw [Subgroup.zpowers_le, MonoidHom.mem_ker, MonoidHom.comp_apply, hπt]
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [Subgroup.mem_center_iff]
    intro X
    rw [neg_one_mul, mul_neg_one]
  let ρ : J ⧸ Z →* ProjectiveSpecialLinearGroup (Fin 2) F :=
    QuotientGroup.lift Z (CFSG.SectionRank.OddCover.pslMk.comp π) hZker
  have hρ : ∀ x, ρ (q x) = CFSG.SectionRank.OddCover.pslMk (π x) := fun x => rfl
  have hρsurj : Function.Surjective ρ := by
    intro y
    obtain ⟨X, rfl⟩ := QuotientGroup.mk'_surjective _ y
    obtain ⟨x, rfl⟩ := hπ X
    exact ⟨q x, rfl⟩
  have hcenterSL : ∀ X : SpecialLinearGroup (Fin 2) F,
      CFSG.SectionRank.OddCover.pslMk X = 1 → X = 1 ∨ X = -1 := by
    intro X hX
    have hXc : X ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) :=
      (QuotientGroup.eq_one_iff X).mp hX
    have h := CFSG.LinearGroups.center_specialLinearGroup_two (F := F)
    have hmem : X ∈ ((Subgroup.center (SpecialLinearGroup (Fin 2) F) :
        Set (SpecialLinearGroup (Fin 2) F))) := hXc
    rw [h] at hmem
    simpa using hmem
  have hρker : ρ.ker ≤ π.ker.map q := by
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Z y
    rw [MonoidHom.mem_ker] at hy
    change CFSG.SectionRank.OddCover.pslMk (π x) = 1 at hy
    rcases hcenterSL _ hy with h1 | h1
    · exact ⟨x, h1, rfl⟩
    · have hqt : q t = 1 := (QuotientGroup.eq_one_iff t).mpr (Subgroup.mem_zpowers t)
      refine ⟨x * t⁻¹, ?_, ?_⟩
      · show π (x * t⁻¹) = 1
        rw [map_mul, map_inv, h1, hπt, mul_inv_cancel]
      · rw [map_mul, map_inv, hqt, inv_one, mul_one]
  have hρC : ρ.ker ≤ Subgroup.center (J ⧸ Z) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hρker hy
    exact Subgroup.map_center_le_center (QuotientGroup.mk'_surjective Z) ⟨x, hker hx, rfl⟩
  have hρodd : Odd (Nat.card ρ.ker) :=
    (hkerodd.of_dvd_nat (Subgroup.card_map_dvd π.ker q)).of_dvd_nat
      (Subgroup.card_dvd_of_le hρker)
  have hαZ : Z.map α.toMonoidHom = Z := by
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (α t) = Z
    rw [hαt]
  let α' : J ⧸ Z ≃* J ⧸ Z := QuotientGroup.congr Z Z α hαZ
  have hα'mk : ∀ x, α' (q x) = q (α x) := fun x => QuotientGroup.congr_mk Z Z α hαZ x
  have hα' : ∀ y, ρ (α' y) =
      CFSG.LinearGroups.pslSemilinearAut g (RingEquiv.refl F) (ρ y) := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Z y
    rw [hα'mk, hρ, hρ, hα, CFSG.LinearGroups.pslSemilinearAut_pslMk]
  have : Group.IsPerfect (J ⧸ Z) :=
    Group.IsPerfect.ofSurjective (f := q) (QuotientGroup.mk'_surjective Z)
  obtain ⟨-, -, -, -, hinv, -, -⟩ :=
    CFSG.LinearGroups.perfect_odd_PSL2_nine_cover_semilinear_kernel_action hF ρ hρsurj hρC
      hρodd g 0 (by norm_num) (RingEquiv.refl F) (fun x => by simp) α' hα'
  intro e he
  have hqe : q e ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, hρ, MonoidHom.mem_ker.mp he, map_one]
  have h1 : q (α e) = q e⁻¹ := by
    rw [← hα'mk, map_inv]
    exact hinv hg rfl (q e) hqe
  have h2 : (α e)⁻¹ * e⁻¹ ∈ Z := QuotientGroup.eq.mp h1
  have hαe : α e ∈ π.ker := by
    rw [MonoidHom.mem_ker, hα, MonoidHom.mem_ker.mp he, map_one]
  have h4 : (α e)⁻¹ * e⁻¹ ∈ π.ker ⊓ Z :=
    ⟨π.ker.mul_mem (π.ker.inv_mem hαe) (π.ker.inv_mem he), h2⟩
  rw [hkert, Subgroup.mem_bot, mul_eq_one_iff_eq_inv, inv_inv, inv_eq_iff_eq_inv] at h4
  exact h4

end

end CFSG.Semidihedral.CentralKernelTorusSplit
