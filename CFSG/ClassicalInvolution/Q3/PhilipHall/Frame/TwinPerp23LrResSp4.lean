module

public import CFSG.Open.StatedAPI
import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
import CFSG.LocalAnalysis.SignalizerFunctor.TwoPrimeOrderSolvability

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Lc.Res

open Matrix CFSG.Open

private abbrev M4 := Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3)

private def jM : M4 := fromBlocks 0 1 (-1) 0

private def xM : M4 := fromBlocks !![0, 0; 2, 2] !![2, 1; 1, 0] !![0, 2; 0, 0] !![0, 0; 2, 0]

private theorem xM_symp : xMᵀ * jM * xM = jM := by decide +kernel

private theorem xM_pow_five : xM ^ 5 = 1 := by decide +kernel

private theorem xM_ne_one : xM ≠ 1 := by decide +kernel

private def vv : Fin 2 ⊕ Fin 2 → ZMod 3 := fun i => if i = Sum.inl 0 then 1 else 0

private def u1 : Fin 2 ⊕ Fin 2 → ZMod 3 := xM *ᵥ vv

private def u2 : Fin 2 ⊕ Fin 2 → ZMod 3 := xM *ᵥ u1

private def u3 : Fin 2 ⊕ Fin 2 → ZMod 3 := xM *ᵥ u2

private theorem span_all : ∀ w : Fin 2 ⊕ Fin 2 → ZMod 3,
    ∃ a b c d : ZMod 3, w = a • vv + b • u1 + c • u2 + d • u3 := by decide +kernel

private def poly (a b c d : ZMod 3) : M4 := a • 1 + b • xM + c • (xM * xM) + d • (xM * xM * xM)

private theorem core81 : ∀ a b c d : ZMod 3, (poly a b c d)ᵀ * jM * poly a b c d = jM →
    (∃ r : ZMod 3, poly a b c d * poly a b c d = r • 1) → ∃ s : ZMod 3, poly a b c d = s • 1 := by
  decide +kernel

private theorem poly_comm : ∀ a b c d : ZMod 3, poly a b c d * xM = xM * poly a b c d := by
  decide +kernel

private theorem poly_mulVec : ∀ a b c d : ZMod 3,
    poly a b c d *ᵥ vv = a • vv + b • u1 + c • u2 + d • u3 := by
  decide +kernel

private theorem comm_poly {Y : M4} (hY : Y * xM = xM * Y) :
    ∃ a b c d : ZMod 3, Y = poly a b c d := by
  obtain ⟨a, b, c, d, hw⟩ := span_all (Y *ᵥ vv)
  refine ⟨a, b, c, d, ?_⟩
  have hv : Y *ᵥ vv = poly a b c d *ᵥ vv := by rw [poly_mulVec]; exact hw
  have hYc : ∀ w, Y *ᵥ (xM *ᵥ w) = xM *ᵥ (Y *ᵥ w) := fun w => by
    rw [Matrix.mulVec_mulVec, hY, ← Matrix.mulVec_mulVec]
  have hPc : ∀ w, poly a b c d *ᵥ (xM *ᵥ w) = xM *ᵥ (poly a b c d *ᵥ w) := fun w => by
    rw [Matrix.mulVec_mulVec, poly_comm, ← Matrix.mulVec_mulVec]
  have h1 : Y *ᵥ u1 = poly a b c d *ᵥ u1 := by
    show Y *ᵥ (xM *ᵥ vv) = poly a b c d *ᵥ (xM *ᵥ vv)
    rw [hYc, hPc, hv]
  have h2 : Y *ᵥ u2 = poly a b c d *ᵥ u2 := by
    show Y *ᵥ (xM *ᵥ u1) = poly a b c d *ᵥ (xM *ᵥ u1)
    rw [hYc, hPc, h1]
  have h3 : Y *ᵥ u3 = poly a b c d *ᵥ u3 := by
    show Y *ᵥ (xM *ᵥ u2) = poly a b c d *ᵥ (xM *ᵥ u2)
    rw [hYc, hPc, h2]
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro w
  obtain ⟨a', b', c', d', rfl⟩ := span_all w
  simp only [Matrix.toLin'_apply, Matrix.mulVec_add, Matrix.mulVec_smul, hv, h1, h2, h3]

private theorem core {Y : M4} (hY : Y * xM = xM * Y) (hs : Yᵀ * jM * Y = jM)
    (hr : ∃ r : ZMod 3, Y * Y = r • 1) : ∃ s : ZMod 3, Y = s • 1 := by
  obtain ⟨a, b, c, d, rfl⟩ := comm_poly hY
  exact core81 a b c d hs hr

private def matSp (g : StatedSp 2 (ZMod 3)) : M4 := ((g : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) : M4)

private theorem matSp_mul (g h : StatedSp 2 (ZMod 3)) : matSp (g * h) = matSp g * matSp h := rfl

private theorem matSp_symp (g : StatedSp 2 (ZMod 3)) : (matSp g)ᵀ * jM * matSp g = jM :=
  CFSG.Open.StatedAPI.mem_statedSp_iff.mp g.2

private theorem matSp_injective : Function.Injective matSp := fun _ _ h =>
  Subtype.ext (Units.ext h)

private def x0GL : GL (Fin 2 ⊕ Fin 2) (ZMod 3) :=
  ⟨xM, xM ^ 4, by rw [← pow_succ']; exact xM_pow_five, by rw [← pow_succ]; exact xM_pow_five⟩

private theorem x0GL_mem : x0GL ∈ StatedSp 2 (ZMod 3) :=
  CFSG.Open.StatedAPI.mem_statedSp_iff.mpr xM_symp

private def x0 : StatedSp 2 (ZMod 3) := ⟨x0GL, x0GL_mem⟩

private theorem matSp_x0 : matSp x0 = xM := rfl

private theorem orderOf_x0 : orderOf x0 = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h5 : x0 ^ 5 = 1 := by
    apply matSp_injective
    rw [show matSp (x0 ^ 5) = matSp x0 ^ 5 from by
      induction 5 with
      | zero => rfl
      | succ n ih => rw [pow_succ, pow_succ, matSp_mul, ih]]
    rw [matSp_x0, xM_pow_five]
    rfl
  exact orderOf_eq_prime h5 (fun h => xM_ne_one (by rw [← matSp_x0, h]; rfl))

private theorem exists_scalar_of_mem_center {g : StatedSp 2 (ZMod 3)}
    (hg : g ∈ Subgroup.center (StatedSp 2 (ZMod 3))) : ∃ r : ZMod 3, matSp g = r • 1 := by
  have hsp := CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic (n := 2) (K := ZMod 3)
  have hmem : (⟨(g : GL (Fin 2 ⊕ Fin 2) (ZMod 3)), by rw [← hsp]; exact g.2⟩ :
      TauCeti.GLSymplectic (Fin 2) (ZMod 3)) ∈
      Subgroup.center (TauCeti.GLSymplectic (Fin 2) (ZMod 3)) := by
    rw [Subgroup.mem_center_iff]
    intro h
    have h' : (h : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) ∈ StatedSp 2 (ZMod 3) := by rw [hsp]; exact h.2
    have := Subgroup.mem_center_iff.1 hg ⟨h, h'⟩
    apply Subtype.ext
    have h3 := congrArg Subtype.val this
    simpa using h3
  rw [CFSG.ClassicalGroups.Symplectic.center_GLSymplectic_eq, Subgroup.mem_subgroupOf] at hmem
  obtain ⟨c, hc⟩ := hmem
  refine ⟨(c : ZMod 3), ?_⟩
  have h1 : (g : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) =
      Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c := hc.symm
  change ((g : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) : M4) = _
  rw [h1, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.smul_one_eq_diagonal]

private theorem mem_center_of_scalar {g : StatedSp 2 (ZMod 3)} {s : ZMod 3}
    (hs : matSp g = s • 1) : g ∈ Subgroup.center (StatedSp 2 (ZMod 3)) := by
  rw [Subgroup.mem_center_iff]
  intro h
  apply matSp_injective
  rw [matSp_mul, matSp_mul, hs, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.one_mul]

private theorem central_of_commute_x0 {g : StatedSp 2 (ZMod 3)}
    (hg2 : g * g ∈ Subgroup.center (StatedSp 2 (ZMod 3))) (hgx : g * x0 = x0 * g) :
    g ∈ Subgroup.center (StatedSp 2 (ZMod 3)) := by
  have h1 : matSp g * xM = xM * matSp g := by
    have := congrArg matSp hgx
    rwa [matSp_mul, matSp_mul, matSp_x0] at this
  obtain ⟨r, hr⟩ := exists_scalar_of_mem_center hg2
  obtain ⟨s, hs⟩ := core h1 (matSp_symp g) ⟨r, by rw [← matSp_mul]; exact hr⟩
  exact mem_center_of_scalar hs

private theorem card_sp43 : Nat.card (StatedSp 2 (ZMod 3)) = 51840 :=
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two_zmod_three

private theorem card_eq_five {S : Subgroup (StatedSp 2 (ZMod 3))} (hS : IsPGroup 5 S)
    (h5 : 5 ∣ Nat.card S) : Nat.card S = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨n, hn⟩ := hS.exists_card_eq
  have hd : Nat.card S ∣ 51840 := by
    rw [← card_sp43]
    exact Subgroup.card_subgroup_dvd_card S
  rcases n with _ | _ | n
  · rw [hn] at h5
    norm_num at h5
  · simpa using hn
  · exfalso
    rw [hn] at hd
    have h25 : 5 ^ 2 ∣ 51840 := (pow_dvd_pow 5 (by omega : 2 ≤ n + 1 + 1)).trans hd
    norm_num at h25

private theorem exists_conj_commute {g x' : StatedSp 2 (ZMod 3)} (hx5 : orderOf x' = 5)
    (hxg : x' * g = g * x') :
    ∃ c : StatedSp 2 (ZMod 3), (c * g * c⁻¹) * x0 = x0 * (c * g * c⁻¹) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hP' : IsPGroup 5 (Subgroup.zpowers x') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx5, pow_one])
  have hP0 : IsPGroup 5 (Subgroup.zpowers x0) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_x0, pow_one])
  obtain ⟨S1, hS1⟩ := hP'.exists_le_sylow
  obtain ⟨S0, hS0⟩ := hP0.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (StatedSp 2 (ZMod 3)) S1 S0
  have h5S1 : 5 ∣ Nat.card (S1 : Subgroup (StatedSp 2 (ZMod 3))) := by
    have := Subgroup.card_dvd_of_le hS1
    rwa [Nat.card_zpowers, hx5] at this
  have hcard1 : Nat.card (S1 : Subgroup (StatedSp 2 (ZMod 3))) = 5 :=
    card_eq_five S1.isPGroup' h5S1
  have hS1eq : Subgroup.zpowers x' = (S1 : Subgroup (StatedSp 2 (ZMod 3))) :=
    Subgroup.eq_of_le_of_card_ge hS1 (by rw [hcard1, Nat.card_zpowers, hx5])
  have hx0 : x0 ∈ ((c • S1 : Sylow 5 (StatedSp 2 (ZMod 3))) : Subgroup (StatedSp 2 (ZMod 3))) := by
    rw [hc]
    exact hS0 (Subgroup.mem_zpowers x0)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hx0
  obtain ⟨y, hy, hyx⟩ := hx0
  rw [← hS1eq] at hy
  have hyx' : c * y * c⁻¹ = x0 := by
    simpa only [MulAut.smul_def, MulAut.conj_apply] using hyx
  have hyg : y * g = g * y := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_left hxg k).eq
  refine ⟨c, ?_⟩
  rw [← hyx']
  calc c * g * c⁻¹ * (c * y * c⁻¹) = c * (g * y) * c⁻¹ := by group
    _ = c * (y * g) * c⁻¹ := by rw [hyg]
    _ = c * y * c⁻¹ * (c * g * c⁻¹) := by group

private theorem not_five_dvd_card_centralizer {g : StatedSp 2 (ZMod 3)}
    (hg2 : g * g ∈ Subgroup.center (StatedSp 2 (ZMod 3)))
    (hgc : g ∉ Subgroup.center (StatedSp 2 (ZMod 3))) :
    ¬ 5 ∣ Nat.card (Subgroup.centralizer ({g} : Set (StatedSp 2 (ZMod 3)))) := by
  intro h5
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
    (G := Subgroup.centralizer ({g} : Set (StatedSp 2 (ZMod 3)))) 5 h5
  have hx5 : orderOf (x : StatedSp 2 (ZMod 3)) = 5 := by rw [Subgroup.orderOf_coe]; exact hx
  have hxg : (x : StatedSp 2 (ZMod 3)) * g = g * x := Subgroup.mem_centralizer_singleton_iff.mp x.2
  obtain ⟨c, hc⟩ := exists_conj_commute hx5 hxg
  apply hgc
  have hg'2 : (c * g * c⁻¹) * (c * g * c⁻¹) ∈ Subgroup.center (StatedSp 2 (ZMod 3)) := by
    have : (c * g * c⁻¹) * (c * g * c⁻¹) = c * (g * g) * c⁻¹ := by group
    rw [this]
    exact (inferInstance : (Subgroup.center (StatedSp 2 (ZMod 3))).Normal).conj_mem _ hg2 c
  have hg' := central_of_commute_x0 hg'2 hc
  have := (inferInstance : (Subgroup.center (StatedSp 2 (ZMod 3))).Normal).conj_mem _ hg' c⁻¹
  simpa [mul_assoc] using this

theorem isSolvable_centralizer_of_sq_mem_center (g : StatedSp 2 (ZMod 3))
    (hg2 : g * g ∈ Subgroup.center (StatedSp 2 (ZMod 3)))
    (hgc : g ∉ Subgroup.center (StatedSp 2 (ZMod 3))) :
    Group.IsSolvable (Subgroup.centralizer ({g} : Set (StatedSp 2 (ZMod 3)))) := by
  have h5 := not_five_dvd_card_centralizer hg2 hgc
  have hd : Nat.card (Subgroup.centralizer ({g} : Set (StatedSp 2 (ZMod 3)))) ∣ 51840 := by
    rw [← card_sp43]
    exact Subgroup.card_subgroup_dvd_card _
  refine CFSG.SignalizerFunctor.Helpers.two_prime_order_solvable _ 2 3 Nat.prime_two
    Nat.prime_three fun r hr hdvd => ?_
  have hr' : r ∣ 2 ^ 7 * 3 ^ 4 * 5 := by
    have := hdvd.trans hd
    norm_num at this ⊢
    exact this
  rcases (Nat.Prime.dvd_mul hr).mp hr' with h | h
  · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp (hr.dvd_of_dvd_pow h))
  · exfalso
    have : r = 5 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_five).mp h
    subst this
    exact h5 hdvd

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Lc.Res
