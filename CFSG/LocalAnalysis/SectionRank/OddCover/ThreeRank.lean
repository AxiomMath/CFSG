module

public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.SectionRank.OddCover

open Matrix CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {K : Type} [Field K]

theorem scalar_eq_diagHom (c : Kˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) c = diagHom 3 (fun _ => c) := by
  apply Units.ext
  rw [GeneralLinearGroup.coe_scalar, coe_diagHom]
  rfl

theorem exists_diag_of_mem_torus3 {M : Subgroup Kˣ} {x : GL (Fin 3) K} (hx : x ∈ torus3 M) :
    ∃ d : Fin 3 → Kˣ, d 0 * d 1 * d 2 = 1 ∧ x = diagHom 3 d := by
  obtain ⟨d, -, hd, rfl⟩ := (mem_torus3 M).1 hx
  exact ⟨d, hd, rfl⟩

theorem eq_of_diag_eq {d d' : Fin 3 → Kˣ} (hd : d 0 * d 1 * d 2 = 1)
    (hd' : d' 0 * d' 1 * d' 2 = 1) (h0 : d 0 = d' 0) (h1 : d 1 = d' 1) : d = d' := by
  have h2 : d 2 = d' 2 := by
    have : d 0 * d 1 * d 2 = d' 0 * d' 1 * d' 2 := by rw [hd, hd']
    rw [h0, h1] at this
    exact mul_left_cancel this
  funext i
  fin_cases i <;> assumption

theorem card_le_of_le_torus3_of_cube [Finite K] {M : Subgroup Kˣ} {F : Subgroup (GL (Fin 3) K)}
    (hF : F ≤ torus3 M)
    (hcube : ∀ x ∈ F, ∃ c : Kˣ, x ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) c) :
    Nat.card F ≤ 27 := by
  classical
  have hdiag : ∀ x : F, ∃ d : Fin 3 → Kˣ, d 0 * d 1 * d 2 = 1 ∧ (x : GL (Fin 3) K) = diagHom 3 d :=
    fun x => exists_diag_of_mem_torus3 (hF x.2)
  choose d hd hxd using hdiag
  have hcub : ∀ x : F, ∃ c : Kˣ, ∀ i, d x i ^ 3 = c := by
    intro x
    obtain ⟨c, hc⟩ := hcube x x.2
    refine ⟨c, fun i => ?_⟩
    rw [hxd x, ← map_pow, scalar_eq_diagHom] at hc
    exact congrFun (diagHom_injective 3 hc) i
  have h9 : ∀ x : F, d x 0 ∈ rootsOfUnity 9 K := by
    intro x
    obtain ⟨c, hc⟩ := hcub x
    rw [mem_rootsOfUnity]
    have h3 : c ^ 3 = 1 := by
      calc c ^ 3 = c * c * c := by rw [pow_three, mul_assoc]
        _ = d x 0 ^ 3 * d x 1 ^ 3 * d x 2 ^ 3 := by rw [hc 0, hc 1, hc 2]
        _ = (d x 0 * d x 1 * d x 2) ^ 3 := by rw [mul_pow, mul_pow]
        _ = 1 := by rw [hd x, one_pow]
    rw [show (9 : ℕ) = 3 * 3 by norm_num, pow_mul, hc 0, h3]
  have h3 : ∀ x : F, d x 1 * (d x 0)⁻¹ ∈ rootsOfUnity 3 K := by
    intro x
    obtain ⟨c, hc⟩ := hcub x
    rw [mem_rootsOfUnity, mul_pow, inv_pow, hc 0, hc 1, mul_inv_cancel]
  let φ : F → rootsOfUnity 9 K × rootsOfUnity 3 K := fun x => (⟨d x 0, h9 x⟩, ⟨_, h3 x⟩)
  have hφ : Function.Injective φ := by
    intro x y hxy
    simp only [φ, Prod.mk.injEq, Subtype.mk.injEq] at hxy
    obtain ⟨h0, h1⟩ := hxy
    have h1' : d x 1 = d y 1 := by
      have := congrArg (· * d x 0) h1
      simp only [inv_mul_cancel_right] at this
      rw [this, h0, inv_mul_cancel_right]
    apply Subtype.ext
    rw [hxd x, hxd y, eq_of_diag_eq (hd x) (hd y) h0 h1']
  calc Nat.card F ≤ Nat.card (rootsOfUnity 9 K × rootsOfUnity 3 K) :=
        Nat.card_le_card_of_injective φ hφ
    _ = Nat.card (rootsOfUnity 9 K) * Nat.card (rootsOfUnity 3 K) := Nat.card_prod _ _
    _ ≤ 9 * 3 := Nat.mul_le_mul (card_rootsOfUnity K 9) (card_rootsOfUnity K 3)
    _ = 27 := by norm_num

theorem cycGL_sq_conj_diagHom (d : Fin 3 → Kˣ) :
    cycGL ^ 2 * diagHom 3 d * (cycGL ^ 2)⁻¹ = diagHom 3 ![d 1, d 2, d 0] := by
  rw [sq, _root_.mul_inv_rev, show cycGL * cycGL * diagHom 3 d * (cycGL⁻¹ * cycGL⁻¹) =
    cycGL * (cycGL * diagHom 3 d * cycGL⁻¹) * cycGL⁻¹ by group, cycGL_conj_diagHom,
    cycGL_conj_diagHom]
  rfl

theorem card_le_of_le_torus3_of_comm_cyc [Finite K] {M : Subgroup Kˣ}
    {F : Subgroup (GL (Fin 3) K)} (hF : F ≤ torus3 M) {j : ℕ} (hj : j = 1 ∨ j = 2)
    (hcomm : ∀ s ∈ F, ∃ c : Kˣ,
      cycGL ^ j * s * (cycGL ^ j)⁻¹ * s⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) c) :
    Nat.card F ≤ 9 := by
  classical
  have hdiag : ∀ x : F, ∃ d : Fin 3 → Kˣ, d 0 * d 1 * d 2 = 1 ∧ (x : GL (Fin 3) K) = diagHom 3 d :=
    fun x => exists_diag_of_mem_torus3 (hF x.2)
  choose d hd hxd using hdiag
  have hrel : ∀ x : F, d x 0 ^ 3 = 1 ∧ (d x 1 * (d x 0)⁻¹) ^ 3 = 1 := by
    intro x
    obtain ⟨c, hc⟩ := hcomm x x.2
    rw [hxd x, scalar_eq_diagHom, ← map_inv, mul_assoc] at hc
    rcases hj with rfl | rfl
    · rw [pow_one, ← mul_assoc, cycGL_conj_diagHom, ← map_mul] at hc
      have h := diagHom_injective 3 hc
      have e0 := congrFun h 0
      have e1 := congrFun h 1
      have e2 := congrFun h 2
      simp only [Pi.mul_apply, Pi.inv_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at e0 e1 e2
      have f0 : d x 2 = c * d x 0 := by rw [← e0]; group
      have f1 : d x 0 = c * d x 1 := by rw [← e1]; group
      have f2 : d x 1 = c * d x 2 := by rw [← e2]; group
      have hc3 : c ^ 3 = 1 := by
        have : d x 0 = c ^ 3 * d x 0 := by
          calc d x 0 = c * d x 1 := f1
            _ = c * (c * d x 2) := by rw [f2]
            _ = c * (c * (c * d x 0)) := by rw [f0]
            _ = c ^ 3 * d x 0 := by rw [pow_three]; simp only [mul_assoc]
        exact (mul_eq_right.1 this.symm)
      constructor
      · have h3 := hd x
        rw [f2, f0, show d x 0 * (c * (c * d x 0)) * (c * d x 0) = c ^ 3 * d x 0 ^ 3 by
          rw [pow_three, pow_three]; ac_rfl, hc3, one_mul] at h3
        exact h3
      · rw [f2, f0, show c * (c * d x 0) * (d x 0)⁻¹ = c ^ 2 by
          rw [mul_assoc, mul_inv_cancel_right, sq],
          ← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hc3, one_pow]
    · rw [← mul_assoc, cycGL_sq_conj_diagHom, ← map_mul] at hc
      have h := diagHom_injective 3 hc
      have e0 := congrFun h 0
      have e1 := congrFun h 1
      have e2 := congrFun h 2
      simp only [Pi.mul_apply, Pi.inv_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at e0 e1 e2
      have f0 : d x 1 = c * d x 0 := by rw [← e0]; group
      have f1 : d x 2 = c * d x 1 := by rw [← e1]; group
      have f2 : d x 0 = c * d x 2 := by rw [← e2]; group
      have hc3 : c ^ 3 = 1 := by
        have : d x 0 = c ^ 3 * d x 0 := by
          calc d x 0 = c * d x 2 := f2
            _ = c * (c * d x 1) := by rw [f1]
            _ = c * (c * (c * d x 0)) := by rw [f0]
            _ = c ^ 3 * d x 0 := by rw [pow_three]; simp only [mul_assoc]
        exact (mul_eq_right.1 this.symm)
      constructor
      · have h3 := hd x
        rw [f1, f0, show d x 0 * (c * d x 0) * (c * (c * d x 0)) = c ^ 3 * d x 0 ^ 3 by
          rw [pow_three, pow_three]; ac_rfl, hc3, one_mul] at h3
        exact h3
      · rw [f0, show c * d x 0 * (d x 0)⁻¹ = c by group, hc3]
  let φ : F → rootsOfUnity 3 K × rootsOfUnity 3 K := fun x =>
    (⟨d x 0, (mem_rootsOfUnity _ _).2 (hrel x).1⟩, ⟨_, (mem_rootsOfUnity _ _).2 (hrel x).2⟩)
  have hφ : Function.Injective φ := by
    intro x y hxy
    simp only [φ, Prod.mk.injEq, Subtype.mk.injEq] at hxy
    obtain ⟨h0, h1⟩ := hxy
    have h1' : d x 1 = d y 1 := by
      have := congrArg (· * d x 0) h1
      simp only [inv_mul_cancel_right] at this
      rw [this, h0, inv_mul_cancel_right]
    apply Subtype.ext
    rw [hxd x, hxd y, eq_of_diag_eq (hd x) (hd y) h0 h1']
  calc Nat.card F ≤ Nat.card (rootsOfUnity 3 K × rootsOfUnity 3 K) :=
        Nat.card_le_card_of_injective φ hφ
    _ = Nat.card (rootsOfUnity 3 K) * Nat.card (rootsOfUnity 3 K) := Nat.card_prod _ _
    _ ≤ 3 * 3 := Nat.mul_le_mul (card_rootsOfUnity K 3) (card_rootsOfUnity K 3)
    _ = 9 := by norm_num

theorem scalar_commute (c : Kˣ) (g : GL (Fin 3) K) :
    Commute (Matrix.GeneralLinearGroup.scalar (Fin 3) c) g :=
  Units.ext (by
    rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar]
    exact (Matrix.scalar_commute (c : K) (fun _ => Commute.all _ _) _).eq)

theorem card_le_of_le_torus3_sup_cyc [Finite K] (M : Subgroup Kˣ) {E : Subgroup (GL (Fin 3) K)}
    (hE : E ≤ torus3 M ⊔ Subgroup.zpowers (cycGL : GL (Fin 3) K))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, ∃ c : Kˣ, ⁅x, y⁆ = Matrix.GeneralLinearGroup.scalar (Fin 3) c)
    (hcube : ∀ x ∈ E, ∃ c : Kˣ, x ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) c) :
    Nat.card E ≤ 27 := by
  by_cases hET : E ≤ torus3 M
  · exact card_le_of_le_torus3_of_cube hET hcube
  obtain ⟨x, hxE, hxT⟩ := IsConcreteLE.not_le_iff_exists.1 hET
  obtain ⟨t, ht, j, hj, rfl⟩ := exists_mem_torus3_mul_cyc M (hE hxE)
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hxT
    exact hxT ht
  have hj12 : j = 1 ∨ j = 2 := by omega
  set F := torus3 M ⊓ E with hFdef
  have hF : F ≤ torus3 M := inf_le_left
  have hFc : ∀ s ∈ F, ∃ c : Kˣ, cycGL ^ j * s * (cycGL ^ j)⁻¹ * s⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
    intro s hs
    obtain ⟨c, hc⟩ := hcomm _ hxE s hs.2
    refine ⟨c, ?_⟩
    have hwT : cycGL ^ j * s * (cycGL ^ j)⁻¹ ∈ torus3 M := by
      have hn : (cycGL : GL (Fin 3) K) ^ j ∈
          Subgroup.normalizer (torus3 (K := K) M : Set (GL (Fin 3) K)) :=
        Subgroup.pow_mem _ (cycGL_mem_normalizer_torus3 M) j
      exact (Subgroup.mem_normalizer_iff.1 hn s).1 hs.1
    rw [← hc, commutatorElement_def]
    have h1 := torus3_comm M ht hwT
    have h2 := torus3_comm M ht hs.1
    calc cycGL ^ j * s * (cycGL ^ j)⁻¹ * s⁻¹
        = t * (cycGL ^ j * s * (cycGL ^ j)⁻¹) * t⁻¹ * s⁻¹ := by
          rw [h1]; group
      _ = t * cycGL ^ j * s * (t * cycGL ^ j)⁻¹ * s⁻¹ := by group
  have hFcard := card_le_of_le_torus3_of_comm_cyc hF hj12 hFc
  set N := torus3 M ⊔ Subgroup.zpowers (cycGL : GL (Fin 3) K)
  have hTN : torus3 M ≤ N := le_sup_left
  have hidx : (torus3 M).relIndex N = 3 := by
    have h := Subgroup.relIndex_mul_card (torus3 M) N
    rw [inf_eq_left.2 hTN, card_torus3, card_torus3_sup_cyc] at h
    have hpos : 0 < Nat.card M ^ 2 := pow_pos Nat.card_pos 2
    exact Nat.eq_of_mul_eq_mul_right hpos h
  have hrel : (torus3 M).relIndex E ≤ 3 := by
    have := Subgroup.relIndex_le_of_le_right (H := torus3 M) hE (by rw [hidx]; norm_num)
    rwa [hidx] at this
  have hEcard := Subgroup.relIndex_mul_card (torus3 M) E
  rw [← hEcard]
  calc (torus3 M).relIndex E * Nat.card F ≤ 3 * 9 := Nat.mul_le_mul hrel hFcard
    _ = 27 := by norm_num

theorem exists_scalar_of_mem {H : Subgroup (GL (Fin 3) K)} {x : H}
    (hx : x ∈ (StatedScalars (Fin 3) K).subgroupOf H) :
    ∃ c : Kˣ, (x : GL (Fin 3) K) = Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
  obtain ⟨c, hc⟩ := hx
  exact ⟨c, hc.symm⟩

theorem three_pRank_statedProj_le_two [Finite K] {H : Subgroup (GL (Fin 3) K)}
    {M : Subgroup Kˣ} (hH : MonomialData H M)
    (hcard : (Nat.card H).factorization 3 = (3 * Nat.card M ^ 2).factorization 3)
    (hD : Nat.card ((StatedScalars (Fin 3) K).subgroupOf H) = 3) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj H)) ≤ 2 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set D := (StatedScalars (Fin 3) K).subgroupOf H with hDdef
  refine pRank_le (H := (⊤ : Subgroup (StatedProj H))) (by norm_num) fun Ebar _ hEbar => ?_
  set E : Subgroup H := Ebar.comap (QuotientGroup.mk' D) with hEdef
  have hEcard : Nat.card E = 3 * Nat.card Ebar := by
    have h := QuotientGroup.card_preimage_mk D (Ebar : Set (StatedProj H))
    rw [hD] at h
    exact h
  have hEp : IsPGroup 3 E := by
    rw [IsPGroup.iff_card]
    have hEb : IsPGroup 3 Ebar := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hEbar.2 g g.2)⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hEb
    exact ⟨k + 1, by rw [hEcard, hk, pow_succ, mul_comm]⟩
  set N : Subgroup (GL (Fin 3) K) := torus3 M ⊔ Subgroup.zpowers cycGL with hNdef
  have hNH : N ≤ H := sup_le (torus3_le M hH) (Subgroup.zpowers_le.2 hH.cyc_mem)
  set N' : Subgroup H := N.subgroupOf H with hN'def
  have hN'card : Nat.card N' = 3 * Nat.card M ^ 2 := by
    rw [hN'def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv, card_torus3_sup_cyc]
  obtain ⟨S₀⟩ := (inferInstance : Nonempty (Sylow 3 N'))
  have hS₀ := Sylow.card_eq_multiplicity S₀
  let S : Sylow 3 H := Sylow.ofCard ((S₀ : Subgroup N').map N'.subtype) (by
    rw [Subgroup.card_map_of_injective N'.subtype_injective, hS₀, hN'card, hcard])
  have hSN : (S : Subgroup H) ≤ N' := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  obtain ⟨S', hES'⟩ := hEp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H S S'
  set E' : Subgroup H := E.map (MulAut.conj g⁻¹).toMonoidHom with hE'def
  have hE'S : E' ≤ (S : Subgroup H) := by
    rintro _ ⟨y, hy, rfl⟩
    have hyS : y ∈ ((g • S : Sylow 3 H) : Subgroup H) := hg ▸ hES' hy
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hyS
    exact hyS
  set EG : Subgroup (GL (Fin 3) K) := E'.map H.subtype with hEGdef
  have hEGN : EG ≤ N := by
    rintro _ ⟨y, hy, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hSN (hE'S hy))
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, ⁅x, y⁆ ∈ D := by
    intro x hx y hy
    have := hEbar.1.1.1 ⟨_, hx⟩ ⟨_, hy⟩
    have h := congrArg Subtype.val this
    simp only [Subgroup.coe_mul] at h
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact h
  have hEcube : ∀ x ∈ E, x ^ 3 ∈ D := by
    intro x hx
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow]
    exact hEbar.2 _ hx
  have hcommG : ∀ x ∈ EG, ∀ y ∈ EG, ∃ c : Kˣ,
      ⁅x, y⁆ = Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩ _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    obtain ⟨c, hc⟩ := exists_scalar_of_mem (hEcomm x hx y hy)
    refine ⟨c, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype]
    rw [show ⁅((g⁻¹ * x * g⁻¹⁻¹ : H) : GL (Fin 3) K), ((g⁻¹ * y * g⁻¹⁻¹ : H) : GL (Fin 3) K)⁆ =
        (g⁻¹ : GL (Fin 3) K) * ((⁅x, y⁆ : H) : GL (Fin 3) K) * (g : GL (Fin 3) K) by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, commutatorElement_def]; group,
      hc, ← (scalar_commute c ((g : GL (Fin 3) K)⁻¹)).eq]
    group
  have hcubeG : ∀ x ∈ EG, ∃ c : Kˣ, x ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    obtain ⟨c, hc⟩ := exists_scalar_of_mem (hEcube x hx)
    refine ⟨c, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype]
    rw [show ((g⁻¹ * x * g⁻¹⁻¹ : H) : GL (Fin 3) K) ^ 3 =
        (g⁻¹ : GL (Fin 3) K) * ((x ^ 3 : H) : GL (Fin 3) K) * (g : GL (Fin 3) K) by
      rw [← Subgroup.coe_pow, conj_pow, inv_inv]; rfl,
      hc, ← (scalar_commute c ((g : GL (Fin 3) K)⁻¹)).eq]
    group
  have h27 := card_le_of_le_torus3_sup_cyc M hEGN hcommG hcubeG
  rw [hEGdef, Subgroup.card_map_of_injective H.subtype_injective, hE'def,
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hEcard] at h27
  omega

end CFSG.SectionRank.OddCover
