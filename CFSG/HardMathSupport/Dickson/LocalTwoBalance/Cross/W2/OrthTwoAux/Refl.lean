module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.OrthTwoAux.Quad
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2Main8

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.OrthTwoAux

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance Polynomial Module
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.RankThree.Classical CFSG.ClassicalGroups.Orthogonal
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open QuadraticMap
open CFSG.RankThree.OrthogonalInvolutions (commSpace mem_commSpace sub_mem_commSpace
  sub_eq_add_vec polar_self_eq_zero)

section Group

variable {G : Type*} [Group G]

theorem cube_of_braid {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hbr : a * b * a = b * a * b) : (a * b) ^ 3 = 1 := by
  calc (a * b) ^ 3 = (a * b * a) * (b * a * b) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = (b * a * b) * (b * a * b) := by rw [hbr]
    _ = b * a * (b * b) * a * b := by simp only [mul_assoc]
    _ = b * (a * a) * b := by rw [hb, mul_one]; simp only [mul_assoc]
    _ = 1 := by rw [ha, mul_one, hb]

theorem conj_of_braid {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hbr : a * b * a = b * a * b) : (a * b) * a * (a * b)⁻¹ = b := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_left ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_left hb
  rw [mul_inv_rev, ha', hb']
  calc a * b * a * (b * a) = (a * b * a) * b * a := by simp only [mul_assoc]
    _ = (b * a * b) * b * a := by rw [hbr]
    _ = b * a * (b * b) * a := by simp only [mul_assoc]
    _ = b * (a * a) := by rw [hb, mul_one]; simp only [mul_assoc]
    _ = b := by rw [ha, mul_one]

end Group

section TwoReflections

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem reflection_apply_of_card_two (hK : Nat.card K = 2) {v : V} [Invertible (Q v)]
    (hv : Q v = 1) (u : V) :
    TauCeti.QuadraticMap.reflection Q v u = u + polar Q v u • v := by
  have := card_two_charP hK
  rw [TauCeti.QuadraticMap.reflection_apply, invOf_eq_inv, hv, inv_one, one_mul,
    sub_eq_add_vec K]

theorem reflection_braid (hK : Nat.card K = 2) {c b : V} [Invertible (Q c)] [Invertible (Q b)]
    (hc : Q c = 1) (hb : Q b = 1) (hcb : polar Q c b = 1) :
    TauCeti.QuadraticMap.reflection Q c * TauCeti.QuadraticMap.reflection Q b *
        TauCeti.QuadraticMap.reflection Q c =
      TauCeti.QuadraticMap.reflection Q b * TauCeti.QuadraticMap.reflection Q c *
        TauCeti.QuadraticMap.reflection Q b := by
  have hchar := card_two_charP hK
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hbc : polar Q b c = 1 := by rw [polar_comm]; exact hcb
  have hcc : polar Q c c = 0 := polar_self_eq_zero Q c
  have hbb : polar Q b b = 0 := polar_self_eq_zero Q b
  ext u
  simp only [LinearEquiv.mul_apply, reflection_apply_of_card_two hK hc,
    reflection_apply_of_card_two hK hb, polar_add_right, polar_smul_right, smul_eq_mul, hcc, hbb,
    hbc, hcb]
  match_scalars <;>
    first
      | ring1
      | linear_combination (polar Q c u) * h2
      | linear_combination (-(polar Q b u)) * h2

theorem reflection_comm_of_fixed (hK : Nat.card K = 2) {c : V} [Invertible (Q c)]
    (hc : Q c = 1) {x : V ≃ₗ[K] V} (hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hxc : x c = c) :
    TauCeti.QuadraticMap.reflection Q c * x = x * TauCeti.QuadraticMap.reflection Q c := by
  ext u
  simp only [LinearEquiv.mul_apply, reflection_apply_of_card_two hK hc, map_add, map_smul, hxc]
  have h1 : polar Q c (x u) = polar Q c u := by
    have := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hxO c u
    rwa [hxc] at this
  rw [h1]

end TwoReflections

section Main

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem orth2_finrank_commSpace_ne_one (hK : Nat.card K = 2)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) (h5 : 5 ≤ finrank K V)
    (hinj : Function.Injective
      (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)))
    {H E : Subgroup (MulAut (ProjOrthDerived Q))} (hH : innerAut (ProjOrthDerived Q) ≤ H)
    {g : MulAut (ProjOrthDerived Q)} (hg : g ∈ localDeltaIn 3 H E)
    (x : orthDerived Q) (hxo : orderOf x = 3)
    (he : MulAut.conj (QuotientGroup.mk x : ProjOrthDerived Q) ∈ E)
    (h4 : 4 ≤ finrank K (fixedSpace (x : V ≃ₗ[K] V)))
    {G : V ≃ₗ[K] V} (hGO : G ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hGg : ∀ y : orthDerived Q, g (QuotientGroup.mk y) = QuotientGroup.mk
      (⟨G * (y : V ≃ₗ[K] V) * G⁻¹, conj_mem_orthDerived hGO y.2⟩ : orthDerived Q))
    (hle : commSpace G ≤ fixedSpace (x : V ≃ₗ[K] V)) :
    finrank K (commSpace G) ≠ 1 := by
  intro h1
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hchar := card_two_charP hK
  have : Finite V := Module.finite_of_finite K
  have hpl : (3 : ℕ) ≠ ringChar K := by rw [ringChar_eq_two_of_card hK]; norm_num
  have hx := oddOrderIsometry_of_orthDerived hp hpl hQ x hxo
  obtain ⟨-, -, -, -, -, -, hodd, -, -⟩ :=
    orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  have hmk := mk_injective_of_card_two (Q := Q) hK
  have hxO : (x : V ≃ₗ[K] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthDerived_le_orthogonalGroup Q x.2
  obtain ⟨c, hcG, hQc, hGc⟩ := exists_reflection_of_finrank_commSpace_eq_one hK hQ hGO h1
  have hcx : c ∈ fixedSpace (x : V ≃ₗ[K] V) := hle hcG
  have hQc1 : Q c = 1 := (card_two_cases hK (Q c)).resolve_left hQc
  have hc0 : c ≠ 0 := fun h => hQc (by rw [h, map_zero])
  obtain ⟨b, hbx, hQb, hcb⟩ :
      ∃ b ∈ fixedSpace (x : V ≃ₗ[K] V), Q b ≠ 0 ∧ polar Q c b ≠ 0 := by
    have hWnd := hx.polarBilin_fixed_nondegenerate
    obtain ⟨b, hb1, hb2⟩ := exists_map_ne_zero_polar_ne_zero
      (Q := Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype) hWnd (by omega)
      (c := ⟨c, hcx⟩) (fun h => hc0 (congrArg Subtype.val h))
    refine ⟨b, b.2, hb1, ?_⟩
    rwa [polar_comp_subtype] at hb2
  have hbx' : (x : V ≃ₗ[K] V) b = b := mem_fixedSpace.1 hbx
  have hcx' : (x : V ≃ₗ[K] V) c = c := mem_fixedSpace.1 hcx
  have hQb1 : Q b = 1 := (card_two_cases hK (Q b)).resolve_left hQb
  have hcb1 : polar Q c b = 1 := (card_two_cases hK _).resolve_left hcb
  have hbc1 : polar Q b c = 1 := by rw [polar_comm]; exact hcb1
  haveI : Invertible (Q c) := invertibleOfNonzero hQc
  haveI : Invertible (Q b) := invertibleOfNonzero hQb
  set tc := TauCeti.QuadraticMap.reflection Q c with htc
  set tb := TauCeti.QuadraticMap.reflection Q b with htb
  have hGtc : G = tc :=
    LinearEquiv.ext fun u => by rw [hGc u, htc, reflection_apply_of_card_two hK hQc1]
  have htcO : tc ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.reflection_mem_orthogonalGroup Q c
  have htbO : tb ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.reflection_mem_orthogonalGroup Q b
  have htc2 : tc * tc = 1 := TauCeti.QuadraticMap.reflection_mul_self Q c
  have htb2 : tb * tb = 1 := TauCeti.QuadraticMap.reflection_mul_self Q b
  have hbr : tc * tb * tc = tb * tc * tb := reflection_braid hK hQc1 hQb1 hcb1
  set h : V ≃ₗ[K] V := tc * tb with hh
  have hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q := mul_mem htcO htbO
  have hh3 : h ^ 3 = 1 := cube_of_braid htc2 htb2 hbr
  have hh1 : h ≠ 1 := by
    intro h1'
    have htbc : tb = tc := by
      have : tb = tc⁻¹ := eq_inv_of_mul_eq_one_right h1'
      rw [this]
      exact inv_eq_of_mul_eq_one_left htc2
    have := LinearEquiv.congr_fun htbc c
    rw [htb, htc, reflection_apply_of_card_two hK hQb1, reflection_apply_of_card_two hK hQc1,
      polar_self_eq_zero Q c, hbc1, zero_smul, one_smul, add_zero, add_eq_left] at this
    exact hQb (by rw [this, map_zero])
  have hhorder : orderOf h = 3 := orderOf_eq_prime hh3 hh1
  have hhΩ : h ∈ orthDerived Q := hodd h hhO (by rw [hhorder]; decide)
  set h' : orthDerived Q := ⟨h, hhΩ⟩ with hh'
  have hhx : h * (x : V ≃ₗ[K] V) = (x : V ≃ₗ[K] V) * h := by
    calc h * (x : V ≃ₗ[K] V) = tc * (tb * (x : V ≃ₗ[K] V)) := by rw [hh, mul_assoc]
      _ = tc * ((x : V ≃ₗ[K] V) * tb) := by rw [reflection_comm_of_fixed hK hQb1 hxO hbx']
      _ = (tc * (x : V ≃ₗ[K] V)) * tb := by rw [mul_assoc]
      _ = ((x : V ≃ₗ[K] V) * tc) * tb := by rw [reflection_comm_of_fixed hK hQc1 hxO hcx']
      _ = (x : V ≃ₗ[K] V) * h := by rw [hh, mul_assoc]
  set ū : MulAut (ProjOrthDerived Q) := MulAut.conj (QuotientGroup.mk h' : ProjOrthDerived Q)
    with hū
  set d : MulAut (ProjOrthDerived Q) := MulAut.conj (QuotientGroup.mk x : ProjOrthDerived Q)
    with hd
  have hd1 : d ≠ 1 := by
    intro hd1
    have h1' : (QuotientGroup.mk x : ProjOrthDerived Q) = 1 := hinj (by rw [← hd, hd1, map_one])
    have h2' : x = 1 := hmk (by rw [h1']; rfl)
    rw [h2', orderOf_one] at hxo
    omega
  have hūH : ū ∈ H := hH ⟨_, rfl⟩
  have hūd : ū ∈ Subgroup.centralizer ({d} : Set (MulAut (ProjOrthDerived Q))) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [hū, hd, ← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 2
    exact Subtype.ext hhx
  have hgcore := le_core_of_mem_localDeltaIn hg he hd1
  have hL : ū ∈ H ⊓ Subgroup.centralizer ({d} : Set (MulAut (ProjOrthDerived Q))) := ⟨hūH, hūd⟩
  have hg' : ū * g * ū⁻¹ ∈
      GLAPPrimeCoreOf 3 (H ⊓ Subgroup.centralizer ({d} : Set (MulAut (ProjOrthDerived Q)))) :=
    CFSG.HardMathSupport.Timmesfeld.Balance.gLAPPrimeCoreOf_conj_mem' ū hL g hgcore
  have hprod : g * (ū * g * ū⁻¹) ∈
      GLAPPrimeCoreOf 3 (H ⊓ Subgroup.centralizer ({d} : Set (MulAut (ProjOrthDerived Q)))) :=
    mul_mem hgcore hg'
  have hcop : Nat.Coprime 3 (orderOf (g * (ū * g * ū⁻¹))) :=
    (CFSG.HardMathSupport.Timmesfeld.Balance.coprime_card_gLAPPrimeCoreOf' hp _).coprime_dvd_right
      (Subgroup.orderOf_dvd_natCard _ hprod)
  have hU : ∀ z : orthDerived Q,
      ū (QuotientGroup.mk z) = QuotientGroup.mk (h' * z * h'⁻¹) := by
    intro z
    rw [hū, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
  have hUinv : ∀ z : orthDerived Q,
      ū⁻¹ (QuotientGroup.mk z) = QuotientGroup.mk (h'⁻¹ * z * h') := by
    intro z
    have : ū⁻¹ = MulAut.conj (QuotientGroup.mk h'⁻¹ : ProjOrthDerived Q) := by
      rw [hū, ← map_inv, QuotientGroup.mk_inv]
    rw [this, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, inv_inv]
  have hE' : G * (h * G * h⁻¹) = h := by
    rw [hGtc, hh, conj_of_braid htc2 htb2 hbr]
  have hgg' : ∀ y : orthDerived Q, (g * (ū * g * ū⁻¹)) (QuotientGroup.mk y) =
      QuotientGroup.mk (⟨h * (y : V ≃ₗ[K] V) * h⁻¹, conj_mem_orthDerived hhO y.2⟩ :
        orthDerived Q) := by
    intro y
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, hUinv, hGg, hU, hGg]
    congr 1
    apply Subtype.ext
    have key : G * (h * (G * (h⁻¹ * (y : V ≃ₗ[K] V) * h) * G⁻¹) * h⁻¹) * G⁻¹ =
        (G * (h * G * h⁻¹)) * (y : V ≃ₗ[K] V) * (G * (h * G * h⁻¹))⁻¹ := by group
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hh']
    rw [key, hE']
  have hδ3 : (g * (ū * g * ū⁻¹)) ^ 3 = 1 := by
    ext t
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective t
    rw [orth2_conj_pow hhO hgg' 3 y, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    show h ^ 3 * (y : V ≃ₗ[K] V) * (h ^ 3)⁻¹ = y
    rw [hh3, one_mul, inv_one, mul_one]
  have hδ1 : g * (ū * g * ū⁻¹) ≠ 1 := by
    intro h1'
    exact hh1 (orth2_isometry_eq_one hK hQ h5 hhO (orth2_conj_eq_of_eq_one hK hhO hgg' h1'))
  have hδord : orderOf (g * (ū * g * ū⁻¹)) = 3 := orderOf_eq_prime hδ3 hδ1
  rw [hδord] at hcop
  exact absurd hcop (by decide)

end Main


end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.OrthTwoAux
