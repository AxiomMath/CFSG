module

public import CFSG.ClassicalGroups.Orthogonal.FiveDimensionalLocalModel
public import CFSG.ClassicalGroups.Orthogonal.PlaneSylow
public import CFSG.NumberTheory.OddModFour
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import TauCeti.Algebra.Group.Subgroup.ZPowers
public import TauCeti.GroupTheory.SemidirectProduct
public import CFSG.ClassicalInvolution.Orders.OrthogonalIndex

public noncomputable section

namespace CFSG.ClassicalGroups.Orthogonal.FiveDimensionalSylow

open Matrix QuadraticMap
open scoped commutatorElement Pointwise
open CFSG.GH74.GLS.IVK.Proofs2
open CFSG.GH74.GLS.IVK.Proofs2.Sp48
open CFSG.GH74.GLS.IVK.Proofs2.Sp48.O2Plane
open CFSG.ClassicalGroups.Orthogonal.FiveDimensionalLocalModel
open CFSG.ClassicalGroups.Orthogonal.PlaneSylow

variable {K : Type} {V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}


theorem natCard_specialOrthogonalWithin_five (F : FrameData Q) (hodd : Odd (Nat.card K))
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K V = 5) :
    Nat.card Q.specialOrthogonalWithin =
      Nat.card K ^ 4 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 4 - 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  have hq2 : 2 ≤ Nat.card K := by
    have := Finite.one_lt_card (α := K)
    omega
  haveI : Fintype K := Fintype.ofFinite K
  have hchar : ringChar K ≠ 2 := by
    intro hchar
    have hcard : Fintype.card K % 2 = 0 := FiniteField.even_card_of_char_two hchar
    have hodd' : Odd (Fintype.card K) := by
      simpa [Nat.card_eq_fintype_card] using hodd
    exact hodd'.not_two_dvd_nat (Nat.dvd_of_mod_eq_zero hcard)
  have htwo : (2 : K) ≠ 0 := by
    intro hzero
    exact hchar (by
      haveI : CharP K 2 := CFSG.GroupTheory.WeirSylow.charP_two_of_two_eq_zero hzero
      exact ringChar.eq K 2)
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  haveI : NeZero (2 : K) := ⟨htwo⟩
  letI : Invertible (2 : K) := invertibleOfNonzero htwo
  have hQ' : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ
  let e : Q.IsometryEquiv F.coordForm :=
    { F.coord with map_app' := fun v => by simp [FrameData.coordForm] }
  have hcongr : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) =
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup F.coordForm) :=
    Nat.card_congr (TauCeti.QuadraticMap.orthogonalGroupCongr e).toEquiv
  have hBcoord : (polarBilin F.coordForm).Nondegenerate := by
    rw [FrameData.coordForm, QuadraticMap.polarBilin_comp]
    have hcongrB : LinearMap.compl₁₂ (polarBilin Q)
        (F.coord.symm : (Fin 5 → K) →ₗ[K] V)
        (F.coord.symm : (Fin 5 → K) →ₗ[K] V) =
        LinearMap.BilinForm.congr F.coord (polarBilin Q) := by
      ext x y
      simp [LinearMap.BilinForm.congr]
    rw [hcongrB]
    exact (LinearMap.BilinForm.Nondegenerate.congr (B := polarBilin Q) F.coord F.nondeg)
  have hcoord : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup F.coordForm) : ℤ) =
      2 * (Nat.card K : ℤ) ^ 4 * ((Nat.card K : ℤ) ^ 2 - 1) *
        ((Nat.card K : ℤ) ^ 4 - 1) := by
    have hraw := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_odd (K := K)
      (V := Fin 5 → K) hchar (Q := F.coordForm) hBcoord
      (n := 2) (by rw [Module.finrank_fin_fun])
    have hprod : (∏ i ∈ Finset.Icc 1 2, (((Nat.card K : ℤ) ^ 2) ^ i - 1)) =
        ((Nat.card K : ℤ) ^ 2 - 1) * ((Nat.card K : ℤ) ^ 4 - 1) := by
      rw [Finset.prod_Icc_succ_top (by norm_num : (1:ℕ) ≤ 2)]
      rw [Finset.prod_Icc_succ_top (by norm_num : (1:ℕ) ≤ 1)]
      rw [show Finset.Icc (1:ℕ) 0 = ∅ by decide]
      rw [Finset.prod_empty, one_mul]
      ring
    rw [hprod] at hraw
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num] at hraw
    ring_nf at hraw ⊢
    exact hraw
  have horder : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) =
      2 * (Nat.card K : ℤ) ^ 4 * ((Nat.card K : ℤ) ^ 2 - 1) *
        ((Nat.card K : ℤ) ^ 4 - 1) := by
    rw [hcongr]
    exact hcoord
  have hindex : Q.specialOrthogonalWithin.index = 2 :=
    TauCeti.QuadraticMap.index_specialOrthogonalWithin hQ'
  have hmul : Nat.card Q.specialOrthogonalWithin * 2 =
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := by
    have := Subgroup.card_mul_index
      (G := TauCeti.QuadraticMap.orthogonalGroup Q) (H := Q.specialOrthogonalWithin)
    rwa [hindex] at this
  have hmulZ : (Nat.card Q.specialOrthogonalWithin : ℤ) * 2 =
      (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) := by
    exact_mod_cast hmul
  have hcardZ : (Nat.card Q.specialOrthogonalWithin : ℤ) =
      (Nat.card K : ℤ) ^ 4 * ((Nat.card K : ℤ) ^ 2 - 1) *
        ((Nat.card K : ℤ) ^ 4 - 1) := by
    rw [horder] at hmulZ
    linarith
  have hcast : ((Nat.card K ^ 4 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 4 - 1) : ℕ) : ℤ) =
      (Nat.card K : ℤ) ^ 4 * ((Nat.card K : ℤ) ^ 2 - 1) *
        ((Nat.card K : ℤ) ^ 4 - 1) := by
    have h2 : 1 ≤ Nat.card K ^ 2 := by
      calc 1 = 1 ^ 2 := by norm_num
        _ ≤ Nat.card K ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h4 : 1 ≤ Nat.card K ^ 4 := by
      calc 1 = 1 ^ 4 := by norm_num
        _ ≤ Nat.card K ^ 4 := Nat.pow_le_pow_left (by omega) 4
    rw [Nat.cast_mul, Nat.cast_mul]
    rw [Nat.cast_sub h4, Nat.cast_sub h2]
    push_cast
    ring
  exact Nat.cast_injective (hcardZ.trans hcast.symm)


private theorem natCard_specialOrthogonalWithin_five_two_part (F : FrameData Q)
    (hodd : Odd (Nat.card K)) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K V = 5) {ε : ℤ} {m n h r m' : ℕ}
    (hε : ε = 1 ∨ ε = -1)
    (hm : (m : ℤ) = (Nat.card K : ℤ) - ε)
    (hn : (Nat.card K : ℤ) + ε = 2 * (n : ℤ))
    (hh : (Nat.card K : ℤ) ^ 2 + 1 = 2 * (h : ℤ))
    (hfac : m = 2 ^ r * m') :
    Nat.card Q.specialOrthogonalWithin =
      2 ^ (2 * r + 3) * (Nat.card K ^ 4 * m' ^ 2 * n ^ 2 * h) := by
  have hcard := natCard_specialOrthogonalWithin_five F hodd hQ hdim
  have hεsq : ε ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hsq : (Nat.card K : ℤ) ^ 2 - 1 = (m : ℤ) * (2 * (n : ℤ)) := by
    have h1 : (Nat.card K : ℤ) ^ 2 - 1 =
        ((Nat.card K : ℤ) - ε) * ((Nat.card K : ℤ) + ε) := by
      have : ((Nat.card K : ℤ) - ε) * ((Nat.card K : ℤ) + ε) =
          (Nat.card K : ℤ) ^ 2 - ε ^ 2 := by ring
      rw [this, hεsq]
    rw [h1, ← hm, ← hn]
  have hfour : (Nat.card K : ℤ) ^ 4 - 1 =
      ((Nat.card K : ℤ) ^ 2 - 1) * ((Nat.card K : ℤ) ^ 2 + 1) := by ring
  have hq2 : 1 ≤ Nat.card K ^ 2 := by
    calc 1 = 1 ^ 2 := by norm_num
      _ ≤ Nat.card K ^ 2 := Nat.pow_le_pow_left (by
          have := Finite.one_lt_card (α := K); omega) 2
  have hq4 : 1 ≤ Nat.card K ^ 4 := by
    calc 1 = 1 ^ 4 := by norm_num
      _ ≤ Nat.card K ^ 4 := Nat.pow_le_pow_left (by
          have := Finite.one_lt_card (α := K); omega) 4
  have hcardZ : (Nat.card Q.specialOrthogonalWithin : ℤ) =
      (Nat.card K : ℤ) ^ 4 * ((Nat.card K : ℤ) ^ 2 - 1) *
        ((Nat.card K : ℤ) ^ 4 - 1) := by
    rw [hcard]
    rw [Nat.cast_mul, Nat.cast_mul]
    rw [Nat.cast_sub hq4, Nat.cast_sub hq2]
    push_cast
    ring
  have htargetZ : (Nat.card Q.specialOrthogonalWithin : ℤ) =
      ((2 ^ (2 * r + 3) * (Nat.card K ^ 4 * m' ^ 2 * n ^ 2 * h) : ℕ) : ℤ) := by
    rw [hcardZ, hfour, hsq, hh]
    have hfacZ : (m : ℤ) = (2 : ℤ) ^ r * (m' : ℤ) := by exact_mod_cast hfac
    rw [hfacZ]
    push_cast
    ring_nf
  exact Nat.cast_injective htargetZ


@[expose] def betaSOHom (F : FrameData Q) : (O2 K × O2 K) →* Q.specialOrthogonalWithin where
  toFun p := F.betaSO p.1 p.2
  map_one' := by
    apply Subtype.ext
    exact F.betaO_one
  map_mul' p q := by
    apply Subtype.ext
    simpa using (F.betaO_mul p.1 p.2 q.1 q.2).symm

theorem betaSOHom_injective (F : FrameData Q) :
    Function.Injective (betaSOHom F) := by
  intro p q h
  apply F.beta_injective
  simpa [betaSOHom] using congrArg (fun g : Q.specialOrthogonalWithin =>
    (g : V ≃ₗ[K] V)) h

theorem betaSO_mul (F : FrameData Q) (d1 d2 e1 e2 : O2 K) :
    F.betaSO d1 d2 * F.betaSO e1 e2 = F.betaSO (d1 * e1) (d2 * e2) := by
  apply Subtype.ext
  exact F.betaO_mul d1 d2 e1 e2

theorem betaSO_one_one (F : FrameData Q) :
    F.betaSO (1 : O2 K) 1 = 1 := by
  apply Subtype.ext
  exact F.betaO_one

theorem sSO_mul_self (F : FrameData Q) : F.sSO * F.sSO = 1 := by
  apply Subtype.ext
  exact F.sO_mul_self

@[expose] def negOneO2 : O2 K :=
  ⟨(-1 : GL (Fin 2) K), SO2_le_O2 (neg_one_mem_SO2 (F := K))⟩

theorem negOneO2_mul_self : negOneO2 (K := K) * negOneO2 = 1 := by
  apply Subtype.ext
  simp [negOneO2]

theorem sSO_neg_one_one (F : FrameData Q) :
    F.betaSO negOneO2 1 = F.tSO := by
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply F.e.ext
  intro i
  change F.beta negOneO2 (1 : O2 K) (F.e i) = F.t (F.e i)
  fin_cases i <;>
    simp [F.beta_e_zero, F.beta_e_one, F.beta_e_two, F.beta_e_three, F.beta_e_four,
      F.t_e, negOneO2, Matrix.det_fin_two] <;>
    norm_num

theorem sSO_neg_one_neg_one (F : FrameData Q) :
    F.betaSO negOneO2 negOneO2 = F.zSO := by
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply F.e.ext
  intro i
  change F.beta negOneO2 negOneO2 (F.e i) = F.z (F.e i)
  fin_cases i <;>
    simp [F.beta_e_zero, F.beta_e_one, F.beta_e_two, F.beta_e_three, F.beta_e_four,
      F.z_e, negOneO2, Matrix.det_fin_two] <;>
    norm_num

theorem sSO_one_neg_one (F : FrameData Q) :
    F.betaSO (1 : O2 K) negOneO2 = F.zSO * F.tSO := by
  have h := betaSO_mul F negOneO2 negOneO2 negOneO2 1
  simp only [negOneO2_mul_self, one_mul, mul_one] at h
  rw [sSO_neg_one_neg_one, sSO_neg_one_one] at h
  exact h.symm

theorem sSO_betaSO_conj (F : FrameData Q) (d1 d2 : O2 K) :
    F.sSO * F.betaSO d1 d2 * F.sSO⁻¹ = F.betaSO d2 d1 := by
  apply Subtype.ext
  exact F.sO_betaO_conj d1 d2

theorem sSO_ne_one (F : FrameData Q) : F.sSO ≠ 1 := by
  intro h
  have h0 : F.coord (F.s (F.e 0)) = F.coord (((1 : Q.specialOrthogonalWithin) :
      V ≃ₗ[K] V) (F.e 0)) :=
    congrArg (fun g : Q.specialOrthogonalWithin =>
      F.coord ((g : V ≃ₗ[K] V) (F.e 0))) h
  rw [F.s_e] at h0
  simp only [FrameData.coord_e, OneMemClass.coe_one, LinearEquiv.coe_one, id_eq] at h0
  have h1 := congrFun h0 2
  simpa using h1

abbrev orthogonalDerived (Q : QuadraticForm K V) :
    Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q) :=
  commutator (TauCeti.QuadraticMap.orthogonalGroup Q)

theorem mem_orthogonalDerived_of_subtype_mem
    {x : TauCeti.QuadraticMap.orthogonalGroup Q}
    (h : (x : V ≃ₗ[K] V) ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆) :
    x ∈ orthogonalDerived Q := by
  have hmap := Subgroup.map_subtype_commutator
    (TauCeti.QuadraticMap.orthogonalGroup Q)
  have hx : (x : V ≃ₗ[K] V) ∈ Subgroup.map
      (TauCeti.QuadraticMap.orthogonalGroup Q).subtype (orthogonalDerived Q) := by
    dsimp [orthogonalDerived]
    rw [hmap]
    exact h
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  have hyx' : y = x := Subtype.ext hyx
  simpa [hyx'] using hy

theorem tO_mem_derived (F : FrameData Q) : F.tO ∈ orthogonalDerived Q :=
  mem_orthogonalDerived_of_subtype_mem F.t_mem_commutator

theorem zO_mem_derived (F : FrameData Q) : F.zO ∈ orthogonalDerived Q :=
  mem_orthogonalDerived_of_subtype_mem F.z_mem_commutator

theorem sO_mem_derived (F : FrameData Q) : F.sO ∈ orthogonalDerived Q :=
  mem_orthogonalDerived_of_subtype_mem F.s_mem_commutator

theorem betaO_diag_mem_derived (F : FrameData Q) (d : O2 K) :
    F.betaO d d ∈ orthogonalDerived Q :=
  mem_orthogonalDerived_of_subtype_mem (F.betaO_diag_mem_commutator d)

@[expose] def planeD (c : GL (Fin 2) K) : Subgroup (O2 K) :=
  (planeSylow c).subgroupOf (O2 K)

@[expose] def betaBase (F : FrameData Q) (D : Subgroup (O2 K)) :
    Subgroup Q.specialOrthogonalWithin :=
  (D.prod D).map (betaSOHom F)

@[expose] def swapSub (F : FrameData Q) : Subgroup Q.specialOrthogonalWithin :=
  Subgroup.zpowers F.sSO

@[expose] def wreathSub (F : FrameData Q) (D : Subgroup (O2 K)) :
    Subgroup Q.specialOrthogonalWithin :=
  betaBase F D ⊔ swapSub F

theorem orderOf_sSO (F : FrameData Q) : orderOf F.sSO = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (p := 2) (by rw [pow_two]; exact sSO_mul_self F)
    (sSO_ne_one F)

theorem sSO_not_mem_betaBase (F : FrameData Q) (D : Subgroup (O2 K)) :
    F.sSO ∉ betaBase F D := by
  intro h
  obtain ⟨p, -, hp⟩ := Subgroup.mem_map.mp h
  have h0 := congrArg (fun g : Q.specialOrthogonalWithin =>
    F.coord ((g : V ≃ₗ[K] V) (F.e 0))) hp
  change F.coord (F.beta p.1 p.2 (F.e 0)) = F.coord (F.s (F.e 0)) at h0
  rw [F.beta_e_zero, F.s_e, map_add, map_smul, map_smul, F.coord_e, F.coord_e] at h0
  have h2 := congrFun h0 2
  simp at h2

theorem betaBase_card (F : FrameData Q) (D : Subgroup (O2 K)) {r : ℕ}
    (hD : Nat.card D = 2 ^ (r + 1)) :
    Nat.card (betaBase F D) = 2 ^ (2 * r + 2) := by
  rw [betaBase, Subgroup.card_map_of_injective (betaSOHom_injective F)]
  have hprod : Nat.card ↥(D.prod D) = Nat.card ↥D * Nat.card ↥D := by
    change Nat.card {c : O2 K × O2 K // c.1 ∈ D ∧ c.2 ∈ D} =
      Nat.card ↥D * Nat.card ↥D
    rw [Nat.card_congr (Equiv.subtypeProdEquivProd (p := fun x : O2 K => x ∈ D)
      (q := fun x : O2 K => x ∈ D)), Nat.card_prod]
  rw [hprod, hD]
  rw [← pow_add]
  congr 1
  ring

theorem swapSub_card (F : FrameData Q) : Nat.card (swapSub F) = 2 := by
  rw [swapSub, Nat.card_zpowers, orderOf_sSO F]

theorem swapSub_le_normalizer_betaBase (F : FrameData Q) (D : Subgroup (O2 K)) :
    swapSub F ≤ Subgroup.normalizer (betaBase F D : Set Q.specialOrthogonalWithin) := by
  rw [swapSub, Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
  intro h
  have hs : F.sSO⁻¹ = F.sSO := inv_eq_of_mul_eq_one_right (sSO_mul_self F)
  constructor
  · intro hh
    obtain ⟨p, hp, hp_eq⟩ := Subgroup.mem_map.mp hh
    have hconj' : F.sSO * F.betaSO p.1 p.2 * F.sSO = F.betaSO p.2 p.1 := by
      simpa [hs] using sSO_betaSO_conj F p.1 p.2
    have hp_eq' : betaSOHom F p = h := hp_eq
    exact Subgroup.mem_map.mpr ⟨(p.2, p.1), ⟨hp.2, hp.1⟩, by
      calc F.betaSO p.2 p.1 = F.sSO * F.betaSO p.1 p.2 * F.sSO := hconj'.symm
        _ = F.sSO * h * F.sSO := by simpa [betaSOHom] using congrArg (fun x => F.sSO * x * F.sSO) hp_eq
        _ = F.sSO * h * F.sSO⁻¹ := by rw [hs]⟩
  · intro hh
    obtain ⟨p, hp, hp_eq⟩ := Subgroup.mem_map.mp hh
    have hconj' : F.sSO * F.betaSO p.1 p.2 * F.sSO = F.betaSO p.2 p.1 := by
      simpa [hs] using sSO_betaSO_conj F p.1 p.2
    have hp_eq' : betaSOHom F p = F.sSO * h * F.sSO := by
      simpa [hs] using hp_eq
    exact Subgroup.mem_map.mpr ⟨(p.2, p.1), ⟨hp.2, hp.1⟩, by
      calc F.betaSO p.2 p.1 = F.sSO * F.betaSO p.1 p.2 * F.sSO := hconj'.symm
        _ = F.sSO * (F.sSO * h * F.sSO) * F.sSO := by
            simpa [betaSOHom] using congrArg (fun x => F.sSO * x * F.sSO) hp_eq'
        _ = h := by
            calc F.sSO * (F.sSO * h * F.sSO) * F.sSO
                = (F.sSO * F.sSO) * h * (F.sSO * F.sSO) := by group
              _ = h := by rw [sSO_mul_self]; simp⟩

theorem disjoint_betaBase_swapSub (F : FrameData Q) (D : Subgroup (O2 K)) :
    Disjoint (betaBase F D) (swapSub F) := by
  rw [Subgroup.disjoint_def]
  intro x hxB hxC
  have hmem := (Subgroup.mem_zpowers_iff_of_orderOf_eq_two (orderOf_sSO F)).mp hxC
  rcases hmem with rfl | rfl
  · rfl
  · exact absurd hxB (sSO_not_mem_betaBase F D)

theorem wreathSub_card (F : FrameData Q) (D : Subgroup (O2 K)) {r : ℕ}
    (hD : Nat.card D = 2 ^ (r + 1)) :
    Nat.card (wreathSub F D) = 2 ^ (2 * r + 3) := by
  rw [wreathSub, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    (betaBase F D) (swapSub F) (swapSub_le_normalizer_betaBase F D)
    (disjoint_betaBase_swapSub F D)]
  rw [betaBase_card F D hD, swapSub_card F]
  calc 2 ^ (2 * r + 2) * 2 = 2 ^ (2 * r + 2) * 2 ^ 1 := by norm_num
    _ = 2 ^ ((2 * r + 2) + 1) := by rw [← pow_add]
    _ = 2 ^ (2 * r + 3) := by congr 1

theorem wreathSub_sylow (F : FrameData Q) (D : Subgroup (O2 K)) {r u : ℕ}
    (hD : Nat.card D = 2 ^ (r + 1))
    (hSOcard : Nat.card Q.specialOrthogonalWithin = 2 ^ (2 * r + 3) * u)
    (hodd_u : Odd u) :
    ∃ hS : Sylow 2 Q.specialOrthogonalWithin,
      (hS : Subgroup Q.specialOrthogonalWithin) = wreathSub F D := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Subgroup Q.specialOrthogonalWithin := wreathSub F D
  have hScard : Nat.card S = 2 ^ (2 * r + 3) := wreathSub_card F D hD
  have hSp : IsPGroup 2 ↥S := IsPGroup.of_card (n := 2 * r + 3) hScard
  have hpos : 0 < 2 ^ (2 * r + 3) := pow_pos (by norm_num) _
  have hSindex : S.index = u := by
    have hm := Subgroup.index_mul_card (G := Q.specialOrthogonalWithin) (H := S)
    rw [hScard, hSOcard] at hm
    rw [mul_comm S.index (2 ^ (2 * r + 3))] at hm
    exact Nat.eq_of_mul_eq_mul_left hpos hm
  have hodd : ¬ 2 ∣ S.index := by rw [hSindex]; exact hodd_u.not_two_dvd_nat
  exact ⟨hSp.toSylow hodd, IsPGroup.toSylow_coe hSp hodd⟩

theorem tO_mul_self (F : FrameData Q) : F.tO * F.tO = 1 := by
  apply Subtype.ext
  exact F.t_mul_self

theorem zO_mul_self (F : FrameData Q) : F.zO * F.zO = 1 := by
  apply Subtype.ext
  exact F.z_mul_self

theorem tO_ne_one (F : FrameData Q) : F.tO ≠ 1 := by
  intro h
  have h0 := congrArg (fun g : TauCeti.QuadraticMap.orthogonalGroup Q =>
    F.coord ((g : V ≃ₗ[K] V) (F.e 0))) h
  rw [F.t_e] at h0
  simp only [FrameData.coord_e, OneMemClass.coe_one, LinearEquiv.coe_one, id_eq,
    map_neg] at h0
  have h1 := congrFun h0 0
  simp at h1
  exact F.two_ne_zero (by
    have h := congrArg (fun x : K => x + 1) h1
    have hzero : (1 : K) + 1 = 0 := by simpa using h.symm
    have htwo : (2 : K) = 1 + 1 := by ring
    rw [htwo]
    exact hzero)

theorem zO_ne_one (F : FrameData Q) : F.zO ≠ 1 := by
  intro h
  have h0 := congrArg (fun g : TauCeti.QuadraticMap.orthogonalGroup Q =>
    F.coord ((g : V ≃ₗ[K] V) (F.e 0))) h
  rw [F.z_e] at h0
  simp only [FrameData.coord_e, OneMemClass.coe_one, LinearEquiv.coe_one, id_eq,
    map_neg] at h0
  have h1 := congrFun h0 0
  simp at h1
  exact F.two_ne_zero (by
    have h := congrArg (fun x : K => x + 1) h1
    have hzero : (1 : K) + 1 = 0 := by simpa using h.symm
    have htwo : (2 : K) = 1 + 1 := by ring
    rw [htwo]
    exact hzero)

theorem negOneO2_commute (d : O2 K) : d * negOneO2 = negOneO2 * d := by
  apply Subtype.ext
  change (d : GL (Fin 2) K) * (-1 : GL (Fin 2) K) =
    (-1 : GL (Fin 2) K) * (d : GL (Fin 2) K)
  simp [mul_neg, neg_mul]

theorem betaO_negOneO2_one (F : FrameData Q) :
    F.betaO negOneO2 (1 : O2 K) = F.tO := by
  apply Subtype.ext
  exact congrArg (fun g : Q.specialOrthogonalWithin => (g : V ≃ₗ[K] V))
    (sSO_neg_one_one F)

theorem betaO_one_negOneO2 (F : FrameData Q) :
    F.betaO (1 : O2 K) negOneO2 = F.zO * F.tO := by
  apply Subtype.ext
  exact congrArg (fun g : Q.specialOrthogonalWithin => (g : V ≃ₗ[K] V))
    (sSO_one_neg_one F)

theorem betaO_commute_tO (F : FrameData Q) (d1 d2 : O2 K) :
    F.betaO d1 d2 * F.tO = F.tO * F.betaO d1 d2 := by
  calc F.betaO d1 d2 * F.tO
      = F.betaO d1 d2 * F.betaO negOneO2 1 := by rw [betaO_negOneO2_one]
    _ = F.betaO (d1 * negOneO2) (d2 * 1) := F.betaO_mul d1 d2 negOneO2 1
    _ = F.betaO (negOneO2 * d1) (1 * d2) := by
        rw [negOneO2_commute d1]
        simp
    _ = F.betaO negOneO2 1 * F.betaO d1 d2 := (F.betaO_mul negOneO2 1 d1 d2).symm
    _ = F.tO * F.betaO d1 d2 := by rw [betaO_negOneO2_one]

theorem betaO_commute_zO (F : FrameData Q) (d1 d2 : O2 K) :
    F.betaO d1 d2 * F.zO = F.zO * F.betaO d1 d2 := by
  have hz : F.zO = F.betaO negOneO2 negOneO2 := by
    apply Subtype.ext
    exact (congrArg (fun g : Q.specialOrthogonalWithin => (g : V ≃ₗ[K] V))
      (sSO_neg_one_neg_one F)).symm
  calc F.betaO d1 d2 * F.zO
      = F.betaO d1 d2 * F.betaO negOneO2 negOneO2 := by rw [hz]
    _ = F.betaO (d1 * negOneO2) (d2 * negOneO2) :=
        F.betaO_mul d1 d2 negOneO2 negOneO2
    _ = F.betaO (negOneO2 * d1) (negOneO2 * d2) := by
        rw [negOneO2_commute d1, negOneO2_commute d2]
    _ = F.betaO negOneO2 negOneO2 * F.betaO d1 d2 :=
        (F.betaO_mul negOneO2 negOneO2 d1 d2).symm
    _ = F.zO * F.betaO d1 d2 := by rw [hz]

theorem zO_commute_tO (F : FrameData Q) : F.zO * F.tO = F.tO * F.zO := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply F.e.ext
  intro i
  change F.z (F.t (F.e i)) = F.t (F.z (F.e i))
  fin_cases i <;> simp [F.t_e, F.z_e]

@[expose] def normalFour (F : FrameData Q) :
    Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q) :=
  Subgroup.zpowers F.zO ⊔ Subgroup.zpowers F.tO

theorem zO_order (F : FrameData Q) : orderOf F.zO = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (p := 2) (by rw [pow_two]; exact zO_mul_self F) (zO_ne_one F)

theorem tO_order (F : FrameData Q) : orderOf F.tO = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (p := 2) (by rw [pow_two]; exact tO_mul_self F) (tO_ne_one F)

theorem zO_ne_tO (F : FrameData Q) : F.zO ≠ F.tO := by
  intro h
  have hz : F.z (F.e 2) = -F.e 2 := by rw [F.z_e]; norm_num
  have ht : F.t (F.e 2) = F.e 2 := by rw [F.t_e]; norm_num
  have h0 : F.z (F.e 2) = F.t (F.e 2) :=
    congrArg (fun g : TauCeti.QuadraticMap.orthogonalGroup Q =>
      (g : V ≃ₗ[K] V) (F.e 2)) h
  rw [hz, ht] at h0
  have h1 := congrArg (fun v : V => F.coord v 2) h0
  simp [FrameData.coord_e] at h1
  exact F.two_ne_zero (by
    have h2 := congrArg (fun x : K => x + 1) h1
    have hzero : (1 : K) + 1 = 0 := by simpa using h2.symm
    have htwo : (2 : K) = 1 + 1 := by ring
    rw [htwo]
    exact hzero)

private theorem zpowers_tO_le_normalizer_zpowers_zO (F : FrameData Q) :
    Subgroup.zpowers F.tO ≤
      Subgroup.normalizer (Subgroup.zpowers F.zO : Set (TauCeti.QuadraticMap.orthogonalGroup Q)) := by
  have ht2 : F.tO * F.tO = 1 := tO_mul_self F
  have ht : F.tO⁻¹ = F.tO := inv_eq_of_mul_eq_one_right ht2
  have hforward : ∀ x, x ∈ Subgroup.zpowers F.zO →
      F.tO * x * F.tO⁻¹ ∈ Subgroup.zpowers F.zO := by
    intro x hx
    have hx' := (Subgroup.mem_zpowers_iff_of_orderOf_eq_two (zO_order F)).mp hx
    rcases hx' with rfl | rfl
    · simp
    · rw [ht]
      have hcomm := (zO_commute_tO F).symm
      have heq : F.tO * F.zO * F.tO = F.zO := by
        calc F.tO * F.zO * F.tO
            = F.zO * (F.tO * F.tO) := by
                calc F.tO * F.zO * F.tO = (F.tO * F.zO) * F.tO := by group
                  _ = (F.zO * F.tO) * F.tO := by rw [hcomm]
                  _ = F.zO * (F.tO * F.tO) := by group
          _ = F.zO := by rw [ht2]; simp
      rw [heq]
      exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
  refine Subgroup.zpowers_le.mpr ?_
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hforward x
  · intro hx
    have h := hforward (F.tO * x * F.tO⁻¹) hx
    have heq : F.tO * (F.tO * x * F.tO⁻¹) * F.tO⁻¹ = x := by
      rw [ht]
      calc F.tO * (F.tO * x * F.tO) * F.tO
          = (F.tO * F.tO) * x * (F.tO * F.tO) := by group
        _ = x := by rw [ht2]; simp
    rwa [heq] at h

theorem mem_normalFour_iff (F : FrameData Q)
    (x : TauCeti.QuadraticMap.orthogonalGroup Q) :
    x ∈ normalFour F ↔ x = 1 ∨ x = F.zO ∨ x = F.tO ∨ x = F.zO * F.tO := by
  have hzord := zO_order F
  have htord := tO_order F
  have hLE : Subgroup.zpowers F.tO ≤
      Subgroup.normalizer (Subgroup.zpowers F.zO : Set (TauCeti.QuadraticMap.orthogonalGroup Q)) :=
    zpowers_tO_le_normalizer_zpowers_zO F
  have hmem : x ∈ Subgroup.zpowers F.zO ⊔ Subgroup.zpowers F.tO ↔
      x = 1 ∨ x = F.zO ∨ x = F.tO ∨ x = F.zO * F.tO := by
    constructor
    · intro hx
      obtain ⟨y, hy, z, hz, hxyz⟩ :=
        (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left
          (H := Subgroup.zpowers F.zO) (K := Subgroup.zpowers F.tO) hLE).mp hx
      have hy' := (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hzord).mp hy
      have hz' := (Subgroup.mem_zpowers_iff_of_orderOf_eq_two htord).mp hz
      rw [hxyz]
      rcases hy' with rfl | rfl <;> rcases hz' with rfl | rfl <;> simp
    · rintro (rfl | rfl | rfl | rfl)
      · refine (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left
          (H := Subgroup.zpowers F.zO) (K := Subgroup.zpowers F.tO) hLE).mpr
          ⟨1, by simp, 1, by simp, by simp⟩
      · refine (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left
          (H := Subgroup.zpowers F.zO) (K := Subgroup.zpowers F.tO) hLE).mpr
          ⟨F.zO, Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩, 1, by simp, by simp⟩
      · refine (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left
          (H := Subgroup.zpowers F.zO) (K := Subgroup.zpowers F.tO) hLE).mpr
          ⟨1, by simp, F.tO, Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩, by simp⟩
      · refine (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left
          (H := Subgroup.zpowers F.zO) (K := Subgroup.zpowers F.tO) hLE).mpr
          ⟨F.zO, Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩,
            F.tO, Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩, rfl⟩
  simpa [normalFour] using hmem

private theorem zpowers_zO_le_normalizer_zpowers_tO (F : FrameData Q) :
    Subgroup.zpowers F.zO ≤
      Subgroup.normalizer (Subgroup.zpowers F.tO : Set (TauCeti.QuadraticMap.orthogonalGroup Q)) := by
  have hz2 : F.zO * F.zO = 1 := zO_mul_self F
  have hz : F.zO⁻¹ = F.zO := inv_eq_of_mul_eq_one_right hz2
  have hforward : ∀ x, x ∈ Subgroup.zpowers F.tO →
      F.zO * x * F.zO⁻¹ ∈ Subgroup.zpowers F.tO := by
    intro x hx
    have hx' := (Subgroup.mem_zpowers_iff_of_orderOf_eq_two (tO_order F)).mp hx
    rcases hx' with rfl | rfl
    · simp
    · rw [hz]
      have hcomm := zO_commute_tO F
      have heq : F.zO * F.tO * F.zO = F.tO := by
        calc F.zO * F.tO * F.zO
            = F.tO * (F.zO * F.zO) := by
                calc F.zO * F.tO * F.zO = (F.zO * F.tO) * F.zO := by group
                  _ = (F.tO * F.zO) * F.zO := by rw [hcomm]
                  _ = F.tO * (F.zO * F.zO) := by group
          _ = F.tO := by rw [hz2]; simp
      rw [heq]
      exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
  refine Subgroup.zpowers_le.mpr ?_
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hforward x
  · intro hx
    have h := hforward (F.zO * x * F.zO⁻¹) hx
    have heq : F.zO * (F.zO * x * F.zO⁻¹) * F.zO⁻¹ = x := by
      rw [hz]
      calc F.zO * (F.zO * x * F.zO) * F.zO
          = (F.zO * F.zO) * x * (F.zO * F.zO) := by group
        _ = x := by rw [hz2]; simp
    rwa [heq] at h

private theorem disjoint_zpowers_zO_zpowers_tO (F : FrameData Q) :
    Disjoint (Subgroup.zpowers F.zO) (Subgroup.zpowers F.tO) := by
  rw [Subgroup.disjoint_def]
  intro x hx hz
  have hx' := (Subgroup.mem_zpowers_iff_of_orderOf_eq_two (zO_order F)).mp hx
  have hz' := (Subgroup.mem_zpowers_iff_of_orderOf_eq_two (tO_order F)).mp hz
  rcases hx' with hx1 | hxz
  · rw [hx1]
  · rcases hz' with hz1 | hzt
    · exfalso; exact (zO_ne_one F) (hxz.symm.trans hz1)
    · exfalso; exact (zO_ne_tO F) (hxz.symm.trans hzt)

theorem normalFour_card (F : FrameData Q) : Nat.card (normalFour F) = 4 := by
  rw [normalFour, sup_comm (Subgroup.zpowers F.zO) (Subgroup.zpowers F.tO),
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    (Subgroup.zpowers F.tO) (Subgroup.zpowers F.zO)
    (zpowers_zO_le_normalizer_zpowers_tO F) (disjoint_zpowers_zO_zpowers_tO F).symm]
  rw [Nat.card_zpowers, Nat.card_zpowers, zO_order F, tO_order F]

@[expose] def betaBaseO (F : FrameData Q) (D : Subgroup (O2 K)) :
    Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q) :=
  (D.prod D).map F.betaHom

@[expose] def swapSubO (F : FrameData Q) :
    Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q) :=
  Subgroup.zpowers F.sO

@[expose] def wreathO (F : FrameData Q) (D : Subgroup (O2 K)) :
    Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q) :=
  betaBaseO F D ⊔ swapSubO F

theorem wreathSub_map_eq (F : FrameData Q) (D : Subgroup (O2 K)) :
    (wreathSub F D).map (Q.specialOrthogonalWithin).subtype = wreathO F D := by
  rw [wreathSub, wreathO, Subgroup.map_sup, betaBase, betaBaseO, swapSub, swapSubO,
    Subgroup.map_map, MonoidHom.map_zpowers]
  rfl

theorem betaO_conj_mem_normalFour (F : FrameData Q) (d1 d2 : O2 K)
    {x : TauCeti.QuadraticMap.orthogonalGroup Q} (hx : x ∈ normalFour F) :
    F.betaO d1 d2 * x * (F.betaO d1 d2)⁻¹ ∈ normalFour F := by
  have hcz : F.betaO d1 d2 * F.zO * (F.betaO d1 d2)⁻¹ = F.zO := by
    rw [betaO_commute_zO F d1 d2]
    group
  have hct : F.betaO d1 d2 * F.tO * (F.betaO d1 d2)⁻¹ = F.tO := by
    rw [betaO_commute_tO F d1 d2]
    group
  rcases (mem_normalFour_iff F x).mp hx with rfl | rfl | rfl | rfl
  · simp
  · rw [hcz]
    exact (mem_normalFour_iff F F.zO).mpr (Or.inr (Or.inl rfl))
  · rw [hct]
    exact (mem_normalFour_iff F F.tO).mpr (Or.inr (Or.inr (Or.inl rfl)))
  · have hzt : F.betaO d1 d2 * (F.zO * F.tO) * (F.betaO d1 d2)⁻¹ =
        F.zO * F.tO := by
      calc F.betaO d1 d2 * (F.zO * F.tO) * (F.betaO d1 d2)⁻¹
          = (F.betaO d1 d2 * F.zO * (F.betaO d1 d2)⁻¹) *
              (F.betaO d1 d2 * F.tO * (F.betaO d1 d2)⁻¹) := by group
        _ = F.zO * F.tO := by rw [hcz, hct]
    rw [hzt]
    exact (mem_normalFour_iff F (F.zO * F.tO)).mpr (Or.inr (Or.inr (Or.inr rfl)))

theorem betaBaseO_le_normalizer_normalFour (F : FrameData Q)
    (D : Subgroup (O2 K)) :
    betaBaseO F D ≤ Subgroup.normalizer (normalFour F : Set (TauCeti.QuadraticMap.orthogonalGroup Q)) := by
  intro b hb
  obtain ⟨p, -, rfl⟩ := Subgroup.mem_map.mp hb
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : (normalFour F).map (MulAut.conj (F.betaO p.1 p.2)).toMonoidHom ≤
      normalFour F := by
    rintro a ha
    obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp ha
    rw [← hxa]
    exact betaO_conj_mem_normalFour F p.1 p.2 hx
  have hcard : Nat.card (normalFour F) ≤
      Nat.card ((normalFour F).map (MulAut.conj (F.betaO p.1 p.2)).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj (F.betaO p.1 p.2)).injective]
  exact Subgroup.eq_of_le_of_card_ge hle hcard

theorem betaO_negOneO2_negOneO2 (F : FrameData Q) :
    F.betaO negOneO2 negOneO2 = F.zO := by
  apply Subtype.ext
  exact congrArg (fun g : Q.specialOrthogonalWithin => (g : V ≃ₗ[K] V))
    (sSO_neg_one_neg_one F)

theorem sO_conj_zO (F : FrameData Q) :
    F.sO * F.zO * F.sO⁻¹ = F.zO := by
  have hs : F.sO⁻¹ = F.sO := inv_eq_of_mul_eq_one_right F.sO_mul_self
  simpa [hs, betaO_negOneO2_negOneO2] using
    (F.sO_betaO_conj' negOneO2 negOneO2)

theorem sO_conj_tO (F : FrameData Q) :
    F.sO * F.tO * F.sO⁻¹ = F.zO * F.tO := by
  have hs : F.sO⁻¹ = F.sO := inv_eq_of_mul_eq_one_right F.sO_mul_self
  simpa [hs, betaO_negOneO2_one, betaO_one_negOneO2] using
    (F.sO_betaO_conj' negOneO2 1)

theorem sO_conj_zt (F : FrameData Q) :
    F.sO * (F.zO * F.tO) * F.sO⁻¹ = F.tO := by
  have hs : F.sO⁻¹ = F.sO := inv_eq_of_mul_eq_one_right F.sO_mul_self
  rw [hs]
  have hcz : F.sO * F.zO * F.sO = F.zO := by simpa [hs] using sO_conj_zO F
  have hct : F.sO * F.tO * F.sO = F.zO * F.tO := by simpa [hs] using sO_conj_tO F
  have hss : F.sO * F.sO = 1 := F.sO_mul_self
  have hsplit : F.sO * (F.zO * F.tO) * F.sO =
      (F.sO * F.zO * F.sO) * (F.sO * F.tO * F.sO) := by
    rw [show (F.sO * F.zO * F.sO) * (F.sO * F.tO * F.sO) =
        F.sO * F.zO * (F.sO * F.sO) * F.tO * F.sO by group]
    rw [hss]
    group
  calc F.sO * (F.zO * F.tO) * F.sO
      = (F.sO * F.zO * F.sO) * (F.sO * F.tO * F.sO) := hsplit
    _ = F.zO * (F.zO * F.tO) := by rw [hcz, hct]
    _ = F.tO := by rw [← mul_assoc, zO_mul_self]; simp

theorem sO_conj_mem_normalFour (F : FrameData Q)
    {x : TauCeti.QuadraticMap.orthogonalGroup Q} (hx : x ∈ normalFour F) :
    F.sO * x * F.sO⁻¹ ∈ normalFour F := by
  rcases (mem_normalFour_iff F x).mp hx with rfl | rfl | rfl | rfl
  · simp
  · rw [sO_conj_zO]
    exact (mem_normalFour_iff F F.zO).mpr (Or.inr (Or.inl rfl))
  · rw [sO_conj_tO]
    exact (mem_normalFour_iff F (F.zO * F.tO)).mpr (Or.inr (Or.inr (Or.inr rfl)))
  · rw [sO_conj_zt]
    exact (mem_normalFour_iff F F.tO).mpr (Or.inr (Or.inr (Or.inl rfl)))


theorem sO_mem_normalizer_normalFour (F : FrameData Q) :
    F.sO ∈ Subgroup.normalizer (normalFour F : Set (TauCeti.QuadraticMap.orthogonalGroup Q)) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : (normalFour F).map (MulAut.conj F.sO).toMonoidHom ≤ normalFour F := by
    rintro a ha
    obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp ha
    rw [← hxa]
    exact sO_conj_mem_normalFour F hx
  have hcard : Nat.card (normalFour F) ≤
      Nat.card ((normalFour F).map (MulAut.conj F.sO).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj F.sO).injective]
  exact Subgroup.eq_of_le_of_card_ge hle hcard

theorem swapSubO_le_normalizer_normalFour (F : FrameData Q) :
    swapSubO F ≤
      Subgroup.normalizer (normalFour F : Set (TauCeti.QuadraticMap.orthogonalGroup Q)) := by
  rw [swapSubO, Subgroup.zpowers_le]
  exact sO_mem_normalizer_normalFour F

theorem wreathO_le_normalizer_normalFour (F : FrameData Q) (D : Subgroup (O2 K)) :
    wreathO F D ≤ Subgroup.normalizer (normalFour F : Set (TauCeti.QuadraticMap.orthogonalGroup Q)) := by
  rw [wreathO]
  exact sup_le (betaBaseO_le_normalizer_normalFour F D) (swapSubO_le_normalizer_normalFour F)

theorem tSO_mul_self (F : FrameData Q) : F.tSO * F.tSO = 1 := by
  apply Subtype.ext
  exact tO_mul_self F

theorem zSO_mul_self (F : FrameData Q) : F.zSO * F.zSO = 1 := by
  apply Subtype.ext
  exact zO_mul_self F

theorem tSO_ne_one (F : FrameData Q) : F.tSO ≠ 1 := fun h =>
  tO_ne_one F (congrArg (fun g : Q.specialOrthogonalWithin => (g : TauCeti.QuadraticMap.orthogonalGroup Q)) h)

theorem zSO_ne_one (F : FrameData Q) : F.zSO ≠ 1 := fun h =>
  zO_ne_one F (congrArg (fun g : Q.specialOrthogonalWithin => (g : TauCeti.QuadraticMap.orthogonalGroup Q)) h)

theorem zSO_ne_tSO (F : FrameData Q) : F.zSO ≠ F.tSO := fun h =>
  zO_ne_tO F (congrArg (fun g : Q.specialOrthogonalWithin => (g : TauCeti.QuadraticMap.orthogonalGroup Q)) h)

theorem zSO_commute_tSO (F : FrameData Q) :
    F.zSO * F.tSO = F.tSO * F.zSO := by
  apply Subtype.ext
  exact zO_commute_tO F

theorem betaSO_commute_tSO (F : FrameData Q) (d1 d2 : O2 K) :
    F.betaSO d1 d2 * F.tSO = F.tSO * F.betaSO d1 d2 := by
  apply Subtype.ext
  exact betaO_commute_tO F d1 d2

theorem betaSO_commute_zSO (F : FrameData Q) (d1 d2 : O2 K) :
    F.betaSO d1 d2 * F.zSO = F.zSO * F.betaSO d1 d2 := by
  apply Subtype.ext
  exact betaO_commute_zO F d1 d2

theorem sSO_conj_tSO (F : FrameData Q) :
    F.sSO * F.tSO * F.sSO⁻¹ = F.zSO * F.tSO := by
  have hs : F.sSO⁻¹ = F.sSO := inv_eq_of_mul_eq_one_right (sSO_mul_self F)
  simpa [hs, sSO_neg_one_one, sSO_one_neg_one] using
    (sSO_betaSO_conj F negOneO2 1)

theorem sSO_conj_zSO (F : FrameData Q) :
    F.sSO * F.zSO * F.sSO⁻¹ = F.zSO := by
  have hs : F.sSO⁻¹ = F.sSO := inv_eq_of_mul_eq_one_right (sSO_mul_self F)
  simpa [hs, sSO_neg_one_neg_one] using
    (sSO_betaSO_conj F negOneO2 negOneO2)

theorem mem_center_planeD_iff (c : GL (Fin 2) K) (hc : c ∈ SO2 K)
    (hcenter_iff : ∀ y : planeSylow c,
      y ∈ Subgroup.center (planeSylow c) ↔
        (y : GL (Fin 2) K) = 1 ∨ (y : GL (Fin 2) K) = -1)
    (x : planeD c) :
    x ∈ Subgroup.center (planeD c) ↔
      (x : GL (Fin 2) K) = 1 ∨ (x : GL (Fin 2) K) = -1 := by
  let e : planeD c ≃* planeSylow c :=
    Subgroup.subgroupOfEquivOfLe (planeSylow_le_O2 hc)
  have hmap := Subgroup.map_center_eq e
  have hx : e x ∈ Subgroup.center (planeSylow c) ↔ x ∈ Subgroup.center (planeD c) := by
    rw [← hmap, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hyx' : y = x := e.injective hyx
      simpa [hyx'] using hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  rw [← hx]
  have he : (e x : GL (Fin 2) K) = (x : GL (Fin 2) K) := rfl
  have hiff := hcenter_iff (e x)
  rw [he] at hiff
  exact hiff

theorem wreathSub_le_centralizer_zSO (F : FrameData Q) (D : Subgroup (O2 K)) :
    wreathSub F D ≤ Subgroup.centralizer ({F.zSO} : Set Q.specialOrthogonalWithin) := by
  rw [wreathSub]
  refine sup_le ?_ ?_
  · intro b hb
    obtain ⟨p, -, rfl⟩ := Subgroup.mem_map.mp hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact betaSO_commute_zSO F p.1 p.2
  · intro s hs
    rw [swapSub] at hs
    have hs' := (Subgroup.mem_zpowers_iff_of_orderOf_eq_two (orderOf_sSO F)).mp hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases hs' with rfl | rfl
    · simp
    · have hss : F.sSO * F.sSO = 1 := sSO_mul_self F
      have hinv : F.sSO⁻¹ = F.sSO := inv_eq_of_mul_eq_one_right hss
      have h := sSO_conj_zSO F
      rw [hinv] at h
      calc F.sSO * F.zSO
          = F.sSO * F.zSO * (F.sSO * F.sSO) := by rw [hss]; simp
        _ = (F.sSO * F.zSO * F.sSO) * F.sSO := by group
        _ = F.zSO * F.sSO := by rw [h]

theorem center_of_subgroup_le_wreath (F : FrameData Q) (D : Subgroup (O2 K))
    (P : Subgroup Q.specialOrthogonalWithin)
    (hPle : P ≤ wreathSub F D) (ht : F.tSO ∈ P) (hz : F.zSO ∈ P) (hs : F.sSO ∈ P)
    (hdiag : ∀ d : D, F.betaSO d d ∈ P)
    (hDcenter : ∀ x : D, x ∈ Subgroup.center D ↔
      (x : GL (Fin 2) K) = 1 ∨ (x : GL (Fin 2) K) = -1) :
    (Subgroup.center P).map ((Q.specialOrthogonalWithin).subtype.comp P.subtype) =
      Subgroup.zpowers F.zO := by
  apply le_antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hxS : (x : Q.specialOrthogonalWithin) ∈ wreathSub F D := hPle x.property
    obtain ⟨b, hb, c, hcC, hxbc⟩ :=
      (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left
        (H := betaBase F D) (K := swapSub F) (swapSub_le_normalizer_betaBase F D)).mp hxS
    have hcCases := (Subgroup.mem_zpowers_iff_of_orderOf_eq_two (orderOf_sSO F)).mp hcC
    rcases hcCases with hc1 | hcs
    ·
      have hx_b : (x : Q.specialOrthogonalWithin) = b := by simpa [hc1] using hxbc
      obtain ⟨p, hp, hpb⟩ := Subgroup.mem_map.mp hb
      have hx_beta : (x : Q.specialOrthogonalWithin) = F.betaSO p.1 p.2 := by
        rw [hx_b, ← hpb]
        rfl
      have hcomm_diag : ∀ d : D,
          F.betaSO d d * (x : Q.specialOrthogonalWithin) =
            (x : Q.specialOrthogonalWithin) * F.betaSO d d := by
        intro d
        have h := (Subgroup.mem_center_iff (G := P)).mp hx ⟨F.betaSO d d, hdiag d⟩
        exact congrArg (fun g : P => (g : Q.specialOrthogonalWithin)) h
      have hcomm_p : ∀ d : D, d * p.1 = p.1 * d ∧ d * p.2 = p.2 * d := by
        intro d
        have h := hcomm_diag d
        rw [hx_beta, betaSO_mul, betaSO_mul] at h
        have hpairs : (d * p.1, d * p.2) = (p.1 * d, p.2 * d) :=
          betaSOHom_injective F (by simpa [betaSOHom] using h)
        exact ⟨congrArg Prod.fst hpairs, congrArg Prod.snd hpairs⟩
      have hp1_center : (⟨p.1, hp.1⟩ : D) ∈ Subgroup.center D := by
        rw [Subgroup.mem_center_iff]
        intro d
        exact Subtype.ext (hcomm_p d).1
      have hp2_center : (⟨p.2, hp.2⟩ : D) ∈ Subgroup.center D := by
        rw [Subgroup.mem_center_iff]
        intro d
        exact Subtype.ext (hcomm_p d).2
      have hp1 := hDcenter ⟨p.1, hp.1⟩ |>.mp hp1_center
      have hp2 := hDcenter ⟨p.2, hp.2⟩ |>.mp hp2_center
      have hcomm_s : F.sSO * (x : Q.specialOrthogonalWithin) =
          (x : Q.specialOrthogonalWithin) * F.sSO := by
        have h := (Subgroup.mem_center_iff (G := P)).mp hx ⟨F.sSO, hs⟩
        exact congrArg (fun g : P => (g : Q.specialOrthogonalWithin)) h
      have hinv : F.sSO⁻¹ = F.sSO := inv_eq_of_mul_eq_one_right (sSO_mul_self F)
      have hconj : F.sSO * F.betaSO p.1 p.2 * F.sSO⁻¹ = F.betaSO p.1 p.2 := by
        rw [← hx_beta]
        rw [hcomm_s]
        group
      have hswap := sSO_betaSO_conj F p.1 p.2
      have hp_eq : F.betaSO p.2 p.1 = F.betaSO p.1 p.2 := by
        rw [← hswap, hconj]
      have hpairs : (p.2, p.1) = (p.1, p.2) :=
        betaSOHom_injective F (by simpa [betaSOHom] using hp_eq)
      have hp21 : p.2 = p.1 := (Prod.ext_iff.mp hpairs).1
      have hx_beta' : (x : Q.specialOrthogonalWithin) = F.betaSO p.1 p.1 := by
        rw [hx_beta, hp21]
      rcases hp1 with hp1 | hp1
      · have hp1gl : (p.1 : GL (Fin 2) K) = 1 := by simpa using hp1
        have hp1O2 : p.1 = (1 : O2 K) := Subtype.ext hp1gl
        have hx_one : (x : Q.specialOrthogonalWithin) = 1 := by
          rw [hx_beta', hp1O2]
          exact betaSO_one_one F
        have hxO : ((Q.specialOrthogonalWithin).subtype.comp P.subtype) x = 1 :=
          congrArg (fun g : Q.specialOrthogonalWithin => (g : TauCeti.QuadraticMap.orthogonalGroup Q)) hx_one
        rw [hxO]
        exact Subgroup.one_mem _
      · have hp1gl : (p.1 : GL (Fin 2) K) = -1 := by simpa using hp1
        have hp1O2 : p.1 = negOneO2 := Subtype.ext hp1gl
        have hx_z : (x : Q.specialOrthogonalWithin) = F.zSO := by
          rw [hx_beta', hp1O2]
          exact sSO_neg_one_neg_one F
        have hxO : ((Q.specialOrthogonalWithin).subtype.comp P.subtype) x = F.zO :=
          congrArg (fun g : Q.specialOrthogonalWithin => (g : TauCeti.QuadraticMap.orthogonalGroup Q)) hx_z
        rw [hxO]
        exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
    ·
      have hx_s : (x : Q.specialOrthogonalWithin) = b * F.sSO := by simpa [hcs] using hxbc
      obtain ⟨p, hp, hpb⟩ := Subgroup.mem_map.mp hb
      have hx_beta : (x : Q.specialOrthogonalWithin) = F.betaSO p.1 p.2 * F.sSO := by
        rw [hx_s, ← hpb]
        rfl
      have hcomm_t : F.tSO * (x : Q.specialOrthogonalWithin) =
          (x : Q.specialOrthogonalWithin) * F.tSO := by
        have h := (Subgroup.mem_center_iff (G := P)).mp hx ⟨F.tSO, ht⟩
        exact congrArg (fun g : P => (g : Q.specialOrthogonalWithin)) h
      have hconj_t : (x : Q.specialOrthogonalWithin) * F.tSO *
          (x : Q.specialOrthogonalWithin)⁻¹ = F.tSO := by
        calc (x : Q.specialOrthogonalWithin) * F.tSO * (x : Q.specialOrthogonalWithin)⁻¹
            = (F.tSO * (x : Q.specialOrthogonalWithin)) *
                (x : Q.specialOrthogonalWithin)⁻¹ := by rw [hcomm_t]
          _ = F.tSO := by group
      have hb_t : F.betaSO p.1 p.2 * F.tSO * (F.betaSO p.1 p.2)⁻¹ = F.tSO := by
        rw [betaSO_commute_tSO F p.1 p.2]
        group
      have hb_z : F.betaSO p.1 p.2 * F.zSO * (F.betaSO p.1 p.2)⁻¹ = F.zSO := by
        rw [betaSO_commute_zSO F p.1 p.2]
        group
      have hcalc : (x : Q.specialOrthogonalWithin) * F.tSO *
          (x : Q.specialOrthogonalWithin)⁻¹ = F.zSO * F.tSO := by
        rw [hx_beta]
        calc (F.betaSO p.1 p.2 * F.sSO) * F.tSO *
              (F.betaSO p.1 p.2 * F.sSO)⁻¹
            = F.betaSO p.1 p.2 * (F.sSO * F.tSO * F.sSO⁻¹) *
                (F.betaSO p.1 p.2)⁻¹ := by group
          _ = F.betaSO p.1 p.2 * (F.zSO * F.tSO) * (F.betaSO p.1 p.2)⁻¹ := by
              rw [sSO_conj_tSO]
          _ = (F.betaSO p.1 p.2 * F.zSO * (F.betaSO p.1 p.2)⁻¹) *
                (F.betaSO p.1 p.2 * F.tSO * (F.betaSO p.1 p.2)⁻¹) := by group
          _ = F.zSO * F.tSO := by rw [hb_z, hb_t]
      have hzt : F.zSO * F.tSO = F.tSO := by
        rw [← hcalc, hconj_t]
      have hz1 : F.zSO = 1 := by
        have h := congrArg (fun g : Q.specialOrthogonalWithin => g * F.tSO) hzt
        simpa [mul_assoc, tSO_mul_self] using h
      exact (zSO_ne_one F hz1).elim
  · rw [Subgroup.zpowers_le]
    let zP : P := ⟨F.zSO, hz⟩
    have hzcenter : zP ∈ Subgroup.center P := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp
        (wreathSub_le_centralizer_zSO F D (hPle g.property))
    exact Subgroup.mem_map.mpr ⟨zP, hzcenter, rfl⟩

public structure FiveDimensionalWreathData (F : FrameData Q) where
  c : GL (Fin 2) K
  r : ℕ
  hc : c ∈ SO2 K
  D : Subgroup (O2 K)
  hD : D = planeD c
  cD : D
  hcD : (cD : GL (Fin 2) K) = c
  hr2 : 2 ≤ r
  hordc : orderOf c = 2 ^ r
  hnegD : negOneO2 ∈ D
  hDcard : Nat.card D = 2 ^ (r + 1)
  hBcard : Nat.card (betaBase F D) = 2 ^ (2 * r + 2)
  S : Sylow 2 Q.specialOrthogonalWithin
  hScoe : (S : Subgroup Q.specialOrthogonalWithin) = wreathSub F D
  twoPart : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
    (Nat.card K : ℤ) ≡ ε [ZMOD 4] ∧
    ∃ m m0 : ℕ, (m : ℤ) = (Nat.card K : ℤ) - ε ∧
      m = 2 ^ r * m0 ∧ Odd m0
  planeSylowWitness : ∃ S : Sylow 2 (O2 K), (S : Subgroup (O2 K)) = D

theorem exists_wreathData (F : FrameData Q) (hodd : Odd (Nat.card K))
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K V = 5) :
    ∃ W : FiveDimensionalWreathData F,
      (∀ x : W.D, x ∈ Subgroup.center W.D ↔
        (x : GL (Fin 2) K) = 1 ∨ (x : GL (Fin 2) K) = -1) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hchar : ringChar K ≠ 2 := by
    intro hchar
    have hcard : Fintype.card K % 2 = 0 := FiniteField.even_card_of_char_two hchar
    have hodd' : Odd (Fintype.card K) := by
      simpa [Nat.card_eq_fintype_card] using hodd
    exact hodd'.not_two_dvd_nat (Nat.dvd_of_mod_eq_zero hcard)
  have htwo : (2 : K) ≠ 0 := by
    intro hzero
    exact hchar (by
      haveI : CharP K 2 := CFSG.GroupTheory.WeirSylow.charP_two_of_two_eq_zero hzero
      exact ringChar.eq K 2)
  obtain ⟨ε, hε, hq, m, n, h, hm, hn, hoddn, hh, hoddh⟩ :=
    CFSG.NumberTheory.exists_sign_mod_four_odd_cofactors (q := Nat.card K) hodd
  obtain ⟨c, hc, hordc, hneg, hle, hDcardP, hcenterEq, hcenterIff, -, hplaneSylowWitness⟩ :=
    exists_planeSylow (K := K) htwo ε hε hq m hm
  have hq3 : 3 ≤ Nat.card K := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card (α := K)
    have h2 : Nat.card K % 2 = 1 := Nat.odd_iff.mp hodd
    omega
  have hmpos : 0 < m := by
    rcases hε with rfl | rfl
    · have hmz : (m : ℤ) = (Nat.card K : ℤ) - 1 := by simpa using hm
      omega
    · have hmz : (m : ℤ) = (Nat.card K : ℤ) + 1 := by simpa using hm
      omega
  let r : ℕ := padicValNat 2 m
  let m' : ℕ := m.divMaxPow 2
  have hfac : m = 2 ^ r * m' := by
    dsimp only [r, m']
    exact (Nat.pow_padicValNat_mul_divMaxPow 2 m).symm
  have hm' : Odd m' := by
    have hnd : ¬ 2 ∣ m' := Nat.not_dvd_divMaxPow (p := 2) (n := m) (by norm_num)
      (Nat.pos_iff_ne_zero.mp hmpos)
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hnd)
  have hm'pos : 0 < m' := by
    rcases Nat.eq_zero_or_pos m' with h | h
    · rw [h, mul_zero] at hfac
      omega
    · exact h
  have h4Z : (4 : ℤ) ∣ (m : ℤ) := by
    have h := hq
    rw [Int.modEq_iff_dvd] at h
    rw [hm]
    have hneg : (Nat.card K : ℤ) - ε = -(ε - (Nat.card K : ℤ)) := by ring
    rw [hneg]
    exact dvd_neg.mpr h
  have h4 : 4 ∣ m := by exact_mod_cast h4Z
  have hr2 : 2 ≤ r := by
    have h4pow : 4 ∣ 2 ^ r := by
      have hdec : 2 ^ r * m' = m := hfac.symm
      have hcop : Nat.Coprime 4 m' := by
        simpa using (Nat.coprime_two_left.mpr hm').pow_left 2
      have hmul4 : 4 ∣ 2 ^ r * m' := by rw [hdec]; exact h4
      exact hcop.dvd_of_dvd_mul_right hmul4
    have hle : 4 ≤ 2 ^ r := Nat.le_of_dvd (by positivity) h4pow
    by_contra h
    have hrle : r ≤ 1 := by omega
    have h2le : 2 ^ r ≤ 2 := by
      calc 2 ^ r ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hrle
        _ = 2 := by norm_num
    omega
  let D : Subgroup (O2 K) := planeD c
  have hDcard : Nat.card D = 2 ^ (r + 1) := by
    dsimp only [D, planeD]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hDcardP]
  let u : ℕ := Nat.card K ^ 4 * m' ^ 2 * n ^ 2 * h
  have hSOcard : Nat.card Q.specialOrthogonalWithin = 2 ^ (2 * r + 3) * u := by
    dsimp only [u]
    exact natCard_specialOrthogonalWithin_five_two_part F hodd hQ hdim hε hm hn hh hfac
  have hodd_u : Odd u := by
    have hq4 : Odd (Nat.card K ^ 4) := hodd.pow
    have hm2 : Odd (m' ^ 2) := hm'.pow
    have hn2 : Odd (n ^ 2) := hoddn.pow
    exact ((hq4.mul hm2).mul hn2).mul hoddh
  obtain ⟨hS, hScoe⟩ := wreathSub_sylow F D hDcard hSOcard hodd_u
  have hnegD : negOneO2 ∈ D := by
    dsimp only [D, planeD, negOneO2]
    exact Subgroup.mem_subgroupOf.mpr (by simpa using neg_one_mem_planeSylow hneg)
  have hcplane : c ∈ planeSylow c := by
    rw [mem_planeSylow_iff hc]
    exact ⟨1, Or.inl (by rw [zpow_one])⟩
  have hcDmem : (⟨c, planeSylow_le_O2 hc hcplane⟩ : O2 K) ∈ D := by
    dsimp only [D, planeD]
    exact Subgroup.mem_subgroupOf.mpr hcplane
  let cD : D := ⟨⟨c, planeSylow_le_O2 hc hcplane⟩, hcDmem⟩
  have hcD : (cD : GL (Fin 2) K) = c := rfl
  have hBcard : Nat.card (betaBase F D) = 2 ^ (2 * r + 2) := betaBase_card F D hDcard
  have hplaneSylow : ∃ S : Sylow 2 (O2 K), (S : Subgroup (O2 K)) = D := by
    simpa only [D, planeD] using hplaneSylowWitness
  have htwoPart : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      (Nat.card K : ℤ) ≡ ε [ZMOD 4] ∧
      ∃ m m0 : ℕ, (m : ℤ) = (Nat.card K : ℤ) - ε ∧
        m = 2 ^ r * m0 ∧ Odd m0 :=
    ⟨ε, hε, hq, m, m', hm, hfac, hm'⟩
  refine ⟨⟨c, r, hc, D, rfl, cD, hcD, hr2, hordc, hnegD, hDcard, hBcard, hS, hScoe,
    htwoPart, hplaneSylow⟩, ?_⟩
  intro x
  exact mem_center_planeD_iff c hc hcenterIff x

private lemma map_center_eq_of_mulEquiv_commute
    {A B X : Type*} [Group A] [Group B] [Group X]
    (e : A ≃* B) (fA : A →* X) (fB : B →* X)
    (hcomm : ∀ x, fA x = fB (e x)) :
    (Subgroup.center A).map fA = (Subgroup.center B).map fB := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine Subgroup.mem_map.mpr ⟨e x, ?_, (hcomm x).symm⟩
    rw [← Subgroup.map_center_eq e]
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    refine Subgroup.mem_map.mpr ⟨e.symm y, ?_, ?_⟩
    · have hx' : e (e.symm y) ∈ Subgroup.center B := by simpa using hy
      have hxmap : e (e.symm y) ∈ Subgroup.map (↑e) (Subgroup.center A) := by
        rw [Subgroup.map_center_eq e]
        exact hx'
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hxmap
      have hz' : z = e.symm y := e.injective (by simpa using hzy)
      simpa [hz'] using hz
    · have h := hcomm (e.symm y)
      simpa using h

theorem center_wreathSub (F : FrameData Q) {D : Subgroup (O2 K)}
    (hnegD : negOneO2 ∈ D)
    (hDcenter : ∀ x : D, x ∈ Subgroup.center D ↔
      (x : GL (Fin 2) K) = 1 ∨ (x : GL (Fin 2) K) = -1) :
    (Subgroup.center (wreathSub F D)).map
        ((Q.specialOrthogonalWithin).subtype.comp (wreathSub F D).subtype) =
      Subgroup.zpowers F.zO := by
  refine center_of_subgroup_le_wreath F D (wreathSub F D) le_rfl ?_ ?_ ?_ ?_ hDcenter
  · rw [← sSO_neg_one_one]
    exact Subgroup.mem_sup_left (Subgroup.mem_map.mpr
      ⟨(negOneO2, (1 : O2 K)), ⟨hnegD, Subgroup.one_mem D⟩, rfl⟩)
  · have hz : F.zSO = F.betaSO negOneO2 negOneO2 := (sSO_neg_one_neg_one F).symm
    rw [hz]
    exact Subgroup.mem_sup_left (Subgroup.mem_map.mpr
      ⟨(negOneO2, negOneO2), ⟨hnegD, hnegD⟩, rfl⟩)
  · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩)
  · intro d
    exact Subgroup.mem_sup_left (Subgroup.mem_map.mpr
      ⟨(d, d), ⟨d.property, d.property⟩, rfl⟩)

theorem normalFour_le_wreathO (F : FrameData Q) {D : Subgroup (O2 K)}
    (hnegD : negOneO2 ∈ D) : normalFour F ≤ wreathO F D := by
  rw [normalFour]
  refine sup_le ?_ ?_
  · rw [Subgroup.zpowers_le]
    have hz : F.zO = F.betaO negOneO2 negOneO2 := (betaO_negOneO2_negOneO2 F).symm
    rw [hz]
    exact Subgroup.mem_sup_left (Subgroup.mem_map.mpr
      ⟨(negOneO2, negOneO2), ⟨hnegD, hnegD⟩, rfl⟩)
  · rw [Subgroup.zpowers_le]
    have ht : F.tO = F.betaO negOneO2 (1 : O2 K) := (betaO_negOneO2_one F).symm
    rw [ht]
    exact Subgroup.mem_sup_left (Subgroup.mem_map.mpr
      ⟨(negOneO2, (1 : O2 K)), ⟨hnegD, Subgroup.one_mem D⟩, rfl⟩)

theorem normalFour_subgroupOf_wreathO_normal (F : FrameData Q)
    (D : Subgroup (O2 K)) (hnegD : negOneO2 ∈ D) :
    ((normalFour F).subgroupOf (wreathO F D)).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer
    (wreathO_le_normalizer_normalFour F D)


public theorem fixed_frame_sylow (F : FrameData Q) (hodd : Odd (Nat.card K))
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K V = 5)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hLG : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ G)
    (hGSO : G ≤ Q.specialOrthogonalWithin) :
    ∃ (W : FiveDimensionalWreathData F) (T : Sylow 2 G),
      (T : Subgroup G).map G.subtype =
        W.S.map (Q.specialOrthogonalWithin).subtype ⊓ G ∧
      let P := (T : Subgroup G).map G.subtype
      F.zO ∈ P ∧ F.tO ∈ P ∧ orderOf F.zO = 2 ∧ orderOf F.tO = 2 ∧
      F.tO ∉ Subgroup.zpowers F.zO ∧
      (Subgroup.center T).map (G.subtype.comp (T : Subgroup G).subtype) = Subgroup.zpowers F.zO ∧
      normalFour F ≤ P ∧ Nat.card (normalFour F) = 4 ∧
      ((normalFour F).subgroupOf P).Normal := by
  obtain ⟨W, hDcenter⟩ := exists_wreathData F hodd hQ hdim
  let D : Subgroup (O2 K) := W.D
  let hS : Sylow 2 Q.specialOrthogonalWithin := W.S
  have hScoe : (hS : Subgroup Q.specialOrthogonalWithin) = wreathSub F D := W.hScoe
  have hnegD : negOneO2 ∈ D := W.hnegD
  let S : Subgroup Q.specialOrthogonalWithin := wreathSub F D
  have hScoe' : (hS : Subgroup Q.specialOrthogonalWithin) = S := hScoe
  have htS : F.tSO ∈ S := by
    rw [← sSO_neg_one_one]
    exact Subgroup.mem_sup_left (Subgroup.mem_map.mpr
      ⟨(negOneO2, (1 : O2 K)), ⟨hnegD, Subgroup.one_mem D⟩, rfl⟩)
  have hzS : F.zSO ∈ S := by
    have hz : F.zSO = F.betaSO negOneO2 negOneO2 := (sSO_neg_one_neg_one F).symm
    rw [hz]
    exact Subgroup.mem_sup_left (Subgroup.mem_map.mpr
      ⟨(negOneO2, negOneO2), ⟨hnegD, hnegD⟩, rfl⟩)
  have hsS : F.sSO ∈ S :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩)
  have hdiagS : ∀ d : D, F.betaSO d d ∈ S := fun d =>
    Subgroup.mem_sup_left (Subgroup.mem_map.mpr
      ⟨(d, d), ⟨d.property, d.property⟩, rfl⟩)
  have hS_sylowOf : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    have hp : IsPGroup 2 S := by
      rw [← hScoe']
      exact hS.isPGroup'
    have hidx : ¬ 2 ∣ S.index := by
      rw [← hScoe']
      exact hS.not_dvd_index
    exact ⟨le_top, hp, by simpa [Subgroup.relIndex_top_right] using hidx⟩
  have hGnormal : G.Normal :=
    Subgroup.Normal.of_commutator_le (G := TauCeti.QuadraticMap.orthogonalGroup Q) hLG
  let GS : Subgroup Q.specialOrthogonalWithin := G.subgroupOf Q.specialOrthogonalWithin
  have hGSnormal : GS.Normal := hGnormal.subgroupOf Q.specialOrthogonalWithin
  letI : GS.Normal := hGSnormal
  let PS : Subgroup Q.specialOrthogonalWithin := S ⊓ GS
  have hPS_sylowOf : CFSG.ABGLocalTools.IsSylowOf 2 PS GS :=
    hS_sylowOf.inf_of_le_normalizer (N := GS) le_top
      (by rw [Subgroup.normalizer_eq_top GS])
  have hPS_le : PS ≤ GS := hPS_sylowOf.le
  have hPS_p : IsPGroup 2 PS := hPS_sylowOf.isPGroup
  have hPS_odd : ¬ 2 ∣ PS.relIndex GS :=
    (CFSG.ABGLocalTools.isSylowOf_iff.mp hPS_sylowOf).2.2
  let e : GS ≃* G := Subgroup.subgroupOfEquivOfLe hGSO
  let PG : Subgroup G := (PS.subgroupOf GS).map e.toMonoidHom
  have hPSsub_p : IsPGroup 2 (PS.subgroupOf GS) :=
    hPS_p.of_equiv (Subgroup.subgroupOfEquivOfLe hPS_le).symm
  have hPG_p : IsPGroup 2 PG := hPSsub_p.map e.toMonoidHom
  have hPG_odd : ¬ 2 ∣ PG.index := by
    have hidx : PG.index = (PS.subgroupOf GS).index := by
      dsimp only [PG]
      exact Subgroup.index_map_equiv (PS.subgroupOf GS) e
    rw [hidx]
    change ¬ 2 ∣ PS.relIndex GS
    exact hPS_odd
  let T0 : Sylow 2 G := hPG_p.toSylow hPG_odd
  have hT0coe : (T0 : Subgroup G) = PG := IsPGroup.toSylow_coe hPG_p hPG_odd
  have htPS : F.tSO ∈ PS := by
    refine ⟨htS, Subgroup.mem_subgroupOf.mpr ?_⟩
    have h : F.tO ∈ G := hLG (tO_mem_derived F)
    change F.tO ∈ G
    exact h
  have hzPS : F.zSO ∈ PS := by
    refine ⟨hzS, Subgroup.mem_subgroupOf.mpr ?_⟩
    have h : F.zO ∈ G := hLG (zO_mem_derived F)
    change F.zO ∈ G
    exact h
  have hsPS : F.sSO ∈ PS := by
    refine ⟨hsS, Subgroup.mem_subgroupOf.mpr ?_⟩
    have h : F.sO ∈ G := hLG (sO_mem_derived F)
    change F.sO ∈ G
    exact h
  have hdiagPS : ∀ d : D, F.betaSO d d ∈ PS := by
    intro d
    refine ⟨hdiagS d, Subgroup.mem_subgroupOf.mpr ?_⟩
    have h : F.betaO (d : O2 K) (d : O2 K) ∈ G :=
      hLG (betaO_diag_mem_derived F (d : O2 K))
    change F.betaO (d : O2 K) (d : O2 K) ∈ G
    exact h
  have hcenterPS : (Subgroup.center PS).map
      ((Q.specialOrthogonalWithin).subtype.comp PS.subtype) = Subgroup.zpowers F.zO :=
    center_of_subgroup_le_wreath F D PS (fun x hx => hx.1) htPS hzPS hsPS hdiagPS hDcenter
  let ePS : PS ≃* PS.subgroupOf GS := (Subgroup.subgroupOfEquivOfLe hPS_le).symm
  let ePG : PS.subgroupOf GS ≃* PG := e.subgroupMap (PS.subgroupOf GS)
  let eP : PS ≃* PG := ePS.trans ePG
  let fA : PS →* TauCeti.QuadraticMap.orthogonalGroup Q :=
    (Q.specialOrthogonalWithin).subtype.comp PS.subtype
  let fB : PG →* TauCeti.QuadraticMap.orthogonalGroup Q := G.subtype.comp PG.subtype
  have hcomm_eP : ∀ x : PS, fA x = fB (eP x) := by
    intro x
    apply Subtype.ext
    rfl
  have hcenterPG : (Subgroup.center PG).map fB = Subgroup.zpowers F.zO :=
    (map_center_eq_of_mulEquiv_commute eP fA fB hcomm_eP).symm.trans hcenterPS
  have hPG_map_eq : PG.map G.subtype = PS.map (Q.specialOrthogonalWithin).subtype := by
    have hcomp : G.subtype.comp e.toMonoidHom =
        (Q.specialOrthogonalWithin).subtype.comp GS.subtype := by
      ext x
      rfl
    calc PG.map G.subtype
        = (PS.subgroupOf GS).map (G.subtype.comp e.toMonoidHom) := by
            dsimp only [PG]
            rw [Subgroup.map_map]
      _ = (PS.subgroupOf GS).map
            ((Q.specialOrthogonalWithin).subtype.comp GS.subtype) := by rw [hcomp]
      _ = ((PS.subgroupOf GS).map GS.subtype).map
            (Q.specialOrthogonalWithin).subtype := by rw [Subgroup.map_map]
      _ = PS.map (Q.specialOrthogonalWithin).subtype := by
            rw [Subgroup.map_subgroupOf_eq_of_le hPS_le]
  have hGS_map : GS.map (Q.specialOrthogonalWithin).subtype = G :=
    Subgroup.map_subgroupOf_eq_of_le hGSO
  have hmapinf : Subgroup.map (Q.specialOrthogonalWithin).subtype (S ⊓ GS) =
      Subgroup.map (Q.specialOrthogonalWithin).subtype S ⊓
        Subgroup.map (Q.specialOrthogonalWithin).subtype GS :=
    Subgroup.map_inf S GS (Q.specialOrthogonalWithin).subtype
      (Q.specialOrthogonalWithin).subtype_injective
  have hPS_map : PS.map (Q.specialOrthogonalWithin).subtype =
      S.map (Q.specialOrthogonalWithin).subtype ⊓ G := by
    dsimp only [PS]
    rw [hmapinf, hGS_map]
  have hSm : S.map (Q.specialOrthogonalWithin).subtype =
      W.S.map (Q.specialOrthogonalWithin).subtype := by
    change (wreathSub F D).map (Q.specialOrthogonalWithin).subtype =
      W.S.map (Q.specialOrthogonalWithin).subtype
    rw [← hScoe]
  have hPS_map' : PS.map (Q.specialOrthogonalWithin).subtype =
      W.S.map (Q.specialOrthogonalWithin).subtype ⊓ G := by
    rw [hPS_map, hSm]
  have hP_eq : (T0 : Subgroup G).map G.subtype =
      PS.map (Q.specialOrthogonalWithin).subtype := by
    rw [hT0coe, hPG_map_eq]
  have hP_intersect : (T0 : Subgroup G).map G.subtype =
      W.S.map (Q.specialOrthogonalWithin).subtype ⊓ G := by
    rw [hP_eq, hPS_map']
  have hzP : F.zO ∈ (T0 : Subgroup G).map G.subtype := by
    rw [hP_eq]
    exact Subgroup.mem_map.mpr ⟨F.zSO, hzPS, rfl⟩
  have htP : F.tO ∈ (T0 : Subgroup G).map G.subtype := by
    rw [hP_eq]
    exact Subgroup.mem_map.mpr ⟨F.tSO, htPS, rfl⟩
  have hP_le_wreathO : (T0 : Subgroup G).map G.subtype ≤ wreathO F D := by
    rw [hP_eq]
    calc PS.map (Q.specialOrthogonalWithin).subtype ≤
          S.map (Q.specialOrthogonalWithin).subtype :=
          Subgroup.map_mono inf_le_left
      _ = wreathO F D := by
          simpa [S] using wreathSub_map_eq F D
  have hnormal : ((normalFour F).subgroupOf
      ((T0 : Subgroup G).map G.subtype)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (hP_le_wreathO.trans (wreathO_le_normalizer_normalFour F D))
  have hcenterT : (Subgroup.center T0).map (G.subtype.comp (T0 : Subgroup G).subtype) =
      Subgroup.zpowers F.zO := by
    rw [hT0coe]
    exact hcenterPG
  have ht_not : F.tO ∉ Subgroup.zpowers F.zO := by
    intro h
    have hmem := (Subgroup.mem_zpowers_iff_of_orderOf_eq_two (zO_order F)).mp h
    rcases hmem with h1 | h2
    · exact (tO_ne_one F) h1
    · exact (zO_ne_tO F) h2.symm
  have hNle : normalFour F ≤ (T0 : Subgroup G).map G.subtype := by
    rw [normalFour]
    exact sup_le (Subgroup.zpowers_le.mpr hzP) (Subgroup.zpowers_le.mpr htP)
  exact ⟨W, T0, hP_intersect, hzP, htP, zO_order F, tO_order F, ht_not, hcenterT,
    hNle, normalFour_card F, hnormal⟩

theorem mem_wreathSub_iff (F : FrameData Q) (D : Subgroup (O2 K))
    (x : Q.specialOrthogonalWithin) :
    x ∈ wreathSub F D ↔
      ∃ b ∈ betaBase F D, ∃ c ∈ swapSub F, x = b * c :=
  TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left
    (H := betaBase F D) (K := swapSub F) (swapSub_le_normalizer_betaBase F D)

private def conjFrame (F : FrameData Q)
    (g : TauCeti.QuadraticMap.orthogonalGroup Q) : FrameData Q where
  e := F.e.map (g : V ≃ₗ[K] V)
  orth i j hij := by
    rw [Module.Basis.map_apply, Module.Basis.map_apply,
      CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem g.property]
    exact F.orth i j hij
  norm i hi := by
    rw [Module.Basis.map_apply, CFSG.ClassicalGroups.Orthogonal.map_of_mem g.property]
    exact F.norm i hi
  last := by
    rw [Module.Basis.map_apply, CFSG.ClassicalGroups.Orthogonal.map_of_mem g.property]
    exact F.last
  nondeg := F.nondeg

private theorem conjFrame_z (F : FrameData Q)
    (g : TauCeti.QuadraticMap.orthogonalGroup Q) :
    (conjFrame F g).z = (g : V ≃ₗ[K] V) * F.z * (g : V ≃ₗ[K] V)⁻¹ := by
  apply LinearEquiv.toLinearMap_injective
  apply (conjFrame F g).e.ext
  intro i
  have he : (conjFrame F g).e i = (g : V ≃ₗ[K] V) (F.e i) := by
    change (F.e.map (g : V ≃ₗ[K] V)) i = (g : V ≃ₗ[K] V) (F.e i)
    rw [Module.Basis.map_apply]
  change (conjFrame F g).z ((conjFrame F g).e i) =
    ((g : V ≃ₗ[K] V) * F.z * (g : V ≃ₗ[K] V)⁻¹) ((conjFrame F g).e i)
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  have hsymm : ((g : V ≃ₗ[K] V)⁻¹) ((conjFrame F g).e i) = F.e i := by
    rw [he]
    exact Equiv.symm_apply_apply ((g : V ≃ₗ[K] V) : V ≃ V) (F.e i)
  rw [hsymm, FrameData.z_e, he]
  by_cases hi : (i : ℕ) < 4 <;> simp [hi]

private theorem conjFrame_t (F : FrameData Q)
    (g : TauCeti.QuadraticMap.orthogonalGroup Q) :
    (conjFrame F g).t = (g : V ≃ₗ[K] V) * F.t * (g : V ≃ₗ[K] V)⁻¹ := by
  apply LinearEquiv.toLinearMap_injective
  apply (conjFrame F g).e.ext
  intro i
  have he : (conjFrame F g).e i = (g : V ≃ₗ[K] V) (F.e i) := by
    change (F.e.map (g : V ≃ₗ[K] V)) i = (g : V ≃ₗ[K] V) (F.e i)
    rw [Module.Basis.map_apply]
  change (conjFrame F g).t ((conjFrame F g).e i) =
    ((g : V ≃ₗ[K] V) * F.t * (g : V ≃ₗ[K] V)⁻¹) ((conjFrame F g).e i)
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  have hsymm : ((g : V ≃ₗ[K] V)⁻¹) ((conjFrame F g).e i) = F.e i := by
    rw [he]
    exact Equiv.symm_apply_apply ((g : V ≃ₗ[K] V) : V ≃ V) (F.e i)
  rw [hsymm, FrameData.t_e, he]
  by_cases hi : (i : ℕ) < 2 <;> simp [hi]

private theorem conjFrame_zO (F : FrameData Q)
    (g : TauCeti.QuadraticMap.orthogonalGroup Q) :
    (conjFrame F g).zO = g * F.zO * g⁻¹ := by
  apply Subtype.ext
  exact conjFrame_z F g

private theorem conjFrame_tO (F : FrameData Q)
    (g : TauCeti.QuadraticMap.orthogonalGroup Q) :
    (conjFrame F g).tO = g * F.tO * g⁻¹ := by
  apply Subtype.ext
  exact conjFrame_t F g

private lemma center_map_conj (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (g : G) (T0 T : Subgroup G)
    (hT : T = T0.map (MulAut.conj g).toMonoidHom) :
    (Subgroup.center T).map (G.subtype.comp T.subtype) =
      ((Subgroup.center T0).map (G.subtype.comp T0.subtype)).map
        (MulAut.conj (g : TauCeti.QuadraticMap.orthogonalGroup Q)).toMonoidHom := by
  subst T
  let f : G ≃* G := MulAut.conj g
  let eT : T0 ≃* T0.map f.toMonoidHom := f.subgroupMap T0
  have hcenter : (Subgroup.center T0).map eT.toMonoidHom =
      Subgroup.center (T0.map f.toMonoidHom) :=
    Subgroup.map_center_eq eT
  ext x
  constructor
  · rintro ⟨c, hc, rfl⟩
    have hc' : c ∈ (Subgroup.center T0).map eT.toMonoidHom := by
      rw [hcenter]
      exact hc
    obtain ⟨s, hs, hsc⟩ := Subgroup.mem_map.mp hc'
    refine Subgroup.mem_map.mpr
      ⟨(G.subtype.comp T0.subtype) s, Subgroup.mem_map.mpr ⟨s, hs, rfl⟩, ?_⟩
    rw [← hsc]
    rfl
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨s, hs, hsy⟩ := Subgroup.mem_map.mp hy
    refine Subgroup.mem_map.mpr ⟨eT s, ?_, ?_⟩
    · rw [← hcenter]
      exact Subgroup.mem_map.mpr ⟨s, hs, rfl⟩
    · rw [← hsy]
      rfl

private theorem normalFour_conjFrame (F : FrameData Q)
    (g : TauCeti.QuadraticMap.orthogonalGroup Q) :
    normalFour (conjFrame F g) =
      (normalFour F).map (MulAut.conj g).toMonoidHom := by
  rw [normalFour, normalFour, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  change Subgroup.zpowers (conjFrame F g).zO ⊔
      Subgroup.zpowers (conjFrame F g).tO =
    Subgroup.zpowers ((g : TauCeti.QuadraticMap.orthogonalGroup Q) * F.zO *
        (g : TauCeti.QuadraticMap.orthogonalGroup Q)⁻¹) ⊔
      Subgroup.zpowers ((g : TauCeti.QuadraticMap.orthogonalGroup Q) * F.tO *
        (g : TauCeti.QuadraticMap.orthogonalGroup Q)⁻¹)
  rw [← conjFrame_zO F g, ← conjFrame_tO F g]

private lemma orderOf_conj_eq (g x : TauCeti.QuadraticMap.orthogonalGroup Q) :
    orderOf (g * x * g⁻¹) = orderOf x := by
  have h : SemiconjBy g x (g * x * g⁻¹) := by
    rw [SemiconjBy]
    group
  exact (SemiconjBy.orderOf_eq g h).symm

public theorem exists_frame_sylow_normal_four
    (hodd : Odd (Nat.card K)) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K V = 5)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hLG : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ G)
    (hGSO : G ≤ Q.specialOrthogonalWithin) (T : Sylow 2 G) :
    ∃ F : FrameData Q,
      let P := (T : Subgroup G).map G.subtype
      let N := Subgroup.zpowers F.zO ⊔ Subgroup.zpowers F.tO
      F.zO ∈ P ∧ F.tO ∈ P ∧
      orderOf F.zO = 2 ∧ orderOf F.tO = 2 ∧
      F.tO ∉ Subgroup.zpowers F.zO ∧
      (Subgroup.center (T : Subgroup G)).map
        (G.subtype.comp (T : Subgroup G).subtype) = Subgroup.zpowers F.zO ∧
      N ≤ P ∧ Nat.card N = 4 ∧ (N.subgroupOf P).Normal := by
  obtain ⟨F0⟩ := exists_frameData hodd hdim Q hQ
  obtain ⟨W, T0, hT0P, hz0, ht0, hzord0, htord0, htnot0, hcenter0,
    hN0le, hN0card, hN0norm⟩ :=
    fixed_frame_sylow F0 hodd hQ hdim G hLG hGSO
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T0 T
  let F : FrameData Q := conjFrame F0 (g : TauCeti.QuadraticMap.orthogonalGroup Q)
  have hTcoe : (T : Subgroup G) =
      (T0 : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rw [Subgroup.pointwise_smul_def]
    rfl
  have hPconj : (T : Subgroup G).map G.subtype =
      ((T0 : Subgroup G).map G.subtype).map
        (MulAut.conj (g : TauCeti.QuadraticMap.orthogonalGroup Q)).toMonoidHom := by
    rw [hTcoe, Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hgT : (T0 : Subgroup G).map (MulAut.conj g).toMonoidHom = (T : Subgroup G) :=
    hTcoe.symm
  have hzP : F.zO ∈ (T : Subgroup G).map G.subtype := by
    rw [hPconj]
    refine Subgroup.mem_map.mpr ⟨F0.zO, hz0, ?_⟩
    show (MulAut.conj (g : TauCeti.QuadraticMap.orthogonalGroup Q)) F0.zO =
      (conjFrame F0 (g : TauCeti.QuadraticMap.orthogonalGroup Q)).zO
    simpa [conjFrame_zO F0 (g : TauCeti.QuadraticMap.orthogonalGroup Q)]
  have htP : F.tO ∈ (T : Subgroup G).map G.subtype := by
    rw [hPconj]
    refine Subgroup.mem_map.mpr ⟨F0.tO, ht0, ?_⟩
    show (MulAut.conj (g : TauCeti.QuadraticMap.orthogonalGroup Q)) F0.tO =
      (conjFrame F0 (g : TauCeti.QuadraticMap.orthogonalGroup Q)).tO
    simpa [conjFrame_tO F0 (g : TauCeti.QuadraticMap.orthogonalGroup Q)]
  have hzord : orderOf F.zO = 2 := by
    rw [show F.zO = (g : TauCeti.QuadraticMap.orthogonalGroup Q) * F0.zO *
      (g : TauCeti.QuadraticMap.orthogonalGroup Q)⁻¹ from conjFrame_zO F0 (g : _)]
    rw [orderOf_conj_eq]
    exact hzord0
  have htord : orderOf F.tO = 2 := by
    rw [show F.tO = (g : TauCeti.QuadraticMap.orthogonalGroup Q) * F0.tO *
      (g : TauCeti.QuadraticMap.orthogonalGroup Q)⁻¹ from conjFrame_tO F0 (g : _)]
    rw [orderOf_conj_eq]
    exact htord0
  have htnot : F.tO ∉ Subgroup.zpowers F.zO := by
    intro hmem
    let cg : TauCeti.QuadraticMap.orthogonalGroup Q ≃*
        TauCeti.QuadraticMap.orthogonalGroup Q := MulAut.conj (g : _)
    have hmap : (Subgroup.zpowers F.zO).map cg.symm.toMonoidHom =
        Subgroup.zpowers F0.zO := by
      rw [MonoidHom.map_zpowers]
      congr 1
      change (MulAut.conj (g : TauCeti.QuadraticMap.orthogonalGroup Q)).symm F.zO = F0.zO
      rw [show (MulAut.conj (g : TauCeti.QuadraticMap.orthogonalGroup Q)).symm =
          MulAut.conj ((g : TauCeti.QuadraticMap.orthogonalGroup Q)⁻¹) by
        ext x
        simp [MulAut.conj_apply]]
      rw [conjFrame_zO F0 (g : _), MulAut.conj_apply]
      group
    have hF0 : F0.tO ∈ Subgroup.zpowers F0.zO := by
      have hsymm_t : cg.symm F.tO = F0.tO := by
        change (MulAut.conj (g : TauCeti.QuadraticMap.orthogonalGroup Q)).symm F.tO = F0.tO
        rw [show (MulAut.conj (g : TauCeti.QuadraticMap.orthogonalGroup Q)).symm =
            MulAut.conj ((g : TauCeti.QuadraticMap.orthogonalGroup Q)⁻¹) by
          ext x
          simp [MulAut.conj_apply]]
        rw [conjFrame_tO F0 (g : _), MulAut.conj_apply]
        group
      have hmem' : cg.symm F.tO ∈ Subgroup.zpowers F0.zO := by
        rw [← hmap]
        exact Subgroup.mem_map.mpr ⟨F.tO, hmem, rfl⟩
      simpa [hsymm_t] using hmem'
    exact htnot0 hF0
  have hcenter : (Subgroup.center (T : Subgroup G)).map
      (G.subtype.comp (T : Subgroup G).subtype) = Subgroup.zpowers F.zO := by
    rw [center_map_conj G g (T0 : Subgroup G) (T : Subgroup G) hTcoe, hcenter0,
      MonoidHom.map_zpowers]
    congr 1
  have hNle : (Subgroup.zpowers F.zO ⊔ Subgroup.zpowers F.tO) ≤
      (T : Subgroup G).map G.subtype := by
    change normalFour F ≤ (T : Subgroup G).map G.subtype
    rw [normalFour_conjFrame F0 (g : _), hPconj]
    exact Subgroup.map_mono hN0le
  have hNcard : Nat.card ↥(Subgroup.zpowers F.zO ⊔ Subgroup.zpowers F.tO) = 4 := by
    rw [show Subgroup.zpowers F.zO ⊔ Subgroup.zpowers F.tO = normalFour F from rfl]
    rw [normalFour_conjFrame F0 (g : _)]
    have hcard := Subgroup.card_map_of_injective
      (K := normalFour F0) (f := (MulAut.conj (g : TauCeti.QuadraticMap.orthogonalGroup Q)).toMonoidHom)
      (MulAut.conj (g : TauCeti.QuadraticMap.orthogonalGroup Q)).injective
    rw [hcard]
    exact hN0card
  have hNnorm : ((Subgroup.zpowers F.zO ⊔ Subgroup.zpowers F.tO).subgroupOf
      ((T : Subgroup G).map G.subtype)).Normal := by
    change ((normalFour F).subgroupOf ((T : Subgroup G).map G.subtype)).Normal
    have hP0norm : (T0 : Subgroup G).map G.subtype ≤
        Subgroup.normalizer (normalFour F0) :=
      Subgroup.le_normalizer_of_normal_subgroupOf hN0le
    have hPnorm : (T : Subgroup G).map G.subtype ≤
        Subgroup.normalizer (normalFour F) := by
      rw [normalFour_conjFrame F0 (g : _), hPconj]
      calc ((T0 : Subgroup G).map G.subtype).map
            (MulAut.conj (g : TauCeti.QuadraticMap.orthogonalGroup Q)).toMonoidHom
          ≤ (Subgroup.normalizer (normalFour F0)).map
              (MulAut.conj (g : TauCeti.QuadraticMap.orthogonalGroup Q)).toMonoidHom :=
            Subgroup.map_mono hP0norm
        _ = Subgroup.normalizer
              ((normalFour F0).map
                (MulAut.conj (g : TauCeti.QuadraticMap.orthogonalGroup Q)).toMonoidHom) :=
            Subgroup.map_normalizer_eq_of_bijective (normalFour F0)
              (MulAut.conj (g : TauCeti.QuadraticMap.orthogonalGroup Q)).bijective
    exact Subgroup.normal_subgroupOf_of_le_normalizer hPnorm
  exact ⟨F, hzP, htP, hzord, htord, htnot, hcenter, hNle, hNcard, hNnorm⟩

end CFSG.ClassicalGroups.Orthogonal.FiveDimensionalSylow
