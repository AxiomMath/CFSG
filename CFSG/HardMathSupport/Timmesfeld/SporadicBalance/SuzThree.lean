
module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzThreeBase

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.AbelianSylow
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzOuter
public import Certificates.Certificate13637

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates CFSG.Certificates.Native CFSG.RankThree.Native CFSG.RankThree.PartOne
  CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu CFSG.Sporadic.Schreier.Co3.Native
  CFSG.RankThree.PartTwo.Sec4.Item434SporE81
open CFSG.Sporadic.SuzOddCore (suzM smallChain smallChain_arrays smallChain_check smallChain_valid
  smallChain_baseCount smallChain_originalSubgroup mem_suzM_iff_siftA suzM_card_chain
  smallStrongArrs smallBaseNat)

section D

theorem rep_dGen {i : ℕ} (hi : i < 5) : Rep 1782 (dGens ())[i]! (dPerm ⟨i, hi⟩) :=
  rep_of_validA (Certificates.certificate13637.2.2.1 i hi).1

theorem dPerm_pow (i : Fin 5) : dPerm i ^ 3 = 1 :=
  (Certificates.certificate13637.2.2.1 i i.2).2.2

theorem dPerm_comm (i j : Fin 5) : Commute (dPerm i) (dPerm j) :=
  Certificates.certificate13637.2.2.2.1 i i.2 j j.2

theorem dPerm_mem (i : Fin 5) : dPerm i ∈ suzM :=
  (Certificates.certificate13637.2.2.1 i i.2).2.1

@[expose] noncomputable def φ : Multiplicative (Fin 5 → ZMod 3) →* Equiv.Perm (Fin 1782) :=
  Co3T.vecProdHom dPerm dPerm_comm dPerm_pow

theorem φ_apply (a : Fin 5 → ZMod 3) : φ (Multiplicative.ofAdd a) = Co3T.vecProd dPerm a := rfl

theorem rep_dElts {k : ℕ} (hk : k < 243) :
    Rep 1782 (dElts ())[k]! (φ (Multiplicative.ofAdd (vec k))) := by
  rw [φ_apply, vecProd_eq]
  have he : (dElts ())[k]! = dProd (dGens ()) k := by
    rw [dElts, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
  rw [he, dProd]
  simp only [vec_val]
  exact rep_compA (rep_powArr (rep_dGen (by norm_num)) _) (rep_compA (rep_powArr
    (rep_dGen (by norm_num)) _) (rep_compA (rep_powArr (rep_dGen (by norm_num)) _)
      (rep_compA (rep_powArr (rep_dGen (by norm_num)) _) (rep_powArr (rep_dGen (by norm_num)) _))))

theorem permOfArr_dElts {k : ℕ} (hk : k < 243) :
    permOfArr 1782 (dElts ())[k]! = φ (Multiplicative.ofAdd (vec k)) :=
  CFSG.Monster.B.Mathieu.permOfArr_eq_of_rep (rep_dElts hk)

theorem φ_injective : Function.Injective φ := by
  intro a b hab
  have ha := permOfArr_dElts (idx_lt a.toAdd)
  have hb := permOfArr_dElts (idx_lt b.toAdd)
  rw [vec_idx, ofAdd_toAdd] at ha hb
  have h := Certificates.certificate13637.2.2.2.2.1 (idx a.toAdd) (idx_lt _) (idx b.toAdd)
    (idx_lt _) (by rw [ha, hb, hab])
  have := congrArg vec h
  rw [vec_idx, vec_idx] at this
  exact Multiplicative.toAdd.injective this

@[expose] noncomputable def Dg : Subgroup (Equiv.Perm (Fin 1782)) := φ.range

theorem Dg_comm : ∀ x ∈ Dg, ∀ y ∈ Dg, x * y = y * x := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [← map_mul, ← map_mul, mul_comm]

theorem Dg_pow_three : ∀ x ∈ Dg, x ^ 3 = 1 := by
  rintro _ ⟨a, rfl⟩
  rw [← map_pow]
  have : a ^ 3 = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    funext i
    rw [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, show ((3 : ℕ) : ZMod 3) = 0 from rfl,
      zero_mul]
  rw [this, map_one]

theorem card_Dg : Nat.card Dg = 243 := by
  rw [Dg, MonoidHom.range_eq_map, Subgroup.card_map_of_injective φ_injective, Subgroup.card_top,
    Co3T.card_vec]
  norm_num

theorem isPGroup_Dg : IsPGroup 3 ↥Dg := IsPGroup.of_card (n := 5) (by rw [card_Dg]; norm_num)

theorem Dg_le : Dg ≤ suzM := by
  rintro _ ⟨a, rfl⟩
  change Co3T.vecProd dPerm a.toAdd ∈ suzM
  rw [vecProd_eq]
  have h := dPerm_mem
  exact suzM.mul_mem (suzM.pow_mem (h 0) _) (suzM.mul_mem (suzM.pow_mem (h 1) _)
    (suzM.mul_mem (suzM.pow_mem (h 2) _) (suzM.mul_mem (suzM.pow_mem (h 3) _)
      (suzM.pow_mem (h 4) _))))

theorem mem_Dg_iff_dElts {x : Equiv.Perm (Fin 1782)} :
    x ∈ Dg ↔ ∃ k < 243, x = permOfArr 1782 (dElts ())[k]! := by
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨idx a.toAdd, idx_lt _, ?_⟩
    rw [permOfArr_dElts (idx_lt _), vec_idx, ofAdd_toAdd]
  · rintro ⟨k, hk, rfl⟩
    rw [permOfArr_dElts hk]
    exact ⟨_, rfl⟩

end D

section HypCard

theorem centralizer_inf_eq_Dg {B : Subgroup (Equiv.Perm (Fin 1782))} (hBD : B ≤ Dg)
    (hB : Nat.card B * 3 = 243) :
    Subgroup.centralizer (B : Set (Equiv.Perm (Fin 1782))) ⊓ suzM = Dg := by
  apply le_antisymm
  · intro c hc
    exact mem_Dg_iff_dElts.2 (Certificates.certificate13637.2.2.2.2.2.1 B
      (fun b hb => mem_Dg_iff_dElts.1 (hBD hb)) hB c hc)
  · exact fun x hx => Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun b hb =>
      Dg_comm b (hBD hb) x hx, Dg_le hx⟩

end HypCard

section DCore

theorem isPGroup_centralizer_Dg :
    IsPGroup 3 ↥(Subgroup.centralizer (Dg : Set (Equiv.Perm (Fin 1782))) ⊓ suzM) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Nontrivial ↥Dg := Finite.one_lt_card_iff_nontrivial.1 (by rw [card_Dg]; norm_num)
  obtain ⟨B1, hB1⟩ := CFSG.SolvableHall.exists_index_eq_prime (p := 3) (A := ↥Dg) isPGroup_Dg
  set B' := B1.map Dg.subtype
  have hB'D : B' ≤ Dg := Subgroup.map_subtype_le B1
  have hcard : Nat.card B' * 3 = 243 := by
    rw [Subgroup.card_map_of_injective Dg.subtype_injective, ← hB1, B1.card_mul_index, card_Dg]
  have hC := centralizer_inf_eq_Dg hB'D hcard
  have hP : IsPGroup 3 ↥(Subgroup.centralizer (B' : Set (Equiv.Perm (Fin 1782))) ⊓ suzM) := by
    rw [hC]
    exact isPGroup_Dg
  exact hP.to_le (inf_le_inf_right _ (Subgroup.centralizer_le hB'D))

@[expose] noncomputable def Tg : Subgroup ↥suzM := Dg.subgroupOf suzM

theorem card_Tg : Nat.card Tg = 243 := by
  rw [Tg, Nat.card_congr (Subgroup.subgroupOfEquivOfLe Dg_le).toEquiv, card_Dg]

theorem Tg_elemAbelian : IsElemAbelian 3 Tg := by
  refine ⟨IsMulCommutative.of_comm fun a b => ?_, fun x hx => ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    exact Dg_comm _ (Subgroup.mem_subgroupOf.1 a.2) _ (Subgroup.mem_subgroupOf.1 b.2)
  · apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact Dg_pow_three _ (Subgroup.mem_subgroupOf.1 hx)

theorem isPGroup_centralizer_of_index {B : Subgroup ↥suzM} (hBT : B ≤ Tg)
    (hidx : B.relIndex Tg = 3) : IsPGroup 3 ↥(Subgroup.centralizer (B : Set ↥suzM)) := by
  set B' := B.map suzM.subtype with hB'
  have hB'D : B' ≤ Dg := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hBT hx)
  have hcard : Nat.card B' * 3 = 243 := by
    rw [Subgroup.card_map_of_injective suzM.subtype_injective]
    have h := Subgroup.relIndex_mul_card B Tg
    rw [inf_eq_left.2 hBT, hidx, card_Tg] at h
    omega
  have hC := centralizer_inf_eq_Dg hB'D hcard
  have hP : IsPGroup 3 ↥(Subgroup.centralizer (B' : Set (Equiv.Perm (Fin 1782))) ⊓ suzM) := by
    rw [hC]
    exact isPGroup_Dg
  refine isPGroup_of_map_le hP fun c hc => Subgroup.mem_inf.2 ⟨?_, c.2⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨b, hb, rfl⟩
  exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hc b hb)

theorem gLAPPrimeCoreOf_eq_bot_of_mem_Dg {s : ↥suzM} (hs : orderOf s = 3)
    (hsD : (s : Equiv.Perm (Fin 1782)) ∈ Dg) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set ↥suzM)) = ⊥ := by
  refine gLAPPrimeCoreOf_eq_bot_of_elemAbelian Nat.prime_three Tg_elemAbelian
    (Subgroup.mem_subgroupOf.2 hsD) hs (fun B hBT hidx => gLAPPrimeCoreOf_eq_bot_of_isPGroup
      Nat.prime_three (isPGroup_centralizer_of_index hBT hidx)) ?_
  refine gLAPPrimeCoreOf_eq_bot_of_isPGroup Nat.prime_three
    (isPGroup_of_map_le isPGroup_centralizer_Dg fun c hc => Subgroup.mem_inf.2 ⟨?_, c.2⟩)
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hc ⟨d, Dg_le hd⟩
    (Subgroup.mem_subgroupOf.2 hd))

end DCore

section Cy

theorem rep_y : Rep 1782 (yArr (levels ())) yPerm :=
  rep_of_validA Certificates.certificate13637.2.2.2.2.2.2.1

theorem yPerm_pow : yPerm ^ 3 = 1 := Certificates.certificate13637.2.2.2.2.2.2.2.2.1

theorem yPerm_mem : yPerm ∈ suzM := Certificates.certificate13637.2.2.2.2.2.2.2.1

theorem cEnum : enumOK 1782 (cGens (levels ())) cKeys (cCert (levels ())) = true :=
  Certificates.certificate13637.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem Cy_eq : Subgroup.closure (permsA 1782 (cGens (levels ()))) =
      Subgroup.centralizer {yPerm} ⊓ suzM ∧
    Nat.card (Subgroup.closure (permsA 1782 (cGens (levels ())))) = 3240 :=
  ⟨Certificates.certificate13637.2.2.2.2.2.2.2.2.2.2.1,
    Certificates.certificate13637.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem cCheck_parts : validA 1782 (yArr (levels ())) = true ∧ yPerm ∈ suzM ∧
    eqA 1782 (powArr 1782 (yArr (levels ())) 3) (idA 1782) = true ∧
    eqA 1782 (yArr (levels ())) (idA 1782) = false ∧
    (Subgroup.closure (permsA 1782 (cGens (levels ()))) =
      Subgroup.centralizer {yPerm} ⊓ suzM ∧
    Nat.card (Subgroup.closure (permsA 1782 (cGens (levels ())))) = 3240) := by
  refine ⟨Certificates.certificate13637.2.2.2.2.2.2.1, yPerm_mem,
    (eqA_iff (rep_powArr rep_y 3) rep_idA).2 yPerm_pow, ?_, Cy_eq⟩
  cases h : eqA 1782 (yArr (levels ())) (idA 1782)
  · rfl
  · exact absurd ((eqA_iff rep_y rep_idA).1 h)
      Certificates.certificate13637.2.2.2.2.2.2.2.2.2.1

theorem gLAPPrimeCoreOf_Cy :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer ({yPerm} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM) =
      ⊥ := by
  obtain ⟨hCeq, hCcard⟩ := Cy_eq
  rw [← hCeq]
  refine Co3T.gLAPPrimeCoreOf_eq_bot_of_classSize Nat.prime_three (a := 4) (r := 40)
    (by rw [hCcard]; norm_num) (by norm_num) ?_
  intro w hw hwp hwr
  rw [hCcard]
  have hw1 : w ≠ 1 := fun h => by
    rw [h, orderOf_one] at hwp
    exact Nat.not_prime_one hwp
  have hw25 : w ^ 2 = 1 ∨ w ^ 5 = 1 := by
    have h40 : orderOf w ∣ 2 ^ 3 * 5 := hwr
    rcases (Nat.Prime.dvd_mul hwp).1 h40 with h | h
    · left
      rw [← (Nat.prime_dvd_prime_iff_eq hwp Nat.prime_two).1 (hwp.dvd_of_dvd_pow h)]
      exact pow_orderOf_eq_one w
    · right
      rw [← (Nat.prime_dvd_prime_iff_eq hwp (by norm_num)).1 h]
      exact pow_orderOf_eq_one w
  have h := Certificates.certificate13637.2.2.2.2.2.2.2.2.2.2.2.2.2.1 w hw hw1 hw25
  rw [inf_comm] at h
  omega

theorem gLAPPrimeCoreOf_eq_bot_of_y {s : ↥suzM}
    (hs : (s : Equiv.Perm (Fin 1782)) = yPerm ∨ (s : Equiv.Perm (Fin 1782)) = yPerm ^ 2) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set ↥suzM)) = ⊥ := by
  have hcs : Subgroup.centralizer ({(s : Equiv.Perm (Fin 1782))} : Set (Equiv.Perm (Fin 1782))) =
      Subgroup.centralizer {yPerm} := by
    rcases hs with h | h
    · rw [h]
    · rw [h]
      exact centralizer_pow_two_eq yPerm_pow
  have hmap := CFSG.HardMathSupport.Timmesfeld.Coordinator.map_glaPPrimeCoreOf_of_injective 3
    suzM.subtype suzM.subtype_injective (Subgroup.centralizer ({s} : Set ↥suzM))
  have hc := CFSG.HardMathSupport.Timmesfeld.Coordinator.map_inf_centralizer_of_injective
    suzM.subtype suzM.subtype_injective ⊤ s
  rw [top_inf_eq, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hc
  have hsub : suzM.subtype s = (s : Equiv.Perm (Fin 1782)) := rfl
  rw [hc, hsub, hcs, inf_comm, gLAPPrimeCoreOf_Cy] at hmap
  exact (Subgroup.map_eq_bot_iff_of_injective _ suzM.subtype_injective).1 hmap

end Cy

section Fusion

theorem exists_conj_D_or_y {x : Equiv.Perm (Fin 1782)} (hx : x ∈ suzM) (hxo : orderOf x = 3) :
    ∃ h ∈ suzM, h * x * h⁻¹ ∈ Dg ∨ h * x * h⁻¹ = yPerm ∨ h * x * h⁻¹ = yPerm ^ 2 := by
  obtain ⟨h, hh, hcase⟩ :=
    Certificates.certificate13637.2.2.2.2.2.2.2.2.2.2.2.2.2.2 x hx hxo
  refine ⟨h, hh, ?_⟩
  rcases hcase with hD | hy | hy2
  · exact Or.inl (mem_Dg_iff_dElts.2 hD)
  · exact Or.inr (Or.inl hy)
  · exact Or.inr (Or.inr hy2)

end Fusion

theorem oPrimeCoreTrivialAt_suzM : OPrimeCoreTrivialAt 3 ↥suzM := by
  intro s hs
  have hso : orderOf (s : Equiv.Perm (Fin 1782)) = 3 := by rw [Subgroup.orderOf_coe]; exact hs
  obtain ⟨h, hhP, hcase⟩ := exists_conj_D_or_y s.2 hso
  set h' : ↥suzM := ⟨h, hhP⟩ with hh'
  have hval : ((h' * s * h'⁻¹ : ↥suzM) : Equiv.Perm (Fin 1782)) = h * (s : Equiv.Perm (Fin 1782)) *
      h⁻¹ := rfl
  have ho : orderOf (h' * s * h'⁻¹) = 3 := by
    have := (MulAut.conj h' : ↥suzM ≃* ↥suzM).orderOf_eq s
    simpa [MulAut.conj_apply, hs] using this
  refine (gLAPPrimeCoreOf_centralizer_conj h' s).1 ?_
  rcases hcase with hD | hy | hy2
  · exact gLAPPrimeCoreOf_eq_bot_of_mem_Dg ho (hval ▸ hD)
  · exact gLAPPrimeCoreOf_eq_bot_of_y (Or.inl (hval.trans hy))
  · exact gLAPPrimeCoreOf_eq_bot_of_y (Or.inr (hval.trans hy2))

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Blueprint CFSG.Sporadic.SuzOddCore

theorem sporadicOPrimeHolds_Suz_three :
    SporadicOPrimeHolds .Suz 3 := by
  intro S _ _ _ ⟨e⟩
  have e0 : S ≃* NativeSporadic.Suz := e
  exact OPrimeCoreTrivialAt.of_mulEquiv (e0.trans suzEquivM) SuzT.oPrimeCoreTrivialAt_suzM

theorem sporadicOnePairHolds_Suz_three :
    SporadicOnePairHolds .Suz 3 :=
  ⟨sporadicOPrimeHolds_Suz_three, sporadicOuterHolds_Suz_three⟩

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
