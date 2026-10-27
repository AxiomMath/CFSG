module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Numerics
public import CFSG.Sporadic.FischerOddCore.Fi22Unitary
public import Certificates.Certificate36908
public import Certificates.Certificate214032
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporFiveKit
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Reps
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Witness
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Sporadic
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Arith
public import CFSG.RankThree.Native.Fi22FiveCentralizers

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08

open CFSG.Open CFSG.Blueprint CFSG.Sporadic.Fi22 CFSG.Monster.B.Fischer CFSG.RankThree.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Native CFSG.Sporadic.Fi22.S0
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Three
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
  CFSG.HardMathSupport.Solomon.Coordinator.Fi22Pump CFSG.HardMathSupport.Solomon.Coordinator

namespace Fi22Copy

noncomputable def iotaJ :
    J →* Equiv.Perm (Fin 3510) :=
  MonoidHom.comp (fi22P.subtype : ↥fi22P →* Equiv.Perm (Fin 3510))
    (MulEquiv.toMonoidHom (CFSG.Sporadic.FischerOddCore.fi22PJ.symm : J ≃* ↥fi22P))

theorem iotaJ_injective :
    Function.Injective (iotaJ : J →* Equiv.Perm (Fin 3510)) :=
  fi22P.subtype_injective.comp (CFSG.Sporadic.FischerOddCore.fi22PJ.symm : J ≃* fi22P).injective

theorem iotaJ_mem
    (g : J) : (iotaJ g : Equiv.Perm (Fin 3510)) ∈ fi22P :=
  (CFSG.Sporadic.FischerOddCore.fi22PJ.symm g).2

theorem pump_facts :
    Rep 3510 (sigmaArr ()) (permOfArr 3510 (sigmaArr ())) ∧
    permOfArr 3510 (sigmaArr ()) * MulAction.toPerm a =
      fi22GenPerm 0 * permOfArr 3510 (sigmaArr ()) ∧
    permOfArr 3510 (sigmaArr ()) * MulAction.toPerm b =
      fi22GenPerm 1 * permOfArr 3510 (sigmaArr ()) := by
  obtain ⟨⟨σ, hr, e0, e1, -⟩, -⟩ := Certificates.certificate36908
  have hr' : Rep 3510 (sigmaArr ()) σ := hr
  rw [permOfArr_eq_of_rep hr']
  exact ⟨hr', e0, e1⟩

theorem iotaJ_eq_conj
    (g : J) :
    (iotaJ g : Equiv.Perm (Fin 3510)) = permOfArr 3510 (sigmaArr ()) * MulAction.toPerm g *
      (permOfArr 3510 (sigmaArr ()))⁻¹ := by
  obtain ⟨-, e0, e1⟩ := pump_facts
  set σ := permOfArr 3510 (sigmaArr ()) with hσ
  have ha : (iotaJ a : Equiv.Perm (Fin 3510)) = σ * MulAction.toPerm a * σ⁻¹ := by
    rw [e0, mul_assoc, mul_inv_cancel, mul_one]
    exact fi22PermEquiv_seedA
  have hb : (iotaJ b : Equiv.Perm (Fin 3510)) = σ * MulAction.toPerm b * σ⁻¹ := by
    rw [e1, mul_assoc, mul_inv_cancel, mul_one]
    exact fi22PermEquiv_seedB
  have key : ∀ x ∈ Subgroup.closure ({a, b} : Set J),
      (iotaJ x : Equiv.Perm (Fin 3510)) = σ * MulAction.toPermHom J (Fin 3510) x * σ⁻¹ := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | rfl
      · exact ha
      · exact hb
    | one => rw [map_one, map_one]; group
    | mul y z _ _ hy hz =>
      rw [map_mul, map_mul, hy, hz]
      group
    | inv y _ hy =>
      rw [map_inv, map_inv, hy]
      group
  exact key g (by rw [closure_ab]; trivial)

noncomputable def fixN (p : Equiv.Perm (Fin 3510)) : ℕ := Nat.card {w : Fin 3510 // p w = w}

theorem fixN_conj (c p : Equiv.Perm (Fin 3510)) : fixN (c * p * c⁻¹) = fixN p := by
  unfold fixN
  refine Nat.card_congr
    { toFun := fun w => ⟨(c⁻¹ : Equiv.Perm (Fin 3510)) w.1, ?_⟩
      invFun := fun w => ⟨c w.1, ?_⟩
      left_inv := fun w => Subtype.ext (by simp)
      right_inv := fun w => Subtype.ext (by simp) }
  · have h : c (p (c⁻¹ w.1)) = w.1 := w.2
    have h2 := congrArg (c⁻¹ : Equiv.Perm (Fin 3510)) h
    simpa using h2
  · have h : p w.1 = w.1 := w.2
    show c (p ((c⁻¹ : Equiv.Perm (Fin 3510)) (c w.1))) = c w.1
    simp [h]

theorem fixCount_eq {t : Array ℕ} {p : Equiv.Perm (Fin 3510)} (h : Rep 3510 t p) :
    fi22FixCount t = fixN p := by
  unfold fi22FixCount fixN
  rw [Fi22Three.countP_range_eq_card]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
  rw [beq_iff_eq, h w]
  exact ⟨fun e => Fin.ext e, fun e => congrArg Fin.val e⟩

theorem fixN_xRep :
    fixN (iotaJ (xRep 0)) = 0 ∧ fixN (iotaJ (xRep 1)) = 27 ∧ fixN (iotaJ (xRep 2)) = 36 ∧
      fixN (iotaJ (xRep 3)) = 126 := by
  obtain ⟨-, h0, h1, h2, h3, -⟩ := Certificates.certificate36908
  rw [iotaJ_eq_conj, iotaJ_eq_conj, iotaJ_eq_conj, iotaJ_eq_conj, fixN_conj, fixN_conj, fixN_conj,
    fixN_conj]
  exact ⟨h0, h1, h2, h3⟩

theorem zpowers_conj {G : Type*} [Group G] (h u : G) :
    Subgroup.zpowers (h * u * h⁻¹) = (Subgroup.zpowers u).map (MulAut.conj h).toMonoidHom := by
  rw [MonoidHom.map_zpowers]
  rfl

theorem exists_conj_zpowers_x0
    {y : Equiv.Perm (Fin 3510)} (hyP : y ∈ fi22P) (hy : orderOf y = 5) :
    ∃ g ∈ fi22P, Subgroup.zpowers (g * y * g⁻¹) = Subgroup.zpowers (fi22FiveLine 0) := by
  obtain ⟨⟨hQP, -, -, hQsyl⟩, ⟨hlines, -⟩, -⟩ :=
    R3E_Fi22_full_five_centralizers_common_outer_involution
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hQ : Nat.card fi22FiveQ = 5 ^ (Nat.card fi22P).factorization 5 :=
    card_eq_of_sylow_subgroupOf hQP hQsyl
  obtain ⟨g, hgP, hgQ⟩ := Co3T.exists_conj_mem_of_full hQP hQ hyP hy
  have hto : orderOf (g⁻¹ * y * g) = 5 := by
    have := (MulAut.conj g⁻¹ : Equiv.Perm (Fin 3510) ≃* Equiv.Perm (Fin 3510)).orderOf_eq y
    simpa [MulAut.conj_apply, hy] using this
  obtain ⟨j, hj⟩ := lines_of_eq hlines (Subgroup.zpowers (g⁻¹ * y * g))
    ((Subgroup.zpowers_le).2 hgQ) (by rw [Nat.card_zpowers, hto])
  have hhP : permOfArr 3510 (fi22FiveHArr j) ∈ fi22P := fi22FiveH_mem_P j
  refine ⟨permOfArr 3510 (fi22FiveHArr j) * g⁻¹, fi22P.mul_mem hhP (fi22P.inv_mem hgP), ?_⟩
  have e : permOfArr 3510 (fi22FiveHArr j) * g⁻¹ * y *
      (permOfArr 3510 (fi22FiveHArr j) * g⁻¹)⁻¹ =
      permOfArr 3510 (fi22FiveHArr j) * (g⁻¹ * y * g) * (permOfArr 3510 (fi22FiveHArr j))⁻¹ := by
    group
  rw [e, zpowers_conj, hj, ← zpowers_conj, fi22FiveH_conj j]

theorem five_centralizer_three
    {Z : Equiv.Perm (Fin 3510)} (hZP : Z ∈ fi22P)
    (hZ3 : orderOf Z = 3) (hZc : Z * fi22FiveLine 0 = fi22FiveLine 0 * Z) :
    fixN Z = 126 ∧ ∃ q ∈ fi22FiveQ, Z * q ≠ q * Z :=
  Certificates.certificate36908.2.2.2.2.2 Z hZP hZ3 hZc

theorem orderOf_conj_eq {G : Type*} [Group G] (g x : G) :
    orderOf (g * x * g⁻¹) = orderOf x := by
  have := (MulAut.conj g : G ≃* G).orderOf_eq x
  simpa [MulAut.conj_apply] using this

theorem exists_conj_into_Q
    {R : Subgroup (Equiv.Perm (Fin 3510))} (hRP : R ≤ fi22P) (hR : Nat.card R = 25) :
    ∃ g ∈ fi22P, ∀ q ∈ fi22FiveQ, g * q * g⁻¹ ∈ R := by
  obtain ⟨⟨hQP, -, -, hQsyl⟩, -⟩ := R3E_Fi22_full_five_centralizers_common_outer_involution
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hQ : Nat.card fi22FiveQ = 5 ^ (Nat.card fi22P).factorization 5 :=
    card_eq_of_sylow_subgroupOf hQP hQsyl
  have hR' : Nat.card R = 5 ^ (Nat.card fi22P).factorization 5 := by
    rw [hR, factorization_card_fi22P_five]; norm_num
  let SQ : Sylow 5 fi22P := Sylow.ofCard (fi22FiveQ.subgroupOf fi22P)
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv, hQ])
  let SR : Sylow 5 fi22P := Sylow.ofCard (R.subgroupOf fi22P)
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRP).toEquiv, hR'])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq fi22P SQ SR
  refine ⟨(g : Equiv.Perm (Fin 3510)), g.2, fun q hq => ?_⟩
  have hqS : (⟨q, hQP hq⟩ : fi22P) ∈ (SQ : Subgroup fi22P) := by
    rw [Sylow.coe_ofCard]
    exact hq
  have h1 : (g * (⟨q, hQP hq⟩ : fi22P) * g⁻¹ : fi22P) ∈ ((g • SQ : Sylow 5 fi22P) : Subgroup fi22P) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
      MulAut.smul_def, MulAut.conj_apply, inv_inv]
    have e : g⁻¹ * (g * (⟨q, hQP hq⟩ : fi22P) * g⁻¹) * g = ⟨q, hQP hq⟩ := by group
    rw [e]
    exact hqS
  rw [hg, Sylow.coe_ofCard] at h1
  simpa using Subgroup.mem_subgroupOf.1 h1

theorem not_five_dvd_of_fixN
    {x : J} (hx : orderOf x = 3) (hfix : fixN (iotaJ x) ≠ 126) :
    ¬ 5 ∣ Nat.card (Subgroup.centralizer ({x} : Set J)) := by
  intro h5
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.centralizer ({x} : Set J))) 5 h5
  have hyJ : orderOf (y : J) = 5 := by rw [Subgroup.orderOf_coe]; exact hy
  have hyc : (y : J) * x = x * (y : J) :=
    (Subgroup.mem_centralizer_singleton_iff (g := x) (k := (y : J))).1 y.2
  have hYo : orderOf (iotaJ (y : J) : Equiv.Perm (Fin 3510)) = 5 := by
    rw [orderOf_injective iotaJ iotaJ_injective]; exact hyJ
  have hXo : orderOf (iotaJ x : Equiv.Perm (Fin 3510)) = 3 := by
    rw [orderOf_injective iotaJ iotaJ_injective]; exact hx
  have hXY : (iotaJ x : Equiv.Perm (Fin 3510)) * iotaJ (y : J) =
      iotaJ (y : J) * iotaJ x := by
    rw [← map_mul, ← map_mul, hyc]
  obtain ⟨g, hgP, hgz⟩ := exists_conj_zpowers_x0 (iotaJ_mem (y : J)) hYo
  have hZP : g * (iotaJ x : Equiv.Perm (Fin 3510)) * g⁻¹ ∈ fi22P :=
    fi22P.mul_mem (fi22P.mul_mem hgP (iotaJ_mem x)) (fi22P.inv_mem hgP)
  have hZo : orderOf (g * (iotaJ x : Equiv.Perm (Fin 3510)) * g⁻¹) = 3 := by
    rw [orderOf_conj_eq]; exact hXo
  have hZc : (g * (iotaJ x : Equiv.Perm (Fin 3510)) * g⁻¹) * fi22FiveLine 0 =
      fi22FiveLine 0 * (g * (iotaJ x : Equiv.Perm (Fin 3510)) * g⁻¹) := by
    have hmem : fi22FiveLine 0 ∈ Subgroup.zpowers (g * (iotaJ (y : J) : Equiv.Perm (Fin 3510)) * g⁻¹) := by
      rw [hgz]; exact Subgroup.mem_zpowers _
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hmem
    rw [← hn]
    have hcomm : Commute (g * (iotaJ x : Equiv.Perm (Fin 3510)) * g⁻¹)
        (g * (iotaJ (y : J) : Equiv.Perm (Fin 3510)) * g⁻¹) := by
      show _ * _ = _ * _
      calc g * (iotaJ x : Equiv.Perm (Fin 3510)) * g⁻¹ * (g * iotaJ (y : J) * g⁻¹)
          = g * (iotaJ x * iotaJ (y : J)) * g⁻¹ := by group
        _ = g * (iotaJ (y : J) * iotaJ x) * g⁻¹ := by rw [hXY]
        _ = g * iotaJ (y : J) * g⁻¹ * (g * iotaJ x * g⁻¹) := by group
    exact (hcomm.zpow_right n).eq
  obtain ⟨h126, -⟩ := five_centralizer_three hZP hZo hZc
  rw [fixN_conj] at h126
  exact hfix h126

theorem not_twentyfive_dvd
    {x : J} (hx : orderOf x = 3) : ¬ 25 ∣ Nat.card (Subgroup.centralizer ({x} : Set J)) := by
  intro h25
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hdvd : 5 ^ 2 ∣ Nat.card (Subgroup.centralizer ({x} : Set J)) := by simpa using h25
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime
    (G := ↥(Subgroup.centralizer ({x} : Set J))) 5 hdvd
  let f : ↥(Subgroup.centralizer ({x} : Set J)) →* Equiv.Perm (Fin 3510) :=
    iotaJ.comp (Subgroup.centralizer ({x} : Set J)).subtype
  have hf : Function.Injective f := iotaJ_injective.comp Subtype.val_injective
  have hRcard : Nat.card (K.map f) = 25 := by
    rw [Subgroup.card_map_of_injective hf, hK]; norm_num
  have hRP : K.map f ≤ fi22P := by
    rintro _ ⟨c, -, rfl⟩
    exact iotaJ_mem (c : J)
  obtain ⟨g, hgP, hgR⟩ := exists_conj_into_Q hRP hRcard
  have hXo : orderOf (iotaJ x : Equiv.Perm (Fin 3510)) = 3 := by
    rw [orderOf_injective iotaJ iotaJ_injective]; exact hx
  have hZQ : ∀ q ∈ fi22FiveQ, (g⁻¹ * (iotaJ x : Equiv.Perm (Fin 3510)) * g) * q =
      q * (g⁻¹ * (iotaJ x : Equiv.Perm (Fin 3510)) * g) := by
    intro q hq
    obtain ⟨c, -, hc⟩ := Subgroup.mem_map.1 (hgR q hq)
    have hcx : (c : J) * x = x * (c : J) :=
      (Subgroup.mem_centralizer_singleton_iff (g := x) (k := (c : J))).1 c.2
    have hXc : (f c) * (iotaJ x : Equiv.Perm (Fin 3510)) = iotaJ x * f c := by
      show iotaJ (c : J) * iotaJ x = iotaJ x * iotaJ (c : J)
      rw [← map_mul, ← map_mul, hcx]
    rw [hc] at hXc
    calc g⁻¹ * (iotaJ x : Equiv.Perm (Fin 3510)) * g * q
        = g⁻¹ * (iotaJ x * (g * q * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * q * g⁻¹) * iotaJ x) * g := by rw [hXc]
      _ = q * (g⁻¹ * iotaJ x * g) := by group
  have hZP : g⁻¹ * (iotaJ x : Equiv.Perm (Fin 3510)) * g ∈ fi22P :=
    fi22P.mul_mem (fi22P.mul_mem (fi22P.inv_mem hgP) (iotaJ_mem x)) hgP
  have hZo : orderOf (g⁻¹ * (iotaJ x : Equiv.Perm (Fin 3510)) * g) = 3 := by
    have := orderOf_conj_eq g⁻¹ (iotaJ x : Equiv.Perm (Fin 3510))
    rw [inv_inv] at this
    rw [this]; exact hXo
  obtain ⟨-, q, hq, hqc⟩ := five_centralizer_three hZP hZo (hZQ _ (fi22FiveLine_mem_Q 0))
  exact hqc (hZQ q hq)

theorem card_closure_pair_map {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (a b : G) :
    Nat.card (Subgroup.closure ({f a, f b} : Set H)) = Nat.card (Subgroup.closure ({a, b} : Set G)) := by
  have : Subgroup.closure ({f a, f b} : Set H) = (Subgroup.closure ({a, b} : Set G)).map f := by
    rw [MonoidHom.map_closure, Set.image_pair]
  rw [this, Subgroup.card_map_of_injective hf]

theorem pair3_facts :
    ∃ Y₁ Y₂ : Equiv.Perm (Fin 3510), Y₁ ∈ fi22P ∧ Y₂ ∈ fi22P ∧ orderOf Y₁ = 5 ∧
      orderOf Y₂ = 5 ∧ Y₁ * (iotaJ (xRep 3) : Equiv.Perm (Fin 3510)) = iotaJ (xRep 3) * Y₁ ∧
      Y₂ * (iotaJ (xRep 3) : Equiv.Perm (Fin 3510)) = iotaJ (xRep 3) * Y₂ ∧
      405 ∣ Nat.card (Subgroup.closure ({Y₁, Y₂} : Set (Equiv.Perm (Fin 3510)))) := by
  obtain ⟨σ, hr, Y₁, Y₂, hP₁, hP₂, ho₁, ho₂, hc₁, hc₂, hbig⟩ := Certificates.certificate214032
  have hr' : Rep 3510 (sigmaArr ()) σ := hr
  have e : (iotaJ (xRep 3) : Equiv.Perm (Fin 3510)) = σ * MulAction.toPerm (xRep 3) * σ⁻¹ := by
    rw [iotaJ_eq_conj, permOfArr_eq_of_rep hr']
  rw [e]
  exact ⟨Y₁, Y₂, hP₁, hP₂, ho₁, ho₂, hc₁, hc₂, hbig⟩

theorem exists_five_gen3
    {x : J} (hx : IsConj x (xRep 3)) :
    ∃ a b : J, a ∈ Subgroup.centralizer ({x} : Set J) ∧ b ∈ Subgroup.centralizer ({x} : Set J) ∧
      orderOf a = 5 ∧ orderOf b = 5 ∧ 405 ∣ Nat.card (Subgroup.closure ({a, b} : Set J)) := by
  obtain ⟨Y₁, Y₂, hP₁, hP₂, ho₁, ho₂, hc₁, hc₂, hbig⟩ := pair3_facts
  obtain ⟨c, hc⟩ := isConj_iff.1 hx
  let t₁ : J := CFSG.Sporadic.FischerOddCore.fi22PJ ⟨Y₁, hP₁⟩
  let t₂ : J := CFSG.Sporadic.FischerOddCore.fi22PJ ⟨Y₂, hP₂⟩
  have hι₁ : (iotaJ t₁ : Equiv.Perm (Fin 3510)) = Y₁ := by
    show ((CFSG.Sporadic.FischerOddCore.fi22PJ.symm
      (CFSG.Sporadic.FischerOddCore.fi22PJ ⟨Y₁, hP₁⟩) : fi22P) : Equiv.Perm (Fin 3510)) = Y₁
    rw [MulEquiv.symm_apply_apply]
  have hι₂ : (iotaJ t₂ : Equiv.Perm (Fin 3510)) = Y₂ := by
    show ((CFSG.Sporadic.FischerOddCore.fi22PJ.symm
      (CFSG.Sporadic.FischerOddCore.fi22PJ ⟨Y₂, hP₂⟩) : fi22P) : Equiv.Perm (Fin 3510)) = Y₂
    rw [MulEquiv.symm_apply_apply]
  have ht₁o : orderOf t₁ = 5 := by
    rw [← orderOf_injective iotaJ iotaJ_injective, hι₁]; exact ho₁
  have ht₂o : orderOf t₂ = 5 := by
    rw [← orderOf_injective iotaJ iotaJ_injective, hι₂]; exact ho₂
  have ht₁c : t₁ * xRep 3 = xRep 3 * t₁ := by
    apply iotaJ_injective
    rw [map_mul, map_mul, hι₁]; exact hc₁
  have ht₂c : t₂ * xRep 3 = xRep 3 * t₂ := by
    apply iotaJ_injective
    rw [map_mul, map_mul, hι₂]; exact hc₂
  have hxe : x = c⁻¹ * xRep 3 * c := by rw [← hc]; group
  have key : ∀ t : J, orderOf t = 5 → orderOf (c⁻¹ * t * c) = 5 := fun t ht => by
    have := orderOf_conj_eq c⁻¹ t
    rw [inv_inv] at this
    rw [this]; exact ht
  refine ⟨c⁻¹ * t₁ * c, c⁻¹ * t₂ * c, ?_, ?_, key t₁ ht₁o, key t₂ ht₂o, ?_⟩
  · refine (Subgroup.mem_centralizer_singleton_iff (g := x) (k := c⁻¹ * t₁ * c)).2 ?_
    rw [hxe]
    calc c⁻¹ * t₁ * c * (c⁻¹ * xRep 3 * c) = c⁻¹ * (t₁ * xRep 3) * c := by group
      _ = c⁻¹ * (xRep 3 * t₁) * c := by rw [ht₁c]
      _ = c⁻¹ * xRep 3 * c * (c⁻¹ * t₁ * c) := by group
  · refine (Subgroup.mem_centralizer_singleton_iff (g := x) (k := c⁻¹ * t₂ * c)).2 ?_
    rw [hxe]
    calc c⁻¹ * t₂ * c * (c⁻¹ * xRep 3 * c) = c⁻¹ * (t₂ * xRep 3) * c := by group
      _ = c⁻¹ * (xRep 3 * t₂) * c := by rw [ht₂c]
      _ = c⁻¹ * xRep 3 * c * (c⁻¹ * t₂ * c) := by group
  · have e1 := card_closure_pair_map (MulAut.conj c⁻¹).toMonoidHom (MulAut.conj c⁻¹).injective t₁ t₂
    have e2 := card_closure_pair_map iotaJ iotaJ_injective t₁ t₂
    rw [hι₁, hι₂] at e2
    have e3 : ((MulAut.conj c⁻¹).toMonoidHom t₁ : J) = c⁻¹ * t₁ * c := by
      simp [MulAut.conj_apply]
    have e4 : ((MulAut.conj c⁻¹).toMonoidHom t₂ : J) = c⁻¹ * t₂ * c := by
      simp [MulAut.conj_apply]
    rw [e3, e4] at e1
    rw [e1, ← e2]
    exact hbig

theorem card_J_eq : Nat.card J = 64561751654400 := by
  rw [← Nat.card_congr CFSG.Sporadic.Fi22.fi22EquivJ.toEquiv]
  exact CFSG.Sporadic.Fi22.card_Fi22

theorem l3Excl_J : L3Excl (Nat.card ↥(⊤ : Subgroup J)) 5 4 := by
  rw [Subgroup.card_top, card_J_eq]
  exact l3Excl_64561751654400_5_4

theorem noL3Comp_J
    (x : J) (hx : orderOf x = 3) : NoL3Comp (Subgroup.centralizer ({x} : Set J)) := by
  obtain ⟨k, hk4, hconj⟩ := fi22_classify x hx
  by_cases hk3 : k = 3
  · subst hk3
    obtain ⟨a, b, ha, hb, hao, hbo, hcard⟩ := exists_five_gen3 hconj
    refine noL3Comp_of_prime_pair (P := ⊤) le_top (q := 5) (k := 4) (by norm_num) (by norm_num)
      l3Excl_J ?_ ⟨a, ha, b, hb, hao, hbo, (by norm_num : 3 ^ 4 ∣ 405).trans hcard⟩
    rw [show (5 : ℕ) ^ 2 = 25 by norm_num]
    exact not_twentyfive_dvd hx
  · refine noL3Comp_of_not_dvd_sub (P := ⊤) le_top (by norm_num) (by norm_num) l3Excl_J
      (not_five_dvd_of_fixN hx ?_)
    have hlt : k < 3 := by omega
    obtain ⟨c, hc⟩ := isConj_iff.1 hconj
    have e1 : (iotaJ (xRep k) : Equiv.Perm (Fin 3510)) = iotaJ c * iotaJ x * (iotaJ c)⁻¹ := by
      rw [← hc, map_mul, map_mul, map_inv]
    have e2 := fixN_conj (iotaJ c) (iotaJ x)
    rw [← e1] at e2
    rw [← e2]
    obtain ⟨f0, f1, f2, -⟩ := fixN_xRep
    interval_cases k <;> omega

end Fi22Copy

theorem sporL3DownInner_Fi22
    (hbr : SporadicBridges) : SporL3DownInner .Fi22 := by
  haveI : Finite J := Nat.finite_of_card_ne_zero (by rw [Fi22Copy.card_J_eq]; norm_num)
  have hM : Nonempty (J ≃* (TauCeti.CFSGIndex.sporadic .Fi22).Group) :=
    ⟨CFSG.Sporadic.Fi22.fi22EquivJ.symm.trans (hbr .Fi22).some⟩
  have h1 := @sporL3DownInner_of_comp .Fi22 J inferInstance inferInstance hM
  have hcard : NoL3Eq (Nat.card J) := by
    rw [Fi22Copy.card_J_eq]
    exact noL3Eq_64561751654400
  have h2 := h1 hcard
  exact h2 (fun x hx => Fi22Copy.noL3Comp_J x hx)

end CFSG.HardMathSupport.Solomon.Coordinator.YS08
