module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BFiveAOdd
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BFiveAClasses
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BFiveAWitness
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BFiveCentral

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Monster.GMS
  CFSG.Blueprint.NativeSporadic CFSG.Monster.B CFSG.Monster.B.Pinned CFSG.RankThree.Native
  CFSG.Monster.B.Short CFSG.Monster.SpinLattice CFSG.Monster.Spin CFSG.Monster.Code
  CFSG.Monster.Griess

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Generic

variable {G : Type*} [Group G]

theorem card_gLAPPrimeCoreOf_centralizer_conj (p : ℕ) (g s : G) :
    Nat.card (GLAPPrimeCoreOf p (Subgroup.centralizer ({g * s * g⁻¹} : Set G))) =
      Nat.card (GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set G))) := by
  have hψ : Function.Injective (MulAut.conj g : G ≃* G).toMonoidHom :=
    (MulAut.conj g : G ≃* G).injective
  have hmap := CFSG.HardMathSupport.Timmesfeld.Coordinator.map_glaPPrimeCoreOf_of_injective p
    (MulAut.conj g : G ≃* G).toMonoidHom hψ (Subgroup.centralizer ({s} : Set G))
  have hc := CFSG.HardMathSupport.Timmesfeld.Coordinator.map_inf_centralizer_of_injective
    (MulAut.conj g : G ≃* G).toMonoidHom hψ ⊤ s
  rw [top_inf_eq, Subgroup.map_top_of_surjective _ (MulAut.conj g : G ≃* G).surjective,
    top_inf_eq] at hc
  rw [hc] at hmap
  have hs : (MulAut.conj g : G ≃* G).toMonoidHom s = g * s * g⁻¹ := by
    simp [MulAut.conj_apply]
  rw [hs] at hmap
  rw [← hmap, Subgroup.card_map_of_injective hψ]

theorem zpowers_pow_eq_of_five [Finite G] {y : G} (hy : orderOf y = 5) {c : ℕ} (hc : ¬ 5 ∣ c) :
    Subgroup.zpowers (y ^ c) = Subgroup.zpowers y := by
  have hco : (orderOf y).Coprime c := by
    rw [hy]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 hc
  refine Subgroup.eq_of_le_of_card_ge
    (Subgroup.zpowers_le.2 (Subgroup.pow_mem _ (Subgroup.mem_zpowers y) c)) ?_
  rw [Nat.card_zpowers, Nat.card_zpowers, hco.orderOf_pow]

theorem five_pow_four_le_card_centralizer_Q [Finite G] {x h z : G} {q : Fin 4 → G}
    (hR : FiveLocal.Rel x h q z) {y : G} (hy : y ∈ FiveLocal.Q q) :
    5 ^ 4 ≤ Nat.card ↥(FiveLocal.Q q ⊓ Subgroup.centralizer ({y} : Set G)) := by
  let φ : ↥(FiveLocal.Q q) →* Multiplicative (ZMod 5) :=
    { toFun := fun u => Multiplicative.ofAdd (lg 5 z (bcomm y u))
      map_one' := by
        rw [OneMemClass.coe_one, show bcomm y 1 = 1 by simp [bcomm], lg_one hR.orderOf_z,
          ofAdd_zero]
      map_mul' := fun u v => by
        rw [← ofAdd_add, Subgroup.coe_mul, hR.bcomm_mul_right hy u.2 v.2,
          lg_mul hR.orderOf_z (hR.bcomm_mem hy u.2) (hR.bcomm_mem hy v.2)] }
  have hker : ∀ u : ↥(FiveLocal.Q q), φ u = 1 → (u : G) * y = y * u := by
    intro u hu
    have h0 : lg 5 z (bcomm y u) = 0 := ofAdd_eq_one.1 hu
    have h1 : bcomm y u = 1 := by
      have := pow_lg (p := 5) hR.orderOf_z (hR.bcomm_mem hy u.2)
      rw [h0, ZMod.val_zero, pow_zero] at this
      exact this.symm
    exact (bcomm_eq_one_iff.1 h1).symm
  have hcard := Subgroup.card_ker_mul_card_range φ
  rw [hR.card_Q] at hcard
  have hrange : Nat.card φ.range ≤ 5 := by
    calc Nat.card φ.range ≤ Nat.card (Multiplicative (ZMod 5)) := Subgroup.card_le_card_group _
      _ = 5 := by rw [Nat.card_eq_fintype_card]; rfl
  have hk : 5 ^ 4 ≤ Nat.card φ.ker := by
    by_contra hlt
    push Not at hlt
    have h1 : Nat.card φ.ker * Nat.card φ.range ≤ Nat.card φ.ker * 5 :=
      Nat.mul_le_mul_left _ hrange
    have h2 : 5 ^ 5 ≤ Nat.card φ.ker * 5 := hcard ▸ h1
    omega
  calc 5 ^ 4 ≤ Nat.card φ.ker := hk
    _ ≤ Nat.card ↥(FiveLocal.Q q ⊓ Subgroup.centralizer ({y} : Set G)) := by
      refine Nat.card_le_card_of_injective (fun u => ⟨((u : ↥(FiveLocal.Q q)) : G),
        Subgroup.mem_inf.2 ⟨(u : ↥(FiveLocal.Q q)).2,
          Subgroup.mem_centralizer_singleton_iff.2 (hker u (MonoidHom.mem_ker.1 u.2))⟩⟩) ?_
      intro a b hab
      have h := congrArg Subtype.val hab
      simp only at h
      exact Subtype.ext (Subtype.ext h)

end Generic

theorem rank_bMat_conj (g y : B) : (bMat (g * y * g⁻¹) - 1).rank = (bMat y - 1).rank := by
  rw [map_mul, map_mul]
  exact rank_sub_one_conj (by rw [← map_mul, mul_inv_cancel, map_one])

theorem rank_bMat_pow {y : B} (hy : orderOf y = 5) {c : ℕ} (hc : ¬ 5 ∣ c) :
    (bMat (y ^ c) - 1).rank = (bMat y - 1).rank := by
  have hb : (y ^ c) ^ (c ^ 3) = y := by
    rw [← pow_mul]
    conv_rhs => rw [← pow_one y]
    rw [pow_eq_pow_iff_modEq, hy]
    have hr : c % 5 < 5 := Nat.mod_lt _ (by norm_num)
    have hr0 : c % 5 ≠ 0 := fun h0 => hc (Nat.dvd_of_mod_eq_zero h0)
    show (c * c ^ 3) % 5 = 1 % 5
    rw [Nat.mul_mod, Nat.pow_mod]
    interval_cases (c % 5) <;> simp_all
  rw [map_pow]
  exact rank_pow_sub_one_eq (by rw [← map_pow, ← map_pow, hb])

section Elements


theorem yAFive_mem_Q : yAFive ∈ FiveLocal.Q qFive :=
  (FiveLocal.Q qFive).mul_mem (FiveLocal.q_mem 1) (FiveLocal.q_mem 2)

end Elements

section FiveLocalZ


theorem tFive_mem_centralizer_zFive : tFive ∈ Subgroup.centralizer ({zFive} : Set B) := by
  have hR := bFiveRel
  have hz5 : zFive ^ 16 = zFive := by
    rw [← pow_mod_orderOf, hR.orderOf_z]
    norm_num
  have h := conj_pow_eq_pow_pow (G := B) hR.conj_hz 4
  rw [show (2 : ℕ) ^ 4 = 16 by norm_num, hz5] at h
  rw [Subgroup.mem_centralizer_singleton_iff, tFive]
  calc hFive ^ 4 * zFive = hFive ^ 4 * ((hFive ^ 4)⁻¹ * zFive * hFive ^ 4) := by rw [h]
    _ = zFive * hFive ^ 4 := by group

end FiveLocalZ

section KSide


theorem tFive_mem_centralizer_yAFive : tFive ∈ Subgroup.centralizer ({yAFive} : Set B) :=
  Subgroup.mem_centralizer_singleton_iff.2 bFiveAK_parts.1

end KSide

section FiveLocalK


theorem orderOf_yAFive : orderOf yAFive = 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine orderOf_eq_prime (bFiveRel.pow_five_of_mem yAFive_mem_Q) ?_
  intro h
  have hr := bFiveAK_parts.2.1
  rw [h, map_one, sub_self, Matrix.rank_zero] at hr
  norm_num at hr

end FiveLocalK

section MSide


theorem orderOf_sFiveA : orderOf sFiveA = 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact orderOf_eq_prime bFiveAM_parts.1 bFiveAM_parts.2.1

theorem aFiveA_mem_centralizer_sFiveA : aFiveA ∈ Subgroup.centralizer ({sFiveA} : Set B) :=
  Subgroup.mem_centralizer_singleton_iff.2 bFiveAM_parts.2.2.2.2.2.2.2.2.2.2.2.1

theorem bFiveA_mem_centralizer_sFiveA : bFiveA ∈ Subgroup.centralizer ({sFiveA} : Set B) :=
  Subgroup.mem_centralizer_singleton_iff.2 bFiveAM_parts.2.2.2.2.2.2.2.2.2.2.2.2

end MSide

section TwoB


theorem babyInv_one_aFiveA : BabyInv 1 aFiveA := by
  obtain ⟨-, -, -, haa, ha1, har, -⟩ := bFiveAM_parts
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.Monster.Existence.babyInv_one_of_rank_2048
    (orderOf_eq_prime (by rw [sq]; exact haa) ha1) har

theorem babyInv_one_bFiveA : BabyInv 1 bFiveA := by
  obtain ⟨-, -, -, -, -, -, hbb, hb1, hbr, -⟩ := bFiveAM_parts
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.Monster.Existence.babyInv_one_of_rank_2048
    (orderOf_eq_prime (by rw [sq]; exact hbb) hb1) hbr

theorem babyInv_one_aFiveA_mul_bFiveA : BabyInv 1 (aFiveA * bFiveA) := by
  obtain ⟨-, -, -, haa, -, -, hbb, -, -, hab, habr, -⟩ := bFiveAM_parts
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (aFiveA * bFiveA) ^ 2 = 1 := by
    rw [sq]
    calc aFiveA * bFiveA * (aFiveA * bFiveA) = aFiveA * (bFiveA * aFiveA) * bFiveA := by group
      _ = aFiveA * (aFiveA * bFiveA) * bFiveA := by rw [hab]
      _ = (aFiveA * aFiveA) * (bFiveA * bFiveA) := by group
      _ = 1 := by rw [haa, hbb, one_mul]
  have h1 : aFiveA * bFiveA ≠ 1 := by
    intro h
    rw [h, map_one, sub_self, Matrix.rank_zero] at habr
    norm_num at habr
  exact CFSG.Monster.Existence.babyInv_one_of_rank_2048 (orderOf_eq_prime h2 h1) habr

end TwoB

section Main


theorem exists_conj_mem_centralizer_xB {y t : B} (ht : BabyInv 1 t)
    (hty : t ∈ Subgroup.centralizer ({y} : Set B)) :
    ∃ d : B, d * y * d⁻¹ ∈ Subgroup.centralizer ({xB} : Set B) := by
  obtain ⟨c, hc⟩ :=
    isConj_iff.1 (CFSG.Monster.Existence.babyTableIII.2 1 t xB ht babyInv_one_xB)
  refine ⟨c, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff, ← hc]
  have h := Subgroup.mem_centralizer_singleton_iff.1 hty
  calc c * y * c⁻¹ * (c * t * c⁻¹) = c * (y * t) * c⁻¹ := by group
    _ = c * (t * y) * c⁻¹ := by rw [← h]
    _ = c * t * c⁻¹ * (c * y * c⁻¹) := by group

theorem exists_conj_pow_of_same_line {y₁ y₂ : B} (h₁ : orderOf y₁ = 5) (h₂ : orderOf y₂ = 5)
    (hx₁ : y₁ ∈ Subgroup.centralizer ({xB} : Set B))
    (hx₂ : y₂ ∈ Subgroup.centralizer ({xB} : Set B)) {r : Fin 2} {a b : ℕ}
    {k₁ k₂ : Co2} (ha : ¬ 5 ∣ a) (hb : ¬ 5 ∣ b)
    (e₁ : k₁ * fiveHom ⟨y₁, hx₁⟩ * k₁⁻¹ = co2LineElt (co2FiveRepLine r) ^ a)
    (e₂ : k₂ * fiveHom ⟨y₂, hx₂⟩ * k₂⁻¹ = co2LineElt (co2FiveRepLine r) ^ b) :
    ∃ c : ℕ, ¬ 5 ∣ c ∧ ∃ g : B, g * y₂ ^ c * g⁻¹ = y₁ := by
  have hfin : Finite B :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.RankThree.OddKernel.card_B_eq]; norm_num)
  obtain ⟨c, hc, k, hk⟩ := exists_conj_pow_of_conj_pow (orderOf_co2LineElt _) ha hb e₁ e₂
  have hN : ¬ 5 ∣ Nat.card fiveHom.ker := by
    rw [card_ker_fiveHom]
    intro hd
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_five hd
    omega
  have ho₁ : orderOf (⟨y₁, hx₁⟩ : ↥(Subgroup.centralizer ({xB} : Set B))) = 5 := by
    rw [Subgroup.orderOf_mk, h₁]
  have ho₂ : orderOf ((⟨y₂, hx₂⟩ : ↥(Subgroup.centralizer ({xB} : Set B))) ^ c) = 5 := by
    have hco : (orderOf (⟨y₂, hx₂⟩ : ↥(Subgroup.centralizer ({xB} : Set B)))).Coprime c := by
      rw [Subgroup.orderOf_mk, h₂]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 hc
    rw [hco.orderOf_pow, Subgroup.orderOf_mk, h₂]
  obtain ⟨g, hg⟩ := exists_conj_eq_of_map_conj Nat.prime_five fiveHom fiveHom_surjective hN ho₁
    ho₂ (k := k) (by rw [map_pow]; exact hk)
  refine ⟨c, hc, g, ?_⟩
  have := congrArg Subtype.val hg
  simpa using this

theorem exists_conj_pow_zFive_or_sFiveA {y : B} (hy : orderOf y = 5) {t : B} (ht : BabyInv 1 t)
    (hty : t ∈ Subgroup.centralizer ({y} : Set B)) :
    ∃ c : ℕ, ¬ 5 ∣ c ∧ ∃ g : B, g * zFive ^ c * g⁻¹ = y ∨ g * sFiveA ^ c * g⁻¹ = y := by
  have hR := bFiveRel
  obtain ⟨dy, hdy⟩ := exists_conj_mem_centralizer_xB ht hty
  obtain ⟨dz, hdz⟩ := exists_conj_mem_centralizer_xB babyInv_one_tFive tFive_mem_centralizer_zFive
  obtain ⟨ds, hds⟩ :=
    exists_conj_mem_centralizer_xB babyInv_one_aFiveA aFiveA_mem_centralizer_sFiveA
  have hoy : orderOf (dy * y * dy⁻¹) = 5 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hy]
  have hoz : orderOf (dz * zFive * dz⁻¹) = 5 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hR.orderOf_z]
  have hos : orderOf (ds * sFiveA * ds⁻¹) = 5 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, orderOf_sFiveA]
  obtain ⟨ry, ay, ky, hay, ey⟩ := exists_conj_pow_co2LineElt (orderOf_fiveHom hoy hdy)
  obtain ⟨rz, az, kz, haz, ez⟩ := exists_conj_pow_co2LineElt (orderOf_fiveHom hoz hdz)
  obtain ⟨rs, as, ks, has, es⟩ := exists_conj_pow_co2LineElt (orderOf_fiveHom hos hds)
  have hzs : rz ≠ rs := by
    intro hrs
    rw [hrs] at ez
    obtain ⟨c, hc, g, hg⟩ := exists_conj_pow_of_same_line hoz hos hdz hds haz has ez es
    rw [conj_pow] at hg
    have e : (dz⁻¹ * g * ds) * sFiveA ^ c * (dz⁻¹ * g * ds)⁻¹ = zFive := by
      calc (dz⁻¹ * g * ds) * sFiveA ^ c * (dz⁻¹ * g * ds)⁻¹
          = dz⁻¹ * (g * (ds * sFiveA ^ c * ds⁻¹) * g⁻¹) * dz := by group
        _ = dz⁻¹ * (dz * zFive * dz⁻¹) * dz := by rw [hg]
        _ = zFive := by group
    have hr := rank_bMat_conj (dz⁻¹ * g * ds) (sFiveA ^ c)
    rw [e, rank_bMat_pow orderOf_sFiveA hc, bFiveAK_parts.2.2, bFiveAM_parts.2.2.1] at hr
    norm_num at hr
  have key : ∀ a b c : Fin 2, b ≠ c → a = b ∨ a = c := by decide
  rcases key ry rz rs hzs with hry | hry
  · rw [hry] at ey
    obtain ⟨c, hc, g, hg⟩ := exists_conj_pow_of_same_line hoy hoz hdy hdz hay haz ey ez
    rw [conj_pow] at hg
    refine ⟨c, hc, dy⁻¹ * g * dz, Or.inl ?_⟩
    calc (dy⁻¹ * g * dz) * zFive ^ c * (dy⁻¹ * g * dz)⁻¹
        = dy⁻¹ * (g * (dz * zFive ^ c * dz⁻¹) * g⁻¹) * dy := by group
      _ = dy⁻¹ * (dy * y * dy⁻¹) * dy := by rw [hg]
      _ = y := by group
  · rw [hry] at ey
    obtain ⟨c, hc, g, hg⟩ := exists_conj_pow_of_same_line hoy hos hdy hds hay has ey es
    rw [conj_pow] at hg
    refine ⟨c, hc, dy⁻¹ * g * ds, Or.inr ?_⟩
    calc (dy⁻¹ * g * ds) * sFiveA ^ c * (dy⁻¹ * g * ds)⁻¹
        = dy⁻¹ * (g * (ds * sFiveA ^ c * ds⁻¹) * g⁻¹) * dy := by group
      _ = dy⁻¹ * (dy * y * dy⁻¹) * dy := by rw [hg]
      _ = y := by group

theorem exists_conj_sFiveA_pow_eq_yAFive :
    ∃ c : ℕ, ¬ 5 ∣ c ∧ ∃ g : B, g * sFiveA ^ c * g⁻¹ = yAFive := by
  obtain ⟨c, hc, g, hg | hg⟩ := exists_conj_pow_zFive_or_sFiveA orderOf_yAFive babyInv_one_tFive
    tFive_mem_centralizer_yAFive
  · exfalso
    have hr := rank_bMat_conj g (zFive ^ c)
    rw [hg, rank_bMat_pow bFiveRel.orderOf_z hc, bFiveAK_parts.2.1, bFiveAK_parts.2.2] at hr
    norm_num at hr
  · exact ⟨c, hc, g, hg⟩

theorem odd_card_gLAPPrimeCoreOf_sFiveA :
    Odd (Nat.card (GLAPPrimeCoreOf 5 (Subgroup.centralizer ({sFiveA} : Set B)))) := by
  have hfin : Finite B :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.RankThree.OddKernel.card_B_eq]; norm_num)
  have hR := bFiveRel
  obtain ⟨c, hc, g, hg⟩ := exists_conj_sFiveA_pow_eq_yAFive
  have hodd := odd_card_gLAPPrimeCoreOf_B_five orderOf_yAFive
    (hR.isPGroup_Q.to_le inf_le_left) (five_pow_four_le_card_centralizer_Q hR yAFive_mem_Q)
    inf_le_right (Subgroup.mem_inf.2 ⟨yAFive_mem_Q, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩)
    babyInv_one_tFive tFive_mem_centralizer_yAFive
  rw [← hg, card_gLAPPrimeCoreOf_centralizer_conj] at hodd
  rwa [centralizer_eq_of_zpowers_eq (zpowers_pow_eq_of_five orderOf_sFiveA hc)] at hodd

theorem gLAPPrimeCoreOf_centralizer_sFiveA_eq_bot :
    GLAPPrimeCoreOf 5 (Subgroup.centralizer ({sFiveA} : Set B)) = ⊥ := by
  have hfin : Finite B :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.RankThree.OddKernel.card_B_eq]; norm_num)
  have hodd := odd_card_gLAPPrimeCoreOf_sFiveA
  set C := Subgroup.centralizer ({sFiveA} : Set B) with hC
  set O := GLAPPrimeCoreOf 5 C with hO
  have hfix : ∀ w : B, BabyInv 1 w → w ∈ C → ∀ q ∈ O, w * q * w⁻¹ = q → q = 1 := by
    intro w hw hwC q hq hqw
    have hqw' : q ∈ Subgroup.centralizer ({w} : Set B) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc q * w = (w * q * w⁻¹) * w := by rw [hqw]
        _ = w * q := by group
    exact eq_one_of_pow_two_pow_of_odd hodd hq (pow_two_pow_eq_one_of_babyInv_one Nat.prime_five
      (by norm_num) oPrimeCoreTrivialAt_Co2_five orderOf_sFiveA hw hwC hq hqw')
  have hinv : ∀ w : B, BabyInv 1 w → w ∈ C → ∀ q ∈ O, w * q * w⁻¹ = q⁻¹ := by
    intro w hw hwC
    have hww : w * w = 1 := by
      have := pow_orderOf_eq_one w
      rwa [hw.1, sq] at this
    exact inv_of_fixedPointFree_involution' (fun q hq => GLAPPrimeCoreOf_conj_mem w hwC q hq) hww
      (hfix w hw hwC)
  have ha := hinv aFiveA babyInv_one_aFiveA aFiveA_mem_centralizer_sFiveA
  have hb := hinv bFiveA babyInv_one_bFiveA bFiveA_mem_centralizer_sFiveA
  have hab : ∀ q ∈ O, aFiveA * bFiveA * q * (aFiveA * bFiveA)⁻¹ = q := by
    intro q hq
    calc aFiveA * bFiveA * q * (aFiveA * bFiveA)⁻¹ = aFiveA * (bFiveA * q * bFiveA⁻¹) * aFiveA⁻¹ :=
          by group
      _ = aFiveA * q⁻¹ * aFiveA⁻¹ := by rw [hb q hq]
      _ = q⁻¹⁻¹ := ha q⁻¹ (O.inv_mem hq)
      _ = q := inv_inv q
  have habC : aFiveA * bFiveA ∈ C :=
    C.mul_mem aFiveA_mem_centralizer_sFiveA bFiveA_mem_centralizer_sFiveA
  rw [eq_bot_iff]
  intro q hq
  exact (Subgroup.mem_bot).2 (hfix _ babyInv_one_aFiveA_mul_bFiveA habC q hq (hab q hq))

theorem oPrimeCoreTrivialAt_B_five_of_twoBCover (h : BFiveTwoBCover) :
    OPrimeCoreTrivialAt 5 B := by
  have hfin : Finite B :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.RankThree.OddKernel.card_B_eq]; norm_num)
  intro s hs
  obtain ⟨t, ht, hts⟩ := h s hs
  obtain ⟨c, hc, g, hg | hg⟩ := exists_conj_pow_zFive_or_sFiveA hs ht hts
  · rw [← hg, gLAPPrimeCoreOf_centralizer_conj,
      centralizer_eq_of_zpowers_eq (zpowers_pow_eq_of_five bFiveRel.orderOf_z hc)]
    exact gLAPPrimeCoreOf_centralizer_zFive_eq_bot
  · rw [← hg, gLAPPrimeCoreOf_centralizer_conj,
      centralizer_eq_of_zpowers_eq (zpowers_pow_eq_of_five orderOf_sFiveA hc)]
    exact gLAPPrimeCoreOf_centralizer_sFiveA_eq_bot

theorem bFiveNonCentral_of_twoBCover (h : BFiveTwoBCover) : BFiveNonCentral :=
  fun s hs _ => oPrimeCoreTrivialAt_B_five_of_twoBCover h s hs

end Main

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
