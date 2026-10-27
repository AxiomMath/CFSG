module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432WitD4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420.WitG2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Yardstones.Md0ec50421ce4 CFSG.Open
open scoped commutatorElement


@[expose] def i2 : Fin Tag.G2.rank := ⟨1, by decide⟩

@[expose] def i1 : Fin Tag.G2.rank := ⟨0, by decide⟩

@[expose] def eS : Fin Tag.G2.rank → ℤ := Pi.single i2 1

@[expose] def eL : Fin Tag.G2.rank → ℤ := Pi.single i1 1

@[expose] def thetaG2 : Fin Tag.G2.rank → ℤ := ![2, 3]

theorem isRoot_eS : IsRoot Tag.G2 eS := isRoot_single Tag.G2 i2

theorem isRoot_eL : IsRoot Tag.G2 eL := isRoot_single Tag.G2 i1

theorem isRoot_thetaG2 :
    IsRoot Tag.G2 thetaG2 :=
  (g2_root_certificate.1 thetaG2).2 (by decide)

theorem cartan_sum_eS : ∑ j, Tag.G2.cartan i2 j * eS j = 2 := by
  decide

theorem cartan_sum_thetaG2 : ∑ j, Tag.G2.cartan i2 j * thetaG2 j = 0 := by
  decide

theorem cartan_sum_eL : ∑ j, Tag.G2.cartan i2 j * eL j = -3 := by
  decide

@[expose] noncomputable def tG2 (K : Type) [Field K] : (Module.End K (RootModule Tag.G2 K))ˣ :=
  torusElt Tag.G2 K i2 (-1)

theorem tG2_mem_adjointGroup (K : Type) [Field K] : tG2 K ∈ adjointGroup Tag.G2 K :=
  torusElt_mem_adjointGroup i2 (-1)

theorem tG2_mul_self (K : Type) [Field K] : tG2 K * tG2 K = 1 := by
  rw [tG2, ← torusElt_mul]
  have h : (-1 : Kˣ) * (-1) = 1 := by simp
  rw [h, torusElt_one]

theorem tG2_conj_eS (K : Type) [Field K] (c : K) :
    tG2 K * pinnedX Tag.G2 K eS c * (tG2 K)⁻¹ = pinnedX Tag.G2 K eS c := by
  rw [tG2, root_torus_conjugation i2 isRoot_eS (-1) c, cartan_sum_eS]
  simp

theorem tG2_conj_thetaG2 (K : Type) [Field K] (c : K) :
    tG2 K * pinnedX Tag.G2 K thetaG2 c * (tG2 K)⁻¹ = pinnedX Tag.G2 K thetaG2 c := by
  rw [tG2, root_torus_conjugation i2 isRoot_thetaG2 (-1) c, cartan_sum_thetaG2]
  simp

theorem tG2_conj_eL (K : Type) [Field K] (c : K) :
    tG2 K * pinnedX Tag.G2 K eL c * (tG2 K)⁻¹ = pinnedX Tag.G2 K eL (-c) := by
  rw [tG2, root_torus_conjugation i2 isRoot_eL (-1) c, cartan_sum_eL]
  congr 1
  have h : ((-1 : Kˣ) ^ (-3 : ℤ) : Kˣ) = -1 := by
    rw [zpow_neg]
    norm_num
  rw [h]
  simp

theorem tG2_not_mem_center (K : Type) [Field K] [CharP K 3] :
    (⟨tG2 K, tG2_mem_adjointGroup K⟩ : adjointGroup Tag.G2 K) ∉
      Subgroup.center (adjointGroup Tag.G2 K) := by
  intro hz
  have h := Subgroup.mem_center_iff.1 hz ⟨pinnedX Tag.G2 K eL 1, pinnedX_mem_adjointGroup eL 1⟩
  have hm : pinnedX Tag.G2 K eL 1 * tG2 K = tG2 K * pinnedX Tag.G2 K eL 1 :=
    congrArg Subtype.val h
  have hX : tG2 K * pinnedX Tag.G2 K eL 1 * (tG2 K)⁻¹ = pinnedX Tag.G2 K eL 1 := by
    rw [← hm, mul_inv_cancel_right]
  rw [tG2_conj_eL] at hX
  have h1 : (-1 : K) = 1 := by
    simpa using pinnedX_injective (τ := Tag.G2) (R := K) eL (by simpa using hX)
  exact CFSG.LocalAnalysis.GLTheoremA.H1420.WitD4.two_ne_zero_of_charThree (K := K)
    (by linear_combination -h1)

theorem tG2_comm_eS (K : Type) [Field K] (c : K) :
    tG2 K * pinnedX Tag.G2 K eS c = pinnedX Tag.G2 K eS c * tG2 K := by
  have := tG2_conj_eS K c
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this

theorem tG2_comm_thetaG2 (K : Type) [Field K] (d : K) :
    tG2 K * pinnedX Tag.G2 K thetaG2 d = pinnedX Tag.G2 K thetaG2 d * tG2 K := by
  have := tG2_conj_thetaG2 K d
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this

@[expose] def G2CommRes : Prop :=
  ∀ (K : Type) [Field K] [CharP K 3] (c d : K),
    pinnedX Tag.G2 K eS c * pinnedX Tag.G2 K thetaG2 d =
      pinnedX Tag.G2 K thetaG2 d * pinnedX Tag.G2 K eS c

@[expose] def G2DirectRes : Prop :=
  ∀ (K : Type) [Field K] [CharP K 3] (c d : K),
    pinnedX Tag.G2 K eS c * pinnedX Tag.G2 K thetaG2 d = 1 → c = 0 ∧ d = 0

@[expose] def iota3 (K : Type) [Field K] [CharP K 3] : ZMod 3 →+* K :=
  ZMod.castHom (dvd_refl 3) K

theorem iota3_injective (K : Type) [Field K] [CharP K 3] : Function.Injective (iota3 K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (iota3 K).injective

@[expose] noncomputable def phiFun (K : Type) [Field K] [CharP K 3]
    (p : Multiplicative (K × ZMod 3)) : adjointGroup Tag.G2 K :=
  ⟨pinnedX Tag.G2 K eS p.toAdd.1 * pinnedX Tag.G2 K thetaG2 (iota3 K p.toAdd.2),
    mul_mem (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _)⟩

theorem phiFun_one (K : Type) [Field K] [CharP K 3] : phiFun K 1 = 1 := by
  apply Subtype.ext
  show pinnedX Tag.G2 K eS 0 * pinnedX Tag.G2 K thetaG2 (iota3 K 0) = 1
  rw [map_zero, pinnedX_zero, pinnedX_zero, mul_one]

theorem mul_mul_aux {G : Type} [Group G] (xp xq ta tb : G) (h : xq * ta = ta * xq) :
    xp * xq * (ta * tb) = xp * ta * (xq * tb) := by
  simp only [mul_assoc]
  rw [← mul_assoc ta xq tb, ← h, mul_assoc xq ta tb]

theorem phiFun_mul (K : Type) [Field K] [CharP K 3] (hcomm : G2CommRes)
    (p q : Multiplicative (K × ZMod 3)) : phiFun K (p * q) = phiFun K p * phiFun K q := by
  apply Subtype.ext
  show pinnedX Tag.G2 K eS (p.toAdd.1 + q.toAdd.1) *
        pinnedX Tag.G2 K thetaG2 (iota3 K (p.toAdd.2 + q.toAdd.2)) =
      (pinnedX Tag.G2 K eS p.toAdd.1 * pinnedX Tag.G2 K thetaG2 (iota3 K p.toAdd.2)) *
        (pinnedX Tag.G2 K eS q.toAdd.1 * pinnedX Tag.G2 K thetaG2 (iota3 K q.toAdd.2))
  rw [map_add, pinnedX_add, pinnedX_add]
  exact mul_mul_aux _ _ _ _ (hcomm K q.toAdd.1 (iota3 K p.toAdd.2))

@[expose] noncomputable def phiG (K : Type) [Field K] [CharP K 3] (hcomm : G2CommRes) :
    Multiplicative (K × ZMod 3) →* adjointGroup Tag.G2 K where
  toFun := phiFun K
  map_one' := phiFun_one K
  map_mul' := phiFun_mul K hcomm

theorem center_G2_bot
    (K : Type) [Field K] [Finite K] :
    Subgroup.center (adjointGroup Tag.G2 K) = ⊥ :=
  CFSG.LieType.Chevalley.center_adjointGroup_eq_bot

@[expose] noncomputable def ttG2 (K : Type) [Field K] : adjointGroup Tag.G2 K := ⟨tG2 K, tG2_mem_adjointGroup K⟩

@[expose] noncomputable def piQ (K : Type) [Field K] :
    adjointGroup Tag.G2 K →* AdjointQuotient Tag.G2 K :=
  QuotientGroup.mk' _

theorem phiG_comm_ttG2 (K : Type) [Field K] [CharP K 3] (hcomm : G2CommRes)
    (p : Multiplicative (K × ZMod 3)) : phiG K hcomm p * ttG2 K = ttG2 K * phiG K hcomm p := by
  apply Subtype.ext
  show pinnedX Tag.G2 K eS p.toAdd.1 * pinnedX Tag.G2 K thetaG2 (iota3 K p.toAdd.2) * tG2 K =
    tG2 K * (pinnedX Tag.G2 K eS p.toAdd.1 * pinnedX Tag.G2 K thetaG2 (iota3 K p.toAdd.2))
  rw [mul_assoc, ← tG2_comm_thetaG2 K, ← mul_assoc, ← tG2_comm_eS K, mul_assoc]

theorem pow_three_eq_one_K3 (K : Type) [Field K] [CharP K 3]
    (p : Multiplicative (K × ZMod 3)) : p ^ 3 = 1 := by
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  have h3' : (3 : ZMod 3) = 0 := rfl
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  ext <;> simp [h3, h3']

theorem g2_witness
    (K : Type) [Field K] [Finite K] [CharP K 3]
    (hK : Nat.card K = 27) (hcomm : G2CommRes) (hdir : G2DirectRes)
    [Finite (AdjointQuotient Tag.G2 K)] :
    HasTwoLocalWitness (AdjointQuotient Tag.G2 K) 4 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Φ := (piQ K).comp (phiG K hcomm)
  have htt2 : ttG2 K * ttG2 K = 1 := Subtype.ext (tG2_mul_self K)
  have hu2 : piQ K (ttG2 K) ^ 2 = 1 := by
    rw [← map_pow, sq, htt2, map_one]
  have hu1 : piQ K (ttG2 K) ≠ 1 := by
    intro h
    rw [piQ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    exact tG2_not_mem_center K h
  have hord : orderOf (piQ K (ttG2 K)) = 2 := orderOf_eq_prime hu2 hu1
  have hcommV : ∀ p, Commute (Φ p) (piQ K (ttG2 K)) := by
    intro p
    show Φ p * piQ K (ttG2 K) = piQ K (ttG2 K) * Φ p
    show (piQ K) (phiG K hcomm p) * piQ K (ttG2 K) = piQ K (ttG2 K) * (piQ K) (phiG K hcomm p)
    rw [← map_mul, ← map_mul]
    exact congrArg (piQ K) (phiG_comm_ttG2 K hcomm p)
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro p hp
    have hc : phiG K hcomm p ∈ Subgroup.center (adjointGroup Tag.G2 K) :=
      (QuotientGroup.eq_one_iff _).1 hp
    rw [center_G2_bot K, Subgroup.mem_bot] at hc
    have hm : pinnedX Tag.G2 K eS p.toAdd.1 * pinnedX Tag.G2 K thetaG2 (iota3 K p.toAdd.2) = 1 :=
      congrArg Subtype.val hc
    obtain ⟨h1, h2⟩ := hdir K p.toAdd.1 (iota3 K p.toAdd.2) hm
    have hn : p.toAdd.2 = 0 := iota3_injective K (h2.trans (map_zero _).symm)
    apply Multiplicative.toAdd.injective
    rw [toAdd_one]
    exact Prod.ext h1 hn
  refine ⟨Subgroup.zpowers (piQ K (ttG2 K)), Φ.range, fun h => hu1 (Subgroup.zpowers_eq_bot.1 h),
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num), ?_, ?_, ?_⟩
  · rintro x ⟨p, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    have hc := hcommV p
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, by rw [((hc).zpow_right k).eq, mul_inv_cancel_right]⟩
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have hh : h = (Φ p)⁻¹ * (Φ p * h * (Φ p)⁻¹) * Φ p := by group
      rw [hh, ← hk, mul_assoc, ← ((hc).zpow_right k).eq, inv_mul_cancel_left]
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, fun z hz => ?_⟩
    · obtain ⟨p, hp⟩ := a.2
      obtain ⟨q, hq⟩ := b.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hp, ← hq, ← map_mul, ← map_mul, mul_comm]
    · obtain ⟨p, hp⟩ := hz
      rw [← hp, ← map_pow, pow_three_eq_one_K3 K p, map_one]
  · rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]
    show Nat.card (K × ZMod 3) = 3 ^ 4
    rw [Nat.card_prod, hK, Nat.card_eq_fintype_card, ZMod.card]
    norm_num

theorem i1432WitG2_G2
    (hcomm : G2CommRes) (hdir : G2DirectRes) :
    ∀ (S : Type) [Group S] [Finite S], catalogIs S (S8.isG2of 27) → HasTwoLocalWitness S 4 := by
  intro S _ _ hS
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex
    (P := fun | .G2 q => q.card = 27 | _ => False) hS
  cases d with
  | G2 q =>
    have hq : q.card = 27 := hP
    have hp2 : q.p ≠ 2 := by
      intro h2
      have hdvd : 2 ∣ q.card := by
        rw [TauCeti.PrimePower.card_def, h2]
        exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.1 q.exponent_pos)
      rw [hq] at hdvd
      norm_num at hdvd
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hK27 : Nat.card (GaloisField 3 3) = 27 := by
      rw [GaloisField.card 3 3 (by norm_num)]
      norm_num
    have hcard : Nat.card (GaloisField 3 3) = q.card := hK27.trans hq.symm
    obtain ⟨eK⟩ := CFSG.TauCetiBridge.untwistedBridge_G2 q hv hp2 (GaloisField 3 3) hcard
    have eS' : S ≃* AdjointQuotient Tag.G2 (GaloisField 3 3) := e.trans eK.symm
    haveI : Finite (AdjointQuotient Tag.G2 (GaloisField 3 3)) := Finite.of_equiv S eS'.toEquiv
    exact CFSG.LocalAnalysis.GLTheoremA.H1420.WitD4.hasTwoLocalWitness_of_mulEquiv eS'
      (g2_witness (GaloisField 3 3) hK27 hcomm hdir)
  | _ => exact (hP : False).elim

end CFSG.LocalAnalysis.GLTheoremA.H1420.WitG2

end
