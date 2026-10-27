module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma83
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma85Aux

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB Lemma85Aux

variable {G : Type} [Group G] [Finite G] {m p : ℕ}

theorem lemma85 (i33 : Input33_4) (hS : GLStanding G m p) {B M₀ : Subgroup G}
    (hB : IsBOneMax p B) (hM : IsPreUniquenessSubgroup p B M₀)
    (h84 : GLAPLayer 2 (GLAPPrimeCoreOf p M₀) = ⊥)
    {Q : Subgroup G} (hQ2 : IsPGroup 2 Q) (hQR : Q ≤ oTwoPrimeTwo (GLAPPrimeCoreOf p M₀))
    (hQmax : ∀ Q' : Subgroup G, Q ≤ Q' → Q' ≤ oTwoPrimeTwo (GLAPPrimeCoreOf p M₀) →
      IsPGroup 2 Q' → Q' = Q)
    (hBQ : B ≤ Subgroup.normalizer (Q : Set G))
    {P : Sylow 2 G} (hPQ : Q ≤ (P : Subgroup G)) {U : Subgroup G}
    (hU : IsUGroup 2 (P : Subgroup G) U) :
    Q ≠ ⊥ ∧ Q = pCoreOf 2 (Subgroup.normalizer (Q : Set G)) ∧
      U ≤ Subgroup.normalizer (Q : Set G) ∧ (U ≤ M₀ → pCoreOf 2 M₀ ≠ ⊥) := by
  have hp := hS.prime
  have hp2 := hS.ne_two
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXM : GLAPPrimeCoreOf p M₀ ≤ M₀ := glaPPrimeCoreOf_le_self M₀ p
  have hMX : M₀ ≤ Subgroup.normalizer (GLAPPrimeCoreOf p M₀ : Set G) :=
    le_normalizer_glaPPrimeCoreOf p M₀
  have hMY := normalizer_le_glaPPrimeCoreOf (X := GLAPPrimeCoreOf p M₀) 2 hMX
  have hMR := normalizer_le_oTwoPrimeTwo hMX
  have hRX := oTwoPrimeTwo_le (GLAPPrimeCoreOf p M₀)
  have hRsup := oTwoPrimeTwo_eq_sup hQR hQ2 hQmax
  have hBM : B ≤ M₀ := hM.le hS hB
  have hQne : Q ≠ ⊥ := by
    rintro rfl
    have hlay : layerPreimage (GLAPPrimeCoreOf p M₀) = GLAPPrimeCoreOf 2 (GLAPPrimeCoreOf p M₀) := by
      unfold layerPreimage
      rw [h84, hRsup, sup_bot_eq, bot_sup_eq]
    have := hS.nontrivial hB
    obtain ⟨⟨b, hb⟩, hb1⟩ := exists_ne (1 : B)
    apply hb1
    have := lemma83 hS hB hM hb (fun y hy => by
      rw [hlay] at hy
      exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.1 (hMY (hBM hb)) y).1 hy)
        (Subgroup.inv_mem _ hy))
    exact Subtype.ext this

  have hBN : B ≤ Subgroup.normalizer (Q : Set G) := hBQ
  have hZM := hM.pCoreOf_two_le hS hB hBN
  have hZN : Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 (Subgroup.normalizer (Q : Set G)) : Set G) :=
    Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  have hZ2 := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (Subgroup.normalizer (Q : Set G))
  have hZR := le_oTwoPrimeTwo_of_frattini hp hp2 hQR hQ2 hQmax hZ2 hZM hZN
  have hQZ : Q ≤ pCoreOf 2 (Subgroup.normalizer (Q : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hQ2
  have hQeq : Q = pCoreOf 2 (Subgroup.normalizer (Q : Set G)) :=
    (hQmax _ hQZ hZR hZ2).symm
  have hPp : IsPGroup 2 (P : Subgroup G) := P.isPGroup'
  obtain ⟨hUP, hPU, hUplane, hU4⟩ := hU
  have hUcard : Nat.card U = 4 := by rw [hUplane.2]; norm_num
  have hUne : U ≠ ⊥ := by
    rintro rfl
    simp at hUcard
  obtain ⟨z, hzU, hz1, hzZ⟩ := exists_mem_inf_centerOf hPp hUP hPU hUne
  have hzcomm : ∀ g ∈ (P : Subgroup G), g * z = z * g := by
    obtain ⟨a, ha, rfl⟩ := hzZ
    intro g hg
    have := Subgroup.mem_center_iff.1 ha ⟨g, hg⟩
    exact congrArg Subtype.val this
  have hzQ : z ∈ Q := by
    have hzC : z ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact hzcomm h (hPQ hh)
    have hloc : IsTwoLocal (Subgroup.normalizer (Q : Set G)) := ⟨Q, hQne, hQ2, rfl⟩
    have key := hS.charTwo _ hloc
    rw [← hQeq] at key
    exact key ⟨Subgroup.centralizer_le_normalizer (Q : Set G) hzC, hzC⟩
  have hUcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hUplane.1.1.is_comm.comm (⟨a, ha⟩ : U) ⟨b, hb⟩)
  have hUN : U ≤ Subgroup.normalizer (Q : Set G) := by
    intro u hu
    refine Subgroup.mem_normalizer_fintype fun q hq => ?_
    have hqP : q ∈ (P : Subgroup G) := hPQ hq
    have hcU : ∀ u ∈ U, q * u * q⁻¹ ∈ U := fun u hu =>
      (Subgroup.mem_normalizer_iff.1 (hPU hqP) u).1 hu
    have hcz : q * z * q⁻¹ = z := by
      rw [hzcomm q hqP]; group
    have ht := inv_mul_conj_mem_zpowers hUplane.1 hUcard hzU hz1 hcU hcz hu
    have htQ : u⁻¹ * (q * u * q⁻¹) ∈ Q := (Subgroup.zpowers_le.2 hzQ) ht
    have hv := hcU u hu
    have hcm := hUcomm _ hv u⁻¹ (U.inv_mem hu)
    have : u * q * u⁻¹ = (u⁻¹ * (q * u * q⁻¹))⁻¹ * q := by
      have e : u⁻¹ * (q * u * q⁻¹) = (q * u * q⁻¹) * u⁻¹ := hcm.symm
      rw [e]; group
    rw [this]
    exact Q.mul_mem (Q.inv_mem htQ) hq
  refine ⟨hQne, hQeq, hUN, fun hUM => ?_⟩
  have hodd : Odd (Nat.card (GLAPPrimeCoreOf 2 (GLAPPrimeCoreOf p M₀))) :=
    Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1
      (not_dvd_card_glaPPrimeCoreOf Nat.prime_two (GLAPPrimeCoreOf p M₀)))
  have hUY : U ≤ Subgroup.centralizer (GLAPPrimeCoreOf 2 (GLAPPrimeCoreOf p M₀) : Set G) :=
    i33 G hS.charTwo P U ⟨hUP, hPU, hUplane, hU4⟩ _ hodd (hUM.trans hMY)
  have hQY : Q ≤ Subgroup.normalizer (GLAPPrimeCoreOf 2 (GLAPPrimeCoreOf p M₀) : Set G) :=
    (hQR.trans hRX).trans (hXM.trans hMY)
  have hU0ne : U ⊓ Q ≠ ⊥ := by
    intro h
    have hz : z ∈ U ⊓ Q := ⟨hzU, hzQ⟩
    rw [h] at hz
    exact hz1 (Subgroup.mem_bot.1 hz)
  have hRN : oTwoPrimeTwo (GLAPPrimeCoreOf p M₀) ≤ Subgroup.normalizer ((U ⊓ Q : Subgroup G) : Set G) := by
    intro r hr
    have hr' : r ∈ ((GLAPPrimeCoreOf 2 (GLAPPrimeCoreOf p M₀) ⊔ Q : Subgroup G) : Set G) := by
      rw [← hRsup]; exact hr
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hQY] at hr'
    obtain ⟨y, hy, q, hq, rfl⟩ := hr'
    refine Subgroup.mem_normalizer_fintype fun u hu => ?_
    have hqP : q ∈ (P : Subgroup G) := hPQ hq
    have hu' : q * u * q⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 (hPU hqP) u).1 hu.1
    have hu'Q : q * u * q⁻¹ ∈ Q := Q.mul_mem (Q.mul_mem hq hu.2) (Q.inv_mem hq)
    have hc : y * (q * u * q⁻¹) = (q * u * q⁻¹) * y :=
      Subgroup.mem_centralizer_iff.1 (hUY hu') y hy
    have : y * q * u * (y * q)⁻¹ = q * u * q⁻¹ := by
      calc y * q * u * (y * q)⁻¹ = y * (q * u * q⁻¹) * y⁻¹ := by group
        _ = q * u * q⁻¹ := by rw [hc]; group
    rw [this]
    exact ⟨hu', hu'Q⟩
  have hU0R : U ⊓ Q ≤ pCoreOf 2 (oTwoPrimeTwo (GLAPPrimeCoreOf p M₀)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (inf_le_right.trans hQR) hRN
      (hQ2.to_le inf_le_right)
  have hDM : pCoreOf 2 (oTwoPrimeTwo (GLAPPrimeCoreOf p M₀)) ≤ pCoreOf 2 M₀ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (hRX.trans hXM))
      (hMR.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  intro h
  exact hU0ne (le_bot_iff.1 (h ▸ hU0R.trans hDM))

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
