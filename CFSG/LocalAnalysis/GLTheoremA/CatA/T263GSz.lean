module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263GVac
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcSmall
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CaseTwoNoTwoSz32
import CFSG.RankThree.PartOne.K159.AutSzIso
import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bArith

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

section Sz

theorem t263_suzuki_odd_not_comm_invol {S' : Type} [Group S'] [Finite S'] {f : ℕ}
    (hS : CFSG.Blueprint.SuzukiModel S' 2 f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {s w : S'}
    (hsp : s ^ p = 1) (hs1 : s ≠ 1) (hw : orderOf w = 2) (hc : w * s = s * w) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, a, ha, K, _, _, hfa, hKcard, ⟨e⟩⟩ := hS
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hKcard
  have hyo : orderOf (e w) = 2 := by rw [MulEquiv.orderOf_eq]; exact hw
  obtain ⟨S₂, hS₂⟩ :=
    ComponentClassification.UnbalancedGS.SuzukiOddCore.suzuki_involution_centralizer_sylow hK (e w) hyo
  have hsS : e s ∈ (S₂ : Subgroup (CFSG.Blueprint.suzukiGroup a K)) := by
    rw [hS₂]
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by rw [← map_mul, ← map_mul, hc])
  have hsord : orderOf (e s) = p :=
    orderOf_eq_prime (by rw [← map_pow, hsp, map_one])
      (fun h1 => hs1 (e.injective (h1.trans (map_one e).symm)))
  have hpS : IsPGroup 2 (S₂ : Subgroup (CFSG.Blueprint.suzukiGroup a K)) := S₂.isPGroup'
  obtain ⟨k, hk⟩ := hpS ⟨e s, hsS⟩
  have hdvd : p ∣ 2 ^ k := by
    have h1 : orderOf (⟨e s, hsS⟩ : (S₂ : Subgroup (CFSG.Blueprint.suzukiGroup a K))) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one hk
    rwa [Subgroup.orderOf_mk, hsord] at h1
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))

theorem t263_sz_inner_elt {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω}
    (hSn : S.Normal) (hSq : CFSG.Open.IsQuasisimple ↥S) (hSp : GLAPPrimeCore p ↥S = ⊥)
    (hcat : catalogIs (PSimple p S) K155X.l154ExcSuz) {x : Ω} (hxp : x ^ p = 1)
    (hInn : InnDiagOn p (Subgroup.zpowers x) S) (hxC : x ∉ Subgroup.centralizer (S : Set Ω)) :
    ∃ s : PSimple p S, MI.indAut p S x (t263_normalizer_of_normal hSn) = MulAut.conj s ∧ s ^ p = 1 ∧ s ≠ 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hxN : x ∈ Subgroup.normalizer (S : Set Ω) := t263_normalizer_of_normal hSn
  have hxN' : x⁻¹ ∈ Subgroup.normalizer (S : Set Ω) := Subgroup.inv_mem _ hxN
  have hcomp : GLAPComponent p S S := glaPComponent_self_p hSq hSp
  obtain ⟨s, hs⟩ := K155X.l154_inner_of_innDiagOn_suz hp hcomp hcat hxN hInn
  haveI : IsSimpleGroup (↥S ⧸ Subgroup.center ↥S) := hSq.2
  haveI : IsSimpleGroup (PSimple p S) := (pSimpleEquiv hSp).isSimpleGroup
  have hnab : ∃ a b : PSimple p S, a * b ≠ b * a := by
    have := CFSG.StandardType.exists_mul_ne_mul_centerQuot_of_perfect hSq.1 inferInstance
    obtain ⟨a, b, hab⟩ := this
    refine ⟨(pSimpleEquiv hSp).symm a, (pSimpleEquiv hSp).symm b, fun h => hab ?_⟩
    have := congrArg (pSimpleEquiv hSp) h
    simpa using this
  have hZ : Subgroup.center (PSimple p S) = ⊥ :=
    CFSG.StandardType.center_eq_bot_of_isSimpleGroup_of_nonabelian hnab
  have hind1 : MI.indAut p S x hxN ^ p = 1 := by
    show chevAut p S ⟨x⁻¹, hxN'⟩ ^ p = 1
    rw [← map_pow]
    have : (⟨x⁻¹, hxN'⟩ : ↥(Subgroup.normalizer (S : Set Ω))) ^ p = 1 :=
      Subtype.ext (by simp [inv_pow, hxp])
    rw [this, map_one]
  refine ⟨s, hs.symm, ?_, ?_⟩
  · rw [← hs, ← map_pow] at hind1
    have hc : s ^ p ∈ Subgroup.center (PSimple p S) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut (PSimple p S) => φ g) hind1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * s ^ p = s ^ p * g * (s ^ p)⁻¹ * s ^ p := by rw [this]
        _ = s ^ p * g := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact hc
  · intro h1
    have h2 : chevAut p S ⟨x⁻¹, hxN'⟩ = 1 := by
      have : MI.indAut p S x hxN = 1 := by rw [← hs, h1, map_one]
      exact this
    have h3 := (chevAut_eq_one_iff hp hcomp hxN').1 h2
    exact hxC (by simpa using Subgroup.inv_mem _ ((centMod_iff_centralizer hSp hxN').1 h3))

theorem t263Desc_szAll : T263Desc t263GSzAll := by
  intro p hp hp2 Ω _ _ hK S B hSn hSq hSp hSc hQ hF2 hSB hΩ hB h4 hT hC B₀ hB₀ hdich hcase T' hT'ne hT'2 hT'S
    hBT' hker x hxB₀ hxC hxcomm
  exfalso
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxN : x ∈ Subgroup.normalizer (S : Set Ω) := t263_normalizer_of_normal hSn
  have hxN' : x⁻¹ ∈ Subgroup.normalizer (S : Set Ω) := Subgroup.inv_mem _ hxN
  have hcomp : GLAPComponent p S S := glaPComponent_self_p hSq hSp
  have hBel : CFSG.Open.IsElemAbelian p B := hB.1
  have hxB : x ∈ B := hB₀.1 hxB₀
  have hxp : x ^ p = 1 := hBel.2 x hxB
  have hcat : catalogIs (PSimple p S) K155X.l154ExcSuz := by
    obtain ⟨i, hi, ⟨e⟩⟩ := hQ
    exact ⟨i, hi, ⟨(pSimpleEquiv hSp).trans e⟩⟩
  have hInn : InnDiagOn p (Subgroup.zpowers x) S :=
    S10.innDiagOn_mono hB₀.2.1 (Subgroup.zpowers_le.2 hxB₀)
  obtain ⟨s, hs⟩ := K155X.l154_inner_of_innDiagOn_suz hp hcomp hcat hxN hInn
  obtain ⟨f, hSz⟩ := K155X.l154_suzukiModel_of_catalogIs hcat
  have hne : T' ⊓ Subgroup.centralizer ({x} : Set Ω) ≠ ⊥ := by
    intro h
    apply hxcomm
    rw [h]
    exact Subgroup.commutator_bot_right B₀
  have hU2 : IsPGroup 2 ↥(T' ⊓ Subgroup.centralizer ({x} : Set Ω)) := hT'2.to_le inf_le_left
  obtain ⟨w, hwU, hw2⟩ := exists_orderOf_two_of_isPGroup hU2 hne
  have hwT' : w ∈ T' := hwU.1
  have hwx : x * w = w * x := (Subgroup.mem_centralizer_singleton_iff.1 hwU.2).symm
  let wS : ↥S := ⟨w, hT'S hwT'⟩
  have hwS2 : orderOf wS = 2 := by
    rw [← hw2, ← Subgroup.orderOf_coe]
  let wb : PSimple p S := chevQuotHom p S wS
  have hwb1 : wb ≠ 1 := by
    intro h1
    have h2 : QuotientGroup.mk wS = (1 : ↥S ⧸ Subgroup.center ↥S) := by
      rw [← pSimpleEquiv_chevQuotHom hSp wS]
      exact (congrArg (pSimpleEquiv hSp) h1).trans (map_one _)
    exact t263_not_mem_center_of_orderOf_two hp hp2 hSp hwS2 ((QuotientGroup.eq_one_iff wS).1 h2)
  have hwb2 : orderOf wb = 2 := by
    refine orderOf_eq_prime ?_ hwb1
    have : wS ^ 2 = 1 := hwS2 ▸ pow_orderOf_eq_one wS
    show chevQuotHom p S wS ^ 2 = 1
    rw [← map_pow, this, map_one]
  have hfix : MI.indAut p S x hxN wb = wb := by
    have h3 := chevAut_chevQuotHom p S ⟨x⁻¹, hxN'⟩ wS
    have e : S.normalizerMonoidHom ⟨x⁻¹, hxN'⟩ wS = wS := by
      apply Subtype.ext
      show x⁻¹ * w * (x⁻¹)⁻¹ = w
      rw [inv_inv, mul_assoc, ← hwx, inv_mul_cancel_left]
    rw [e] at h3
    exact h3
  have hcomm : wb * s = s * wb := by
    have h1 : s * wb * s⁻¹ = wb := by
      have := hfix
      rw [← hs, MulAut.conj_apply] at this
      exact this
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  haveI : IsSimpleGroup (↥S ⧸ Subgroup.center ↥S) := hSq.2
  haveI : IsSimpleGroup (PSimple p S) := (pSimpleEquiv hSp).isSimpleGroup
  have hnab : ∃ a b : PSimple p S, a * b ≠ b * a := by
    have := CFSG.StandardType.exists_mul_ne_mul_centerQuot_of_perfect hSq.1 inferInstance
    obtain ⟨a, b, hab⟩ := this
    refine ⟨(pSimpleEquiv hSp).symm a, (pSimpleEquiv hSp).symm b, fun h => hab ?_⟩
    have := congrArg (pSimpleEquiv hSp) h
    simpa using this
  have hZ : Subgroup.center (PSimple p S) = ⊥ :=
    CFSG.StandardType.center_eq_bot_of_isSimpleGroup_of_nonabelian hnab
  have hind1 : MI.indAut p S x hxN ^ p = 1 := by
    show chevAut p S ⟨x⁻¹, hxN'⟩ ^ p = 1
    rw [← map_pow]
    have : (⟨x⁻¹, hxN'⟩ : ↥(Subgroup.normalizer (S : Set Ω))) ^ p = 1 :=
      Subtype.ext (by simp [inv_pow, hxp])
    rw [this, map_one]
  have hsp : s ^ p = 1 := by
    rw [← hs, ← map_pow] at hind1
    have hc : s ^ p ∈ Subgroup.center (PSimple p S) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut (PSimple p S) => φ g) hind1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * s ^ p = s ^ p * g * (s ^ p)⁻¹ * s ^ p := by rw [this]
        _ = s ^ p * g := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact hc
  have hs1 : s ≠ 1 := by
    intro h1
    have h2 : chevAut p S ⟨x⁻¹, hxN'⟩ = 1 := by
      have : MI.indAut p S x hxN = 1 := by rw [← hs, h1, map_one]
      exact this
    have h3 := (chevAut_eq_one_iff hp hcomp hxN').1 h2
    exact hxC (by simpa using Subgroup.inv_mem _ ((centMod_iff_centralizer hSp hxN').1 h3))
  exact t263_suzuki_odd_not_comm_invol hSz hp hp2 hsp hs1 hwb2 hcomm

theorem t263Desc_sz : T263Desc t263GSz := t263Desc_mono (fun _ hi => hi.1) t263Desc_szAll

theorem t263Vac_sz32 : T263Vac t263GSz32 := by
  intro p hp hp2 Ω _ _ S B hSn hSq hSp hQ hF2 hB h4 hT hC
  classical
  have hvh := t263VHyp_of_data hSn hSq hSp hB hp h4 hT
  haveI : IsSimpleGroup (↥S ⧸ Subgroup.center ↥S) := hSq.2
  obtain ⟨i, hi, ⟨e⟩⟩ := hQ
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie d =>
    obtain ⟨x, hv⟩ := d
    have hx : x = .suzuki 2 := by
      cases x <;> first | exact hi.elim | skip
      rename_i k
      rcases k with _ | _ | _ | k <;> first | exact hi.elim | rfl
    subst hx
    have hiso : CFSG.RankThree.PartOne.Census3.IsoLie (↥S ⧸ Subgroup.center ↥S) (.suzuki 2) := ⟨hv, ⟨e⟩⟩
    have hSz := CFSG.RankThree.PartOne.K159.SzAbs.szSylow_of_isoLie hiso
    have hmodel := CFSG.RankThree.PartOne.CTP.suzukiModel_of_isoLie 2 hiso
    have hOut : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer (↥S ⧸ Subgroup.center ↥S)) ∣ 5 :=
      (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} _ 2 5 hmodel).1.2.1
    have hcard : Nat.card (↥S ⧸ Subgroup.center ↥S) = 32537600 := hSz.card
    have hZ : Subgroup.center (↥S ⧸ Subgroup.center ↥S) = ⊥ :=
      center_eq_bot_of_simple_nonprime hcard (by norm_num)
    have hAut : Nat.card (MulAut (↥S ⧸ Subgroup.center ↥S)) =
        32537600 * Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer (↥S ⧸ Subgroup.center ↥S)) :=
      card_mulAut_eq_mul_outer hcard (by norm_num)
    by_cases hp5 : p = 5
    · subst hp5
      have hZ' : ∀ g : ↥S ⧸ Subgroup.center ↥S, (∀ y, g * y = y * g) → g = 1 := by
        intro g hg
        have : g ∈ Subgroup.center (↥S ⧸ Subgroup.center ↥S) := Subgroup.mem_center_iff.2 fun y => (hg y).symm
        rwa [hZ, Subgroup.mem_bot] at this
      refine t263_false_of_rank_bound' (m := 5) (r := 1) hp hp2 hvh hC (MulEquiv.refl _) hZ
        (fun P _ => ?_) ?_ (by norm_num)
      · have h1 := card_le_mul_card_inf_inner P
        have h2 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
            (↥S ⧸ Subgroup.center ↥S)) ≤ 5 := Nat.le_of_dvd (by norm_num) hOut
        exact h1.trans (Nat.mul_le_mul_right _ h2)
      · intro E T hE hT2 hT0 hET
        by_contra hlt
        push Not at hlt
        have hcardE : 5 ∣ Nat.card E := by
          obtain ⟨a, ha⟩ := exists_card_eq_pow_of_isElemAbelian hp hE
          rcases Nat.eq_zero_or_pos a with h0 | h0
          · rw [h0, pow_zero] at ha
            omega
          · rw [ha]
            exact dvd_pow_self 5 h0.ne'
        obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥E) 5 hcardE
        have ht5 : orderOf (t : ↥S ⧸ Subgroup.center ↥S) = 5 := by rw [Subgroup.orderOf_coe]; exact ht
        have hU : IsPGroup 2 (T.map (MulAut.conj : (↥S ⧸ Subgroup.center ↥S) →* MulAut (↥S ⧸ Subgroup.center ↥S))) :=
          hT2.map _
        have hN : MulAut.conj (t : ↥S ⧸ Subgroup.center ↥S) ∈
            Subgroup.normalizer ((T.map (MulAut.conj : (↥S ⧸ Subgroup.center ↥S) →* MulAut (↥S ⧸ Subgroup.center ↥S)) :
              Subgroup _) : Set _) :=
          Subgroup.le_normalizer_map _ ⟨(t : ↥S ⧸ Subgroup.center ↥S), hET t.2, rfl⟩
        have hbot := AGLEmbedding.SzNoTwo.eq_bot_of_normalizes hSz hZ' hOut ht5 hU hN
        have hinj : Function.Injective (MulAut.conj : (↥S ⧸ Subgroup.center ↥S) →* MulAut (↥S ⧸ Subgroup.center ↥S)) :=
          conj_injective_of_center_eq_bot hZ
        exact hT0 ((Subgroup.map_eq_bot_iff_of_injective T hinj).1 hbot)
    · refine t263_false_of_not_sq_dvd hp hvh hC (MulEquiv.refl _) fun hdvd => ?_
      rw [hAut] at hdvd
      have h5 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
          (↥S ⧸ Subgroup.center ↥S)) ∣ 5 := hOut
      have hdvd' : 32537600 * Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
          (↥S ⧸ Subgroup.center ↥S)) ∣ (2 ^ 10 * 5 ^ 3) * (31 * 41) := by
        have : (2 ^ 10 * 5 ^ 3) * (31 * 41) = 32537600 * 5 := by norm_num
        rw [this]
        exact Nat.mul_dvd_mul_left _ h5
      exact not_sq_dvd_of_dvd_mul_squarefree hp
        (Nat.Coprime.mul_right (Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2))
          (Nat.Coprime.pow_right _ ((Nat.coprime_primes hp (by norm_num)).2 hp5)))
        (squarefree_prime_mul (by norm_num) (by norm_num) (by norm_num)) hdvd' hdvd

end Sz

end CFSG.LocalAnalysis.GLTheoremA.T263

end
