module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.SmallOmega73
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.Omega73Lifts
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.Pullback
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HeisRelative
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.Small
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1
  CFSG.LieType.Steinberg.CentralExt.SpinOddClosed

theorem two_pow_54_le_of_omega73_center_three {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {L : Subgroup (MulAut W)} (hperf : Group.IsPerfect ↥L)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    (hZ : Nat.card (Subgroup.center ↥L) = 3)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedOmega (StatedQuadOdd 3 K))) :
    2 ^ 54 ≤ Nat.card W := by
  have hord : orderOf (2 : ZMod 3) = 2 :=
    orderOf_eq_prime (p := 2) (x := (2 : ZMod 3)) (by decide) (by decide)
  have h2 : (2 : K) ≠ 0 := CFSG.LieType.Steinberg.CentralExt.FieldThree.two_ne_zero_of_card_three hK
  have hn : 3 ≤ 3 := le_rfl
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have : Finite ↥L := inferInstance
  set ψ := spinToStatedProj (quadOdd 3 K) (range_spinMatrix_quadOdd h2 hn) with hψdef
  obtain ⟨hψs, -, hψc⟩ := spinToStatedProj_quadOdd h2 hn
  have : Group.IsPerfect (spinGroup (quadOdd 3 K)) := isPerfect_spinGroup_quadOdd h2 hn
  have : Finite (spinGroup (quadOdd 3 K)) :=
    CFSG.LieType.Steinberg.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadOdd h2)
  let φ : ↥L →* StatedProj (StatedOmega (StatedQuadOdd 3 K)) :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hφs : Function.Surjective φ := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hφk : φ.ker = Subgroup.center ↥L := by
    ext l
    simp [φ]
  have hcop : Nat.Coprime (Nat.card φ.ker) (Nat.card ψ.ker) := by
    rw [hφk, hZ, card_ker_spinToStatedProj_quadOdd h2 hn]
    norm_num
  have hψk : ψ.ker ≤ Subgroup.center (spinGroup (quadOdd 3 K)) := hψc.le
  have hFperf : Group.IsPerfect (pullback φ ψ) :=
    isPerfect_pullback hφs hψs hφk.le hψk hcop
  have : Finite (pullback φ ψ) := inferInstance
  let π : pullback φ ψ →* spinGroup (quadOdd 3 K) :=
    (MonoidHom.snd _ _).comp (pullback φ ψ).subtype
  have hπ : Function.Surjective π := pullback_snd_surjective hφs
  have hcen : π.ker ≤ Subgroup.center (pullback φ ψ) := ker_pullback_snd_le_center hφk.le
  have hkerc : Nat.card π.ker = 3 := by
    rw [card_ker_pullback_snd, hφk, hZ]
  have hker : π.ker ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hkerc
    omega
  obtain ⟨a, b, z, x, y, hzk, hz1, hz3, ha3, hb, hxa, hya, hx3, hyx, hxx, hyy, hxy⟩ :=
    relHeis_data hK hπ hcen hker
  let f : pullback φ ψ →* MulAut W :=
    (Subgroup.subtype L).comp ((MonoidHom.fst _ _).comp (pullback φ ψ).subtype)
  have hzc : ∀ g, g * z = z * g := Subgroup.mem_center_iff.1 (hcen hzk)
  have hz1' : f z ≠ 1 := by
    intro h
    apply hz1
    have h2' : (z : ↥L × spinGroup (quadOdd 3 K)).2 = 1 := MonoidHom.mem_ker.1 hzk
    have h1' : (z : ↥L × spinGroup (quadOdd 3 K)).1 = 1 := Subtype.ext h
    exact Subtype.ext (Prod.ext h1' h2')
  have hmapz : ∀ g : pullback φ ψ, g ∈ Subgroup.zpowers a → f g ∈ Subgroup.zpowers (f a) :=
    fun g hg => by
      have := Subgroup.mem_map_of_mem f hg
      rwa [MonoidHom.map_zpowers] at this
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have key := two_pow_le_card_of_relHeis (W := W) (p := 3) hW (by norm_num) (n := 2)
    (x₀ := f a) (y₀ := f b) (z := f z)
    ⟨by rw [← map_pow, ha3, map_one], by rw [← map_pow, hz3, map_one],
      by rw [← map_mul, ← map_mul, hzc a], by rw [← map_mul, ← map_mul, hzc b],
      by rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, hb], hz1'⟩
    (x := fun i => f (x i)) (y := fun i => f (y i))
    (fun i => by rw [← map_mul, ← map_mul, hxa i])
    (fun i => by rw [← map_mul, ← map_mul, hya i])
    (fun i => by rw [← map_mul, ← map_mul, hzc (x i)])
    (fun i => by rw [← map_mul, ← map_mul, hzc (y i)])
    (fun i => by rw [← map_pow, hx3 i, map_one])
    (fun i => by rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, hyx i])
    (fun i j => by simpa only [map_mul, map_inv] using hmapz _ (hxx i j))
    (fun i j hij => by simpa only [map_mul, map_inv] using hmapz _ (hyy i j hij))
    (fun i j hij => by simpa only [map_mul, map_inv] using hmapz _ (hxy i j hij))
  rw [hord] at key
  norm_num at key
  exact key


open TauCeti CFSG.HardMathSupport.Cooperstein.Coordinator CFSG.ClassicalGroups.Orthogonal

theorem lt_of_omega73_of_center_three {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)} (hq : CFSG.IsQuasisimple ↥L)
    (hirr : CFSG.QuasithinUnique.Setup.X1.IsIrrOn L)
    (hEN : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hE : E ≠ ⊥)
    (hel : IsElemAbelian2 E) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    (hZ : Nat.card (Subgroup.center ↥L) = 3)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedOmega (StatedQuadOdd 3 K))) :
    Nat.card E * Nat.card (fixV E) < Nat.card W := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK' : Nat.card K = 3 ^ 1 := by rw [hK]; norm_num
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 3 := charP_of_card_eq_prime_pow (f := 1) (by
    rw [← Nat.card_eq_fintype_card]; exact hK')
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_card Nat.prime_three (by norm_num) hK'
  have h54 := two_pow_54_le_of_omega73_center_three hW hq.1 hK hZ θ
  have hM : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadOdd 3 K))) .POmegaOdd 3 3 1 :=
    ⟨⟨Nat.prime_three, le_rfl, le_rfl, by norm_num⟩, K, inferInstance, inferInstance, hK',
      ⟨MulEquiv.refl _⟩⟩
  have hout := card_outer_le_of_orthogonal _ .POmegaOdd (.inl rfl) 3 3 1 (by norm_num) hM
  have hS := (card_statedProj_statedOmega_le (coe_quadOdd 3 K)).trans
    (card_orthogonalGroup_quadOdd_le h2 3)
  rw [hK] at hS
  refine FFToolkit.exclusion_of_card_lt_of_outer hW hq hirr hEN hE hel θ (k := 24)
    (fun B _ _ => (card_le_card_outer_mul_card_inf B).trans (Nat.mul_le_mul_right _ hout)) ?_
  rw [hZ]
  calc 24 * (3 * Nat.card (StatedProj (StatedOmega (StatedQuadOdd 3 K))))
      ≤ 24 * (3 * (2 * 3 ^ (3 * (2 * 3 + 1)))) := by gcongr
    _ < 2 ^ 54 := by norm_num
    _ ≤ Nat.card W := h54

section Cell


theorem noIrrFFOffender_smallOmega73 {q : PrimePower} (hv : (LieTypeIndex.B 3 q).Valid)
    (h3 : q.card = 3) : NoIrrFFOffender (CFSGIndex.lie ⟨.B 3 q, hv⟩).Group := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hEN hE hel _
  have hp : q.p.Prime := q.prime_p
  have hcard : q.card = q.p ^ q.exponent := PrimePower.card_def q
  have hp3 : q.p = 3 := by
    have h1 : q.p ∣ 3 := by
      rw [← h3, hcard]; exact dvd_pow_self _ q.exponent_pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h1
  have hp2 : q.p ≠ 2 := by rw [hp3]; norm_num
  obtain ⟨hdvd, K, _, _, hK, ⟨θ⟩⟩ :=
    exists_pomega_model_of_lie_B3_three hq.1 (FFToolkit.odd_card_center_of_isIrrOn hW hirr) hv hp2
      h3 e
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3'
  · have hbot : Subgroup.center ↥L = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    exact lt_of_omega73_of_center_bot hW hq hirr hEN hE hel hK hbot
      ((QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hbot.symm)).trans θ)
  · exact lt_of_omega73_of_center_three hW hq hirr hEN hE hel hK h3' θ

theorem smallOmega73 : SmallOmega73 := by
  intro d q hq hd
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  exact noFFModule_of_noIrrFFOffender (noIrrFFOffender_smallOmega73 hv hq)

end Cell

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
