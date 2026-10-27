module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021LayerCore
public import TauCeti.GroupTheory.QuotientGroup.MulAut
import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021FixMax
import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021RankHolds
import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021TD4Quot
import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021TD4Lift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T2021

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.I2015

section Certs

theorem t2021LayerFact_holds : T2021LayerFact := by
  intro H _ _ p 𝔅 _ _ ψ T a b₁ hp hp2 hchev hD4 hexp hcomm hT2 hTinv hrank hF hID _ _ ht
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set N := GLAPPrimeCore p H with hN
  let ψQ : 𝔅 →* MulAut (ppQuot p H) := (MulAut.mapQuotient N).comp ψ
  have hψQ : ∀ (g : 𝔅) (l : H), ψQ g (QuotientGroup.mk l) = QuotientGroup.mk (ψ g l) :=
    fun g l => MulAut.mapQuotient_mk N (ψ g) l
  set Z := Subgroup.center (ppQuot p H) with hZ
  let ψS : 𝔅 →* MulAut (psimpleOf p H) := (MulAut.mapQuotient Z).comp ψQ
  have hψS : ∀ (g : 𝔅) (x : ppQuot p H), ψS g (QuotientGroup.mk x) = QuotientGroup.mk (ψQ g x) :=
    fun g x => MulAut.mapQuotient_mk Z (ψQ g) x
  have hcongr : ∀ (g : 𝔅) {R : Type} [Group R] (θ : psimpleOf p H ≃* R),
      MulAut.congr θ (ψS g) = autR p θ (ψ g) := by
    intro g R _ θ
    refine MulEquiv.ext fun r => ?_
    obtain ⟨s, rfl⟩ := θ.surjective r
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective s
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    rw [autR_apply_mk]
    show θ (ψS g (θ.symm (θ (QuotientGroup.mk (QuotientGroup.mk l))))) = _
    rw [MulEquiv.symm_apply_apply, hψS, hψQ]
  have hF' : GLAMarking (ppQuot p H) fun lab _ _ I F θ =>
      GLAPrimeField p lab I F (GLAInduces θ (relOfAut p (ψ a))) := by
    rcases hF with hM | ⟨h3, hT4, -⟩
    · exact hM
    · exact absurd ⟨h3, h3 ▸ hT4⟩ hD4
  have ha : GLAMarking (ppQuot p H) fun lab _ _ I F θ =>
      GLAPrimeField p lab I F (· = MulAut.congr θ (ψS a)) := by
    refine CFSG.StandardType.Canonical.largeEvenMarking_mono ?_ hF'
    rintro lab R _ I F θ ⟨hne, f, hf, u, hu, hord, hind⟩
    exact ⟨hne, f, hf, u, hu, hord, ((induces_iff θ (ψ a) _).1 hind).trans (hcongr a θ).symm⟩
  have hb : GLAMarking (ppQuot p H) fun _ _ _ I _ θ => MulAut.congr θ (ψS b₁) ∈ I := by
    refine CFSG.StandardType.Canonical.largeEvenMarking_mono ?_ hID
    rintro lab R _ I F θ ⟨u, hu, hind⟩
    rw [hcongr b₁ θ, ← (induces_iff θ (ψ b₁) u).1 hind]
    exact hu
  have hperf : commutator (ppQuot p H) = ⊤ := hF'.1
  have hZodd : Odd (Nat.card Z) := t2021Fix_odd_center hp hp2
  have htriv : ∀ g : 𝔅, TrivAut p H (ψ g) ↔ ψS g = 1 := by
    intro g
    refine ⟨fun h => ?_, fun h => t2021Fix_trivAut hperf (ψ g) (ψQ g) (hψQ g) h⟩
    have hQ1 : ψQ g = 1 := (trivAut_iff (ψ g)).1 h
    show MulAut.mapQuotient Z (ψQ g) = 1
    rw [hQ1, map_one]
  have hrank' : p ^ 3 * Nat.card {g : 𝔅 // ψS g = 1} ≤ Nat.card 𝔅 := by
    have : Nat.card {g : 𝔅 // TrivAut p H (ψ g)} = Nat.card {g : 𝔅 // ψS g = 1} :=
      Nat.card_congr (Equiv.subtypeEquivRight htriv)
    rwa [this] at hrank
  set Tb : Subgroup (psimpleOf p H) := (T.map (QuotientGroup.mk' N)).map (QuotientGroup.mk' Z)
    with hTb
  have hTb2 : IsPGroup 2 Tb := (hT2.map _).map _
  have hTbinv : ∀ g : 𝔅, ∀ x ∈ Tb, ψS g x ∈ Tb := by
    rintro g _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    refine ⟨_, ⟨ψ g s, hTinv g s hs, rfl⟩, ?_⟩
    simp only [QuotientGroup.mk'_apply]
    rw [hψS, hψQ]
  obtain ⟨t, htT, hta, htb⟩ := ht
  have htbT : (QuotientGroup.mk (QuotientGroup.mk t : ppQuot p H) : psimpleOf p H) ∈ Tb :=
    ⟨_, ⟨t, htT, rfl⟩, rfl⟩
  have htba : ψS a (QuotientGroup.mk (QuotientGroup.mk t : ppQuot p H)) =
      QuotientGroup.mk (QuotientGroup.mk t : ppQuot p H) := by
    rw [hψS, hψQ]
    congr 1
    exact QuotientGroup.eq_iff_div_mem.2 (by rw [div_eq_mul_inv]; exact hta)
  have htbb : ψS b₁ (QuotientGroup.mk (QuotientGroup.mk t : ppQuot p H)) ≠
      QuotientGroup.mk (QuotientGroup.mk t : ppQuot p H) := by
    intro h
    rw [hψS, hψQ] at h
    apply htb
    set c := ψ b₁ t * t⁻¹ with hc
    have hcT : c ∈ T := T.mul_mem (hTinv b₁ t htT) (T.inv_mem htT)
    have hcZ : (QuotientGroup.mk c : ppQuot p H) ∈ Z := by
      have h1 := QuotientGroup.eq_iff_div_mem.1 h
      rwa [div_eq_mul_inv, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul] at h1
    obtain ⟨k, hk⟩ := hT2 ⟨c, hcT⟩
    have hk' : (QuotientGroup.mk c : ppQuot p H) ^ 2 ^ k = 1 := by
      have := congrArg (fun x : T => (QuotientGroup.mk (x : H) : ppQuot p H)) hk
      simpa using this
    have hord : orderOf (⟨_, hcZ⟩ : Z) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (Subtype.ext hk')
    have hodd : Odd (orderOf (⟨_, hcZ⟩ : Z)) := hZodd.of_dvd_nat (orderOf_dvd_natCard _)
    have h1 : orderOf (⟨_, hcZ⟩ : Z) = 1 := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · rw [hj, h0, pow_zero]
      · exfalso
        rw [hj] at hodd
        exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_pow.2 ⟨even_two, h0.ne'⟩)
    have h2 : (QuotientGroup.mk c : ppQuot p H) = 1 :=
      congrArg Subtype.val (orderOf_eq_one_iff.1 h1)
    exact (QuotientGroup.eq_one_iff c).1 h2
  have hD4' : ¬ (p = 3 ∧ catalogIs (ppQuot p H ⧸ Subgroup.center (ppQuot p H))
      (onLie fun | .trialityD4 _ => True | _ => False)) := by
    rintro ⟨h3, hc⟩
    subst h3
    exact hD4 ⟨rfl, hc⟩
  obtain ⟨Kb, Ub, hKfix, hKn, hKinv, hKs, hKnab, hK3, hUK, hU2, hU1, hUinv⟩ :=
    t2021Layer_core hp hp2 ψS hexp hcomm hchev hD4' hrank' ha hb hTb2 hTbinv htbT htba htbb
  obtain ⟨K, U, hK, hKq, hKZ, hK3', hUK', hU2', hU1', hUinv'⟩ :=
    t2021TD4_quot hp ψQ a hZodd hKfix hKn hKinv hKs hKnab hK3 hUK hU2 hU1 hUinv
  exact t2021TD4_lift hp hp2 ψ ψQ hψQ a hexp hcomm hK hKq hKZ hK3' hUK' hU2' hU1' hUinv'

end Certs

end CFSG.LocalAnalysis.GLTheoremA.T2021

end

