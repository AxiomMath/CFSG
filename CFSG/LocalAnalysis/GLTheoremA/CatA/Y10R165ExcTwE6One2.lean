module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6One
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwistedTorus
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwE6ThreeSC
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwE6ThreeHolds
public import CFSG.HardMathSupport.Lang.AnisoE6.PlaneConjGen
public import CFSG.GroupTheory.PGroup.ElemAbelianSq

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6One

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.TwistedE6 CFSG.SeitzReduction CFSG.StandardType
  CFSG.HardMathSupport.Lang.AnisoE6 CFSG.LieType.SeitzGeneration
  CFSG.LieType.Steinberg.Exceptional CFSG.RankThree.PartTwo.Census.Exceptional

noncomputable def thetaTorusP {f : ℕ} {k : Type} [Field k]
    [Algebra k (GaloisField 2 (2 * f))] (t : kˣ) : Subgroup (C0 f) :=
  (Subgroup.zpowers (E6GraphLevi.thetaTorusHom (GaloisField 2 (2 * f))
    (Units.map (algebraMap k (GaloisField 2 (2 * f))).toMonoidHom t))).subgroupOf (C0 f)

variable {f : ℕ} {k : Type} [Field k] [Algebra k (GaloisField 2 (2 * f))]

private theorem card_galoisField_two_mul' (hf : 1 ≤ f) :
    Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
  rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]

private theorem thetaTorusHom_mem_C0 [Finite k] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (t : kˣ) :
    E6GraphLevi.thetaTorusHom (GaloisField 2 (2 * f))
        (Units.map (algebraMap k (GaloisField 2 (2 * f))).toMonoidHom t) ∈ C0 f :=
  TwistedE6Pilot.thetaTorus_le_C0 hf hk (card_galoisField_two_mul' hf)
    (fun c => frobQ_apply 2 f c) ⟨t, rfl⟩

theorem thetaTorusP_le_thetaTorus (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f) (t : kˣ) :
    thetaTorusP (f := f) t ≤ (W0 f k).subgroupOf (C0 f) := by
  rintro x hx
  have hx' : (x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈
      Subgroup.zpowers (E6GraphLevi.thetaTorusHom (GaloisField 2 (2 * f))
        (Units.map (algebraMap k (GaloisField 2 (2 * f))).toMonoidHom t)) := hx
  exact Subgroup.zpowers_le.2
    ((E6GraphLevi.mem_thetaTorus (algebraMap k (GaloisField 2 (2 * f)))).2
      ⟨t, (E6GraphLevi.thetaTorusHom_apply _).symm⟩) hx'

theorem card_thetaTorusP [Finite k] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f) {t : kˣ} {p : ℕ}
    (ht : orderOf t = p) :
    Nat.card (thetaTorusP (f := f) t) = p := by
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := card_galoisField_two_mul' hf
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : GaloisField 2 (2 * f)) = 0 := CharP.cast_eq_zero _ 2
  have hinj : Function.Injective (E6GraphLevi.thetaTorusHom (GaloisField 2 (2 * f))) :=
    E6GraphLevi.thetaTorusHom_injective h2
  have hle : Subgroup.zpowers (E6GraphLevi.thetaTorusHom (GaloisField 2 (2 * f))
      (Units.map (algebraMap k (GaloisField 2 (2 * f))).toMonoidHom t)) ≤ C0 f :=
    Subgroup.zpowers_le.2 (thetaTorusHom_mem_C0 hf hk t)
  rw [thetaTorusP, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    Nat.card_zpowers]
  rw [orderOf_injective (E6GraphLevi.thetaTorusHom (GaloisField 2 (2 * f))) hinj,
    orderOf_injective (Units.map (algebraMap k (GaloisField 2 (2 * f))).toMonoidHom)
      (Units.map_injective (algebraMap k (GaloisField 2 (2 * f))).injective) t, ht]

theorem isElemAbelian_thetaTorusP [Finite k] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f) {t : kˣ} {p : ℕ}
    (hp : p.Prime) (ht : orderOf t = p) :
    IsElemAbelian p (thetaTorusP (f := f) t) := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact CFSG.GroupTheory.isElemAbelian_of_card_prime (card_thetaTorusP hf hk ht)

theorem thetaTorusP_inf_DLevi_eq_bot (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f) (t : kˣ) :
    thetaTorusP (f := f) t ⊓ (DLevi f).subgroupOf (C0 f) = ⊥ := by
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := card_galoisField_two_mul' hf
  have hσ : ∀ c, frobQ 2 f c = c ^ 2 ^ f := fun c => frobQ_apply 2 f c
  have hdisj := (TwistedE6Pilot.su6Levi_facts hf hk hK hσ).2.2.1
  have hle := thetaTorusP_le_thetaTorus hf hk t
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxW, hxD⟩ := Subgroup.mem_inf.1 hx
  have hxW' : (x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈ W0 f k := hle hxW
  have hxD' : (x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈ DLevi f := hxD
  have hmem : (x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈ W0 f k ⊓ DLevi f :=
    Subgroup.mem_inf.2 ⟨hxW', hxD'⟩
  rw [inf_comm, hdisj] at hmem
  exact Subgroup.mem_bot.2 (Subtype.ext (Subgroup.mem_bot.1 hmem))

theorem exists_conj_eq_threeFrame_of_sc (hf : 1 ≤ f) (h3 : ¬ 3 ∣ 2 ^ f + 1)
    {ζ : (GaloisField 2 (2 * f))ˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {A : Subgroup (C0 f)} (hA : IsElemAbelian 3 A) (hA4 : 3 ^ 4 ≤ Nat.card A)
    (hASC : ∀ c ∈ Subgroup.centralizer (A : Set (C0 f)), c ^ 3 = 1 → c ∈ A) :
    ∃ c : C0 f, A = (ExcFrames.twE6ThreeFrameHom hf h3 ζ hζ).range.map
      (MulAut.conj c).toMonoidHom :=
  ExcFrames.twistedE6ThreeSCReference_holds hf h3 hζo hζ hA hA4 hASC

private theorem frobQ_bijective (hf : 1 ≤ f) :
    Function.Bijective (frobQ 2 f : GaloisField 2 (2 * f) →+* GaloisField 2 (2 * f)) := by
  have hright : ∀ c, frobQ 2 f (frobQ 2 f c) = c := fun c => frobQ_frobQ 2 f hf c
  refine ⟨fun a b h => ?_, fun c => ⟨frobQ 2 f c, hright c⟩⟩
  have := congrArg (frobQ 2 f) h
  simpa [hright] using this

theorem sylowTorus_C0 (hf : 1 ≤ f) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (he : orderOf (((2 ^ f : ℕ)) : ZMod p) = 1) :
    SylowTorus (↥(C0 f)) p 4 := by
  let σ : GaloisField 2 (2 * f) ≃+* GaloisField 2 (2 * f) :=
    RingEquiv.ofBijective (frobQ 2 f) (frobQ_bijective hf)
  have hσ : ∀ c, σ c = c ^ 2 ^ f := fun c => frobQ_apply 2 f c
  have h := ExcFrames.sylowTorus_twistedE6_one (ℓ := 2) Nat.prime_two hf
    (GaloisField 2 (2 * f)) (card_galoisField_two_mul' hf) σ hσ hp hp5
    (by
      intro hd
      have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow hd
      have hp_eq : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2
      omega) he
  exact h

theorem exists_conj_eq_of_card_eq (hf : 1 ≤ f) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (he : orderOf (((2 ^ f : ℕ)) : ZMod p) = 1)
    {A A₀ : Subgroup (C0 f)} (hA : IsElemAbelian p A) (hAc : Nat.card A = p ^ 4)
    (hA₀ : IsElemAbelian p A₀) (hA₀c : Nat.card A₀ = p ^ 4) :
    ∃ g : C0 f, A.map (MulAut.conj g).toMonoidHom = A₀ := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact exists_conj_eq_of_sylowTorus (sylowTorus_C0 hf hp hp5 he) hA hAc hA₀ hA₀c

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6One
