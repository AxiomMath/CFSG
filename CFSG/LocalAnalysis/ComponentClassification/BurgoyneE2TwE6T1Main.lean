module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6T1Def
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE6T1Row
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2Outer

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ToralSign CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

namespace TwE6T1

theorem map_pow_apply_eq_conj {T G : Type*} [Group T] [Group G] {Ψ : T →* G} {β : MulAut T}
    {z : G} (h : ∀ s, Ψ (β s) = z * Ψ s * z⁻¹) (n : ℕ) (s : T) :
    Ψ ((β ^ n) s) = z ^ n * Ψ s * (z ^ n)⁻¹ := by
  induction n generalizing s with
  | zero => rw [pow_zero, pow_zero, MulAut.one_apply, one_mul, inv_one, mul_one]
  | succ n ih =>
    rw [pow_succ β, MulAut.mul_apply, ih, h]
    group

theorem pow_succ_eq_one_of_mem_t1R
    {p f : ℕ} [Fact p.Prime] {L : Type} [Field L] [CharP L p] {c : Fin TwistTag.E6.tag.rank → Lˣ}
    (h24 : c (t1Node 2) * c (t1Node 4) = 1)
    (hcR : rootDiagUnit TwistTag.E6.tag c ∈ fixedPointsIn (adjointGroup TwistTag.E6.tag L)
        (frobTwistGL TwistTag.E6.tag L p f (diagramMap TwistTag.E6 L))) :
    c (t1Node 2) ^ (p ^ f + 1) = 1 := by
  have h := (mem_fixedPointsIn.1 hcR).2
  rw [frobTwistGL_apply, entrywiseFrobGL_rootDiagUnit_eq_map, diagramMap_mul_rootDiagUnit,
    mul_inv_cancel_right] at h
  have h4 : Units.map (iterateFrobenius L p f).toMonoidHom
      (c (TwistTag.E6.perm.symm (t1Node 4))) = c (t1Node 4) :=
    congrFun (rootDiagUnit_injective h) (t1Node 4)
  have hs : TwistTag.E6.perm.symm (t1Node 4) = t1Node 2 := by decide
  have hq : c (t1Node 2) ^ (p ^ f) = c (t1Node 4) := by
    rw [← h4, hs]
    ext
    simp
  rw [pow_succ, hq, mul_comm, h24]

end TwE6T1


namespace TwE6T1

variable {p f : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K] {L : Type} [Field L]
  [Algebra K L] [IsAlgClosure K L] [CharP L p]

theorem burgCoreFor_t1_three (hp2 : p ≠ 2) (hf : 1 ≤ f) (h3 : p ^ f = 3)
    (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (t : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) {g₀ : ModGL TwistTag.E6.tag L}
    (hg₀G : g₀ ∈ adjointGroup TwistTag.E6.tag L)
    (hg₀F : frobTwistGL TwistTag.E6.tag L p f (diagramMap TwistTag.E6 L) g₀ = g₀)
    (hg₀t : g₀ * baseChangeGL (algebraMap K L) (t : ModGL TwistTag.E6.tag K) * g₀⁻¹ =
      rootDiagUnit TwistTag.E6.tag (signCharTuple (k := L) (signMaskChar TwistTag.E6.tag 20))) :
    BurgCoreFor (MulAut.conj t) := by
  classical
  set R := fixedPointsIn (adjointGroup TwistTag.E6.tag L)
        (frobTwistGL TwistTag.E6.tag L p f (diagramMap TwistTag.E6 L)) with hR
  set ι := baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K L) with hι
  set d := rootDiagUnit TwistTag.E6.tag
    (signCharTuple (k := L) (signMaskChar TwistTag.E6.tag 20)) with hd
  have hg₀R : g₀ ∈ R := mem_fixedPointsIn.2 ⟨hg₀G, hg₀F⟩
  have hRR : ⁅R, R⁆ ≤ R := Subgroup.commutator_le_of_le le_rfl le_rfl
  have hιR : ∀ s : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      ι (s : ModGL TwistTag.E6.tag K) ∈ R := fun s => hRR ((t1_preimage hp2 hf hK σ hσ
        (one_mem R)).2 ⟨s, by rw [one_mul, inv_one, mul_one]⟩)
  set Ψ : graphFixedRootGroup TwistTag.E6 K σ.toRingHom →* ModGL TwistTag.E6.tag L :=
    (MulAut.conj g₀).toMonoidHom.comp
      (ι.comp (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype) with hΨ
  have hΨinj : Function.Injective Ψ :=
    (MulAut.conj g₀).injective.comp ((baseChangeGL_injective _).comp Subtype.val_injective)
  have hΨapp : ∀ s, Ψ s = g₀ * ι (s : ModGL TwistTag.E6.tag K) * g₀⁻¹ := fun s => rfl
  have hΨt : Ψ t = d := hg₀t
  have hΨR : ∀ s, Ψ s ∈ R := fun s => mul_mem (mul_mem hg₀R (hιR s)) (inv_mem hg₀R)
  have hcomm : ∀ s, Ψ s * d = d * Ψ s ↔ s * t = t * s := fun s => by
    rw [← hΨt, ← map_mul, ← map_mul]
    exact hΨinj.eq_iff
  have hfixt : ∀ s, s ∈ fixedSubgroup (MulAut.conj t) ↔ s * t = t * s := fun s => by
    change t * s * t⁻¹ = s ↔ _
    constructor
    · intro h
      calc s * t = t * s * t⁻¹ * t := by rw [h]
        _ = t * s := by group
    · intro h
      rw [← h]
      group
  obtain ⟨CA, hqCA, hCAH, hCAn, hCAind⟩ := exists_t1_layer hp2 hf hK σ hσ hg₀R
  have hCAΨ : CA ≤ Ψ.range := fun y hy => by
    obtain ⟨s, hs⟩ := (t1_preimage hp2 hf hK σ hσ hg₀R).1 (Subgroup.mem_inf.1 (hCAH hy)).1
    exact ⟨s, hs⟩
  let eJ : CA.comap Ψ ≃* CA := ((CA.comap Ψ).equivMapOfInjective Ψ hΨinj).trans
    (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hCAΨ))
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have : Finite (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := Subtype.finite
  refine burgCoreFor_of_normal_quasisimple (exceptional_fixed_center_trivial TwistTag.E6 K σ)
    (J := CA.comap Ψ) (fun s hs => ?_) (fun g hg j hj => ?_)
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv eJ.symm hqCA) fun β hβ hβJ => ?_
  ·
    have hs' : Ψ s ∈ CA := hs
    exact (hfixt s).2 ((hcomm s).1
      (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hCAH hs')).2))
  ·
    have hj' : Ψ j ∈ CA := hj
    have hgd : Ψ g ∈ R ⊓ Subgroup.centralizer {d} :=
      Subgroup.mem_inf.2 ⟨hΨR g, Subgroup.mem_centralizer_singleton_iff.2
        ((hcomm g).2 ((hfixt g).1 hg))⟩
    change Ψ (g * j * g⁻¹) ∈ CA
    rw [map_mul, map_mul, map_inv]
    exact hCAn _ hgd _ hj'
  ·
    obtain ⟨c, h0, h1, h3', h5, h24, hcR, hcβ⟩ := hCAind β hβ fun s hs => hβJ s hs
    have hcβ' : ∀ s, Ψ (β s) = rootDiagUnit TwistTag.E6.tag c * Ψ s *
        (rootDiagUnit TwistTag.E6.tag c)⁻¹ := fun s => by
      rw [hΨapp, hΨapp]
      exact hcβ s
    have hc2 : c (t1Node 2) ^ 4 = 1 := by
      have h := pow_succ_eq_one_of_mem_t1R h24 hcR
      rwa [h3] at h
    have hc4 : c (t1Node 4) ^ 4 = 1 := by
      rw [eq_inv_of_mul_eq_one_right h24, inv_pow, hc2, inv_one]
    have e1 : ∀ x : Lˣ, x = 1 → x ^ 4 = 1 := fun x hx => by rw [hx, one_pow]
    have hc : c ^ 4 = 1 := by
      funext i
      obtain ⟨j, rfl⟩ : ∃ j : Fin 6, t1Node j = i := ⟨i, rfl⟩
      rw [Pi.pow_apply, Pi.one_apply]
      fin_cases j
      · exact e1 _ h0
      · exact e1 _ h1
      · exact hc2
      · exact e1 _ h3'
      · exact hc4
      · exact e1 _ h5
    have hd4 : rootDiagUnit TwistTag.E6.tag c ^ 4 = 1 := by
      rw [rootDiagUnit_pow, hc, rootDiagUnit_one]
    have hβ4 : β ^ 4 = 1 := MulEquiv.ext fun s => hΨinj (by
      rw [map_pow_apply_eq_conj hcβ' 4 s, hd4, one_mul, inv_one, mul_one, MulAut.one_apply])
    have hco : Nat.Coprime (orderOf β) (2 ^ 2) :=
      Nat.Coprime.pow_right 2 (Nat.coprime_two_right.2 hβ)
    exact orderOf_eq_one_iff.1 (hco.eq_one_of_dvd (orderOf_dvd_of_pow_eq_one hβ4))

end TwE6T1

theorem burgoyneE2TwistedE6T1Input_holds : BurgoyneE2TwistedE6T1Input := by
  rintro p f _ hp2 hf K _ _ hK σ hσ t - L _ _ _ _ ⟨g₁, hg₁G, hg₁F, hg₁t⟩
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
    have := hp.two_le
    omega
  have h3 : 3 ≤ p ^ f := hp3.trans (by
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf)
  obtain ⟨m, hm⟩ : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have h35 : p ^ f = 3 ∨ 5 ≤ p ^ f := by
    generalize p ^ f = q at hm h3 ⊢
    omega
  rcases h35 with h | h
  · exact Or.inl (TwE6T1.burgCoreFor_t1_three hp2 hf h hK σ hσ t hg₁G hg₁F hg₁t)
  · exact Or.inr (TwE6T1.burgTorusFor_t1 hp2 hf h hK σ hσ t hg₁G hg₁F hg₁t)

end CFSG.ComponentClassification.Burgoyne.E2
