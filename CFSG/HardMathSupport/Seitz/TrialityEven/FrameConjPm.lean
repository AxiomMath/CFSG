module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4PlaneLeaf
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4TorusLang
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartOne.KGD.D4T36Frame

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Seitz.TrialityEven

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD CFSG.GH74.GLS.Stage2.Bender.Thm1


theorem exists_conj_into_frame_torus_pm {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpd : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * ((ℓ ^ f : ℕ) : ℤ) + 1)
    (F : D4PhiFrame K σ (ℓ ^ f) ε)
    (Q : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hQ : IsPGroup p Q) :
    ∃ c : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, ∀ y ∈ Q,
      F.g0⁻¹ * triEmb K σ (AlgebraicClosure K) (c * y * c⁻¹) * F.g0 ∈
        twistedTorusOf F.n (twistHom TwistTag.D4 (AlgebraicClosure K) F.Fr) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  have : CharP K ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ (by omega : 1 ≤ f * 3) (by rw [hK, ← pow_mul])
  let L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨n₁, hn₁, w₁, hnw₁, hw₁, g₁, hg₁C, hg₁, hperf₁, hconj₁⟩ :=
    d4T36_frame hf K hK σ hσ hε hp hp3 hpd L
  have hFr : F.Fr = iterateFrobenius L ℓ f :=
    RingHom.ext fun c => by rw [F.hFr, iterateFrobenius_def]
  obtain ⟨c₁, hc₁⟩ := hconj₁ Q hQ
  have hWeq : weylQuotientHom TwistTag.D4.tag L ⟨n₁, hn₁⟩ =
      weylQuotientHom TwistTag.D4.tag L ⟨F.n, F.hn⟩ := by
    rw [hnw₁, F.hnw]
    exact ext_single fun i => (hw₁ _).trans (F.hw _).symm
  set t := n₁ * F.n⁻¹ with ht
  have htM : t ∈ monomialSubgroup TwistTag.D4.tag L := mul_mem hn₁ (inv_mem F.hn)
  have htT : t ∈ torusGroup TwistTag.D4.tag L := by
    refine mem_torusGroup_of_mapsRootLines_one htM ?_
    have h1 : weylQuotientHom TwistTag.D4.tag L ⟨t, htM⟩ = 1 := by
      have e : (⟨t, htM⟩ : monomialSubgroup TwistTag.D4.tag L) =
          ⟨n₁, hn₁⟩ * (⟨F.n, F.hn⟩)⁻¹ := rfl
      rw [e, map_mul, map_inv, hWeq, mul_inv_cancel]
    have := mapsRootLines_weylQuotientHom (τ := TwistTag.D4.tag) (R := L) ⟨t, htM⟩
    rwa [h1] at this
  obtain ⟨s, hsT, hs⟩ := d4_torus_adjust F.Fr F.hFr F.hn (d4T36M ε)
    (fun x => by rw [F.hnw]; exact F.hw x) (d4T36M_sub_det_ne_zero hε hq1) htT
  set Fh := twistHom TwistTag.D4 L F.Fr with hFh
  set c' := F.g0 * s * g₁⁻¹ with hc'
  have hsA : s ∈ adjointGroup TwistTag.D4.tag L := torusGroup_le_adjointGroup' hsT
  have hc'A : c' ∈ adjointGroup TwistTag.D4.tag L :=
    mul_mem (mul_mem F.hg0C hsA) (inv_mem hg₁C)
  have hg₁' : Fh g₁ = g₁ * n₁ := by rw [hFh, hFr]; exact hg₁
  have hFc' : Fh c' = c' := by
    rw [hc', map_mul, map_mul, map_inv, F.hg0, hg₁']
    have e : F.n * Fh s * n₁⁻¹ = s := by
      have h2 : F.n * Fh s * F.n⁻¹ = s * t := hs
      calc F.n * Fh s * n₁⁻¹ = (F.n * Fh s * F.n⁻¹) * (F.n * n₁⁻¹) := by group
        _ = (s * t) * (F.n * n₁⁻¹) := by rw [h2]
        _ = s := by rw [ht]; group
    calc F.g0 * F.n * Fh s * (g₁ * n₁)⁻¹ = F.g0 * (F.n * Fh s * n₁⁻¹) * g₁⁻¹ := by group
      _ = F.g0 * s * g₁⁻¹ := by rw [e]
  have hrange := F.hperf (Subgroup.zpowers c') (by
      rw [Subgroup.zpowers_le]; exact hc'A) (by
      rintro x ⟨k, rfl⟩
      rw [map_zpow, hFc'])
  obtain ⟨c₀, hc₀⟩ := hrange (Subgroup.mem_zpowers c')
  refine ⟨c₀ * c₁, fun y hy => ?_⟩
  have hX := hc₁ y hy
  rw [mem_twistedTorusOf] at hX ⊢
  obtain ⟨hXT, hXn⟩ := hX
  have hconjeq : F.g0⁻¹ * triEmb K σ L (c₀ * c₁ * y * (c₀ * c₁)⁻¹) * F.g0 =
      s * (g₁⁻¹ * triEmb K σ L (c₁ * y * c₁⁻¹) * g₁) * s⁻¹ := by
    have e1 : c₀ * c₁ * y * (c₀ * c₁)⁻¹ = c₀ * (c₁ * y * c₁⁻¹) * c₀⁻¹ := by group
    rw [e1, map_mul, map_mul, map_inv, hc₀, hc']
    group
  rw [hconjeq]
  refine ⟨mul_mem (mul_mem hsT hXT) (inv_mem hsT), ?_⟩
  set x := g₁⁻¹ * triEmb K σ L (c₁ * y * c₁⁻¹) * g₁ with hx
  have hxn : n₁ * Fh x * n₁⁻¹ = x := by rw [hFh, hFr]; exact hXn
  have htc : t * x = x * t := torusGroup_comm htT hXT
  have hn₁eq : n₁ = t * F.n := by rw [ht]; group
  have hxF : F.n * Fh x * F.n⁻¹ = x := by
    have : F.n * Fh x * F.n⁻¹ = t⁻¹ * (n₁ * Fh x * n₁⁻¹) * t := by
      rw [hn₁eq]; group
    rw [this, hxn]
    have : t⁻¹ * x * t = x := by
      calc t⁻¹ * x * t = t⁻¹ * (x * t) := by group
        _ = t⁻¹ * (t * x) := by rw [htc]
        _ = x := by group
    exact this
  have hs2 : F.n * Fh s * F.n⁻¹ = s * t := hs
  have hs3 : F.n * Fh s⁻¹ * F.n⁻¹ = (s * t)⁻¹ := by
    rw [map_inv, ← hs2]; group
  calc F.n * Fh (s * x * s⁻¹) * F.n⁻¹
      = (F.n * Fh s * F.n⁻¹) * (F.n * Fh x * F.n⁻¹) * (F.n * Fh s⁻¹ * F.n⁻¹) := by
        rw [map_mul, map_mul]; group
    _ = (s * t) * x * (s * t)⁻¹ := by rw [hs2, hxF, hs3]
    _ = s * (t * x * t⁻¹) * s⁻¹ := by group
    _ = s * x * s⁻¹ := by rw [htc]; group

end CFSG.HardMathSupport.Seitz.TrialityEven
