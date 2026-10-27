module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Three13

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE6
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.E6 (weylMatrix weylMatrix_mulVec)

open scoped Matrix MatrixGroups

section Certs


variable {K : Type} [Field K] [Finite K] {ℓ f p : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]

theorem concl165_of_e8T3_model (hE6 : E6Layer Tag.E8) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1)
    (hq2 : ε = -1 → 2 < ℓ ^ f)
    (n : ModGL Tag.E8 L) (hnm : n ∈ monomialSubgroup Tag.E8 L)
    (hnW : weylQuotientHom Tag.E8 L ⟨n, hnm⟩ = e8T3We ε)
    (g0 : ModGL Tag.E8 L) (hg0C : g0 ∈ adjointGroup Tag.E8 L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL Tag.E8 L), Finite P → P ≤ adjointGroup Tag.E8 L →
      (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb Tag.E8 K L).range)
    (hconj : ∀ Q : Subgroup (adjointGroup Tag.E8 K), IsPGroup p Q →
      ∃ c : adjointGroup Tag.E8 K, ∀ y ∈ Q,
        c * y * c⁻¹ ∈ subtorusImage (adjEmb Tag.E8 K L) g0
          (twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))))
    {A : Subgroup (adjointGroup Tag.E8 K)} (hAe : IsElemAbelian p A)
    (hΩ : ∀ g ∈ Subgroup.centralizer (A : Set (adjointGroup Tag.E8 K)),
      orderOf g = p → g ∈ A)
    {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p)
    {q : ℕ} (hq : q.Prime) (hq2' : q ≠ 2) (hqp : q ≠ p)
    (hJQ : ∀ (x z c : adjointGroup Tag.E8 K), Commute x z → orderOf x = p →
      adjEmb Tag.E8 K L (c * x * c⁻¹) = g0 *
        rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3XColumn ε (Nat.card K : ZMod p) i).val) *
        g0⁻¹ →
      adjEmb Tag.E8 K L (c * z * c⁻¹) = g0 *
        rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3ZColumn ε (Nat.card K : ZMod p) i).val) *
        g0⁻¹ →
      ∃ J Q : Subgroup (adjointGroup Tag.E8 K),
        J ≤ Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K)) ∧
        (J.subgroupOf (Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K)))).Normal ∧
        CFSG.IsQuasisimple J ∧ p ∣ Nat.card J ∧
        Q ≤ J ∧ Q ≤ Subgroup.centralizer ({z} : Set (adjointGroup Tag.E8 K)) ∧
        (Q.subgroupOf (J ⊓ Subgroup.centralizer ({z} : Set (adjointGroup Tag.E8 K)))).Normal ∧
        CFSG.IsQuasisimple Q ∧ p ∣ Nat.card Q)
    (hF : ∀ (x z c x₀ z₀ : adjointGroup Tag.E8 K) (J : Subgroup (adjointGroup Tag.E8 K)),
      x ∈ A → z ∈ A → orderOf x = p → orderOf z = p → z ∉ Subgroup.zpowers x →
      c * x * c⁻¹ = x₀ → c * z * c⁻¹ = z₀ →
      adjEmb Tag.E8 K L x₀ = g0 *
        rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3XColumn ε (Nat.card K : ZMod p) i).val) *
        g0⁻¹ →
      adjEmb Tag.E8 K L z₀ = g0 *
        rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3ZColumn ε (Nat.card K : ZMod p) i).val) *
        g0⁻¹ →
      J ≤ Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K)) →
      (J.subgroupOf (Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K)))).Normal →
      CFSG.IsQuasisimple J → p ∣ Nat.card J →
      ∃ F : Subgroup (adjointGroup Tag.E8 K),
        F ≤ Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K)) ∧
        F ≤ Subgroup.normalizer (J : Set (adjointGroup Tag.E8 K)) ∧
        IsElemAbelian q F ∧ 3 ≤ CFSG.Open.pRank q F) :
    Concl165 (adjointGroup Tag.E8 K) p q A := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨x, z, c, x₀, z₀, hxA, hzA, hxord, hzord, hzx, hcx, hcz, hxframe, hzframe⟩ :=
    exists_selection_pair hE6 hε hf hK hp hp3 hpf hq2 n hnm hnW g0 hg0C hg0 hperf hconj hAe hΩ hζ
  have hxframe' : adjEmb Tag.E8 K L (c * x * c⁻¹) = g0 *
      rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3XColumn ε (Nat.card K : ZMod p) i).val) *
      g0⁻¹ := by rw [hcx]; exact hxframe
  have hzframe' : adjEmb Tag.E8 K L (c * z * c⁻¹) = g0 *
      rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3ZColumn ε (Nat.card K : ZMod p) i).val) *
      g0⁻¹ := by rw [hcz]; exact hzframe
  obtain ⟨J, Q, hJx, hJn, hJq, hpJ, hQJ, hQz, hQn, hQq, hpQ⟩ :=
    hJQ x z c (hAe.comm hxA hzA) hxord hxframe' hzframe'
  obtain ⟨F, hFx, hFJ, hFel, hF3⟩ :=
    hF x z c x₀ z₀ J hxA hzA hxord hzord hzx hcx hcz hxframe hzframe hJx hJn hJq hpJ
  have hx1 : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hxord
    exact hp.ne_one hxord.symm
  exact concl165_of_layers hp hAe hxA hzA hx1 hzx hJx hJn
    (CFSG.Quasithin.A3.isQuasisimple_iff_open.mp hJq) hpJ hQJ hQz hQn
    (CFSG.Quasithin.A3.isQuasisimple_iff_open.mp hQq) hpQ hFel hFx hFJ hF3


end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three
