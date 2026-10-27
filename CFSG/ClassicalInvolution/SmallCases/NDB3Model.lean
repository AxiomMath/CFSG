module

public import CFSG.ClassicalInvolution.RouteD.SCRTwinGenSp4

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.Assembly.LowTwoRank

theorem sp4Gen_model {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (t : StatedLieTag) (n e : ℕ)
    (ht : t = .PSp) (hn : n = 2) (hadm : StatedLieAdmissible t n p e) (h5 : 5 ≤ p ^ e)
    {R R' : Subgroup (Generic.modelUniv t n p e Fact.out).K}
    (hR : R ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t n p e Fact.out).D)
    (hR' : R' ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t n p e Fact.out).D)
    (hne : R ≠ R') {x x' : (Generic.modelUniv t n p e Fact.out).K} (hxR : x ∈ R)
    (hxc : ∀ r ∈ R, x * r = r * x) (hx1 : x ≠ 1) (hx'R' : x' ∈ R')
    (hx'c : ∀ r ∈ R', x' * r = r * x') (hx'1 : x' ≠ 1)
    (hsame : x * x'⁻¹ ∈ Subgroup.center (Generic.modelUniv t n p e Fact.out).K)
    {a a' : (Generic.modelUniv t n p e Fact.out).K} (ha : a ∈ R) (ha' : a' ∈ R')
    (hsq : a * a * x⁻¹ ∈ Subgroup.center (Generic.modelUniv t n p e Fact.out).K)
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (Generic.modelUniv t n p e Fact.out).K) :
    Subgroup.centralizer ({x} : Set (Generic.modelUniv t n p e Fact.out).K) ⊔
      Subgroup.centralizer ({a * a'} : Set (Generic.modelUniv t n p e Fact.out).K) ⊔
      Subgroup.centralizer ({x * (a * a')} : Set (Generic.modelUniv t n p e Fact.out).K) = ⊤ := by
  subst ht hn
  have he : e ≠ 0 := by
    rintro rfl
    simp at h5
  have h2 : (2 : GaloisField p e) ≠ 0 := ModelFacts.two_ne_zero_galoisField e hp2
  have hcard : 3 ≤ Nat.card (GaloisField p e) := by
    rw [GaloisField.card p e he]
    exact le_trans (by norm_num : 3 ≤ 5) h5
  exact RouteD.SCRSp4.sp4_gen h2 hcard ((ModelFacts.fund_iff_isLongRootSp2 hadm h2 R).mp hR)
    ((ModelFacts.fund_iff_isLongRootSp2 hadm h2 R').mp hR') hne hxR hxc hx1 hx'R' hx'c hx'1 hsame
    ha ha' hsq hsq'

end CFSG.ClassicalInvolution.NDB
