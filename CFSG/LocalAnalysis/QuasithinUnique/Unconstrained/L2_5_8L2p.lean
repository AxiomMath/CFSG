module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Four
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2pFactsCycle
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2pFactsPSL2
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourMapInjective
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2KleinFourSelfCentralizer
public import CFSG.Walter.Cited.PSL2Small

public section

namespace CFSG.QuasithinUnique.Unc25Small

open CFSG.Open CFSG.Quasithin CFSG.GorensteinWalter
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped MatrixGroups

theorem isKleinFour_of_isFourSubgroup {X : Type} [Group X] {F : Subgroup X}
    (hF : IsFourSubgroup F) : IsKleinFour F := by
  obtain ⟨⟨hc, hexp⟩, hcard⟩ := hF
  refine ⟨hcard, ?_⟩
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
  intro g hg
  exact orderOf_eq_prime (Subtype.ext (hexp g g.2)) hg

theorem exists_kleinFour_gens {X : Type} [Group X] {F : Subgroup X} (hF : IsFourSubgroup F) :
    ∃ (t s : X) (ht : t * t = 1) (hs : s * s = 1) (hc : Commute t s), t ≠ 1 ∧ s ≠ 1 ∧ t ≠ s ∧
      F = kleinFourOfCommutingInvolutions t s ht hs hc := by
  obtain ⟨t, htF, s, hsF, ht1, hs1, hts⟩ := exists_two_nonid hF.2
  have hexp : ∀ x ∈ F, x * x = 1 := fun x hx => by
    have := hF.1.2 x hx
    rwa [pow_two] at this
  have := hF.1.1
  have hc : Commute t s := setLike_mul_comm htF hsF
  refine ⟨t, s, hexp t htF, hexp s hsF, hc, ht1, hs1, hts, ?_⟩
  ext x
  rw [mem_klein_iff hF.2 hexp htF hsF ht1 hs1 hts x,
    Unc25K1.mem_kleinFourOfCommutingInvolutions_iff (hexp t htF) (hexp s hsF) hc x]
  tauto

section PSL2

variable {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime]

structure L2pHyp (K : Type) [Field K] (p : ℕ) : Prop where
  hp7 : 7 ≤ p
  hK : Nat.card K = p
  hpow : (p % 8 = 1 ∧ ∃ m : ℕ, p = 2 ^ m + 1) ∨ (p % 8 = 7 ∧ ∃ m : ℕ, p + 1 = 2 ^ m)

omit [Finite K] [Fact p.Prime] in
theorem L2pHyp.h8 (H : L2pHyp K p) : p % 8 = 1 ∨ p % 8 = 7 :=
  H.hpow.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)

omit [Finite K] in
theorem L2pHyp.odd (H : L2pHyp K p) : IsOddPrimePower (Nat.card K) :=
  Unc25K1.isOddPrimePower_of_card_prime H.hp7 H.hK

theorem psl2_dihedral_sylow (H : L2pHyp K p) (S : Sylow 2 PSL(2, K)) :
    ∃ m : ℕ, 2 ≤ m ∧ Nonempty (↥(S : Subgroup PSL(2, K)) ≃* DihedralGroup (2 ^ m)) := by
  obtain ⟨m, hm, ⟨e⟩⟩ := psl2_odd_hasDihedralSylowTwo_model K H.odd S
  have hcard : Nat.card (S : Subgroup PSL(2, K)) = 2 ^ (Nat.card PSL(2, K)).factorization 2 :=
    S.card_eq_multiplicity
  have hcard2 : Nat.card (S : Subgroup PSL(2, K)) = 2 * 2 ^ m :=
    (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
  have hv : 3 ≤ (Nat.card PSL(2, K)).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp
      (by simpa using Unc25K1.eight_dvd_card_psl2 H.hp7 H.hK H.h8)
  have hm2 : 2 ≤ m := by
    by_contra hlt
    have hm1 : m = 1 := by omega
    subst hm1
    have h8' : 2 ^ 3 ≤ 2 ^ (Nat.card PSL(2, K)).factorization 2 :=
      Nat.pow_le_pow_right (by norm_num) hv
    omega
  exact ⟨m, hm2, ⟨e⟩⟩

theorem psl2_sylow_dihedral (H : L2pHyp K p) :
    ∀ P : Subgroup PSL(2, K), IsSylowTwoOf P ⊤ →
      ∃ m : ℕ, 2 ≤ m ∧ Nonempty (↥P ≃* DihedralGroup (2 ^ m)) := by
  intro P hP
  obtain ⟨S, hSP⟩ := Unc25K1.exists_sylow_of_isSylowTwoOf_top hP
  obtain ⟨m, hm2, ⟨e⟩⟩ := psl2_dihedral_sylow H S
  exact ⟨m, hm2, ⟨(MulEquiv.subgroupCongr hSP.symm).trans e⟩⟩

theorem psl2_sylow_shape (H : L2pHyp K p) :
    ∀ P : Subgroup PSL(2, K), IsSylowTwoOf P ⊤ →
      (∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥P ≃* DihedralGroup n)) ∨
        Nonempty (↥P ≃* SemidihedralGroup 4) := by
  intro P hP
  obtain ⟨m, hm2, ⟨e⟩⟩ := psl2_sylow_dihedral H P hP
  refine Or.inl ⟨2 ^ m, ?_, ⟨e⟩⟩
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2

theorem psl2_centralizer_kleinFour
    (H : L2pHyp K p) {V : Subgroup PSL(2, K)} (hV : IsKleinFour V) :
    Subgroup.centralizer (V : Set PSL(2, K)) = V := by
  let toPGL : PSL(2, K) →* PGL2 K := Matrix.ProjectiveSpecialLinearGroup.toPGL
  have htoPGL : Function.Injective toPGL := fun _ _ h =>
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective h
  have hVP : IsKleinFour (V.map toPGL) := isKleinFour_map_of_injective _ hV toPGL htoPGL
  have hcent := pgl2_kleinFour_centralizer_eq_self K H.odd _ hVP
  apply le_antisymm
  · intro g hg
    have hgC : toPGL g ∈ Subgroup.centralizer ((V.map toPGL : Subgroup (PGL2 K)) : Set (PGL2 K)) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨v, hv, rfl⟩
      have := Subgroup.mem_centralizer_iff.mp hg v hv
      simp only [← map_mul]
      exact congrArg toPGL this
    rw [hcent] at hgC
    obtain ⟨v, hv, hvg⟩ := hgC
    rw [← htoPGL hvg]
    exact hv
  · intro v hv
    have := hV.isMulCommutative
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact setLike_mul_comm hw hv

theorem psl2_aut_fix_four
    (H : L2pHyp K p) {V : Subgroup PSL(2, K)} (hV : IsKleinFour V)
    {α : MulAut PSL(2, K)} (hα : ∀ v ∈ V, α v = v) : ∃ g0 ∈ V, α = MulAut.conj g0 := by
  have hK' := H.odd
  have hKpow : Nat.card K = p ^ 1 := by rw [H.hK, pow_one]
  have hcard : 3 < Nat.card K := by rw [H.hK]; have := H.hp7; omega
  have hex : ∃ (g : PGL2 K) (σ : K ≃+* K),
      α = pgl2InnerAutPSL2 K hK' hcard g * psl2FieldAut K σ := by
    obtain ⟨xx, hxx⟩ := pGammaL2ToMulAutPSL2_surjective K hKpow hK' hcard α
    have h := congrArg (pGammaL2ToMulAutPSL2 K hK' hcard)
      (SemidirectProduct.inl_left_mul_inr_right xx)
    rw [map_mul, pGammaL2ToMulAutPSL2_inl, pGammaL2ToMulAutPSL2_inr, hxx] at h
    exact ⟨xx.left, xx.right, h.symm⟩
  obtain ⟨g, σ, hαgσ⟩ := hex
  have hσ : σ = 1 := (CFSG.Walter.Suzuki.subsingleton_ringEquiv_of_card_prime K H.hK).elim _ _
  rw [hσ, map_one, mul_one] at hαgσ
  let toPGL : PSL(2, K) →* PGL2 K := Matrix.ProjectiveSpecialLinearGroup.toPGL
  have htoPGL : Function.Injective toPGL := fun _ _ h =>
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective h
  have hVP : IsKleinFour (V.map toPGL) := isKleinFour_map_of_injective _ hV toPGL htoPGL
  have hgC : g ∈ Subgroup.centralizer ((V.map toPGL : Subgroup (PGL2 K)) : Set (PGL2 K)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨v, hv, rfl⟩
    have h1 : pgl2InnerAutPSL2 K hK' hcard g v = v := by
      rw [← hαgσ]
      exact hα v hv
    have h2 := toPGL_pgl2InnerAutPSL2_apply K hK' hcard g v
    rw [h1] at h2
    calc toPGL v * g = (g * toPGL v * g⁻¹) * g := by rw [← h2]
      _ = g * toPGL v := by group
  rw [pgl2_kleinFour_centralizer_eq_self K hK' _ hVP] at hgC
  obtain ⟨g0, hg0V, hg0⟩ := hgC
  refine ⟨g0, hg0V, ?_⟩
  rw [hαgσ, ← hg0]
  exact pgl2InnerAutPSL2_toPGL K hK' hcard g0

omit [Finite K] in
theorem psl2_out_two (H : L2pHyp K p) :
    ∀ φ : MulAut PSL(2, K), ∃ k : ℕ, φ ^ 2 ^ k ∈ innerAut PSL(2, K) := by
  intro φ
  have hout := (CFSG.LocalAnalysis.ComponentInitial.linear_two_outer_order_divisor
    (p := p) (f := 1) Fact.out K (by rw [H.hK, pow_one])).1
  have hcard2 : Nat.card (Outer PSL(2, K)) ∣ 2 := by
    refine hout.trans ?_
    rw [one_mul]
    exact Nat.gcd_dvd_left _ _
  have hord : orderOf (QuotientGroup.mk φ : Outer PSL(2, K)) ∣ 2 :=
    (orderOf_dvd_natCard _).trans hcard2
  have h1 : (QuotientGroup.mk φ : Outer PSL(2, K)) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp hord
  refine ⟨1, ?_⟩
  have h2 : φ ^ 2 ∈ inner PSL(2, K) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact h1
  obtain ⟨k, hk⟩ := h2
  exact ⟨k, by simpa using hk⟩

end PSL2

end CFSG.QuasithinUnique.Unc25Small
