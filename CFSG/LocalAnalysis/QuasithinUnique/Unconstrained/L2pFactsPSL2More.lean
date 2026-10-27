module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2pFactsPSL2
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20Facts
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2pFactsCycle
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourMapInjective
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2KleinFourSelfCentralizer
public import CFSG.Walter.Cited.PSL2Small

public section

namespace CFSG.QuasithinUnique.Unc25K1

open CFSG.QuasithinUnique CFSG.GorensteinWalter
open scoped MatrixGroups

section Facts

variable {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime]

theorem psl2_a4 (hp7 : 7 ≤ p) (hK : Nat.card K = p)
    (hc2 : ∀ i : PSL(2, K), orderOf i = 2 →
      IsPGroup 2 (Subgroup.centralizer ({i} : Set PSL(2, K)))) :
    ∃ V : Subgroup PSL(2, K), V ≠ ⊥ ∧ IsPGroup 2 V ∧
      3 ∣ Nat.card (Subgroup.normalizer (V : Set PSL(2, K))) ∧
      ∀ x ∈ Subgroup.normalizer (V : Set PSL(2, K)),
        (∀ y ∈ Subgroup.normalizer (V : Set PSL(2, K)), y * x = x * y) → x ^ 3 = 1 → x = 1 := by
  have hK' := isOddPrimePower_of_card_prime hp7 hK
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K
    (by rw [hK]; exact (Fact.out : p.Prime).odd_of_ne_two (by omega))
  obtain ⟨S⟩ : Nonempty (Sylow 2 PSL(2, K)) := inferInstance
  obtain ⟨t, s, -, -, ht2, hs2, ht1, hs1, hts, hcomm⟩ :=
    exists_commuting_involutions_of_sylow hK' S
  have hc : Commute t s := hcomm
  obtain ⟨w, hw1, hw2⟩ := exists_psl2_cycle h2 ht1 hs1 hts ht2 hs2 hcomm
  obtain ⟨hwN, hw3⟩ := three_dvd_orderOf_of_cycle ht2 hs2 hc hts hw1 hw2
  have hV4 : IsKleinFour (kleinFourOfCommutingInvolutions t s ht2 hs2 hc) :=
    isKleinFour_kleinFourOfCommutingInvolutions t s ht2 hs2 ht1 hs1 hts hc
  have htV : t ∈ kleinFourOfCommutingInvolutions t s ht2 hs2 hc :=
    (mem_kleinFourOfCommutingInvolutions_iff ht2 hs2 hc t).mpr (Or.inr (Or.inl rfl))
  refine ⟨kleinFourOfCommutingInvolutions t s ht2 hs2 hc, ?_,
    IsPGroup.of_card (n := 2) (by rw [hV4.card_four]; norm_num), ?_, ?_⟩
  · intro hbot
    apply ht1
    have : t ∈ (⊥ : Subgroup PSL(2, K)) := hbot ▸ htV
    simpa using this
  · have h := orderOf_dvd_natCard (⟨w, hwN⟩ : Subgroup.normalizer
      ((kleinFourOfCommutingInvolutions t s ht2 hs2 hc : Subgroup PSL(2, K)) : Set PSL(2, K)))
    rw [Subgroup.orderOf_mk] at h
    exact hw3.trans h
  · intro x _ hcen hx3
    have htN : t ∈ Subgroup.normalizer
        ((kleinFourOfCommutingInvolutions t s ht2 hs2 hc : Subgroup PSL(2, K)) : Set PSL(2, K)) :=
      Subgroup.le_normalizer htV
    have hxt : x * t = t * x := (hcen t htN).symm
    have hxC : x ∈ Subgroup.centralizer ({t} : Set PSL(2, K)) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hxt
    have hord : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1
    obtain ⟨n, hn⟩ := hc2 t hord ⟨x, hxC⟩
    have hxn : x ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
    have h1 : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hxn
    have h3 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
    exact orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left n (by norm_num)) h1 h3)

theorem psl2_nonab (hp7 : 7 ≤ p) (hK : Nat.card K = p) (h8 : p % 8 = 1 ∨ p % 8 = 7) :
    ∀ P : Subgroup PSL(2, K), IsSylowTwoOf P ⊤ → ∃ y ∈ P, y ^ 2 ≠ 1 := by
  intro P hP
  obtain ⟨S, hSP⟩ := exists_sylow_of_isSylowTwoOf_top hP
  obtain ⟨y, hy, hy2⟩ := exists_sq_ne_one_of_sylow (isOddPrimePower_of_card_prime hp7 hK)
    (eight_dvd_card_psl2 hp7 hK h8) S
  exact ⟨y, hSP ▸ hy, hy2⟩

theorem psl2_aut_two
    (hp7 : 7 ≤ p) (hK : Nat.card K = p) :
    ∀ P : Subgroup PSL(2, K), IsSylowTwoOf P ⊤ → ∀ α : MulAut PSL(2, K), (∀ y ∈ P, α y = y) →
      ∀ x : PSL(2, K), α (α x) = x := by
  intro P hP α hα x
  have hK' := isOddPrimePower_of_card_prime hp7 hK
  have hKpow : Nat.card K = p ^ 1 := by rw [hK, pow_one]
  have hcard : 3 < Nat.card K := by omega
  obtain ⟨S, hSP⟩ := exists_sylow_of_isSylowTwoOf_top hP
  obtain ⟨t, s, htS, hsS, ht2, hs2, ht1, hs1, hts, hcomm⟩ :=
    exists_commuting_involutions_of_sylow hK' S
  rw [hSP] at htS hsS
  have hc : Commute t s := hcomm
  have hV : IsKleinFour (kleinFourOfCommutingInvolutions t s ht2 hs2 hc) :=
    isKleinFour_kleinFourOfCommutingInvolutions t s ht2 hs2 ht1 hs1 hts hc
  have hVfix : ∀ v ∈ kleinFourOfCommutingInvolutions t s ht2 hs2 hc, α v = v := by
    intro v hv
    apply hα
    rcases (mem_kleinFourOfCommutingInvolutions_iff ht2 hs2 hc v).mp hv with rfl | rfl | rfl | rfl
    · exact P.mul_mem htS hsS
    · exact htS
    · exact hsS
    · exact P.one_mem
  have hex : ∃ (g : PGL2 K) (σ : K ≃+* K),
      α = pgl2InnerAutPSL2 K hK' hcard g * psl2FieldAut K σ := by
    obtain ⟨xx, hxx⟩ := pGammaL2ToMulAutPSL2_surjective K hKpow hK' hcard α
    have h := congrArg (pGammaL2ToMulAutPSL2 K hK' hcard)
      (SemidirectProduct.inl_left_mul_inr_right xx)
    rw [map_mul, pGammaL2ToMulAutPSL2_inl, pGammaL2ToMulAutPSL2_inr, hxx] at h
    exact ⟨xx.left, xx.right, h.symm⟩
  obtain ⟨g, σ, hαgσ⟩ := hex
  have hσ : σ = 1 := (CFSG.Walter.Suzuki.subsingleton_ringEquiv_of_card_prime K hK).elim _ _
  rw [hσ, map_one, mul_one] at hαgσ
  let toPGL : PSL(2, K) →* PGL2 K := Matrix.ProjectiveSpecialLinearGroup.toPGL
  have htoPGL : Function.Injective toPGL := fun _ _ h =>
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective h
  have hVP : IsKleinFour ((kleinFourOfCommutingInvolutions t s ht2 hs2 hc).map toPGL) :=
    isKleinFour_map_of_injective _ hV toPGL htoPGL
  have hgC : g ∈ Subgroup.centralizer
      (((kleinFourOfCommutingInvolutions t s ht2 hs2 hc).map toPGL : Subgroup (PGL2 K)) :
        Set (PGL2 K)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨v, hv, rfl⟩
    have h1 : pgl2InnerAutPSL2 K hK' hcard g v = v := by
      rw [← hαgσ]
      exact hVfix v hv
    have h2 := toPGL_pgl2InnerAutPSL2_apply K hK' hcard g v
    rw [h1] at h2
    calc toPGL v * g = (g * toPGL v * g⁻¹) * g := by rw [← h2]
      _ = g * toPGL v := by group
  rw [pgl2_kleinFour_centralizer_eq_self K hK' _ hVP] at hgC
  obtain ⟨g0, hg0V, hg0⟩ := hgC
  have hα2 : α = MulAut.conj g0 := by
    rw [hαgσ, ← hg0]
    exact pgl2InnerAutPSL2_toPGL K hK' hcard g0
  have hg02 : g0 ^ 2 = 1 := by
    have h := Monoid.pow_exponent_eq_one
      (⟨g0, hg0V⟩ : kleinFourOfCommutingInvolutions t s ht2 hs2 hc)
    rw [hV.exponent_two] at h
    exact congrArg Subtype.val h
  have hg0g0 : g0 * g0 = 1 := by rw [← pow_two]; exact hg02
  have hinv : g0⁻¹ = g0 := inv_eq_of_mul_eq_one_right hg0g0
  rw [hα2]
  simp only [MulAut.conj_apply]
  rw [hinv]
  calc g0 * (g0 * x * g0) * g0 = (g0 * g0) * x * (g0 * g0) := by group
    _ = x := by rw [hg0g0]; group

theorem psl2_l2pData
    (hp7 : 7 ≤ p) (hK : Nat.card K = p)
    (hpow : (p % 8 = 1 ∧ ∃ m : ℕ, p = 2 ^ m + 1) ∨ (p % 8 = 7 ∧ ∃ m : ℕ, p + 1 = 2 ^ m)) :
    L2pData PSL(2, K) := by
  have h8 : p % 8 = 1 ∨ p % 8 = 7 := hpow.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hc2 := psl2_cent_two hp7 hK hpow
  exact
    { simple := psl2_simple hp7 hK
      nonabelian := psl2_nonabelian hp7 hK h8
      single_class := psl2_single_class hp7 hK
      cent_two := hc2
      inner_three := psl2_inner_three hK
      a4 := psl2_a4 hp7 hK hc2
      nonab := psl2_nonab hp7 hK h8
      aut_two := psl2_aut_two hp7 hK }

end Facts

end CFSG.QuasithinUnique.Unc25K1
