module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.Walter.PSL2Facts.Odd

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.Hin.SporX

open CFSG.GorensteinWalter

theorem natCard_ringEquiv_le {K : Type} [Field K] [Finite K] {p m : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p ^ m) : Nat.card (K ≃+* K) ≤ m := by
  have : Fact p.Prime := ⟨hp⟩
  let : Fintype K := Fintype.ofFinite K
  have hcardF : Fintype.card K = p ^ m := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  have : CharP K p := charP_of_card_eq_prime_pow hcardF
  let : Algebra (ZMod p) K := ZMod.algebra K p
  have : FiniteDimensional (ZMod p) K := Module.Finite.of_finite
  let e : (K ≃+* K) ≃ (K ≃ₐ[ZMod p] K) :=
    { toFun := fun σ => AlgEquiv.ofRingEquiv (f := σ) (fun x => by
        have h : (σ.toRingHom.comp (algebraMap (ZMod p) K) : ZMod p →+* K) =
            algebraMap (ZMod p) K := RingHom.ext_zmod _ _
        exact DFunLike.congr_fun h x)
      invFun := fun σ => σ.toRingEquiv
      left_inv := fun σ => by ext x; rfl
      right_inv := fun σ => by ext x; rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  refine AlgEquiv.card_le.trans (le_of_eq ?_)
  have h := Module.card_eq_pow_finrank (K := ZMod p) (V := K)
  rw [ZMod.card, hcardF] at h
  exact (Nat.pow_right_injective hp.two_le h).symm

theorem ringEquiv_eq_one_of_pow {K : Type} [Field K] [Finite K] {p m r : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p ^ m) (hr : r.Prime) (hmr : m < r) {σ : K ≃+* K} (hσ : σ ^ r = 1) :
    σ = 1 := by
  have : Finite (K ≃+* K) := Finite.of_injective (fun σ : K ≃+* K => (σ : K → K))
    DFunLike.coe_injective
  rcases (Nat.dvd_prime hr).1 (orderOf_dvd_of_pow_eq_one hσ) with h1 | h1
  · exact orderOf_eq_one_iff.1 h1
  · have hle : orderOf σ ≤ Nat.card (K ≃+* K) := orderOf_le_card
    have := natCard_ringEquiv_le hp hK
    omega

theorem psl2_aut_mem_inner {K : Type} [Field K] [Finite K] {p m r : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hm : 1 ≤ m) (hK : Nat.card K = p ^ m) (hq : 3 < p ^ m) (hr : r.Prime)
    (hr3 : 3 < r) (hmr : m < r) {β : MulAut (PSL2 K)} (hβ : β ^ r = 1) :
    β ∈ (MulAut.conj : PSL2 K →* MulAut (PSL2 K)).range := by
  have : Fact p.Prime := ⟨hp⟩
  have hKodd : IsOddPrimePower (Nat.card K) := ⟨p, m, hp, hp.odd_of_ne_two hp2, hm, hK⟩
  have hcard : 3 < Nat.card K := hK ▸ hq
  obtain ⟨g, rfl⟩ := pGammaL2ToMulAutPSL2_surjective K hK hKodd hcard β
  have hg : g ^ r = 1 :=
    pGammaL2ToMulAutPSL2_injective K hKodd hcard (by rw [map_pow, hβ, map_one])
  have hσ : g.right ^ r = 1 := by
    have h := congrArg SemidirectProduct.rightHom hg
    rwa [map_pow, map_one, SemidirectProduct.rightHom_eq_right] at h
  have hσ1 : g.right = 1 := ringEquiv_eq_one_of_pow hp hK hr hmr hσ
  have hgl : g = SemidirectProduct.inl g.left := by
    refine SemidirectProduct.ext ?_ ?_
    · rw [SemidirectProduct.left_inl]
    · rw [SemidirectProduct.right_inl, hσ1]
  rw [hgl, pGammaL2ToMulAutPSL2_inl] at hβ ⊢
  have hy : pgl2InnerAutPSL2 K hKodd hcard (g.left ^ r) =
      pgl2InnerAutPSL2 K hKodd hcard (Matrix.ProjectiveSpecialLinearGroup.toPGL 1) := by
    rw [map_pow, hβ, map_one, map_one]
  have hgr : g.left ^ r ^ 1 ∈
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range :=
    ⟨1, by rw [pow_one]; exact (pgl2InnerAutPSL2_injective K hKodd hcard hy).symm⟩
  have hidx : (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range.index ≤
      3 := by
    rw [pgl2_psl2Range_index_eq_two K hKodd]
    norm_num
  have : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  obtain ⟨y, hy'⟩ :=
    RankThree.PartOne.OutStructure.mem_of_pow_mem_of_index_le_three _ hidx hr hr3 hgr
  exact ⟨y, by rw [← hy', pgl2InnerAutPSL2_toPGL]⟩

theorem prime_dvd_card_ON {p : ℕ} (hp : p.Prime) (h : p ∣ 460815505920) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 19 ∨ p = 31 := by
  rw [show (460815505920 : ℕ) = 2 ^ 9 * 3 ^ 4 * 5 * 7 ^ 3 * 11 * 19 * 31 by norm_num] at h
  have hq : ∀ {q : ℕ}, q.Prime → ∀ {k : ℕ}, p ∣ q ^ k → p = q := fun hq _ hk =>
    (Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow hk)
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
        · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
          · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
            · exact Or.inl (hq Nat.prime_two h)
            · exact Or.inr (Or.inl (hq (by norm_num) h))
          · exact Or.inr (Or.inr (Or.inl (hq (by norm_num) (k := 1) (by rwa [pow_one]))))
        · exact Or.inr (Or.inr (Or.inr (Or.inl (hq (by norm_num) h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          (hq (by norm_num) (k := 1) (by rwa [pow_one]))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (hq (by norm_num) (k := 1) (by rwa [pow_one])))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (hq (by norm_num) (k := 1) (by rwa [pow_one])))))))

theorem on_q_cases {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (h16 : 16 ∣ (p ^ m) ^ 2 - 1) (hdvd : p ^ m * ((p ^ m) ^ 2 - 1) / 2 ∣ 460815505920) :
    p ^ m = 7 ∨ p ^ m = 9 ∨ p ^ m = 31 := by
  have hqd : p ^ m ∣ 460815505920 := by
    refine Dvd.dvd.trans ⟨((p ^ m) ^ 2 - 1) / 2, ?_⟩ hdvd
    have hodd : Odd (p ^ m) := (hp.odd_of_ne_two hp2).pow
    have h2 : 2 ∣ (p ^ m) ^ 2 - 1 := by
      obtain ⟨k, hk⟩ := hodd
      exact ⟨2 * k ^ 2 + 2 * k, by rw [hk]; ring_nf; omega⟩
    rw [Nat.mul_div_assoc _ h2]
  have hpd : p ∣ 460815505920 := (dvd_pow_self p (by omega)).trans hqd
  have hbound : ∀ e : ℕ, ¬ p ^ (e + 1) ∣ 460815505920 → m ≤ e := fun e he => by
    by_contra hlt
    exact he ((pow_dvd_pow p (by omega)).trans hqd)
  rcases prime_dvd_card_ON hp hpd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hp2
  · have := hbound 4 (by norm_num)
    interval_cases m <;> revert h16 hdvd <;> norm_num
  · obtain rfl : m = 1 := le_antisymm (hbound 1 (by norm_num)) hm
    revert h16 hdvd
    norm_num
  · have := hbound 3 (by norm_num)
    interval_cases m <;> revert h16 hdvd <;> norm_num
  · obtain rfl : m = 1 := le_antisymm (hbound 1 (by norm_num)) hm
    revert h16 hdvd
    norm_num
  · obtain rfl : m = 1 := le_antisymm (hbound 1 (by norm_num)) hm
    revert h16 hdvd
    norm_num
  · obtain rfl : m = 1 := le_antisymm (hbound 1 (by norm_num)) hm
    revert h16 hdvd
    norm_num

theorem exists_involution_ne_of_dihedral {G : Type*} [Group G] {n : ℕ} (hn : 1 < n)
    (e : G ≃* DihedralGroup n) (t : G) : ∃ b : G, orderOf b = 2 ∧ b ≠ t := by
  have : Fact (1 < n) := ⟨hn⟩
  have h01 : e.symm (DihedralGroup.sr 0) ≠ e.symm (DihedralGroup.sr 1) := fun h =>
    zero_ne_one (DihedralGroup.sr.inj (e.symm.injective h))
  have ho : ∀ i : ZMod n, orderOf (e.symm (DihedralGroup.sr i)) = 2 := fun i => by
    rw [MulEquiv.orderOf_eq, DihedralGroup.orderOf_sr]
  by_cases h0 : e.symm (DihedralGroup.sr 0) = t
  · exact ⟨_, ho 1, fun h1 => h01 (h0.trans h1.symm)⟩
  · exact ⟨_, ho 0, h0⟩

open scoped MatrixGroups in
theorem psl2_centralizer_involution_small {K : Type} [Field K] [Finite K] {p f : ℕ}
    [Fact p.Prime] (hK : Nat.card K = p ^ f) (hp : Odd p) (hf : 0 < f)
    (hq : p ^ f = 7 ∨ p ^ f = 9 ∨ p ^ f = 31) {t : PSL(2, K)} (ht : orderOf t = 2) :
    Nat.card (Subgroup.centralizer ({t} : Set PSL(2, K))) ∣ 32 ∧
      ∃ b ∈ Subgroup.centralizer ({t} : Set PSL(2, K)), orderOf b = 2 ∧ b ≠ t := by
  obtain ⟨h1, h3⟩ := Walter.psl2_centralizer_involution K hK hp hf ht
  have hsec : ∀ {n : ℕ}, 1 < n →
      Nonempty (Subgroup.centralizer ({t} : Set PSL(2, K)) ≃* DihedralGroup n) →
      ∃ b ∈ Subgroup.centralizer ({t} : Set PSL(2, K)), orderOf b = 2 ∧ b ≠ t := by
    rintro n hn ⟨e⟩
    obtain ⟨b, hb2, hbt⟩ := exists_involution_ne_of_dihedral hn e
      ⟨t, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
    refine ⟨b, b.2, by rw [Subgroup.orderOf_coe]; exact hb2, fun h => hbt (Subtype.ext h)⟩
  rcases hq with hq | hq | hq
  · obtain ⟨hc, he⟩ := h3 (by rw [hq])
    rw [hq] at hc he
    exact ⟨by norm_num [hc], hsec (by norm_num) he⟩
  · obtain ⟨hc, he⟩ := h1 (by rw [hq])
    rw [hq] at hc he
    exact ⟨by norm_num [hc], hsec (by norm_num) he⟩
  · obtain ⟨hc, he⟩ := h3 (by rw [hq])
    rw [hq] at hc he
    exact ⟨by norm_num [hc], hsec (by norm_num) he⟩

end CFSG.ComponentClassification.HarrisLit.Hin.SporX
