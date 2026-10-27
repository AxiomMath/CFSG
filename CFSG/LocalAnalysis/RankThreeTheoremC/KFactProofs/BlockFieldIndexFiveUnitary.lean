module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexUnitary
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexFiveAbstract

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndexP

open Matrix CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.AGLEmbedding.ParabPrime (perfectJoin)
open CFSG.RankThree.PartOne.OutStructure (exists_pow_eq_of_pow_eq ringAut_comm)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex
open scoped Pointwise commutatorElement

section Torus3

variable {f : ℕ} {K : Type} [Field K]

theorem uniElemAbelian_rangeP {p : ℕ} {G : Type*} [Group G] {C : Type*} [CommGroup C] {r : ℕ}
    (hC3 : ∀ x : C, x ^ p = 1) (hC : Nat.card C = p) (σ : (Fin r → C) →* G)
    (hσ : Function.Injective σ) : IsElemAbelian p σ.range ∧ Nat.card σ.range = p ^ r := by
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩, ?_⟩
  · obtain ⟨x, hx⟩ := a.2
    obtain ⟨z, hz⟩ := b.2
    apply Subtype.ext
    change (a : G) * b = b * a
    rw [← hx, ← hz, ← map_mul, ← map_mul, mul_comm x z]
  · obtain ⟨x, rfl⟩ := hy
    rw [← map_pow]
    have : x ^ p = 1 := by
      funext i
      simp only [Pi.pow_apply, Pi.one_apply]
      exact hC3 (x i)
    rw [this, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hσ).toEquiv, Nat.card_fun, hC, Nat.card_fin]

theorem uniExists_cyclic_prime {p : ℕ} [OddPrime p] (h : UnitaryFieldData 2 f K)
    (h3 : p ∣ 2 ^ f + 1) :
    ∃ C : Subgroup Kˣ, Nat.card C = p ∧ ∀ x ∈ C, h.norm (x : K) = 1 := by
  haveI : Finite K := h.finite
  have hcard : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units, h.card, show 2 * f = f * 2 from mul_comm _ _, pow_mul]
    have : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
      have := Nat.sq_sub_sq (2 ^ f) 1
      simpa using this
    rw [this]
    exact Dvd.dvd.mul_right h3 _
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' p hcard
  have hω3 : ω ^ p = 1 := by
    rw [← hω]
    exact pow_orderOf_eq_one ω
  refine ⟨Subgroup.zpowers ω, by rw [Nat.card_zpowers, hω], fun x hx => ?_⟩
  have hx3 : x ^ p = 1 := by
    obtain ⟨k, rfl⟩ := hx
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hω3,
      _root_.one_zpow]
  have hxq : x ^ (2 ^ f + 1) = 1 := by
    obtain ⟨m, hm⟩ := h3
    rw [hm, pow_mul, hx3, one_pow]
  rw [UnitaryFieldData.norm_eq_pow, ← Units.val_pow_eq_pow_val, hxq, Units.val_one]

end Torus3

section Rank

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem uniExists_elemAbelian_sq_su {p : ℕ} [OddPrime p] {s ε : ℕ} (hm : 3 ≤ 2 * s + ε)
    (h3 : p ∣ 2 ^ f + 1) :
    ∃ E : Subgroup (GL (HypIndex s ε) K), E ≤ hypSU h s ε ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ 2 := by
  haveI : Finite K := h.finite
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := s) (ε := ε) h
  obtain ⟨C, hCcard, hCnorm⟩ := uniExists_cyclic_prime h h3
  have hC3 : ∀ x : C, x ^ p = 1 := fun x => by
    have := pow_card_eq_one' (G := C) (x := x)
    rwa [hCcard] at this
  let τ := uniTorusStd h (by omega : 2 + 1 ≤ 2 * s + ε) C hCnorm
  let σ : (Fin 2 → C) →* GL (HypIndex s ε) K :=
    (hypSU h s ε).subtype.comp
      (((hypTransport h hR).symm : unitarySU 2 f K (2 * s + ε) ≃* hypSU h s ε).toMonoidHom.comp τ)
  have hσ : Function.Injective σ :=
    Subtype.val_injective.comp ((hypTransport h hR).symm.injective.comp
      (uniTorusStd_injective h _ C hCnorm))
  obtain ⟨hE, hcard⟩ := uniElemAbelian_rangeP hC3 hCcard σ hσ
  refine ⟨σ.range, ?_, hE, by rw [hcard]⟩
  rintro _ ⟨t, rfl⟩
  exact ((hypTransport h hR).symm (τ t)).2

theorem uniFour_le_pRankP {p : ℕ} [OddPrime p] {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}
    {r ε : ℕ}
    (hn : 6 ≤ 2 * r + ε) (h3 : p ∣ 2 ^ f + 1) (ρ : hypSU h r ε →* ↥L)
    (hZ : ∀ y, ρ y ∈ Subgroup.center ↥L ↔ y ∈ hypScalars h r ε) : 4 ≤ Open.pRank p L := by
  haveI : Finite K := h.finite
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := r) (ε := ε) h
  obtain ⟨C, hCcard, hCnorm⟩ := uniExists_cyclic_prime h h3
  have hC3 : ∀ x : C, x ^ p = 1 := fun x => by
    have := pow_card_eq_one' (G := C) (x := x)
    rwa [hCcard] at this
  let τ := uniTorusStd h (by omega : 4 + 1 ≤ 2 * r + ε) C hCnorm
  let σ : (Fin 4 → C) →* hypSU h r ε :=
    ((hypTransport h hR).symm : unitarySU 2 f K (2 * r + ε) ≃* hypSU h r ε).toMonoidHom.comp τ
  let Ψ : (Fin 4 → C) →* Y := L.subtype.comp (ρ.comp σ)
  have hinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    intro t ht
    have h1 : ρ (σ t) = 1 := Subtype.ext ht
    have h2 : σ t ∈ hypScalars h r ε := (hZ _).1 (h1 ▸ Subgroup.one_mem _)
    have h4 := (mem_hypScalars_iff_transport hR (σ t)).1 h2
    have e : hypTransport h hR (σ t) = τ t := MulEquiv.apply_symm_apply _ _
    rw [e] at h4
    obtain ⟨c, -, -, hc⟩ := h4
    exact uniTorusStd_eq_one_of_scalar h (by omega : 4 + 2 ≤ 2 * r + ε) C hCnorm t c
      (by rw [hc]; rfl)
  refine CFSG.SectionRank.le_pRank_of_injective (p := p) (Fact.out : p.Prime).one_lt
    (fun a b => mul_comm a b)
    (fun x => funext fun i => hC3 (x i)) (k := 4) ?_ Ψ hinj ?_
  · rw [Nat.card_fun, hCcard, Nat.card_fin]
  · rintro _ ⟨t, rfl⟩
    exact (ρ (σ t)).2

end Rank

section GU

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem uniExists_pow_eq_normOneP {p : ℕ} [OddPrime p] (h : UnitaryFieldData 2 f K) {m k : ℕ}
    (hm : ¬ p ∣ Nat.gcd m (2 ^ f + 1)) {d u : Kˣ} (hd : h.norm (d : K) = 1)
    (hu : h.norm (u : K) = 1) (hdu : d ^ (p ^ k) = u ^ m) :
    ∃ μ : Kˣ, h.norm (μ : K) = 1 ∧ μ ^ m = d := by
  haveI : Finite K := h.finite
  let Z : Subgroup Kˣ := (powMonoidHom (2 ^ f + 1) : Kˣ →* Kˣ).ker
  have hZmem : ∀ x : Kˣ, x ∈ Z ↔ h.norm (x : K) = 1 := fun x => by
    rw [UnitaryFieldData.norm_eq_pow, ← Units.val_pow_eq_pow_val, Units.val_eq_one]
    simp [Z, MonoidHom.mem_ker]
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Z)
  have hord : orderOf γ = Nat.card Z := orderOf_eq_card_of_forall_mem_zpowers hγ
  have hγq : γ ^ (2 ^ f + 1) = 1 := by
    have h1 := MonoidHom.mem_ker.1 γ.2
    exact Subtype.ext (by simpa using h1)
  have hcard : Nat.card Z ∣ 2 ^ f + 1 := hord ▸ orderOf_dvd_of_pow_eq_one hγq
  have hn : ¬ p ∣ Nat.gcd m (Nat.card Z) := fun h3 =>
    hm (h3.trans (Nat.gcd_dvd_gcd_of_dvd_right m hcard))
  obtain ⟨μ, hμ⟩ := exists_pow_eq_of_pow_eq (Z := Z) OddPrime.prime hn (k := k)
    (d := ⟨d, (hZmem d).2 hd⟩) (u := ⟨u, (hZmem u).2 hu⟩) (Subtype.ext hdu)
  exact ⟨μ, (hZmem _).1 μ.2, congrArg Subtype.val hμ⟩

end GU

section LeviData

variable {f t s ε : ℕ} {K : Type} [Field K]

theorem uniHZP {p : ℕ} [OddPrime p] {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}
    (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1) {I : Finset ℕ} (hI : IsTopCut I t)
    (ρ : hypSU h (t + s) ε →* ↥L)
    (hZ : ∀ y, ρ y ∈ Subgroup.center ↥L ↔ y ∈ hypScalars h (t + s) ε)
    (hrankp : Open.pRank p L ≤ 3) (j : Option ↥I)
    (E : Subgroup (uniBlockGroup K s ε I j))
    (hES : E ≤ uniBlockSub (s := s) (ε := ε) h I j) (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 2) (x : ↥(flagStabilizer h (t + s) ε ↑I))
    (hρx : ρ (x : hypSU h (t + s) ε) = 1)
    (hβx : uniLeviHom h hε hI x ∈ E.map (MonoidHom.mulSingle (uniBlockGroup K s ε I) j)) :
    x = 1 := by
  classical
  haveI : Finite K := h.finite
  have ht1 : 1 ≤ t := (hI.le t hI.mem).1
  have hxs : (x : hypSU h (t + s) ε) ∈ hypScalars h (t + s) ε :=
    (hZ _).1 (by rw [hρx]; exact Subgroup.one_mem _)
  by_cases h3 : p ∣ Nat.gcd (2 * (t + s) + ε) (2 ^ f + 1)
  · have h3q : p ∣ 2 ^ f + 1 := h3.trans (Nat.gcd_dvd_right _ _)
    have h3n : p ∣ 2 * (t + s) + ε := h3.trans (Nat.gcd_dvd_left _ _)
    by_cases hn6 : 6 ≤ 2 * (t + s) + ε
    · exfalso
      have := uniFour_le_pRankP hn6 h3q ρ hZ
      omega
    ·
      obtain ⟨c, hcn, -, hxc⟩ := hxs
      obtain ⟨k, hk⟩ := h3n
      have hp3 := OddPrime.three_le p
      have hk1 : k = 1 := by
        rcases Nat.lt_or_ge k 2 with hk2 | hk2
        · rcases Nat.eq_zero_or_pos k with hk0 | hk0
          · subst hk0
            omega
          · omega
        · exfalso
          have : p * 2 ≤ p * k := Nat.mul_le_mul_left p hk2
          omega
      have hodd : Odd (2 * (t + s) + ε) := by
        rw [hk, hk1, mul_one]
        exact OddPrime.odd
      obtain ⟨m, hm⟩ := hodd
      have hε1 : ε = 1 := by omega
      subst hε1
      have hc1 : (c : K) = 1 := by
        obtain ⟨y, hy, hyx⟩ := hβx
        have hxm : (((x : hypSU h (t + s) 1) : GL (HypIndex (t + s) 1) K) :
            Matrix (HypIndex (t + s) 1) (HypIndex (t + s) 1) K) =
              Matrix.scalar (HypIndex (t + s) 1) (c : K) := by
          rw [hxc, GeneralLinearGroup.coe_scalar]
        by_cases hj : j = none
        · subst hj
          have hne : (some ⟨t, hI.mem⟩ : Option ↥I) ≠ none := by simp
          have h1 : uniLeviHom h hε hI x (some ⟨t, hI.mem⟩) = 1 := by
            rw [← hyx]
            exact Pi.mulSingle_eq_of_ne (M := uniBlockGroup K s 1 I) hne y
          have hpos : 0 < t - predCut I t := by
            have := predCut_lt (I := I) ht1
            omega
          rw [uniLeviHom_some] at h1
          have h2 := congrArg (fun g : GL (Fin (t - predCut I t)) K =>
            (g : Matrix (Fin (t - predCut I t)) (Fin (t - predCut I t)) K) ⟨0, hpos⟩ ⟨0, hpos⟩) h1
          simp only [coe_eBlockHom, hxm, Matrix.submatrix_apply, Matrix.scalar_apply,
            Matrix.diagonal_apply_eq, Units.val_one, Matrix.one_apply_eq] at h2
          exact h2
        · have hne : (none : Option ↥I) ≠ j := fun hh => hj hh.symm
          have h1 : uniLeviHom h hε hI x none = 1 := by
            rw [← hyx]
            exact Pi.mulSingle_eq_of_ne (M := uniBlockGroup K s 1 I) hne y
          let z : HypIndex s 1 := Sum.inr (Sum.inl 0)
          rw [uniLeviHom_none] at h1
          have h2 := congrArg (fun g : GL (HypIndex s 1) K =>
            (g : Matrix (HypIndex s 1) (HypIndex s 1) K) z z) h1
          simp only [coe_resBlockHom, hxm, Matrix.submatrix_apply, Matrix.scalar_apply,
            Matrix.diagonal_apply_eq, Units.val_one, Matrix.one_apply_eq] at h2
          exact h2
      have hc1' : c = 1 := Units.ext hc1
      apply Subtype.ext
      apply Subtype.ext
      rw [hxc, hc1', map_one]
      rfl
  · have hxord : orderOf (x : hypSU h (t + s) ε) ∣ Nat.gcd (2 * (t + s) + ε) (2 ^ f + 1) := by
      rw [← card_hypScalars h (by omega)]
      exact Subgroup.orderOf_dvd_natCard _ hxs
    have hβ3 : (uniLeviHom h hε hI x) ^ p = 1 := by
      obtain ⟨y, hy, hyx⟩ := hβx
      rw [← hyx, ← map_pow, hE.2 y hy, map_one]
    have hβ1 : uniLeviHom h hε hI x = 1 := by
      by_contra hne
      have hordp : orderOf (uniLeviHom h hε hI x) = p := orderOf_eq_prime hβ3 hne
      have h3x : p ∣ orderOf x := hordp ▸ orderOf_map_dvd _ x
      rw [← Subgroup.orderOf_coe] at h3x
      exact h3 (h3x.trans hxord)
    have hker : x ∈ (uniLeviHom h hε hI).ker := hβ1
    obtain ⟨n, hn⟩ := isPGroup_ker_uniLeviHom h hε hI ⟨x, hker⟩
    have hx2 : x ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
    have hdvd2 : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hx2
    have hdvdq : orderOf x ∣ 2 ^ f + 1 := by
      rw [← Subgroup.orderOf_coe]
      exact hxord.trans (Nat.gcd_dvd_right _ _)
    have hcop : Nat.Coprime (2 ^ n) (2 ^ f + 1) := by
      apply Nat.Coprime.pow_left
      have hodd : Odd (2 ^ f + 1) :=
        (Nat.even_pow.2 ⟨even_two, by have := h.one_le; omega⟩).add_one
      exact Nat.coprime_two_left.2 hodd
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop hdvd2 hdvdq)

end LeviData

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndexP
