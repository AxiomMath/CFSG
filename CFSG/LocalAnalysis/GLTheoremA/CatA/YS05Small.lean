module

public import CFSG.LocalAnalysis.GLTheoremA.S6.Inputs6364
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultLie
public import CFSG.HardMathSupport.Timmesfeld.LinearRank.ProjRank
public import CFSG.RankThree.PartTwo.Sec4.Item413AutU3

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial

theorem card_le_prime_mul_card_inf {ℓ : ℕ} {X : Type*} [Group X] [Finite X] {B N C : Subgroup X}
    (hℓ : ℓ.Prime) (hB : CFSG.Open.IsElemAbelian ℓ B) (hC : IsCyclic C)
    (hCN : C ≤ Subgroup.normalizer (N : Set X))
    (hBNC : ∀ b ∈ B, ∃ n ∈ N, ∃ c ∈ C, b = n * c) :
    Nat.card B ≤ ℓ * Nat.card (B ⊓ N : Subgroup X) := by
  set P := Subgroup.normalizer (N : Set X)
  have hNP : N ≤ P := Subgroup.le_normalizer
  have hBP : B ≤ P := by
    intro b hb
    obtain ⟨n, hn, c, hc, rfl⟩ := hBNC b hb
    exact P.mul_mem (hNP hn) (hCN hc)
  have : (N.subgroupOf P).Normal := Subgroup.normal_in_normalizer
  set π := QuotientGroup.mk' (N.subgroupOf P)
  set ψ : B →* P ⧸ N.subgroupOf P := π.comp (Subgroup.inclusion hBP)
  set Cbar : Subgroup (P ⧸ N.subgroupOf P) := (C.subgroupOf P).map π
  have hCbar : IsCyclic Cbar := by
    have : IsCyclic (C.subgroupOf P) :=
      isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hCN).symm.toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hCN).symm.surjective
    have h := isCyclic_of_surjective (π.comp (C.subgroupOf P).subtype).rangeRestrict
      (π.comp (C.subgroupOf P).subtype).rangeRestrict_surjective
    have e : (π.comp (C.subgroupOf P).subtype).range = Cbar := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [e] at h
    exact h
  have hrange : ψ.range ≤ Cbar := by
    rintro _ ⟨b, rfl⟩
    obtain ⟨n, hn, c, hc, hbnc⟩ := hBNC b b.2
    refine ⟨⟨c, hCN hc⟩, Subgroup.mem_subgroupOf.mpr hc, ?_⟩
    change π ⟨c, hCN hc⟩ = π (Subgroup.inclusion hBP b)
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    rw [Subgroup.mem_subgroupOf]
    have : ((⟨c, hCN hc⟩ : P)⁻¹ * Subgroup.inclusion hBP b : P) = c⁻¹ * n * c := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, hbnc]
      group
    rw [this]
    have hcN : c⁻¹ ∈ P := P.inv_mem (hCN hc)
    have h := (Subgroup.mem_normalizer_iff.mp hcN n).mp hn
    rwa [inv_inv] at h
  have hcardℓ : Nat.card ψ.range ≤ ℓ := by
    have hcyc : IsCyclic ψ.range := by
      have : IsCyclic (ψ.range.subgroupOf Cbar) := Subgroup.isCyclic _
      have e := Subgroup.subgroupOfEquivOfLe hrange
      exact isCyclic_of_surjective e.toMonoidHom e.surjective
    have hexp : Monoid.exponent ψ.range ∣ ℓ := Monoid.exponent_dvd_of_forall_pow_eq_one
      fun y => by
        obtain ⟨b, hb⟩ := y.2
        apply Subtype.ext
        rw [Subgroup.coe_pow, ← hb, ← map_pow, Subgroup.coe_one]
        have : b ^ ℓ = 1 := Subtype.ext (by simpa using hB.2 b b.2)
        rw [this, map_one]
    rw [← IsCyclic.exponent_eq_card]
    exact Nat.le_of_dvd hℓ.pos hexp
  have hker : Nat.card ψ.ker = Nat.card (B ⊓ N : Subgroup X) := by
    have hk : ψ.ker = N.subgroupOf B := by
      ext b
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      change π (Subgroup.inclusion hBP b) = 1 ↔ _
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      rfl
    rw [hk, inf_comm]
    exact ((Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm.trans
      (by rw [Subgroup.inf_subgroupOf_right])).symm
  have hfirst : Nat.card B = Nat.card ψ.range * Nat.card ψ.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [hfirst, hker]
  exact Nat.mul_le_mul_right _ hcardℓ

theorem card_le_cube_mulAut_unitaryPSU {ℓ r f : ℕ} {K : Type} [Field K] [Finite K]
    {h : UnitaryFieldData r f K} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓK : ℓ ∣ Nat.card Kˣ)
    (hq : 2 < r ^ f) (B : Subgroup (MulAut (unitaryPSU h 3)))
    (hB : CFSG.Open.IsElemAbelian ℓ B) : Nat.card B ≤ ℓ ^ 3 := by
  set N := (psuConj h).range
  set C := (psuField h).range
  have hcycK := (card_ringAut_and_isCyclic h.prime K h.card).2
  have hcyc : IsCyclic C :=
    isCyclic_of_surjective (psuField h).rangeRestrict (psuField h).rangeRestrict_surjective
  have hCN : C ≤ Subgroup.normalizer (N : Set (MulAut (unitaryPSU h 3))) := by
    rintro _ ⟨σ, rfl⟩
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨A, rfl⟩ := hn
    exact ⟨_, (psuField_mul_psuConj_mul_inv σ A).symm⟩
  have hBNC : ∀ b ∈ B, ∃ n ∈ N, ∃ c ∈ C, b = n * c := by
    intro b _
    obtain ⟨A, σ, hAσ⟩ := exists_psuConj_mul_psuField hq b
    exact ⟨psuConj h A, ⟨A, rfl⟩, psuField h σ, ⟨σ, rfl⟩, hAσ⟩
  have hker : ∀ A : unitaryIsom3 h, psuConj h A = 1 ↔
      (A : GL (Fin 3) K) ∈ Subgroup.center (GL (Fin 3) K) := fun A => by
    rw [psuConj_eq_one_iff, Matrix.GeneralLinearGroup.center_eq_range_scalar]
    rfl
  have hBN : CFSG.Open.IsElemAbelian ℓ (B ⊓ N) := isElemAbelian_mono hB inf_le_left
  have hN := CFSG.HardMathSupport.Timmesfeld.LinearRank.card_le_of_scalar_kernel hℓ hℓ2 hℓK
    (by norm_num : 0 < 3) (unitaryIsom3 h)
    (psuConj h) hker (B ⊓ N) inf_le_right hBN
  have hN' : Nat.card (B ⊓ N : Subgroup _) ≤ ℓ ^ 2 := by simpa using hN
  have h1 := card_le_prime_mul_card_inf hℓ hB hcyc hCN hBNC
  calc Nat.card B ≤ ℓ * Nat.card (B ⊓ N : Subgroup _) := h1
    _ ≤ ℓ * ℓ ^ 2 := Nat.mul_le_mul_left _ hN'
    _ = ℓ ^ 3 := by ring

theorem i71U3At_holds (G : Type) [Group G] [Finite G] (p : ℕ) : I71U3At G p := by
  intro hp hp2 q hq hq2 hqp X L A hX hL hU hA hAN
  obtain ⟨Q, rfl, hdvd, hcat⟩ := hU
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic _ _ => exact (show False from hi).elim
  | alternating _ _ => exact (show False from hi).elim
  | sporadic _ => exact (show False from hi).elim
  | lie j =>
    obtain ⟨d, hv⟩ := j
    have hd : d = TauCeti.LieTypeIndex.twistedA 2 Q := hi
    subst hd
    have hQ3 : 3 ≤ Q.card := ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp
      ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1).2 rfl
    have hm := lieModel_twistedA' 2 Q hv e
    rcases hm.2 with hcl | ⟨h0, -⟩
    swap
    · exact absurd h0 (by norm_num)
    obtain ⟨-, K, hKf, hKfin, hKcard, ⟨eK⟩⟩ := hcl
    have hUK : UnitaryFieldData Q.p Q.exponent K :=
      ⟨Q.prime_p, Q.exponent_pos, by rw [hKcard, ← pow_mul, Nat.mul_comm]⟩
    have eU : CFSG.Yardstones.Md0ec50421ce4.PSimple p L ≃* unitaryPSU hUK 3 :=
      eK.trans (unitaryPSUEquiv hUK (by norm_num)).symm
    have hq3 : 2 < Q.p ^ Q.exponent := by
      have : Q.card = Q.p ^ Q.exponent := TauCeti.PrimePower.card_def Q
      omega
    have hℓK : p ∣ Nat.card Kˣ := by
      rw [Nat.card_units, hKcard]
      have hdvd' : p ∣ Q.p ^ Q.exponent + 1 := by
        rw [← TauCeti.PrimePower.card_def]
        exact hdvd
      obtain ⟨m, hm⟩ : ∃ m, Q.p ^ Q.exponent = m + 1 :=
        ⟨Q.p ^ Q.exponent - 1, by omega⟩
      rw [hm] at hdvd' ⊢
      rw [Nat.sub_eq_of_eq_add (show (m + 1) ^ 2 = m * (m + 1 + 1) + 1 by ring)]
      exact Dvd.dvd.mul_left hdvd' m
    have hbound : ∀ B : Subgroup (MulAut (unitaryPSU hUK 3)),
        CFSG.Open.IsElemAbelian p B → Nat.card B ≤ p ^ 3 :=
      fun B hB => card_le_cube_mulAut_unitaryPSU hp hp2 hℓK hq3 B hB
    let N : Subgroup G := Subgroup.normalizer (L : Set G)
    let H : Subgroup N := A.subgroupOf N
    let ψ : H →* MulAut (CFSG.Yardstones.Md0ec50421ce4.PSimple p L) :=
      (CFSG.LocalAnalysis.GLTheoremA.chevAut p L).comp H.subtype
    have hcardH : Nat.card H = Nat.card A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv
    have hsplit : Nat.card H = Nat.card ψ.range * Nat.card ψ.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
    have hf : Function.Injective (N.subtype.comp H.subtype) :=
      Subtype.val_injective.comp Subtype.val_injective
    have hmap : ψ.ker.map (N.subtype.comp H.subtype) =
        A ⊓ CFSG.LocalAnalysis.GLTheoremA.centModSubgroup p L := by
      ext g
      simp only [Subgroup.mem_map, MonoidHom.mem_ker, Subgroup.mem_inf]
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hx' : CFSG.LocalAnalysis.GLTheoremA.chevAut p L x.1 = 1 := hx
        have hcent : CFSG.Yardstones.Md0ec50421ce4.CentMod p L (x.1 : G) :=
          (CFSG.LocalAnalysis.GLTheoremA.chevAut_eq_one_iff hp hL x.1.2).1 hx'
        exact ⟨Subgroup.mem_subgroupOf.1 x.2,
          CFSG.LocalAnalysis.GLTheoremA.centMod_iff.1 hcent⟩
      · rintro ⟨hgA, hgC⟩
        have hgN : g ∈ N := (CFSG.LocalAnalysis.GLTheoremA.mem_centModSubgroup.1 hgC).1
        refine ⟨⟨⟨g, hgN⟩, Subgroup.mem_subgroupOf.2 hgA⟩, ?_, rfl⟩
        show CFSG.LocalAnalysis.GLTheoremA.chevAut p L ⟨g, hgN⟩ = 1
        exact (CFSG.LocalAnalysis.GLTheoremA.chevAut_eq_one_iff hp hL hgN).2
          (CFSG.LocalAnalysis.GLTheoremA.centMod_iff.2 hgC)
    have hkerCard : Nat.card ψ.ker =
        Nat.card ↥(A ⊓ CFSG.LocalAnalysis.GLTheoremA.centModSubgroup p L) := by
      rw [← hmap, Subgroup.card_map_of_injective hf]
    have hHcomm : ∀ x y : H, x * y = y * x := by
      intro x y
      have hxA : (x.1 : G) ∈ A := Subgroup.mem_subgroupOf.1 x.2
      have hyA : (y.1 : G) ∈ A := Subgroup.mem_subgroupOf.1 y.2
      have h1 := congrArg Subtype.val
        ((isMulCommutative_iff.mp hA.1) ⟨(x.1 : G), hxA⟩ ⟨(y.1 : G), hyA⟩)
      apply Subtype.ext
      apply Subtype.ext
      simpa using h1
    have hE0 : CFSG.Open.IsElemAbelian p ψ.range := by
      refine ⟨isMulCommutative_iff.mpr ?_, ?_⟩
      · rintro ⟨a, ha⟩ ⟨b, hb⟩
        obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 ha
        obtain ⟨y, rfl⟩ := MonoidHom.mem_range.1 hb
        apply Subtype.ext
        show ψ x * ψ y = ψ y * ψ x
        rw [← map_mul, ← map_mul, hHcomm x y]
      · intro a ha
        obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 ha
        have hxA : (x.1 : G) ∈ A := Subgroup.mem_subgroupOf.1 x.2
        have hxp : x ^ p = 1 := by
          apply Subtype.ext
          apply Subtype.ext
          simpa using hA.2 _ hxA
        rw [← map_pow, hxp, map_one]
    have hE1 : CFSG.Open.IsElemAbelian p (ψ.range.map (MulAut.congr eU).toMonoidHom) :=
      CFSG.SectionRank.isElemAbelian_map hE0 (MulAut.congr eU).toMonoidHom
    have hE1card : Nat.card (ψ.range.map (MulAut.congr eU).toMonoidHom) = Nat.card ψ.range := by
      rw [Subgroup.card_map_of_injective (MulAut.congr eU).injective]
    have hE0card : Nat.card ψ.range ≤ p ^ 3 := by
      have := hbound _ hE1
      rwa [hE1card] at this
    calc Nat.card A = Nat.card H := hcardH.symm
      _ = Nat.card ψ.range * Nat.card ψ.ker := hsplit
      _ ≤ p ^ 3 * Nat.card ψ.ker := Nat.mul_le_mul_right _ hE0card
      _ = p ^ 3 * Nat.card ↥(A ⊓ CFSG.LocalAnalysis.GLTheoremA.centModSubgroup p L) := by
        rw [hkerCard]

end CFSG.LocalAnalysis.GLTheoremA
