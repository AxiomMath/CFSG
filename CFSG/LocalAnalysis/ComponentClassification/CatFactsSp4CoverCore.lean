module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Classify
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Order
public import CFSG.Dihedral.BrauerSuzuki
public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneQuaternionRecognition
public import CFSG.Dihedral.DisconnectedInvolutionGraph.CyclicSylowOddComplement
public import CFSG.GH74.GLS.AssemblyComponents

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsSp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag Subgroup
open scoped commutatorElement

section FourGroup

variable {K : Type} [Field K]

variable (K) in
@[expose] def negS : StatedSp 2 K := toSp (-1) neg_one_symplectic

theorem coe_negS : (((negS K : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = -1 := rfl

theorem eq_negS_of_coe {x : StatedSp 2 K}
    (h : ((x : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = -1) :
    x = negS K := sp_ext h

theorem exists_conj_T1_of_sq (h2 : (2 : K) ≠ 0) {x : StatedSp 2 K} (hx : x * x = 1) (hx1 : x ≠ 1)
    (hxn : x ≠ negS K) : ∃ g : StatedSp 2 K, g⁻¹ * x * g = T1 K := by
  apply exists_conj_T1 h2 x
  · have := congrArg (fun y : StatedSp 2 K =>
      ((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hx
    simpa using this
  · intro h
    exact hx1 (sp_ext h)
  · intro h
    exact hxn (sp_ext h)

theorem eq_of_commute_T1 (h2 : (2 : K) ≠ 0) {y : StatedSp 2 K} (hy : y * y = 1)
    (hyT : y * T1 K = T1 K * y) :
    y = 1 ∨ y = negS K ∨ y = T1 K ∨ y = negS K * T1 K := by
  obtain ⟨⟨a, b⟩, rfl⟩ := (mem_centralizer_T1_iff h2).mp (mem_centralizer_singleton_iff.mpr hyT)
  have hab := congrArg (fun y : StatedSp 2 K =>
    ((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hy
  simp only [Subgroup.coe_mul, Units.val_mul, coe_blkSL, blk_mul, OneMemClass.coe_one,
    Units.val_one] at hab
  rw [← blk_one_one] at hab
  obtain ⟨ha, hb⟩ := blk_injective _ _ _ _ hab
  rcases eq_one_or_neg_one_of_sq h2 a.2 ha with ha' | ha' <;>
    rcases eq_one_or_neg_one_of_sq h2 b.2 hb with hb' | hb'
  · left
    exact sp_ext (by rw [coe_blkSL, ha', hb', blk_one_one]; rfl)
  · right; right; left
    exact sp_ext (by rw [coe_blkSL, ha', hb', coe_T1])
  · right; right; right
    apply sp_ext
    rw [coe_blkSL, ha', hb', Subgroup.coe_mul, Units.val_mul, coe_negS, coe_T1, Matrix.neg_mul,
      Matrix.one_mul, blk_neg, neg_neg]
  · right; left
    exact sp_ext (by rw [coe_blkSL, ha', hb', coe_negS, blk_neg_one_neg_one])

theorem neg_one_mem_of_four_group (h2 : (2 : K) ≠ 0) {x y : StatedSp 2 K} (hx : x * x = 1)
    (hy : y * y = 1) (hxy : x * y = y * x) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hne : x ≠ y) :
    x = negS K ∨ y = negS K ∨ x * y = negS K := by
  by_cases hxn : x = negS K
  · exact Or.inl hxn
  obtain ⟨g, hg⟩ := exists_conj_T1_of_sq h2 hx hx1 hxn
  set y' := g⁻¹ * y * g with hy'
  have hy'2 : y' * y' = 1 := by
    rw [hy']
    calc g⁻¹ * y * g * (g⁻¹ * y * g) = g⁻¹ * (y * y) * g := by group
      _ = 1 := by rw [hy, mul_one, inv_mul_cancel]
  have hy'T : y' * T1 K = T1 K * y' := by
    rw [← hg, hy']
    calc g⁻¹ * y * g * (g⁻¹ * x * g) = g⁻¹ * (y * x) * g := by group
      _ = g⁻¹ * (x * y) * g := by rw [hxy]
      _ = g⁻¹ * x * g * (g⁻¹ * y * g) := by group
  have hneg : ∀ z : StatedSp 2 K, g⁻¹ * z * g = negS K → z = negS K := by
    intro z hz
    have hc : negS K ∈ center (StatedSp 2 K) :=
      mem_center_of_mem_spScalars ((mem_spScalars_iff _).mpr (Or.inr rfl))
    have := mem_center_iff.mp hc g
    calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      _ = g * negS K * g⁻¹ := by rw [hz]
      _ = negS K := by rw [this, mul_inv_cancel_right]
  rcases eq_of_commute_T1 h2 hy'2 hy'T with h | h | h | h
  · exfalso
    apply hy1
    calc y = g * y' * g⁻¹ := by rw [hy']; group
      _ = 1 := by rw [h, mul_one, mul_inv_cancel]
  · exact Or.inr (Or.inl (hneg y h))
  · exfalso
    apply hne
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = g * y' * g⁻¹ := by rw [hg, h]
      _ = y := by rw [hy']; group
  · right; right
    apply hneg
    have hc : negS K ∈ center (StatedSp 2 K) :=
      mem_center_of_mem_spScalars ((mem_spScalars_iff _).mpr (Or.inr rfl))
    have hT2 : T1 K * T1 K = 1 := by
      apply sp_ext
      rw [Subgroup.coe_mul, Units.val_mul, coe_T1, blk_mul]
      simp [blk_one_one]
    calc g⁻¹ * (x * y) * g = (g⁻¹ * x * g) * y' := by rw [hy']; group
      _ = T1 K * (negS K * T1 K) := by rw [hg, h]
      _ = negS K * (T1 K * T1 K) := by
          rw [← mul_assoc, (mem_center_iff.mp hc (T1 K)), mul_assoc]
      _ = negS K := by rw [hT2, mul_one]

end FourGroup

section Abstract

open CFSG.DisconnectedInvolutionGraph.Helpers in
theorem helpersOddCore_eq (M : Type*) [Group M] :
    CFSG.DisconnectedInvolutionGraph.Helpers.oddCore M = pPrimeCore 2 M := by
  unfold CFSG.DisconnectedInvolutionGraph.Helpers.oddCore CFSG.pPrimeCore
  congr 1
  ext N
  simp [Nat.coprime_two_left]

theorem oddCore_eq_pPrimeCore' (M : Type*) [Group M] : CFSG.oddCore M = pPrimeCore 2 M := by
  unfold CFSG.oddCore CFSG.pPrimeCore
  congr 1
  ext N
  simp [Nat.coprime_two_left]

variable {M : Type*} [Group M] [Finite M]

omit [Finite M] in
theorem mk_mem_center_iff (N : Subgroup M) [N.Normal] (z : M) :
    (QuotientGroup.mk z : M ⧸ N) ∈ center (M ⧸ N) ↔ ∀ g : M, z * g * z⁻¹ * g⁻¹ ∈ N := by
  rw [mem_center_iff]
  constructor
  · intro h g
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, ← h,
      mul_inv_cancel_right, mul_inv_cancel]
  · intro h g
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
    have h1 := (QuotientGroup.eq_one_iff _).mpr (h g')
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv] at h1
    have h2 : (QuotientGroup.mk z : M ⧸ N) * QuotientGroup.mk g' =
        QuotientGroup.mk g' * QuotientGroup.mk z := by
      calc (QuotientGroup.mk z : M ⧸ N) * QuotientGroup.mk g' =
          (QuotientGroup.mk z * QuotientGroup.mk g' * (QuotientGroup.mk z)⁻¹ *
            (QuotientGroup.mk g')⁻¹) * (QuotientGroup.mk g' * QuotientGroup.mk z) := by group
        _ = QuotientGroup.mk g' * QuotientGroup.mk z := by rw [h1, one_mul]
    exact h2.symm

theorem center_quotient_ne_bot_of {z : M} (hz : orderOf z = 2)
    (hzc : (QuotientGroup.mk z : M ⧸ pPrimeCore 2 M) ∈ center (M ⧸ pPrimeCore 2 M)) :
    center (M ⧸ pPrimeCore 2 M) ≠ ⊥ := by
  intro h
  rw [h, mem_bot, QuotientGroup.eq_one_iff] at hzc
  have hcop := pPrimeCore_coprime_card (p := 2) (G := M)
  have hdvd := orderOf_dvd_natCard (⟨z, hzc⟩ : pPrimeCore 2 M)
  rw [Subgroup.orderOf_mk, hz] at hdvd
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hcop hdvd

omit [Finite M] in
theorem mk_mem_center {z : M} (hz : z ∈ center M) :
    (QuotientGroup.mk z : M ⧸ pPrimeCore 2 M) ∈ center (M ⧸ pPrimeCore 2 M) := by
  rw [mem_center_iff]
  intro g
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.mp hz g']

theorem center_quotient_ne_bot (hperf : Group.IsPerfect M) (heven : Even (Nat.card M))
    (hK : ∀ x y : M, orderOf x = 2 → orderOf y = 2 → x * y = y * x → x ≠ y →
      ∃ w ∈ center M, orderOf w = 2) :
    center (M ⧸ pPrimeCore 2 M) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hrank : ∃ x y : M, orderOf x = 2 ∧ orderOf y = 2 ∧ x * y = y * x ∧ x ≠ y
  · obtain ⟨x, y, hx, hy, hxy, hne⟩ := hrank
    obtain ⟨w, hw, hw2⟩ := hK x y hx hy hxy hne
    exact center_quotient_ne_bot_of hw2 (mk_mem_center hw)
  push Not at hrank
  obtain ⟨T⟩ : Nonempty (Sylow 2 M) := inferInstance
  have hT2 : IsPGroup 2 (T : Subgroup M) := T.isPGroup'
  have hTrank : CFSG.DisconnectedInvolutionGraph.Helpers.NoCommutingDistinctInvolutions
      (T : Subgroup M) := by
    intro a b hab
    exact Subtype.ext (Subtype.ext (hrank ((a : T) : M) ((b : T) : M)
      (by rw [Subgroup.orderOf_coe]; exact a.2) (by rw [Subgroup.orderOf_coe]; exact b.2)
      (congrArg Subtype.val hab)))
  have hdvd : 2 ∣ Nat.card (T : Subgroup M) := by
    have hne := T.ne_bot_of_dvd_card (even_iff_two_dvd.mp heven)
    have : Nontrivial (T : Subgroup M) := (nontrivial_iff_ne_bot _).mpr hne
    rcases hT2.card_eq_or_dvd with h | h
    · exact absurd h Finite.one_lt_card.ne'
    · exact h
  by_cases hab : ∀ a b : (T : Subgroup M), a * b = b * a
  · exfalso
    let _ : CommGroup (T : Subgroup M) := { mul_comm := hab }
    have hcyc := CFSG.DisconnectedInvolutionGraph.Helpers.rank_one_abelian_two_group_cyclic
      (T : Subgroup M) hT2 hTrank
    have hcomp := CFSG.DisconnectedInvolutionGraph.Helpers.cyclic_two_sylow_oddCore_complement
      T hcyc heven
    rw [helpersOddCore_eq] at hcomp
    have hsup : (pPrimeCore 2 M ⊔ (T : Subgroup M) : Subgroup M) = ⊤ := hcomp.sup_eq_top
    have hcommut : ⁅(⊤ : Subgroup M), ⊤⁆ ≤ pPrimeCore 2 M := by
      rw [commutator_le]
      intro g₁ _ g₂ _
      have hdec : ∀ g : M, ∃ n ∈ pPrimeCore 2 M, ∃ s ∈ (T : Subgroup M), n * s = g := by
        intro g
        have hg : g ∈ ((pPrimeCore 2 M ⊔ (T : Subgroup M) : Subgroup M) : Set M) := by
          rw [hsup]
          trivial
        rw [Subgroup.normal_mul] at hg
        obtain ⟨n, hn, s, hs, hns⟩ := hg
        exact ⟨n, hn, s, hs, hns⟩
      obtain ⟨n₁, hn₁, s₁, hs₁, rfl⟩ := hdec g₁
      obtain ⟨n₂, hn₂, s₂, hs₂, rfl⟩ := hdec g₂
      rw [← QuotientGroup.eq_one_iff]
      change QuotientGroup.mk' (pPrimeCore 2 M) ⁅n₁ * s₁, n₂ * s₂⁆ = 1
      have hc : s₁ * s₂ = s₂ * s₁ := congrArg Subtype.val (hab ⟨s₁, hs₁⟩ ⟨s₂, hs₂⟩)
      have e₁ : QuotientGroup.mk' (pPrimeCore 2 M) n₁ = 1 :=
        (QuotientGroup.eq_one_iff (N := pPrimeCore 2 M) n₁).mpr hn₁
      have e₂ : QuotientGroup.mk' (pPrimeCore 2 M) n₂ = 1 :=
        (QuotientGroup.eq_one_iff (N := pPrimeCore 2 M) n₂).mpr hn₂
      rw [map_commutatorElement, map_mul, map_mul, e₁, e₂, one_mul, one_mul,
        ← map_commutatorElement, commutatorElement_eq_one_iff_mul_comm.mpr hc, map_one]
    have htop : (⊤ : Subgroup M) ≤ pPrimeCore 2 M := by
      have h1 : commutator M = ⊤ := Group.isPerfect_def.mp hperf
      rw [← h1, _root_.commutator_def]
      exact hcommut
    have hcard : Nat.card (pPrimeCore 2 M) = Nat.card M := by
      rw [top_le_iff.mp htop, Subgroup.card_top]
    have hcop := pPrimeCore_coprime_card (p := 2) (G := M)
    rw [hcard, Nat.coprime_two_left] at hcop
    exact (Nat.not_even_iff_odd.mpr hcop) heven
  · push Not at hab
    obtain ⟨a, b, hab⟩ := hab
    obtain ⟨e, he, ⟨φ⟩⟩ :=
      CFSG.DisconnectedInvolutionGraph.Helpers.rank_one_two_nonabelian_quaternion
        hT2 hTrank ⟨a, b, hab⟩
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
    have hBS := CFSG.BrauerSuzuki.brauer_suzuki (e + 2) (by omega) T
      ⟨by rw [Nat.add_sub_cancel]; exact φ.symm⟩ (t : M) t.2 (by rw [Subgroup.orderOf_coe, ht])
    have key := (mk_mem_center_iff _ _).mp hBS
    simp only [oddCore_eq_pPrimeCore'] at key
    exact center_quotient_ne_bot_of (by rw [Subgroup.orderOf_coe, ht])
      ((mk_mem_center_iff _ _).mpr key)

theorem even_card_of_isPComponent {X : Type*} [Group X] [Finite X] {L : Subgroup X}
    (hL : CFSG.IsPComponent 2 L) : Even (Nat.card L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hK, hsub, hmap, -⟩ := hL
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  have hle : L ≤ pPrimeCore 2 X :=
    CFSG.GH74.GLS.le_pPrimeCore_of_subnormal 2 hsub (Nat.coprime_two_left.mpr hodd)
  have hK' : K = ⊥ := by
    rw [← hmap, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hle
  subst hK'
  obtain ⟨-, -, a, b, hab⟩ := hK.1
  have : Subsingleton (↥(⊥ : Subgroup (X ⧸ pPrimeCore 2 X)) ⧸
      center ↥(⊥ : Subgroup (X ⧸ pPrimeCore 2 X))) := by
    constructor
    intro u v
    obtain ⟨u', rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨v', rfl⟩ := QuotientGroup.mk_surjective v
    rw [Subsingleton.elim u' v']
  exact hab (Subsingleton.elim _ _)

end Abstract

end CFSG.ComponentClassification.CatFactsSp4
