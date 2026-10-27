module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResSpPairs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResLinOuter
public import CFSG.RankThree.Classical.SteinbergBYSymplecticFieldDescent
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.Open (IsElemAbelian)

section Weir

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem mem_of_pow_eq_one_of_index_dvd_two {G : Type*} [Group G] {H : Subgroup G}
    (hH : H.index ∣ 2) {m : ℕ} (hm : Odd m) {g : G} (hg : g ^ m = 1) : g ∈ H := by
  rcases (Nat.dvd_prime Nat.prime_two).1 hH with h1 | h2
  · rw [Subgroup.index_eq_one.1 h1]
    exact Subgroup.mem_top g
  · haveI : H.Normal := Subgroup.normal_of_index_eq_two h2
    have hq : (QuotientGroup.mk g : G ⧸ H) ^ m = 1 := by
      rw [← QuotientGroup.mk_pow, hg, QuotientGroup.mk_one]
    have h3 : orderOf (QuotientGroup.mk g : G ⧸ H) ∣ m := orderOf_dvd_of_pow_eq_one hq
    have h4 : orderOf (QuotientGroup.mk g : G ⧸ H) ∣ 2 := by
      have := orderOf_dvd_natCard (QuotientGroup.mk g : G ⧸ H)
      rwa [show Nat.card (G ⧸ H) = 2 from h2] at this
    have h5 : orderOf (QuotientGroup.mk g : G ⧸ H) = 1 := by
      have hcop : Nat.Coprime m 2 := by
        have : ¬ 2 ∣ m := by
          have := Nat.odd_iff.1 hm
          omega
        exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 this).symm
      exact Nat.eq_one_of_dvd_coprimes hcop h3 h4
    exact (QuotientGroup.eq_one_iff g).1 (orderOf_eq_one_iff.1 h5)

theorem le_of_elemAbelian_sp {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpc : ¬ p ∣ Nat.card K)
    {W : Subgroup (StatedSp n K)} (hW : IsElemAbelian p W) (hWc : Nat.card W = p ^ 2) :
    2 * orderOf (Nat.card K : ZMod p) ≤
      (if Even (orderOf (Nat.card K : ZMod p)) then 2 * n else n) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI := isElementaryAbelian_of_isElemAbelian hW
  have hcardK : Nat.card K = Fintype.card K := Nat.card_eq_fintype_card
  have hpK : ¬ p ∣ Fintype.card K := by rwa [← hcardK]
  rw [hcardK]
  set e := orderOf (Fintype.card K : ZMod p) with he
  by_contra hlt
  push Not at hlt
  have hz : ((Fintype.card K : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hpK
  have hpos : 0 < e := orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2
    ⟨p - 1, by have := hp.two_le; omega, ZMod.pow_card_sub_one_eq_one hz⟩)
  have hdiv : (if Even e then 2 * n else n) / e ≤ 1 := by
    have := (Nat.div_lt_iff_lt_mul hpos).2 (by omega : (if Even e then 2 * n else n) < 2 * e)
    omega
  obtain ⟨Q, hQ⟩ := (IsPGroup.of_card hWc).exists_le_sylow
  obtain ⟨P'⟩ : Nonempty (Sylow p (GL (Fin (if Even e then 2 * n else n)) K)) := inferInstance
  obtain ⟨φ⟩ := CFSG.GroupTheory.WeirSylow.sylow_Sp_mulEquiv_sylow_GL (hp.odd_of_ne_two hp2) K hpK
    n Q P'
  have hcyc' : IsCyclic P' :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.isCyclic_sylow_gl_of_div (hp.odd_of_ne_two hp2)
      hpc (by rw [hcardK]; exact hdiv) P'
  have hcycQ : IsCyclic Q := (MulEquiv.isCyclic φ).2 hcyc'
  have hcycW : IsCyclic W := isCyclic_of_injective (Subgroup.inclusion hQ)
    (Subgroup.inclusion_injective hQ)
  exact CFSG.IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hWc hcycW

theorem proj_injective_sp [CharP K 2] (hn : 1 ≤ n) : Function.Injective (proj n K) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  obtain ⟨c, hc, hc2⟩ := spScalars_sq hn ((QuotientGroup.eq_one_iff y).1 hy)
  have hc1 : c = 1 := by
    have h : ((c : K) - 1) ^ 2 = 0 := by
      have h2 : (c : K) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, hc2, Units.val_one]
      linear_combination h2 + (1 - (c : K)) * (CharP.cast_eq_zero K 2)
    exact Units.ext (sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h))
  apply Subtype.ext
  rw [hc, hc1, map_one]
  rfl

theorem exists_block_size_sp {p : ℕ} (hp : p.Prime) (hpc : ¬ p ∣ Nat.card K)
    (h2e : 2 * orderOf (Nat.card K : ZMod p) ≤
      (if Even (orderOf (Nat.card K : ZMod p)) then 2 * n else n)) :
    ∃ e' : ℕ, 1 ≤ e' ∧ 2 * e' ≤ n ∧ (p : ℤ) ∣ ((Nat.card K : ℤ) ^ 2) ^ e' - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hpos, -⟩ := orderOf_card_spec (K := K) hp hpc
  set e := orderOf (Nat.card K : ZMod p) with he
  have hpow : (Nat.card K : ZMod p) ^ e = 1 := pow_orderOf_eq_one _
  have hdvd : ∀ k : ℕ, (Nat.card K : ZMod p) ^ (2 * k) = 1 → (p : ℤ) ∣ ((Nat.card K : ℤ) ^ 2) ^ k - 1 := by
    intro k hk
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [← pow_mul, hk, sub_self]
  by_cases hev : Even e
  · obtain ⟨f, hf⟩ := hev
    rw [if_pos ⟨f, hf⟩] at h2e
    refine ⟨f, by omega, by omega, hdvd f ?_⟩
    rw [show 2 * f = e by omega]
    exact hpow
  · have hodd : ¬ Even e := hev
    rw [if_neg hodd] at h2e
    refine ⟨e, hpos, by omega, hdvd e ?_⟩
    rw [two_mul, pow_add, hpow, one_mul]

theorem sp_outer_fixesPair [CharP K 2] (hn : 2 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hge : ∃ E : Subgroup (StatedProj (StatedSp n K)), IsElemAbelian p E ∧ Nat.card E = p ^ 2)
    {α : MulAut (StatedProj (StatedSp n K))} (hα : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (StatedProj (StatedSp n K)))
    (hαp : α ^ p = 1) : FixesIndepPair p α := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨m, -, hm⟩ := FiniteField.card K 2
  have hcard : Nat.card K = 2 ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hm]
  have hpc : ¬ p ∣ Nat.card K := by
    intro hd
    rw [hcard] at hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  obtain ⟨-, -, -, -, -, -, -, hidx, hrel, hdesc⟩ :=
    CFSG.RankThree.Classical.SteinbergBY.symplectic_prime_semilinear_field_descent
      Nat.prime_two m.pos hn hcard
  have hα1 : α ≠ 1 := fun h => hα (h ▸ (CFSG.ComponentClassification.OuterAutomorphisms.inner (StatedProj (StatedSp n K))).one_mem)
  have hao : orderOf α = p := orderOf_eq_prime hαp hα1
  have haE : α ∈ spSemilinearAutGroup n K :=
    mem_of_pow_eq_one_of_index_dvd_two hidx (hp.odd_of_ne_two hp2) hαp
  have hgcd : Nat.gcd 2 (2 ^ (m : ℕ) - 1) = 1 := by
    obtain ⟨k, hk⟩ := dvd_pow_self 2 (Nat.pos_iff_ne_zero.1 m.pos)
    have hk1 : 1 ≤ k := by
      have : 0 < 2 ^ (m : ℕ) := pow_pos (by norm_num) _
      omega
    rcases (Nat.dvd_prime Nat.prime_two).1 (Nat.gcd_dvd_left 2 (2 ^ (m : ℕ) - 1)) with h | h
    · exact h
    · exfalso
      have h2 : 2 ∣ 2 ^ (m : ℕ) - 1 := by
        have := Nat.gcd_dvd_right 2 (2 ^ (m : ℕ) - 1)
        rwa [h] at this
      omega
  have hDle : spLinearAutGroup n K ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner (StatedProj (StatedSp n K)) :=
    Subgroup.relIndex_eq_one.1 (Nat.dvd_one.1 (hgcd ▸ hrel))
  have haD : α ∉ spLinearAutGroup n K := fun h => hα (hDle h)
  obtain ⟨-, σ, hσo, -, h, -, hah⟩ := hdesc p hp α haE haD hao
  have hσp : σ ^ p = 1 := by rw [← hσo]; exact pow_orderOf_eq_one σ
  obtain ⟨E, hE, hEc⟩ := hge
  let e₀ : StatedSp n K ≃* StatedProj (StatedSp n K) :=
    MulEquiv.ofBijective (proj n K) ⟨proj_injective_sp (by omega), QuotientGroup.mk'_surjective _⟩
  have hWc : Nat.card (E.map e₀.symm.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective e₀.symm.injective]
    exact hEc
  have h2e := le_of_elemAbelian_sp hp hp2 hpc
    (CFSG.Open.IsElemAbelian.map hE e₀.symm.toMonoidHom) hWc
  obtain ⟨e', he', hn', hpe⟩ := exists_block_size_sp hp hpc h2e
  have hdvd := dvd_card_statedSp_of_dvd (K := K) he' hpe
  obtain ⟨x₁, x₂, hc, h1, h2, hi, hf1, hf2⟩ := exists_two_indep_fixed_sp (K := K) hp hp2 he' hn' hdvd hσp
  have hpair : FixesIndepPair p (fieldAut n K σ) := ⟨x₁, x₂, hc, h1, h2, hi, hf1, hf2⟩
  rw [hah]
  exact hpair.map h

end Weir

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
