module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinearCyc
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinearEigen

public section

namespace CFSG.AGLEmbedding

namespace ToralCensus

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.AGLEmbedding.ParabPrime (perfectJoin perfectJoin_le)

variable {K : Type} [Field K] {n : ℕ}

omit [Field K] in
theorem exists_isConsecutiveCut_of_not_mem {I : Set ℕ} {k : ℕ} (hk0 : 0 < k) (hkn : k < n)
    (hk : k ∉ I) : ∃ a b, IsConsecutiveCut n I a b ∧ a < k ∧ k < b := by
  classical
  obtain ⟨a, hak, haI, hamax⟩ : ∃ a, a ≤ k ∧ (a = 0 ∨ a ∈ I) ∧ ∀ c ∈ I, c ≤ k → c ≤ a := by
    refine ⟨Nat.findGreatest (· ∈ I) k, Nat.findGreatest_le k, ?_,
      fun c hc hck => Nat.le_findGreatest hck hc⟩
    by_cases h0 : Nat.findGreatest (· ∈ I) k = 0
    · exact Or.inl h0
    · exact Or.inr (Nat.findGreatest_of_ne_zero rfl h0)
  have hex : ∃ c, k < c ∧ (c = n ∨ c ∈ I) := ⟨n, hkn, Or.inl rfl⟩
  obtain ⟨b, ⟨hkb, hbI⟩, hbn, hbmin⟩ : ∃ b, (k < b ∧ (b = n ∨ b ∈ I)) ∧ b ≤ n ∧
      ∀ c ∈ I, k < c → b ≤ c :=
    ⟨Nat.find hex, Nat.find_spec hex, Nat.find_min' hex ⟨hkn, Or.inl rfl⟩,
      fun c hc hkc => Nat.find_min' hex ⟨hkc, Or.inr hc⟩⟩
  have hak' : a < k := by
    refine lt_of_le_of_ne hak fun h => ?_
    rcases haI with h0 | hI
    · omega
    · exact hk (h ▸ hI)
  refine ⟨a, b, ⟨by omega, hbn, haI, hbI, fun c hc ⟨hac, hcb⟩ => ?_⟩, hak', hkb⟩
  rcases le_or_gt c k with hck | hck
  · exact absurd (hamax c hc hck) (by omega)
  · exact absurd (hbmin c hc hck) (by omega)

omit [Field K] in
theorem sub_lt_of_isConsecutiveCut {I : Set ℕ} (hI : ∀ i ∈ I, 1 ≤ i ∧ i < n) (hne : I.Nonempty)
    {a b : ℕ} (h : IsConsecutiveCut n I a b) : b - a < n := by
  obtain ⟨c, hc⟩ := hne
  have h1 := hI c hc
  have h2 := h.2.2.2.2 c hc
  have := h.1
  have := h.2.1
  omega

theorem dvd_card_sl_two_of_dvd [Finite K] {p : ℕ} (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) :
    p ∣ Nat.card (SpecialLinearGroup (Fin 2) K) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p
    (by rw [Nat.card_units]; exact hpK)
  have hω0 : (u : K) ≠ 0 := u.ne_zero
  have hωp : (u : K) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one, Units.val_one]
  have hω1 : (u : K) ≠ 1 := fun h1 => by
    rw [Units.val_eq_one.mp h1, orderOf_one] at hu
    exact hp.one_lt.ne hu
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  set s := LinearCover.diagElt (LinearCover.corootVec (0 : Fin 2) 1 (u : K))
    (LinearCover.prod_corootVec 0 1 hω0) with hs
  have hs1 : s ≠ 1 := fun h => hω1 (by
    have := congrArg (fun g : SpecialLinearGroup (Fin 2) K =>
      (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
    simpa [hs, LinearCover.coe_diagElt, LinearCover.corootVec_apply_left h01] using this)
  rw [← orderOf_eq_prime (diagElt_corootVec_pow_eq_one hω0 hωp) hs1]
  exact orderOf_dvd_natCard s

@[expose] def CycFlagPerfect (n : ℕ) (K : Type) [Field K] (I : Set ℕ) (p : ℕ) : Prop :=
  ∀ Q : Subgroup (SpecialLinearGroup (Fin n) K), Q ≤ perfectJoin (flagStabilizer n K I) →
    IsPGroup p Q → Q ⊓ Subgroup.center (SpecialLinearGroup (Fin n) K) = ⊥ → IsCyclic Q

theorem sub_le_two_of_cyc [Finite K] [CharP K 2] {I : Set ℕ} (hI : ∀ i ∈ I, 1 ≤ i ∧ i < n)
    (hne : I.Nonempty) {p : ℕ} (hp : p.Prime) (hpK : p ∣ Nat.card K - 1)
    (hcyc : CycFlagPerfect n K I p) {a b : ℕ} (h : IsConsecutiveCut n I a b) : b - a ≤ 2 := by
  by_contra hab
  obtain ⟨Q, hQ, hQp, hQZ, hQc⟩ := cycBlocksSL_holds K n I p hp
    (Or.inr (Or.inl ⟨a, b, h, by omega, sub_lt_of_isConsecutiveCut hI hne h, hpK⟩))
  exact hQc (hcyc Q hQ hQp hQZ)

theorem isConsecutiveCut_of_not_mem_of_cyc [Finite K] [CharP K 2] {I : Set ℕ}
    (hI : ∀ i ∈ I, 1 ≤ i ∧ i < n) (hne : I.Nonempty) {p : ℕ} (hp : p.Prime)
    (hpK : p ∣ Nat.card K - 1) (hcyc : CycFlagPerfect n K I p) {k : ℕ} (hk0 : 0 < k)
    (hkn : k < n) (hk : k ∉ I) : IsConsecutiveCut n I (k - 1) (k + 1) := by
  obtain ⟨a, b, h, hak, hkb⟩ := exists_isConsecutiveCut_of_not_mem hk0 hkn hk
  have h2 := sub_le_two_of_cyc hI hne hp hpK hcyc h
  obtain rfl : a = k - 1 := by omega
  obtain rfl : b = k + 1 := by omega
  exact h

theorem false_of_two_not_mem_of_cyc [Finite K] [CharP K 2] {I : Set ℕ}
    (hI : ∀ i ∈ I, 1 ≤ i ∧ i < n) (hne : I.Nonempty) {p : ℕ} (hp : p.Prime)
    (hK : 4 ≤ Nat.card K) (hpK : p ∣ Nat.card K - 1) (hcyc : CycFlagPerfect n K I p)
    {k k' : ℕ} (hk0 : 0 < k) (hkk' : k < k') (hk'n : k' < n) (hk : k ∉ I) (hk' : k' ∉ I) :
    False := by
  have h := isConsecutiveCut_of_not_mem_of_cyc hI hne hp hpK hcyc hk0 (by omega) hk
  have h' := isConsecutiveCut_of_not_mem_of_cyc hI hne hp hpK hcyc (by omega) hk'n hk'
  have hsep : k + 1 ≤ k' - 1 := by
    rcases h'.2.2.1 with h0 | hI'
    · omega
    · by_contra hlt
      exact hk (show k = k' - 1 by omega ▸ hI')
  have hsl : p ∣ Nat.card (SpecialLinearGroup (Fin 2) K) := dvd_card_sl_two_of_dvd hp hpK
  have e₁ : k + 1 - (k - 1) = 2 := by omega
  have e₂ : k' + 1 - (k' - 1) = 2 := by omega
  obtain ⟨Q, hQ, hQp, hQZ, hQc⟩ := cycBlocksSL_holds K n I p hp
    (Or.inl ⟨k - 1, k + 1, k' - 1, k' + 1, h, h', hsep, Or.inr ⟨e₁, hK⟩, Or.inr ⟨e₂, hK⟩,
      by rw [e₁]; exact hsl, by rw [e₂]; exact hsl⟩)
  exact hQc (hcyc Q hQ hQp hQZ)

theorem eq_of_not_mem_of_cyc [Finite K] [CharP K 2] {I : Set ℕ}
    (hI : ∀ i ∈ I, 1 ≤ i ∧ i < n) (hne : I.Nonempty) {p : ℕ} (hp : p.Prime)
    (hK : 4 ≤ Nat.card K) (hpK : p ∣ Nat.card K - 1) (hcyc : CycFlagPerfect n K I p)
    {k k' : ℕ} (hk0 : 0 < k) (hkn : k < n) (hk : k ∉ I) (hk'0 : 0 < k') (hk'n : k' < n)
    (hk' : k' ∉ I) : k' = k := by
  rcases lt_trichotomy k k' with hlt | heq | hgt
  · exact (false_of_two_not_mem_of_cyc hI hne hp hK hpK hcyc hk0 hlt hk'n hk hk').elim
  · exact heq.symm
  · exact (false_of_two_not_mem_of_cyc hI hne hp hK hpK hcyc hk'0 hgt hkn hk' hk).elim

theorem isConsecutiveCut_unit {I : Set ℕ} {i₀ : ℕ}
    (huniq : ∀ k, 0 < k → k < n → k ∉ I → k = i₀) {j : ℕ} (hjn : j < n) (hj1 : j + 1 ≠ i₀)
    (hj : j ≠ i₀) : IsConsecutiveCut n I j (j + 1) := by
  refine ⟨by omega, by omega, ?_, ?_, fun c _ hc => by omega⟩
  · rcases Nat.eq_zero_or_pos j with h0 | hpos
    · exact Or.inl h0
    · refine Or.inr (by_contra fun hjI => hj (huniq j hpos hjn hjI))
  · by_cases hjn' : j + 1 = n
    · exact Or.inl hjn'
    · refine Or.inr (by_contra fun hjI => hj1 (huniq (j + 1) (by omega) (by omega) hjI))

theorem pow_apply_self_eq_one {I : Set ℕ} {x : SpecialLinearGroup (Fin n) K}
    (hxI : x ∈ flagStabilizer n K I) {j : ℕ} (hj : IsConsecutiveCut n I j (j + 1))
    (hjn : j < n) (hxj : cutBlock (x : Matrix (Fin n) (Fin n) K) j (j + 1) hj.2.1 = 1)
    (i : ℕ) : ((x : Matrix (Fin n) (Fin n) K) ^ i) ⟨j, hjn⟩ ⟨j, hjn⟩ = 1 := by
  have hpow := map_pow (cutBlockHom (K := K) hj) ⟨x, hxI⟩ i
  rw [cutBlockHom_apply, cutBlockHom_apply] at hpow
  change cutBlock ((x ^ i : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) j (j + 1)
    hj.2.1 = cutBlock (x : Matrix (Fin n) (Fin n) K) j (j + 1) hj.2.1 ^ i at hpow
  rw [hxj, one_pow, Matrix.SpecialLinearGroup.coe_pow] at hpow
  have h := congrFun (congrFun hpow ⟨0, by omega⟩) ⟨0, by omega⟩
  rw [cutBlock_apply, Matrix.one_apply_eq] at h
  simpa using h

@[expose] noncomputable def unitFixedVec (p : ℕ) (X : Matrix (Fin n) (Fin n) K) (j : Fin n) :
    Fin n → K :=
  LinearThreeKit.fixedSum p X (Pi.single j 1)

theorem unitFixedVec_apply_self (p : ℕ) (X : Matrix (Fin n) (Fin n) K) (j : Fin n) :
    unitFixedVec p X j j = ∑ i ∈ Finset.range p, (X ^ i) j j := by
  rw [unitFixedVec, LinearThreeKit.fixedSum, Finset.sum_apply]
  simp

theorem unitFixedVec_mem_flagSpace {I : Set ℕ} {x : SpecialLinearGroup (Fin n) K}
    (hxI : x ∈ flagStabilizer n K I) {d : ℕ} (hd : d ∈ I) (p : ℕ) {j : Fin n}
    (hj : (j : ℕ) < d) :
    unitFixedVec p (x : Matrix (Fin n) (Fin n) K) j ∈ flagSpace n K d := by
  rw [unitFixedVec, LinearThreeKit.fixedSum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hxi : x ^ i ∈ stabilizer (flagSpace n K d) :=
    mem_flagStabilizer.mp (Subgroup.pow_mem _ hxI i) d hd
  rw [← Matrix.SpecialLinearGroup.coe_pow]
  exact (mem_stabilizer.mp hxi) ▸ ⟨_, single_mem_flagSpace_of_lt hj, rfl⟩

theorem natCast_ne_zero_of_odd_charTwo [CharP K 2] {p : ℕ} (hp : Odd p) : (p : K) ≠ 0 := by
  obtain ⟨k, rfl⟩ := hp
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, CharTwo.two_eq_zero, zero_mul, zero_add,
    Nat.cast_one]
  exact one_ne_zero

theorem false_of_unitBlocks [CharP K 2] {I : Set ℕ} {p : ℕ} (hp : Odd p)
    {x : SpecialLinearGroup (Fin n) K} (hxI : x ∈ flagStabilizer n K I) (hxp : x ^ p = 1)
    (hfix : Subgroup.centralizer ({x} : Set (SpecialLinearGroup (Fin n) K)) ≤
      flagStabilizer n K I)
    {k k' : ℕ} (hk : IsConsecutiveCut n I k (k + 1)) (hk' : IsConsecutiveCut n I k' (k' + 1))
    (hkk' : k < k') (hxk : cutBlock (x : Matrix (Fin n) (Fin n) K) k (k + 1) hk.2.1 = 1)
    (hxk' : cutBlock (x : Matrix (Fin n) (Fin n) K) k' (k' + 1) hk'.2.1 = 1) : False := by
  have hk'I : k' ∈ I := hk'.2.2.1.resolve_left (by omega)
  have hpK := natCast_ne_zero_of_odd_charTwo (K := K) hp
  have hkn : k < n := by have := hk.2.1; omega
  have hk'n : k' < n := by have := hk'.2.1; omega
  set X := (x : Matrix (Fin n) (Fin n) K) with hX
  have hXp : X ^ p = 1 := LinearThreeKit.coe_pow_eq_one hxp
  set j : Fin n := ⟨k, hkn⟩ with hj
  set j' : Fin n := ⟨k', hk'n⟩ with hj'
  set v := unitFixedVec p X j with hv
  set v' := unitFixedVec p X j' with hv'
  have hcoord : ∀ {m : ℕ} (hm : IsConsecutiveCut n I m (m + 1)) (hmn : m < n),
      cutBlock X m (m + 1) hm.2.1 = 1 → unitFixedVec p X ⟨m, hmn⟩ ⟨m, hmn⟩ = p := by
    intro m hm hmn hxm
    rw [unitFixedVec_apply_self, Finset.sum_congr rfl fun i _ =>
      pow_apply_self_eq_one hxI hm hmn hxm i, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
  have hvj : v j = p := hcoord hk hkn hxk
  have hvj' : v' j' = p := hcoord hk' hk'n hxk'
  set E := LinearMap.ker (Matrix.mulVecLin X - (1 : K) • LinearMap.id) with hE
  have hvE : v ∈ E := mem_ker_sub_smul_iff.mpr (by
    rw [one_smul]; exact LinearThreeKit.mulVec_fixedSum hXp _)
  have hv'E : v' ∈ E := mem_ker_sub_smul_iff.mpr (by
    rw [one_smul]; exact LinearThreeKit.mulVec_fixedSum hXp _)
  have hvF : v ∈ flagSpace n K k' := unitFixedVec_mem_flagSpace hxI hk'I p hkk'
  have hv0 : v ≠ 0 := fun h => hpK (by rw [← hvj, h, Pi.zero_apply])
  have hv'F : v' ∉ flagSpace n K k' := fun h =>
    hpK (by rw [← hvj', mem_flagSpace.mp h j' le_rfl])
  have hli := LinearThreeKit.linearIndependent_pair_of_notMem hvF hv0 hv'F
  have hdim : 2 ≤ Module.finrank K E := by
    have hspan : Submodule.span K (Set.range ![v, v']) ≤ E := by
      rw [Submodule.span_le, Set.range_subset_iff]
      intro i
      fin_cases i
      · exact hvE
      · exact hv'E
    have h2 := Submodule.finrank_mono hspan
    rwa [finrank_span_eq_card hli, Fintype.card_fin] at h2
  have hW : ∀ g ∈ Subgroup.centralizer ({x} : Set (SpecialLinearGroup (Fin n) K)),
      ∀ w ∈ flagSpace n K k', (g : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ flagSpace n K k' := by
    intro g hg w hw
    have hgs := mem_flagStabilizer.mp (hfix hg) k' hk'I
    exact (mem_stabilizer.mp hgs) ▸ ⟨w, hw, rfl⟩
  rcases eigenSpaceRigid_holds K n p hp x 1 1 (by rw [hXp, map_one]) hdim
      (flagSpace n K k') hW with h | h
  · exact hv0 ((Submodule.mem_bot K).mp (h ▸ ⟨hvF, hvE⟩))
  · exact hv'F (h hv'E)

theorem eq_three_of_cyc_fix [Finite K] [CharP K 2] {I : Set ℕ} (hI : ∀ i ∈ I, 1 ≤ i ∧ i < n)
    (hne : I.Nonempty) (hnb : ∃ i, 1 ≤ i ∧ i < n ∧ i ∉ I) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : 4 ≤ Nat.card K) (hpK : p ∣ Nat.card K - 1) (hcyc : CycFlagPerfect n K I p)
    {x : SpecialLinearGroup (Fin n) K} (hx : x ∈ perfectJoin (flagStabilizer n K I))
    (hxp : x ^ p ∈ Subgroup.center (SpecialLinearGroup (Fin n) K))
    (hfix : Subgroup.centralizer ({x} : Set (SpecialLinearGroup (Fin n) K)) ≤
      flagStabilizer n K I) : n = 3 := by
  obtain ⟨i₀, hi₀1, hi₀n, hi₀⟩ := hnb
  have huniq : ∀ k, 0 < k → k < n → k ∉ I → k = i₀ := fun k hk0 hkn hk =>
    eq_of_not_mem_of_cyc hI hne hp hK hpK hcyc (by omega) hi₀n hi₀ hk0 hkn hk
  obtain ⟨c, hc⟩ := hne
  have hc1 := hI c hc
  have hci : c ≠ i₀ := fun h => hi₀ (h ▸ hc)
  by_contra hn3
  obtain ⟨k, k', hkk', hk'n, hk1, hk0, hk'1, hk'0⟩ : ∃ k k', k < k' ∧ k' < n ∧ k + 1 ≠ i₀ ∧
      k ≠ i₀ ∧ k' + 1 ≠ i₀ ∧ k' ≠ i₀ := by
    rcases (show i₀ = 1 ∨ i₀ = 2 ∨ 3 ≤ i₀ by omega) with h | h | h
    · exact ⟨2, 3, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact ⟨0, 3, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact ⟨0, 1, by omega, by omega, by omega, by omega, by omega, by omega⟩
  have hk := isConsecutiveCut_unit huniq (by omega : k < n) hk1 hk0
  have hk' := isConsecutiveCut_unit huniq hk'n hk'1 hk'0
  have hxI : x ∈ flagStabilizer n K I := perfectJoin_le _ hx
  have hxk := (gradedPerfectSL_holds K n I x hx k (k + 1) hk).2 (Or.inl (by omega))
  have hxk' := (gradedPerfectSL_holds K n I x hx k' (k' + 1) hk').2 (Or.inl (by omega))
  have hxp1 : x ^ p = 1 := by
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hxp
    have h1 := pow_apply_self_eq_one hxI hk (by omega) hxk p
    rw [← Matrix.SpecialLinearGroup.coe_pow, ← hr, scalar_apply, diagonal_apply_eq] at h1
    refine Subtype.ext ?_
    rw [← hr, h1, map_one, Matrix.SpecialLinearGroup.coe_one]
  exact false_of_unitBlocks (hp.odd_of_ne_two hp2) hxI hxp1 hfix hk hk' hkk' hxk hxk'

end ToralCensus

end CFSG.AGLEmbedding
