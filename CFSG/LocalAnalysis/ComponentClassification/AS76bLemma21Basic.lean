module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bInputs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Basic
public import CFSG.LocalAnalysis.ComponentClassification.SolvableKernelContainment
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore

public section

namespace CFSG.ComponentClassification.AS76b

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

section OddCore

theorem assemblyOddCore_eq_helpers (H : Type*) [Group H] :
    CFSG.Assembly.oddCore H = CFSG.DisconnectedInvolutionGraph.Helpers.oddCore H := rfl

theorem odd_card_assemblyOddCore (H : Type*) [Group H] [Finite H] :
    Odd (Nat.card (CFSG.Assembly.oddCore H)) :=
  CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd

theorem assemblyOddCore_characteristic (H : Type*) [Group H] [Finite H] :
    (CFSG.Assembly.oddCore H).Characteristic :=
  CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_characteristic

theorem le_assemblyOddCore {H : Type*} [Group H] {N : Subgroup H} (hN : N.Normal)
    (hodd : Odd (Nat.card N)) : N ≤ CFSG.Assembly.oddCore H :=
  CFSG.DisconnectedInvolutionGraph.Helpers.normal_odd_le_oddCore N hN hodd

theorem assemblyOddCore_eq_pPrimeCore (H : Type*) [Group H] :
    CFSG.Assembly.oddCore H = CFSG.pPrimeCore 2 H := by
  unfold CFSG.Assembly.oddCore CFSG.pPrimeCore
  congr 1
  ext N
  simp only [Set.mem_ofPred_eq, Nat.coprime_two_left]

variable {G : Type} [Group G]

theorem oddCoreIn_le (K : Subgroup G) : oddCoreIn K ≤ K :=
  map_subtype_le _

theorem odd_card_oddCoreIn [Finite G] (K : Subgroup G) : Odd (Nat.card (oddCoreIn K)) := by
  rw [oddCoreIn, card_map_of_injective K.subtype_injective]
  exact odd_card_assemblyOddCore K

theorem le_normalizer_map_subtype_of_normal (K : Subgroup G) (N : Subgroup K) [N.Normal] :
    K ≤ normalizer ((N.map K.subtype : Subgroup G) : Set G) := by
  have h := Subgroup.le_normalizer_map (H := N) K.subtype
  rw [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  exact h

theorem mem_normalizer_of_map_conj_eq {X : Subgroup G} {w : G}
    (h : X.map (MulAut.conj w).toMonoidHom = X) : w ∈ normalizer (X : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hyx' : w * y * w⁻¹ = w * x * w⁻¹ := hyx
    have : y = x := by simpa using hyx'
    exact this ▸ hy

theorem mem_normalizer_of_map_conj_le [Finite G] {X : Subgroup G} {w : G}
    (h : X.map (MulAut.conj w).toMonoidHom ≤ X) : w ∈ normalizer (X : Set G) :=
  mem_normalizer_of_map_conj_eq (eq_of_le_of_card_ge h
    (le_of_eq (card_map_of_injective (MulAut.conj w).injective).symm))

theorem map_conj_map_subtype_of_characteristic {K : Subgroup G} (C : Subgroup K)
    [hC : C.Characteristic] {w : G} (hw : w ∈ normalizer (K : Set G)) :
    (C.map K.subtype).map (MulAut.conj w).toMonoidHom = C.map K.subtype := by
  let φ : K ≃* K :=
    { toFun := fun k => ⟨w * k * w⁻¹, (mem_normalizer_iff.mp hw k).mp k.2⟩
      invFun := fun k => ⟨w⁻¹ * k * w, by
        simpa using (mem_normalizer_iff.mp (inv_mem hw) k).mp k.2⟩
      left_inv := fun k => Subtype.ext (by simp [mul_assoc])
      right_inv := fun k => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp only [coe_mul]; group) }
  have h1 : (MulAut.conj w).toMonoidHom.comp K.subtype = K.subtype.comp φ.toMonoidHom := by
    ext k
    rfl
  rw [map_map, h1, ← map_map, characteristic_iff_map_eq.mp hC φ]

theorem normalizer_le_normalizer_oddCoreIn [Finite G] (K : Subgroup G) :
    normalizer (K : Set G) ≤ normalizer (oddCoreIn K : Set G) := fun w hw => by
  have := assemblyOddCore_characteristic K
  exact mem_normalizer_of_map_conj_eq (map_conj_map_subtype_of_characteristic _ hw)

theorem le_normalizer_oddCoreIn (K : Subgroup G) :
    K ≤ normalizer (oddCoreIn K : Set G) :=
  le_normalizer_map_subtype_of_normal K _

theorem eq_bot_of_isPGroup_of_odd [Finite G] {H : Subgroup G} (hH : IsPGroup 2 H)
    (hodd : Odd (Nat.card H)) : H = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hH
  rcases n with _ | n
  · exact card_eq_one.mp (by simpa using hn)
  · rw [hn, pow_succ] at hodd
    exact absurd hodd (by simp [Nat.not_odd_iff_even, parity_simps])

theorem oddCoreIn_inf_eq_bot [Finite G] {K R : Subgroup G} (hR : IsPGroup 2 R) :
    oddCoreIn K ⊓ R = ⊥ :=
  eq_bot_of_isPGroup_of_odd (hR.to_le inf_le_right)
    ((odd_card_oddCoreIn K).of_dvd_nat (card_dvd_of_le inf_le_left))

end OddCore

section Sylow

variable {G : Type} [Group G] [Finite G]

theorem isPGroup_zpowers_of_pow_eq_one {H : Type*} [Group H] {x : H} {n : ℕ}
    (hx : x ^ 2 ^ n = 1) : IsPGroup 2 (zpowers x) := by
  rintro ⟨y, m, rfl⟩
  refine ⟨n, Subtype.ext ?_⟩
  change (x ^ m) ^ 2 ^ n = 1
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

theorem exists_conj_mem_of_isSylowOf {P K : Subgroup G} (hP : IsSylowOf 2 P K) {q : G}
    (hqK : q ∈ K) {n : ℕ} (hq : q ^ 2 ^ n = 1) : ∃ a ∈ K, a * q * a⁻¹ ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hP.exists_sylow_eq_subgroupOf
  have hq' : (⟨q, hqK⟩ : K) ^ 2 ^ n = 1 := Subtype.ext (by simpa using hq)
  obtain ⟨Q', hQ'⟩ := (isPGroup_zpowers_of_pow_eq_one hq').exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q' Q
  have h1 : (⟨q, hqK⟩ : K) ∈ (Q' : Subgroup K) := hQ' (mem_zpowers _)
  have h2 : MulAut.conj g • (⟨q, hqK⟩ : K) ∈ ((g • Q' : Sylow 2 K) : Subgroup K) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ h1
  rw [hg, hQ, mem_subgroupOf] at h2
  exact ⟨g, g.2, by simpa [MulAut.smul_def, MulAut.conj_apply] using h2⟩

theorem pow_dvd_card_of_isSylowOf {P K : Subgroup G} (hP : IsSylowOf 2 P K) {j : ℕ}
    (hj : 2 ^ j ∣ Nat.card K) : 2 ^ j ∣ Nat.card P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [hP.card_eq]
  exact pow_dvd_pow 2 ((Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hj)

theorem two_dvd_card_of_isSylowOf {P K : Subgroup G} (hP : IsSylowOf 2 P K)
    (hK : Even (Nat.card K)) : 2 ∣ Nat.card P := by
  simpa using pow_dvd_card_of_isSylowOf hP (j := 1) (by simpa using even_iff_two_dvd.mp hK)

end Sylow

section Tight

variable {G : Type} [Group G] [Finite G]

theorem tightlyEmbedded_of_conj_mem {K X R : Subgroup G} (hK : TightlyEmbedded K)
    (hXK : X ≤ K) (hR : IsSylowOf 2 R K) (hRX : R ≤ X)
    (hTI : ∀ w ∈ normalizer (K : Set G), ∀ r ∈ R, r ≠ 1 → w * r * w⁻¹ ∈ R →
      w ∈ normalizer (X : Set G)) :
    TightlyEmbedded X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRX' : IsSylowOf 2 R X := hR.of_le hRX hXK
  refine ⟨even_iff_two_dvd.mpr ((two_dvd_card_of_isSylowOf hR hK.1).trans (card_dvd_of_le hRX)),
    fun x hx => ?_⟩
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  by_cases hxK : x ∈ normalizer (K : Set G)
  ·
    obtain ⟨⟨q, hq⟩, hq2⟩ := exists_prime_orderOf_dvd_card' (G := ↥(X ⊓ rightConjugate X x)) 2
      (even_iff_two_dvd.mp hev)
    rw [Subgroup.orderOf_mk] at hq2
    have hq1 : q ≠ 1 := by
      rintro rfl
      simp at hq2
    have hqpow : q ^ 2 ^ 1 = 1 := by
      rw [pow_one, ← hq2]
      exact pow_orderOf_eq_one q
    obtain ⟨a, haX, haR⟩ := exists_conj_mem_of_isSylowOf hRX' hq.1 hqpow
    obtain ⟨b, hbX, hbR⟩ := exists_conj_mem_of_isSylowOf
      (AschbacherTheorem3.isSylowOf_rightConjugate hRX' x) hq.2 hqpow
    rw [mem_rightConjugate_iff] at hbR hbX
    have hbK : b ∈ K := by
      have h := (mem_normalizer_iff.mp (inv_mem hxK) _).mp (hXK hbX)
      simpa [mul_assoc] using h
    have hwK : x * b * a⁻¹ ∈ normalizer (K : Set G) :=
      mul_mem (mul_mem hxK (le_normalizer hbK)) (inv_mem (le_normalizer (hXK haX)))
    have hr1 : a * q * a⁻¹ ≠ 1 := fun h => hq1 (by simpa using h)
    have hwr : (x * b * a⁻¹) * (a * q * a⁻¹) * (x * b * a⁻¹)⁻¹ ∈ R := by
      have heq : (x * b * a⁻¹) * (a * q * a⁻¹) * (x * b * a⁻¹)⁻¹ = x * (b * q * b⁻¹) * x⁻¹ := by
        group
      rw [heq]
      exact hbR
    have hwX := hTI _ hwK _ haR hr1 hwr
    have hcX : x * b⁻¹ * x⁻¹ ∈ normalizer (X : Set G) := by
      refine le_normalizer ?_
      have h := X.inv_mem hbX
      simpa [mul_assoc] using h
    have hmem := mul_mem (mul_mem hcX hwX) (le_normalizer haX)
    have heq : x * b⁻¹ * x⁻¹ * (x * b * a⁻¹) * a = x := by group
    rw [heq] at hmem
    exact hx hmem
  · have hle : X ⊓ rightConjugate X x ≤ K ⊓ rightConjugate K x :=
      inf_le_inf hXK (AschbacherTheorem3.rightConjugate_le_rightConjugate hXK x)
    exact (Nat.not_odd_iff_even.mpr hev) ((hK.2 x hxK).of_dvd_nat (card_dvd_of_le hle))

theorem map_conj_le_of_map_conj_le {K R : Subgroup G} {w : G} (hw : w ∈ normalizer (K : Set G))
    (hR : R.map (MulAut.conj w).toMonoidHom ≤ oddCoreIn K ⊔ R) :
    (oddCoreIn K ⊔ R).map (MulAut.conj w).toMonoidHom ≤ oddCoreIn K ⊔ R := by
  rw [Subgroup.map_sup]
  refine sup_le ?_ hR
  rintro _ ⟨o, ho, rfl⟩
  exact mem_sup_left ((mem_normalizer_iff.mp (normalizer_le_normalizer_oddCoreIn K hw) o).mp ho)

theorem tightlyEmbedded_and_isSolvable_of_twoElements {K R : Subgroup G}
    (hK : TightlyEmbedded K) (hR : IsSylowOf 2 R K)
    (h2 : ∀ k ∈ K, ∀ n : ℕ, k ^ 2 ^ n = 1 → k ∈ oddCoreIn K ⊔ R) :
    TightlyEmbedded (oddCoreIn K ⊔ R) ∧ Group.IsSolvable K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := oddCoreIn K with hOdef
  set X := O ⊔ R with hX
  have hXK : X ≤ K := sup_le (oddCoreIn_le K) hR.le
  have hNX : normalizer (K : Set G) ≤ normalizer (X : Set G) := by
    intro w hw
    refine mem_normalizer_of_map_conj_le (map_conj_le_of_map_conj_le hw ?_)
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨n, hn⟩ := hR.isPGroup ⟨r, hr⟩
    refine h2 _ ((mem_normalizer_iff.mp hw r).mp (hR.le hr)) n ?_
    have hn' : r ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    simp [MulAut.conj_apply, conj_pow, hn']
  refine ⟨tightlyEmbedded_of_conj_mem hK hXK hR le_sup_right
    fun w hw _ _ _ _ => hNX hw, ?_⟩
  have hOX : O ≤ X := le_sup_left
  have hOn : (O.subgroupOf X).Normal :=
    (normal_subgroupOf_iff_le_normalizer hOX).mpr
      (hXK.trans ((le_normalizer).trans (normalizer_le_normalizer_oddCoreIn K)))
  have hOsolv : Group.IsSolvable (O.subgroupOf X) := by
    refine CFSG.FeitThompson.isSolvable_of_odd_natCard _ ?_
    rw [Nat.card_congr (subgroupOfEquivOfLe hOX).toEquiv]
    exact odd_card_oddCoreIn K
  have hXOsolv : Group.IsSolvable (↥X ⧸ O.subgroupOf X) := by
    have hidx : O.relIndex X = O.relIndex R :=
      AschbacherTheorem3.relIndex_sup_of_le_normalizer
        (hR.le.trans ((le_normalizer).trans (normalizer_le_normalizer_oddCoreIn K)))
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hR.isPGroup
    have hdvd : Nat.card (↥X ⧸ O.subgroupOf X) ∣ 2 ^ m := by
      change O.relIndex X ∣ 2 ^ m
      rw [hidx, ← hm]
      exact relIndex_dvd_card O R
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have := (IsPGroup.of_card hj).isNilpotent
    infer_instance
  have hXsolv : Group.IsSolvable X :=
    Group.isSolvable_of_ker_le_range (O.subgroupOf X).subtype (QuotientGroup.mk' (O.subgroupOf X))
      (by rw [QuotientGroup.ker_mk', range_subtype])
  have hXn : (X.subgroupOf K).Normal :=
    (normal_subgroupOf_iff_le_normalizer hXK).mpr ((le_normalizer).trans hNX)
  have hXsolv' : Group.IsSolvable (X.subgroupOf K) :=
    Group.isSolvable_of_isSolvable_injective (f := (subgroupOfEquivOfLe hXK).toMonoidHom)
      (subgroupOfEquivOfLe hXK).injective
  have hKXsolv : Group.IsSolvable (↥K ⧸ X.subgroupOf K) := by
    refine CFSG.FeitThompson.isSolvable_of_odd_natCard _ ?_
    change Odd (X.relIndex K)
    refine Nat.not_even_iff_odd.mp fun he => ?_
    have hdvd := (isSylowOf_iff.mp hR).2.2
    apply hdvd
    rw [← relIndex_mul_relIndex R X K le_sup_right hXK]
    exact (even_iff_two_dvd.mp he).mul_left _
  exact Group.isSolvable_of_ker_le_range (X.subgroupOf K).subtype
    (QuotientGroup.mk' (X.subgroupOf K)) (by rw [QuotientGroup.ker_mk', range_subtype])

end Tight

theorem four_dvd_card_of_isPerfect {Q : Type*} [Group Q] [Finite Q] [Nontrivial Q]
    [Group.IsPerfect Q] : 4 ∣ Nat.card Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card Q := by
    by_contra hnot
    have : Group.IsSolvable Q := CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.odd_iff.mpr
      (Nat.two_dvd_ne_zero.mp hnot))
    have := CFSG.ComponentClassification.SolvableKernelContainment.perfect_solvable_subsingleton
      (G := Q)
    exact not_subsingleton Q this
  by_contra hnot4
  let P : Sylow 2 Q := Classical.choice inferInstance
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp P.isPGroup'
  have hm1 : m ≤ 1 := by
    by_contra h
    have h4 : 2 ^ 2 ∣ Nat.card Q :=
      (pow_dvd_pow 2 (show 2 ≤ m by omega)).trans (by rw [← hm]; exact card_subgroup_dvd_card _)
    exact hnot4 (by simpa using h4)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact Sylow.ne_bot_of_dvd_card P h2 (card_eq_one.mp (by simpa using hm))
  have hPcard : Nat.card (P : Subgroup Q) = 2 := by
    rw [hm, show m = 1 by omega, pow_one]
  have hPcyc : IsCyclic P := isCyclic_of_prime_card (p := 2) hPcard
  have hmin : (Nat.card Q).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr h2
  have hcomp := IsCyclic.isComplement' hmin hPcyc
  have : Group.IsSolvable (P : Subgroup Q) := by
    have := P.isPGroup'.isNilpotent
    infer_instance
  rw [CFSG.ComponentClassification.SolvableKernelContainment.hom_eq_one
    (MonoidHom.transferSylow P (hPcyc.normalizer_le_centralizer hmin)), MonoidHom.ker_one]
    at hcomp
  have h := hcomp.card_mul_card
  rw [card_top, hPcard] at h
  have hpos : 0 < Nat.card Q := Nat.card_pos
  omega

end CFSG.ComponentClassification.AS76b
