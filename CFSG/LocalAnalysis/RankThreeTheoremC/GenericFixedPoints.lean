module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerTwoGroups
import CFSG.LocalAnalysis.RankThreeTheoremC.LayerNormal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_two_inf_centralizer_eq_bot (hS : Setting G) (hD1 : TheoremD1 G)
    (hU0 : FullCoreLocal G) {p : ℕ} [Fact p.Prime] (hp : p ∈ rankThreeSigmaA G)
    {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M) {x : G}
    (hx : IsGenericPoint p P M x) (h5 : 5 ≤ p) {m : ℕ} (hm : 2 ≤ m)
    (e : rankThreeLayer (centralizer ({x} : Set G)) ≃* PSL(2, GaloisField p m)) :
    pCoreOf 2 M ⊓ centralizer ({x} : Set G) = ⊥ := by
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  refine eq_bot_of_isPGroup_two_of_le_normalizer_of_isGenericPoint hS hD1 hU0 hp hM hx h5 hm e
    inf_le_right (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_inf_left ?_
  refine le_normalizer_inf ((inf_le_left.trans inf_le_left).trans
    (hPM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))) ?_
  exact inf_le_right.trans ((rankThreeLayer_le _).trans Subgroup.le_normalizer)

omit [Finite G] in
theorem exists_isSylowOf_ge_of_isPGroup {p : ℕ} [Fact p.Prime] {K Q : Subgroup G} (hQK : Q ≤ K)
    (hQ : IsPGroup p Q) : ∃ S : Subgroup G, IsSylowOf p S K ∧ Q ≤ S := by
  obtain ⟨T, hT⟩ := (hQ.comap_subtype (K := K)).exists_le_sylow
  refine ⟨(T : Subgroup K).map K.subtype, ⟨T, rfl⟩, fun y hy => ?_⟩
  exact ⟨⟨y, hQK hy⟩, hT hy, rfl⟩

theorem mem_zpowers_of_isCyclic_of_orderOf_eq {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    [IsCyclic A] {x v : G} (hxA : x ∈ A) (hvA : v ∈ A) (hx : orderOf x = p) (hv1 : v ≠ 1)
    (hv : ∃ k : ℕ, v ^ (p ^ k) = 1) : x ∈ zpowers v := by
  have hprime : p.Prime := Fact.out
  obtain ⟨k, hk⟩ := hv
  set a : A := ⟨x, hxA⟩ with ha
  set b : A := ⟨v, hvA⟩ with hb
  have hao : orderOf a = p := by rw [ha, Subgroup.orderOf_mk, hx]
  have hbk : b ^ (p ^ k) = 1 := Subtype.ext hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hprime).mp (orderOf_dvd_of_pow_eq_one hbk)
  have hj1 : j ≠ 0 := by
    rintro rfl
    apply hv1
    have : orderOf b = 1 := by simpa using hj
    exact congrArg Subtype.val (orderOf_eq_one_iff.mp this)
  have hpdvd : p ∣ orderOf b := by
    rw [hj]
    exact dvd_pow_self p hj1
  have hb0 : orderOf b ≠ 0 := by
    rw [hj]
    exact pow_ne_zero _ hprime.ne_zero
  set b' : A := b ^ (orderOf b / p) with hb'
  have hb'o : orderOf b' = p := orderOf_pow_orderOf_div hb0 hpdvd
  have hzeq : zpowers a = zpowers b' := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers, hao, hb'o]
  have hab' : a ∈ zpowers b' := hzeq ▸ mem_zpowers a
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hab'
  refine mem_zpowers_iff.mpr ⟨((orderOf b / p : ℕ) : ℤ) * n, ?_⟩
  have h1 : (b ^ (orderOf b / p)) ^ n = a := hn
  have h2 : b ^ (((orderOf b / p : ℕ) : ℤ) * n) = a := by
    rw [zpow_mul, zpow_natCast]
    exact h1
  have h3 : ((b ^ (((orderOf b / p : ℕ) : ℤ) * n) : A) : G) = (a : G) := congrArg Subtype.val h2
  rw [SubgroupClass.coe_zpow] at h3
  exact h3

theorem fixedPointFree_of_isPGroup (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    {p : ℕ} [Fact p.Prime] (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G}
    (hM : IsCoreMaxLocal p P M) {x : G} (hx : IsGenericPoint p P M x) (h5 : 5 ≤ p) {m : ℕ}
    (hm : 2 ≤ m)
    (e : rankThreeLayer (centralizer ({x} : Set G)) ≃* PSL(2, GaloisField p m)) :
    ∀ v ∈ centralizer ((rankThreeLayer (centralizer ({x} : Set G)) : Subgroup G) : Set G),
      v ≠ 1 → (∃ k : ℕ, v ^ (p ^ k) = 1) →
        ∀ t ∈ pCoreOf 2 M, t * v = v * t → t = 1 := by
  intro v hvZ hv1 hvp t htT htv
  set L : Subgroup G := rankThreeLayer (centralizer ({x} : Set G)) with hL
  set Z : Subgroup G := centralizer (L : Set G) with hZ
  obtain ⟨-, hZM, -, -, hcyc⟩ := generic_layer_facts hS hD1 hU0 hp hM hx hm e
  have hCT := pCoreOf_two_inf_centralizer_eq_bot hS hD1 hU0 hp hM hx h5 hm e
  obtain ⟨-, ⟨-, hx1, hxp, -, -⟩, -, -⟩ := id hx
  have hxZ : x ∈ Z := mem_centralizer_iff.mpr fun l hl =>
    mem_centralizer_singleton_iff.mp (rankThreeLayer_le _ hl)
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  have hxP : IsPGroup p (zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hxo, pow_one])
  obtain ⟨k, hk⟩ := hvp
  have hvP : IsPGroup p (zpowers v) := by
    rintro ⟨g, hg⟩
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hg
    refine ⟨k, Subtype.ext ?_⟩
    change (v ^ i) ^ (p ^ k) = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
  obtain ⟨A, hA, hxA⟩ := exists_isSylowOf_ge_of_isPGroup (p := p) (K := Z) (Q := zpowers x)
    (zpowers_le.mpr hxZ) hxP
  obtain ⟨B, hB, hvB⟩ := exists_isSylowOf_ge_of_isPGroup (p := p) (K := Z) (Q := zpowers v)
    (zpowers_le.mpr hvZ) hvP
  obtain ⟨z, hzZ, hz⟩ := hA.exists_mem_conj hB
  have hv'A : z⁻¹ * v * z ∈ A := (hz v).mp (hvB (mem_zpowers v))
  have : IsCyclic A := hcyc A hA.isPGroup hA.le
  have hv'1 : z⁻¹ * v * z ≠ 1 := fun h => hv1 (by
    have := congrArg (fun y => z * y * z⁻¹) h
    simpa [mul_assoc] using this)
  have hv'k : (z⁻¹ * v * z) ^ (p ^ k) = 1 := by
    have h := conj_pow (a := z⁻¹) (b := v) (i := p ^ k)
    simp only [inv_inv] at h
    rw [h, hk]
    group
  have hxv' : x ∈ zpowers (z⁻¹ * v * z) :=
    mem_zpowers_of_isCyclic_of_orderOf_eq (hxA (mem_zpowers x)) hv'A hxo hv'1 ⟨k, hv'k⟩
  have hzM : z ∈ M := hZM hzZ
  have ht' : z⁻¹ * t * z ∈ pCoreOf 2 M := by
    have := (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (M.inv_mem hzM)) t).mp htT
    simpa using this
  have hcomm : Commute (z⁻¹ * t * z) (z⁻¹ * v * z) := by
    show z⁻¹ * t * z * (z⁻¹ * v * z) = z⁻¹ * v * z * (z⁻¹ * t * z)
    calc z⁻¹ * t * z * (z⁻¹ * v * z) = z⁻¹ * (t * v) * z := by group
      _ = z⁻¹ * (v * t) * z := by rw [htv]
      _ = z⁻¹ * v * z * (z⁻¹ * t * z) := by group
  obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hxv'
  have htx : z⁻¹ * t * z ∈ centralizer ({x} : Set G) := by
    rw [mem_centralizer_singleton_iff, ← hi]
    exact (hcomm.zpow_right i).eq
  have h1 : z⁻¹ * t * z ∈ pCoreOf 2 M ⊓ centralizer ({x} : Set G) := ⟨ht', htx⟩
  rw [hCT, Subgroup.mem_bot] at h1
  have := congrArg (fun y => z * y * z⁻¹) h1
  simpa [mul_assoc] using this

end CFSG.LocalAnalysis.RankThreeTheoremC
