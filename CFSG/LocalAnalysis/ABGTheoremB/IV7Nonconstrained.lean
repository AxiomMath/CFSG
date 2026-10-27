module

public import CFSG.LocalAnalysis.ABGTheoremB.IV2
public import CFSG.LocalAnalysis.ABGTheoremB.IV7Data
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.ABGTheoremB

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools CFSG.ABGQGroups
open scoped Pointwise

universe u

section General

variable {G : Type u} [Group G]

private theorem normalizer_le_normalizer_centralizer_of_subgroup (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (H : Set G) : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
    (Subgroup.normal_subgroupOf_centralizer_normalizer _)

private theorem normalizer_le_normalizer_centerOf (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤ Subgroup.normalizer (centerOf H : Set G) :=
  (le_inf le_rfl (normalizer_le_normalizer_centralizer_of_subgroup H)).trans
    Subgroup.inf_normalizer_le_normalizer_inf

private theorem le_normalizer_centerOf (H : Subgroup G) :
    H ≤ Subgroup.normalizer (centerOf H : Set G) :=
  Subgroup.le_normalizer.trans (normalizer_le_normalizer_centerOf H)

private theorem centerOf_le_centralizer_centerOf (H : Subgroup G) :
    centerOf H ≤ Subgroup.centralizer (centerOf H : Set G) := by
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact Subgroup.mem_centralizer_iff.mp ha.2 b hb.1

private theorem le_centralizer_centerOf (H : Subgroup G) :
    H ≤ Subgroup.centralizer (centerOf H : Set G) :=
  Subgroup.le_centralizer_iff.mp inf_le_right

private theorem centerOf_subgroupOf_eq_center (H : Subgroup G) :
    (centerOf H).subgroupOf H = Subgroup.center H := by
  ext ⟨g, hg⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_center_iff]
  constructor
  · intro h k
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp h.2 k k.2)
  · intro h
    refine ⟨hg, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
    exact congrArg Subtype.val (h ⟨k, hk⟩)

private theorem centerOf_subgroupOf_characteristic (H : Subgroup G) :
    ((centerOf H).subgroupOf H).Characteristic := by
  rw [centerOf_subgroupOf_eq_center]
  infer_instance

private theorem inf_centerOf_ne_bot_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime] {P M : Subgroup G}
    (hP : IsPGroup p P) (hMP : M ≤ P) (hPM : P ≤ Subgroup.normalizer (M : Set G))
    (hM : M ≠ ⊥) : M ⊓ centerOf P ≠ ⊥ := by
  have : (M.subgroupOf P).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hMP).mpr hPM
  have : Group.IsNilpotent P := hP.isNilpotent
  have hM' : M.subgroupOf P ≠ ⊥ := by
    intro h
    apply hM
    rw [← Subgroup.map_subgroupOf_eq_of_le hMP, h, Subgroup.map_bot]
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hM')
  rw [Subgroup.ne_bot_iff_exists_ne_one]
  refine ⟨⟨z, hz.1, z.2, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩, fun h => hz1 ?_⟩
  · exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz.2 ⟨g, hg⟩)
  · have h' : (z : G) = 1 := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')

private theorem centerOf_ne_bot_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime] {P : Subgroup G}
    (hP : IsPGroup p P) (hP1 : P ≠ ⊥) : centerOf P ≠ ⊥ := by
  intro h
  apply inf_centerOf_ne_bot_of_isPGroup hP le_rfl Subgroup.le_normalizer hP1
  rw [h, inf_bot_eq]

private theorem not_dvd_index_of_isSylowOf_of_sylow_le [Finite G] {p : ℕ} [Fact p.Prime]
    {S H : Subgroup G} (hS : IsSylowOf p S H) (S' : Sylow p G) (hS'H : (S' : Subgroup G) ≤ H) :
    ¬ p ∣ S.index := by
  have h1 : ¬ p ∣ H.index := fun h => S'.not_dvd_index (h.trans (Subgroup.index_dvd_of_le hS'H))
  rw [← Subgroup.relIndex_mul_index hS.le]
  exact (Fact.out : p.Prime).not_dvd_mul (isSylowOf_iff.mp hS).2.2 h1

private theorem exists_isSylowOf_ge_of_le [Finite G] {p : ℕ} [Fact p.Prime] {P K : Subgroup G}
    (hPK : P ≤ K) (hP : IsPGroup p P) : ∃ S : Subgroup G, IsSylowOf p S K ∧ P ≤ S := by
  obtain ⟨Q, hQ⟩ := (hP.comap_subtype (K := K)).exists_le_sylow
  refine ⟨(Q : Subgroup K).map K.subtype, ⟨Q, rfl⟩, ?_⟩
  rw [← Subgroup.map_subgroupOf_eq_of_le hPK]
  exact Subgroup.map_mono hQ

private theorem subset_inf_normalizer_mul_of_isSylowOf [Finite G] {p : ℕ} [Fact p.Prime]
    {H M P : Subgroup G} (hMH : M ≤ H) (hHM : H ≤ Subgroup.normalizer (M : Set G))
    (hP : IsSylowOf p P M) :
    (H : Set G) ⊆ ((H ⊓ Subgroup.normalizer (P : Set G) : Subgroup G) : Set G) * (M : Set G) := by
  intro h hh
  set P' : Subgroup G := P.map (MulAut.conj h⁻¹).toMonoidHom with hP'
  have hmem : ∀ z, z ∈ P' ↔ h * z * h⁻¹ ∈ P := by
    intro z
    rw [hP', Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
  have hP'M : P' ≤ M := by
    intro z hz
    have h1 := hP.le ((hmem z).mp hz)
    have h2 := (Subgroup.mem_normalizer_iff.mp (hHM (H.inv_mem hh)) _).mp h1
    have e : h⁻¹ * (h * z * h⁻¹) * h⁻¹⁻¹ = z := by group
    rwa [e] at h2
  have hP'syl : IsSylowOf p P' M := by
    apply isSylowOf_of_card hP'M
    rw [hP', Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective, hP.card_eq]
  obtain ⟨k, hk, hconj⟩ := hP.exists_mem_conj hP'syl
  have hg : h * k ∈ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have e1 := hconj (k * y * k⁻¹)
    rw [hmem] at e1
    have e2 : k⁻¹ * (k * y * k⁻¹) * k = y := by group
    have e3 : h * (k * y * k⁻¹) * h⁻¹ = h * k * y * (h * k)⁻¹ := by group
    rw [e2, e3] at e1
    exact e1.symm
  exact ⟨h * k, ⟨H.mul_mem hh (hMH hk), hg⟩, k⁻¹, M.inv_mem hk, by group⟩

private theorem exists_mul_mem_centralizer_of_two_group [Finite G] {A M : Subgroup G}
    (hA : IsPGroup 2 A) (hM : Odd (Nat.card M)) {y : G}
    (hyM : y ∈ Subgroup.normalizer (M : Set G)) (hy : ∀ a ∈ A, y⁻¹ * (a * y * a⁻¹) ∈ M)
    (hAM : A ≤ Subgroup.normalizer (M : Set G)) :
    ∃ m ∈ M, y * m ∈ Subgroup.centralizer (A : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := Subgroup.normalizer (M : Set G) with hK
  set M' : Subgroup K := M.subgroupOf K with hM'
  have hM'n : M'.Normal := Subgroup.normal_in_normalizer
  set A' : Subgroup K := A.subgroupOf K with hA'def
  have hA' : IsPGroup 2 A' := hA.comap_subtype
  have hM'2 : ¬ 2 ∣ Nat.card M' := by
    rw [hM', Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv]
    exact hM.not_two_dvd_nat
  have key := CFSG.Semidihedral.Local.map_centralizer_eq_of_coprime 2 M' hM'2 A' hA'
  have hmem : QuotientGroup.mk' M' (⟨y, hyM⟩ : K) ∈
      Subgroup.centralizer ((A'.map (QuotientGroup.mk' M') : Subgroup (K ⧸ M')) :
        Set (K ⧸ M')) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      hM', Subgroup.mem_subgroupOf]
    have h1 := hy _ (A.inv_mem (show (a : G) ∈ A from ha))
    rw [inv_inv] at h1
    have e : (((a * ⟨y, hyM⟩)⁻¹ * (⟨y, hyM⟩ * a) : K) : G) = y⁻¹ * ((a : G)⁻¹ * y * a) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact h1
  rw [← key] at hmem
  obtain ⟨c, hc, hcy⟩ := hmem
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hM',
    Subgroup.mem_subgroupOf] at hcy
  refine ⟨y⁻¹ * c, ?_, ?_⟩
  · have := M.inv_mem hcy
    simpa using this
  · rw [mul_inv_cancel_left, Subgroup.mem_centralizer_iff]
    intro a ha
    have h := Subgroup.mem_centralizer_iff.mp hc ⟨a, hAM ha⟩ ha
    exact congrArg Subtype.val h

private theorem mem_centralizer_of_stabilizes [Finite G] {p : ℕ} [Fact p.Prime] {Q Z : Subgroup G}
    {g : G} (hZ : IsPGroup p Z) (hgZ : g ∈ Subgroup.centralizer (Z : Set G))
    (hgQ : ∀ y ∈ Q, g * y * g⁻¹ * y⁻¹ ∈ Z) {m : ℕ} (hm : g ^ m = 1) (hpm : ¬ p ∣ m) :
    g ∈ Subgroup.centralizer (Q : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨z, hzdef⟩ : ∃ z, z = g * y * g⁻¹ * y⁻¹ := ⟨_, rfl⟩
  have hz : z ∈ Z := hzdef ▸ hgQ y hy
  have hgz : Commute g z := ((Subgroup.mem_centralizer_iff.mp hgZ) z hz).symm
  have hgy : g * y * g⁻¹ = z * y := by rw [hzdef]; group
  have hk : ∀ k : ℕ, g ^ k * y * (g ^ k)⁻¹ = z ^ k * y := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hc : g * z ^ k * g⁻¹ = z ^ k := by
        rw [(hgz.pow_right k).eq, mul_assoc, mul_inv_cancel, mul_one]
      calc g ^ (k + 1) * y * (g ^ (k + 1))⁻¹ = g * (g ^ k * y * (g ^ k)⁻¹) * g⁻¹ := by
            rw [pow_succ']; group
        _ = (g * z ^ k * g⁻¹) * (g * y * g⁻¹) := by rw [ih]; group
        _ = z ^ (k + 1) * y := by rw [hc, hgy, pow_succ, mul_assoc]
  have hzm : z ^ m = 1 := by
    have h := hk m
    rw [hm, one_mul, inv_one, mul_one] at h
    have h' : z ^ m * y = 1 * y := by rw [← h, one_mul]
    exact mul_right_cancel h'
  obtain ⟨j, hj⟩ := hZ ⟨z, hz⟩
  have hzj : z ^ p ^ j = 1 := by
    have := congrArg Subtype.val hj
    simpa using this
  have h1 : orderOf z ∣ m := orderOf_dvd_of_pow_eq_one hzm
  have h2 : orderOf z ∣ p ^ j := orderOf_dvd_of_pow_eq_one hzj
  have hcop : Nat.Coprime (p ^ j) m :=
    Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpm)
  have hz1 : z = 1 :=
    orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left h2) h1)
  have : g * y * g⁻¹ = y := by rw [hgy, hz1, one_mul]
  calc y * g = g * y * g⁻¹ * g := by rw [this]
    _ = g * y := by group

private theorem exists_relIndex_eq_pow_of_pow_mem [Finite G] {p : ℕ} [Fact p.Prime]
    {N C : Subgroup G} (hCN : C ≤ N) (hNC : N ≤ Subgroup.normalizer (C : Set G))
    (hpow : ∀ g ∈ N, ∃ a : ℕ, g ^ p ^ a ∈ C) : ∃ n : ℕ, C.relIndex N = p ^ n := by
  have : (C.subgroupOf N).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hCN).mpr hNC
  have hpg : IsPGroup p (N ⧸ C.subgroupOf N) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, ha⟩ := hpow g g.2
    refine ⟨a, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_pow]
    exact ha
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpg
  exact ⟨n, hn⟩

private theorem le_sup_of_isSylowOf_of_relIndex_eq_pow [Finite G] {p : ℕ} [Fact p.Prime]
    {N C S : Subgroup G} (hCN : C ≤ N) (hS : IsSylowOf p S N) {n : ℕ}
    (hn : C.relIndex N = p ^ n) : N ≤ S ⊔ C := by
  have hBN : S ⊔ C ≤ N := sup_le hS.le hCN
  have h1 := Subgroup.relIndex_mul_relIndex C (S ⊔ C) N le_sup_right hBN
  have h2 := Subgroup.relIndex_mul_relIndex S (S ⊔ C) N le_sup_left hBN
  have hdvd : (S ⊔ C).relIndex N ∣ p ^ n := by
    rw [← hn, ← h1]
    exact Dvd.intro_left _ rfl
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Fact.out).mp hdvd
  have hS' := (isSylowOf_iff.mp hS).2.2
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · rw [pow_zero] at hk
    exact Subgroup.relIndex_eq_one.mp hk
  · exfalso
    apply hS'
    rw [← h2, hk]
    exact Dvd.dvd.mul_left (dvd_pow_self p hkpos.ne') _

private theorem le_normalizer_of_forall_commutator_mem {H K J : Subgroup G} (hKJ : K ≤ J)
    (hJH : J ≤ H) (hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b * a⁻¹ * b⁻¹ ∈ K) :
    H ≤ Subgroup.normalizer (J : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro j
  constructor
  · intro hj
    have e : h * j * h⁻¹ = (h * j * h⁻¹ * j⁻¹) * j := by group
    rw [e]
    exact J.mul_mem (hKJ (hcomm h hh j (hJH hj))) hj
  · intro hj
    have hj' := hJH hj
    have e : j = (h⁻¹ * (h * j * h⁻¹) * h⁻¹⁻¹ * (h * j * h⁻¹)⁻¹) * (h * j * h⁻¹) := by group
    rw [e]
    exact J.mul_mem (hKJ (hcomm _ (H.inv_mem hh) _ hj')) hj

private theorem le_solvRadIn_of_isSolvable {H K : Subgroup G} (hKH : K ≤ H)
    (hnorm : H ≤ Subgroup.normalizer (K : Set G)) (hsolv : Group.IsSolvable K) :
    K ≤ solvRadIn H := by
  have hnormal : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hnorm
  have hsolv' : Group.IsSolvable (K.subgroupOf H) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKH).injective
  have hle : K.subgroupOf H ≤ CFSG.solvableRadical H := le_sSup ⟨hnormal, hsolv'⟩
  rw [← Subgroup.map_subgroupOf_eq_of_le hKH]
  exact Subgroup.map_mono hle

private theorem mem_of_pow_mem_of_coprime_orderOf {K : Subgroup G} {u : G} {n : ℕ}
    (hcop : Nat.Coprime n (orderOf u)) (h : u ^ n ∈ K) : u ∈ K := by
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact K.pow_mem h m

private theorem odd_card_of_isPGroup_of_ne_two [Finite G] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {K : Subgroup G} (hK : IsPGroup r K) : Odd (Nat.card K) := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hK
  rw [hk]
  exact (hr.eq_two_or_odd'.resolve_left hr2).pow

private theorem isPGroup_two_zpowers {x : G} (hx : orderOf x = 2) :
    IsPGroup 2 (Subgroup.zpowers x) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])

private theorem le_of_isSylowOf_of_le_normalizer [Finite G] {p : ℕ} [Fact p.Prime]
    {R K W : Subgroup G} (hR : IsSylowOf p R K) (hWK : W ≤ K) (hW : IsPGroup p W)
    (hWR : W ≤ Subgroup.normalizer (R : Set G)) : W ≤ R := by
  have h := hR.eq_of_le le_sup_left (sup_le hR.le hWK) (hR.isPGroup.to_sup_of_normal_left' hW hWR)
  rw [← h]
  exact le_sup_right

private theorem le_centerOf_of_isSylowOf [Finite G] {p : ℕ} [Fact p.Prime] {W K U : Subgroup G}
    (hW : IsSylowOf p W K) (hUK : U ≤ K) (hU : IsPGroup p U)
    (hUW : U ≤ Subgroup.centralizer (W : Set G)) : U ≤ centerOf W :=
  le_inf (le_of_isSylowOf_of_le_normalizer hW hUK hU
    (hUW.trans (Subgroup.centralizer_le_normalizer _))) hUW

private theorem eq_bot_of_isPGroup_of_not_dvd [Finite G] {p : ℕ} [Fact p.Prime]
    {U K : Subgroup G} (hUK : U ≤ K) (hU : IsPGroup p U) (hK : ¬ p ∣ Nat.card K) : U = ⊥ := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hU
  have hdvd : p ^ n ∣ Nat.card K := hn ▸ Subgroup.card_dvd_of_le hUK
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · rw [pow_zero] at hn
    exact Subgroup.card_eq_one.mp hn
  · exact absurd ((dvd_pow_self p hpos.ne').trans hdvd) hK

private theorem not_dvd_card_of_isSylowOf_bot [Finite G] {p : ℕ} [Fact p.Prime]
    {K : Subgroup G} (h : IsSylowOf p ⊥ K) : ¬ p ∣ Nat.card K := by
  have h1 := (isSylowOf_iff.mp h).2.2
  rwa [Subgroup.relIndex_bot_left] at h1

private theorem exists_orderOf_eq_two [Finite G] {K : Subgroup G} (hK : IsPGroup 2 K)
    (hK1 : K ≠ ⊥) : ∃ z ∈ K, orderOf z = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hK
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hK1 (Subgroup.card_eq_one.mp (by rw [hn, pow_zero]))
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := K) 2
    (by rw [hn]; exact dvd_pow_self 2 hn0)
  exact ⟨z, z.2, by rw [Subgroup.orderOf_coe, hz]⟩

private theorem eq_one_of_inv_eq_of_odd {u : G} (hu : Odd (orderOf u)) (h : u⁻¹ = u) :
    u = 1 := by
  have h2 : u ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 1 [← h]
    exact inv_mul_cancel u
  rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h2) with h3 | h3
  · exact orderOf_eq_one_iff.mp h3
  · rw [h3] at hu
    exact absurd hu (by decide)

private theorem oddCore_le_solvableRadical_of_finite (K : Type*) [Group K] [Finite K] :
    CFSG.oddCore K ≤ CFSG.solvableRadical K :=
  le_sSup ⟨CFSG.oddCore_normal K,
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (CFSG.ABGTheoremB.odd_card_oddCore K)⟩

private theorem le_pPrimePCoreIn_normalizer {r : ℕ} {R : Subgroup G} (hR : IsPGroup r R) :
    R ≤ pPrimePCoreIn r (Subgroup.normalizer (R : Set G)) := by
  have hle : R.subgroupOf (Subgroup.normalizer (R : Set G)) ≤
      CFSG.Op_p'p r (Subgroup.normalizer (R : Set G)) := by
    apply le_Op_p'p_of_normal Subgroup.normal_in_normalizer
    intro y hy
    obtain ⟨k, hk⟩ := (hR.comap_subtype (K := Subgroup.normalizer (R : Set G))) ⟨y, hy⟩
    refine ⟨k, ?_⟩
    have hk' : y ^ r ^ k = 1 := by
      have := congrArg Subtype.val hk
      rw [Subgroup.coe_pow] at this
      exact this
    rw [hk']
    exact one_mem _
  intro x hx
  exact ⟨⟨x, Subgroup.le_normalizer hx⟩, hle hx, rfl⟩

private theorem isSylowOf_sup_of_forall_le [Finite G] {p : ℕ} [Fact p.Prime]
    {Q K S : Subgroup G} (hQS : Q ≤ S) (hSp : IsPGroup p S) (hSJ : S ≤ Q ⊔ K)
    (hQK : Q ≤ Subgroup.normalizer (K : Set G))
    (hK : ∀ U : Subgroup G, U ≤ K → IsPGroup p U → U ≤ S) : IsSylowOf p S (Q ⊔ K) := by
  obtain ⟨S', hS', hSS'⟩ := exists_isSylowOf_ge_of_le hSJ hSp
  have hS'S : S' ≤ S := by
    intro s hs
    have hsJ : s ∈ ((Q ⊔ K : Subgroup G) : Set G) := hS'.le hs
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hQK] at hsJ
    obtain ⟨q, hq, k, hk, rfl⟩ := hsJ
    have hkS' : k ∈ S' := by
      have := S'.mul_mem (S'.inv_mem (hSS' (hQS hq))) hs
      simpa using this
    exact S.mul_mem (hQS hq) (hK (S' ⊓ K) inf_le_right hS'.isPGroup.to_inf_left ⟨hkS', hk⟩)
  rwa [le_antisymm hS'S hSS'] at hS'

private theorem subset_inf_normalizer_mul_of_comm [Finite G] {p : ℕ} [Fact p.Prime]
    {H₂ K Q S : Subgroup G} (hKH₂ : K ≤ H₂) (hQH₂ : Q ≤ H₂) (hQS : Q ≤ S)
    (hcomm : ∀ a ∈ H₂, ∀ b ∈ H₂, a * b * a⁻¹ * b⁻¹ ∈ K) (hS : IsSylowOf p S (Q ⊔ K)) :
    (H₂ : Set G) ⊆
      ((H₂ ⊓ Subgroup.normalizer (S : Set G) : Subgroup G) : Set G) * (K : Set G) := by
  have hJH₂ : Q ⊔ K ≤ H₂ := sup_le hQH₂ hKH₂
  have hH₂J : H₂ ≤ Subgroup.normalizer ((Q ⊔ K : Subgroup G) : Set G) :=
    le_normalizer_of_forall_commutator_mem le_sup_right hJH₂ hcomm
  have hH₂K : H₂ ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_of_forall_commutator_mem le_rfl hKH₂ hcomm
  intro h hh
  obtain ⟨n, hn, j, hj, rfl⟩ := subset_inf_normalizer_mul_of_isSylowOf hJH₂ hH₂J hS hh
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hQH₂.trans hH₂K)] at hj
  obtain ⟨q, hq, k, hk, rfl⟩ := hj
  refine ⟨n * q, ⟨H₂.mul_mem hn.1 (hQH₂ hq),
    (Subgroup.normalizer _).mul_mem hn.2 (Subgroup.le_normalizer (hQS hq))⟩, k, hk, by group⟩

private theorem le_centralizer_of_stability [Finite G] {p : ℕ} [Fact p.Prime]
    {Nn S Q₉ Z Q : Subgroup G} (hS : IsSylowOf p S Nn)
    (hSQ : S ≤ Subgroup.centralizer (Q : Set G)) (hQQ₉ : Q ≤ Q₉) (hZ : IsPGroup p Z)
    (hNnZ : Nn ≤ Subgroup.centralizer (Z : Set G))
    (hNnQ₉ : Nn ≤ Subgroup.normalizer (Q₉ : Set G))
    (hstab : ∀ g ∈ Nn, ∀ y ∈ Q₉, g * y * g⁻¹ * y⁻¹ ∈ Z) :
    Nn ≤ Subgroup.centralizer (Q : Set G) := by
  set Cn := Nn ⊓ Subgroup.centralizer (Q₉ : Set G) with hCn
  have hCnNn : Cn ≤ Nn := inf_le_left
  have hNnCn : Nn ≤ Subgroup.normalizer (Cn : Set G) :=
    (le_inf Subgroup.le_normalizer
      (hNnQ₉.trans (normalizer_le_normalizer_centralizer_of_subgroup Q₉))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hpow : ∀ g ∈ Nn, ∃ a : ℕ, g ^ p ^ a ∈ Cn := by
    intro g hg
    obtain ⟨a, m, hpm, hord⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' p (Fact.out : p.Prime).one_lt.ne'
    refine ⟨a, Nn.pow_mem hg _, ?_⟩
    have hgm : (g ^ p ^ a) ^ m = 1 := by
      rw [← pow_mul, ← hord, pow_orderOf_eq_one]
    exact mem_centralizer_of_stabilizes hZ (hNnZ (Nn.pow_mem hg _))
      (hstab _ (Nn.pow_mem hg _)) hgm hpm
  obtain ⟨n, hn⟩ := exists_relIndex_eq_pow_of_pow_mem hCnNn hNnCn hpow
  refine (le_sup_of_isSylowOf_of_relIndex_eq_pow hCnNn hS hn).trans (sup_le hSQ ?_)
  exact inf_le_right.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hQQ₉))

private theorem exists_sylow_pPrimePCoreIn [Finite G] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {H A Q₀ X : Subgroup G} (hc : PConstrainedWithin r H (CFSG.oddCore H)) (hA : IsPGroup 2 A)
    (hAH : A ≤ H) (hQ₀H : Q₀ ≤ H) (hQ₀ : IsPGroup r Q₀)
    (hAQ₀ : A ≤ Subgroup.normalizer (Q₀ : Set G)) (hX : IsPGroup r X)
    (hXK : X ≤ pPrimePCoreIn r H) (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hQ₀X : Q₀ ≤ Subgroup.normalizer (X : Set G)) :
    ∃ Rs : Subgroup G, IsSylowOf r Rs (pPrimePCoreIn r H) ∧ X ≤ Rs ∧
      A ≤ Subgroup.normalizer (Rs : Set G) ∧ Q₀ ≤ Subgroup.normalizer (Rs : Set G) := by
  have : Fact r.Prime := ⟨hr⟩
  set K := pPrimePCoreIn r H with hK
  have hKO : K ≤ oddCoreIn H := Subgroup.map_mono hc.1
  have hKodd : Odd (Nat.card K) :=
    (odd_card_oddCoreIn H).of_dvd_nat (Subgroup.card_dvd_of_le hKO)
  have hHK : H ≤ Subgroup.normalizer (K : Set G) :=
    CFSG.ABGTheoremB.le_normalizer_map_subtype H (CFSG.Op_p'p r H)
  have hQ₀K : Q₀ ≤ Subgroup.normalizer (K : Set G) := hQ₀H.trans hHK
  have hK'odd : Odd (Nat.card (K ⊔ Q₀ : Subgroup G)) :=
    odd_card_sup_of_le_normalizer_of_odd hQ₀K hKodd
      (odd_card_of_isPGroup_of_ne_two hr hr2 hQ₀)
  have hAK' : A ≤ Subgroup.normalizer ((K ⊔ Q₀ : Subgroup G) : Set G) :=
    (le_inf (hAH.trans hHK) hAQ₀).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hY : IsPGroup r (X ⊔ Q₀ : Subgroup G) := hX.to_sup_of_normal_left' hQ₀ hQ₀X
  have hAY : A ≤ Subgroup.normalizer ((X ⊔ Q₀ : Subgroup G) : Set G) :=
    (le_inf hAX hAQ₀).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  obtain ⟨R₁, hR₁, hYR₁, hAR₁⟩ := exists_isSylowOf_normalized_ge_of_odd hr hA hAK' hK'odd
    (sup_le_sup_right hXK _) hY hAY
  have hK'K : K ⊔ Q₀ ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hQ₀K
  refine ⟨R₁ ⊓ K, hR₁.inf_of_le_normalizer le_sup_left hK'K,
    le_inf (le_sup_left.trans hYR₁) hXK,
    (le_inf hAR₁ (hAH.trans hHK)).trans Subgroup.inf_normalizer_le_normalizer_inf, ?_⟩
  exact (le_inf ((le_sup_right.trans hYR₁).trans Subgroup.le_normalizer) hQ₀K).trans
    Subgroup.inf_normalizer_le_normalizer_inf

private theorem mem_oddCoreIn_of_inverted [Finite G] {H : Subgroup G} {x u : G} (hx : x ∈ H)
    (hfac : oddCoreIn H ⊔ (H ⊓ Subgroup.centralizer {x}) = H) (hu : u ∈ H)
    (hux : x * u * x⁻¹ = u⁻¹) (hodd : Odd (orderOf u)) : u ∈ oddCoreIn H := by
  have hnorm : H ⊓ Subgroup.centralizer {x} ≤ Subgroup.normalizer (oddCoreIn H : Set G) :=
    inf_le_left.trans (le_normalizer_oddCoreIn H)
  have hu' : u ∈ (oddCoreIn H : Set G) *
      ((H ⊓ Subgroup.centralizer {x} : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm, hfac]
    exact hu
  obtain ⟨o, ho, n, hn, hon⟩ := hu'
  have hxn : n * x = x * n := Subgroup.mem_centralizer_singleton_iff.mp hn.2
  have hxnx : x * n * x⁻¹ = n := by rw [← hxn, mul_inv_cancel_right]
  have hxo : x * o * x⁻¹ ∈ oddCoreIn H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_oddCoreIn H hx) o).mp ho
  have h1 : u⁻¹ * (x * u * x⁻¹) ∈ oddCoreIn H := by
    have e : u⁻¹ * (x * u * x⁻¹) = n⁻¹ * (o⁻¹ * (x * o * x⁻¹)) * n⁻¹⁻¹ := by
      rw [← hon]
      calc (o * n)⁻¹ * (x * (o * n) * x⁻¹)
          = n⁻¹ * (o⁻¹ * (x * o * x⁻¹)) * (x * n * x⁻¹) := by group
        _ = n⁻¹ * (o⁻¹ * (x * o * x⁻¹)) * n⁻¹⁻¹ := by rw [hxnx, inv_inv]
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_oddCoreIn H (H.inv_mem hn.1)) _).mp
      ((oddCoreIn H).mul_mem ((oddCoreIn H).inv_mem ho) hxo)
  rw [hux] at h1
  apply mem_of_pow_mem_of_coprime_orderOf (Nat.coprime_two_left.mpr hodd)
  have := (oddCoreIn H).inv_mem h1
  rw [mul_inv_rev, inv_inv] at this
  rw [pow_two]
  exact this

private theorem not_mem_centralizer_of_inverted [Finite G] {r : ℕ} (hr : r.Prime)
    {K Rs : Subgroup G} {x u : G} (hK : Odd (Nat.card K)) (hx : orderOf x = 2)
    (hxK : x ∈ Subgroup.normalizer (K : Set G)) (hRs : IsSylowOf r Rs K)
    (hxRs : x ∈ Subgroup.normalizer (Rs : Set G)) (huK : u ∈ K)
    (hur : IsPGroup r (Subgroup.zpowers u)) (hu1 : u ≠ 1) (hux : x * u * x⁻¹ = u⁻¹) :
    x ∉ Subgroup.centralizer (Rs : Set G) := by
  have hx2 := isPGroup_two_zpowers hx
  have hAK : Subgroup.zpowers x ≤ Subgroup.normalizer (K : Set G) := Subgroup.zpowers_le.mpr hxK
  have hAU : Subgroup.zpowers x ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    show Subgroup.zpowers (x * u * x⁻¹) = _
    rw [hux, Subgroup.zpowers_inv]
  obtain ⟨R₁, hR₁, huR₁, hxR₁⟩ := exists_isSylowOf_normalized_ge_of_odd hr hx2 hAK hK
    (Subgroup.zpowers_le.mpr huK) hur hAU
  obtain ⟨c, hc, hcR⟩ := exists_conj_eq_of_isSylowOf_normalized_of_odd hr hx2 hAK hK hRs hR₁
    (Subgroup.zpowers_le.mpr hxRs) hxR₁
  intro hxC
  have hu : u ∈ R₁ := huR₁ (Subgroup.mem_zpowers u)
  rw [← hcR] at hu
  obtain ⟨y, hy, hyu⟩ := hu
  have hyu' : c * y * c⁻¹ = u := by
    rw [← hyu]
    rfl
  have hcx : Commute x c := (Subgroup.mem_centralizer_iff.mp hc.2) x (Subgroup.mem_zpowers x)
  have hyx : Commute x y := ((Subgroup.mem_centralizer_iff.mp hxC) y hy).symm
  have hxu : Commute x u := by
    rw [← hyu']
    exact (hcx.mul_right hyx).mul_right hcx.inv_right
  have hodd : Odd (orderOf u) := hK.of_dvd_nat (Subgroup.orderOf_dvd_natCard K huK)
  apply hu1
  apply eq_one_of_inv_eq_of_odd hodd
  rw [← hux, hxu.eq, mul_inv_cancel_right]

end General

namespace Setting

variable {G : Type u} [Group G] [Finite G] (σ : Setting G)

omit [Finite G] in
private theorem isPGroup_two_D_nc : IsPGroup 2 σ.D := σ.S.isPGroup'.to_le σ.D_le_S

private theorem x_mem_D_nc (hσ : σ.IsValid) : σ.x ∈ σ.D := σ.T_le_D hσ σ.x_mem_T

private theorem ON_le_solvRadIn_L (hσ : σ.IsValid) : σ.ON ≤ solvRadIn σ.L :=
  le_solvRadIn_of_isSolvable (hσ.ON_le_L₀.trans le_sup_left)
    ((sup_le hσ.L₀_le_N (σ.S_le_N hσ)).trans σ.N_le_normalizer_ON)
    (CFSG.FeitThompson.isSolvable_of_odd_natCard _ σ.odd_card_ON)

omit [Finite G] in
private theorem C_le_normalizer_inf_ON :
    σ.C ≤ Subgroup.normalizer ((σ.C ⊓ σ.ON : Subgroup G) : Set G) :=
  (le_inf Subgroup.le_normalizer (σ.C_le_N.trans σ.N_le_normalizer_ON)).trans
    Subgroup.inf_normalizer_le_normalizer_inf

private theorem ne_bot_of_isSylowOf_of_dvd_nc {r : ℕ} (hr : r.Prime) {P K : Subgroup G}
    (hP : IsSylowOf r P K) (hdvd : r ∣ Nat.card K) : P ≠ ⊥ := by
  have : Fact r.Prime := ⟨hr⟩
  intro hbot
  have h1 := hP.card_eq
  rw [hbot, Subgroup.card_bot] at h1
  exact absurd h1 (Nat.one_lt_pow (hr.factorization_pos_of_dvd Nat.card_pos.ne' hdvd).ne'
    hr.one_lt).ne

private theorem inf_ON_le_of_le_normalizer {r : ℕ} (hr : r.Prime) {P R : Subgroup G}
    (hP : IsPGroup r P) (hR : IsSylowOf r R σ.ON) (hRP : P ≤ Subgroup.normalizer (R : Set G)) :
    P ⊓ σ.ON ≤ R :=
  have : Fact r.Prime := ⟨hr⟩
  le_of_isSylowOf_of_le_normalizer hR inf_le_right hP.to_inf_left (inf_le_left.trans hRP)

private theorem inf_L₀_subset_mul_of_cover (hσ : σ.IsValid) {X : Subgroup G}
    (hXL₀ : X ≤ σ.L₀) (hTX : σ.T ≤ Subgroup.normalizer (X : Set G))
    (hcov : (σ.L₀ : Set G) ⊆ (X : Set G) * (σ.ON : Set G)) :
    ((σ.C ⊓ σ.L₀ : Subgroup G) : Set G) ⊆
      ((σ.C ⊓ X : Subgroup G) : Set G) * ((σ.C ⊓ σ.ON : Subgroup G) : Set G) := by
  intro c hc
  have hcC : c ∈ σ.C := hc.1
  obtain ⟨y, hy, o, ho, rfl⟩ := hcov hc.2
  have hModd : Odd (Nat.card (X ⊓ σ.ON : Subgroup G)) :=
    σ.odd_card_ON.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
  have hyN : y ∈ σ.N := hσ.L₀_le_N (hXL₀ hy)
  have hyM : y ∈ Subgroup.normalizer ((X ⊓ σ.ON : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hy, σ.N_le_normalizer_ON hyN⟩
  have hTON : σ.T ≤ Subgroup.normalizer (σ.ON : Set G) := (σ.T_le_N hσ).trans σ.N_le_normalizer_ON
  have hTM : σ.T ≤ Subgroup.normalizer ((X ⊓ σ.ON : Subgroup G) : Set G) :=
    (le_inf hTX hTON).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hT2 : IsPGroup 2 σ.T := (σ.isPGroup_two_D_nc).to_le (σ.T_le_D hσ)
  have hyT : ∀ t ∈ σ.T, y⁻¹ * (t * y * t⁻¹) ∈ X ⊓ σ.ON := by
    intro t ht
    have h := (Subgroup.mem_centralizer_iff.mp hcC) t ht
    have e : y⁻¹ * (t * y * t⁻¹) = o * (t * o⁻¹ * t⁻¹) := by
      calc y⁻¹ * (t * y * t⁻¹) = y⁻¹ * (t * (y * o) * o⁻¹ * t⁻¹) := by group
        _ = y⁻¹ * (y * o * t * o⁻¹ * t⁻¹) := by rw [h]
        _ = o * (t * o⁻¹ * t⁻¹) := by group
    refine ⟨X.mul_mem (X.inv_mem hy) ((Subgroup.mem_normalizer_iff.mp (hTX ht) y).mp hy), ?_⟩
    rw [e]
    exact σ.ON.mul_mem ho ((Subgroup.mem_normalizer_iff.mp (hTON ht) _).mp (σ.ON.inv_mem ho))
  obtain ⟨m, hm, hym⟩ := exists_mul_mem_centralizer_of_two_group hT2 hModd hyM hyT hTM
  refine ⟨y * m, ⟨hym, X.mul_mem hy hm.1⟩, m⁻¹ * o, ⟨?_, σ.ON.mul_mem (σ.ON.inv_mem hm.2) ho⟩,
    by group⟩
  have e : m⁻¹ * o = (y * m)⁻¹ * (y * o) := by group
  rw [e]
  exact σ.C.mul_mem (σ.C.inv_mem hym) hcC

private theorem inf_L_subset_mul_of_inf_L₀_subset (hσ : σ.IsValid) (hII : σ.ChapterIIFacts)
    {W : Subgroup G} (hDW : σ.D ⊓ Subgroup.centralizer (σ.T : Set G) ≤ W)
    (h : ((σ.C ⊓ σ.L₀ : Subgroup G) : Set G) ⊆
      (W : Set G) * ((σ.C ⊓ σ.ON : Subgroup G) : Set G)) :
    ((σ.C ⊓ σ.L : Subgroup G) : Set G) ⊆
      (W : Set G) * ((σ.C ⊓ solvRadIn σ.L : Subgroup G) : Set G) := by
  intro c hc
  have hDN : σ.D ⊓ Subgroup.centralizer (σ.T : Set G) ≤ Subgroup.normalizer (σ.L₀ : Set G) :=
    (inf_le_left.trans (σ.D_le_N hσ)).trans hσ.N_le_normalizer_L₀
  have hcL : c ∈ ((σ.L₀ ⊔ (σ.D ⊓ Subgroup.centralizer (σ.T : Set G)) : Subgroup G) : Set G) := by
    rw [← hII.L_eq]
    exact hc.2
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hDN] at hcL
  obtain ⟨l, hl, d, hd, rfl⟩ := hcL
  have hdC : d ∈ σ.C := hd.2
  have hlC : l ∈ σ.C := by
    have := σ.C.mul_mem hc.1 (σ.C.inv_mem hdC)
    simpa using this
  obtain ⟨w, hw, k, hk, rfl⟩ := h ⟨hlC, hl⟩
  refine ⟨w * d, W.mul_mem hw (hDW hd), d⁻¹ * k * d, ⟨?_, ?_⟩, by group⟩
  · exact σ.C.mul_mem (σ.C.mul_mem (σ.C.inv_mem hdC) hk.1) hdC
  · apply σ.ON_le_solvRadIn_L hσ
    have := (Subgroup.mem_normalizer_iff.mp
      (σ.N_le_normalizer_ON (σ.D_le_N hσ (σ.D.inv_mem hd.1))) k).mp hk.2
    simpa using this

private theorem exists_inverted_mem_centralizer (hσ : σ.IsValid) (hII : σ.ChapterIIFacts)
    {r : ℕ} (hr : r.Prime) (hst : ¬ σ.Stationary r) {R : Subgroup G}
    (hR : IsSylowOf r R σ.ON) (hRD : σ.D ≤ Subgroup.normalizer (R : Set G))
    (hcov : (σ.L₀ : Set G) ⊆ (Subgroup.normalizer (R : Set G) : Set G) * (σ.ON : Set G)) :
    ∃ u ∈ Subgroup.centralizer (R : Set G), u ≠ 1 ∧ σ.x * u * σ.x⁻¹ = u⁻¹ ∧
      IsPGroup r (Subgroup.zpowers u) := by
  have : Fact r.Prime := ⟨hr⟩
  have hxH : σ.x ∈ Subgroup.normalizer (R : Set G) := hRD (σ.x_mem_D_nc hσ)
  have hRodd : Odd (Nat.card R) := σ.odd_card_ON.of_dvd_nat (Subgroup.card_dvd_of_le hR.le)
  have hRO : R ≤ oddCoreIn (Subgroup.normalizer (R : Set G)) :=
    le_oddCoreIn Subgroup.le_normalizer le_rfl hRodd
  obtain ⟨R₁, hR₁, hRR₁, hxR₁⟩ := exists_isSylowOf_normalized_ge_of_odd hr
    (isPGroup_two_zpowers hσ.x_order)
    (Subgroup.zpowers_le.mpr (le_normalizer_oddCoreIn _ hxH))
    (odd_card_oddCoreIn _) hRO hR.isPGroup (Subgroup.zpowers_le.mpr hxH)
  have hfix : R₁ ⊓ Subgroup.centralizer {σ.x} = R := by
    have hle : R₁ ⊓ Subgroup.centralizer {σ.x} ≤ σ.ON :=
      (inf_le_inf_right _ hR₁.le).trans (σ.oddCoreIn_inf_N_le_ON_of_cover hσ hII hcov)
    exact hR.eq_of_le (le_inf hRR₁ (hR.le.trans σ.ON_le_N)) hle (hR₁.isPGroup.to_le inf_le_left)
  have hne : R₁ ≠ R := by
    intro h
    rw [h] at hR₁
    exact hst ⟨R, hR, hR₁⟩
  have hlt : R₁ ⊓ Subgroup.centralizer {σ.x} < R₁ := by
    rw [hfix]
    exact lt_of_le_of_ne hRR₁ (Ne.symm hne)
  have hR₁odd : Odd (Nat.card R₁) :=
    (odd_card_oddCoreIn _).of_dvd_nat (Subgroup.card_dvd_of_le hR₁.le)
  obtain ⟨u, ⟨huR₁, hux⟩, hu1, huc⟩ := exists_inverted_centralizing_fixed hR₁.isPGroup hR₁odd
    hσ.x_order (hxR₁ (Subgroup.mem_zpowers _)) hlt
  rw [hfix] at huc
  exact ⟨u, huc, hu1, hux, hR₁.isPGroup.to_le (Subgroup.zpowers_le.mpr huR₁)⟩

theorem lemmaIV78 (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ} (hr : σ.HypIV7 r)
    (hnc : ¬ σ.Constrained r) {P R R₀ : Subgroup G} (hR : IsSylowOf r R σ.ON)
    (hRD : σ.D ≤ Subgroup.normalizer (R : Set G)) (hR₀ : R₀ ≠ ⊥) (hR₀R : R₀ ≤ R)
    (hR₀D : σ.D ≤ Subgroup.normalizer (R₀ : Set G))
    (hR₀P : P ≤ Subgroup.normalizer (R₀ : Set G)) :
    HasQCharPower (Subgroup.normalizer (R₀ : Set G)) σ.q ∧
      (σ.L₀ : Set G) ⊆ (Subgroup.normalizer (R₀ : Set G) : Set G) * (σ.ON : Set G) ∧
      σ.D ⊔ P ≤ Subgroup.normalizer (R₀ : Set G) ∧
      PConstrainedWithin r (Subgroup.normalizer (R₀ : Set G))
        (CFSG.oddCore (Subgroup.normalizer (R₀ : Set G))) := by
  have : Fact r.Prime := ⟨hr.prime⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr2 : r ≠ 2 := σ.prime_ne_two_of_dvd_ON hr.prime hr.dvd_ON
  set H := Subgroup.normalizer (R₀ : Set G) with hH
  have hcovR := (σ.not_constrained_iff_covers hσ hII hr.prime hr.dvd_ON hR).mp hnc
  have hCRH : Subgroup.centralizer (R : Set G) ≤ H :=
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hR₀R)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hcov : (σ.L₀ : Set G) ⊆ (H : Set G) * (σ.ON : Set G) :=
    hcovR.trans (Set.mul_subset_mul_right (SetLike.coe_subset_coe.mpr (inf_le_right.trans hCRH)))
  have hTH : σ.T ≤ H := (σ.T_le_D hσ).trans hR₀D
  have hO : oddCoreIn H ≠ ⊥ :=
    oddCoreIn_ne_bot_of_isPLocal hr.prime hr2 ⟨R₀, hR₀, hR.isPGroup.to_le hR₀R, rfl⟩
  obtain ⟨hQ, hfac⟩ := hII.cover_qgroup H hTH hO hcov
  refine ⟨hQ, hcov, sup_le hR₀D hR₀P, ?_⟩
  have hcovL : (σ.L : Set G) ⊆ (H : Set G) * (σ.ON : Set G) :=
    (σ.L_subset_inf_N_mul_ON_of_cover hσ hII hR₀D hcov).trans
      (Set.mul_subset_mul_right (SetLike.coe_subset_coe.mpr inf_le_left))
  obtain ⟨S', hS'⟩ := σ.exists_sylow_two_le_inf_L hσ hcovL
  obtain ⟨S₀, hS₀, hDS₀⟩ := exists_isSylowOf_ge_of_le hR₀D σ.isPGroup_two_D_nc
  have hS₀idx := not_dvd_index_of_isSylowOf_of_sylow_le hS₀ S' (hS'.trans inf_le_left)
  have hS₀coe : ((hS₀.isPGroup.toSylow hS₀idx : Sylow 2 G) : Subgroup G) = S₀ :=
    IsPGroup.toSylow_coe _ _
  have hcent := hII.center_involution_of_sylow (hS₀.isPGroup.toSylow hS₀idx)
    (by rw [hS₀coe]; exact hDS₀)
  rw [hS₀coe] at hcent
  obtain ⟨Rs, hRs, hS₀Rs⟩ := exists_isSylowOf_normalized_of_odd hr.prime hS₀.isPGroup
    (hS₀.le.trans (le_normalizer_oddCoreIn H)) (odd_card_oddCoreIn H)
  obtain ⟨u, huR, hu1, hux, hur⟩ := σ.exists_inverted_mem_centralizer hσ hII hr.prime
    (fun hst => hr.exceptional ((σ.ordinary_iff hσ hII hr.prime hr.dvd_ON).mpr ⟨hst, hnc⟩))
    hR hRD (hcovR.trans (Set.mul_subset_mul_right (SetLike.coe_subset_coe.mpr
      (inf_le_right.trans (Subgroup.centralizer_le_normalizer _)))))
  have hxH : σ.x ∈ H := hR₀D (σ.x_mem_D_nc hσ)
  have huodd : Odd (orderOf u) := by
    rw [← Nat.card_zpowers]
    exact odd_card_of_isPGroup_of_ne_two hr.prime hr2 hur
  have huO : u ∈ oddCoreIn H := mem_oddCoreIn_of_inverted hxH hfac (hCRH huR) hux huodd
  have hxS₀ : σ.x ∈ S₀ := hDS₀ (σ.x_mem_D_nc hσ)
  have hxRs : σ.x ∉ Subgroup.centralizer (Rs : Set G) :=
    not_mem_centralizer_of_inverted hr.prime (odd_card_oddCoreIn H) hσ.x_order
      (le_normalizer_oddCoreIn H hxH) hRs (hS₀Rs hxS₀) huO hur hu1 hux
  have hS₀C : S₀ ⊓ Subgroup.centralizer (Rs : Set G) = ⊥ := by
    by_contra hne
    have hnorm : S₀ ≤ Subgroup.normalizer
        ((S₀ ⊓ Subgroup.centralizer (Rs : Set G) : Subgroup G) : Set G) :=
      (le_inf Subgroup.le_normalizer
        (hS₀Rs.trans (normalizer_le_normalizer_centralizer_of_subgroup Rs))).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have h1 := inf_centerOf_ne_bot_of_isPGroup hS₀.isPGroup inf_le_left hnorm hne
    obtain ⟨z, hz, hzo⟩ := exists_orderOf_eq_two (hS₀.isPGroup.to_le
      (inf_le_left.trans inf_le_left)) h1
    have hzx : z = σ.x := hcent.2 z hz.2 hzo
    exact hxRs (hzx ▸ hz.1.2)
  have hodd : Odd (Nat.card (H ⊓ Subgroup.centralizer (Rs : Set G) : Subgroup G)) := by
    have hSN : IsSylowOf 2 S₀ (H ⊓ Subgroup.normalizer (Rs : Set G)) :=
      hS₀.of_le (le_inf hS₀.le hS₀Rs) inf_le_left
    have hCN : H ⊓ Subgroup.centralizer (Rs : Set G) ≤ H ⊓ Subgroup.normalizer (Rs : Set G) :=
      inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _)
    have hNC : H ⊓ Subgroup.normalizer (Rs : Set G) ≤
        Subgroup.normalizer ((H ⊓ Subgroup.centralizer (Rs : Set G) : Subgroup G) : Set G) :=
      (inf_le_inf Subgroup.le_normalizer
        (normalizer_le_normalizer_centralizer_of_subgroup Rs)).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have h := hSN.inf_of_le_normalizer hCN hNC
    rw [← inf_assoc, inf_eq_left.mpr hS₀.le, hS₀C] at h
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (not_dvd_card_of_isSylowOf_bot h))
  exact ((hII.qgroup_constraint_criterion H hR₀D hO hcov S₀ hS₀ r hr.prime hr2 Rs hRs
    hS₀Rs).2).mpr hodd

private theorem inf_L₀_subset_centralizer_centerOf_mul (hσ : σ.IsValid) {r : ℕ} (hr : r.Prime)
    (h_II42ii : ⁅σ.C ⊓ σ.L₀, σ.C ⊓ σ.L₀⁆ ≤ σ.ON) {P R : Subgroup G} (hP : IsSylowOf r P σ.C)
    (hR : IsSylowOf r R σ.ON) (hRP : P ≤ Subgroup.normalizer (R : Set G))
    (hcovR : (σ.L₀ : Set G) ⊆ (Subgroup.centralizer (R : Set G) : Set G) * (σ.ON : Set G))
    (h77 : centerOf P ≤ σ.L₀) :
    ((σ.C ⊓ σ.L₀ : Subgroup G) : Set G) ⊆
      ((σ.C ⊓ Subgroup.centralizer (centerOf P : Set G) : Subgroup G) : Set G) *
        ((σ.C ⊓ σ.ON : Subgroup G) : Set G) := by
  have : Fact r.Prime := ⟨hr⟩
  set Q := centerOf P with hQdef
  set A := P ⊓ σ.ON with hAdef
  set X := σ.L₀ ⊓ Subgroup.centralizer (A : Set G) with hXdef
  set H₂ := σ.C ⊓ X with hH₂def
  set K₂ := H₂ ⊓ σ.ON with hK₂def
  set Z₀ := centerOf A with hZ₀def
  have hPC : P ≤ σ.C := hP.le
  have hPN : P ≤ σ.N := hPC.trans σ.C_le_N
  have hAP : A ≤ P := inf_le_left
  have hAp : IsPGroup r A := hP.isPGroup.to_inf_left
  have hAR : A ≤ R := σ.inf_ON_le_of_le_normalizer hr hP.isPGroup hR hRP
  have hXcov : (σ.L₀ : Set G) ⊆ (X : Set G) * (σ.ON : Set G) := by
    intro l hl
    obtain ⟨n, hn, o, ho, rfl⟩ := hcovR hl
    refine ⟨n, ⟨?_, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hAR) hn⟩, o, ho, rfl⟩
    have := σ.L₀.mul_mem hl (σ.L₀.inv_mem (hσ.ON_le_L₀ ho))
    simpa using this
  have hTA : σ.T ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.le_centralizer_iff.mpr (hAP.trans hPC)
  have hTX : σ.T ≤ Subgroup.normalizer (X : Set G) :=
    (le_inf ((σ.T_le_N hσ).trans hσ.N_le_normalizer_L₀) (hTA.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hstep := σ.inf_L₀_subset_mul_of_cover hσ inf_le_left hTX hXcov
  have hH₂CL : H₂ ≤ σ.C ⊓ σ.L₀ := inf_le_inf_left _ inf_le_left
  have hcomm : ∀ a ∈ H₂, ∀ b ∈ H₂, a * b * a⁻¹ * b⁻¹ ∈ K₂ := by
    intro a ha b hb
    refine ⟨H₂.mul_mem (H₂.mul_mem (H₂.mul_mem ha hb) (H₂.inv_mem ha)) (H₂.inv_mem hb), ?_⟩
    apply h_II42ii
    rw [← commutatorElement_def]
    exact Subgroup.commutator_mem_commutator (hH₂CL ha) (hH₂CL hb)
  have hK₂H₂ : K₂ ≤ H₂ := inf_le_left
  have hK₂CON : K₂ ≤ σ.C ⊓ σ.ON := inf_le_inf_right _ inf_le_left
  have hK₂A : K₂ ≤ Subgroup.centralizer (A : Set G) :=
    inf_le_left.trans (inf_le_right.trans inf_le_right)
  have hAsyl : IsSylowOf r A (σ.C ⊓ σ.ON) := by
    have h := hP.inf_of_le_normalizer inf_le_left σ.C_le_normalizer_inf_ON
    rwa [← inf_assoc, inf_eq_left.mpr hPC] at h
  have hZ₀max : ∀ U : Subgroup G, U ≤ K₂ → IsPGroup r U → U ≤ Z₀ := fun U hU hUp =>
    le_centerOf_of_isSylowOf hAsyl (hU.trans hK₂CON) hUp (hU.trans hK₂A)
  have hZ₀A : Z₀ ≤ A := inf_le_left
  have hZ₀p : IsPGroup r Z₀ := hAp.to_le hZ₀A
  have hZ₀K₂ : Z₀ ≤ K₂ := by
    intro z hz
    have hzA := hZ₀A hz
    exact ⟨⟨hPC hzA.1, hσ.ON_le_L₀ hzA.2, hz.2⟩, hzA.2⟩
  have hQP : Q ≤ P := inf_le_left
  have hQp : IsPGroup r Q := hP.isPGroup.to_le hQP
  have hQA : Q ≤ Subgroup.centralizer (A : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hAP))
  have hQH₂ : Q ≤ H₂ := le_inf (hQP.trans hPC) (le_inf h77 hQA)
  have hQZ₀ : Q ≤ Subgroup.normalizer (Z₀ : Set G) :=
    (inf_le_right.trans (Subgroup.centralizer_le
      (SetLike.coe_subset_coe.mpr (hZ₀A.trans hAP)))).trans (Subgroup.centralizer_le_normalizer _)
  have hQ₉p : IsPGroup r (Z₀ ⊔ Q : Subgroup G) := hZ₀p.to_sup_of_normal_left' hQp hQZ₀
  have hH₂K₂ : H₂ ≤ Subgroup.normalizer (K₂ : Set G) :=
    le_normalizer_of_forall_commutator_mem le_rfl hK₂H₂ hcomm
  have hQ₉syl : IsSylowOf r (Z₀ ⊔ Q) (Q ⊔ K₂) :=
    isSylowOf_sup_of_forall_le le_sup_right hQ₉p (sup_le (hZ₀K₂.trans le_sup_right) le_sup_left)
      (hQH₂.trans hH₂K₂) fun U hU hUp => (hZ₀max U hU hUp).trans le_sup_left
  have hfr := subset_inf_normalizer_mul_of_comm hK₂H₂ hQH₂ le_sup_right hcomm hQ₉syl
  have hPA : P ≤ Subgroup.normalizer (A : Set G) :=
    (le_inf Subgroup.le_normalizer (hPN.trans σ.N_le_normalizer_ON)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hPH₂ : P ≤ Subgroup.normalizer (H₂ : Set G) :=
    (le_inf (hPC.trans Subgroup.le_normalizer)
      ((le_inf (hPN.trans hσ.N_le_normalizer_L₀)
        (hPA.trans (normalizer_le_normalizer_centralizer_of_subgroup A))).trans
        Subgroup.inf_normalizer_le_normalizer_inf)).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hS : IsSylowOf r (P ⊓ H₂) H₂ :=
    (hP.of_le le_sup_left (sup_le hPC inf_le_left)).inf_of_le_normalizer le_sup_right
      (sup_le hPH₂ Subgroup.le_normalizer)
  have hPQ₉ : P ≤ Subgroup.normalizer ((Z₀ ⊔ Q : Subgroup G) : Set G) :=
    (le_inf (hPA.trans (normalizer_le_normalizer_centerOf A)) (le_normalizer_centerOf P)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hNnQ : H₂ ⊓ Subgroup.normalizer ((Z₀ ⊔ Q : Subgroup G) : Set G) ≤
      Subgroup.centralizer (Q : Set G) := by
    refine le_centralizer_of_stability
      (hS.of_le (le_inf inf_le_right (inf_le_left.trans hPQ₉)) inf_le_left)
      (inf_le_left.trans (le_centralizer_centerOf P)) le_sup_right hZ₀p
      (inf_le_left.trans ?_) inf_le_right ?_
    · intro g hg
      exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hZ₀A) hg.2.2
    · intro g hg y hy
      have hQ₉K₂ : (Z₀ ⊔ Q) ⊓ K₂ ≤ Z₀ := hZ₀max _ inf_le_right (hQ₉p.to_le inf_le_left)
      apply hQ₉K₂
      refine ⟨(Z₀ ⊔ Q).mul_mem ((Subgroup.mem_normalizer_iff.mp hg.2 y).mp hy)
        ((Z₀ ⊔ Q).inv_mem hy), hcomm g hg.1 y ?_⟩
      exact sup_le (hZ₀K₂.trans hK₂H₂) hQH₂ hy
  intro c hc
  obtain ⟨h, hh, o, ho, rfl⟩ := hstep hc
  obtain ⟨n, hn, k, hk, rfl⟩ := hfr hh
  exact ⟨n, ⟨hn.1.1, hNnQ hn⟩, k * o, (σ.C ⊓ σ.ON).mul_mem (hK₂CON hk) ho, by group⟩

private theorem centerOf_le_centralizer_of_inf_ON_eq_bot {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (h_II42i : ∃ d ∈ σ.D, d ∈ σ.L₀ ∧
      ∀ c ∈ σ.C ⊓ σ.L₀, Odd (orderOf c) → d * c * d⁻¹ * c ∈ σ.ON)
    {P R : Subgroup G} (hP : IsSylowOf r P σ.C) (hPD : σ.D ≤ Subgroup.normalizer (P : Set G))
    (hRD : σ.D ≤ Subgroup.normalizer (R : Set G)) (hRP : P ≤ Subgroup.normalizer (R : Set G))
    (hcovR : (σ.L₀ : Set G) ⊆ (Subgroup.centralizer (R : Set G) : Set G) * (σ.ON : Set G))
    (h77 : centerOf P ≤ σ.L₀) (hPO : P ⊓ σ.ON = ⊥) :
    centerOf P ≤ Subgroup.centralizer (R : Set G) := by
  obtain ⟨d, hdD, hdL₀, hdinv⟩ := h_II42i
  have hPC : P ≤ σ.C := hP.le
  have hQP : centerOf P ≤ P := inf_le_left
  have hPodd : Odd (Nat.card P) := odd_card_of_isPGroup_of_ne_two hr hr2 hP.isPGroup
  have hdQ : ∀ a ∈ centerOf P, d * a * d⁻¹ = a⁻¹ := by
    intro a ha
    have haodd : Odd (orderOf a) := hPodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard P (hQP ha))
    have h1 := hdinv a ⟨hPC (hQP ha), h77 ha⟩ haodd
    have h2 : d * a * d⁻¹ ∈ centerOf P :=
      (Subgroup.mem_normalizer_iff.mp ((hPD.trans (normalizer_le_normalizer_centerOf P)) hdD)
        a).mp ha
    have h3 : d * a * d⁻¹ * a ∈ P ⊓ σ.ON := ⟨P.mul_mem (hQP h2) (hQP ha), h1⟩
    rw [hPO, Subgroup.mem_bot] at h3
    exact eq_inv_of_mul_eq_one_left h3
  have hdR : d ∈ Subgroup.centralizer (R : Set G) := by
    obtain ⟨c, hc, o, ho, hco⟩ := hcovR hdL₀
    have hoR : o ∈ Subgroup.normalizer (R : Set G) := by
      have e : o = c⁻¹ * d := by rw [← hco]; group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.centralizer_le_normalizer _ hc))
        (hRD hdD)
    have hconj : ∀ y ∈ R, d * y * d⁻¹ = o * y * o⁻¹ := by
      intro y hy
      have hy' : o * y * o⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hoR y).mp hy
      have hcy := (Subgroup.mem_centralizer_iff.mp hc) _ hy'
      rw [← hco]
      calc c * o * y * (c * o)⁻¹ = c * (o * y * o⁻¹) * c⁻¹ := by group
        _ = o * y * o⁻¹ := by rw [← hcy, mul_inv_cancel_right]
    have hpow : ∀ j : ℕ, ∀ y ∈ R, d ^ j * y * (d ^ j)⁻¹ = o ^ j * y * (o ^ j)⁻¹ := by
      intro j
      induction j with
      | zero => intro y _; simp
      | succ j ih =>
        intro y hy
        have hy' : o ^ j * y * (o ^ j)⁻¹ ∈ R :=
          (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hoR j) y).mp hy
        calc d ^ (j + 1) * y * (d ^ (j + 1))⁻¹ = d * (d ^ j * y * (d ^ j)⁻¹) * d⁻¹ := by
              rw [pow_succ']; group
          _ = d * (o ^ j * y * (o ^ j)⁻¹) * d⁻¹ := by rw [ih y hy]
          _ = o * (o ^ j * y * (o ^ j)⁻¹) * o⁻¹ := hconj _ hy'
          _ = o ^ (j + 1) * y * (o ^ (j + 1))⁻¹ := by rw [pow_succ']; group
    obtain ⟨k, hk⟩ := σ.isPGroup_two_D_nc ⟨d, hdD⟩
    have hdk : d ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      rw [Subgroup.coe_pow] at this
      exact this
    have hoodd : Odd (orderOf o) := σ.odd_card_ON.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ ho)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := hpow (2 ^ k) y hy
    rw [hdk, one_mul, inv_one, mul_one] at h1
    have hoy : o ^ 2 ^ k ∈ Subgroup.centralizer ({y} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc o ^ 2 ^ k * y = (o ^ 2 ^ k * y * (o ^ 2 ^ k)⁻¹) * o ^ 2 ^ k := by group
        _ = y * o ^ 2 ^ k := by rw [← h1]
    have hoy' := mem_of_pow_mem_of_coprime_orderOf
      (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hoodd)) hoy
    rw [Subgroup.mem_centralizer_singleton_iff] at hoy'
    have h3 : d * y * d⁻¹ = y := by rw [hconj y hy, hoy', mul_inv_cancel_right]
    calc y * d = d * y * d⁻¹ * d := by rw [h3]
      _ = d * y := by group
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hay : a * y * a⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hRP (hQP ha)) y).mp hy
  have hd1 : d * (a * y * a⁻¹) * d⁻¹ = a * y * a⁻¹ := by
    rw [← (Subgroup.mem_centralizer_iff.mp hdR) _ hay, mul_inv_cancel_right]
  have hdy : d * y * d⁻¹ = y := by
    rw [← (Subgroup.mem_centralizer_iff.mp hdR) _ hy, mul_inv_cancel_right]
  have hd2 : d * (a * y * a⁻¹) * d⁻¹ = a⁻¹ * y * a := by
    calc d * (a * y * a⁻¹) * d⁻¹ = (d * a * d⁻¹) * (d * y * d⁻¹) * (d * a * d⁻¹)⁻¹ := by group
      _ = a⁻¹ * y * a := by rw [hdQ a ha, hdy, inv_inv]
  have e := hd1.symm.trans hd2
  have h4 : a * a * y = y * (a * a) := by
    calc a * a * y = a * (a * y * a⁻¹) * a := by group
      _ = a * (a⁻¹ * y * a) * a := by rw [e]
      _ = y * (a * a) := by group
  have haodd : Odd (orderOf a) := hPodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard P (hQP ha))
  have h5 : a ^ 2 ∈ Subgroup.centralizer ({y} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, pow_two]
    exact h4
  have h6 := mem_of_pow_mem_of_coprime_orderOf (Nat.coprime_two_left.mpr haodd) h5
  rw [Subgroup.mem_centralizer_singleton_iff] at h6
  exact h6.symm

private theorem inf_L₀_subset_normalizer_centerOf_mul (hσ : σ.IsValid) {r : ℕ} (hr : r.Prime)
    (h_II42ii : ⁅σ.C ⊓ σ.L₀, σ.C ⊓ σ.L₀⁆ ≤ σ.ON) {P R : Subgroup G} (hP : IsSylowOf r P σ.C)
    (hRD : σ.D ≤ Subgroup.normalizer (R : Set G))
    (hcovR : (σ.L₀ : Set G) ⊆ (Subgroup.centralizer (R : Set G) : Set G) * (σ.ON : Set G))
    (h77 : centerOf P ≤ σ.L₀) (hPO : P ⊓ σ.ON = ⊥)
    (hQR : centerOf P ≤ Subgroup.centralizer (R : Set G)) :
    ((σ.C ⊓ σ.L₀ : Subgroup G) : Set G) ⊆
      ((σ.C ⊓ Subgroup.normalizer (R : Set G) ⊓ Subgroup.normalizer (centerOf P : Set G) :
        Subgroup G) : Set G) * ((σ.C ⊓ σ.ON : Subgroup G) : Set G) := by
  have : Fact r.Prime := ⟨hr⟩
  set Q := centerOf P with hQdef
  set X := σ.L₀ ⊓ Subgroup.centralizer (R : Set G) with hXdef
  set H₂ := σ.C ⊓ X with hH₂def
  set K₂ := H₂ ⊓ σ.ON with hK₂def
  have hPC : P ≤ σ.C := hP.le
  have hXcov : (σ.L₀ : Set G) ⊆ (X : Set G) * (σ.ON : Set G) := by
    intro l hl
    obtain ⟨n, hn, o, ho, rfl⟩ := hcovR hl
    refine ⟨n, ⟨?_, hn⟩, o, ho, rfl⟩
    have := σ.L₀.mul_mem hl (σ.L₀.inv_mem (hσ.ON_le_L₀ ho))
    simpa using this
  have hTX : σ.T ≤ Subgroup.normalizer (X : Set G) :=
    (le_inf ((σ.T_le_N hσ).trans hσ.N_le_normalizer_L₀)
      (((σ.T_le_D hσ).trans hRD).trans (normalizer_le_normalizer_centralizer_of_subgroup R))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hstep := σ.inf_L₀_subset_mul_of_cover hσ inf_le_left hTX hXcov
  have hH₂CL : H₂ ≤ σ.C ⊓ σ.L₀ := inf_le_inf_left _ inf_le_left
  have hcomm : ∀ a ∈ H₂, ∀ b ∈ H₂, a * b * a⁻¹ * b⁻¹ ∈ K₂ := by
    intro a ha b hb
    refine ⟨H₂.mul_mem (H₂.mul_mem (H₂.mul_mem ha hb) (H₂.inv_mem ha)) (H₂.inv_mem hb), ?_⟩
    apply h_II42ii
    rw [← commutatorElement_def]
    exact Subgroup.commutator_mem_commutator (hH₂CL ha) (hH₂CL hb)
  have hK₂H₂ : K₂ ≤ H₂ := inf_le_left
  have hK₂CON : K₂ ≤ σ.C ⊓ σ.ON := inf_le_inf_right _ inf_le_left
  have hCONr : ¬ r ∣ Nat.card (σ.C ⊓ σ.ON : Subgroup G) := by
    have h := hP.inf_of_le_normalizer inf_le_left σ.C_le_normalizer_inf_ON
    rw [← inf_assoc, inf_eq_left.mpr hPC, hPO] at h
    exact not_dvd_card_of_isSylowOf_bot h
  have hQP : Q ≤ P := inf_le_left
  have hQp : IsPGroup r Q := hP.isPGroup.to_le hQP
  have hQH₂ : Q ≤ H₂ := le_inf (hQP.trans hPC) (le_inf h77 hQR)
  have hH₂K₂ : H₂ ≤ Subgroup.normalizer (K₂ : Set G) :=
    le_normalizer_of_forall_commutator_mem le_rfl hK₂H₂ hcomm
  have hQsyl : IsSylowOf r Q (Q ⊔ K₂) :=
    isSylowOf_sup_of_forall_le le_rfl hQp le_sup_left (hQH₂.trans hH₂K₂) fun U hU hUp => by
      rw [eq_bot_of_isPGroup_of_not_dvd (hU.trans hK₂CON) hUp hCONr]
      exact bot_le
  have hfr := subset_inf_normalizer_mul_of_comm hK₂H₂ hQH₂ le_rfl hcomm hQsyl
  intro c hc
  obtain ⟨h, hh, o, ho, rfl⟩ := hstep hc
  obtain ⟨n, hn, k, hk, rfl⟩ := hfr hh
  refine ⟨n, ⟨⟨hn.1.1, Subgroup.centralizer_le_normalizer _ hn.1.2.2⟩, hn.2⟩, k * o,
    (σ.C ⊓ σ.ON).mul_mem (hK₂CON hk) ho, by group⟩

omit [Finite G] in
private theorem le_normalizer_bot_nc (K : Subgroup G) :
    K ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
  intro g _
  rw [Subgroup.mem_normalizer_iff]
  intro h
  simp [Subgroup.mem_bot]

theorem lemmaIV79 (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ} (hr : σ.HypIV7 r)
    (hnc : ¬ σ.Constrained r) {P R : Subgroup G} (hP : IsSylowOf r P σ.C)
    (hPD : σ.D ≤ Subgroup.normalizer (P : Set G)) (hR : IsSylowOf r R σ.ON)
    (hRD : σ.D ≤ Subgroup.normalizer (R : Set G)) (hRP : P ≤ Subgroup.normalizer (R : Set G))
    (h77 : centerOf P ≤ σ.L₀) (h_II42ii : ⁅σ.C ⊓ σ.L₀, σ.C ⊓ σ.L₀⁆ ≤ σ.ON)
    (hPO : P ⊓ σ.ON ≠ ⊥) :
    ∃ d : σ.IV7Data r, d.P = P ∧ d.R = R ∧ d.Q = centerOf P ∧
      d.Nstar = Subgroup.normalizer ((centerOf P ⊓ σ.ON : Subgroup G) : Set G) ∧
      d.Cstar = σ.C ⊓ Subgroup.normalizer (centerOf P : Set G) := by
  have : Fact r.Prime := ⟨hr.prime⟩
  have hr2 : r ≠ 2 := σ.prime_ne_two_of_dvd_ON hr.prime hr.dvd_ON
  have hPC : P ≤ σ.C := hP.le
  have hPN : P ≤ σ.N := hPC.trans σ.C_le_N
  have hcovR := (σ.not_constrained_iff_covers hσ hII hr.prime hr.dvd_ON hR).mp hnc
  have hcovR' : (σ.L₀ : Set G) ⊆ (Subgroup.centralizer (R : Set G) : Set G) * (σ.ON : Set G) :=
    hcovR.trans (Set.mul_subset_mul_right (SetLike.coe_subset_coe.mpr inf_le_right))
  have hQD : σ.D ≤ Subgroup.normalizer (centerOf P : Set G) :=
    hPD.trans (normalizer_le_normalizer_centerOf P)
  have hPON : P ≤ Subgroup.normalizer ((P ⊓ σ.ON : Subgroup G) : Set G) :=
    (le_inf Subgroup.le_normalizer (hPN.trans σ.N_le_normalizer_ON)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hR₀ : centerOf P ⊓ σ.ON ≠ ⊥ := by
    intro hbot
    apply inf_centerOf_ne_bot_of_isPGroup hP.isPGroup inf_le_left hPON hPO
    rw [eq_bot_iff, ← hbot]
    exact le_inf inf_le_right (inf_le_left.trans inf_le_right)
  have hR₀R : centerOf P ⊓ σ.ON ≤ R :=
    (inf_le_inf_right _ (inf_le_left : centerOf P ≤ P)).trans
      (σ.inf_ON_le_of_le_normalizer hr.prime hP.isPGroup hR hRP)
  have hR₀D : σ.D ≤ Subgroup.normalizer ((centerOf P ⊓ σ.ON : Subgroup G) : Set G) :=
    (le_inf hQD ((σ.D_le_N hσ).trans σ.N_le_normalizer_ON)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hR₀P : P ≤ Subgroup.normalizer ((centerOf P ⊓ σ.ON : Subgroup G) : Set G) :=
    (le_inf (le_normalizer_centerOf P) (hPN.trans σ.N_le_normalizer_ON)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  obtain ⟨hQq, hcov, hDP, hcons⟩ := σ.lemmaIV78 hσ hII hr hnc hR hRD hR₀ hR₀R hR₀D hR₀P
  set Ns := Subgroup.normalizer ((centerOf P ⊓ σ.ON : Subgroup G) : Set G) with hNs
  have hDNs : σ.D ≤ Ns := le_sup_left.trans hDP
  have hQNs : centerOf P ≤ Ns := (inf_le_left : centerOf P ≤ P).trans (le_sup_right.trans hDP)
  have hCs : σ.C ⊓ Ns ⊓ Subgroup.normalizer (centerOf P : Set G) =
      σ.C ⊓ Subgroup.normalizer (centerOf P : Set G) := by
    refine le_antisymm (inf_le_inf_right _ inf_le_left) fun c hc => ⟨⟨hc.1, ?_⟩, hc.2⟩
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hc.2, σ.N_le_normalizer_ON (σ.C_le_N hc.1)⟩
  obtain ⟨Rs, hRs, -, hRsD, hRsQ⟩ := exists_sylow_pPrimePCoreIn hr.prime hr2 hcons
    σ.isPGroup_two_D_nc hDNs hQNs (hP.isPGroup.to_le inf_le_left) hQD IsPGroup.of_bot bot_le
    (le_normalizer_bot_nc _) (le_normalizer_bot_nc _)
  have hcovC := σ.inf_L₀_subset_centralizer_centerOf_mul hσ hr.prime h_II42ii hP hR hRP hcovR' h77
  have hCsCov : ((σ.C ⊓ σ.L : Subgroup G) : Set G) ⊆
      ((σ.C ⊓ Ns ⊓ Subgroup.normalizer (centerOf P : Set G) : Subgroup G) : Set G) *
        ((σ.C ⊓ solvRadIn σ.L : Subgroup G) : Set G) := by
    rw [hCs]
    refine σ.inf_L_subset_mul_of_inf_L₀_subset hσ hII
      (le_inf inf_le_right (inf_le_left.trans hQD)) ?_
    exact hcovC.trans (Set.mul_subset_mul_right (SetLike.coe_subset_coe.mpr
      (inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _))))
  have hCsC : σ.C ⊓ Subgroup.centralizer ((centerOf P ⊔ Rs ⊓
      Subgroup.centralizer (centerOf P : Set G) : Subgroup G) : Set G) ≤
        σ.C ⊓ Ns ⊓ Subgroup.normalizer (centerOf P : Set G) := by
    rw [hCs]
    exact inf_le_inf_left _ ((Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr
      le_sup_left)).trans (Subgroup.centralizer_le_normalizer _))
  refine ⟨
    { P := P
      P_sylow := hP
      P_D := hPD
      R := R
      R_sylow := hR
      R_D := hRD
      R_P := hRP
      Q := centerOf P
      Q_ne_bot := centerOf_ne_bot_of_isPGroup hP.isPGroup fun h => hPO (by rw [h, bot_inf_eq])
      Q_le := inf_le_left
      Q_characteristic := centerOf_subgroupOf_characteristic P
      Nstar := Ns
      Nstar_qgroup := hQq.1
      Nstar_constrained := ⟨hcons.1.trans (oddCore_le_solvableRadical_of_finite _), hcons.2⟩
      Nstar_covers := (σ.L_subset_inf_N_mul_ON_of_cover hσ hII hDNs hcov).trans
        (Set.mul_subset_mul_right (SetLike.coe_subset_coe.mpr inf_le_left))
      D_le_Nstar := hDNs
      Q_le_Nstar := hQNs
      Cstar_covers := hCsCov
      Rstar := Rs
      Rstar_sylow := hRs
      Rstar_D := hRsD
      Rstar_Q := hRsQ
      centralizer_le := hCsC
      cases := Or.inl hCs }, rfl, rfl, rfl, rfl, hCs⟩

theorem lemmaIV710 (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ} (hr : σ.HypIV7 r)
    (hnc : ¬ σ.Constrained r) {P R : Subgroup G} (hP : IsSylowOf r P σ.C)
    (hPD : σ.D ≤ Subgroup.normalizer (P : Set G)) (hR : IsSylowOf r R σ.ON)
    (hRD : σ.D ≤ Subgroup.normalizer (R : Set G)) (hRP : P ≤ Subgroup.normalizer (R : Set G))
    (h77 : centerOf P ≤ σ.L₀)
    (h_II42i : ∃ d ∈ σ.D, d ∈ σ.L₀ ∧
      ∀ c ∈ σ.C ⊓ σ.L₀, Odd (orderOf c) → d * c * d⁻¹ * c ∈ σ.ON)
    (h_II42ii : ⁅σ.C ⊓ σ.L₀, σ.C ⊓ σ.L₀⁆ ≤ σ.ON) (hPO : P ⊓ σ.ON = ⊥) :
    ∃ d : σ.IV7Data r, d.P = P ∧ d.R = R ∧ d.Q = centerOf P ∧
      d.Nstar = Subgroup.normalizer (R : Set G) ∧
      R ≤ d.Rstar ⊓ Subgroup.centralizer (centerOf P : Set G) := by
  have : Fact r.Prime := ⟨hr.prime⟩
  have hr2 : r ≠ 2 := σ.prime_ne_two_of_dvd_ON hr.prime hr.dvd_ON
  have hcovR := (σ.not_constrained_iff_covers hσ hII hr.prime hr.dvd_ON hR).mp hnc
  have hcovR' : (σ.L₀ : Set G) ⊆ (Subgroup.centralizer (R : Set G) : Set G) * (σ.ON : Set G) :=
    hcovR.trans (Set.mul_subset_mul_right (SetLike.coe_subset_coe.mpr inf_le_right))
  have hQD : σ.D ≤ Subgroup.normalizer (centerOf P : Set G) :=
    hPD.trans (normalizer_le_normalizer_centerOf P)
  have hQR := σ.centerOf_le_centralizer_of_inf_ON_eq_bot hr.prime hr2 h_II42i hP hPD hRD hRP
    hcovR' h77 hPO
  have hRQ : R ≤ Subgroup.centralizer (centerOf P : Set G) := Subgroup.le_centralizer_iff.mp hQR
  obtain ⟨hQq, hcov, hDP, hcons⟩ := σ.lemmaIV78 hσ hII hr hnc hR hRD
    (ne_bot_of_isSylowOf_of_dvd_nc hr.prime hR hr.dvd_ON) le_rfl hRD hRP
  have hQNs : centerOf P ≤ Subgroup.normalizer (R : Set G) :=
    hQR.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨Rs, hRs, hRRs, hRsD, hRsQ⟩ := exists_sylow_pPrimePCoreIn hr.prime hr2 hcons
    σ.isPGroup_two_D_nc hRD hQNs (hP.isPGroup.to_le inf_le_left) hQD hR.isPGroup
    (le_pPrimePCoreIn_normalizer hR.isPGroup) hRD hQNs
  have hcovC := σ.inf_L₀_subset_normalizer_centerOf_mul hσ hr.prime h_II42ii hP hRD hcovR' h77
    hPO hQR
  have hCsCov := σ.inf_L_subset_mul_of_inf_L₀_subset hσ hII
    (le_inf (le_inf inf_le_right (inf_le_left.trans hRD)) (inf_le_left.trans hQD)) hcovC
  have hCsC : σ.C ⊓ Subgroup.centralizer ((centerOf P ⊔ Rs ⊓
      Subgroup.centralizer (centerOf P : Set G) : Subgroup G) : Set G) ≤
        σ.C ⊓ Subgroup.normalizer (R : Set G) ⊓ Subgroup.normalizer (centerOf P : Set G) := by
    intro c hc
    have hcQ : c ∈ Subgroup.centralizer (centerOf P : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left) hc.2
    have hcR : c ∈ Subgroup.centralizer (R : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr
        ((le_inf hRRs hRQ).trans le_sup_right)) hc.2
    exact ⟨⟨hc.1, Subgroup.centralizer_le_normalizer _ hcR⟩,
      Subgroup.centralizer_le_normalizer _ hcQ⟩
  refine ⟨
    { P := P
      P_sylow := hP
      P_D := hPD
      R := R
      R_sylow := hR
      R_D := hRD
      R_P := hRP
      Q := centerOf P
      Q_ne_bot := centerOf_ne_bot_of_isPGroup hP.isPGroup (ne_bot_of_isSylowOf_of_dvd_nc
        hr.prime hP (hr.dvd_CL.trans (Subgroup.card_dvd_of_le inf_le_left)))
      Q_le := inf_le_left
      Q_characteristic := centerOf_subgroupOf_characteristic P
      Nstar := Subgroup.normalizer (R : Set G)
      Nstar_qgroup := hQq.1
      Nstar_constrained := ⟨hcons.1.trans (oddCore_le_solvableRadical_of_finite _), hcons.2⟩
      Nstar_covers := (σ.L_subset_inf_N_mul_ON_of_cover hσ hII hRD hcov).trans
        (Set.mul_subset_mul_right (SetLike.coe_subset_coe.mpr inf_le_left))
      D_le_Nstar := hRD
      Q_le_Nstar := hQNs
      Cstar_covers := hCsCov
      Rstar := Rs
      Rstar_sylow := hRs
      Rstar_D := hRsD
      Rstar_Q := hRsQ
      centralizer_le := hCsC
      cases := Or.inr ⟨rfl, rfl, hQR⟩ }, rfl, rfl, rfl, rfl, le_inf hRRs hRQ⟩

theorem exists_IV7Data_of_not_constrained (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ}
    (hr : σ.HypIV7 r) (hnc : ¬ σ.Constrained r) {P R : Subgroup G} (hP : IsSylowOf r P σ.C)
    (hPD : σ.D ≤ Subgroup.normalizer (P : Set G)) (hR : IsSylowOf r R σ.ON)
    (hRD : σ.D ≤ Subgroup.normalizer (R : Set G)) (hRP : P ≤ Subgroup.normalizer (R : Set G))
    (h77 : centerOf P ≤ σ.L₀)
    (h_II42i : ∃ d ∈ σ.D, d ∈ σ.L₀ ∧
      ∀ c ∈ σ.C ⊓ σ.L₀, Odd (orderOf c) → d * c * d⁻¹ * c ∈ σ.ON)
    (h_II42ii : ⁅σ.C ⊓ σ.L₀, σ.C ⊓ σ.L₀⁆ ≤ σ.ON) :
    ∃ d : σ.IV7Data r, d.P = P ∧ d.R = R ∧ d.Q = centerOf P := by
  by_cases hPO : P ⊓ σ.ON = ⊥
  · obtain ⟨d, h1, h2, h3, -⟩ :=
      σ.lemmaIV710 hσ hII hr hnc hP hPD hR hRD hRP h77 h_II42i h_II42ii hPO
    exact ⟨d, h1, h2, h3⟩
  · obtain ⟨d, h1, h2, h3, -⟩ := σ.lemmaIV79 hσ hII hr hnc hP hPD hR hRD hRP h77 h_II42ii hPO
    exact ⟨d, h1, h2, h3⟩

end Setting

end CFSG.ABGTheoremB
