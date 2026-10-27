module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralCentralizerBasicsRooting
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralCentralizerBasicsFixedSet
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.EscapingCaseOneFusion

public section

namespace CFSG.ProperTwoGeneratedCore.Assembly

open CFSG.Open CFSG.BenderSuzuki.PFchapter1section1

section Transport

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G}

theorem centralInvolution_exists_sq_of_isConj_sq {z t w : G}
    (hz : IsCentralInvolution (S : Subgroup G) z) (htz : IsConj t z) (hwS : w ∈ (S : Subgroup G))
    (hwt : w ^ 2 = t) : ∃ v ∈ (S : Subgroup G), v ^ 2 = z := by
  obtain ⟨g, hgt, hgS⟩ := centralInvolution_exists_transport hz htz
  refine ⟨g⁻¹ * w * g, hgS w hwS (hwt ▸ Commute.self_pow w 2), ?_⟩
  have h := map_pow (MulAut.conj g⁻¹) w 2
  simp only [MulAut.conj_apply, inv_inv] at h
  rw [← h, hwt, hgt]

theorem centralInvolution_exists_sq_of_centralizer_sq {z w : G}
    (hz : IsCentralInvolution (S : Subgroup G) z) (hwM : w ∈ Subgroup.centralizer ({z} : Set G))
    (hwz : w ^ 2 = z) : ∃ v ∈ (S : Subgroup G), v ^ 2 = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.centralizer ({z} : Set G)
  have hw4 : (⟨w, hwM⟩ : M) ^ 2 ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, show 2 ^ 2 = 2 * 2 by norm_num, pow_mul, hwz,
      ← hz.2.1, pow_orderOf_eq_one]
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hw4)
  have h2 : IsPGroup 2 (Subgroup.zpowers (⟨w, hwM⟩ : M)) :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  obtain ⟨c, hc⟩ := exists_conj_mem_sylow (S.subtype hz.le_centralizer) h2
  have hcS := hc _ (Subgroup.mem_zpowers _)
  rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hcS
  refine ⟨_, hcS, ?_⟩
  have h := map_pow (MulAut.conj (c : G)⁻¹) w 2
  simp only [MulAut.conj_apply, inv_inv] at h
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [← h, hwz, mul_assoc, ← Subgroup.mem_centralizer_singleton_iff.mp c.property,
    inv_mul_cancel_left]

end Transport

section Bar

variable {G : Type} [Group G] [Finite G] {x : G}

theorem escaping_exists_sq_of_bar_sq (hx : orderOf x = 2) {w : EscapingQuotient x}
    (hw : w ^ 2 = escapingBar x) :
    ∃ v : Subgroup.centralizer ({x} : Set G), v ^ 2 = escapingSelf x := by
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective _ w
  set n := Nat.card (pPrimeCore 2 (Subgroup.centralizer ({x} : Set G)))
  set o := (escapingSelf x)⁻¹ * c ^ 2 with ho
  have hoO : o ∈ pPrimeCore 2 (Subgroup.centralizer ({x} : Set G)) := by
    rw [← QuotientGroup.ker_mk' (pPrimeCore 2 (Subgroup.centralizer ({x} : Set G))),
      MonoidHom.mem_ker, ho, map_mul, map_inv, map_pow, hw, inv_mul_cancel]
  have hon : o ^ n = 1 := by
    have h1 : (⟨o, hoO⟩ : pPrimeCore 2 (Subgroup.centralizer ({x} : Set G))) ^ n = 1 :=
      pow_card_eq_one'
    simpa only [SubgroupClass.coe_pow, OneMemClass.coe_one] using congrArg Subtype.val h1
  have hxo : Commute (escapingSelf x) o :=
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp o.property).symm
  have hc2 : c ^ 2 = escapingSelf x * o := by rw [ho, mul_inv_cancel_left]
  have hxx : escapingSelf x ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hx, pow_orderOf_eq_one]
  obtain ⟨k, hk⟩ : Odd n := escaping_oddCore_odd x
  refine ⟨c ^ n, ?_⟩
  rw [← pow_mul, mul_comm, pow_mul, hc2, hxo.mul_pow, hon, mul_one, hk, pow_succ, pow_mul, hxx,
    one_pow, one_mul]

theorem centralInvolution_not_sq_bar {S : Sylow 2 G} {z : G}
    (hz : IsCentralInvolution (S : Subgroup G) z) (hsq : ∀ v ∈ (S : Subgroup G), v ^ 2 ≠ z)
    (w : EscapingQuotient z) : w ^ 2 ≠ escapingBar z := by
  intro hw
  obtain ⟨v, hv⟩ := escaping_exists_sq_of_bar_sq hz.2.1 hw
  obtain ⟨u, huS, hu⟩ := centralInvolution_exists_sq_of_centralizer_sq hz v.property
    (by simpa using congrArg Subtype.val hv)
  exact hsq u huS hu

end Bar

section NormalTwo

variable {X : Type} [Group X] [Finite X]

theorem isPGroup_two_of_normal_of_twoElements_commute (hodd : pPrimeCore 2 X = ⊥)
    {N : Subgroup X} [hN : N.Normal]
    (hcomm : ∀ n ∈ N, ∀ k : ℕ, n ^ 2 ^ k = 1 → ∀ m ∈ N, Commute n m) : IsPGroup 2 N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T⟩ : Nonempty (Sylow 2 N) := inferInstance
  have hT : Subgroup.normalizer ((T : Subgroup N) : Set N) ≤
      Subgroup.centralizer ((T : Subgroup N) : Set N) := by
    intro g _ t ht
    obtain ⟨k, hk⟩ := T.isPGroup' ⟨t, ht⟩
    have hk' : (t : X) ^ 2 ^ k = 1 := by
      simpa using congrArg (fun y : (T : Subgroup N) => ((y : N) : X)) hk
    exact Subtype.ext (hcomm t t.property k hk' g g.property).eq
  have hcomp := MonoidHom.ker_transferSylow_isComplement' T hT
  have hcop : Nat.Coprime 2 (Nat.card (MonoidHom.transferSylow T hT).ker) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
      (MonoidHom.not_dvd_card_ker_transferSylow T hT)
  have hcoreN : pPrimeCore 2 N = ⊥ :=
    CFSG.RankThreeCoreUniqueness.Helpers.cfsg_subnormal_primeComplementCore_eq_bot 2 N
      (IsSubnormal.step le_top Subgroup.normal_subgroupOf (IsSubnormal.refl ⊤)) hodd
  have hker := CFSG.pPrimeCore_eq_bot_iff.mp hcoreN _ inferInstance hcop
  rw [hker, Subgroup.isComplement'_bot_left] at hcomp
  intro g
  obtain ⟨k, hk⟩ := T.isPGroup' ⟨g, hcomp ▸ Subgroup.mem_top g⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem exists_orderOf_eq_two_pow_of_pow_eq_one {Y : Type*} [Group Y] {n : Y} {k : ℕ}
    (hn : n ^ 2 ^ k = 1) : ∃ j ≤ k, orderOf n = 2 ^ j :=
  (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hn)

theorem normal_le_zpowers_of_unique_involution (hodd : pPrimeCore 2 X = ⊥) {t : X}
    (htc : t ∈ Subgroup.center X) {N : Subgroup X} [N.Normal]
    (hinv : ∀ n ∈ N, orderOf n = 2 → n = t) (hsq : ∀ n ∈ N, n ^ 2 ≠ t) :
    N ≤ Subgroup.zpowers t := by
  have hcases : ∀ n ∈ N, ∀ k : ℕ, n ^ 2 ^ k = 1 → n = 1 ∨ n = t := by
    intro n hnN k hk
    obtain ⟨j, -, hj⟩ := exists_orderOf_eq_two_pow_of_pow_eq_one hk
    rcases j with _ | _ | j
    · left
      rwa [pow_zero, orderOf_eq_one_iff] at hj
    · right
      exact hinv n hnN (by rw [hj, zero_add, pow_one])
    · exfalso
      have hdvd : 2 ^ j ∣ orderOf n := hj ▸ pow_dvd_pow 2 (by omega)
      have hm : orderOf (n ^ 2 ^ j) = 4 := by
        rw [orderOf_pow_of_dvd (by positivity) hdvd, hj, pow_add, pow_add,
          Nat.mul_assoc, Nat.mul_div_cancel_left _ (by positivity)]
        norm_num
      have hm2 : orderOf ((n ^ 2 ^ j) ^ 2) = 2 := by
        rw [orderOf_pow_of_dvd (by norm_num) (by rw [hm]; norm_num), hm]
      exact hsq _ (N.pow_mem hnN _) (hinv _ (N.pow_mem (N.pow_mem hnN _) _) hm2)
  have hcentral : ∀ n ∈ N, ∀ k : ℕ, n ^ 2 ^ k = 1 → ∀ m ∈ N, Commute n m := by
    intro n hnN k hk m _
    rcases hcases n hnN k hk with h | h
    · rw [h]
      exact Commute.one_left m
    · rw [h]
      exact (Subgroup.mem_center_iff.mp htc m).symm
  have h2 := isPGroup_two_of_normal_of_twoElements_commute hodd hcentral
  intro n hnN
  obtain ⟨k, hk⟩ := h2 ⟨n, hnN⟩
  rcases hcases n hnN k (by simpa using congrArg Subtype.val hk) with h | h
  · rw [h]
    exact Subgroup.one_mem _
  · rw [h]
    exact Subgroup.mem_zpowers t

end NormalTwo

section Kernel

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {x : G}
  (hset : CoreSetting G S H) (hxH : x ∈ H) (hx : orderOf x = 2)
include hset hxH hx

theorem coreSetting_oddCore_le_fixedSetKernel
    (hesc : ¬ Subgroup.centralizer ({x} : Set G) ≤ H) :
    pPrimeCore 2 (Subgroup.centralizer ({x} : Set G)) ≤
      (fixedSetKernel H x).subgroupOf (Subgroup.centralizer ({x} : Set G)) := by
  have hq := escapingQuotientData hset hxH hx hesc
  set M := Subgroup.centralizer ({x} : Set G)
  set P := (pPrimeCore 2 M).map M.subtype
  have hPM : P ≤ M := Subgroup.map_subtype_le _
  have hPH : P ≤ H := by
    rintro _ ⟨o, ho, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hq.oddCore_le ho)
  have hMP : M ≤ Subgroup.normalizer (P : Set G) := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hPM).mp ?_
    have hPQ : P.subgroupOf M = pPrimeCore 2 M :=
      Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
    rw [hPQ]
    infer_instance
  intro o ho
  exact Subgroup.mem_subgroupOf.mpr
    (coreSetting_le_fixedSetKernel_of_normalized hset hxH hx hPH hPM hMP ⟨o, ho, rfl⟩)

theorem coreSetting_map_fixedSetKernel_eq_zpowers
    (hesc : ¬ Subgroup.centralizer ({x} : Set G) ≤ H)
    (hsq : ∀ w : EscapingQuotient x, w ^ 2 ≠ escapingBar x) :
    ((fixedSetKernel H x).subgroupOf (Subgroup.centralizer ({x} : Set G))).map (escapingMk x) =
      Subgroup.zpowers (escapingBar x) := by
  have hq := escapingQuotientData hset hxH hx hesc
  set M := Subgroup.centralizer ({x} : Set G)
  have hKM : fixedSetKernel H x ≤ M := inf_le_left
  have hnormal : ((fixedSetKernel H x).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mpr
      (centralizer_le_normalizer_fixedSetKernel x)
  have := hnormal.map (escapingMk x) (QuotientGroup.mk'_surjective _)
  refine le_antisymm (normal_le_zpowers_of_unique_involution hq.oddCore_eq_bot hq.bar_mem_center
    ?_ fun n _ => hsq n) ?_
  · rintro _ ⟨k, hk, rfl⟩ hk2
    obtain ⟨hord, himage⟩ := orderOf_pow_card_eq_two (escaping_oddCore_odd x) hk2
    have hkK : ((k ^ Nat.card (pPrimeCore 2 M) : M) : G) ∈ fixedSetKernel H x :=
      Subgroup.mem_subgroupOf.mp ((fixedSetKernel H x).subgroupOf M |>.pow_mem hk _)
    have heq := coreSetting_fixedSetKernel_involution_eq hset hxH hx hesc hkK
      (by rwa [Subgroup.orderOf_coe])
    rw [← himage, eq_escapingSelf heq]
  · exact Subgroup.zpowers_le.mpr ⟨escapingSelf x,
      Subgroup.mem_subgroupOf.mpr (self_mem_fixedSetKernel x), rfl⟩

theorem coreSetting_fixedSetKernel_eq_comap_zpowers
    (hesc : ¬ Subgroup.centralizer ({x} : Set G) ≤ H)
    (hsq : ∀ w : EscapingQuotient x, w ^ 2 ≠ escapingBar x) :
    (fixedSetKernel H x).subgroupOf (Subgroup.centralizer ({x} : Set G)) =
      (Subgroup.zpowers (escapingBar x)).comap (escapingMk x) := by
  rw [← coreSetting_map_fixedSetKernel_eq_zpowers hset hxH hx hesc hsq, Subgroup.comap_map_eq,
    QuotientGroup.ker_mk', sup_eq_left.mpr (coreSetting_oddCore_le_fixedSetKernel hset hxH hx hesc)]

end Kernel

end CFSG.ProperTwoGeneratedCore.Assembly
