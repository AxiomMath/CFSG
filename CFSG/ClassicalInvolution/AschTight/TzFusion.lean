module

public import CFSG.ClassicalInvolution.AschTight.TzConj
public import CFSG.ClassicalInvolution.AschTight.OmegaD

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G]

theorem isPGroup_of_mem_rSet {Ω : Set (Subgroup G)} {R : Subgroup G} (hR : R ∈ RSet Ω) :
    IsPGroup 2 R := by
  obtain ⟨J, -, P, rfl⟩ := hR
  exact P.isPGroup'.map _

theorem quaternionGroup_a_mul_xa_ne {n : ℕ} (hn : 2 ≤ n) :
    (QuaternionGroup.a 1 : QuaternionGroup n) * QuaternionGroup.xa 0 ≠
      QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by
  rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a]
  intro h
  have h' : (0 - 1 : ZMod (2 * n)) = 0 + 1 := QuaternionGroup.xa.inj h
  have h2 : ((2 : ℕ) : ZMod (2 * n)) = 0 := by
    push_cast
    linear_combination -h'
  rw [ZMod.natCast_eq_zero_iff] at h2
  have : 2 * n ≤ 2 := Nat.le_of_dvd (by norm_num) h2
  omega

variable {p f : ℕ} [Fact p.Prime] [Finite G] {K : Subgroup G} {z : G}

theorem exists_ne_comm_of_mem_rSet (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hK : IsClassicalMember p f K z)
    {R : Subgroup G} (hR : R ∈ RSet (CoreAssembly.conjClass K)) :
    (∃ x ∈ R, ∃ y ∈ R, x * y ≠ y * x) ∧ 8 ≤ Nat.card R := by
  obtain ⟨J, hJ, P, rfl⟩ := hR
  obtain ⟨g, rfl⟩ := CoreAssembly.single_class K J hJ
  obtain ⟨r, hr, ⟨e⟩⟩ := quaternion_sylow_of_isClassicalMember hp hq (hK.conj g) P
  let e' : ↥((P : Subgroup ↥(conjSub g K)).map (conjSub g K).subtype) ≃*
      QuaternionGroup (2 ^ (r - 2)) :=
    (Subgroup.equivMapOfInjective _ _ (conjSub g K).subtype_injective).symm.trans e
  have hn : 2 ≤ 2 ^ (r - 2) :=
    le_of_eq_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 1 ≤ r - 2))
  refine ⟨⟨(e'.symm (QuaternionGroup.a 1) : G), (e'.symm _).2,
    (e'.symm (QuaternionGroup.xa 0) : G), (e'.symm _).2, fun h => ?_⟩, ?_⟩
  · apply quaternionGroup_a_mul_xa_ne hn
    apply e'.symm.injective
    rw [map_mul, map_mul]
    exact Subtype.ext h
  · have : NeZero (2 ^ (r - 2)) := ⟨by positivity⟩
    rw [Nat.card_congr e'.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    omega

theorem isUniqueInvolution_of_mem_rSet_of_le (ht : S19R.TightStdDelta p f K z) {R : Subgroup G}
    (hR : R ∈ RSet (CoreAssembly.conjClass K)) (hRK : R ≤ K) : IsUniqueInvolution R z := by
  have hI := isUniqueInvolution_of_tight ht
  have h8 := (exists_ne_comm_of_mem_rSet ht.branch.odd ht.branch.five ht.branch.member hR).2
  obtain ⟨k, hk⟩ := (isPGroup_of_mem_rSet hR).exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [hk, pow_zero] at h8
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 (hk ▸ dvd_pow_self 2 hk0)
  have hu' : orderOf (u : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hu
  have huz : (u : G) = z := (uniqueInvolutionNormal_of_tight ht).2.2.1 _ (hRK u.2) hu'
  exact ⟨huz ▸ u.2, hI.ne_one, hI.sq, fun y hy hy2 => hI.unique y (hRK hy) hy2⟩

theorem exists_mul_self_eq_of_mem_uSet (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hK : IsClassicalMember p f K z) {V : Subgroup G} (hV : V ∈ USet (CoreAssembly.conjClass K))
    {t : G} (htV : t ∈ V) (ht2 : orderOf t = 2) : ∃ w ∈ V, w * w = t := by
  obtain ⟨R, hR, hVR, hcyc, hidx⟩ := hV
  have h8 := (exists_ne_comm_of_mem_rSet hp hq hK hR).2
  have hcard : 2 * Nat.card V = Nat.card R := by
    have h := Subgroup.relIndex_mul_card (H := V) (K := R)
    rwa [hidx, inf_of_le_left hVR] at h
  obtain ⟨k, hk⟩ := ((isPGroup_of_mem_rSet hR).to_le hVR).exists_card_eq
  have hk2 : 2 ≤ k := by
    by_contra h
    have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := V)
  have hord : orderOf (g : G) = 2 ^ k := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hk]
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨t, htV⟩)
  have hi' : (g : G) ^ i = t := by rw [← Subgroup.coe_zpow, hi]
  obtain ⟨v, hv⟩ : ∃ v : G, (g : G) = v := ⟨_, rfl⟩
  rw [hv] at hord hi'
  refine ⟨v ^ (2 ^ (k - 2)), hv ▸ V.pow_mem g.2 _, ?_⟩
  have e : v ^ (2 ^ (k - 2)) * v ^ (2 ^ (k - 2)) = v ^ ((2 ^ (k - 1) : ℕ) : ℤ) := by
    rw [← pow_add, zpow_natCast, ← two_mul, ← pow_succ', show k - 2 + 1 = k - 1 by omega]
  have hv1 : v ^ ((2 ^ (k - 1) : ℕ) : ℤ) * v ^ ((2 ^ (k - 1) : ℕ) : ℤ) = 1 := by
    rw [← zpow_add, ← Nat.cast_add, zpow_natCast, ← two_mul, ← pow_succ',
      show k - 1 + 1 = k by omega, ← hord, pow_orderOf_eq_one]
  have hv2 : v ^ ((2 ^ (k - 1) : ℕ) : ℤ) ≠ 1 := by
    rw [zpow_natCast]
    exact pow_ne_one_of_lt_orderOf (pow_ne_zero _ two_ne_zero)
      (by rw [hord]; exact Nat.pow_lt_pow_right (by norm_num) (by omega))
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht2
    omega
  have htt : t * t = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
  calc v ^ (2 ^ (k - 2)) * v ^ (2 ^ (k - 2)) = v ^ ((2 ^ (k - 1) : ℕ) : ℤ) := e
    _ = v ^ i := zpow_eq_zpow_of_mul_self_eq_one hv1 (by rw [hi']; exact htt) hv2
        (by rw [hi']; exact ht1)
    _ = t := hi'

theorem exists_conj_eq_mul_of_sixTwo (ht : S19R.TightStd p f K z) {t : G} (ht2 : orderOf t = 2)
    (htz : t ≠ z) (hzt : t * z = z * t) {V : Subgroup G} (htV : t ∈ V)
    (hVz : V ≤ Subgroup.centralizer ({z} : Set G))
    (h62 : (V = Subgroup.zpowers t ∧ conjSub t K ≠ K) ∨
      (V = Subgroup.zpowers t ∧ ∃ R ∈ RSet (CoreAssembly.conjClass K), R ≤ K ∧
        V ≤ Subgroup.normalizer (R : Set G) ∧ IsSemidihedral (R ⊔ V)) ∨
      (V ∈ USet (CoreAssembly.conjClass K) ∧ ∃ R ∈ RSet (CoreAssembly.conjClass K), R ≤ K ∧
        V ≤ Subgroup.normalizer (R : Set G) ∧ IsWreathed (R ⊔ V)) ∨
      V ∈ RSet (CoreAssembly.conjClass K)) :
    ∃ k ∈ K, k * t * k⁻¹ = z * t := by
  have htb := ht.toTightBranch
  have hNC := normalizer_eq_centralizer_of_tight htb
  have hU := uniqueInvolutionNormal_of_tight htb
  have htt : t * t = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht2
    omega
  have htK : t ∉ K := fun h => htz (hU.2.2.1 t h ht2)
  rcases h62 with ⟨-, hne⟩ | ⟨hVt, R, hR, hRK, hVR, hsd⟩ | ⟨hVU, R, hR, hRK, hVR, hwr⟩ | hVR
  ·
    exfalso
    apply hne
    apply conjSub_eq_of_mem_normalizer
    rw [hNC, Subgroup.mem_centralizer_singleton_iff]
    exact hzt
  ·
    have hzR := isUniqueInvolution_of_mem_rSet_of_le htb hR hRK
    obtain ⟨r, hr, hrt⟩ := exists_conj_eq_mul_of_isSemidihedral (isPGroup_of_mem_rSet hR) hzR
      htt (fun h => htK (hRK h)) (hVR htV) (by rw [← hVt]; exact hsd)
    exact ⟨r, hRK hr, hrt⟩
  ·
    have hzR := isUniqueInvolution_of_mem_rSet_of_le htb hR hRK
    have hnc := (exists_ne_comm_of_mem_rSet ht.branch.odd ht.branch.five ht.branch.member hR).1
    obtain ⟨r, hr, hrt⟩ := exists_conj_eq_mul_of_isWreathed hzR hnc hVR htV htt ht1 htz
      (exists_mul_self_eq_of_mem_uSet ht.branch.odd ht.branch.five ht.branch.member hVU htV ht2)
      hwr
    exact ⟨r, hRK hr, hrt⟩
  ·
    exfalso
    obtain ⟨J, hJ, P, hVP⟩ := hVR
    have hVJ : V ≤ J := hVP ▸ Subgroup.map_subtype_le _
    by_cases hJK : J = K
    · exact htK (hJK ▸ hVJ htV)
    · apply ht.edgeless K (CoreAssembly.mem_conjClass_self K) J hJ
      left
      refine ⟨hJ, hJK, V, ⟨J, hJ, P, hVP⟩, hVJ, ?_⟩
      rw [hNC]
      exact hVz

theorem conj_eq_mul_of_sixTwo (ht : S19R.TightStd p f K z) {g : G} (htz : g * z * g⁻¹ ≠ z)
    (hzt : g * z * g⁻¹ * z = z * (g * z * g⁻¹)) {V : Subgroup G} (htV : g * z * g⁻¹ ∈ V)
    (hVz : V ≤ Subgroup.centralizer ({z} : Set G))
    (h62 : (V = Subgroup.zpowers (g * z * g⁻¹) ∧ conjSub (g * z * g⁻¹) K ≠ K) ∨
      (V = Subgroup.zpowers (g * z * g⁻¹) ∧ ∃ R ∈ RSet (CoreAssembly.conjClass K), R ≤ K ∧
        V ≤ Subgroup.normalizer (R : Set G) ∧ IsSemidihedral (R ⊔ V)) ∨
      (V ∈ USet (CoreAssembly.conjClass K) ∧ ∃ R ∈ RSet (CoreAssembly.conjClass K), R ≤ K ∧
        V ≤ Subgroup.normalizer (R : Set G) ∧ IsWreathed (R ⊔ V)) ∨
      V ∈ RSet (CoreAssembly.conjClass K)) :
    ∃ x : G, x * z * x⁻¹ = z * (g * z * g⁻¹) := by
  have ht2 : orderOf (g * z * g⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact (uniqueInvolutionNormal_of_tight ht.toTightBranch).1
  obtain ⟨k, -, hk⟩ := exists_conj_eq_mul_of_sixTwo ht ht2 htz hzt htV hVz h62
  exact ⟨k * g, by rw [← hk]; group⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight
