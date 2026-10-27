module

public import CFSG.GH74.QTGen4.Recog.G23.P7.LeafWrappers
public import CFSG.GroupTheory.BurnsideNormalComplement
public import CFSG.GroupTheory.ABGLocalTools.OddInvolution
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourOfCommutingInvolutions
public import CFSG.GH74.QTGen4.Recog.G23.HK2

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable

variable {G : Type} [Group G]

namespace PbarMixedAux

theorem orderOf_conj_aux' (n x : G) : orderOf (n * x * n⁻¹) = orderOf x := by
  have h := orderOf_injective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective x
  simpa [MulAut.conj_apply] using h

theorem odd_mem_of_sq_mem {Y K : Subgroup G} (hsq : ∀ x ∈ Y, x ^ 2 ∈ K) {x : G} (hx : x ∈ Y)
    (hodd : Odd (orderOf x)) : x ∈ K := by
  obtain ⟨m, hm⟩ := hodd
  have hpow : x ^ orderOf x = 1 := pow_orderOf_eq_one x
  have h1 : x ^ (2 * (m + 1)) = x := by
    have h2 : 2 * (m + 1) = orderOf x + 1 := by omega
    rw [h2, pow_succ, hpow, one_mul]
  have h2 : (x ^ 2) ^ (m + 1) = x := by rw [← pow_mul, h1]
  rw [← h2]
  exact K.pow_mem (hsq x hx) (m + 1)

theorem odd_orderOf_of_mem {K : Subgroup G} [Finite G] (hK : Odd (Nat.card K)) {k : G}
    (hk : k ∈ K) : Odd (orderOf k) := by
  have h := orderOf_dvd_natCard (⟨k, hk⟩ : K)
  rw [Subgroup.orderOf_mk] at h
  exact Odd.of_dvd_nat hK h

theorem eq_one_or_eq_of_mem_zpowers {Γ : Type*} [Group Γ] {g w : Γ} (hg : orderOf g = 2)
    (hw : w ∈ Subgroup.zpowers g) : w = 1 ∨ w = g := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have h := zpow_mod_orderOf g k
  rw [hg] at h
  simp only [Nat.cast_ofNat] at h
  have hmod : k % 2 = 0 ∨ k % 2 = 1 := Int.emod_two_eq_zero_or_one k
  rcases hmod with h0 | h1
  · left; rw [← h, h0, zpow_zero]
  · right; rw [← h, h1, zpow_one]

theorem not_two_dvd_index_zpowers [Finite G] {Y : Subgroup G} {z : G} (hzY : z ∈ Y)
    (hz2 : orderOf z = 2) (hY2 : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ Y → Nat.card R ≤ 2) :
    ¬ 2 ∣ (Subgroup.zpowers (⟨z, hzY⟩ : ↥Y)).index := by
  intro hdvd
  have hcard : Nat.card (Subgroup.zpowers (⟨z, hzY⟩ : ↥Y)) = 2 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hz2]
  have h4 : 2 ^ 2 ∣ Nat.card ↥Y := by
    rw [← Subgroup.card_mul_index (Subgroup.zpowers (⟨z, hzY⟩ : ↥Y)), hcard]
    obtain ⟨k, hk⟩ := hdvd
    exact ⟨k, by rw [hk]; ring⟩
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥Y) 2 h4
  have hQinj : Function.Injective (Y.subtype) := Subtype.val_injective
  have hQ2 : IsPGroup 2 (Q.map Y.subtype) := IsPGroup.of_card (n := 2) (by
    rw [Subgroup.card_map_of_injective hQinj, hQ])
  have hle := hY2 _ hQ2 (Subgroup.map_subtype_le Q)
  rw [Subgroup.card_map_of_injective hQinj, hQ] at hle
  norm_num at hle


theorem orderOf_sq_eq_one_of_orderOf_two {g : G} (hg : orderOf g = 2) : g ^ 2 = 1 := by
  rw [← hg]; exact pow_orderOf_eq_one g

theorem exists_normal_two_complement [Finite G] {Y : Subgroup G} {z : G} (hzY : z ∈ Y)
    (hz2 : orderOf z = 2) (hY2 : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ Y → Nat.card R ≤ 2) :
    ∃ K : Subgroup G, K ≤ Y ∧ (∀ c ∈ Y, ∀ k ∈ K, c * k * c⁻¹ ∈ K) ∧ Odd (Nat.card K) ∧
      (∀ x ∈ Y, x ^ 2 ∈ K) ∧ (∀ x ∈ Y, x ∈ K ∨ x * z ∈ K) ∧ K ⊓ Subgroup.zpowers z = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx := not_two_dvd_index_zpowers hzY hz2 hY2
  have hzY2 : orderOf (⟨z, hzY⟩ : ↥Y) = 2 := by rw [Subgroup.orderOf_mk, hz2]
  have hP : IsPGroup 2 (Subgroup.zpowers (⟨z, hzY⟩ : ↥Y)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzY2]; norm_num)
  let S0 : Sylow 2 ↥Y := hP.toSylow hidx
  have hS0 : (S0 : Subgroup ↥Y) = Subgroup.zpowers (⟨z, hzY⟩ : ↥Y) :=
    IsPGroup.toSylow_coe hP hidx
  have hS0card : Nat.card (S0 : Subgroup ↥Y) = 2 := by rw [hS0, Nat.card_zpowers, hzY2]
  have hz_sq : z ^ 2 = 1 := orderOf_sq_eq_one_of_orderOf_two hz2
  have hzz : z * z = 1 := by rw [← pow_two]; exact hz_sq
  have hN : Subgroup.normalizer ((S0 : Subgroup ↥Y) : Set ↥Y) ≤
      Subgroup.centralizer ((S0 : Subgroup ↥Y) : Set ↥Y) := by
    rw [hS0]
    intro g hg
    have hgz : g * (⟨z, hzY⟩ : ↥Y) * g⁻¹ ∈ Subgroup.zpowers (⟨z, hzY⟩ : ↥Y) :=
      (Subgroup.mem_normalizer_iff.mp hg _).mp (Subgroup.mem_zpowers _)
    have hne : g * (⟨z, hzY⟩ : ↥Y) * g⁻¹ ≠ 1 := by
      intro h1
      have h2 : (⟨z, hzY⟩ : ↥Y) = 1 := by
        have := congrArg (fun x => g⁻¹ * x * g) h1
        simpa [mul_assoc] using this
      have h3 : orderOf (⟨z, hzY⟩ : ↥Y) = 1 := by rw [h2, orderOf_one]
      rw [hzY2] at h3
      exact absurd h3 (by norm_num)
    have heq : g * (⟨z, hzY⟩ : ↥Y) * g⁻¹ = ⟨z, hzY⟩ :=
      (eq_one_or_eq_of_mem_zpowers hzY2 hgz).resolve_left hne
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    have hcomm : Commute (⟨z, hzY⟩ : ↥Y) g := by
      show (⟨z, hzY⟩ : ↥Y) * g = g * (⟨z, hzY⟩ : ↥Y)
      calc (⟨z, hzY⟩ : ↥Y) * g = (g * (⟨z, hzY⟩ : ↥Y) * g⁻¹) * g := by rw [heq]
        _ = g * (⟨z, hzY⟩ : ↥Y) := by group
    exact (hcomm.zpow_left k).eq
  obtain ⟨K, hKn, hKp, hKidx, -, -, -, hsup, hinf, -, -⟩ :=
    CFSG.GroupTheory.burnside_normal_complement S0 hN
  haveI := hKn
  have hKidx2 : K.index = 2 := by rw [hKidx]; exact hS0card
  refine ⟨K.map Y.subtype, Subgroup.map_subtype_le K, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc k hk
    obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.mp hk
    refine Subgroup.mem_map.mpr ⟨(⟨c, hc⟩ : ↥Y) * k' * (⟨c, hc⟩ : ↥Y)⁻¹,
      hKn.conj_mem k' hk' ⟨c, hc⟩, ?_⟩
    simp
  · rw [Subgroup.card_map_of_injective Subtype.val_injective]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hKp)
  · intro x hx
    have h1 : (⟨x, hx⟩ : ↥Y) ^ 2 ∈ K := by
      have := Subgroup.pow_index_mem K (⟨x, hx⟩ : ↥Y)
      rwa [hKidx2] at this
    exact Subgroup.mem_map.mpr ⟨_, h1, by simp⟩
  · intro x hx
    have hmem : (⟨x, hx⟩ : ↥Y) ∈ K ⊔ (S0 : Subgroup ↥Y) := by
      rw [hsup]; exact Subgroup.mem_top _
    obtain ⟨y, hy, w, hw, hyw⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
    rw [hS0] at hw
    rcases eq_one_or_eq_of_mem_zpowers hzY2 hw with rfl | rfl
    · left
      exact Subgroup.mem_map.mpr ⟨y, hy, by simpa using congrArg Subtype.val hyw⟩
    · right
      refine Subgroup.mem_map.mpr ⟨y, hy, ?_⟩
      have h : (y : G) * z = x := by simpa using congrArg Subtype.val hyw
      show (y : G) = x * z
      calc (y : G) = (y : G) * z * z := by rw [mul_assoc, hzz, mul_one]
        _ = x * z := by rw [h]
  · rw [eq_bot_iff]
    rintro x ⟨hxK, hxz⟩
    obtain ⟨x', hx'K, rfl⟩ := Subgroup.mem_map.mp hxK
    have hx'S : x' ∈ (S0 : Subgroup ↥Y) := by
      rw [hS0]
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxz
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
      simpa using hk
    have h1 : x' ∈ K ⊓ (S0 : Subgroup ↥Y) := ⟨hx'K, hx'S⟩
    rw [hinf, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot, h1, map_one]

theorem exists_conj_of_involution [Finite G] {Y : Subgroup G} {z : G} (hzY : z ∈ Y)
    (hz2 : orderOf z = 2) (hY2 : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ Y → Nat.card R ≤ 2)
    {u : G} (huY : u ∈ Y) (hu2 : orderOf u = 2) : ∃ c ∈ Y, c * u * c⁻¹ = z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx := not_two_dvd_index_zpowers hzY hz2 hY2
  have hzY2 : orderOf (⟨z, hzY⟩ : ↥Y) = 2 := by rw [Subgroup.orderOf_mk, hz2]
  have huY2 : orderOf (⟨u, huY⟩ : ↥Y) = 2 := by rw [Subgroup.orderOf_mk, hu2]
  have hP : IsPGroup 2 (Subgroup.zpowers (⟨z, hzY⟩ : ↥Y)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzY2]; norm_num)
  have hu : IsPGroup 2 (Subgroup.zpowers (⟨u, huY⟩ : ↥Y)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, huY2]; norm_num)
  let S0 : Sylow 2 ↥Y := hP.toSylow hidx
  have hS0 : (S0 : Subgroup ↥Y) = Subgroup.zpowers (⟨z, hzY⟩ : ↥Y) :=
    IsPGroup.toSylow_coe hP hidx
  obtain ⟨Q, hQ⟩ := hu.exists_le_sylow
  haveI : Finite (Sylow 2 ↥Y) := S0.finite_of_finiteIndex
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥Y S0 Q
  have huQ : (⟨u, huY⟩ : ↥Y) ∈ (Q : Subgroup ↥Y) := hQ (Subgroup.mem_zpowers _)
  have h1 : (⟨u, huY⟩ : ↥Y) ∈ ((g • S0 : Sylow 2 ↥Y) : Subgroup ↥Y) := by
    rw [hg]; exact huQ
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
  have h2 : (MulAut.conj g)⁻¹ • (⟨u, huY⟩ : ↥Y) = g⁻¹ * (⟨u, huY⟩ : ↥Y) * g := by
    ext
    simp [MulAut.conj_apply]
  rw [h2, hS0] at h1
  have hu1 : (⟨u, huY⟩ : ↥Y) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at huY2
    norm_num at huY2
  have hcu : g⁻¹ * (⟨u, huY⟩ : ↥Y) * g ≠ 1 := by
    intro h
    apply hu1
    have h' : (⟨u, huY⟩ : ↥Y) = g * 1 * g⁻¹ := by
      rw [← h]; group
    rw [h']; group
  have heq := (eq_one_or_eq_of_mem_zpowers hzY2 h1).resolve_left hcu
  refine ⟨(g⁻¹ : ↥Y), (g⁻¹ : ↥Y).2, ?_⟩
  have := congrArg Subtype.val heq
  simpa using this

theorem le_sup_of_frattini [Finite G] {Y K T Nn : Subgroup G} {z : G} (hzY : z ∈ Y)
    (hz2 : orderOf z = 2) (hY2 : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ Y → Nat.card R ≤ 2)
    (hNY : ∀ n ∈ Nn, ∀ x ∈ Y, n * x * n⁻¹ ∈ Y) (hYNn : Y ≤ Nn) (hYKT : Y ≤ K ⊔ T)
    (hC : ∀ n ∈ Nn, n * z = z * n → n ∈ K ⊔ T) : Nn ≤ K ⊔ T := by
  intro n hn
  have huY : n * z * n⁻¹ ∈ Y := hNY n hn z hzY
  have hu2 : orderOf (n * z * n⁻¹) = 2 := by rw [orderOf_conj_aux', hz2]
  obtain ⟨c, hcY, hc⟩ := exists_conj_of_involution hzY hz2 hY2 huY hu2
  have hcn : (c * n) * z = z * (c * n) := by
    have h1 : c * n * z * (c * n)⁻¹ = z := by
      calc c * n * z * (c * n)⁻¹ = c * (n * z * n⁻¹) * c⁻¹ := by group
        _ = z := hc
    calc c * n * z = (c * n * z * (c * n)⁻¹) * (c * n) := by group
      _ = z * (c * n) := by rw [h1]
  have h1 : c * n ∈ K ⊔ T := hC (c * n) (Nn.mul_mem (hYNn hcY) hn) hcn
  have h2 : c⁻¹ ∈ K ⊔ T := hYKT (Y.inv_mem hcY)
  have hn' : n = c⁻¹ * (c * n) := by group
  rw [hn']
  exact (K ⊔ T).mul_mem h2 h1


theorem conj_fixes_of_mem_centralizer {S : Set G} {y : G} (hy : y ∈ Subgroup.centralizer S)
    {h : G} (hh : h ∈ S) : y * h * y⁻¹ = h := by
  have h1 := Subgroup.mem_centralizer_iff.mp hy h hh
  rw [← h1, mul_inv_cancel_right]

theorem centralizer_le_normalizer' {S : Set G} :
    Subgroup.centralizer S ≤ Subgroup.normalizer S := by
  intro x hx
  rw [Subgroup.mem_set_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [conj_fixes_of_mem_centralizer hx hh]
    exact hh
  · intro hs
    have hxinv : x⁻¹ ∈ Subgroup.centralizer S := (Subgroup.centralizer S).inv_mem hx
    have h1 := conj_fixes_of_mem_centralizer hxinv hs
    have h2 : h = x * h * x⁻¹ := by
      calc h = x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ := by group
        _ = x * h * x⁻¹ := h1
    rw [h2]
    exact hs

theorem conj_mem_centralizer_of_normalizer {S : Set G} {n x : G}
    (hn : n ∈ Subgroup.normalizer S) (hx : x ∈ Subgroup.centralizer S) :
    n * x * n⁻¹ ∈ Subgroup.centralizer S := by
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have hn' : n⁻¹ ∈ Subgroup.normalizer S := (Subgroup.normalizer S).inv_mem hn
  have hs' : n⁻¹ * s * n⁻¹⁻¹ ∈ S := (Subgroup.mem_set_normalizer_iff.mp hn' s).mp hs
  have hc := Subgroup.mem_centralizer_iff.mp hx _ hs'
  calc s * (n * x * n⁻¹) = n * ((n⁻¹ * s * n⁻¹⁻¹) * x) * n⁻¹ := by group
    _ = n * (x * (n⁻¹ * s * n⁻¹⁻¹)) * n⁻¹ := by rw [hc]
    _ = (n * x * n⁻¹) * s := by group

theorem mem_centralizer_zpowers_of {x y : G} (hx : x ∈ Subgroup.centralizer {y}) :
    x ∈ Subgroup.centralizer (Subgroup.zpowers y : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
  have hc : Commute x y := Subgroup.mem_centralizer_singleton_iff.mp hx
  exact ((hc.zpow_right k).eq).symm

theorem centralizer_singleton_of_zpowers {w y : G}
    (hw : w ∈ Subgroup.centralizer (Subgroup.zpowers y : Set G)) :
    w ∈ Subgroup.centralizer {y} := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact ((Subgroup.mem_centralizer_iff.mp hw) y (Subgroup.mem_zpowers y)).symm

theorem mem_sup_zpowers_of_comm {P : Subgroup G} {z : G} (hz : ∀ p ∈ P, p * z = z * p) {x : G}
    (hx : x ∈ P ⊔ Subgroup.zpowers z) : ∃ p ∈ P, ∃ i : ℤ, x = p * z ^ i := by
  have hcomm : ∀ p ∈ P, ∀ i : ℤ, p * z ^ i = z ^ i * p := fun p hp i =>
    (Commute.zpow_right (show Commute p z from hz p hp) i).eq
  let S : Subgroup G :=
    { carrier := {x | ∃ p ∈ P, ∃ i : ℤ, x = p * z ^ i}
      one_mem' := ⟨1, P.one_mem, 0, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨p, hp, i, rfl⟩ ⟨q, hq, j, rfl⟩
        refine ⟨p * q, P.mul_mem hp hq, i + j, ?_⟩
        calc p * z ^ i * (q * z ^ j) = p * (z ^ i * q) * z ^ j := by group
          _ = p * (q * z ^ i) * z ^ j := by rw [← hcomm q hq i]
          _ = p * q * z ^ (i + j) := by rw [zpow_add]; group
      inv_mem' := by
        rintro _ ⟨p, hp, i, rfl⟩
        refine ⟨p⁻¹, P.inv_mem hp, -i, ?_⟩
        calc (p * z ^ i)⁻¹ = z ^ (-i) * p⁻¹ := by group
          _ = p⁻¹ * z ^ (-i) := (hcomm p⁻¹ (P.inv_mem hp) (-i)).symm }
  have hle : P ⊔ Subgroup.zpowers z ≤ S := by
    refine sup_le (fun p hp => ⟨p, hp, 0, by simp⟩) ?_
    rw [Subgroup.zpowers_le]
    exact ⟨1, P.one_mem, 1, by simp⟩
  have hxS : x ∈ S := hle hx
  exact hxS

theorem card_two_le_of_le_sup [Finite G] {P : Subgroup G} {z : G}
    (hz : ∀ p ∈ P, p * z = z * p) (hz2 : orderOf z = 2) (h3 : ∀ p ∈ P, p ^ 3 = 1)
    {R : Subgroup G} (hR : IsPGroup 2 R) (hRX : R ≤ P ⊔ Subgroup.zpowers z) :
    Nat.card R ≤ 2 := by
  have hz_sq : z ^ 2 = 1 := orderOf_sq_eq_one_of_orderOf_two hz2
  have hRz : R ≤ Subgroup.zpowers z := by
    intro x hxR
    obtain ⟨p, hp, i, rfl⟩ := mem_sup_zpowers_of_comm hz (hRX hxR)
    obtain ⟨k, hk⟩ := hR ⟨_, hxR⟩
    have hk' : (p * z ^ i) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simp only [pow_zero, pow_one] at hk'
      rw [hk']
      exact Subgroup.one_mem _
    · have hy2 : (z ^ i) ^ 2 = 1 := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz_sq, one_zpow]
      have hpy : Commute p (z ^ i) := Commute.zpow_right (show Commute p z from hz p hp) i
      have hy2k : (z ^ i) ^ (2 ^ k) = 1 := by
        obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
        rw [pow_succ, mul_comm, pow_mul, hy2, one_pow]
      have hpk : p ^ (2 ^ k) = 1 := by
        rw [hpy.mul_pow, hy2k, mul_one] at hk'
        exact hk'
      have hdvd1 : orderOf p ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hpk
      have hdvd2 : orderOf p ∣ 3 := orderOf_dvd_of_pow_eq_one (h3 p hp)
      have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
      have h1 : orderOf p ∣ Nat.gcd (2 ^ k) 3 := Nat.dvd_gcd hdvd1 hdvd2
      rw [hcop.gcd_eq_one] at h1
      have hp1 : p = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)
      rw [hp1, one_mul]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) i
  calc Nat.card R ≤ Nat.card (Subgroup.zpowers z) := Subgroup.card_le_of_le hRz
    _ = 2 := by rw [Nat.card_zpowers, hz2]

theorem inf_centralizer_eq_of_decomp {Y K P : Subgroup G} {z : G} (hPK : P ≤ K) (hKY : K ≤ Y)
    (hPz : ∀ p ∈ P, p * z = z * p) (hKz : K ⊓ Subgroup.zpowers z = ⊥)
    (hYX : ∀ x ∈ Y, x * z = z * x → x ∈ P ⊔ Subgroup.zpowers z) :
    K ⊓ Subgroup.centralizer {z} = P := by
  ext x
  constructor
  · rintro ⟨hxK, hxC⟩
    have hxz : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
    obtain ⟨p, hp, i, rfl⟩ := mem_sup_zpowers_of_comm hPz (hYX _ (hKY hxK) hxz)
    have hzi : z ^ i ∈ K ⊓ Subgroup.zpowers z := by
      constructor
      · have hz' : z ^ i = p⁻¹ * (p * z ^ i) := by group
        rw [hz']
        exact K.mul_mem (K.inv_mem (hPK hp)) hxK
      · exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) i
    rw [hKz, Subgroup.mem_bot] at hzi
    rw [hzi, mul_one]
    exact hp
  · intro hxP
    exact ⟨hPK hxP, Subgroup.mem_centralizer_singleton_iff.mpr (hPz x hxP)⟩

theorem inf_centralizer_eq_bot_of_card {P H : Subgroup G} {t : G} [Finite G] (hPH : P ≤ H)
    (hP9 : Nat.card P = 9) (ht8 : Nat.card ↥(Subgroup.centralizer {t} ⊓ H) = 8) :
    P ⊓ Subgroup.centralizer {t} = ⊥ := by
  have h1 := Subgroup.card_dvd_of_le (inf_le_left : P ⊓ Subgroup.centralizer {t} ≤ P)
  rw [hP9] at h1
  have h2 := Subgroup.card_dvd_of_le
    (show P ⊓ Subgroup.centralizer {t} ≤ Subgroup.centralizer {t} ⊓ H from
      fun x hx => ⟨hx.2, hPH hx.1⟩)
  rw [ht8] at h2
  have h3 : Nat.card ↥(P ⊓ Subgroup.centralizer {t}) = 1 := by
    have := Nat.dvd_gcd h1 h2
    exact Nat.dvd_one.mp (by simpa using this)
  exact Subgroup.card_eq_one.mp h3

theorem dvd_nine_of_odd_cent {H : Subgroup G} {z g u : G} (hCz : Subgroup.centralizer {z} = H)
    (hodd9 : ∀ S : Subgroup G, S ≤ H → Odd (Nat.card S) → Nat.card S ∣ 9)
    (hgu : g * z * g⁻¹ = u) {S : Subgroup G} (hS : S ≤ Subgroup.centralizer {u})
    (hSodd : Odd (Nat.card S)) : Nat.card S ∣ 9 := by
  have hmap : Nat.card (S.map (MulAut.conj g⁻¹).toMonoidHom) = Nat.card S :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hle : S.map (MulAut.conj g⁻¹).toMonoidHom ≤ H := by
    rintro _ ⟨s, hs, rfl⟩
    rw [← hCz, Subgroup.mem_centralizer_singleton_iff]
    have hsu := Subgroup.mem_centralizer_singleton_iff.mp (hS hs)
    rw [← hgu] at hsu
    show (g⁻¹ * s * g⁻¹⁻¹) * z = z * (g⁻¹ * s * g⁻¹⁻¹)
    calc (g⁻¹ * s * g⁻¹⁻¹) * z = g⁻¹ * (s * (g * z * g⁻¹)) * g⁻¹⁻¹ := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * s) * g⁻¹⁻¹ := by rw [hsu]
      _ = z * (g⁻¹ * s * g⁻¹⁻¹) := by group
  have hodd' : Odd (Nat.card (S.map (MulAut.conj g⁻¹).toMonoidHom)) := by
    rw [hmap]; exact hSodd
  have := hodd9 _ hle hodd'
  rwa [hmap] at this

theorem isPGroup_three_of_dvd {K : Subgroup G} [Finite G] {a b : ℕ}
    (hK : Nat.card K = a * 9 * b) (ha : a ∣ 9) (hb : b ∣ 9) :
    IsPGroup 3 K ∧ Nat.card K ≤ 3 ^ 6 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h9 : (9 : ℕ) = 3 ^ 2 := by norm_num
  rw [h9] at ha hb
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp ha
  obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hb
  have hcard : Nat.card K = 3 ^ (2 + i + j) := by rw [hK]; ring
  refine ⟨(IsPGroup.iff_card).mpr ⟨2 + i + j, hcard⟩, ?_⟩
  rw [hcard]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem closure_pair_eq_kleinFour {t z : G} (ht : t * t = 1) (hz : z * z = 1) (hc : Commute t z) :
    Subgroup.closure ({t, z} : Set G) =
      CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions t z ht hz hc := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    change x ∈ ({t * z, t, z, 1} : Set G)
    rcases hx with rfl | rfl <;> simp
  · intro x hx
    change x ∈ ({t * z, t, z, 1} : Set G) at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.one_mem _


theorem core_of_normalizer [Finite G] {Y Nn E P : Subgroup G} {z t : G} [IsKleinFour E]
    (hzY : z ∈ Y) (hz2 : orderOf z = 2)
    (hY2 : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ Y → Nat.card R ≤ 2)
    (hPY : P ≤ Y) (hYX : ∀ x ∈ Y, x * z = z * x → x ∈ P ⊔ Subgroup.zpowers z)
    (hP3 : ∀ p ∈ P, p ^ 3 = 1) (hPz : ∀ p ∈ P, p * z = z * p)
    (hNY : ∀ n ∈ Nn, ∀ x ∈ Y, n * x * n⁻¹ ∈ Y) (hYNn : Y ≤ Nn) (hEN : E ≤ Nn)
    (hNnC : ∀ n ∈ Nn, n * z = z * n → n ∈ P ⊔ E)
    (htE : t ∈ E) (hzE : z ∈ E) (ht1 : t ≠ 1) (htz : t ≠ z)
    (hgt : ∃ g : G, g * z * g⁻¹ = t) (hgtz : ∃ g : G, g * z * g⁻¹ = t * z)
    (hdvd9 : ∀ u : G, (∃ g : G, g * z * g⁻¹ = u) → ∀ S : Subgroup G,
      S ≤ Subgroup.centralizer {u} → Odd (Nat.card S) → Nat.card S ∣ 9)
    (hPt : P ⊓ Subgroup.centralizer {t} = ⊥) (hP9 : Nat.card P = 9) :
    ∃ K : Subgroup G, K ≤ Y ∧ IsCentComplement Y (Subgroup.zpowers z) K ∧ IsPGroup 3 K ∧
      Nat.card K ≤ 3 ^ 6 ∧ P ≤ K ∧ K ⊓ Subgroup.centralizer {z} = P ∧
      (∀ m ∈ K, t * m * t⁻¹ ∈ K) ∧ Nn = K ⊔ E := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    norm_num at hz2
  have hz_mul : z * z = 1 := by
    rw [← pow_two]; exact orderOf_sq_eq_one_of_orderOf_two hz2
  obtain ⟨K, hKY, hKc, hKodd, hKsq, hKcos, hKz⟩ := exists_normal_two_complement hzY hz2 hY2
  have hPK : P ≤ K := fun p hp =>
    odd_mem_of_sq_mem hKsq (hPY hp)
      (Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one (hP3 p hp)))
  have hconj : ∀ n ∈ Nn, ∀ k ∈ K, n * k * n⁻¹ ∈ K := fun n hn k hk =>
    odd_mem_of_sq_mem hKsq (hNY n hn k (hKY hk))
      (by rw [orderOf_conj_aux']; exact odd_orderOf_of_mem hKodd hk)
  have hKK : K ⊓ Subgroup.centralizer {z} = P :=
    inf_centralizer_eq_of_decomp hPK hKY hPz hKz hYX
  have hKZ : K ⊔ Subgroup.zpowers z = Y := by
    apply le_antisymm
    · exact sup_le hKY (Subgroup.zpowers_le.mpr hzY)
    · intro x hx
      rcases hKcos x hx with h | h
      · exact Subgroup.mem_sup_left h
      · have hx' : x = x * z * z := by rw [mul_assoc, hz_mul, mul_one]
        rw [hx']
        exact (K ⊔ Subgroup.zpowers z).mul_mem (Subgroup.mem_sup_left h)
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
  have hcomp : IsCentComplement Y (Subgroup.zpowers z) K :=
    { left_le := hKY
      right_le := Subgroup.zpowers_le.mpr hzY
      conj_mem := fun c hc k hk => hKc c hc k hk
      odd_card := hKodd
      disjoint := hKz
      sup_eq := hKZ }
  have hYKE : Y ≤ K ⊔ E := by
    rw [← hKZ]
    exact sup_le_sup_left (Subgroup.zpowers_le.mpr hzE) K
  have hNnKE : Nn ≤ K ⊔ E :=
    le_sup_of_frattini hzY hz2 hY2 hNY hYNn hYKE
      (fun n hn hc => sup_le_sup_right hPK E (hNnC n hn hc))
  have hKE : K ⊔ E ≤ Nn := sup_le (hKY.trans hYNn) hEN
  have hNeq : Nn = K ⊔ E := le_antisymm hNnKE hKE
  have hconjt : ∀ m ∈ K, t * m * t⁻¹ ∈ K := hconj t (hEN htE)
  have hTK : E ≤ Subgroup.normalizer (K : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hconj n (hEN hn) h hh
    · intro hh
      have h1 := hconj n⁻¹ (Nn.inv_mem (hEN hn)) _ hh
      rwa [show n⁻¹ * (n * h * n⁻¹) * n⁻¹⁻¹ = h by group] at h1
  have hKEc : K ⊓ Subgroup.centralizer (E : Set G) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxK, hxE⟩
    have hxz : z * x = x * z := (Subgroup.mem_centralizer_iff.mp hxE) z hzE
    have hxt : t * x = x * t := (Subgroup.mem_centralizer_iff.mp hxE) t htE
    have hxP : x ∈ P := by
      rw [← hKK]
      exact ⟨hxK, Subgroup.mem_centralizer_singleton_iff.mpr hxz.symm⟩
    have hxPt : x ∈ P ⊓ Subgroup.centralizer {t} :=
      ⟨hxP, Subgroup.mem_centralizer_singleton_iff.mpr hxt.symm⟩
    rw [hPt] at hxPt
    exact hxPt
  have hBW := CFSG.ABGLocalTools.card_mul_card_centralizer_four_sq (T := E) (K := K)
    hKodd hTK htE hzE ht1 hz1 htz
  rw [hKEc, Subgroup.card_bot, hKK, hP9, one_pow, mul_one] at hBW
  have hodd_t : Odd (Nat.card ↥(K ⊓ Subgroup.centralizer {t})) :=
    Odd.of_dvd_nat hKodd (Subgroup.card_dvd_of_le inf_le_left)
  have hodd_tz : Odd (Nat.card ↥(K ⊓ Subgroup.centralizer {t * z})) :=
    Odd.of_dvd_nat hKodd (Subgroup.card_dvd_of_le inf_le_left)
  have ha9 := hdvd9 t hgt (K ⊓ Subgroup.centralizer {t}) inf_le_right hodd_t
  have hb9 := hdvd9 (t * z) hgtz (K ⊓ Subgroup.centralizer {t * z}) inf_le_right hodd_tz
  obtain ⟨hPG, hcard⟩ := isPGroup_three_of_dvd hBW ha9 hb9
  exact ⟨K, hKY, hcomp, hPG, hcard, hPK, hKK, hconjt, hNeq⟩


end PbarMixedAux

open PbarMixedAux

theorem zOf_facts [Finite G] {T H H₁ H₂ M : Subgroup G} {e : Fin 6 → G}
    (h : Setup G T H H₁ H₂ M e) (hF : HFacts H H₁ H₂ e) :
    orderOf (zOf e) = 2 ∧ zOf e ∈ H₁ ⊓ H₂ ∧ Subgroup.centralizer {zOf e} = H := by
  have hH : G23One H H₁ H₂ := h.ctx.one
  have hL : HLetters H H₁ H₂ e := h.lets
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have he0H₁ : e 0 ∈ H₁ := by rw [← hL.gen₁]; exact Subgroup.subset_closure (by simp)
  have he1H₁ : e 1 ∈ H₁ := by rw [← hL.gen₁]; exact Subgroup.subset_closure (by simp)
  have he2H₂ : e 2 ∈ H₂ := by rw [← hL.gen₂]; exact Subgroup.subset_closure (by simp)
  have he3H₂ : e 3 ∈ H₂ := by rw [← hL.gen₂]; exact Subgroup.subset_closure (by simp)
  have hR7 : (e 0 * e 1) ^ 2 = (e 2 * e 3) ^ 2 := by
    have h7 := hL.rels [(0, true), (1, true), (0, true), (1, true), (3, false), (2, false),
      (3, false), (2, false)] (by simp [g23WordsH])
    have h2 : (e 0 * e 1) ^ 2 * ((e 3)⁻¹ * (e 2)⁻¹) ^ 2 = 1 := by
      simpa [FreeGroup.lift_mk, pow_two, mul_assoc] using h7
    rw [eq_inv_of_mul_eq_one_left h2]
    simp only [pow_two, mul_inv_rev, inv_inv]
  have hzH₁ : zOf e ∈ H₁ := H₁.pow_mem (H₁.mul_mem he0H₁ he1H₁) 2
  have hzH₂ : zOf e ∈ H₂ := by
    show (e 0 * e 1) ^ 2 ∈ H₂
    rw [hR7]
    exact H₂.pow_mem (H₂.mul_mem he2H₂ he3H₂) 2
  have hzinf : zOf e ∈ H₁ ⊓ H₂ := ⟨hzH₁, hzH₂⟩
  have hsq : zOf e ^ 2 = 1 := CFSG.GH74.QTGen4.Recog.G23.G23One.sq_inf hH hzinf
  have hzne : zOf e ≠ 1 := by
    intro hz0
    obtain ⟨w, hwmem, hw1, -⟩ := CFSG.GH74.QTGen4.Recog.G23.G23One.exists_unique_inf hH
    have he0H : e 0 ∈ H := hH.le_one he0H₁
    have hwC : w ∈ Subgroup.centralizer {e 0} ⊓ H₁ := by
      refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, hwmem.1⟩
      exact (CFSG.GH74.QTGen4.Recog.G23.G23One.mul_comm_of_mem_inf hH he0H hwmem).symm
    rw [hF.centL₁, hz0, Subgroup.zpowers_one_eq_bot, sup_bot_eq] at hwC
    have hwP : w ∈ Psub e :=
      Subgroup.zpowers_le.mpr
        (show e 0 ∈ Psub e from Subgroup.subset_closure (Set.mem_insert _ _)) hwC
    have hw3 : w ^ 3 = 1 := hF.elem_P.2 w hwP
    have hw2 : w ^ 2 = 1 := CFSG.GH74.QTGen4.Recog.G23.G23One.sq_inf hH hwmem
    apply hw1
    calc w = w ^ 3 * (w ^ 2)⁻¹ := by group
      _ = 1 := by rw [hw3, hw2]; simp
  have hord : orderOf (zOf e) = 2 := orderOf_eq_prime hsq hzne
  have hCz : Subgroup.centralizer {zOf e} = H := by
    ext g
    rw [Subgroup.mem_centralizer_singleton_iff, hH.eq_centralizer, Subgroup.mem_centralizer_iff]
    constructor
    · intro hg s hs
      obtain ⟨w, -, -, huniq⟩ := CFSG.GH74.QTGen4.Recog.G23.G23One.exists_unique_inf hH
      rcases huniq s hs with h1 | h1
      · rw [h1]; simp
      · have hzw : zOf e = w := (huniq _ hzinf).resolve_left hzne
        rw [h1, ← hzw]
        exact hg.symm
    · intro hg
      exact (hg (zOf e) hzinf).symm
  exact ⟨hord, hzinf, hCz⟩

theorem leafPbarMixed [G23Leaf LeafSylow2Cent] : LeafPbarMixed := by
  intro G _ _ T H H₁ H₂ M e h hF hO
  obtain ⟨hz2, hzinf, hCz⟩ := zOf_facts h hF
  have hH : G23One H H₁ H₂ := h.ctx.one
  have hL : HLetters H H₁ H₂ e := h.lets
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzsq : zOf e ^ 2 = 1 := by rw [← hz2]; exact pow_orderOf_eq_one _
  have hz_mul : zOf e * zOf e = 1 := by rw [← pow_two]; exact hzsq
  have he0H : e 0 ∈ H := by rw [← hL.gen]; exact Subgroup.subset_closure ⟨0, rfl⟩
  have he2H : e 2 ∈ H := by rw [← hL.gen]; exact Subgroup.subset_closure ⟨2, rfl⟩
  have he4H : e 4 ∈ H := by rw [← hL.gen]; exact Subgroup.subset_closure ⟨4, rfl⟩
  have hPH : Psub e ≤ H := by
    show Subgroup.closure ({e 0, e 2} : Set G) ≤ H
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact he0H
    · exact he2H
  have hP3 : ∀ p ∈ Psub e, p ^ 3 = 1 := fun p hp => hF.elem_P.2 p hp
  have hcommH : ∀ g ∈ H, g * zOf e = zOf e * g := fun g hg => by
    have hgC : g ∈ Subgroup.centralizer {zOf e} := by rw [hCz]; exact hg
    exact Subgroup.mem_centralizer_singleton_iff.mp hgC
  have hPz : ∀ p ∈ Psub e, p * zOf e = zOf e * p := fun p hp => hcommH p (hPH hp)
  have hPC : Psub e ≤ Subgroup.centralizer (Psub e : Set G) := fun p hp => by
    have h1 : p ∈ Psub e ⊔ Subgroup.zpowers (zOf e) := Subgroup.mem_sup_left hp
    rw [← hF.centP] at h1
    exact h1.1
  have hzC : zOf e ∈ Subgroup.centralizer (Psub e : Set G) :=
    Subgroup.mem_centralizer_iff.mpr (fun p hp => hPz p hp)
  have hY2_of : ∀ (Y : Subgroup G), zOf e ∈ Y →
      Y ⊓ Subgroup.centralizer {zOf e} = Psub e ⊔ Subgroup.zpowers (zOf e) →
      ∀ R : Subgroup G, IsPGroup 2 R → R ≤ Y → Nat.card R ≤ 2 := by
    intro Y hzY hYH R hR hRY
    refine sylow2_le_two_of_cent hz2 hzY ?_ R hR hRY
    intro R' hR' hR'le
    exact card_two_le_of_le_sup hPz hz2 hP3 hR' (hR'le.trans hYH.le)
  have hYH_P : Subgroup.centralizer (Psub e : Set G) ⊓ Subgroup.centralizer {zOf e} =
      Psub e ⊔ Subgroup.zpowers (zOf e) := by
    rw [hCz, hF.centP]
  have hY2_P := hY2_of _ hzC hYH_P
  have hP9 : Nat.card (Psub e) = 9 := hF.card_P
  have htE : e 4 ∈ Esub e := by
    show e 4 ∈ Subgroup.closure ({e 4, zOf e} : Set G)
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hzE : zOf e ∈ Esub e := by
    show zOf e ∈ Subgroup.closure ({e 4, zOf e} : Set G)
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have ht2 : e 4 ^ 2 = 1 := by
    have h4 := hL.rels [(4, true), (4, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, pow_two, mul_assoc] using h4
  have ht_mul : e 4 * e 4 = 1 := by rw [← pow_two]; exact ht2
  have ht1 : e 4 ≠ 1 := by
    intro h1
    have h8 := hF.card_cent_t
    rw [h1] at h8
    have hTriv : Subgroup.centralizer {(1 : G)} ⊓ H = H := by
      ext x
      constructor
      · intro hx
        exact hx.2
      · intro hx
        exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr (by simp), hx⟩
    rw [hTriv, hF.card_H] at h8
    norm_num at h8
  have htz : e 4 ≠ zOf e := by
    intro h1
    have h8 := hF.card_cent_t
    rw [h1, hCz, inf_idem, hF.card_H] at h8
    norm_num at h8
  have he4C : e 4 ∈ Subgroup.centralizer {zOf e} := by rw [hCz]; exact he4H
  have hcomm : Commute (e 4) (zOf e) := Subgroup.mem_centralizer_singleton_iff.mp he4C
  have ht_ord : orderOf (e 4) = 2 := orderOf_eq_prime ht2 ht1
  have htz_ord : orderOf (e 4 * zOf e) = 2 := by
    have hsq' : (e 4 * zOf e) ^ 2 = 1 := by
      rw [hcomm.mul_pow, ht2, hzsq, one_mul]
    have hne : e 4 * zOf e ≠ 1 := by
      intro h1
      apply htz
      calc e 4 = e 4 * zOf e * zOf e := by rw [mul_assoc, hz_mul, mul_one]
        _ = zOf e := by rw [h1, one_mul]
    exact orderOf_eq_prime hsq' hne
  have hEK : IsKleinFour ↥(Esub e) := by
    have hE : Esub e = CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions (e 4) (zOf e)
        ht_mul hz_mul hcomm :=
      closure_pair_eq_kleinFour ht_mul hz_mul hcomm
    rw [hE]
    exact CFSG.GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions (e 4) (zOf e)
      ht_mul hz_mul ht1 (by intro h1; rw [h1, orderOf_one] at hz2; norm_num at hz2) htz hcomm
  have hgt : ∃ g : G, g * zOf e * g⁻¹ = e 4 := isConj_iff.mp (hO (e 4) ht_ord)
  have hgtz : ∃ g : G, g * zOf e * g⁻¹ = e 4 * zOf e :=
    isConj_iff.mp (hO (e 4 * zOf e) htz_ord)
  have hPt : Psub e ⊓ Subgroup.centralizer {e 4} = ⊥ :=
    inf_centralizer_eq_bot_of_card hPH hP9 hF.card_cent_t
  have hdvd9 : ∀ u : G, (∃ g : G, g * zOf e * g⁻¹ = u) → ∀ S : Subgroup G,
      S ≤ Subgroup.centralizer {u} → Odd (Nat.card S) → Nat.card S ∣ 9 := by
    rintro u ⟨g, hg⟩ S hS hodd
    exact dvd_nine_of_odd_cent hCz (fun S' hS' ho => (hF.odd_sub S' hS' ho).1) hg hS hodd
  have hNY_P : ∀ n ∈ Subgroup.normalizer (Psub e : Set G), ∀ x ∈ Subgroup.centralizer (Psub e : Set G),
      n * x * n⁻¹ ∈ Subgroup.centralizer (Psub e : Set G) :=
    fun n hn x hx => conj_mem_centralizer_of_normalizer hn hx
  have hEN_P : Esub e ≤ Subgroup.normalizer (Psub e : Set G) := by
    have h1 : Esub e ≤ Subgroup.normalizer (Psub e : Set G) ⊓ H := by
      rw [hF.normP]; exact le_sup_right
    exact fun x hx => (h1 hx).1
  have hNnC_P : ∀ n ∈ Subgroup.normalizer (Psub e : Set G), n * zOf e = zOf e * n →
      n ∈ Psub e ⊔ Esub e := by
    intro n hn hc
    have h1 : n ∈ Subgroup.normalizer (Psub e : Set G) ⊓ H := by
      refine ⟨hn, ?_⟩
      rw [← hCz]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hc
    rw [hF.normP] at h1
    exact h1
  have hYX_P : ∀ x ∈ Subgroup.centralizer (Psub e : Set G), x * zOf e = zOf e * x →
      x ∈ Psub e ⊔ Subgroup.zpowers (zOf e) := by
    intro x hx hxz
    have hxH : x ∈ H := by
      rw [← hCz]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hxz
    rw [← hF.centP]
    exact ⟨hx, hxH⟩
  obtain ⟨Pb, -, hPbc, hPb3, hPbcard, hPbP, hPbKK, hPbconj, hPbN⟩ :=
    core_of_normalizer (Y := Subgroup.centralizer (Psub e : Set G))
      (Nn := Subgroup.normalizer (Psub e : Set G)) (E := Esub e) (P := Psub e)
      (z := zOf e) (t := e 4) hzC hz2 hY2_P hPC hYX_P hP3 hPz hNY_P
      centralizer_le_normalizer' hEN_P hNnC_P htE hzE ht1 htz hgt hgtz hdvd9 hPt hP9
  have hPbarCore : PbarCore e Pb :=
    { compl := hPbc
      three := hPb3
      P_le := hPbP
      inf_cent_z := hPbKK
      conj_t := hPbconj
      normalizer_eq := hPbN }
  have hmixed : ∀ y : G, y ∈ H → Subgroup.centralizer {y} ⊓ H = Psub e ⊔ Subgroup.zpowers (zOf e) →
      Subgroup.normalizer (Subgroup.zpowers y : Set G) ⊓ H = Psub e ⊔ Esub e →
      ∃ N : Subgroup G, MixedCore e y N := by
    intro y hyH hcentY hnormY
    have hzCy : zOf e ∈ Subgroup.centralizer {y} :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hcommH y hyH).symm
    have hPCy : Psub e ≤ Subgroup.centralizer {y} := fun p hp => by
      have h1 : p ∈ Psub e ⊔ Subgroup.zpowers (zOf e) := Subgroup.mem_sup_left hp
      rw [← hcentY] at h1
      exact h1.1
    have hYX_y : ∀ x ∈ Subgroup.centralizer {y}, x * zOf e = zOf e * x →
        x ∈ Psub e ⊔ Subgroup.zpowers (zOf e) := by
      intro x hx hxz
      have hxH : x ∈ H := by
        rw [← hCz]
        exact Subgroup.mem_centralizer_singleton_iff.mpr hxz
      rw [← hcentY]
      exact ⟨hx, hxH⟩
    have hYH_y : Subgroup.centralizer {y} ⊓ Subgroup.centralizer {zOf e} =
        Psub e ⊔ Subgroup.zpowers (zOf e) := by
      rw [hCz, hcentY]
    have hY2_y := hY2_of _ hzCy hYH_y
    have hNY_y : ∀ n ∈ Subgroup.normalizer (Subgroup.zpowers y : Set G),
        ∀ x ∈ Subgroup.centralizer {y}, n * x * n⁻¹ ∈ Subgroup.centralizer {y} :=
      fun n hn x hx => centralizer_singleton_of_zpowers
        (conj_mem_centralizer_of_normalizer hn (mem_centralizer_zpowers_of hx))
    have hYNn_y : Subgroup.centralizer {y} ≤ Subgroup.normalizer (Subgroup.zpowers y : Set G) :=
      fun x hx => centralizer_le_normalizer' (mem_centralizer_zpowers_of hx)
    have hEN_y : Esub e ≤ Subgroup.normalizer (Subgroup.zpowers y : Set G) := by
      have h1 : Esub e ≤ Subgroup.normalizer (Subgroup.zpowers y : Set G) ⊓ H := by
        rw [hnormY]; exact le_sup_right
      exact fun x hx => (h1 hx).1
    have hNnC_y : ∀ n ∈ Subgroup.normalizer (Subgroup.zpowers y : Set G),
        n * zOf e = zOf e * n → n ∈ Psub e ⊔ Esub e := by
      intro n hn hc
      have h1 : n ∈ Subgroup.normalizer (Subgroup.zpowers y : Set G) ⊓ H := by
        refine ⟨hn, ?_⟩
        rw [← hCz]
        exact Subgroup.mem_centralizer_singleton_iff.mpr hc
      rw [hnormY] at h1
      exact h1
    obtain ⟨N, -, hNc, hN3, hNcard, hNP, -, -, hNN⟩ :=
      core_of_normalizer (Y := Subgroup.centralizer {y})
        (Nn := Subgroup.normalizer (Subgroup.zpowers y : Set G)) (E := Esub e) (P := Psub e)
        (z := zOf e) (t := e 4) hzCy hz2 hY2_y hPCy hYX_y hP3 hPz hNY_y hYNn_y hEN_y hNnC_y
        htE hzE ht1 htz hgt hgtz hdvd9 hPt hP9
    refine ⟨N, ?_⟩
    exact { compl := hNc
            three := hN3
            P_le := hNP
            card_le := hNcard
            normalizer_eq := hNN
            sylow2 := hY2_y }
  obtain ⟨Np, hNp⟩ := hmixed (e 0 * e 2) (H.mul_mem he0H he2H) hF.centYp hF.normYp
  obtain ⟨Nm, hNm⟩ := hmixed (e 0 * (e 2)⁻¹) (H.mul_mem he0H (H.inv_mem he2H))
    hF.centYm hF.normYm
  exact ⟨Pb, Np, Nm, hPbarCore, hNp, hNm⟩


end CFSG.GH74.QTGen4.Recog.G23.P7
