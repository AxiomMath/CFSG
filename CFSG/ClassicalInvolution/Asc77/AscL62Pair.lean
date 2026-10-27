module

public import CFSG.ClassicalInvolution.Asc77.AscL62Core
public import CFSG.ClassicalInvolution.Asc77.ModOApi

public section

namespace CFSG.ClassicalInvolution.Asc77.AscL62

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable {G : Type} [Group G]

private theorem isSylow2In_map_subtype' [Finite G] (K : Subgroup G) (P : Sylow 2 ↥K) :
    IsSylow2In ((P : Subgroup ↥K).map K.subtype) K := by
  refine ⟨Subgroup.map_subtype_le _, P.isPGroup'.map _, fun V' hV'K hV'2 hle => ?_⟩
  have hQV : (P : Subgroup ↥K) ≤ V'.subgroupOf K := fun x hx => hle ⟨x, hx, rfl⟩
  have hcomap : V'.subgroupOf K = (P : Subgroup ↥K) := P.is_maximal' hV'2.comap_subtype hQV
  rw [← Subgroup.map_subgroupOf_eq_of_le hV'K, hcomap]

@[expose] noncomputable def sylowOfIsSylow2In'' {V K : Subgroup G} (h : IsSylow2In V K) :
    Sylow 2 ↥K where
  toSubgroup := V.subgroupOf K
  isPGroup' := h.2.1.comap_subtype
  is_maximal' := by
    intro Q hQ hle
    have hVQ : V ≤ Q.map K.subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le h.1]
      exact Subgroup.map_mono hle
    have := h.2.2 (Q.map K.subtype) (Subgroup.map_subtype_le _) (hQ.map _) hVQ
    rw [← Subgroup.comap_map_eq_self_of_injective K.subtype_injective Q, this]
    rfl

private theorem natCard_isSylow2In'' [Finite G] (K : Subgroup G) :
    Nat.card {R : Subgroup G // IsSylow2In R K} = Nat.card (Sylow 2 ↥K) := by
  refine Nat.card_congr
    { toFun := fun R => sylowOfIsSylow2In'' R.2
      invFun := fun P => ⟨(P : Subgroup ↥K).map K.subtype, isSylow2In_map_subtype' K P⟩
      left_inv := fun R => ?_
      right_inv := fun P => ?_ }
  · exact Subtype.ext (Subgroup.map_subgroupOf_eq_of_le R.2.1)
  · apply Sylow.ext
    exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _

theorem exists_sylow_normalized [Finite G] {K W : Subgroup G} (hW : IsPGroup 2 W)
    (hWK : W ≤ Subgroup.normalizer (K : Set G)) :
    ∃ R : Subgroup G, IsSylow2In R K ∧ ∀ w ∈ W, conjSub w R = R := by
  have hinv : ∀ w ∈ W, ∀ R ∈ {R : Subgroup G | IsSylow2In R K}, conjSub w R ∈
      {R : Subgroup G | IsSylow2In R K} := by
    intro w hw R hR
    have := IsSylow2In.conj hR w
    rwa [mem_normalizer_iff_conjSub_eq.mp (hWK hw)] at this
  have hodd : ¬ 2 ∣ Nat.card ↥{R : Subgroup G | IsSylow2In R K} := by
    have h1 : Nat.card ↥{R : Subgroup G | IsSylow2In R K} = Nat.card (Sylow 2 ↥K) :=
      natCard_isSylow2In'' K
    rw [h1]
    exact not_dvd_card_sylow 2 ↥K
  obtain ⟨R, hR, hfix⟩ := exists_fixed_conjSub hW hinv hodd
  exact ⟨R, hR, hfix⟩

theorem mem_of_uniqueInvolution_of_pGroup [Finite G] {K A : Subgroup G} {z : G}
    (hz : IsUniqueInvolution K z) (hAK : A ≤ K) (hA : IsPGroup 2 A) (h2 : 2 ≤ Nat.card A) :
    z ∈ A := by
  have h2dvd : 2 ∣ Nat.card ↥A := by
    rcases hA.card_eq_or_dvd with h | h
    · omega
    · exact h
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
  have htG : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  have htsq : (t : G) * (t : G) = 1 := by
    have := pow_orderOf_eq_one (t : G)
    rwa [htG, pow_two] at this
  have htne : (t : G) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at htG
    omega
  rcases hz.unique (t : G) (hAK t.2) htsq with h | h
  · exact absurd h htne
  · exact h ▸ t.2

theorem isUniqueInvolution_of_le {K A : Subgroup G} {z : G} (hz : IsUniqueInvolution K z)
    (hAK : A ≤ K) (hzA : z ∈ A) : IsUniqueInvolution A z where
  mem := hzA
  ne_one := hz.ne_one
  sq := hz.sq
  unique := fun y hy hy2 => hz.unique y (hAK hy) hy2

theorem exists_involution_pow {g : G} (hg1 : g ≠ 1) {i : ℕ} (hi : orderOf g = 2 ^ i) :
    ∃ y ∈ Subgroup.zpowers g, y * y = 1 ∧ y ≠ 1 := by
  have hi0 : i ≠ 0 := by
    intro h0
    rw [h0] at hi
    exact hg1 (orderOf_eq_one_iff.mp (by simpa using hi))
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  refine ⟨g ^ 2 ^ k, Subgroup.pow_mem _ (Subgroup.mem_zpowers g) _, ?_, ?_⟩
  · rw [← pow_add, ← two_mul, ← pow_succ']
    have := pow_orderOf_eq_one g
    rwa [hi] at this
  · intro h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hi] at this
    have := Nat.le_of_dvd (by positivity) this
    have h2 : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega

structure Pair (Ω : Set (Subgroup G)) (K J : Subgroup G) (z t : G) : Prop where
  hK : K ∈ Ω
  hJ : J ∈ Ω
  hz : IsUniqueInvolution K z
  ht : IsUniqueInvolution J t
  hne : z ≠ t

variable {Ω : Set (Subgroup G)} {K J : Subgroup G} {z t : G}

theorem Pair.symm (h : Pair Ω K J z t) : Pair Ω J K t z :=
  ⟨h.hJ, h.hK, h.ht, h.hz, h.hne.symm⟩

theorem Pair.ne (h : Pair Ω K J z t) : K ≠ J := by
  rintro rfl
  exact h.hne (h.hz.eq h.ht)

theorem Pair.eq_one_of_mem_of_mem (h : Pair Ω K J z t) {g : G} (hgK : g ∈ K) (hgJ : g ∈ J)
    (hg : ∃ i : ℕ, orderOf g = 2 ^ i) : g = 1 := by
  by_contra hg1
  obtain ⟨i, hi⟩ := hg
  obtain ⟨y, hy, hy2, hy1⟩ := exists_involution_pow hg1 hi
  have hyK : y ∈ K := (Subgroup.zpowers_le.mpr hgK) hy
  have hyJ : y ∈ J := (Subgroup.zpowers_le.mpr hgJ) hy
  rcases h.hz.unique y hyK hy2 with h1 | h1
  · exact hy1 h1
  rcases h.ht.unique y hyJ hy2 with h2 | h2
  · exact hy1 h2
  exact h.hne (h1 ▸ h2)

variable {p f : ℕ} [Fact p.Prime]

theorem orderOf_eq_two_pow_of_isPGroup {A : Subgroup G} (hA : IsPGroup 2 ↥A) {g : G} (hg : g ∈ A) :
    ∃ i : ℕ, orderOf g = 2 ^ i := by
  have := (IsPGroup.iff_orderOf (p := 2) (G := ↥A)).mp hA ⟨g, hg⟩
  simpa [Subgroup.orderOf_mk] using this

theorem Pair.coreCfg [Finite G] (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) (h : Pair Ω K J z t)
    {R V : Subgroup G} (hR : IsSylow2In R K) (hV2 : IsPGroup 2 ↥V) (hVJ : V ≤ J) (htV : t ∈ V)
    (hVR : ∀ y ∈ V, conjSub y R = R) : CoreCfg R V z t := by
  have hquat : IsQuatSub R := hΩ.isQuatSub_of_mem_RSet hp (mem_RSet_of_isSylow2In h.hK hR)
  have hzR : z ∈ R :=
    mem_of_uniqueInvolution_of_pGroup h.hz hR.1 hR.2.1 (by have := hquat.eight_le; omega)
  exact ⟨hquat, isUniqueInvolution_of_le h.hz hR.1 hzR, hV2, hVR,
    fun g hgV hgR => h.eq_one_of_mem_of_mem (hR.1 hgR) (hVJ hgV)
      (orderOf_eq_two_pow_of_isPGroup hV2 hgV), isUniqueInvolution_of_le h.ht hVJ htV⟩

theorem Pair.comm_of_normalizes (h : Pair Ω K J z t) {R V : Subgroup G} (hRK : R ≤ K)
    (hR2 : IsPGroup 2 ↥R) (hVJ : V ≤ J) (hVR : ∀ y ∈ V, conjSub y R = R) {u v : G} (hu : u ∈ R)
    (huJ : u ∈ Subgroup.normalizer (J : Set G)) (hv : v ∈ V) : u * v = v * u := by
  have hgJ : u * v * u⁻¹ * v⁻¹ ∈ J := by
    have h1 : u * v * u⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp huJ v).mp (hVJ hv)
    exact J.mul_mem h1 (J.inv_mem (hVJ hv))
  have hgR : u * v * u⁻¹ * v⁻¹ ∈ R := by
    have h1 : v * u⁻¹ * v⁻¹ ∈ conjSub v R := conj_mem_conjSub (R.inv_mem hu)
    rw [hVR v hv] at h1
    have : u * v * u⁻¹ * v⁻¹ = u * (v * u⁻¹ * v⁻¹) := by group
    rw [this]
    exact R.mul_mem hu h1
  have h1 := h.eq_one_of_mem_of_mem (hRK hgR) hgJ (orderOf_eq_two_pow_of_isPGroup hR2 hgR)
  have h2 : u * v * u⁻¹ = v := by
    have := congrArg (fun w => w * v) h1
    simpa [mul_assoc] using this
  calc u * v = (u * v * u⁻¹) * u := by group
    _ = v * u := by rw [h2]

theorem Pair.bootstrap [Finite G] (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (h : Pair Ω K J z t) {W : Subgroup G} (hWK : W ≤ K) (hW2 : IsPGroup 2 ↥W) (hzW : z ∈ W)
    (hWc : W ≤ Subgroup.centralizer ({t} : Set G)) (hW4 : 4 ≤ Nat.card W) :
    W ≤ Subgroup.normalizer (J : Set G) ∧
      ∃ R : Subgroup G, IsSylow2In R J ∧ CoreCfg R W t z ∧
        4 ≤ Nat.card ↥(R ⊓ Subgroup.centralizer ({z} : Set G)) ∧
        R ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (K : Set G) ∧
        (∀ u ∈ R ⊓ Subgroup.centralizer ({z} : Set G), ∀ w ∈ W, u * w = w * u) ∧
        CoreDich R W z := by
  have hWJ : W ≤ Subgroup.normalizer (J : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hp hq h.hJ h.hK h.ne.symm h.ht hWK hW2 (by omega) hWc
  refine ⟨hWJ, ?_⟩
  obtain ⟨R, hR, hRinv⟩ := exists_sylow_normalized hW2 hWJ
  have hcfg : CoreCfg R W t z := h.symm.coreCfg hp hΩ hR hW2 hWK hzW hRinv
  have hWne : W ≠ Subgroup.zpowers z := by
    intro hW
    have : Nat.card W = 2 := by
      rw [hW, Nat.card_zpowers]
      exact orderOf_eq_prime (by rw [pow_two]; exact h.hz.sq) h.hz.ne_one
    omega
  have hU4 := hcfg.four_le_natCard_cent hWne
  have hUJ : R ⊓ Subgroup.centralizer ({z} : Set G) ≤ J := inf_le_left.trans hR.1
  have hU2 : IsPGroup 2 ↥(R ⊓ Subgroup.centralizer ({z} : Set G)) := hR.2.1.to_inf_left
  have hUN : R ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hp hq h.hK h.hJ h.ne h.hz hUJ hU2 (by omega) inf_le_right
  have hcomm : ∀ u ∈ R ⊓ Subgroup.centralizer ({z} : Set G), ∀ w ∈ W, u * w = w * u := by
    intro u hu w hw
    exact h.symm.comm_of_normalizes hR.1 hR.2.1 hWK hRinv hu.1 (hUN hu) hw
  exact ⟨R, hR, hcfg, hU4, hUN, hcomm, hcfg.core_dichotomy hWne hcomm⟩

theorem natCard_eq_pow_of_isSylow2In [Finite G] {V P : Subgroup G} (h : IsSylow2In V P) :
    Nat.card V = 2 ^ (Nat.card P).factorization 2 := by
  have e1 := Sylow.card_eq_multiplicity (sylowOfIsSylow2In'' h)
  have c1 : Nat.card ↥(V.subgroupOf P) = Nat.card V :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.1).toEquiv
  have e1' : Nat.card ↥(V.subgroupOf P) = 2 ^ (Nat.card P).factorization 2 := e1
  rw [← c1, e1']

theorem Pair.natCard_sylow_eq [Finite G] (hΩ : HypOmegaMod p f Ω) (h : Pair Ω K J z t)
    {R R' : Subgroup G} (hR : IsSylow2In R K) (hR' : IsSylow2In R' J) :
    Nat.card R = Nat.card R' := by
  rw [hΩ.natCard_isSylow2In h.hK hR, hΩ.natCard_isSylow2In h.hJ hR']

theorem Pair.eq_zpowers_of_not_le_normalizer [Finite G] (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) (h : Pair Ω K J z t) {V : Subgroup G} (hV2 : IsPGroup 2 ↥V)
    (hVJ : V ≤ J) (hVc : V ≤ Subgroup.centralizer ({z} : Set G)) (htV : t ∈ V)
    (hVN : ¬ V ≤ Subgroup.normalizer (K : Set G)) :
    V = Subgroup.zpowers t ∧ conjSub t K ≠ K := by
  have hV2' : Nat.card V ≤ 2 := by
    by_contra hgt
    push Not at hgt
    exact hVN (hΩ.le_normalizer_of_le_centralizer hp hq h.hK h.hJ h.ne h.hz hVJ hV2 (by omega) hVc)
  have hzp : Nat.card (Subgroup.zpowers t) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact h.ht.sq) h.ht.ne_one
  have hle : Subgroup.zpowers t ≤ V := Subgroup.zpowers_le.mpr htV
  have hVeq : V = Subgroup.zpowers t :=
    (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm
  refine ⟨hVeq, fun hcon => hVN ?_⟩
  rw [hVeq, Subgroup.zpowers_le]
  exact mem_normalizer_iff_conjSub_eq.mpr hcon

@[expose] def CentSylow (Ω : Set (Subgroup G)) : Prop :=
  ∀ {K R V : Subgroup G}, K ∈ Ω → IsSylow2In R K → IsPGroup 2 ↥V → (∀ y ∈ V, conjSub y K = K) →
    (∀ r ∈ R, ∀ v ∈ V, r * v = v * r) → ∀ k ∈ K, ∀ v ∈ V, ⁅v, k⁆ ∈ oddCoreOf K

end CFSG.ClassicalInvolution.Asc77.AscL62
