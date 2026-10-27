module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S9InspKit
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspL33Core
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.TabBigM11
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15FactsSL3

public section

namespace CFSG.QuasithinUnique.A5.Insp

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3

@[expose] def NoTwoCent (X : Type) [Group X] : Prop :=
  ∀ k : X, k * k = 1 → k ≠ 1 → ¬ IsPGroup 2 ↥(Subgroup.centralizer ({k} : Set X))

theorem NoTwoCent.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : NoTwoCent Y) :
    NoTwoCent X := by
  intro k hk2 hk1 hp
  apply h (e k) (by rw [← map_mul, hk2, map_one])
    (fun h' => hk1 (e.injective (by rw [h', map_one])))
  intro y
  have hy : e.symm (y : Y) ∈ Subgroup.centralizer ({k} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.mp y.2
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact this
  obtain ⟨n, hn⟩ := hp ⟨e.symm (y : Y), hy⟩
  refine ⟨n, Subtype.ext ?_⟩
  have h1 : (e.symm (y : Y)) ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
  have h2 : (y : Y) ^ (2 ^ n) = 1 := by
    have := congrArg e (show (e.symm (y : Y)) ^ (2 ^ n) = 1 from h1)
    simpa [map_pow] using this
  simpa using h2

theorem false_of_noTwoCent {G : Type} [Group G] {K : Subgroup G} {X : Type} [Group X]
    (e : ↥K ≃* X) (hX : NoTwoCent X) {T : Subgroup G} (hT : IsPGroup 2 ↥T) {k : G} (hkK : k ∈ K)
    (hk2 : k * k = 1) (hk1 : k ≠ 1) (hcent : ∀ g ∈ K, g * k = k * g → g ∈ T) : False := by
  have hkK2 : (⟨k, hkK⟩ : ↥K) * ⟨k, hkK⟩ = 1 := Subtype.ext hk2
  have hkK1 : (⟨k, hkK⟩ : ↥K) ≠ 1 := fun h => hk1 (congrArg Subtype.val h)
  apply hX (e ⟨k, hkK⟩) (by rw [← map_mul, hkK2, map_one])
    (fun h => hkK1 (e.injective (by rw [h, map_one])))
  intro y
  have hyc : (y : X) * e ⟨k, hkK⟩ = e ⟨k, hkK⟩ * (y : X) :=
    Subgroup.mem_centralizer_singleton_iff.mp y.2
  have hg : e.symm (y : X) * ⟨k, hkK⟩ = ⟨k, hkK⟩ * e.symm (y : X) := by
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hyc
  have hgT : ((e.symm (y : X) : ↥K) : G) ∈ T :=
    hcent _ (e.symm (y : X)).2 (congrArg Subtype.val hg)
  obtain ⟨n, hn⟩ := hT ⟨((e.symm (y : X) : ↥K) : G), hgT⟩
  refine ⟨n, Subtype.ext ?_⟩
  have h1 : ((e.symm (y : X) : ↥K) : G) ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
  have h2 : (e.symm (y : X)) ^ (2 ^ n) = 1 := Subtype.ext (by simpa using h1)
  have h3 : (y : X) ^ (2 ^ n) = 1 := by
    have := congrArg e h2
    simpa [map_pow] using this
  simpa using h3

theorem isPGroup_centralizer_of_conj {X : Type} [Group X] {g k₀ k : X} (hk : g * k₀ * g⁻¹ = k)
    (h : IsPGroup 2 ↥(Subgroup.centralizer ({k} : Set X))) :
    IsPGroup 2 ↥(Subgroup.centralizer ({k₀} : Set X)) := by
  intro y
  have hy : g * (y : X) * g⁻¹ ∈ Subgroup.centralizer ({k} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyc : (y : X) * k₀ = k₀ * y := Subgroup.mem_centralizer_singleton_iff.mp y.2
    rw [← hk]
    calc g * y * g⁻¹ * (g * k₀ * g⁻¹) = g * (y * k₀) * g⁻¹ := by group
      _ = g * (k₀ * y) * g⁻¹ := by rw [hyc]
      _ = g * k₀ * g⁻¹ * (g * y * g⁻¹) := by group
  obtain ⟨m, hm⟩ := h ⟨g * (y : X) * g⁻¹, hy⟩
  refine ⟨m, Subtype.ext ?_⟩
  have hm' : (g * (y : X) * g⁻¹) ^ (2 ^ m) = 1 := by simpa using congrArg Subtype.val hm
  rw [conj_pow] at hm'
  have : (y : X) ^ (2 ^ m) = 1 := by
    calc (y : X) ^ (2 ^ m) = g⁻¹ * (g * (y : X) ^ (2 ^ m) * g⁻¹) * g := by group
      _ = 1 := by rw [hm']; group
  simpa using this

theorem noTwoCent_alt {n : ℕ} (hn : 7 ≤ n) : NoTwoCent (alternatingGroup (Fin n)) := by
  intro k hk2 hk1 hp
  obtain ⟨g, hg1, hg3, hgk⟩ := alt_exists_three_cent hn k hk2 hk1
  have hgC : g ∈ Subgroup.centralizer ({k} : Set (alternatingGroup (Fin n))) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hgk
  obtain ⟨m, hm⟩ := hp ⟨g, hgC⟩
  have hm' : g ^ (2 ^ m) = 1 := by simpa using congrArg Subtype.val hm
  have h1 : orderOf g ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm'
  have h2 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hg3
  exact hg1 (orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left m (by norm_num)) h1 h2))

section L33

open CFSG.QuasithinUnique.Vol2Native.L239.L33Insp

theorem not_isPGroup_Cs : ¬ IsPGroup 2 Cs := by
  intro h2
  have hd := card_dvd_sixteen h2
  have hle := Subgroup.card_le_of_le T16_le_Cs
  rw [card_T16] at hle
  have hEq : Nat.card Cs = 16 := Nat.le_antisymm (Nat.le_of_dvd (by norm_num) hd) hle
  have hT : T16 = Cs := Subgroup.eq_of_le_of_card_ge T16_le_Cs (by rw [card_T16, hEq])
  obtain ⟨x, hx, hxn⟩ : ∃ x ∈ c48p, x ∉ t16p := by decide +kernel
  obtain ⟨h1, h2', hmem⟩ := c48_mem hx
  have : ofN x h2' ∈ T16 := hT ▸ hmem
  rw [mem_T16, rn_ofN x h1 h2'] at this
  exact hxn this

theorem Cs_eq : Cs = Subgroup.centralizer ({u0} : Set S3) := by
  ext x
  rw [mem_Cs, Subgroup.mem_centralizer_singleton_iff, ← rn_inj.eq_iff, rn_mul, rn_mul, rn_u0]

theorem not_isPGroup_cent_u0 : ¬ IsPGroup 2 ↥(Subgroup.centralizer ({u0} : Set S3)) := by
  rw [← Cs_eq]
  exact not_isPGroup_Cs

theorem noTwoCent_S3 : NoTwoCent S3 := by
  intro k hk2 hk1 hp
  obtain ⟨g, hg⟩ := exists_conj_u0 hk2 hk1
  exact not_isPGroup_cent_u0 (isPGroup_centralizer_of_conj hg hp)

theorem noTwoCent_of_psl33 {X : Type} [Group X] (h : StatedClassicalModel X .PSL 3 3 1) :
    NoTwoCent X := by
  obtain ⟨e₀⟩ := CFSG.QuasithinUnique.Unc25K1.psl33_equiv h
  exact NoTwoCent.of_mulEquiv (e₀.trans CFSG.QuasithinUnique.Unc25K1.psl33EquivS3) noTwoCent_S3

end L33

section M11

open CFSG.QuasithinUnique.Unc25G2

theorem noTwoCent_M11
    : NoTwoCent ↥CFSG.Blueprint.NativeSporadic.M11 := by
  intro k hk2 hk1 hp
  obtain ⟨g, hg⟩ := CFSG.QuasithinUnique.Vol2Native.L239.M11Insp.exists_conj hk2 hk1
  have hp0 := isPGroup_centralizer_of_conj hg hp
  obtain ⟨n, hn⟩ := hp0.exists_card_eq
  rw [TabBigM11.card_centralizer_gA] at hn
  have h3 : 3 ∣ 2 ^ n := by rw [← hn]; norm_num
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

theorem noTwoCent_of_m11 {X : Type} [Group X]
    (h : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11)) : NoTwoCent X := by
  obtain ⟨e⟩ := h
  exact NoTwoCent.of_mulEquiv e noTwoCent_M11

end M11

end CFSG.QuasithinUnique.A5.Insp
