module

public import CFSG.GH74.GLS.Stage1.Thm4.L96Act
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Hat

public section

namespace CFSG.GH74.GLS.Stage1.Thm4.L96

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm4
  CFSG.GH74.Uniqueness.SU.SU13.TA CFSG.GH74.GLS.IVK.Lifted
open scoped commutatorElement

section TwoCoverLemmas

variable {H : Type} [Group H] {n : ℕ} {π : H →* alternatingGroup (Fin n)}

theorem twoCover_sq_eq_one_of_mem_ker (hπ : TwoCover π) {k : H} (hk : k ∈ π.ker) : k ^ 2 = 1 := by
  obtain ⟨zz, -, -, hzz2, hzzk⟩ := hπ.exists_z
  rcases hzzk k hk with rfl | rfl
  · exact one_pow 2
  · exact hzz2

theorem twoCover_eq_of_odd_pow (hπ : TwoCover π) {u v : H} (huv : π u = π v) {m : ℕ}
    (hm : Odd m) (hu : u ^ m = 1) (hv : v ^ m = 1) : u = v := by
  obtain ⟨zz, hzc, hz1, hz2, hzk⟩ := hπ.exists_z
  have hk : u⁻¹ * v ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, huv, inv_mul_cancel]
  rcases hzk _ hk with h1 | h1
  · exact inv_mul_eq_one.1 h1
  · exfalso
    have hv' : v = u * zz := by rw [← h1]; group
    have hc : Commute u zz := Subgroup.mem_center_iff.1 hzc u
    have hzm : zz ^ m = zz := by
      obtain ⟨k, rfl⟩ := hm
      rw [pow_succ, pow_mul, hz2, one_pow, one_mul]
    rw [hv', hc.mul_pow, hu, one_mul, hzm] at hv
    exact hz1 hv

theorem twoCover_exists_pow_eq_one (hπ : TwoCover π) (γ : alternatingGroup (Fin n))
    (hγ : Odd (orderOf γ)) : ∃ u : H, π u = γ ∧ u ^ orderOf γ = 1 := by
  obtain ⟨g, rfl⟩ := hπ.surj γ
  have key : ∀ m : ℕ, Odd m → g ^ m ∈ π.ker → (g ^ (m + 1)) ^ m = 1 := by
    intro m hm hker
    have hsq := twoCover_sq_eq_one_of_mem_ker hπ hker
    obtain ⟨j, hj⟩ := hm
    have e : (g ^ (m + 1)) ^ m = (g ^ m) ^ (m + 1) := by rw [← pow_mul, ← pow_mul, mul_comm]
    rw [e, show m + 1 = 2 * (j + 1) by omega, pow_mul, hsq, one_pow]
  refine ⟨g ^ (orderOf (π g) + 1), ?_, key _ hγ ?_⟩
  · rw [map_pow, pow_succ, pow_orderOf_eq_one, one_mul]
  · rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]

end TwoCoverLemmas

variable {G : Type} [Group G] [Finite G] {Lh : Type} [Group Lh] {z t : G} {S K : Subgroup G}
  {h : Ctx98 G Lh z t S K} {n : ℕ}

theorem Act.coe_pi_phi (A : Act h n) {s : G} (hsC : s ∈ Cz z) (k : ↥K) :
    ((A.π (phi K s (h.mem_normalizer hsC) (QuotientGroup.mk k)) : alternatingGroup (Fin n)) :
        Equiv.Perm (Fin n)) =
      A.ρ ⟨s, hsC⟩ * ((A.π (QuotientGroup.mk k) : alternatingGroup (Fin n)) :
        Equiv.Perm (Fin n)) * (A.ρ ⟨s, hsC⟩)⁻¹ := by
  have hs := h.mem_normalizer hsC
  have e1 : phi K s hs (QuotientGroup.mk k) =
      QuotientGroup.mk ⟨s * (k : G) * s⁻¹, (mem_normalizer_iff.mp hs k).mp k.2⟩ := phi_mk K hs k
  rw [e1, ← A.ρ_K, ← A.ρ_K k]
  have e2 : (⟨s * (k : G) * s⁻¹, h.K_le ((mem_normalizer_iff.mp hs k).mp k.2)⟩ : ↥(Cz z)) =
      ⟨s, hsC⟩ * ⟨(k : G), h.K_le k.2⟩ * ⟨s, hsC⟩⁻¹ := rfl
  rw [e2, map_mul, map_mul, map_inv]

theorem Act.exists_lift_odd (A : Act h n) (γ : alternatingGroup (Fin n)) (hγ : Odd (orderOf γ))
    (hcomm : (γ : Equiv.Perm (Fin n)) * A.ρ ⟨t, h.std.t_cen⟩ =
      A.ρ ⟨t, h.std.t_cen⟩ * (γ : Equiv.Perm (Fin n))) :
    ∃ x : ↥K, (x : G) * t = t * (x : G) ∧ Odd (orderOf (x : G)) ∧
      A.π (QuotientGroup.mk x) = γ := by
  have htN : t ∈ normalizer (K : Set G) := h.mem_normalizer h.std.t_cen
  have ht2 : t ^ (2 : ℤ) = 1 := by
    have h1 := pow_orderOf_eq_one t
    rw [h.std.t_ord] at h1
    simpa using h1
  have hR : ∀ y ∈ zpowers t, y = 1 ∨ y = t := by
    intro y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rcases Int.emod_two_eq_zero_or_one j with h0 | h1
    · left
      rw [← Int.emod_add_mul_ediv j 2, h0, zero_add, zpow_mul, ht2, one_zpow]
    · right
      rw [← Int.emod_add_mul_ediv j 2, h1, zpow_add, zpow_mul, ht2, one_zpow, mul_one, zpow_one]
  obtain ⟨u, hu, hum⟩ := twoCover_exists_pow_eq_one A.cover γ hγ
  obtain ⟨k₀, rfl⟩ := QuotientGroup.mk_surjective u
  have hφu : phi K t htN (QuotientGroup.mk k₀) = QuotientGroup.mk k₀ := by
    refine twoCover_eq_of_odd_pow A.cover ?_ hγ ?_ hum
    · apply Subtype.ext
      rw [A.coe_pi_phi h.std.t_cen k₀, hu, ← hcomm, mul_assoc, mul_inv_cancel, mul_one]
    · rw [← map_pow, hum, map_one]
  have hφfix : ∀ w ∈ zpowers (QuotientGroup.mk k₀ : HatT K), phi K t htN w = w := by
    intro w hw
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    rw [map_zpow, hφu]
  obtain ⟨V, hV⟩ : ∃ V : Subgroup G,
      V = ((zpowers (QuotientGroup.mk k₀ : HatT K)).comap (hatMk K)).map K.subtype := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : Subgroup G, M = pPrimeCoreOf 2 K := ⟨_, rfl⟩
  have hVK : V ≤ K := hV ▸ Subgroup.map_subtype_le _
  have hVmem : ∀ g : G, g ∈ V ↔
      ∃ hg : g ∈ K, hatMk K ⟨g, hg⟩ ∈ zpowers (QuotientGroup.mk k₀ : HatT K) := by
    intro g
    rw [hV]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hg, hmem⟩
      exact ⟨⟨g, hg⟩, hmem, rfl⟩
  have hMK : ∀ g ∈ M, g ∈ K := fun g hg => TwoThin.pPrimeCoreOf_le K (hM ▸ hg)
  have hMV : M ≤ V := by
    intro g hg
    refine (hVmem g).2 ⟨hMK g hg, ?_⟩
    rw [(hatMk_eq_one_iff K ⟨g, hMK g hg⟩).2 (hM ▸ hg)]
    exact one_mem _
  have hKM : K ≤ normalizer (M : Set G) := fun g hg => hM ▸ TwoThin.mem_normalizer_pPrimeCoreOf
    (le_normalizer hg)
  have hMn : (M.subgroupOf V).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMV).2 (hVK.trans hKM)
  have hModd : Odd (Nat.card M) := hM ▸ TwoThin.card_pPrimeCoreOf_odd K
  have hRM : zpowers t ≤ normalizer (M : Set G) :=
    Subgroup.zpowers_le.2 (hM ▸ TwoThin.mem_normalizer_pPrimeCoreOf htN)
  have hRp : IsPGroup 2 (zpowers t) := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by rw [Nat.card_zpowers, h.std.t_ord, pow_one]⟩
  have hcommVM : ⁅V, zpowers t⁆ ≤ M := by
    rw [Subgroup.commutator_le]
    intro v hv y hy
    rcases hR y hy with h1 | h1
    · rw [h1, commutatorElement_one_right]
      exact one_mem _
    · rw [h1]
      obtain ⟨hvK, hvz⟩ := (hVmem v).1 hv
      have hvK' : t * v⁻¹ * t⁻¹ ∈ K := (mem_normalizer_iff.mp htN v⁻¹).mp (inv_mem hvK)
      have hcK : ⁅v, t⁆ ∈ K := by
        have e : ⁅v, t⁆ = v * (t * v⁻¹ * t⁻¹) := by simp [commutatorElement_def, mul_assoc]
        rw [e]
        exact mul_mem hvK hvK'
      rw [hM, ← hatMk_eq_one_iff K ⟨⁅v, t⁆, hcK⟩]
      have e : (⟨⁅v, t⁆, hcK⟩ : ↥K) = ⟨v, hvK⟩ * ⟨t * v⁻¹ * t⁻¹, hvK'⟩ :=
        Subtype.ext (by simp [commutatorElement_def, mul_assoc])
      have hw : phi K t htN (hatMk K ⟨v, hvK⟩) = hatMk K ⟨v, hvK⟩ := hφfix _ hvz
      have h3 : hatMk K ⟨t * v⁻¹ * t⁻¹, hvK'⟩ = (hatMk K ⟨v, hvK⟩)⁻¹ := by
        have h4 : phi K t htN (hatMk K ⟨v⁻¹, inv_mem hvK⟩) =
            hatMk K ⟨t * v⁻¹ * t⁻¹, hvK'⟩ := phi_mk K htN ⟨v⁻¹, inv_mem hvK⟩
        rw [← h4]
        have h5 : hatMk K ⟨v⁻¹, inv_mem hvK⟩ = (hatMk K ⟨v, hvK⟩)⁻¹ :=
          map_inv (hatMk K) ⟨v, hvK⟩
        rw [h5, map_inv, hw]
      rw [e, map_mul, h3, mul_inv_cancel]
  have hk₀V : (k₀ : G) ∈ V := (hVmem _).2 ⟨k₀.2, mem_zpowers _⟩
  obtain ⟨c, ⟨hcV, hcC⟩, m, hmM, hcm⟩ :=
    CFSG.ClassicalInvolution.LBalanceProof.exists_centralizer_mul_of_commutator_le V (zpowers t) M
      hRp hMV hMn hModd hRM hcommVM (k₀ : G) hk₀V
  have hcK : c ∈ K := hVK hcV
  have hct : c * t = t * c := (mem_centralizer_iff.1 hcC t (mem_zpowers t)).symm
  have hmk : (QuotientGroup.mk (⟨c, hcK⟩ : ↥K) : HatT K) = QuotientGroup.mk k₀ := by
    have hmK : m ∈ K := hMK m hmM
    have e : (⟨c, hcK⟩ : ↥K)⁻¹ * k₀ = ⟨m, hmK⟩ := Subtype.ext (by simp [hcm])
    have h1 : hatMk K ((⟨c, hcK⟩ : ↥K)⁻¹ * k₀) = 1 := by
      rw [e]
      exact (hatMk_eq_one_iff K ⟨m, hmK⟩).2 (hM ▸ hmM)
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1
  refine ⟨⟨c, hcK⟩, hct, ?_, by rw [hmk, hu]⟩
  have hpow : (⟨c, hcK⟩ : ↥K) ^ orderOf γ ∈ pPrimeCore 2 ↥K := by
    have h1 : (QuotientGroup.mk ((⟨c, hcK⟩ : ↥K) ^ orderOf γ) : HatT K) = 1 := by
      rw [QuotientGroup.mk_pow, hmk, hum]
    exact (QuotientGroup.eq_one_iff _).1 h1
  have hN : ((⟨c, hcK⟩ : ↥K) ^ orderOf γ) ^ Nat.card (pPrimeCore 2 ↥K) = 1 := by
    have h1 : (⟨_, hpow⟩ : ↥(pPrimeCore 2 ↥K)) ^ Nat.card (pPrimeCore 2 ↥K) = 1 :=
      pow_card_eq_one'
    exact congrArg Subtype.val h1
  have hdvd : orderOf (⟨c, hcK⟩ : ↥K) ∣ orderOf γ * Nat.card (pPrimeCore 2 ↥K) :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_mul]; exact hN)
  rw [Subgroup.orderOf_coe]
  exact (hγ.mul odd_card_pPrimeCore).of_dvd_nat hdvd

theorem Act.exists_lift_pElement (A : Act h n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (γ : alternatingGroup (Fin n)) (hγ : orderOf γ = p)
    (hcomm : (γ : Equiv.Perm (Fin n)) * A.ρ ⟨t, h.std.t_cen⟩ =
      A.ρ ⟨t, h.std.t_cen⟩ * (γ : Equiv.Perm (Fin n))) :
    ∃ x : ↥K, (x : G) * t = t * (x : G) ∧ (∃ a : ℕ, (x : G) ^ (p ^ a) = 1) ∧
      A.π (QuotientGroup.mk x) = γ := by
  have hodd : Odd (orderOf γ) := by
    rw [hγ]
    exact hp.odd_of_ne_two hp2
  obtain ⟨x, hxt, -, hxγ⟩ := A.exists_lift_odd γ hodd hcomm
  obtain ⟨a, m', hm', hom⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos (x : G)).ne' p hp.ne_one
  have hcop : Nat.Coprime m' p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hm').symm
  have he : m' ^ (p - 1) ≡ 1 [MOD p] := by
    have := Nat.ModEq.pow_totient hcop
    rwa [Nat.totient_prime hp] at this
  have hm'e : m' ∣ m' ^ (p - 1) := dvd_pow_self m' (by have := hp.two_le; omega)
  refine ⟨x ^ (m' ^ (p - 1)), ?_, ⟨a, ?_⟩, ?_⟩
  · rw [Subgroup.coe_pow]
    exact ((Commute.pow_left (show Commute (x : G) t from hxt) _)).eq
  · rw [Subgroup.coe_pow, ← pow_mul]
    refine orderOf_dvd_iff_pow_eq_one.1 ?_
    rw [hom, mul_comm (m' ^ (p - 1))]
    exact Nat.mul_dvd_mul_left _ hm'e
  · have he' : m' ^ (p - 1) % p = 1 := by
      have h1 : m' ^ (p - 1) % p = 1 % p := he
      rwa [Nat.mod_eq_of_lt hp.one_lt] at h1
    rw [QuotientGroup.mk_pow, map_pow, hxγ, ← pow_mod_orderOf, hγ, he', pow_one]

end CFSG.GH74.GLS.Stage1.Thm4.L96
