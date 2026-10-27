module

public import CFSG.ClassicalInvolution.Asc77.AscT3CIIX

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

section Bur

variable {G : Type} [Group G] [Finite G]

theorem le_oddCoreOf_sup_zpowers {E : Subgroup G} {z : G} (hzE : z ∈ E) (hz2 : z * z = 1)
    (hz1 : z ≠ 1)
    (h2 : ∀ x ∈ E, IsPGroup 2 (Subgroup.zpowers x) → x ∈ Subgroup.zpowers z) :
    E ≤ oddCoreOf E ⊔ Subgroup.zpowers z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥E) := inferInstance
  set zE : ↥E := ⟨z, hzE⟩ with hzE_def
  have hzord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have hzEord : orderOf zE = 2 := by rw [hzE_def, Subgroup.orderOf_mk]; exact hzord
  have hdvd : 2 ∣ Nat.card ↥E := by
    have := orderOf_dvd_natCard zE
    rwa [hzEord] at this
  have hPle : (P : Subgroup ↥E) ≤ Subgroup.zpowers zE := by
    intro x hx
    obtain ⟨k, hk⟩ := (P.isPGroup'.to_le (Subgroup.zpowers_le.mpr hx) :
      IsPGroup 2 (Subgroup.zpowers x)).exists_card_eq
    have hxord : orderOf x = 2 ^ k := by rwa [Nat.card_zpowers] at hk
    have hGord : orderOf (x : G) = 2 ^ k := by rw [Subgroup.orderOf_coe, hxord]
    have hxG : IsPGroup 2 (Subgroup.zpowers (x : G)) :=
      IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hGord])
    have := h2 x x.2 hxG
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp this
    exact Subgroup.mem_zpowers_iff.mpr ⟨m, Subtype.ext (by simpa using hm)⟩
  have hcardP : Nat.card (P : Subgroup ↥E) = 2 := by
    have h1 : Nat.card (P : Subgroup ↥E) ≤ Nat.card (Subgroup.zpowers zE) :=
      Subgroup.card_le_of_le hPle
    rw [Nat.card_zpowers, hzEord] at h1
    have h3 : 2 ≤ Nat.card (P : Subgroup ↥E) := by
      rw [P.card_eq_multiplicity]
      have : 1 ≤ (Nat.card ↥E).factorization 2 :=
        (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two Nat.card_pos.ne').mp hdvd
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (Nat.card ↥E).factorization 2 := Nat.pow_le_pow_right (by norm_num) this
    omega
  have hcyc : IsCyclic ↥(P : Subgroup ↥E) := isCyclic_of_prime_card (p := 2) hcardP
  have hmin : (Nat.card ↥E).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr hdvd
  have hcomp := IsCyclic.isComplement' hmin hcyc
  set Kr : Subgroup ↥E := (MonoidHom.transferSylow P (hcyc.normalizer_le_centralizer hmin)).ker
    with hKr
  have hKrodd : ¬ 2 ∣ Nat.card ↥Kr :=
    MonoidHom.not_dvd_card_ker_transferSylow P (hcyc.normalizer_le_centralizer hmin)
  set K₀ : Subgroup G := Kr.map E.subtype with hK₀
  have hK₀E : K₀ ≤ E := Subgroup.map_subtype_le _
  have hK₀odd : Odd (Nat.card ↥K₀) := by
    have hc : Nat.card ↥K₀ = Nat.card ↥Kr :=
      Subgroup.card_map_of_injective E.subtype_injective
    rw [hc]
    exact Nat.odd_iff.mpr (by omega)
  have hK₀norm : E ≤ Subgroup.normalizer (K₀ : Set G) := by
    intro e he
    refine mem_normalizer_of_conjSub_le ?_
    rintro _ ⟨y, ⟨y', hy', rfl⟩, rfl⟩
    refine ⟨⟨e, he⟩ * y' * ⟨e, he⟩⁻¹, ?_, rfl⟩
    exact (inferInstance : Kr.Normal).conj_mem y' hy' ⟨e, he⟩
  have hK₀le : K₀ ≤ oddCoreOf E := Balance.le_oddCoreIn_of_normalizes hK₀E hK₀norm hK₀odd
  intro e he
  obtain ⟨⟨⟨h, hh⟩, ⟨p, hp⟩⟩, hhp⟩ := hcomp.2 ⟨e, he⟩
  have hhK₀ : (h : G) ∈ K₀ := ⟨h, hh, rfl⟩
  have hpz : (p : G) ∈ Subgroup.zpowers z := by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hPle hp)
    exact Subgroup.mem_zpowers_iff.mpr ⟨m, by simpa using congrArg Subtype.val hm⟩
  have he' : e = (h : G) * (p : G) := by
    have := congrArg Subtype.val hhp
    simpa using this.symm
  rw [he']
  exact Subgroup.mul_mem_sup (hK₀le hhK₀) hpz

@[expose] def OutComm (K : Subgroup G) : Prop :=
  ∀ x ∈ Subgroup.normalizer (K : Set G), ∀ y ∈ Subgroup.normalizer (K : Set G),
    ∃ k ∈ K, ∀ g ∈ K, ⁅x, y⁆ * g * ⁅x, y⁆⁻¹ = k * g * k⁻¹

omit [Finite G] in
theorem commutator_decomp {K K' : Subgroup G} (hcomm : ∀ k ∈ K, ∀ k' ∈ K', k * k' = k' * k)
    (hK : OutComm K) (hK' : OutComm K') {x y : G}
    (hxK : x ∈ Subgroup.normalizer (K : Set G)) (hxK' : x ∈ Subgroup.normalizer (K' : Set G))
    (hyK : y ∈ Subgroup.normalizer (K : Set G)) (hyK' : y ∈ Subgroup.normalizer (K' : Set G)) :
    ∃ k ∈ K, ∃ k' ∈ K', ∀ m ∈ K ⊔ K',
      ((k * k')⁻¹ * ⁅x, y⁆) * m = m * ((k * k')⁻¹ * ⁅x, y⁆) := by
  obtain ⟨k, hk, hkg⟩ := hK x hxK y hyK
  obtain ⟨k', hk', hk'g⟩ := hK' x hxK' y hyK'
  refine ⟨k, hk, k', hk', ?_⟩
  generalize ⁅x, y⁆ = w at hkg hk'g ⊢
  have hA : ∀ g ∈ K, k'⁻¹ * g * k' = g := fun g hg => by
    have := hcomm g hg k' hk'
    calc k'⁻¹ * g * k' = k'⁻¹ * (g * k') := by group
      _ = k'⁻¹ * (k' * g) := by rw [this]
      _ = g := by group
  have hB : ∀ g ∈ K', k⁻¹ * g * k = g := fun g hg => by
    have := hcomm k hk g hg
    calc k⁻¹ * g * k = k⁻¹ * (g * k) := by group
      _ = k⁻¹ * (k * g) := by rw [← this]
      _ = g := by group
  have hKc : K ≤ Subgroup.centralizer ({(k * k')⁻¹ * w} : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h : (k * k')⁻¹ * w * g * ((k * k')⁻¹ * w)⁻¹ = g := by
      calc (k * k')⁻¹ * w * g * ((k * k')⁻¹ * w)⁻¹
          = (k * k')⁻¹ * (w * g * w⁻¹) * (k * k') := by group
        _ = (k * k')⁻¹ * (k * g * k⁻¹) * (k * k') := by rw [hkg g hg]
        _ = k'⁻¹ * (k⁻¹ * (k * g * k⁻¹) * k) * k' := by group
        _ = k'⁻¹ * g * k' := by group
        _ = g := hA g hg
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  have hK'c : K' ≤ Subgroup.centralizer ({(k * k')⁻¹ * w} : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h : (k * k')⁻¹ * w * g * ((k * k')⁻¹ * w)⁻¹ = g := by
      calc (k * k')⁻¹ * w * g * ((k * k')⁻¹ * w)⁻¹
          = (k * k')⁻¹ * (w * g * w⁻¹) * (k * k') := by group
        _ = (k * k')⁻¹ * (k' * g * k'⁻¹) * (k * k') := by rw [hk'g g hg]
        _ = k'⁻¹ * (k⁻¹ * (k' * g * k'⁻¹) * k) * k' := by group
        _ = k'⁻¹ * (k' * g * k'⁻¹) * k' := by
            rw [hB (k' * g * k'⁻¹) (K'.mul_mem (K'.mul_mem hk' hg) (K'.inv_mem hk'))]
        _ = g := by group
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  intro m hm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (sup_le hKc hK'c hm)).symm

end Bur

end CFSG.ClassicalInvolution.Asc77.T3CII
