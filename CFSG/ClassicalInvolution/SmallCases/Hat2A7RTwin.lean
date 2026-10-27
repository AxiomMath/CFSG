module

public import CFSG.ClassicalInvolution.Omega
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Tight

public section

namespace CFSG.ClassicalInvolution.Hat2A7R

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Hat2A7
open scoped commutatorElement

section OddCore

variable {F : Type*} [Group F] [Finite F]

theorem eq_one_of_isPGroup_of_mem_oddCore {K P : Subgroup F} (hP2 : IsPGroup 2 P) {x : F}
    (hx : x ∈ P) (hxN : x ∈ (classicalInvolutionOddCore ↥K).map K.subtype) : x = 1 := by
  obtain ⟨x', hx'N, hxeq⟩ := hxN
  have hx' : (x' : F) ∈ P := by rw [← hxeq] at hx; exact hx
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥K)) := odd_card_oddCore K
  have h1 : orderOf x' ∣ Nat.card (classicalInvolutionOddCore ↥K) :=
    Subgroup.orderOf_dvd_natCard _ hx'N
  have hxo : orderOf (x' : F) = orderOf x' := Subgroup.orderOf_coe x'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hP2.exists_orderOf_eq_pow (⟨(x' : F), hx'⟩ : P)
  rw [Subgroup.orderOf_mk] at hk
  by_cases hk0 : k = 0
  · rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
    rw [← hxeq]
    exact hk
  · exfalso
    have h4 : 2 ∣ orderOf x' := by rw [← hxo, hk]; exact dvd_pow_self 2 hk0
    exact absurd (hodd.of_dvd_nat (h4.trans h1)) (by decide)

end OddCore

section Twins

variable {F : Type*} [Group F] [Finite F] {K K' : Subgroup F} {z : F}

theorem twins_of_classical2A7 (hK : IsClassical2A7 ⊤ K z) (hK' : K' ∈ omegaAt K z z)
    (hne : K' ≠ K) :
    K' ≤ Subgroup.normalizer (K : Set F) ∧ K ≤ Subgroup.normalizer (K' : Set F) ∧
      ⁅K, K'⁆ ≤ (classicalInvolutionOddCore ↥K).map K.subtype ⊓
        (classicalInvolutionOddCore ↥K').map K'.subtype ∧
      ⁅K, K'⁆ ≤ (classicalInvolutionOddCore ↥(Subgroup.centralizer ({z} : Set F))).map
        (Subgroup.centralizer ({z} : Set F)).subtype := by
  have hsub : IsSubnormal K (Subgroup.centralizer ({z} : Set F)) := by
    have h1 := hK.subnormal
    rwa [top_inf_eq] at h1
  exact twins_self_of_perfect hsub hK.perfect.commutator_eq_top hK.witness.1 hK' hne

theorem card_le_two_of_twins (hK : IsClassical2A7 ⊤ K z) (hK' : K' ∈ omegaAt K z z)
    (hne : K' ≠ K) {P : Subgroup F} (hPK : P ≤ K) (hPK' : P ≤ K') (hP2 : IsPGroup 2 P) :
    Nat.card P ≤ 2 := by
  obtain ⟨-, -, hcomm, -⟩ := twins_of_classical2A7 hK hK' hne
  set N : Subgroup ↥K := classicalInvolutionOddCore ↥K with hN
  have hcen : ∀ p : ↥(P.subgroupOf K), ((p : ↥K) : OddQuot K) ∈ Subgroup.center (OddQuot K) := by
    intro p
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    have hpP : ((p : ↥K) : F) ∈ P := p.2
    have h1 : ⁅(k : F), ((p : ↥K) : F)⁆ ∈ ⁅K, K'⁆ :=
      Subgroup.commutator_mem_commutator k.2 (hPK' hpP)
    have h2 := (hcomm h1).1
    obtain ⟨c, hcN, hc⟩ := h2
    have hck : c = ⁅k, (p : ↥K)⁆ := Subtype.ext (by
      have hc' : (c : F) = ⁅(k : F), ((p : ↥K) : F)⁆ := hc
      rw [hc']
      simp [commutatorElement_def])
    rw [hck] at hcN
    have h3 : (⁅k, (p : ↥K)⁆ : ↥K) ∈ N := hcN
    have h4 : ((⁅k, (p : ↥K)⁆ : ↥K) : OddQuot K) = 1 := (QuotientGroup.eq_one_iff _).mpr h3
    rw [commutatorElement_def] at h4
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h4
    have h5 := mul_inv_eq_one.mp h4
    calc ((k : ↥K) : OddQuot K) * ((p : ↥K) : OddQuot K)
        = (k : OddQuot K) * (p : OddQuot K) * (k : OddQuot K)⁻¹ * (k : OddQuot K) := by group
      _ = (p : OddQuot K) * (k : OddQuot K) := by rw [h5]
  let f : ↥(P.subgroupOf K) →* OddQuot K :=
    (QuotientGroup.mk' N).comp (P.subgroupOf K).subtype
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro p hp
    have hpN : ((p : ↥K) : ↥K) ∈ N := (QuotientGroup.eq_one_iff _).mp hp
    have hpP : ((p : ↥K) : F) ∈ P := p.2
    have : ((p : ↥K) : F) = 1 :=
      eq_one_of_isPGroup_of_mem_oddCore hP2 hpP ⟨(p : ↥K), hpN, rfl⟩
    exact Subtype.ext (Subtype.ext this)
  have hrange : f.range ≤ Subgroup.center (OddQuot K) := by
    rintro _ ⟨p, rfl⟩
    exact hcen p
  have hc2 : Nat.card (Subgroup.center (OddQuot K)) = 2 := hK.witness.2.1
  calc Nat.card P = Nat.card (P.subgroupOf K) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).symm.toEquiv
    _ = Nat.card f.range := Nat.card_congr (MonoidHom.ofInjective hf).toEquiv
    _ ≤ Nat.card (Subgroup.center (OddQuot K)) := Subgroup.card_le_of_le hrange
    _ = 2 := hc2

theorem mem_normalizer_of_centralizes_two_subgroup (hK : IsClassical2A7 ⊤ K z) {t : F}
    (ht : t ∈ Subgroup.centralizer ({z} : Set F)) {P : Subgroup F} (hPK : P ≤ K)
    (hP2 : IsPGroup 2 P) (hP3 : 3 ≤ Nat.card P) (hPt : ∀ x ∈ P, t * x = x * t) :
    t ∈ Subgroup.normalizer (K : Set F) := by
  by_contra hn
  have hK' : K.map (MulAut.conj t).toMonoidHom ∈ omegaAt K z z := map_conj_mem_omegaAt_self ht
  have hne : K.map (MulAut.conj t).toMonoidHom ≠ K := fun h =>
    hn (map_conj_eq_iff_mem_normalizer.mp h)
  have hPK' : P ≤ K.map (MulAut.conj t).toMonoidHom := by
    intro x hx
    refine ⟨x, hPK hx, ?_⟩
    show t * x * t⁻¹ = x
    rw [hPt x hx]
    group
  have := card_le_two_of_twins hK hK' hne hPK hPK' hP2
  omega

end Twins

section Step

variable {F : Type*} [Group F] [Finite F] {J : Subgroup F} {t : F}

theorem mem_normalizer_of_commute_of_mem_noncentral (hJ : IsClassical2A7 ⊤ J t) {z y : F}
    (hzt : z * t = t * z) (hy : y ∈ J) (hy2 : IsPGroup 2 (Subgroup.zpowers y))
    (hy3 : 3 ≤ Nat.card (Subgroup.zpowers y)) (hzy : z * y = y * z) :
    z ∈ Subgroup.normalizer (J : Set F) := by
  refine mem_normalizer_of_centralizes_two_subgroup hJ ?_
    (Subgroup.zpowers_le.mpr hy) hy2 hy3 ?_
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hzt.symm
  · intro x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (Commute.zpow_right (show Commute z y from hzy) n).eq

end Step

end CFSG.ClassicalInvolution.Hat2A7R
