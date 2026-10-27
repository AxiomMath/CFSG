module

public import CFSG.GH74.Generic.BProg.B3.S3Sec29Tail

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.ABGLocalTools
open scoped commutatorElement

namespace S3T3

variable {G : Type} [Group G] [Finite G]

theorem H29.exists_E {x y : G} {K A B Q : Subgroup G} (h : H29 G x K A B Q y) :
    ∃ E : Subgroup G, E ≤ K ∧ A = E ⊔ zpowers x ∧ x ∉ E ∧ CFSG.IsElementaryAbelian 2 ↥E ∧
      Nat.card ↥E = 4 ∧ y ∈ E := by
  have hx : orderOf x = 2 := h.circ.1.1.1.1
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := h.circ.1.1.1.2.2
  have hZ := B1.PilotS3.center_trivial_of_shape3 hK h.shape.qShape3
  obtain ⟨E, hEK, hAE, hxE, hEel, hE4⟩ := S3Theta52.exists_E_of_src h.src hZ
  have hxK : x ∉ K := B1.PilotS5.not_mem_of_center_trivial hx hK.1 hZ
  refine ⟨E, hEK, hAE, hxE, hEel, hE4, ?_⟩
  obtain ⟨hyA, hyK⟩ := Subgroup.mem_inf.1 h.y_mem
  have hc : ∀ e ∈ E, ∀ k ∈ zpowers x, e * k = k * e := by
    intro e he k hk
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    exact (Commute.zpow_right (show Commute e x from
      Subgroup.mem_centralizer_singleton_iff.1 (hK.1 (hEK he))) n).eq
  rw [hAE] at hyA
  obtain ⟨e, he, k, hk, rfl⟩ := S3Theta52.exists_mul_of_mem_sup hc hyA
  have hkK : k ∈ K := by
    have := K.mul_mem (K.inv_mem (hEK he)) hyK
    simpa using this
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
  have hmod : x ^ (n % 2) = x ^ n := by
    have := zpow_mod_orderOf x n
    rwa [hx, Nat.cast_ofNat] at this
  rcases Int.emod_two_eq_zero_or_one n with h0 | h1
  · rw [← hmod, h0, zpow_zero, mul_one]
    exact he
  · exact absurd (by rw [← hmod, h1, zpow_one] at hkK; exact hkK) hxK

omit [Finite G] in
theorem inf_eq_of_exists_E {x : G} {K A E : Subgroup G} (hKx : K ≤ centralizer ({x} : Set G))
    (hx : orderOf x = 2) (hxK : x ∉ K) (hEK : E ≤ K) (hAE : A = E ⊔ zpowers x) :
    A ⊓ K = E := by
  apply le_antisymm
  · intro a ha
    obtain ⟨haA, haK⟩ := Subgroup.mem_inf.1 ha
    have hc : ∀ e ∈ E, ∀ k ∈ zpowers x, e * k = k * e := by
      intro e he k hk
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
      exact (Commute.zpow_right (show Commute e x from
        Subgroup.mem_centralizer_singleton_iff.1 (hKx (hEK he))) n).eq
    rw [hAE] at haA
    obtain ⟨e, he, k, hk, rfl⟩ := S3Theta52.exists_mul_of_mem_sup hc haA
    have hkK : k ∈ K := by
      have := K.mul_mem (K.inv_mem (hEK he)) haK
      simpa using this
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    have hmod : x ^ (n % 2) = x ^ n := by
      have := zpow_mod_orderOf x n
      rwa [hx, Nat.cast_ofNat] at this
    rcases Int.emod_two_eq_zero_or_one n with h0 | h1
    · rw [← hmod, h0, zpow_zero, mul_one]
      exact he
    · exact absurd (by rw [← hmod, h1, zpow_one] at hkK; exact hkK) hxK
  · exact le_inf (hAE ▸ le_sup_left) hEK

omit [Finite G] in
theorem mem_pPrimeCoreOf_of_mem_cSec {K : Subgroup G}
    (hZ : ∀ z : ↥K ⧸ pPrimeCore 2 ↥K, (∀ g, g * z = z * g) → z = 1) {c : G}
    (hcs : c ∈ cSec K) (hcK : c ∈ K) : c ∈ pPrimeCoreOf 2 K := by
  set c' : ↥K := ⟨c, hcK⟩ with hc'
  have hcomm : ∀ g : ↥K ⧸ pPrimeCore 2 ↥K,
      g * (QuotientGroup.mk c' : ↥K ⧸ pPrimeCore 2 ↥K) = QuotientGroup.mk c' * g := by
    intro g
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
    have h1 : ⁅(k : G), c⁆ ∈ pPrimeCoreOf 2 K := hcs.2.2 (k : G) k.2
    obtain ⟨o, ho, hoe⟩ := h1
    have hoeq : o = ⁅k, c'⁆ := Subtype.ext hoe
    have h2 : (QuotientGroup.mk ⁅k, c'⁆ : ↥K ⧸ pPrimeCore 2 ↥K) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (hoeq ▸ ho)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    have h4 : ⁅k, c'⁆ = k * c' * k⁻¹ * c'⁻¹ := rfl
    have : k * c' = ⁅k, c'⁆ * (c' * k) := by rw [h4]; group
    rw [this, QuotientGroup.mk_mul, h2, one_mul]
  have hz := hZ _ hcomm
  exact ⟨c', (QuotientGroup.eq_one_iff _).1 hz, rfl⟩

omit [Finite G] in
theorem exists_mul_of_mem_sup_normalizer {N H : Subgroup G} (hH : H ≤ normalizer (N : Set G))
    {g : G} (hg : g ∈ N ⊔ H) : ∃ n ∈ N, ∃ h ∈ H, g = n * h := by
  have hconj : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N := fun h hh n hn =>
    (Subgroup.mem_normalizer_iff.1 (hH hh) n).1 hn
  let S : Subgroup G :=
    { carrier := {g | ∃ n ∈ N, ∃ h ∈ H, g = n * h}
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨n₁, hn₁, h₁, hh₁, rfl⟩ ⟨n₂, hn₂, h₂, hh₂, rfl⟩
        refine ⟨n₁ * (h₁ * n₂ * h₁⁻¹), mul_mem hn₁ (hconj h₁ hh₁ n₂ hn₂), h₁ * h₂,
          mul_mem hh₁ hh₂, ?_⟩
        group
      inv_mem' := by
        rintro _ ⟨n, hn, h, hh, rfl⟩
        refine ⟨h⁻¹ * n⁻¹ * h⁻¹⁻¹, ?_, h⁻¹, inv_mem hh, ?_⟩
        · exact hconj h⁻¹ (inv_mem hh) n⁻¹ (inv_mem hn)
        · group }
  have hle : N ⊔ H ≤ S := sup_le (fun n hn => ⟨n, hn, 1, one_mem _, by simp⟩)
    (fun h hh => ⟨1, one_mem _, h, hh, by simp⟩)
  exact hle hg

theorem card_le_four_mul_inf {x : G} {K X : Subgroup G}
    (hZ : ∀ z : ↥K ⧸ pPrimeCore 2 ↥K, (∀ g, g * z = z * g) → z = 1)
    (hC : pRank 2 ↥(CxK x K) ≤ 2) (hXel : CFSG.IsElementaryAbelian 2 ↥X)
    (hXM : X ≤ K ⊔ CxK x K) : Nat.card ↥X ≤ 4 * Nat.card ↥(X ⊓ K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCN : CxK x K ≤ normalizer (K : Set G) := fun c hc => (Subgroup.mem_inf.1 hc).2.1
  set M : Subgroup G := K ⊔ CxK x K with hM
  have hCM : CxK x K ≤ M := le_sup_right
  have hKM : K ≤ M := le_sup_left
  have hMN : M ≤ normalizer (K : Set G) := sup_le Subgroup.le_normalizer hCN
  set K' : Subgroup ↥M := K.subgroupOf M with hK'
  have hK'n : K'.Normal := ⟨fun n hn g => by
    rw [hK', Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.1 (hMN g.2) n).1 hn⟩
  set q : ↥M →* ↥M ⧸ K' := QuotientGroup.mk' K' with hq
  have hq1 : ∀ m : ↥M, q m = 1 ↔ (m : G) ∈ K := fun m => by
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hK', Subgroup.mem_subgroupOf]
  set ψ : ↥(CxK x K) →* ↥M ⧸ K' := q.comp (Subgroup.inclusion hCM) with hψ
  have hψs : Function.Surjective ψ := by
    intro w
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective K' w
    obtain ⟨k, hk, c, hc, hm⟩ := exists_mul_of_mem_sup_normalizer hCN m.2
    refine ⟨⟨c, hc⟩, ?_⟩
    show q ⟨c, hCM hc⟩ = q m
    have e1 : q m = q ⟨k, hKM hk⟩ * q ⟨c, hCM hc⟩ := by
      rw [← map_mul]
      congr 1
      exact Subtype.ext hm
    rw [e1, (hq1 ⟨k, hKM hk⟩).2 hk, one_mul]
  have hψker : ¬ 2 ∣ Nat.card ψ.ker := by
    let ι : ↥ψ.ker →* ↥(pPrimeCoreOf 2 K) :=
      { toFun := fun c => ⟨((c : ↥(CxK x K)) : G), mem_pPrimeCoreOf_of_mem_cSec hZ
          (Subgroup.mem_inf.1 (c : ↥(CxK x K)).2).2 ((hq1 _).1 (MonoidHom.mem_ker.1 c.2))⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hι : Function.Injective ι := fun a b hab => by
      have h := congrArg (fun z : ↥(pPrimeCoreOf 2 K) => (z : G)) hab
      exact Subtype.ext (Subtype.ext h)
    have hdvd := Subgroup.card_dvd_of_injective ι hι
    intro h2
    have := Nat.odd_iff.1 (TwoThin.card_pPrimeCoreOf_odd K)
    have h3 := dvd_trans h2 hdvd
    omega
  have hrank : pRank 2 (↥M ⧸ K') ≤ 2 := by
    rw [← Stage1.Thm2.Recip.pRank_eq_of_mulEquiv'
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψs),
      CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two _ hψker]
    exact hC
  set X' : Subgroup ↥M := X.subgroupOf M with hX'
  have hX'el : CFSG.IsElementaryAbelian 2 ↥X' := CFSG.IsElementaryAbelian.subgroupOf hXM
  have hYel : CFSG.IsElementaryAbelian 2 ↥(X'.map q) := CFSG.IsElementaryAbelian.map q
  have hY4 : Nat.card ↥(X'.map q) ≤ 4 := by
    rw [C3.Layer1.Back.card_eq_two_pow_pRank hYel]
    calc 2 ^ pRank 2 ↥(X'.map q) ≤ 2 ^ 2 :=
          Nat.pow_le_pow_right (by norm_num) ((pRank_le_top' _).trans hrank)
      _ = 4 := by norm_num
  set f : ↥X' →* ↥M ⧸ K' := q.comp X'.subtype with hf
  have hfr : f.range = X'.map q := by rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  have hfk : Nat.card ↥f.ker = Nat.card ↥(X ⊓ K) := by
    refine Nat.card_congr
      { toFun := fun a => ⟨(((a : ↥X') : ↥M) : G), Subgroup.mem_inf.2
          ⟨Subgroup.mem_subgroupOf.1 (a : ↥X').2, (hq1 _).1 (MonoidHom.mem_ker.1 a.2)⟩⟩
        invFun := fun b => ⟨⟨⟨b, hXM (Subgroup.mem_inf.1 b.2).1⟩,
          Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.1 b.2).1⟩,
          MonoidHom.mem_ker.2 ((hq1 _).2 (Subgroup.mem_inf.1 b.2).2)⟩
        left_inv := fun a => rfl
        right_inv := fun b => rfl }
  have hcard : Nat.card ↥X' = Nat.card ↥f.range * Nat.card ↥f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  have hX'X : Nat.card ↥X' = Nat.card ↥X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv
  rw [← hX'X, hcard, hfr, hfk]
  exact Nat.mul_le_mul_right _ hY4

omit [Finite G] in
theorem isRootFour_map_conj {F : Subgroup (Equiv.Perm (Fin 7))} (hF : GLS.Th2.Obs.IsRootFour F)
    (τ : Equiv.Perm (Fin 7)) :
    GLS.Th2.Obs.IsRootFour (F.map (MulAut.conj τ).toMonoidHom) := by
  classical
  obtain ⟨hFA, hF4, hFsq, S, hS4, hSupp⟩ := hF
  refine ⟨?_, ?_, ?_, S.map τ.toEmbedding, by rw [Finset.card_map, hS4], ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    have h1 := hFA hf
    rw [Equiv.Perm.mem_alternatingGroup] at h1 ⊢
    simp [MulAut.conj_apply, h1]
  · rw [Subgroup.card_map_of_injective (MulAut.conj τ).injective, hF4]
  · rintro _ ⟨f, hf, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show τ * f * τ⁻¹ * (τ * f * τ⁻¹) = τ * (f * f) * τ⁻¹ by group, hFsq f hf]
    group
  · rintro _ ⟨f, hf, rfl⟩ hne
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hne ⊢
    have hf1 : f ≠ 1 := fun h => hne (by rw [h]; group)
    rw [Equiv.Perm.support_conj, hSupp f hf hf1]

end S3T3

end CFSG.GH74.Generic.BProg.B3
