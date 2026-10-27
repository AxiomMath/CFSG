module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42Setup
public import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

namespace L246C127

variable {G : Type} [Group G]

@[expose] def oddPPow (K : Subgroup G) : Set G :=
  {x | x ∈ K ∧ ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ IsPGroup q (Subgroup.zpowers x)}

theorem mem_oddPPow_le {K : Subgroup G} : oddPPow K ⊆ (K : Set G) := fun _ hx => hx.1

theorem closure_oddPPow_le (K : Subgroup G) : Subgroup.closure (oddPPow K) ≤ K :=
  (Subgroup.closure_le K).2 mem_oddPPow_le

theorem odd_orderOf_of_mem_oddPPow [Finite G] {K : Subgroup G} {x : G} (hx : x ∈ oddPPow K) :
    Odd (orderOf x) := by
  obtain ⟨-, q, hq, hq2, hp⟩ := hx
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  rw [Nat.card_zpowers] at hk
  rw [hk]
  exact (hq.odd_of_ne_two hq2).pow

theorem conj_mem_oddPPow {K : Subgroup G} {g x : G} (hg : g ∈ K) (hx : x ∈ oddPPow K) :
    g * x * g⁻¹ ∈ oddPPow K := by
  obtain ⟨hxK, q, hq, hq2, hp⟩ := hx
  refine ⟨K.mul_mem (K.mul_mem hg hxK) (K.inv_mem hg), q, hq, hq2, ?_⟩
  have h : Subgroup.zpowers (g * x * g⁻¹) =
      (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom := by
    rw [MonoidHom.map_zpowers]
    rfl
  rw [h]
  exact hp.map _

theorem le_normalizer_closure_oddPPow (K : Subgroup G) :
    K ≤ Subgroup.normalizer (Subgroup.closure (oddPPow K) : Set G) := by
  have key : ∀ g ∈ K, ∀ h ∈ Subgroup.closure (oddPPow K),
      g * h * g⁻¹ ∈ Subgroup.closure (oddPPow K) := by
    intro g hg h hh
    induction hh using Subgroup.closure_induction with
    | mem x hx => exact Subgroup.subset_closure (conj_mem_oddPPow hg hx)
    | one => simp
    | mul x y _ _ hx hy =>
      have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hx hy
    | inv x _ hx =>
      have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ hx
  exact L246.le_normalizer_of_forall_conj key

theorem le_closure_oddPPow [Finite G] {K : Subgroup G}
    (hK : ∀ (N : Subgroup ↥K) [N.Normal], IsPGroup 2 (↥K ⧸ N) → N = ⊤) :
    K ≤ Subgroup.closure (oddPPow K) := by
  classical
  set M : Subgroup G := Subgroup.closure (oddPPow K) with hM
  have hMK : M ≤ K := closure_oddPPow_le K
  have hnorm : (M.subgroupOf K).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hg := le_normalizer_closure_oddPPow K g.2
    have := (Subgroup.mem_normalizer_iff.1 hg n).1 hn
    simpa using this
  have : (M.subgroupOf K).Normal := hnorm
  have hidx : ∀ q : ℕ, q.Prime → q ≠ 2 → ¬ q ∣ (M.subgroupOf K).index := by
    intro q hq hq2 hqd
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨P⟩ : Nonempty (Sylow q ↥K) := inferInstance
    have hPN : (P : Subgroup ↥K) ≤ M.subgroupOf K := by
      intro y hy
      rw [Subgroup.mem_subgroupOf]
      apply Subgroup.subset_closure
      refine ⟨y.2, q, hq, hq2, ?_⟩
      have hyP : Subgroup.zpowers y ≤ (P : Subgroup ↥K) := Subgroup.zpowers_le.2 hy
      have := P.isPGroup'.to_le hyP
      have h : Subgroup.zpowers (y : G) = (Subgroup.zpowers y).map K.subtype := by
        rw [MonoidHom.map_zpowers]
        rfl
      rw [h]
      exact this.map _
    exact P.not_dvd_index (hqd.trans (Subgroup.index_dvd_of_le hPN))
  have hpow : ∃ k : ℕ, (M.subgroupOf K).index = 2 ^ k := by
    refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Subgroup.index_ne_zero_of_finite ?_⟩
    intro d hd hdd
    by_contra hne
    exact hidx d hd hne hdd
  obtain ⟨k, hk⟩ := hpow
  have hp2 : IsPGroup 2 (↥K ⧸ M.subgroupOf K) :=
    IsPGroup.of_card (n := k) (by rw [← Subgroup.index_eq_card]; exact hk)
  have htop := hK (M.subgroupOf K) hp2
  intro x hx
  have : (⟨x, hx⟩ : ↥K) ∈ M.subgroupOf K := by rw [htop]; trivial
  exact this

theorem commutator_le_commutator_commutator_two [Finite G] {R K : Subgroup G} (hR : IsPGroup 2 R)
    (hKR : K ≤ Subgroup.normalizer (R : Set G)) (hgen : K ≤ Subgroup.closure (oddPPow K)) :
    ⁅R, K⁆ ≤ ⁅⁅R, K⁆, K⁆ := by
  have hRK : K ≤ Subgroup.normalizer ((⁅R, K⁆ : Subgroup G) : Set G) :=
    CFSG.SignalizerFunctor.Helpers.normalized_commutator_normalized K R hKR
  have hM : K ≤ Subgroup.normalizer ((⁅⁅R, K⁆, K⁆ : Subgroup G) : Set G) :=
    CFSG.SignalizerFunctor.Helpers.normalized_commutator_normalized K ⁅R, K⁆ hRK
  have hgenstep : ∀ x ∈ oddPPow K, ∀ r ∈ R, ⁅r, x⁆ ∈ (⁅⁅R, K⁆, K⁆ : Subgroup G) := by
    intro x hx r hr
    obtain ⟨hxK, q, hq, hq2, hp⟩ := hx
    have hAK : Subgroup.zpowers x ≤ K := Subgroup.zpowers_le.2 hxK
    have hAN : Subgroup.zpowers x ≤ Subgroup.normalizer (R : Set G) := hAK.trans hKR
    have hcop : Nat.Coprime q (Nat.card R) := by
      obtain ⟨k, hk⟩ := hR.exists_card_eq
      rw [hk]
      exact Nat.Coprime.pow_right k ((Nat.coprime_primes hq Nat.prime_two).2 hq2)
    have hidem := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_idempotent q hq
      (Subgroup.zpowers x) R hp hAN hcop
    have h1 : ⁅r, x⁆ ∈ (⁅R, Subgroup.zpowers x⁆ : Subgroup G) :=
      Subgroup.commutator_mem_commutator hr (Subgroup.mem_zpowers x)
    rw [← hidem] at h1
    exact Subgroup.commutator_mono (Subgroup.commutator_mono le_rfl hAK) hAK h1
  have hP : ∀ k, k ∈ Subgroup.closure (oddPPow K) → ∀ r ∈ R, ⁅r, k⁆ ∈ (⁅⁅R, K⁆, K⁆ : Subgroup G) := by
    intro k hk'
    induction hk' using Subgroup.closure_induction with
    | mem x hx => exact fun r hr => hgenstep x hx r hr
    | one => intro r _; simp
    | mul x y hx hy ihx ihy =>
      intro r hr
      have hxK : x ∈ K := closure_oddPPow_le K hx
      have e : ⁅r, x * y⁆ = ⁅r, x⁆ * (x * ⁅r, y⁆ * x⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e]
      refine Subgroup.mul_mem _ (ihx r hr) ?_
      have := (Subgroup.mem_normalizer_iff.1 (hM hxK) ⁅r, y⁆).1
      exact this (ihy r hr)
    | inv x hx ihx =>
      intro r hr
      have hxK : x ∈ K := closure_oddPPow_le K hx
      have e : ⁅r, x⁻¹⁆ = x⁻¹ * ⁅r, x⁆⁻¹ * x := by
        simp only [commutatorElement_def]; group
      rw [e]
      have h1 : ⁅r, x⁆⁻¹ ∈ (⁅⁅R, K⁆, K⁆ : Subgroup G) := Subgroup.inv_mem _ (ihx r hr)
      have := (Subgroup.mem_normalizer_iff.1 (hM (K.inv_mem hxK)) _).1 h1
      simpa [mul_assoc] using this
  exact Subgroup.commutator_le.2 fun r hr k hk => hP k (hgen hk) r hr


theorem mul_mem_of_odd_orderOf {H M N : Subgroup G} (hHM : H ≤ M) (hHn : (H.subgroupOf M).Normal)
    (hNM : N ≤ M) (hN2 : IsPGroup 2 N) {x n : G} (hx : x ∈ H) (hn : n ∈ N)
    (hodd : Odd (orderOf (n * x))) : n * x ∈ H := by
  have : (H.subgroupOf M).Normal := hHn
  let π : ↥M →* ↥M ⧸ H.subgroupOf M := QuotientGroup.mk' (H.subgroupOf M)
  let n' : ↥M := ⟨n, hNM hn⟩
  let x' : ↥M := ⟨x, hHM hx⟩
  have hx'H : x' ∈ H.subgroupOf M := Subgroup.mem_subgroupOf.2 hx
  have hπx : π x' = 1 := (QuotientGroup.eq_one_iff _).2 hx'H
  have hπy : π (n' * x') = π n' := by rw [map_mul, hπx, mul_one]
  have hord_y : orderOf (π (n' * x')) ∣ orderOf (n * x) := by
    have h1 := orderOf_map_dvd π (n' * x')
    have h2 : orderOf (n' * x') = orderOf (n * x) := by
      rw [show n' * x' = ⟨n * x, M.mul_mem (hNM hn) (hHM hx)⟩ from rfl, Subgroup.orderOf_mk]
    rwa [h2] at h1
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hN2 ⟨n, hn⟩
  have hord_n : orderOf (π n') ∣ 2 ^ k := by
    have h1 := orderOf_map_dvd π n'
    have h2 : orderOf n' = 2 ^ k := by
      have e1 : orderOf n' = orderOf n := Subgroup.orderOf_mk n (hNM hn)
      have e2 : orderOf (⟨n, hn⟩ : ↥N) = orderOf n := Subgroup.orderOf_mk n hn
      rw [e1, ← e2, hk]
    rwa [h2] at h1
  have hcop : Nat.Coprime (2 ^ k) (orderOf (n * x)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
  have h1 : orderOf (π (n' * x')) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (by rwa [hπy]) hord_y
  have : n' * x' ∈ H.subgroupOf M :=
    (QuotientGroup.eq_one_iff _).1 (orderOf_eq_one_iff.1 h1)
  exact Subgroup.mem_subgroupOf.1 this

theorem conj_mem_of_isSubnormal {H P N : Subgroup G} (hHP : IsSubnormal H P) :
    N ≤ P → (N.subgroupOf P).Normal → IsPGroup 2 N → ∀ x ∈ H, Odd (orderOf x) →
      ∀ n ∈ N, n * x * n⁻¹ ∈ H := by
  induction hHP with
  | refl H =>
    intro hNP _ _ x hx _ n hn
    exact H.mul_mem (H.mul_mem (hNP hn) hx) (H.inv_mem (hNP hn))
  | @step H M P hHM hHn hMP ih =>
    intro hNP hNn hN2 x hx hxo n hn
    have hMP' : M ≤ P := A3.subnormal_le hMP
    have hxM : x ∈ M := hHM hx
    have hyM : n * x * n⁻¹ ∈ M := ih hNP hNn hN2 x hxM hxo n hn
    have hxP : x ∈ P := hMP' hxM
    have hn₁N : n * x * n⁻¹ * x⁻¹ ∈ N := by
      have h1 : x * n⁻¹ * x⁻¹ ∈ N := by
        have := hNn.conj_mem ⟨n⁻¹, hNP (N.inv_mem hn)⟩ (by
          rw [Subgroup.mem_subgroupOf]; exact N.inv_mem hn) ⟨x, hxP⟩
        simpa [Subgroup.mem_subgroupOf] using this
      have e : n * x * n⁻¹ * x⁻¹ = n * (x * n⁻¹ * x⁻¹) := by group
      rw [e]
      exact N.mul_mem hn h1
    have hn₁M : n * x * n⁻¹ * x⁻¹ ∈ M := M.mul_mem hyM (M.inv_mem hxM)
    have hord : Odd (orderOf (n * x * n⁻¹ * x⁻¹ * x)) := by
      have e : n * x * n⁻¹ * x⁻¹ * x = n * x * n⁻¹ := by group
      rw [e]
      have := orderOf_injective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective x
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
      rw [this]
      exact hxo
    have key := mul_mem_of_odd_orderOf hHM hHn (N := N ⊓ M) inf_le_right
      (hN2.to_le inf_le_left) hx ⟨hn₁N, hn₁M⟩ hord
    have e : n * x * n⁻¹ * x⁻¹ * x = n * x * n⁻¹ := by group
    rwa [e] at key

theorem le_normalizer_of_isSubnormal {K P N : Subgroup G} (hKP : IsSubnormal K P) (hNP : N ≤ P)
    (hNn : (N.subgroupOf P).Normal) (hN2 : IsPGroup 2 N) [Finite G]
    (hgen : K ≤ Subgroup.closure (oddPPow K)) : N ≤ Subgroup.normalizer (K : Set G) := by
  have key : ∀ n ∈ N, ∀ k ∈ Subgroup.closure (oddPPow K), n * k * n⁻¹ ∈ K := by
    intro n hn k hk
    induction hk using Subgroup.closure_induction with
    | mem x hx =>
      exact conj_mem_of_isSubnormal hKP hNP hNn hN2 x hx.1 (odd_orderOf_of_mem_oddPPow hx) n hn
    | one => simp
    | mul x y _ _ hx hy =>
      have e : n * (x * y) * n⁻¹ = (n * x * n⁻¹) * (n * y * n⁻¹) := by group
      rw [e]
      exact K.mul_mem hx hy
    | inv x _ hx =>
      have e : n * x⁻¹ * n⁻¹ = (n * x * n⁻¹)⁻¹ := by group
      rw [e]
      exact K.inv_mem hx
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    exact key n hn k (hgen hk)
  · intro hk
    have := key n⁻¹ (N.inv_mem hn) _ (hgen hk)
    simpa [mul_assoc] using this

theorem commutator_le_inf_of_isSubnormal [Finite G] {K P N : Subgroup G} (hKP : IsSubnormal K P)
    (hNP : N ≤ P) (hNn : (N.subgroupOf P).Normal) (hN2 : IsPGroup 2 N)
    (hgen : K ≤ Subgroup.closure (oddPPow K)) : ⁅K, N⁆ ≤ K ⊓ N := by
  have hnorm := le_normalizer_of_isSubnormal hKP hNP hNn hN2 hgen
  have hKP' : K ≤ P := A3.subnormal_le hKP
  rw [Subgroup.commutator_le]
  intro k hk n hn
  refine ⟨?_, ?_⟩
  · have h1 : n * k⁻¹ * n⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 (hnorm hn) k⁻¹).1 (K.inv_mem hk)
    have : k * (n * k⁻¹ * n⁻¹) ∈ K := K.mul_mem hk h1
    simpa [commutatorElement_def, mul_assoc] using this
  · have h1 := hNn.conj_mem ⟨n, hNP hn⟩ (by rw [Subgroup.mem_subgroupOf]; exact hn) ⟨k, hKP' hk⟩
    have h2 : k * n * k⁻¹ ∈ N := by simpa [Subgroup.mem_subgroupOf] using h1
    have : k * n * k⁻¹ * n⁻¹ ∈ N := N.mul_mem h2 (N.inv_mem hn)
    simpa [commutatorElement_def] using this

end L246C127

end CFSG.QuasithinUnique
