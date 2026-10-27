module

public import CFSG.GH74.GLS.Balance.CompNormalizes
import CFSG.ClassicalInvolution.LBalance.Glauberman
import CFSG.Walter.AStar.Subnormal

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG
open scoped commutatorElement

namespace Comp

theorem innerAut_normal {K : Type*} [Group K] : ((MulAut.conj : K →* MulAut K).range).Normal := by
  refine ⟨?_⟩
  rintro _ ⟨k, rfl⟩ φ
  refine ⟨φ k, ?_⟩
  ext y
  simp [MulAut.conj_apply]

theorem mem_sup_of_pow_mem {G : Type*} [Group G] {N' I : Subgroup G} {g : G} {a m : ℕ}
    (hcop : Nat.Coprime a m) (hN : g ^ a ∈ N') (hI : g ^ m ∈ I) : g ∈ N' ⊔ I := by
  obtain ⟨s, t, hst⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have h : g = (g ^ a) ^ s * (g ^ m) ^ t := by
    rw [← zpow_natCast g a, ← zpow_natCast g m, ← zpow_mul, ← zpow_mul, ← zpow_add]
    have : (a : ℤ) * s + m * t = 1 := by linarith
    rw [this, zpow_one]
  rw [h]
  exact mul_mem_sup (zpow_mem hN s) (zpow_mem hI t)

theorem mem_of_mem_sup_of_two_pow {G : Type*} [Group G] {N' I : Subgroup G} [I.Normal]
    (hodd : Odd (Nat.card N')) {g : G} (hg : g ∈ N' ⊔ I) {k : ℕ} (hgk : g ^ (2 ^ k) = 1) :
    g ∈ I := by
  set π : G →* G ⧸ I := QuotientGroup.mk' I with hπ
  have hmem : π g ∈ N'.map π := by
    have h1 := Subgroup.mem_map_of_mem π hg
    rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq] at h1
  have h2 : orderOf (π g) ∣ Nat.card (N'.map π) := by
    have := orderOf_dvd_natCard (⟨π g, hmem⟩ : N'.map π)
    rwa [Subgroup.orderOf_mk] at this
  have h3 : Nat.card (N'.map π) ∣ Nat.card N' := Subgroup.card_map_dvd N' π
  have h4 : orderOf (π g) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hgk, map_one])
  have hcop : Nat.Coprime (2 ^ k) (Nat.card N') :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have h5 : orderOf (π g) ∣ Nat.gcd (2 ^ k) (Nat.card N') := Nat.dvd_gcd h4 (h2.trans h3)
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h5
  exact (QuotientGroup.eq_one_iff g).mp h5

theorem pow_index_mem {G : Type*} [Group G] (N : Subgroup G) [N.Normal] (g : G) :
    g ^ N.index ∈ N := by
  have h : (g : G ⧸ N) ^ Nat.card (G ⧸ N) = 1 := pow_card_eq_one'
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, ← Subgroup.index_eq_card] at h
  exact h

section Action

variable {X : Type} [Group X]

theorem rho_mem_sup {K Q : Subgroup X} (Γ : Subgroup (MulAut K))
    (hΓ : ∀ φ : MulAut K, (∀ s : K, (s : X) ∈ Q → φ s = s) → φ ∈ Γ)
    (N : Subgroup Γ) [N.Normal] {a : ℕ} (hN : N.index = 2 ^ a) {v n c : X} (hn : n ∈ K)
    (hc : c ∈ centralizer (Q : Set X)) (hvnc : v = n * c) (hv : v ∈ normalizer (K : Set X))
    (hcop : Nat.Coprime (orderOf v) 2) :
    K.normalizerMonoidHom ⟨v, hv⟩ ∈ N.map Γ.subtype ⊔ (MulAut.conj : K →* MulAut K).range := by
  set I : Subgroup (MulAut K) := (MulAut.conj : K →* MulAut K).range with hI
  have : I.Normal := innerAut_normal
  have hnN : n ∈ normalizer (K : Set X) := Subgroup.le_normalizer hn
  have hcN : c ∈ normalizer (K : Set X) := by
    have : c = n⁻¹ * v := by rw [hvnc]; group
    rw [this]
    exact mul_mem (inv_mem hnN) hv
  set ρ := K.normalizerMonoidHom with hρ
  have hmul : ρ ⟨v, hv⟩ = ρ ⟨n, hnN⟩ * ρ ⟨c, hcN⟩ := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext hvnc
  have hρn : ρ ⟨n, hnN⟩ ∈ I := by
    refine ⟨⟨n, hn⟩, ?_⟩
    ext y
    simp [hρ, MulAut.conj_apply]
  have hρc : ρ ⟨c, hcN⟩ ∈ Γ := by
    refine hΓ _ fun s hsQ => ?_
    apply Subtype.ext
    have h := mem_centralizer_iff.mp hc s hsQ
    simp only [hρ, Subgroup.normalizerMonoidHom_apply_apply_coe]
    rw [← h]
    group
  set g₀ : Γ := ⟨ρ ⟨c, hcN⟩, hρc⟩ with hg₀
  have h2a : (ρ ⟨c, hcN⟩) ^ (2 ^ a) ∈ N.map Γ.subtype := by
    have := pow_index_mem N g₀
    rw [hN] at this
    exact ⟨g₀ ^ (2 ^ a), this, by simp [hg₀]⟩
  have hπρ : QuotientGroup.mk' I (ρ ⟨c, hcN⟩) = QuotientGroup.mk' I (ρ ⟨v, hv⟩) := by
    rw [hmul, map_mul]
    have : QuotientGroup.mk' I (ρ ⟨n, hnN⟩) = 1 := (QuotientGroup.eq_one_iff _).mpr hρn
    rw [this, one_mul]
  have hρv : (ρ ⟨v, hv⟩) ^ (orderOf v) = 1 := by
    rw [← map_pow]
    have : (⟨v, hv⟩ : normalizer (K : Set X)) ^ (orderOf v) = 1 := by
      rw [← Subgroup.orderOf_mk v hv]
      exact pow_orderOf_eq_one _
    rw [this, map_one]
  have hm : (ρ ⟨c, hcN⟩) ^ (orderOf v) ∈ I := by
    rw [← QuotientGroup.ker_mk' I]
    rw [MonoidHom.mem_ker, map_pow, hπρ, ← map_pow, hρv, map_one]
  have hcopm : Nat.Coprime (2 ^ a) (orderOf v) := Nat.Coprime.pow_left a hcop.symm
  have hρc' : ρ ⟨c, hcN⟩ ∈ N.map Γ.subtype ⊔ I := mem_sup_of_pow_mem hcopm h2a hm
  rw [hmul]
  exact mul_mem (Subgroup.mem_sup_right hρn) hρc'

end Action

end Comp

variable {X : Type} [Group X] [Finite X]

theorem exists_inner_of_two_element (hO : pPrimeCore 2 X = ⊥) {K : Subgroup X} (hK : IsComponent K)
    (Q : Subgroup X) (hQK : Q ≤ K) (hQ2 : IsPGroup 2 Q)
    (hQs : ∀ T : Subgroup X, T ≤ K → IsPGroup 2 T → Nat.card T ≤ Nat.card Q)
    (H : Subgroup X) (hHK : H ≤ normalizer (K : Set X))
    (hgen : ∀ H' : Subgroup X, (∀ v ∈ H, Nat.Coprime (orderOf v) 2 → v ∈ H') → H ≤ H')
    (hdec : ∀ v ∈ H, Nat.Coprime (orderOf v) 2 → ∃ n ∈ K, ∃ c ∈ centralizer (Q : Set X), v = n * c)
    {r : X} (hr : r ∈ H) (hr2 : ∃ k : ℕ, r ^ (2 ^ k) = 1) :
    ∃ k ∈ K, ∀ y ∈ K, r * y * r⁻¹ = k * y * k⁻¹ := by
  obtain ⟨S, hS⟩ := Comp.exists_sylow_of_maximal hQK hQ2 hQs
  have hOK : pPrimeCore 2 K = ⊥ := by
    have h := CFSG.Walter.map_pPrimeCore_le_of_isSubnormal hK.2
    rw [hO, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective] at h
    exact h
  obtain ⟨N, hNn, hNodd, a, hNa⟩ :=
    CFSG.ClassicalInvolution.glauberman_sylowFixingAut_normal_complement_index hOK S
  have hΓ : ∀ φ : MulAut K, (∀ s : K, (s : X) ∈ Q → φ s = s) →
      φ ∈ CFSG.ClassicalInvolution.sylowFixingAut (S : Subgroup K) := by
    intro φ hφ
    rw [CFSG.ClassicalInvolution.mem_sylowFixingAut]
    intro s hs
    exact hφ s (hS ▸ ⟨s, hs, rfl⟩)
  set ρ := K.normalizerMonoidHom with hρ
  set I : Subgroup (MulAut K) := (MulAut.conj : K →* MulAut K).range with hI
  have : I.Normal := Comp.innerAut_normal
  set M : Subgroup (MulAut K) :=
    N.map (CFSG.ClassicalInvolution.sylowFixingAut (S : Subgroup K)).subtype ⊔ I with hM
  have hH₁ : H ≤ (M.comap ρ).map (normalizer (K : Set X)).subtype := by
    refine hgen _ fun v hv hcop => ?_
    obtain ⟨n, hn, c, hc, hvnc⟩ := hdec v hv hcop
    exact ⟨⟨v, hHK hv⟩, Comp.rho_mem_sup _ hΓ N hNa hn hc hvnc (hHK hv) hcop, rfl⟩
  obtain ⟨z, hz, hzr⟩ := hH₁ hr
  have hzr' : z = ⟨r, hHK hr⟩ := Subtype.ext hzr
  rw [hzr'] at hz
  obtain ⟨k₂, hk₂⟩ := hr2
  have hρr : (ρ ⟨r, hHK hr⟩) ^ (2 ^ k₂) = 1 := by
    rw [← map_pow]
    have : (⟨r, hHK hr⟩ : normalizer (K : Set X)) ^ (2 ^ k₂) = 1 := Subtype.ext hk₂
    rw [this, map_one]
  have hodd : Odd (Nat.card (N.map (CFSG.ClassicalInvolution.sylowFixingAut (S : Subgroup K)).subtype)) := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact hNodd
  obtain ⟨k, hk⟩ := Comp.mem_of_mem_sup_of_two_pow hodd hz hρr
  refine ⟨k, k.2, fun y hy => ?_⟩
  have h := congrArg (fun f : MulAut K => ((f ⟨y, hy⟩ : K) : X)) hk
  simp only [hρ, Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply] at h
  exact h.symm

end CFSG.GH74.GLS.Balance
