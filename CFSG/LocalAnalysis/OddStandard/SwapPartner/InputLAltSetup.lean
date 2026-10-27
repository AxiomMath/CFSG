module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.InputLShape
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.InputLDescent
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.InputLDescentCentral

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Equiv Equiv.Perm Subgroup

variable {X : Type*} [Group X] [Finite X] {t : X} {Sg V K : Subgroup X}

@[expose] def imageAbar (Sg K : Subgroup X) {m : ℕ}
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin m)) : Subgroup (Perm (Fin m)) :=
  ((⁅Sg, Sg⁆ : Subgroup X).subgroupOf K).map (toPerm e)

private noncomputable def resAbar {Sg K : Subgroup X} {m : ℕ}
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin m)) :
    ((⁅Sg, Sg⁆ : Subgroup X).subgroupOf K) →* Perm (Fin m) :=
  (toPerm e).domRestrict ((⁅Sg, Sg⁆ : Subgroup X).subgroupOf K)

private lemma resAbar_apply {Sg K : Subgroup X} {m : ℕ}
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin m))
    (x : ↥((⁅Sg, Sg⁆ : Subgroup X).subgroupOf K)) :
    resAbar (Sg := Sg) (K := K) e x = toPerm e x := rfl

private lemma resAbar_range {Sg K : Subgroup X} {m : ℕ}
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin m)) :
    (resAbar (Sg := Sg) (K := K) e).range = imageAbar Sg K e := by
  rw [imageAbar]
  exact MonoidHom.domRestrict_range ((⁅Sg, Sg⁆ : Subgroup X).subgroupOf K) (toPerm e)

private lemma resAbar_injective (hS : SwapShape t Sg V) (hA : ⁅Sg, Sg⁆ ≤ K) {m : ℕ}
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin m)) :
    Function.Injective (resAbar (Sg := Sg) (K := K) e) := by
  haveI hA_simple : IsSimpleGroup (⁅Sg, Sg⁆ : Subgroup X) := hS.isSimpleGroup_commutator_sg
  haveI hsimple : IsSimpleGroup ((⁅Sg, Sg⁆ : Subgroup X).subgroupOf K) :=
    (Subgroup.subgroupOfEquivOfLe hA).isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (resAbar (Sg := Sg) (K := K) e).ker with h | h
  · exact (MonoidHom.ker_eq_bot_iff _).mp h
  · exfalso
    have hle_center : ((⁅Sg, Sg⁆ : Subgroup X).subgroupOf K) ≤ Subgroup.center K := by
      intro x hx
      have hxker : (⟨x, hx⟩ : ↥((⁅Sg, Sg⁆ : Subgroup X).subgroupOf K)) ∈
          (resAbar (Sg := Sg) (K := K) e).ker := by
        rw [h]; exact Subgroup.mem_top _
      rw [MonoidHom.mem_ker] at hxker
      have hxker' : x ∈ (toPerm e).ker := by
        rw [MonoidHom.mem_ker]
        rwa [resAbar_apply] at hxker
      rwa [ker_toPerm] at hxker'
    haveI : IsMulCommutative ((⁅Sg, Sg⁆ : Subgroup X).subgroupOf K) :=
      isMulCommutative_anti hle_center
    have hprime : (Nat.card ((⁅Sg, Sg⁆ : Subgroup X).subgroupOf K)).Prime :=
      (Group.is_simple_iff_prime_card).mp hsimple
    have hcard : Nat.card ((⁅Sg, Sg⁆ : Subgroup X).subgroupOf K) = 20160 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv, hS.card_commutator_sg]
    rw [hcard] at hprime
    have hnot : ¬ Nat.Prime 20160 := by
      intro hp
      rcases hp.eq_one_or_self_of_dvd 2 (by norm_num : 2 ∣ 20160) with h' | h' <;> omega
    exact hnot hprime

theorem injOn_toPerm_commutator (hS : SwapShape t Sg V) (hA : ⁅Sg, Sg⁆ ≤ K) {m : ℕ}
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin m)) :
    Set.InjOn (toPerm e) ((⁅Sg, Sg⁆ : Subgroup X).subgroupOf K : Set K) := by
  rw [Set.injOn_iff_injective]
  exact resAbar_injective hS hA e

theorem card_imageAbar (hS : SwapShape t Sg V) (hA : ⁅Sg, Sg⁆ ≤ K) {m : ℕ}
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin m)) :
    Nat.card (imageAbar Sg K e) = 20160 := by
  have hrinj := resAbar_injective (Sg := Sg) (K := K) hS hA e
  have hcard : Nat.card ((⁅Sg, Sg⁆ : Subgroup X).subgroupOf K) =
      Nat.card (resAbar (Sg := Sg) (K := K) e).range :=
    Nat.card_congr (MonoidHom.ofInjective hrinj).toEquiv
  rw [← resAbar_range (Sg := Sg) (K := K) e, ← hcard,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv, hS.card_commutator_sg]

theorem isSimpleGroup_imageAbar (hS : SwapShape t Sg V) (hA : ⁅Sg, Sg⁆ ≤ K) {m : ℕ}
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin m)) :
    IsSimpleGroup (imageAbar Sg K e) := by
  have hrinj := resAbar_injective (Sg := Sg) (K := K) hS hA e
  haveI hA_simple : IsSimpleGroup (⁅Sg, Sg⁆ : Subgroup X) := hS.isSimpleGroup_commutator_sg
  haveI hsimple : IsSimpleGroup ((⁅Sg, Sg⁆ : Subgroup X).subgroupOf K) :=
    (Subgroup.subgroupOfEquivOfLe hA).isSimpleGroup
  rw [← resAbar_range (Sg := Sg) (K := K) e]
  exact (MonoidHom.ofInjective hrinj).symm.isSimpleGroup

theorem eight_le (hS : SwapShape t Sg V) (hA : ⁅Sg, Sg⁆ ≤ K) {m : ℕ}
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin m)) : 8 ≤ m := by
  have hcard : Nat.card (imageAbar Sg K e) ≤ Nat.card (Perm (Fin m)) := by
    have h := Subgroup.card_le_of_le (K := (⊤ : Subgroup (Perm (Fin m)))) (le_top :
      imageAbar Sg K e ≤ ⊤)
    rwa [Subgroup.card_top] at h
  rw [card_imageAbar hS hA e, Nat.card_perm, Nat.card_fin] at hcard
  by_contra h
  have hm : m ≤ 7 := by omega
  have h7 : Nat.factorial 7 = 5040 := by norm_num [Nat.factorial]
  have : Nat.factorial m ≤ 5040 := by simpa [h7] using Nat.factorial_le hm
  omega

theorem imageAbar_le [K.Normal] (hS : SwapShape t Sg V) {m : ℕ}
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin m)) {π : Perm (Fin m)}
    (hπ : ∀ k : K, toPerm e (MulAut.conjNormal t k) = π * toPerm e k * π⁻¹) :
    imageAbar Sg K e ≤ alternatingGroup (Fin m) ⊓ centralizer ({π} : Set (Perm (Fin m))) := by
  refine le_inf ?_ ?_
  · intro g hg
    rw [imageAbar] at hg
    obtain ⟨k, -, rfl⟩ := Subgroup.mem_map.mp hg
    rw [← range_toPerm (e := e)]
    exact MonoidHom.mem_range.mpr ⟨k, rfl⟩
  · intro g hg
    rw [imageAbar] at hg
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hkC : (k : X) ∈ centralizer ({t} : Set X) :=
      hS.commutator_sg_le_centralizer hk
    have htk : t * (k : X) = (k : X) * t :=
      (Subgroup.mem_centralizer_singleton_iff.mp hkC).symm
    have hconj : MulAut.conjNormal t k = k := by
      ext
      rw [MulAut.conjNormal_apply, htk, mul_assoc, mul_inv_cancel, mul_one]
    have hthis := hπ k
    rw [hconj] at hthis
    conv_lhs => rw [hthis]
    rw [mul_assoc, inv_mul_cancel, mul_one]

theorem pi_ne_one [K.Normal] (hS : SwapShape t Sg V) (hK : ⁅K, K⁆ = K) (hne : ⁅Sg, Sg⁆ ≠ K)
    (hA : ⁅Sg, Sg⁆ ≤ K) {m : ℕ} (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin m))
    {π : Perm (Fin m)}
    (hπ : ∀ k : K, toPerm e (MulAut.conjNormal t k) = π * toPerm e k * π⁻¹) : π ≠ 1 := by
  intro hπ1
  have hq : ∀ k : K, toPerm e (MulAut.conjNormal t k) = toPerm e k := by
    intro k
    rw [hπ k, hπ1]
    simp
  have hker : (toPerm e).ker ≤ Subgroup.center K := by
    rw [ker_toPerm]
  have hKC : K ≤ centralizer ({t} : Set X) :=
    le_centralizer_of_perfect hK (toPerm e) hker hq
  have h1 : ⁅K, K⁆ ≤ ⁅Sg, Sg⁆ := by
    have hmono : ⁅K, K⁆ ≤ ⁅centralizer ({t} : Set X), centralizer ({t} : Set X)⁆ :=
      Subgroup.commutator_mono hKC hKC
    exact hmono.trans hS.commutator_centralizer_le
  rw [hK] at h1
  exact hne (le_antisymm hA h1)

theorem card_alt_inf_centralizer_le [K.Normal] (hS : SwapShape t Sg V) {m : ℕ}
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin m)) {π : Perm (Fin m)}
    (hπ : ∀ k : K, toPerm e (MulAut.conjNormal t k) = π * toPerm e k * π⁻¹) :
    Nat.card (alternatingGroup (Fin m) ⊓ centralizer ({π} : Set (Perm (Fin m))) :
      Subgroup (Perm (Fin m))) ≤ 161280 := by
  have hker : (toPerm e).ker ≤ Subgroup.center K := by
    rw [ker_toPerm]
  have h := card_range_inf_centralizer_le (toPerm e) hker π hπ
  rw [range_toPerm] at h
  refine h.trans ?_
  calc Nat.card (K ⊓ centralizer ({t} : Set X) : Subgroup X)
      ≤ Nat.card (centralizer ({t} : Set X)) := Subgroup.card_le_of_le inf_le_right
    _ = 161280 := hS.card_centralizer

theorem exists_commuting_lifts (hS : SwapShape t Sg V) (hA : ⁅Sg, Sg⁆ ≤ K) {m : ℕ}
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin m)) {g₁ g₂ : Perm (Fin m)}
    (h₁ : g₁ ∈ imageAbar Sg K e) (h₂ : g₂ ∈ imageAbar Sg K e) (hc : g₁ * g₂ = g₂ * g₁) :
    ∃ x y : K, toPerm e x = g₁ ∧ toPerm e y = g₂ ∧ x * y = y * x := by
  rw [imageAbar] at h₁ h₂
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp h₁
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp h₂
  refine ⟨x, y, rfl, rfl, ?_⟩
  have hinj := injOn_toPerm_commutator (Sg := Sg) (K := K) hS hA e
  apply hinj (mul_mem hx hy) (mul_mem hy hx)
  rw [map_mul, map_mul, hc]

end CFSG.OddStandard.AltStdSec.SwapPartner
