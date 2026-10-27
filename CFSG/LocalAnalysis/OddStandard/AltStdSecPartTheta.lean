module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecPartBasic
public import CFSG.LocalAnalysis.OddStandard.AltStdSecHerCop
public import CFSG.LocalAnalysis.OddStandard.AltStdSecPermSec

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv CFSG.OddStandard.AltStdBal

section Kappa

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z u : G}

@[expose] noncomputable def swapIota (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) : Perm (Fin n) ≃* ↥(L ⊔ zpowers u) :=
  (MulEquiv.ofBijective (rhoSwap h d T.cent e)
    (rhoSwap_bijective h d T.card T.cent T.outer T.sq e)).symm

theorem rhoSwap_swapIota (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) (σ : Perm (Fin n)) :
    rhoSwap h d T.cent e (swapIota h d T e σ) = σ :=
  (MulEquiv.ofBijective (rhoSwap h d T.cent e)
    (rhoSwap_bijective h d T.card T.cent T.outer T.sq e)).apply_symm_apply σ

theorem swapIota_mem_centralizer (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) (σ : Perm (Fin n)) :
    ((swapIota h d T e σ : ↥(L ⊔ zpowers u)) : G) ∈ centralizer ({z} : Set G) :=
  (sup_le (le_centralizer_single h d) (zpowers_le.2 T.cent)) (swapIota h d T e σ).2

theorem permOf_swapIota (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) (σ : Perm (Fin n)) :
    permOf h d e (swapIota_mem_centralizer h d T e σ) = σ := by
  have := rhoSwap_swapIota h d T e σ
  rw [rhoSwap_apply] at this
  exact this

@[expose] noncomputable def kappa (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) (S : Finset (Fin n)) : Perm ↥Sᶜ →* G :=
  (L ⊔ zpowers u).subtype.comp
    ((swapIota h d T e).toMonoidHom.comp (Perm.ofSubtype : Perm ↥Sᶜ →* Perm (Fin n)))

theorem kappa_apply (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) (S : Finset (Fin n)) (π : Perm ↥Sᶜ) :
    kappa h d T e S π = ((swapIota h d T e (Perm.ofSubtype π) : ↥(L ⊔ zpowers u)) : G) := rfl

theorem kappa_mem_centralizer (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) (S : Finset (Fin n)) (π : Perm ↥Sᶜ) :
    kappa h d T e S π ∈ centralizer ({z} : Set G) :=
  swapIota_mem_centralizer h d T e _

theorem permOf_kappa (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) (S : Finset (Fin n)) (π : Perm ↥Sᶜ) :
    permOf h d e (kappa_mem_centralizer h d T e S π) = Perm.ofSubtype π :=
  permOf_swapIota h d T e _

theorem kappa_injective (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) (S : Finset (Fin n)) :
    Function.Injective (kappa h d T e S) := by
  intro π₁ π₂ h12
  have h1 : swapIota h d T e (Perm.ofSubtype π₁) = swapIota h d T e (Perm.ofSubtype π₂) :=
    Subtype.ext h12
  exact Perm.ofSubtype_injective ((swapIota h d T e).injective h1)

theorem kappa_mem_centralizer_root (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) (S : Finset (Fin n)) (π : Perm ↥Sᶜ) :
    kappa h d T e S π ∈ centralizer (corr (X := G) e (altSub S) : Set G) := by
  rw [mem_centralizer_iff]
  intro r hr
  refine (comm_of_mem_corr_of_permOf_fix h d e (kappa_mem_centralizer h d T e S π)
    (F := S) (fun i hi => ?_) hr).symm
  rw [permOf_kappa]
  exact Perm.ofSubtype_apply_of_not_mem π (by simpa using hi)

end Kappa

section Theta

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z u : G}

@[expose] noncomputable def thetaHom (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) (S : Finset (Fin n)) :
    Perm ↥Sᶜ →* Sec G (corr (X := G) e (altSub S)) :=
  (QuotientGroup.mk' (CFSG.oddCore ↥(centralizer (corr (X := G) e (altSub S) : Set G)))).comp
    ((kappa h d T e S).codRestrict (centralizer (corr (X := G) e (altSub S) : Set G))
      (kappa_mem_centralizer_root h d T e S))

theorem thetaHom_apply (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) (S : Finset (Fin n)) (π : Perm ↥Sᶜ) :
    thetaHom h d T e S π =
      (QuotientGroup.mk ⟨kappa h d T e S π, kappa_mem_centralizer_root h d T e S π⟩ :
        Sec G (corr (X := G) e (altSub S))) := rfl

theorem oddCore_inf_corr_compl (e : L ≃* alternatingGroup (Fin n)) {S : Finset (Fin n)}
    (hSc : 5 ≤ Sᶜ.card) (x : ↥(centralizer (corr (X := G) e (altSub S) : Set G)))
    (hx : (x : G) ∈ corr (X := G) e (altSub Sᶜ))
    (hO : x ∈ CFSG.oddCore ↥(centralizer (corr (X := G) e (altSub S) : Set G))) : x = 1 := by
  have hBA : corr (X := G) e (altSub Sᶜ) ≤ L ⊓ centralizer (corr (X := G) e (altSub S) : Set G) :=
    corr_le_centralizer_corr (X := G) e
      (fun g hg g' hg' => comm_of_altSub_disjoint disjoint_compl_right hg hg')
  have hBC : corr (X := G) e (altSub Sᶜ) ≤ centralizer (corr (X := G) e (altSub S) : Set G) :=
    fun b hb => (hBA hb).2
  obtain ⟨eB⟩ := exists_equiv_corr_altSub (X := G) e Sᶜ
  let eB' : (corr (X := G) e (altSub Sᶜ)).subgroupOf
      (centralizer (corr (X := G) e (altSub S) : Set G)) ≃* alternatingGroup (Fin Sᶜ.card) :=
    (Subgroup.subgroupOfEquivOfLe hBC).trans eB
  have hbot := inf_oddCore_eq_bot_of_alt hSc eB'
  have hmem : x ∈ (corr (X := G) e (altSub Sᶜ)).subgroupOf
      (centralizer (corr (X := G) e (altSub S) : Set G)) ⊓
      CFSG.oddCore ↥(centralizer (corr (X := G) e (altSub S) : Set G)) := Subgroup.mem_inf.2 ⟨hx, hO⟩
  rw [hbot] at hmem
  exact hmem

theorem kappa_sq_mem_corr (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) (S : Finset (Fin n)) (π : Perm ↥Sᶜ) :
    kappa h d T e S π * kappa h d T e S π ∈ corr (X := G) e (altSub Sᶜ) := by
  have hC := kappa_mem_centralizer h d T e S π
  have hL : kappa h d T e S π * kappa h d T e S π ∈ L := T.sq_mem h d hC
  refine mem_corr.2 ⟨hL, ?_⟩
  have h1 := permOf_of_mem h d e (mul_mem hC hC) hL
  rw [permOf_mul h d e hC hC (mul_mem hC hC), permOf_kappa] at h1
  rw [← h1]
  refine mem_altSub.2 ⟨?_, fun i hi => ?_⟩
  · rw [Perm.sign_mul, Int.units_mul_self]
  · have hiS : i ∈ S := by simpa using hi
    have : Perm.ofSubtype π i = i := Perm.ofSubtype_apply_of_not_mem π (by simpa using hiS)
    simp [Perm.mul_apply, this]

theorem thetaHom_injective (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) {S : Finset (Fin n)} (hSc : 5 ≤ Sᶜ.card) :
    Function.Injective (thetaHom h d T e S) := by
  rw [injective_iff_map_eq_one]
  intro π hπ
  rw [thetaHom_apply] at hπ
  have hO := (QuotientGroup.eq_one_iff _).1 hπ
  have hC := kappa_mem_centralizer h d T e S π
  have hCR := kappa_mem_centralizer_root h d T e S π
  have hsqO : (⟨kappa h d T e S π, hCR⟩ : ↥(centralizer (corr (X := G) e (altSub S) : Set G))) *
      ⟨kappa h d T e S π, hCR⟩ ∈ CFSG.oddCore ↥(centralizer (corr (X := G) e (altSub S) : Set G)) :=
    mul_mem hO hO
  have hsq1 := oddCore_inf_corr_compl e hSc _ (kappa_sq_mem_corr h d T e S π) hsqO
  have hsq : kappa h d T e S π * kappa h d T e S π = 1 := congrArg Subtype.val hsq1
  have hodd : Odd (orderOf (kappa h d T e S π)) := by
    have := orderOf_odd_of_mem_oddCore hO
    rwa [Subgroup.orderOf_mk] at this
  have hdvd : orderOf (kappa h d T e S π) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
  have h1 : orderOf (kappa h d T e S π) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
    · exact h1
    · rw [h2] at hodd; exact absurd hodd (by decide)
  have h2 : kappa h d T e S π = 1 := orderOf_eq_one_iff.1 h1
  exact kappa_injective h d T e S (by rw [h2, map_one])

theorem thetaHom_ne_z (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) (S : Finset (Fin n))
    (hz : z ∈ centralizer (corr (X := G) e (altSub S) : Set G)) (π : Perm ↥Sᶜ) :
    thetaHom h d T e S π ≠ (QuotientGroup.mk ⟨z, hz⟩ : Sec G (corr (X := G) e (altSub S))) := by
  intro hπ
  rw [thetaHom_apply, QuotientGroup.eq] at hπ
  have hodd0 := orderOf_odd_of_mem_oddCore hπ
  rw [Subgroup.orderOf_mk] at hodd0
  set x := kappa h d T e S π with hx
  have hxz : x * z = z * x := mem_centralizer_singleton_iff.1 (kappa_mem_centralizer h d T e S π)
  have hz2 : z * z = 1 := d.mul_self
  have hz1 : z ≠ 1 := fun h1 => by simpa [h1] using d.order
  obtain ⟨r, hr⟩ := hodd0
  have hpow : (x⁻¹ * z) ^ (2 * r + 1) = 1 := by
    rw [← hr]; exact pow_orderOf_eq_one _
  have hcomm : Commute x⁻¹ z := (Commute.inv_left (show Commute x z from hxz))
  have hzpow : z ^ (2 * r + 1) = z := by
    rw [pow_succ, pow_mul, pow_two, hz2, one_pow, one_mul]
  rw [hcomm.mul_pow, hzpow, inv_pow] at hpow
  have hzx : z = x ^ (2 * r + 1) := by
    have := inv_mul_eq_one.1 hpow
    exact this.symm
  have hzS : z ∈ L ⊔ zpowers u := by
    rw [hzx]
    exact pow_mem (swapIota h d T e (Perm.ofSubtype π)).2 _
  exact z_notMem_swapComplement h d T.cent T.outer T.sq hzS

end Theta

end CFSG.OddStandard.AltStdSec
