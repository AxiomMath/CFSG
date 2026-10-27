module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.U6Local
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.U6Model

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Dickson.I271 Bal209F4Aux

namespace E6LocalAux

section Arith

theorem sq_mem_of_pow_mem_of_hom {G R : Type*} [Group G] [Group R] (u : G →* R) {I : Subgroup G}
    (hI : I ≤ u.ker) (hR : ∀ r : R, r ^ 6 = 1) (hN : ∀ g ∈ u.ker, g ^ 3 ∈ I) {m : ℕ}
    (hm : Nat.Coprime 3 m) {g : G} (hg : g ^ m ∈ I) : g ^ 2 ∈ I := by
  have h1 : (u g) ^ m = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.1 (hI hg)
  have h2 : orderOf (u g) ∣ m := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf (u g) ∣ 2 * 3 := orderOf_dvd_of_pow_eq_one (hR (u g))
  have h4 : Nat.Coprime (orderOf (u g)) 3 := Nat.Coprime.coprime_dvd_left h2 hm.symm
  have h5 : orderOf (u g) ∣ 2 := h4.dvd_of_dvd_mul_right h3
  have h6 : (u g) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 h5
  have h7 : g ^ 2 ∈ u.ker := by rw [MonoidHom.mem_ker, map_pow, h6]
  have h8 : (g ^ 2) ^ 3 ∈ I := hN _ h7
  have h9 : (g ^ 2) ^ m ∈ I := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact I.pow_mem hg 2
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * 3 + b * m = 1 := Nat.isCoprime_iff_coprime.2 hm
  have h10 : g ^ 2 = ((g ^ 2) ^ 3) ^ a * ((g ^ 2) ^ m) ^ b := by
    rw [← zpow_natCast (g ^ 2) 3, ← zpow_natCast (g ^ 2) m, ← zpow_mul, ← zpow_mul, ← zpow_add]
    have : (3 : ℤ) * a + m * b = 1 := by linarith
    rw [show ((3 : ℕ) : ℤ) * a + (m : ℤ) * b = 1 by simpa using this, zpow_one]
  rw [h10]
  exact I.mul_mem (I.zpow_mem h8 a) (I.zpow_mem h9 b)

end Arith

section Transport

theorem coreBot_of_map {p : ℕ} {Y S : Type*} [Group Y] [Group S] (ψ : MulAut Y →* MulAut S)
    (hψ : Function.Injective ψ) (hinn : innerAut S ≤ (innerAut Y).map ψ) {d : MulAut Y}
    (h : ∀ H' : Subgroup (MulAut S), innerAut S ≤ H' →
      GLAPPrimeCoreOf p (H' ⊓ Subgroup.centralizer ({ψ d} : Set (MulAut S))) = ⊥)
    {H : Subgroup (MulAut Y)} (hH : innerAut Y ≤ H) :
    GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({d} : Set (MulAut Y))) = ⊥ := by
  have h0 := h (H.map ψ) (hinn.trans (Subgroup.map_mono hH))
  rw [← map_inf_centralizer_of_injective ψ hψ, ← map_glaPPrimeCoreOf_of_injective p ψ hψ] at h0
  exact (Subgroup.map_eq_bot_iff_of_injective _ hψ).1 h0

variable {X : Type} [Group X] {K : Subgroup X}

noncomputable def barToS (hperf : commutator ↥K = ⊤)
    (hN : GLAPPrimeCore 3 ↥K ≤ Subgroup.center ↥K) :
    MulAut (barOf 3 K) →* MulAut (↥K ⧸ Subgroup.center ↥K) :=
  (MulAut.congr (U6LocalAux.centerQuotEquiv hperf hN)).toMonoidHom.comp
    (autCenterQuot (barOf 3 K))

theorem barToS_injective (hperf : commutator ↥K = ⊤)
    (hN : GLAPPrimeCore 3 ↥K ≤ Subgroup.center ↥K) : Function.Injective (barToS hperf hN) := by
  have hperfY : commutator (barOf 3 K) = ⊤ :=
    U6LocalAux.commutator_quotient_eq_top hperf (GLAPPrimeCore 3 ↥K)
  exact (MulAut.congr (U6LocalAux.centerQuotEquiv hperf hN)).injective.comp
    (autCenterQuot_injective_of_perfect hperfY)

theorem barToS_barAut (hperf : commutator ↥K = ⊤) (hN : GLAPPrimeCore 3 ↥K ≤ Subgroup.center ↥K)
    (γ : ↥(Subgroup.normalizer (K : Set X))) :
    barToS hperf hN (barAut 3 K γ) = actHom K γ :=
  U6LocalAux.congr_centerQuotEquiv_barAut hperf hN γ

theorem innerAut_le_map_barToS (hperf : commutator ↥K = ⊤)
    (hN : GLAPPrimeCore 3 ↥K ≤ Subgroup.center ↥K) :
    innerAut (↥K ⧸ Subgroup.center ↥K) ≤ (innerAut (barOf 3 K)).map (barToS hperf hN) := by
  rintro _ ⟨s, rfl⟩
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective s
  refine ⟨MulAut.conj (QuotientGroup.mk k : barOf 3 K), ⟨_, rfl⟩, ?_⟩
  change MulAut.congr (U6LocalAux.centerQuotEquiv hperf hN)
      (autCenterQuot (barOf 3 K) (MulAut.conj (QuotientGroup.mk k : barOf 3 K))) =
    MulAut.conj (QuotientGroup.mk k : ↥K ⧸ Subgroup.center ↥K)
  rw [Bal209TwoInnerAux.autCenterQuot_conj, congr_conj']
  rfl

end Transport

section Inner

variable {X : Type} [Group X]

theorem centralizer_eq_of_mem_zpowers {z s : X} (hz : orderOf z = 3) (hs : s ∈ Subgroup.zpowers z)
    (hs1 : s ≠ 1) :
    Subgroup.centralizer ({s} : Set X) = Subgroup.centralizer ({z} : Set X) := by
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
  have hz3 : z ^ 3 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    omega
  have hj : ¬ (3 : ℤ) ∣ j := by
    rintro ⟨k, rfl⟩
    apply hs1
    have hz3z : z ^ (3 : ℤ) = 1 := by simpa using hz3
    rw [zpow_mul, hz3z, one_zpow]
  ext t
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have hmem : z ^ j ∈ Subgroup.centralizer ({t} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact h.symm
    have := mem_of_zpow_mem (H := Subgroup.centralizer ({t} : Set X)) hz3 hz1 hj hmem
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this.symm
  · intro h
    exact (Commute.zpow_right (show Commute t z from h) j).eq

theorem mem_zpowers_of_inner_mem_pairSub {K : Subgroup X} {x y : X} (hxy : Commute x y)
    (hx3 : x ^ 3 = 1) (hxI : x ∉ innerSub K) (hyI : y ∈ innerSub K) {a : X}
    (ha : a ∈ pairSub hxy) (hain : a ∈ innerSub K) : a ∈ Subgroup.zpowers y := by
  obtain ⟨i, j, rfl⟩ := mem_pairSub.1 ha
  have hx1 : x ≠ 1 := fun h => hxI (h ▸ (innerSub K).one_mem)
  have hxi : x ^ i ∈ innerSub K := by
    have h2 : y ^ j ∈ innerSub K := (innerSub K).zpow_mem hyI j
    have h3 := (innerSub K).mul_mem hain ((innerSub K).inv_mem h2)
    simpa using h3
  have hi3 : (3 : ℤ) ∣ i := by
    by_contra hi
    exact hxI (mem_of_zpow_mem hx3 hx1 hi hxi)
  obtain ⟨k, rfl⟩ := hi3
  have hx3z : x ^ (3 : ℤ) = 1 := by simpa using hx3
  rw [zpow_mul, hx3z, one_zpow, one_mul]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers y) j

theorem sup_zpowers_eq_pairSub {x y : X} (hxy : Commute x y) :
    Subgroup.zpowers x ⊔ Subgroup.zpowers y = pairSub hxy := by
  apply le_antisymm
  · refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · exact mem_pairSub.2 ⟨1, 0, by simp⟩
    · exact mem_pairSub.2 ⟨0, 1, by simp⟩
  · rintro _ ⟨i, j, rfl⟩
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_left (Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) i))
      (Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.mem_zpowers y) j))

end Inner

end E6LocalAux

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
