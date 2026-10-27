module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3S7Step7Q
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S73U3

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ABGLocalTools
open scoped MatrixGroups commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {z : G} {L : Subgroup G}

theorem S7Config.mem_Q (h : S7Config G z L) :
    z ∈ centralizer ({z} : Set G) ⊓ coreActionKernel L := by
  have hN : z ∈ normalizer (L : Set G) := le_normalizer h.hzL
  have hzc : (QuotientGroup.mk (⟨z, h.hzL⟩ : ↥L) : Bar L) ∈ center (Bar L) :=
    mk_mem_center_of_mem_center (mem_center_of_le_centralizer h.hL.1 h.hzL)
  exact mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr rfl, (mem_ker_barAction L ⟨z, hN⟩).mp
    (MonoidHom.mem_ker.mpr (barAction_eq_one_of_mem_center (t := ⟨z, h.hzL⟩) hzc hN))⟩

theorem S7Config.pPrimeCore_le_Q (hI : S7Inputs) (h : S7Config G z L) :
    (pPrimeCore 2 ↥(centralizer ({z} : Set G))).map (centralizer {z}).subtype ≤
      centralizer {z} ⊓ coreActionKernel L := by
  have hLn := h.normal hI
  have hHN : centralizer ({z} : Set G) ≤ normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer h.hL.1).mp hLn
  intro o ho
  have hoH : o ∈ centralizer ({z} : Set G) := map_subtype_le _ ho
  refine mem_inf.mpr ⟨hoH, mem_coreActionKernel.mpr ⟨hHN hoH, fun j hj => ?_⟩⟩
  have hjH : j ∈ centralizer ({z} : Set G) := h.hL.1 hj
  have hcL : j⁻¹ * o⁻¹ * j * o ∈ L := by
    have h1 : o⁻¹ * j * o ∈ L := by
      have h2 := (mem_normalizer_iff.mp (hHN (inv_mem hoH)) j).mp hj
      rwa [inv_inv] at h2
    rw [show j⁻¹ * o⁻¹ * j * o = j⁻¹ * (o⁻¹ * j * o) by group]
    exact mul_mem (inv_mem hj) h1
  have hcO : j⁻¹ * o⁻¹ * j * o ∈ (pPrimeCore 2 ↥(centralizer ({z} : Set G))).map
      (centralizer {z}).subtype := by
    have h1 := conj_mem_pPrimeCore_map (inv_mem hjH) (inv_mem ho)
    rw [inv_inv] at h1
    exact mul_mem h1 ho
  exact ⟨⟨_, hcL⟩, mem_pPrimeCore_of_normal (fun m hm n hn => conj_mem_pPrimeCore_map
    (h.hL.1 hm) hn) (odd_card_pPrimeCore_map _) hcL hcO, rfl⟩

theorem S7Config.conj_mem_Q' (hI : S7Inputs) (h : S7Config G z L) {x : G}
    (hx : x ∈ centralizer ({z} : Set G)) {q : G}
    (hq : q ∈ centralizer ({z} : Set G) ⊓ coreActionKernel L) :
    x * q * x⁻¹ ∈ centralizer ({z} : Set G) ⊓ coreActionKernel L :=
  conj_mem_Q ((normal_subgroupOf_iff_le_normalizer h.hL.1).mp (h.normal hI)) hx hq

section Certified


theorem S7Config.inf_Q_eq (hI : S7Inputs) (h : S7Config G z L) {S : Subgroup G}
    (hS : IsSylowOf 2 S (centralizer {z})) :
    S ⊓ (centralizer {z} ⊓ coreActionKernel L) = zpowers z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzS : z ∈ S := IsSylowOf.mem_of_central hS (mem_centralizer_singleton_iff.mpr rfl)
    (fun k hk => mem_centralizer_singleton_iff.mp hk) (n := 1)
    (by rw [pow_one, ← h.hz, pow_orderOf_eq_one])
  refine (Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr (mem_inf.mpr ⟨hzS, h.mem_Q⟩)) ?_).symm
  rw [Nat.card_zpowers, h.hz]
  exact h.card_inf_Q_le_two hI hS

theorem S7Config.Q_eq (hI : S7Inputs) (h : S7Config G z L) :
    centralizer {z} ⊓ coreActionKernel L =
      (pPrimeCore 2 ↥(centralizer ({z} : Set G))).map (centralizer {z}).subtype ⊔ zpowers z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ (sup_le (h.pPrimeCore_le_Q hI) (zpowers_le.mpr h.mem_Q))
  set H := centralizer ({z} : Set G) with hH
  set Q := H ⊓ coreActionKernel L with hQ
  have hQn : ∀ x ∈ H, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q := fun x hx q hq => h.conj_mem_Q' hI hx hq
  obtain ⟨S, hS⟩ := exists_isSylowOf 2 H
  have hSQ : IsSylowOf 2 (S ⊓ Q) Q := hS.inf_of_le_normalizer inf_le_left (fun x hx =>
    mem_normalizer_iff.mpr fun q => ⟨fun hq => hQn x hx q hq, fun hq => by
      have h1 := hQn x⁻¹ (inv_mem hx) _ hq
      rwa [show x⁻¹ * (x * q * x⁻¹) * x⁻¹⁻¹ = q by group] at h1⟩)
  have hSQz : S ⊓ Q = zpowers z := h.inf_Q_eq hI hS
  obtain ⟨P, hP⟩ := hSQ.exists_sylow_eq_subgroupOf
  have hPc : Nat.card P = 2 := by
    have h1 : Nat.card ↥((P : Subgroup ↥Q).map Q.subtype) = Nat.card P :=
      Subgroup.card_map_of_injective Q.subtype_injective
    rw [← h1, hP, subgroupOf_map_subtype, inf_eq_left.mpr inf_le_right, hSQz, Nat.card_zpowers,
      h.hz]
  obtain ⟨-, hmul, -⟩ := cyclic_sylow_normal_odd_complement P (isCyclic_of_prime_card hPc)
  have hOQ : ∀ k ∈ (pPrimeCore 2 ↥Q).map Q.subtype, k ∈ (pPrimeCore 2 ↥H).map H.subtype := by
    intro k hk
    have hkH : k ∈ H := (mem_inf.mp (map_subtype_le _ hk)).1
    have hnorm : ∀ m ∈ H, ∀ n ∈ (pPrimeCore 2 ↥Q).map Q.subtype,
        m * n * m⁻¹ ∈ (pPrimeCore 2 ↥Q).map Q.subtype := fun m hm n hn =>
      conj_mem_pPrimeCore_map_of_map_eq (map_conj_eq_of_conj_mem (hQn m hm)
        (fun q hq => by
          have h1 := hQn m⁻¹ (inv_mem hm) q hq
          rwa [inv_inv] at h1)) hn
    exact ⟨⟨k, hkH⟩, mem_pPrimeCore_of_normal hnorm (odd_card_pPrimeCore_map Q) hkH hk, rfl⟩
  intro q hq
  have hu : (⟨q, hq⟩ : ↥Q) ∈ (pPrimeCore 2 ↥Q : Set ↥Q) * (P : Set ↥Q) := by
    rw [hmul]
    exact Set.mem_univ _
  obtain ⟨k, hk, s, hs, hks⟩ := Set.mem_mul.mp hu
  have hqks : (k : G) * (s : G) = q := congrArg Subtype.val hks
  have hsz : (s : G) ∈ zpowers z := by
    rw [← hSQz]
    have h1 : (s : G) ∈ (P : Subgroup ↥Q).map Q.subtype := ⟨s, hs, rfl⟩
    rwa [hP, subgroupOf_map_subtype, inf_eq_left.mpr inf_le_right] at h1
  rw [← hqks]
  exact mul_mem (mem_sup_left (hOQ _ ⟨k, hk, rfl⟩)) (mem_sup_right hsz)

theorem S7Config.commutator_le (hI : S7Inputs) (h : S7Config G z L) :
    ⁅centralizer ({z} : Set G), centralizer ({z} : Set G)⁆ ≤
      (pPrimeCore 2 ↥(centralizer ({z} : Set G))).map (centralizer {z}).subtype ⊔ L := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hLn := h.normal hI
  have hHN : centralizer ({z} : Set G) ≤ normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer h.hL.1).mp hLn
  obtain ⟨w, hw⟩ := harris82Lemma411U3Odd_holds (Bar L) 3 1 Nat.prime_three (by norm_num) h.hcov
    (barAction L ⟨x, hHN hx⟩) (barAction L ⟨y, hHN hy⟩)
  obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk_surjective w
  have hlN : l ∈ normalizer (L : Set G) := le_normalizer hl
  have h1 : barAction L ⟨l, hlN⟩ = MulAut.conj (QuotientGroup.mk ⟨l, hl⟩ : Bar L) :=
    barAction_of_mem L ⟨l, hl⟩ hlN
  have hcN : ⁅x, y⁆ * l⁻¹ ∈ normalizer (L : Set G) := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem (mul_mem (hHN hx) (hHN hy)) (inv_mem (hHN hx)))
      (inv_mem (hHN hy))) (inv_mem hlN)
  have h2 : barAction L ⟨⁅x, y⁆ * l⁻¹, hcN⟩ = 1 := by
    have h3 : (⟨⁅x, y⁆ * l⁻¹, hcN⟩ : ↥(normalizer (L : Set G))) =
        ⟨x, hHN hx⟩ * ⟨y, hHN hy⟩ * (⟨x, hHN hx⟩)⁻¹ * (⟨y, hHN hy⟩)⁻¹ * (⟨l, hlN⟩)⁻¹ :=
      Subtype.ext (by
        change ⁅x, y⁆ * l⁻¹ = x * y * x⁻¹ * y⁻¹ * l⁻¹
        rw [commutatorElement_def])
    rw [h3, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, map_inv, hw, h1,
      mul_inv_cancel]
  have hcK : ⁅x, y⁆ * l⁻¹ ∈ coreActionKernel L :=
    (mem_ker_barAction L _).mp (MonoidHom.mem_ker.mpr h2)
  have hcH : ⁅x, y⁆ * l⁻¹ ∈ centralizer ({z} : Set G) := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy))
      (inv_mem (h.hL.1 hl))
  have hcQ := (h.Q_eq hI) ▸ mem_inf.mpr ⟨hcH, hcK⟩
  have hle : (pPrimeCore 2 ↥(centralizer ({z} : Set G))).map (centralizer {z}).subtype ⊔
      zpowers z ≤ (pPrimeCore 2 ↥(centralizer ({z} : Set G))).map (centralizer {z}).subtype ⊔ L :=
    sup_le_sup_left (zpowers_le.mpr h.hzL) _
  have h4 := mul_mem (hle hcQ) (mem_sup_right hl)
  rwa [inv_mul_cancel_right] at h4

theorem S7Config.inv_mul_conj_mem (hI : S7Inputs) (h : S7Config G z L) {S : Subgroup G}
    (hSH : S ≤ centralizer {z}) (hS : IsPGroup 2 S) {x k : G} (hx : x ∈ S)
    (hk : k ∈ centralizer ({z} : Set G)) (hkx : k * x * k⁻¹ ∈ S) : x⁻¹ * (k * x * k⁻¹) ∈ L := by
  have hLn := h.normal hI
  have hxH : x⁻¹ ∈ centralizer ({z} : Set G) := inv_mem (hSH hx)
  have hc := Subgroup.commutator_mem_commutator hxH hk
  have hc' : x⁻¹ * (k * x * k⁻¹) ∈
      (pPrimeCore 2 ↥(centralizer ({z} : Set G))).map (centralizer {z}).subtype ⊔ L := by
    have h1 := h.commutator_le hI hc
    rwa [commutatorElement_def, inv_inv, show x⁻¹ * k * x * k⁻¹ = x⁻¹ * (k * x * k⁻¹) by
      group] at h1
  have hS' : x⁻¹ * (k * x * k⁻¹) ∈ S := mul_mem (inv_mem hx) hkx
  obtain ⟨n, hn⟩ := hS ⟨_, hS'⟩
  have hn' : (x⁻¹ * (k * x * k⁻¹)) ^ 2 ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  exact mem_of_mem_sup_of_two_pow h.hL.1 hc' hn'

end Certified

end CFSG.ComponentClassification.HarrisLit.T1
