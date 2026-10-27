module

public import CFSG.ClassicalInvolution.AschTight.T6AMuB

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.T6A

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] [Finite G] {K : Subgroup G} {z : G}

theorem isSemidihedral_sup_of_allTypeTwo (ht : Setup194 p f K z) (hA : AllTypeTwo K z)
    {R : Subgroup G} (hR : R ∈ RSet (CoreAssembly.conjClass K)) (hRK : R ≤ K) {g : G}
    (htN : g * z * g⁻¹ ∈ Subgroup.normalizer (R : Set G))
    (htzc : g * z * g⁻¹ * z = z * (g * z * g⁻¹)) (htz : g * z * g⁻¹ ≠ z) :
    IsSemidihedral (R ⊔ Subgroup.zpowers (g * z * g⁻¹)) := by
  have hI := ht.isUniqueInvolution
  have hU := ht.uniqueInvolutionNormal
  set t := g * z * g⁻¹ with htdef
  have ht2 : t * t = 1 := by
    calc t * t = g * (z * z) * g⁻¹ := by rw [htdef]; group
      _ = 1 := by rw [hI.sq]; group
  have ht1 : t ≠ 1 := fun h1 => hI.ne_one (by
    have : z = g⁻¹ * t * g := by rw [htdef]; group
    rw [this, h1]; group)
  have hord : orderOf t = 2 := orderOf_eq_prime (by rw [_root_.sq]; exact ht2) ht1
  have htR : t ∉ R := fun h1 => htz (hU.2.2.1 t (hRK h1) hord)
  have hR2 : IsPGroup 2 R := isPGroup_of_mem_rSet hR
  have hzt : ∀ y ∈ Subgroup.zpowers t, y = 1 ∨ y = t := fun y hy =>
    eq_one_or_eq_of_mem_zpowers_of_mul_self ht2 hy
  have hCRt : ¬ 4 ≤ Nat.card ↥(R ⊓ Subgroup.centralizer ({t} : Set G)) := by
    have := hA K (CoreAssembly.mem_conjClass_self K) z t hI ⟨g, rfl⟩ htz htzc
      (R ⊓ Subgroup.centralizer ({t} : Set G)) (hR2.to_le inf_le_left) (inf_le_left.trans hRK)
      inf_le_right
    omega
  have hcfg : AscL62.CoreCfg R (Subgroup.zpowers t) z t :=
    { quat := isQuatSub_of_mem_rSet ht.odd ht.five ht.member hR
      hz := ht.isUniqueInvolution_of_mem_rSet_of_le hR hRK
      V2 := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, pow_one]; exact hord)
      norm := fun y hy => conjSub_eq_of_mem_normalizer (Subgroup.zpowers_le.mpr htN hy)
      inter := fun y hy hyR => (hzt y hy).resolve_right fun h1 => htR (h1 ▸ hyR)
      ht := ⟨Subgroup.mem_zpowers t, ht1, ht2, fun y hy _ => hzt y hy⟩ }
  exact (hcfg.eq_zpowers_and_isSemidihedral hCRt).2

theorem mem_sup_of_conj_mem (ht : Setup194 p f K z) (hA : AllTypeTwo K z)
    {R : Subgroup G} (hR : R ∈ RSet (CoreAssembly.conjClass K)) (hRK : R ≤ K) {S : Sylow 2 G}
    (hRS : R ≤ (S : Subgroup G)) (hSKR : (S : Subgroup G) ⊓ K ≤ R)
    (hSN : (S : Subgroup G) ≤ Subgroup.normalizer (R : Set G))
    (hSz : (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G)) {g : G}
    (htS : g * z * g⁻¹ ∈ (S : Subgroup G)) (htz : g * z * g⁻¹ ≠ z) {x : G}
    (hxP : x ∈ R ⊔ Subgroup.zpowers (g * z * g⁻¹)) {y : G}
    (hyx : y * x * y⁻¹ ∈ (S : Subgroup G)) :
    y * x * y⁻¹ ∈ R ⊔ Subgroup.zpowers (g * z * g⁻¹) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hI := ht.isUniqueInvolution
  have hcl : ∀ h : G, h * z * h⁻¹ ∈ (S : Subgroup G) →
      h * z * h⁻¹ ∈ R ⊔ Subgroup.zpowers (g * z * g⁻¹) := fun h hh =>
    mem_sup_of_allTypeTwo ht hA hR hRK S.isPGroup' hRS hSN hSz htS htz hh
  have hzR : IsUniqueInvolution R z := ht.isUniqueInvolution_of_mem_rSet_of_le hR hRK
  have hR2 : IsPGroup 2 R := isPGroup_of_mem_rSet hR
  have hRnc := (exists_ne_comm_of_mem_rSet ht.odd ht.five ht.member hR).1
  set t := g * z * g⁻¹ with htdef
  have ht2 : t * t = 1 := by
    calc t * t = g * (z * z) * g⁻¹ := by rw [htdef]; group
      _ = 1 := by rw [hI.sq]; group
  have htzc : t * z = z * t := Subgroup.mem_centralizer_singleton_iff.mp (hSz htS)
  have hU := ht.uniqueInvolutionNormal
  have htR : t ∉ R := fun h1 => htz (hU.2.2.1 t (hRK h1)
    (orderOf_eq_prime (by rw [_root_.sq]; exact ht2) fun h2 => hI.ne_one (by
      have : z = g⁻¹ * t * g := by rw [htdef]; group
      rw [this, h2]; group)))
  have hsd := isSemidihedral_sup_of_allTypeTwo ht hA hR hRK (hSN htS) htzc htz
  have hPS : R ⊔ Subgroup.zpowers t ≤ (S : Subgroup G) :=
    sup_le hRS (Subgroup.zpowers_le.mpr htS)
  obtain ⟨a, b, M, hsdd⟩ := exists_sdData (S.isPGroup'.to_le hPS) hsd
  have hM := hsdd.M_pos
  have ha2 : a * a ∈ R := mul_self_mem_of_mem_sup_zpowers ht2 (hSN htS) hsdd.a_mem
  have hza : z = a ^ (4 * (M : ℤ)) := by
    have h4 : a ^ (4 * (M : ℤ)) ∈ R := by
      rw [show 4 * (M : ℤ) = 2 * (2 * M) by ring, zpow_mul, zpow_two]
      exact R.zpow_mem ha2 _
    refine ((hzR.unique _ h4 ?_).resolve_left ?_).symm
    · rw [← zpow_add, hsdd.zpow_eq_one_iff]; exact ⟨1, by ring⟩
    · rw [hsdd.zpow_eq_one_iff]
      rintro ⟨c, hc⟩
      have : (M : ℤ) * (4 - 8 * c) = 0 := by linarith
      rcases mul_eq_zero.mp this with h0 | h0 <;> omega
  by_cases hx1 : x = 1
  · rw [hx1, mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  by_cases hx2 : x * x = 1
  ·
    by_cases hxR : x ∈ R
    · have hxz : x = z := (hzR.unique x hxR hx2).resolve_left hx1
      rw [hxz]
      exact hcl y (by rw [← hxz]; exact hyx)
    · obtain ⟨-, q, -, hq⟩ := conj_of_not_mem_of_isSemidihedral hR2 hzR hRnc ht2 htR (hSN htS)
        hsd hxP hxR (Or.inl hx2)
      have e : y * x * y⁻¹ = (y * q * g) * z * (y * q * g)⁻¹ := by
        rw [← hq, htdef]; group
      rw [e]
      exact hcl _ (by rw [← e]; exact hyx)
  ·
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp (S.isPGroup'.to_le hPS)) ⟨x, hxP⟩
    rw [Subgroup.orderOf_mk] at hj
    have hj2 : 2 ≤ j := by
      by_contra hj2
      apply hx2
      rw [← _root_.sq]
      have : orderOf x ∣ 2 := by
        rw [hj]
        exact (pow_dvd_pow 2 (by omega : j ≤ 1)).trans (by rw [pow_one])
      exact orderOf_dvd_iff_pow_eq_one.mp this
    obtain ⟨x₀, hx₀⟩ : ∃ x₀ : G, x ^ (2 ^ (j - 2)) = x₀ := ⟨_, rfl⟩
    have hx₀P : x₀ ∈ R ⊔ Subgroup.zpowers t := hx₀ ▸ Subgroup.pow_mem _ hxP _
    have hx₀2 : x₀ * x₀ = x ^ (2 ^ (j - 1)) := by
      rw [← hx₀, ← pow_add, ← two_mul, ← pow_succ', show j - 2 + 1 = j - 1 by omega]
    have hx₀4 : x₀ * x₀ * (x₀ * x₀) = 1 := by
      rw [hx₀2, ← pow_add, ← two_mul, ← pow_succ', show j - 1 + 1 = j by omega, ← hj,
        pow_orderOf_eq_one]
    have hx₀1 : x₀ * x₀ ≠ 1 := by
      rw [hx₀2]
      exact pow_ne_one_of_lt_orderOf (pow_ne_zero _ two_ne_zero)
        (by rw [hj]; exact Nat.pow_lt_pow_right (by norm_num) (by omega))
    have hx₀z : x₀ * x₀ = z := (hsdd.mul_self_eq hx₀P hx₀4 hx₀1).trans hza.symm
    by_cases hyz : y * z * y⁻¹ = z
    ·
      have hyC : y ∈ Subgroup.centralizer ({z} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc y * z = y * z * y⁻¹ * y := by group
          _ = z * y := by rw [hyz]
      exact mem_sup_of_conj_mem_of_mem_centralizer ht hA hR hRK hRS hSKR hSN hSz htS htz hxP hyC
        hyx
    ·
      exfalso
      have hwS : y * x₀ * y⁻¹ ∈ (S : Subgroup G) := by
        rw [← hx₀, ← conj_pow]
        exact Subgroup.pow_mem _ hyx _
      have hw : y * x₀ * y⁻¹ * (y * x₀ * y⁻¹) = y * z * y⁻¹ := by
        rw [← hx₀z]; group
      exact false_of_mul_self_eq ht hA
        (Subgroup.mem_centralizer_singleton_iff.mp (hSz hwS)) hw hyz

end CFSG.ClassicalInvolution.Disconnected.AschTight.T6A
