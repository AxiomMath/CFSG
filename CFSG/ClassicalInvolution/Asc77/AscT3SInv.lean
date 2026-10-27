module

public import CFSG.ClassicalInvolution.Asc77.AscT3CIIClose

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII.T3S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups commutatorElement

section Coset

variable {G : Type} [Group G]

theorem exists_conj_of_involutions_coset [Finite G] {N : Subgroup G} (hodd : Odd (Nat.card N))
    {s₁ s₂ : G} (hs₁ : s₁ * s₁ = 1) (hs₂ : s₂ * s₂ = 1) (h : s₂⁻¹ * s₁ ∈ N) :
    ∃ n ∈ N, n * s₂ * n⁻¹ = s₁ := by
  set n₀ : G := s₂⁻¹ * s₁ with hn₀
  have hs₂inv : s₂⁻¹ = s₂ := inv_eq_of_mul_eq_one_right hs₂
  have hs₁eq : s₁ = s₂ * n₀ := by rw [hn₀]; group
  have hinv : s₂ * n₀ * s₂ = n₀⁻¹ := by
    have h1 : (s₂ * n₀) * (s₂ * n₀) = 1 := by rw [← hs₁eq]; exact hs₁
    have h2 : (s₂ * n₀ * s₂) * n₀ = 1 := by
      have : (s₂ * n₀ * s₂) * n₀ = (s₂ * n₀) * (s₂ * n₀) := by group
      rw [this]; exact h1
    exact eq_inv_of_mul_eq_one_left h2
  have hr : Odd (orderOf n₀) := by
    have h1 : orderOf n₀ ∣ Nat.card N := by
      have := Subgroup.orderOf_dvd_natCard N h
      exact this
    exact hodd.of_dvd_nat h1
  obtain ⟨e, he⟩ := hr
  have hpow : n₀ ^ (2 * e + 1) = 1 := by rw [← he]; exact pow_orderOf_eq_one n₀
  have hconj : ∀ k : ℕ, s₂ * n₀ ^ k * s₂ = (n₀⁻¹) ^ k := by
    intro k
    calc s₂ * n₀ ^ k * s₂ = (s₂ * n₀ * s₂) ^ k := by
          have h3 : (s₂ * n₀ * s₂⁻¹) ^ k = s₂ * n₀ ^ k * s₂⁻¹ := conj_pow
          rw [hs₂inv] at h3
          exact h3.symm
      _ = (n₀⁻¹) ^ k := by rw [hinv]
  have hkey : n₀ ^ e * s₂ = s₁ * n₀ ^ e := by
    have h1 : s₂ * n₀ ^ (e + 1) * s₂ = n₀ ^ e := by
      rw [hconj (e + 1)]
      have h2 : n₀ ^ e * n₀ ^ (e + 1) = 1 := by
        rw [← pow_add, show e + (e + 1) = 2 * e + 1 by ring]
        exact hpow
      rw [inv_pow]
      exact (inv_eq_of_mul_eq_one_left h2)
    have h3 : s₂ * n₀ ^ (e + 1) = n₀ ^ e * s₂ := by
      calc s₂ * n₀ ^ (e + 1) = (s₂ * n₀ ^ (e + 1) * s₂) * s₂ := by
            rw [mul_assoc (s₂ * n₀ ^ (e + 1)) s₂ s₂, hs₂, mul_one]
        _ = n₀ ^ e * s₂ := by rw [h1]
    calc n₀ ^ e * s₂ = s₂ * n₀ ^ (e + 1) := h3.symm
      _ = s₁ * n₀ ^ e := by rw [hs₁eq, pow_succ]; group
  refine ⟨n₀ ^ e, N.pow_mem h e, ?_⟩
  rw [hkey]
  group

end Coset

section Chart

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]

theorem sl2_sq_cases (hodd : Odd (Nat.card F)) {x : SL(2, F)} (hx : x * x = 1) :
    x = 1 ∨ x = -1 := by
  have h2 : (2 : F) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
  exact CFSG.Semidihedral.OddFieldSL2.eq_one_or_minusIdentity_of_inv_eq_self F h2 x
    (inv_eq_of_mul_eq_one_right hx)

theorem chart_apply_z (hodd : Odd (Nat.card F)) {K : Subgroup G} {z : G}
    (hz : IsUniqueInvolution K z) {φ : ↥K →* SL(2, F)}
    (hφk : ∀ x : ↥K, φ x = 1 ↔ x ∈ classicalInvolutionOddCore ↥K) :
    φ ⟨z, hz.mem⟩ = -1 := by
  have hz2 := isPGroup_zpowers_of_mul_self_eq_one hz.sq hz.ne_one
  have hzN : (⟨z, hz.mem⟩ : ↥K) ∉ classicalInvolutionOddCore ↥K := fun hN =>
    hz.ne_one (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K)
      (mem_oddCoreOf_iff.mpr ⟨hz.mem, hN⟩) hz2)
  have h1 : φ ⟨z, hz.mem⟩ ≠ 1 := fun h => hzN ((hφk _).mp h)
  have h2 : φ ⟨z, hz.mem⟩ * φ ⟨z, hz.mem⟩ = 1 := by
    rw [← map_mul]
    have : (⟨z, hz.mem⟩ : ↥K) * ⟨z, hz.mem⟩ = 1 := Subtype.ext hz.sq
    rw [this, map_one]
  rcases sl2_sq_cases hodd h2 with h | h
  · exact absurd h h1
  · exact h

omit [Finite G] [Finite F] in
theorem chart_central {K : Subgroup G} {φ : ↥K →* SL(2, F)} (hφs : Function.Surjective φ)
    (hφk : ∀ x : ↥K, φ x = 1 ↔ x ∈ classicalInvolutionOddCore ↥K) {w : G} (hwK : w ∈ K)
    (hcomm : ∀ y ∈ K, ⁅w, y⁆ ∈ oddCoreOf K) :
    φ ⟨w, hwK⟩ ∈ Subgroup.center SL(2, F) := by
  rw [Subgroup.mem_center_iff]
  intro s
  obtain ⟨y, rfl⟩ := hφs s
  have h1 : ⁅(⟨w, hwK⟩ : ↥K), y⁆ ∈ classicalInvolutionOddCore ↥K :=
    (mem_oddCoreOf_iff.mp (hcomm (y : G) y.2)).2
  have h2 : φ ⁅(⟨w, hwK⟩ : ↥K), y⁆ = 1 := (hφk _).mpr h1
  rw [map_commutatorElement] at h2
  exact (commutatorElement_eq_one_iff_mul_comm.mp h2).symm

theorem exists_mul_mem_oddCore (hodd : Odd (Nat.card F)) {K : Subgroup G} {z : G}
    (hz : IsUniqueInvolution K z) {φ : ↥K →* SL(2, F)}
    (hφk : ∀ x : ↥K, φ x = 1 ↔ x ∈ classicalInvolutionOddCore ↥K) {w : G} (hwK : w ∈ K)
    (hw : φ ⟨w, hwK⟩ = 1 ∨ φ ⟨w, hwK⟩ = -1) :
    ∃ e : G, (e = 1 ∨ e = z) ∧ w * e ∈ oddCoreOf K := by
  rcases hw with h | h
  · exact ⟨1, Or.inl rfl, by
      rw [mul_one]
      exact mem_oddCoreOf_iff.mpr ⟨hwK, (hφk _).mp h⟩⟩
  · refine ⟨z, Or.inr rfl, mem_oddCoreOf_iff.mpr ⟨K.mul_mem hwK hz.mem, (hφk _).mp ?_⟩⟩
    have hzφ := chart_apply_z hodd hz hφk
    have : (⟨w * z, K.mul_mem hwK hz.mem⟩ : ↥K) = ⟨w, hwK⟩ * ⟨z, hz.mem⟩ := rfl
    rw [this, map_mul, h, hzφ]
    simp

end Chart

section Main

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem oddCoreOf_le_oddCoreOf_sup {K K' : Subgroup G}
    (hK'N : K' ≤ Subgroup.normalizer (K : Set G)) : oddCoreOf K ≤ oddCoreOf (K ⊔ K') := by
  refine Disconnected.AschTight.Sec6Gen.le_oddCoreOf_of_normal
    ((oddCoreOf_le_self K).trans le_sup_left) ?_ (oddCoreOf_odd_natCard K)
  exact sup_le (fun k hk => mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer hk))
    (fun k hk => mem_normalizer_oddCore_of_mem_normalizer (hK'N hk))

theorem oddCoreOf_sup_inf_le {K K' : Subgroup G} {x : G} (hx : x ∈ oddCoreOf (K ⊔ K'))
    (hxK' : x ∈ K') : x ∈ oddCoreOf K' :=
  oddCoreOf_inf_le (le_sup_right : K' ≤ K ⊔ K') ⟨hx, hxK'⟩

theorem exists_sq_data (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K K' : Subgroup G} (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hne : K' ≠ K) {z : G}
    (hz : IsUniqueInvolution K z) (hz' : IsUniqueInvolution K' z)
    {φ : ↥K →* SL(2, GaloisField p f)} (hφs : Function.Surjective φ)
    (hφk : ∀ x : ↥K, φ x = 1 ↔ x ∈ classicalInvolutionOddCore ↥K)
    {φ' : ↥K' →* SL(2, GaloisField p f)}
    (hφ'k : ∀ x : ↥K', φ' x = 1 ↔ x ∈ classicalInvolutionOddCore ↥K')
    {s : G} (hs : s ∈ K ⊔ K') (hs2 : s * s = 1) (hs1 : s ≠ 1) (hsz : s ≠ z) :
    ∃ (k : G) (hk : k ∈ K) (k' : G) (hk' : k' ∈ K'), s = k * k' ∧
      φ ⟨k, hk⟩ * φ ⟨k, hk⟩ = -1 ∧ φ' ⟨k', hk'⟩ * φ' ⟨k', hk'⟩ = -1 := by
  have hodd := odd_natCard_galoisField hp hq
  have hcomm := hΩ.comm_le_oddCore_of_twin hK hK' hne.symm hz hz'
  have hc : ∀ x ∈ K, ∀ y ∈ K', ⁅x, y⁆ ∈ oddCoreOf K ∧ ⁅x, y⁆ ∈ oddCoreOf K' := fun x hx y hy =>
    hcomm (Subgroup.commutator_mem_commutator hx hy)
  have hK'N : K' ≤ Subgroup.normalizer (K : Set G) :=
    hΩ.le_normalizer_of_twin hK' hK hne hz' hz
  have hNodd := oddCoreOf_odd_natCard (K ⊔ K')
  have hKN : oddCoreOf K ≤ oddCoreOf (K ⊔ K') := oddCoreOf_le_oddCoreOf_sup hK'N
  have hKN' : oddCoreOf K' ≤ oddCoreOf (K ⊔ K') := by
    have h' : K ≤ Subgroup.normalizer (K' : Set G) :=
      hΩ.le_normalizer_of_twin hK hK' hne.symm hz hz'
    have := oddCoreOf_le_oddCoreOf_sup h'
    rwa [sup_comm] at this
  have hzc : ∀ x ∈ K ⊔ K', z * x = x * z := by
    intro x hx
    have : K ⊔ K' ≤ Subgroup.centralizer ({z} : Set G) :=
      sup_le (fun w hw => Subgroup.mem_centralizer_singleton_iff.mpr (hz.commute_of_mem hw).symm)
        (fun w hw => Subgroup.mem_centralizer_singleton_iff.mpr (hz'.commute_of_mem hw).symm)
    exact (Subgroup.mem_centralizer_singleton_iff.mp (this hx)).symm
  have hφz := chart_apply_z hodd hz hφk
  have hφ'z := chart_apply_z hodd hz' hφ'k
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left K K' hK'N] at hs
  obtain ⟨k, hk, k', hk', rfl⟩ := hs
  have hak : ⁅k', k⁆ ∈ oddCoreOf K := by
    rw [← commutatorElement_inv]
    exact (oddCoreOf K).inv_mem (hc k hk k' hk').1
  have hoK : k * ⁅k', k⁆ * k⁻¹ ∈ oddCoreOf K :=
    (Subgroup.mem_normalizer_iff.mp (mem_normalizer_oddCore_of_mem_normalizer
      (Subgroup.le_normalizer hk)) _).mp hak
  set o : G := k * ⁅k', k⁆ * k⁻¹ with ho
  have hkey : (k * k') * (k * k') = o * (k * k) * (k' * k') := by
    rw [ho, commutatorElement_def]
    group
  have h1 : o * (k * k) * (k' * k') = 1 := by rw [← hkey]; exact hs2
  have hc1 : (k' * k')⁻¹ = o * (k * k) := (eq_inv_of_mul_eq_one_left h1).symm
  set c : G := (k' * k')⁻¹ with hc0
  have hoKK : o ∈ K := oddCoreOf_le_self K hoK
  have hcK' : c ∈ K' := K'.inv_mem (K'.mul_mem hk' hk')
  have hcK : c ∈ K := by rw [hc1]; exact K.mul_mem hoKK (K.mul_mem hk hk)
  have hφc : φ ⟨c, hcK⟩ = φ ⟨k, hk⟩ * φ ⟨k, hk⟩ := by
    have hoφ : φ ⟨o, hoKK⟩ = 1 := (hφk _).mpr (mem_oddCoreOf_iff.mp hoK).2
    have : (⟨c, hcK⟩ : ↥K) = ⟨o, hoKK⟩ * (⟨k, hk⟩ * ⟨k, hk⟩) := Subtype.ext hc1
    rw [this, map_mul, map_mul, hoφ, one_mul]
  have hφ'c : φ' ⟨c, hcK'⟩ = (φ' ⟨k', hk'⟩ * φ' ⟨k', hk'⟩)⁻¹ := by
    have : (⟨c, hcK'⟩ : ↥K') = (⟨k', hk'⟩ * ⟨k', hk'⟩)⁻¹ := rfl
    rw [this, map_inv, map_mul]
  have hcen : φ ⟨c, hcK⟩ ∈ Subgroup.center SL(2, GaloisField p f) :=
    chart_central hφs hφk hcK (fun y hy => by
      rw [← commutatorElement_inv]
      exact (oddCoreOf K).inv_mem (hc y hy c hcK').1)
  rcases (CFSG.ClassicalInvolution.mem_center_sl2_iff _).mp hcen with hA | hB
  · exfalso
    have hcO : c ∈ oddCoreOf K := mem_oddCoreOf_iff.mpr ⟨hcK, (hφk _).mp hA⟩
    have hcO' : c ∈ oddCoreOf K' := oddCoreOf_sup_inf_le (hKN hcO) hcK'
    have hφ'c1 : φ' ⟨c, hcK'⟩ = 1 := (hφ'k _).mpr (mem_oddCoreOf_iff.mp hcO').2
    have hk1 : φ ⟨k, hk⟩ * φ ⟨k, hk⟩ = 1 := by rw [← hφc]; exact hA
    have hk'1 : φ' ⟨k', hk'⟩ * φ' ⟨k', hk'⟩ = 1 := by
      rw [hφ'c] at hφ'c1
      exact inv_eq_one.mp hφ'c1
    obtain ⟨e, he, hkO⟩ := exists_mul_mem_oddCore hodd hz hφk hk (sl2_sq_cases hodd hk1)
    obtain ⟨e', he', hk'O⟩ := exists_mul_mem_oddCore hodd hz' hφ'k hk' (sl2_sq_cases hodd hk'1)
    have hKK' : k * k' ∈ K ⊔ K' := Subgroup.mul_mem _ (Subgroup.mem_sup_left hk)
      (Subgroup.mem_sup_right hk')
    have hzk' : z * k' = k' * z := hzc k' (Subgroup.mem_sup_right hk')
    have hec : ∀ x ∈ K ⊔ K', e * x = x * e := by
      intro x hx
      rcases he with rfl | rfl
      · simp
      · exact hzc x hx
    have hec' : ∀ x ∈ K ⊔ K', e' * x = x * e' := by
      intro x hx
      rcases he' with rfl | rfl
      · simp
      · exact hzc x hx
    obtain ⟨w, hw, hwe⟩ : ∃ w : G, (w = 1 ∨ w = z) ∧ w = e * e' := by
      refine ⟨e * e', ?_, rfl⟩
      rcases he with rfl | rfl <;> rcases he' with rfl | rfl
      · left; simp
      · right; simp
      · right; simp
      · left; exact hz.sq
    have hwc : ∀ x ∈ K ⊔ K', w * x = x * w := by
      intro x hx
      rcases hw with rfl | rfl
      · simp
      · exact hzc x hx
    have hw2 : w * w = 1 := by
      rcases hw with rfl | rfl
      · simp
      · exact hz.sq
    have hu : (k * k') * w ∈ oddCoreOf (K ⊔ K') := by
      have : (k * k') * w = (k * e) * (k' * e') := by
        rw [hwe]
        calc k * k' * (e * e') = k * (k' * e) * e' := by group
          _ = k * (e * k') * e' := by rw [← hec k' (Subgroup.mem_sup_right hk')]
          _ = (k * e) * (k' * e') := by group
      rw [this]
      exact (oddCoreOf (K ⊔ K')).mul_mem (hKN hkO) (hKN' hk'O)
    have huu : ((k * k') * w) * ((k * k') * w) = 1 := by
      calc ((k * k') * w) * ((k * k') * w) = (k * k') * (w * (k * k')) * w := by group
        _ = (k * k') * ((k * k') * w) * w := by rw [hwc _ hKK']
        _ = ((k * k') * (k * k')) * (w * w) := by group
        _ = 1 := by rw [hs2, hw2, one_mul]
    have hu1 : (k * k') * w = 1 := by
      by_contra hne1
      exact hne1 (eq_one_of_isPGroup_of_mem_odd hNodd hu
        (isPGroup_zpowers_of_mul_self_eq_one huu hne1))
    rcases hw with h | h
    · rw [h] at hu1
      exact hs1 (by simpa using hu1)
    · rw [h] at hu1
      apply hsz
      show k * k' = z
      have := eq_inv_of_mul_eq_one_left hu1
      rw [this]
      exact inv_eq_of_mul_eq_one_right hz.sq
  · have hk2 : φ ⟨k, hk⟩ * φ ⟨k, hk⟩ = -1 := by rw [← hφc]; exact hB
    have hczK : c * z ∈ oddCoreOf K := by
      refine mem_oddCoreOf_iff.mpr ⟨K.mul_mem hcK hz.mem, (hφk _).mp ?_⟩
      have : (⟨c * z, K.mul_mem hcK hz.mem⟩ : ↥K) = ⟨c, hcK⟩ * ⟨z, hz.mem⟩ := rfl
      rw [this, map_mul, hB, hφz]
      simp
    have hczK' : c * z ∈ oddCoreOf K' :=
      oddCoreOf_sup_inf_le (hKN hczK) (K'.mul_mem hcK' hz'.mem)
    have hφ'cz : φ' ⟨c, hcK'⟩ * φ' ⟨z, hz'.mem⟩ = 1 := by
      have h1 : φ' ⟨c * z, K'.mul_mem hcK' hz'.mem⟩ = 1 :=
        (hφ'k _).mpr (mem_oddCoreOf_iff.mp hczK').2
      have : (⟨c * z, K'.mul_mem hcK' hz'.mem⟩ : ↥K') = ⟨c, hcK'⟩ * ⟨z, hz'.mem⟩ := rfl
      rw [this, map_mul] at h1
      exact h1
    have hφ'c' : φ' ⟨c, hcK'⟩ = -1 := by
      rw [hφ'z] at hφ'cz
      have h2 : φ' ⟨c, hcK'⟩ = ((-1 : SL(2, GaloisField p f)))⁻¹ := eq_inv_of_mul_eq_one_left hφ'cz
      rw [h2]
      exact inv_eq_of_mul_eq_one_right (by simp)
    refine ⟨k, hk, k', hk', rfl, hk2, ?_⟩
    rw [hφ'c] at hφ'c'
    have h3 := inv_eq_iff_eq_inv.mp hφ'c'
    rw [h3]
    exact inv_eq_of_mul_eq_one_right (by simp)

theorem exists_conj_of_involutions_sup_mod (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) {K K' : Subgroup G} (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hne : K' ≠ K)
    {z : G} (hz : IsUniqueInvolution K z) (hz' : IsUniqueInvolution K' z) {s s' : G}
    (hs : s ∈ K ⊔ K') (hs2 : s * s = 1) (hs1 : s ≠ 1) (hsz : s ≠ z) (hs' : s' ∈ K ⊔ K')
    (hs'2 : s' * s' = 1) (hs'1 : s' ≠ 1) (hs'z : s' ≠ z) :
    ∃ m ∈ K ⊔ K', m * s * m⁻¹ = s' := by
  have hodd := odd_natCard_galoisField hp hq
  obtain ⟨φ, hφs, hφk⟩ := hΩ.exists_chart hK
  obtain ⟨φ', hφ's, hφ'k⟩ := hΩ.exists_chart hK'
  have hcomm := hΩ.comm_le_oddCore_of_twin hK hK' hne.symm hz hz'
  have hc : ∀ x ∈ K, ∀ y ∈ K', ⁅x, y⁆ ∈ oddCoreOf K ∧ ⁅x, y⁆ ∈ oddCoreOf K' := fun x hx y hy =>
    hcomm (Subgroup.commutator_mem_commutator hx hy)
  have hK'N : K' ≤ Subgroup.normalizer (K : Set G) :=
    hΩ.le_normalizer_of_twin hK' hK hne hz' hz
  have hKN'' : K ≤ Subgroup.normalizer (K' : Set G) :=
    hΩ.le_normalizer_of_twin hK hK' hne.symm hz hz'
  have hNodd := oddCoreOf_odd_natCard (K ⊔ K')
  have hKN : oddCoreOf K ≤ oddCoreOf (K ⊔ K') := oddCoreOf_le_oddCoreOf_sup hK'N
  have hKN' : oddCoreOf K' ≤ oddCoreOf (K ⊔ K') := by
    have := oddCoreOf_le_oddCoreOf_sup hKN''
    rwa [sup_comm] at this
  have hNnorm : ∀ x ∈ K ⊔ K', ∀ n ∈ oddCoreOf (K ⊔ K'), x * n * x⁻¹ ∈ oddCoreOf (K ⊔ K') :=
    fun x hx n hn => (Subgroup.mem_normalizer_iff.mp (mem_normalizer_oddCore_of_mem_normalizer
      (Subgroup.le_normalizer hx)) n).mp hn
  obtain ⟨k, hk, k', hk', rfl, hk2, hk'2⟩ :=
    exists_sq_data hp hq hΩ hK hK' hne hz hz' hφs hφk hφ'k hs hs2 hs1 hsz
  obtain ⟨h, hh, h', hh', rfl, hh2, hh'2⟩ :=
    exists_sq_data hp hq hΩ hK hK' hne hz hz' hφs hφk hφ'k hs' hs'2 hs'1 hs'z
  obtain ⟨g₀, hg₀⟩ := exists_sl2_conj_of_sq_eq_neg_one hodd hk2 hh2
  obtain ⟨g, rfl⟩ := hφs g₀
  obtain ⟨g₁, hg₁⟩ := exists_sl2_conj_of_sq_eq_neg_one hodd hk'2 hh'2
  obtain ⟨g', rfl⟩ := hφ's g₁
  have hgK : (g : G) ∈ K := g.2
  have hg'K' : (g' : G) ∈ K' := g'.2
  have ho₂ : h⁻¹ * ((g : G) * k * (g : G)⁻¹) ∈ oddCoreOf K := by
    have hmem : h⁻¹ * ((g : G) * k * (g : G)⁻¹) ∈ K :=
      K.mul_mem (K.inv_mem hh) (K.mul_mem (K.mul_mem hgK hk) (K.inv_mem hgK))
    refine mem_oddCoreOf_iff.mpr ⟨hmem, (hφk _).mp ?_⟩
    have : (⟨h⁻¹ * ((g : G) * k * (g : G)⁻¹), hmem⟩ : ↥K) =
        (⟨h, hh⟩ : ↥K)⁻¹ * (g * ⟨k, hk⟩ * g⁻¹) := rfl
    rw [this, map_mul, map_inv, map_mul, map_mul, map_inv]
    have h1 : φ g * φ ⟨k, hk⟩ * (φ g)⁻¹ = φ ⟨h, hh⟩ := by
      rw [hg₀, mul_assoc, mul_inv_cancel, mul_one]
    rw [h1, inv_mul_cancel]
  have ho₂' : h'⁻¹ * ((g' : G) * k' * (g' : G)⁻¹) ∈ oddCoreOf K' := by
    have hmem : h'⁻¹ * ((g' : G) * k' * (g' : G)⁻¹) ∈ K' :=
      K'.mul_mem (K'.inv_mem hh') (K'.mul_mem (K'.mul_mem hg'K' hk') (K'.inv_mem hg'K'))
    refine mem_oddCoreOf_iff.mpr ⟨hmem, (hφ'k _).mp ?_⟩
    have : (⟨h'⁻¹ * ((g' : G) * k' * (g' : G)⁻¹), hmem⟩ : ↥K') =
        (⟨h', hh'⟩ : ↥K')⁻¹ * (g' * ⟨k', hk'⟩ * g'⁻¹) := rfl
    rw [this, map_mul, map_inv, map_mul, map_mul, map_inv]
    have h1 : φ' g' * φ' ⟨k', hk'⟩ * (φ' g')⁻¹ = φ' ⟨h', hh'⟩ := by
      rw [hg₁, mul_assoc, mul_inv_cancel, mul_one]
    rw [h1, inv_mul_cancel]
  have ha : ⁅(g' : G), k⁆ ∈ oddCoreOf K := by
    rw [← commutatorElement_inv]
    exact (oddCoreOf K).inv_mem (hc k hk g' hg'K').1
  have hb : ⁅(g : G), h'⁆ ∈ oddCoreOf K' := (hc g hgK h' hh').2
  have ha₁ : (g : G) * ⁅(g' : G), k⁆ * (g : G)⁻¹ ∈ oddCoreOf K :=
    (Subgroup.mem_normalizer_iff.mp (mem_normalizer_oddCore_of_mem_normalizer
      (Subgroup.le_normalizer hgK)) _).mp ha
  have hKK : k * k' ∈ K ⊔ K' := Subgroup.mul_mem _ (Subgroup.mem_sup_left hk)
    (Subgroup.mem_sup_right hk')
  have hmM : (g : G) * g' ∈ K ⊔ K' := Subgroup.mul_mem _ (Subgroup.mem_sup_left hgK)
    (Subgroup.mem_sup_right hg'K')
  have hhh : h * h' ∈ K ⊔ K' := Subgroup.mul_mem _ (Subgroup.mem_sup_left hh)
    (Subgroup.mem_sup_right hh')
  have hhM : h ∈ K ⊔ K' := Subgroup.mem_sup_left hh
  have hh'M : h' ∈ K ⊔ K' := Subgroup.mem_sup_right hh'
  have hgM : (g : G) ∈ K ⊔ K' := Subgroup.mem_sup_left hgK
  have hn₃ : (g : G) * (h'⁻¹ * ((g' : G) * k' * (g' : G)⁻¹)) * (g : G)⁻¹ ∈ oddCoreOf (K ⊔ K') :=
    hNnorm g hgM _ (hKN' ho₂')
  have hX : (h⁻¹ * ((g : G) * ⁅(g' : G), k⁆ * (g : G)⁻¹) * h) *
      (h⁻¹ * ((g : G) * k * (g : G)⁻¹)) * ⁅(g : G), h'⁆ ∈ oddCoreOf (K ⊔ K') := by
    refine (oddCoreOf (K ⊔ K')).mul_mem ((oddCoreOf (K ⊔ K')).mul_mem ?_ (hKN ho₂)) (hKN' hb)
    have := hNnorm h⁻¹ ((K ⊔ K').inv_mem hhM) _ (hKN ha₁)
    simpa using this
  have hY : h'⁻¹ * ((h⁻¹ * ((g : G) * ⁅(g' : G), k⁆ * (g : G)⁻¹) * h) *
      (h⁻¹ * ((g : G) * k * (g : G)⁻¹)) * ⁅(g : G), h'⁆) * h' *
      ((g : G) * (h'⁻¹ * ((g' : G) * k' * (g' : G)⁻¹)) * (g : G)⁻¹) ∈ oddCoreOf (K ⊔ K') := by
    refine (oddCoreOf (K ⊔ K')).mul_mem ?_ hn₃
    have := hNnorm h'⁻¹ ((K ⊔ K').inv_mem hh'M) _ hX
    simpa using this
  have hcoset : (h * h')⁻¹ * (((g : G) * g') * (k * k') * ((g : G) * g')⁻¹) ∈
      oddCoreOf (K ⊔ K') := by
    have e : (h * h')⁻¹ * (((g : G) * g') * (k * k') * ((g : G) * g')⁻¹) =
        h'⁻¹ * ((h⁻¹ * ((g : G) * ⁅(g' : G), k⁆ * (g : G)⁻¹) * h) *
          (h⁻¹ * ((g : G) * k * (g : G)⁻¹)) * ⁅(g : G), h'⁆) * h' *
          ((g : G) * (h'⁻¹ * ((g' : G) * k' * (g' : G)⁻¹)) * (g : G)⁻¹) := by
      rw [commutatorElement_def, commutatorElement_def]
      group
    rw [e]
    exact hY
  have hs₂ : (((g : G) * g') * (k * k') * ((g : G) * g')⁻¹) *
      (((g : G) * g') * (k * k') * ((g : G) * g')⁻¹) = 1 := by
    calc _ = ((g : G) * g') * ((k * k') * (k * k')) * ((g : G) * g')⁻¹ := by group
      _ = 1 := by rw [hs2]; group
  obtain ⟨n, hnN, hn⟩ := exists_conj_of_involutions_coset hNodd hs'2 hs₂
    (by simpa using (oddCoreOf (K ⊔ K')).inv_mem hcoset)
  refine ⟨n * ((g : G) * g'), (K ⊔ K').mul_mem (oddCoreOf_le_self _ hnN) hmM, ?_⟩
  rw [← hn]
  group

end Main

end CFSG.ClassicalInvolution.Asc77.T3CII.T3S
