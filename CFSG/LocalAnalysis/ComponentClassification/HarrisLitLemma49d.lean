module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma49c

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools
open scoped Pointwise

theorem inv_mul_mem_of_relIndex_two {G : Type*} [Group G] {T U : Subgroup G}
    (hUidx : U.relIndex T = 2) {a b : G} (haT : a ∈ T) (hbT : b ∈ T) (haU : a ∉ U)
    (hbU : b ∉ U) : a⁻¹ * b ∈ U := by
  have key := (Subgroup.mul_mem_iff_of_index_two (H := U.subgroupOf T) hUidx
    (a := (⟨a, haT⟩ : T)⁻¹) (b := ⟨b, hbT⟩)).2 (by
      rw [inv_mem_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact iff_of_false haU hbU)
  exact Subgroup.mem_subgroupOf.1 key

variable {X : Type} [Group X] {t : X} {L : Subgroup X} {p f : ℕ}

namespace Standing

namespace Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem inf_centralizer_X_eq [Finite X] (hKC : AutPSL2CentralizerInput) (hσ : Setup42 h hS w z)
    {V : Subgroup X}
    (hV : IsSylowOf 2 V (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)))
    (hSV : S ≤ V) :
    V ⊓ centralizer ((closure {t, w ^ (orderOf w / 2), z} : Subgroup X) : Set X) =
      zpowers t ⊔ (S ⊓ L) ⊔ zpowers w :=
  (hσ.isSylowOf_centralizer_X hKC).eq_of_le (le_inf (hσ.T_le.trans hSV) fun g hg =>
    mem_centralizer_iff.mpr fun _ hx =>
      (mem_centralizer_iff.mp (hσ.X_le_center_T hx).2 g hg).symm)
    inf_le_right (hV.isPGroup.to_le inf_le_left)

theorem center_V_le_X [Finite X] (hKC : AutPSL2CentralizerInput) (hσ : Setup42 h hS w z)
    {V : Subgroup X}
    (hV : IsSylowOf 2 V (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)))
    (hSV : S ≤ V) : V ⊓ centralizer (V : Set X) ≤ closure {t, w ^ (orderOf w / 2), z} := by
  intro y hy
  have hTV : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ V := hσ.T_le.trans hSV
  have hyT : y ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := by
    rw [← hσ.inf_centralizer_X_eq hKC hV hSV]
    refine Subgroup.mem_inf.mpr ⟨hy.1, mem_centralizer_iff.mpr fun x hx => ?_⟩
    exact mem_centralizer_iff.mp hy.2 x (hTV (hσ.X_le_T hx))
  rw [← hσ.center_T]
  exact Subgroup.mem_inf.mpr ⟨hyT, mem_centralizer_iff.mpr fun g hg =>
    mem_centralizer_iff.mp hy.2 g (hTV hg)⟩

theorem relIndex_le_four [Finite X] (hKF : AutPSL2FusionInput) (hσ : Setup42 h hS w z)
    {V : Subgroup X}
    (hV : IsSylowOf 2 V (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)))
    (hSV : S ≤ V) : S.relIndex V = 2 ∨ S.relIndex V = 4 := by
  have hk := hσ.relIndex_eq hKF hV hSV
  have htT : t ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := mem_sup_left (mem_sup_left (mem_zpowers t))
  have htM : t ∈ normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X) :=
    Subgroup.le_normalizer htT
  obtain ⟨hsub, h6⟩ := hσ.conj_t_subset
  have hle6 : S.relIndex V ≤ 6 := by
    rw [← hk, ← ncard_conj_orbit _ htM]
    exact (Set.ncard_le_ncard hsub).trans h6
  have hdvd : S.relIndex V ∣ 2 ^ (Nat.card (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w :
      Subgroup X) : Set X))).factorization 2 := by
    rw [← hV.card_eq]
    exact Subgroup.relIndex_dvd_card (H := S) (K := V)
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hne1 : S.relIndex V ≠ 1 := fun h1 =>
    hσ.ne_of_isSylowOf_normalizer hV hSV (le_antisymm hSV (Subgroup.relIndex_eq_one.mp h1))
  rw [he] at hle6 hne1 ⊢
  rcases e with _ | _ | _ | e
  · exact absurd (pow_zero 2) hne1
  · left
    rfl
  · right
    rfl
  · exfalso
    have : 8 ≤ 2 ^ (e + 1 + 1 + 1) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (e + 1 + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem sq_mem_centralizer_X_of_fix [Finite X] (hσ : Setup42 h hS w z) {m β : X}
    (hmN : m ∈ normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X))
    (hβX : β ∈ closure {t, w ^ (orderOf w / 2), z}) (hβ1 : β ≠ 1) (hβz : β ≠ z)
    (hmβ : m * β * m⁻¹ = β) :
    m ^ 2 ∈ centralizer ((closure {t, w ^ (orderOf w / 2), z} : Subgroup X) : Set X) := by
  classical
  have hMX := hσ.normalizer_T_le_normalizer_X hmN
  have hmz : m * z * m⁻¹ = z := hσ.conj_z_of_mem_normalizer_T hmN
  have hzX : z ∈ closure {t, w ^ (orderOf w / 2), z} := subset_closure (by simp)
  have hz1 : z ≠ 1 := by
    intro hz
    have := hσ.z_order
    rw [hz, orderOf_one] at this
    exact absurd this (by norm_num)
  set K := closure ({β, z} : Set X) with hK
  have hKX : K ≤ closure {t, w ^ (orderOf w / 2), z} := by
    rw [closure_le]
    rintro x (rfl | rfl)
    · exact hβX
    · exact hzX
  have hKm : K ≤ centralizer ({m} : Set X) := by
    rw [closure_le]
    rintro x (rfl | rfl) <;> rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    · calc x * m = (m * x * m⁻¹) * m := by rw [hmβ]
        _ = m * x := by group
    · calc x * m = (m * x * m⁻¹) * m := by rw [hmz]
        _ = m * x := by group
  have hβzK : β * z ∈ K := mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  have hK4 : 4 ≤ Nat.card K := by
    have hsub : (({1, β, z, β * z} : Finset X) : Set X) ⊆ (K : Set X) := by
      intro x hx
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact one_mem K
      · exact subset_closure (by simp)
      · exact subset_closure (by simp)
      · exact hβzK
    have hcard : ({1, β, z, β * z} : Finset X).card = 4 := by
      have h1 : β * z ≠ 1 := fun h' => hβz (by
        calc β = β * z * z⁻¹ := by group
          _ = z⁻¹ := by rw [h', one_mul]
          _ = z := inv_eq_of_mul_eq_one_right (by
            rw [← sq, ← hσ.z_order, pow_orderOf_eq_one]))
      have h2 : β * z ≠ β := fun h' => hz1 (by simpa using h')
      have h3 : β * z ≠ z := fun h' => hβ1 (by simpa using h')
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_pair (Ne.symm h3)]
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hβz, Ne.symm h2⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨Ne.symm hβ1, Ne.symm hz1, Ne.symm h1⟩
    have := Set.ncard_le_ncard hsub
    rw [Set.ncard_coe_finset, hcard] at this
    rw [← Nat.card_coe_set_eq] at this
    exact this
  have hidx : K.relIndex (closure {t, w ^ (orderOf w / 2), z}) ≤ 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := K) (K := closure {t, w ^ (orderOf w / 2), z})
    rw [inf_of_le_left hKX] at h1
    have h2 := hσ.card_X_le
    by_contra hlt
    have : 3 * Nat.card K ≤ K.relIndex (closure {t, w ^ (orderOf w / 2), z}) * Nat.card K :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  refine mem_centralizer_iff.mpr fun x hx => ?_
  by_cases hxK : x ∈ K
  · have hc := mem_centralizer_singleton_iff.mp (hKm hxK)
    rw [sq]
    calc x * (m * m) = (x * m) * m := by group
      _ = (m * x) * m := by rw [hc]
      _ = m * (x * m) := by group
      _ = m * (m * x) := by rw [hc]
      _ = m * m * x := by group
  ·
    have hidx2 : K.relIndex (closure {t, w ^ (orderOf w / 2), z}) = 2 := by
      have hne1 : K.relIndex (closure {t, w ^ (orderOf w / 2), z}) ≠ 1 := fun h1 =>
        hxK (Subgroup.relIndex_eq_one.mp h1 hx)
      have hne0 : K.relIndex (closure {t, w ^ (orderOf w / 2), z}) ≠ 0 := by
        intro h0
        have h1 := Subgroup.relIndex_mul_card (H := K) (K := closure {t, w ^ (orderOf w / 2), z})
        rw [h0, zero_mul] at h1
        exact Nat.card_pos.ne' h1.symm
      omega
    have hmx : m * x * m⁻¹ ∈ closure {t, w ^ (orderOf w / 2), z} :=
      (mem_normalizer_iff.mp hMX x).mp hx
    have hmxK : m * x * m⁻¹ ∉ K := by
      intro hmxK
      apply hxK
      have hc := mem_centralizer_singleton_iff.mp (hKm hmxK)
      have : x = m⁻¹ * (m * x * m⁻¹) * m := by group
      rw [this, show m⁻¹ * (m * x * m⁻¹) * m = m * x * m⁻¹ by
        calc m⁻¹ * (m * x * m⁻¹) * m = m⁻¹ * ((m * x * m⁻¹) * m) := by group
          _ = m⁻¹ * (m * (m * x * m⁻¹)) := by rw [hc]
          _ = m * x * m⁻¹ := by group]
      exact hmxK
    have hcK := inv_mul_mem_of_relIndex_two hidx2 hx hmx hxK hmxK
    set c := x⁻¹ * (m * x * m⁻¹) with hc
    have hcm := mem_centralizer_singleton_iff.mp (hKm hcK)
    have hc2 : c * c = 1 := by
      rw [← sq]
      exact hσ.sq_eq_one_of_mem_X (hKX hcK)
    have hmxe : m * x * m⁻¹ = x * c := by rw [hc]; group
    have hm2x : m ^ 2 * x * (m ^ 2)⁻¹ = x := by
      calc m ^ 2 * x * (m ^ 2)⁻¹ = m * (m * x * m⁻¹) * m⁻¹ := by rw [sq]; group
        _ = m * (x * c) * m⁻¹ := by rw [hmxe]
        _ = (m * x * m⁻¹) * (m * c * m⁻¹) := by group
        _ = (x * c) * c := by
            rw [hmxe, show m * c * m⁻¹ = c by
              calc m * c * m⁻¹ = (c * m) * m⁻¹ := by rw [hcm]
                _ = c := by group]
        _ = x := by rw [mul_assoc, hc2, mul_one]
    calc x * m ^ 2 = (m ^ 2 * x * (m ^ 2)⁻¹) * m ^ 2 := by rw [hm2x]
      _ = m ^ 2 * x := by group

theorem sq_mem_T_of_fix [Finite X] (hKC : AutPSL2CentralizerInput) (hσ : Setup42 h hS w z)
    {V : Subgroup X}
    (hV : IsSylowOf 2 V (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)))
    (hSV : S ≤ V) {β v : X} (hβX : β ∈ closure {t, w ^ (orderOf w / 2), z}) (hβ1 : β ≠ 1)
    (hβz : β ≠ z) (hv : v ∈ V) (hvβ : v * β * v⁻¹ = β) :
    v ^ 2 ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := by
  rw [← hσ.inf_centralizer_X_eq hKC hV hSV]
  exact Subgroup.mem_inf.mpr ⟨pow_mem hv 2,
    hσ.sq_mem_centralizer_X_of_fix (hV.le hv) hβX hβ1 hβz hvβ⟩

end Setup42

end Standing

end CFSG.ComponentClassification.HarrisLit
