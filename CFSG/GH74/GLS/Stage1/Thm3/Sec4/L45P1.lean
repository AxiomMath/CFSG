module

public import CFSG.GH74.GLS.Stage1.Thm2.Recip.L285
public import CFSG.GH74.GLS.IVK.Lifted.Lem31c
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Lem45

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.ComponentClassification
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

namespace L45Bal

variable {G : Type} [Group G]

theorem not_mem_odd_of_sq {N : Subgroup G} (hN : Odd (Nat.card ↥N)) {x : G}
    (hx2 : x * x = 1) (hx1 : x ≠ 1) : x ∉ N := by
  intro hx
  have h1 := Subgroup.orderOf_dvd_natCard N hx
  rw [orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1] at h1
  exact (Nat.not_even_iff_odd.2 hN) (even_iff_two_dvd.2 h1)

theorem conjSub_conjSub_of_sq {H : Type*} [Group H] {a : H} (ha : a * a = 1) (A : Subgroup H) :
    conjSub a⁻¹ (conjSub a⁻¹ A) = A := by
  rw [conjSub_conjSub']
  have : a⁻¹ * a⁻¹ = 1 := by rw [← mul_inv_rev, ha, inv_one]
  rw [this]
  ext x
  simp [conjSub]

variable [Finite G]

theorem pumpup_step {z w : G} (hw2 : orderOf w = 2) (hwC : w ∈ centralizer ({z} : Set G))
    {K₁ K₂ I : Subgroup G}
    (hK₁ : IsPCompIn 2 (centralizer ({z} : Set G)) K₁)
    (hK₂ : IsPCompIn 2 (centralizer ({z} : Set G)) K₂)
    (hperm : ∀ K : Subgroup G, (K = K₁ ∨ K = K₂) → M.cj K w = K₁ ∨ M.cj K w = K₂)
    (hI : IsPCompIn 2 (centralizer ({w} : Set G) ⊓ centralizer ({z} : Set G)) I)
    (hrk : ∀ K : Subgroup G, (K = K₁ ∨ K = K₂) →
      ¬ I ≤ centralizer ({z, w} : Set G) ⊓ centralizerSection K (pPrimeCoreOf 2 K)) :
    ∀ q ∈ I, ∃ k ∈ K₁ ⊔ K₂, k⁻¹ * q ∈ pPrimeCoreOf 2 (centralizer ({z} : Set G)) := by
  classical
  set C : Subgroup G := centralizer ({z} : Set G) with hC
  set π := TwoThin.barMk ↥C with hπ
  set s : ↥C := ⟨w, hwC⟩ with hs
  have hso : orderOf s = 2 := TwoThin.orderOf_mk_centralizer hwC hw2
  have hIW : I ≤ centralizer ({w} : Set G) ⊓ centralizer ({z} : Set G) :=
    (TwoThin.isPCompIn_two_iff.mp hI).1
  have hΛC := TwoThin.le_centralizer_mk hIW hwC
  have hΛ2 := TwoThin.isTwoComponent_centralizer_mk hI hwC
  obtain ⟨hΛE, hJsub, L₀, hL₀, hcases, hLJ, hLsJ, hiff⟩ :=
    TwoThin.pumpupY_structure hso hΛC hΛ2
  have hss : s * s = 1 := Subtype.ext (mul_self_eq_one_of_orderOf_eq_two hw2)
  have hπss : π s * π s = 1 := by rw [← map_mul, hss, map_one]
  have hΛT : (I.subgroupOf C).map π ≤ L₀ ⊔ conjSub (π s)⁻¹ L₀ := by
    rcases hcases with ⟨-, hPL⟩ | ⟨-, hAB, hPD⟩
    · exact hPL.trans le_sup_left
    · refine hPD.trans ?_
      rintro _ ⟨x, rfl⟩
      exact swapDiag_mem_sup hAB x
  have hKC₁ : K₁ ≤ C := hK₁.1
  have hKC₂ : K₂ ≤ C := hK₂.1
  have hA2 : ∀ K : Subgroup G, (K = K₁ ∨ K = K₂) →
      TwoComponents.IsTwoComponent (K.subgroupOf C) := by
    rintro K (rfl | rfl)
    · exact (TwoThin.isPCompIn_two_iff.mp hK₁).2
    · exact (TwoThin.isPCompIn_two_iff.mp hK₂).2
  set A : Subgroup G → Subgroup (TwoThin.barQ ↥C) := fun K => (K.subgroupOf C).map π with hAdef
  have hconjA : ∀ K : Subgroup G, conjSub (π s)⁻¹ (A K) = A (M.cj K w) := by
    intro K
    have h : conjSub (π s)⁻¹ ((K.subgroupOf C).map π) =
        (conjSub s⁻¹ (K.subgroupOf C)).map π := by
      unfold conjSub
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
    show conjSub (π s)⁻¹ ((K.subgroupOf C).map π) = ((M.cj K w).subgroupOf C).map π
    rw [h]
    congr 1
    ext x
    rw [TwoThin.mem_conjSub_iff']
    simp only [Subgroup.mem_subgroupOf, M.mem_cj, inv_inv]
    rfl
  have hcc : ∀ B : Subgroup (TwoThin.barQ ↥C), conjSub (π s)⁻¹ (conjSub (π s)⁻¹ B) = B :=
    fun B => conjSub_conjSub_of_sq hπss B
  have hT : ∀ K : Subgroup G, (K = K₁ ∨ K = K₂) →
      K.subgroupOf C ≤ TwoThin.pumpupY (I.subgroupOf C) →
      L₀ ⊔ conjSub (π s)⁻¹ L₀ ≤ A K₁ ⊔ A K₂ := by
    intro K hK hle
    have hAK : A K ≤ A K₁ ⊔ A K₂ := by
      rcases hK with rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
    have hcjK : conjSub (π s)⁻¹ (A K) ≤ A K₁ ⊔ A K₂ := by
      rw [hconjA]
      rcases hperm K hK with h | h
      · rw [h]; exact le_sup_left
      · rw [h]; exact le_sup_right
    rcases (hiff _ (hA2 K hK)).mp hle with h | h
    · have h' : A K = L₀ := h
      rw [h'] at hAK hcjK
      exact sup_le hAK hcjK
    · have h' : A K = conjSub (π s)⁻¹ L₀ := h
      rw [h'] at hAK hcjK
      rw [hcc] at hcjK
      exact sup_le hcjK hAK
  have hex : ∃ K : Subgroup G, (K = K₁ ∨ K = K₂) ∧
      K.subgroupOf C ≤ TwoThin.pumpupY (I.subgroupOf C) := by
    by_contra hcon
    push Not at hcon
    have hK : (K₁ = K₁ ∨ K₁ = K₂) := Or.inl rfl
    have hle := hcon K₁ hK
    have hn : ¬ (A K₁ = L₀ ∨ A K₁ = conjSub (π s)⁻¹ L₀) := fun h =>
      hle ((hiff _ (hA2 K₁ hK)).mpr h)
    have ne₁ : A K₁ ≠ L₀ := fun h => hn (Or.inl h)
    have ne₂ : A K₁ ≠ conjSub (π s)⁻¹ L₀ := fun h => hn (Or.inr h)
    have c1 : IsComponent (A K₁) := TwoThin.isComponent_map_barMk (hA2 K₁ hK)
    have hcomm1 := (CFSG.LocalCores.distinct_components_commute c1 hL₀).resolve_left ne₁
    have hcomm2 := (CFSG.LocalCores.distinct_components_commute c1
      (isComponent_conjSub hL₀ _)).resolve_left ne₂
    have hTc : L₀ ⊔ conjSub (π s)⁻¹ L₀ ≤ centralizer ((A K₁ : Subgroup (TwoThin.barQ ↥C)) :
        Set (TwoThin.barQ ↥C)) :=
      sup_le (le_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hcomm1))
        (le_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hcomm2))
    apply hrk K₁ hK
    intro q hq
    have hqC : q ∈ C := (hIW hq).2
    have hqT : π ⟨q, hqC⟩ ∈ L₀ ⊔ conjSub (π s)⁻¹ L₀ :=
      hΛT (Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hq))
    have hπ' : ∀ m ∈ K₁.subgroupOf C, π (⟨q, hqC⟩ * m * ⟨q, hqC⟩⁻¹) = π m := by
      intro m hm
      have hjm : π m ∈ A K₁ := Subgroup.mem_map_of_mem π hm
      have hcm : π m * π ⟨q, hqC⟩ = π ⟨q, hqC⟩ * π m :=
        mem_centralizer_iff.mp (hTc hqT) (π m) hjm
      rw [map_mul, map_mul, map_inv, ← hcm, mul_inv_cancel_right]
    have hqs := TwoThin.mem_centralizerSection_of_map_eq hKC₁ (hA2 K₁ hK) hqC hπ'
    refine Subgroup.mem_inf.2 ⟨?_, hqs⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hq1 : q ∈ centralizer ({w} : Set G) := (hIW hq).1
    have hq2 : q ∈ centralizer ({z} : Set G) := (hIW hq).2
    rcases hh with rfl | hh
    · exact (Subgroup.mem_centralizer_singleton_iff.1 hq2).symm
    · rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (Subgroup.mem_centralizer_singleton_iff.1 hq1).symm
  intro q hq
  have hqC : q ∈ C := (hIW hq).2
  obtain ⟨K, hK, hKle⟩ := hex
  have hqT : π ⟨q, hqC⟩ ∈ A K₁ ⊔ A K₂ :=
    hT K hK hKle (hΛT (Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hq)))
  have hsup : A K₁ ⊔ A K₂ = ((K₁.subgroupOf C) ⊔ (K₂.subgroupOf C)).map π :=
    (Subgroup.map_sup _ _ _).symm
  rw [hsup] at hqT
  obtain ⟨k', hk', hk'q⟩ := Subgroup.mem_map.1 hqT
  have hk'K : (k' : G) ∈ K₁ ⊔ K₂ := by
    have e := Subgroup.subgroupOf_sup hKC₁ hKC₂
    rw [← e] at hk'
    exact hk'
  refine ⟨k', hk'K, ?_⟩
  have h1 : k'⁻¹ * ⟨q, hqC⟩ ∈ pPrimeCore 2 ↥C := by
    have : (k' : TwoThin.barQ ↥C) = ((⟨q, hqC⟩ : ↥C) : TwoThin.barQ ↥C) := hk'q
    exact QuotientGroup.eq.1 this
  exact ⟨_, h1, by simp⟩

theorem lift_involution {N K : Subgroup G} (hN : Odd (Nat.card ↥N)) {w : G} (hw2 : w * w = 1)
    (hw1 : w ≠ 1) (hwN : ∀ n ∈ N, w * n * w⁻¹ ∈ N) {k : G} (hk : k ∈ K) (hkN : k⁻¹ * w ∈ N) :
    ∃ v ∈ K, v * v = 1 ∧ v ≠ 1 ∧ v * w⁻¹ ∈ N ∧ ∃ g : G, g * w * g⁻¹ = v := by
  classical
  have hwnot : w ∉ N := not_mem_odd_of_sq hN hw2 hw1
  set n : G := k⁻¹ * w with hn
  have hkw : k = w * n⁻¹ := by
    rw [hn]; group
  have hkk : k * k ∈ N := by
    have h1 : w * n⁻¹ * w⁻¹ ∈ N := hwN _ (inv_mem hkN)
    have e : k * k = (w * n⁻¹ * w⁻¹) * n⁻¹ := by
      calc k * k = (w * n⁻¹) * (w * n⁻¹) := by rw [← hkw]
        _ = (w * n⁻¹ * w⁻¹) * (w * w) * n⁻¹ := by group
        _ = (w * n⁻¹ * w⁻¹) * n⁻¹ := by rw [hw2, mul_one]
    rw [e]
    exact mul_mem h1 (inv_mem hkN)
  set m : ℕ := orderOf (k * k) with hm
  have hmodd : Odd m := Odd.of_dvd_nat hN (Subgroup.orderOf_dvd_natCard N hkk)
  obtain ⟨j, hj⟩ := hmodd
  have hkm : (k * k) ^ m = 1 := pow_orderOf_eq_one _
  have hv2 : k ^ m * k ^ m = 1 := by
    calc k ^ m * k ^ m = (k * k) ^ m := by rw [← pow_add, ← two_mul, pow_mul, pow_two]
      _ = 1 := hkm
  have e : k ^ m = k * (k * k) ^ j := by
    rw [hj, pow_succ', pow_mul, pow_two]
  have hvN : k ^ m * w⁻¹ ∈ N := by
    have e2 : k ^ m * w⁻¹ = w * (n⁻¹ * (k * k) ^ j) * w⁻¹ := by
      rw [e, hkw]; group
    rw [e2]
    exact hwN _ (mul_mem (inv_mem hkN) (pow_mem hkk j))
  have hv1 : k ^ m ≠ 1 := by
    intro h1
    rw [h1, one_mul] at hvN
    exact hwnot (by simpa using inv_mem hvN)
  obtain ⟨g, -, hg⟩ := IVK.Lifted.exists_conj_of_mul_mem_odd hN hv2 hw2 hv1 hw1 hwN hvN
  refine ⟨k ^ m, pow_mem hk m, hv2, hv1, hvN, g⁻¹, ?_⟩
  calc g⁻¹ * w * g⁻¹⁻¹ = g⁻¹ * (g * k ^ m * g⁻¹) * g := by rw [hg]; group
    _ = k ^ m := by group

theorem fusion_mod_core {z u₀ k : G} {K₁ K₂ : Subgroup G} (hz2 : z * z = 1)
    (hzK : z ∈ K₁ ⊔ K₂)
    (h31 : ∀ u v : G, u ∈ K₁ ⊔ K₂ → v ∈ K₁ ⊔ K₂ → u * u = 1 → v * v = 1 → u ≠ 1 → v ≠ 1 →
      u ≠ z → v ≠ z → ∃ k ∈ K₁ ⊔ K₂, k * u * k⁻¹ = v)
    (hu₀C : u₀ ∈ centralizer ({z} : Set G)) (hu₀2 : u₀ * u₀ = 1) (hu₀1 : u₀ ≠ 1) (hu₀z : u₀ ≠ z)
    (hk : k ∈ K₁ ⊔ K₂) (hkN : k⁻¹ * u₀ ∈ pPrimeCoreOf 2 (centralizer ({z} : Set G))) :
    IsConj u₀ (z * u₀) := by
  classical
  set N := pPrimeCoreOf 2 (centralizer ({z} : Set G)) with hN
  have hNodd : Odd (Nat.card ↥N) := TwoThin.card_pPrimeCoreOf_odd _
  have hNnorm : ∀ x ∈ centralizer ({z} : Set G), ∀ n ∈ N, x * n * x⁻¹ ∈ N :=
    fun x hx n hn => TwoThin.pPrimeCoreOf_normalized _ hx hn
  have hzC : z ∈ centralizer ({z} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hu₀z' : u₀ * z = z * u₀ := Subgroup.mem_centralizer_singleton_iff.1 hu₀C
  have hu₀inv : u₀⁻¹ = u₀ := inv_eq_of_mul_eq_one_right hu₀2
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  obtain ⟨v₁, hv₁K, hv₁2, hv₁1, hv₁N, g₁, hg₁⟩ :=
    lift_involution hNodd hu₀2 hu₀1 (fun n hn => hNnorm u₀ hu₀C n hn) hk hkN
  have hzu2 : (z * u₀) * (z * u₀) = 1 := by
    calc (z * u₀) * (z * u₀) = z * (u₀ * z) * u₀ := by group
      _ = z * (z * u₀) * u₀ := by rw [hu₀z']
      _ = (z * z) * (u₀ * u₀) := by group
      _ = 1 := by rw [hz2, hu₀2, mul_one]
  have hzu1 : z * u₀ ≠ 1 := by
    intro h1
    apply hu₀z
    have h2 : u₀ = z⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2, hzinv]
  have hzuC : z * u₀ ∈ centralizer ({z} : Set G) := mul_mem hzC hu₀C
  have hzk : z * k ∈ K₁ ⊔ K₂ := mul_mem hzK hk
  have hzkN : (z * k)⁻¹ * (z * u₀) ∈ N := by
    have e : (z * k)⁻¹ * (z * u₀) = k⁻¹ * u₀ := by group
    rw [e]; exact hkN
  obtain ⟨v₂, hv₂K, hv₂2, hv₂1, hv₂N, g₂, hg₂⟩ :=
    lift_involution hNodd hzu2 hzu1 (fun n hn => hNnorm _ hzuC n hn) hzk hzkN
  have hv₁z : v₁ ≠ z := by
    intro h1
    rw [h1, hu₀inv] at hv₁N
    exact not_mem_odd_of_sq hNodd hzu2 hzu1 hv₁N
  have hv₂z : v₂ ≠ z := by
    intro h1
    rw [h1] at hv₂N
    have e : z * (z * u₀)⁻¹ = u₀ := by
      calc z * (z * u₀)⁻¹ = z * (u₀⁻¹ * z⁻¹) := by rw [mul_inv_rev]
        _ = z * (u₀ * z) := by rw [hu₀inv, hzinv]
        _ = z * (z * u₀) := by rw [hu₀z']
        _ = (z * z) * u₀ := by group
        _ = u₀ := by rw [hz2, one_mul]
    rw [e] at hv₂N
    exact not_mem_odd_of_sq hNodd hu₀2 hu₀1 hv₂N
  obtain ⟨k₃, -, hk₃⟩ := h31 v₁ v₂ hv₁K hv₂K hv₁2 hv₂2 hv₁1 hv₂1 hv₁z hv₂z
  refine isConj_iff.2 ⟨g₂⁻¹ * k₃ * g₁, ?_⟩
  calc g₂⁻¹ * k₃ * g₁ * u₀ * (g₂⁻¹ * k₃ * g₁)⁻¹
      = g₂⁻¹ * (k₃ * (g₁ * u₀ * g₁⁻¹) * k₃⁻¹) * g₂ := by group
    _ = g₂⁻¹ * v₂ * g₂ := by rw [hg₁, hk₃]
    _ = z * u₀ := by rw [← hg₂]; group

end L45Bal

theorem l45_balance_step_thm (hII : II4_4_4_center) (h31 : IVK_3_1a_lifted)
    (h327 : IG_3_27) : L45_balance_step := by
  classical
  intro G _ _ z S K₁ K₂ h hA t htS htz htne hIch u₁ hu₁K hu₁S hu₁2
  have hM := m4_of_std hII h
  have hz2 : z * z = 1 := hM.z_sq
  have hzord : orderOf z = 2 := h.orderOf_z
  obtain ⟨g, hg⟩ := M.exists_conj_inv htz
  have htord : orderOf t = 2 := orderOf_conj_z h hg
  have ht2 : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two htord
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htC : t ∈ centralizer ({z} : Set G) := hM.S_syl.1 htS
  have htz' : t * z = z * t := M.centralizer_comm htC
  have hIch' : M.Intch t K₁ K₂ := (interchanges_iff t).1 hIch
  have hA' : M.H4A (pPrimeCoreOf 2) z S K₁ K₂ := (hyp4A_iff h).1 hA
  obtain ⟨u₂, hu₂def⟩ : ∃ u₂ : G, u₂ = t * u₁ * t := ⟨_, rfl⟩
  rw [← hu₂def]
  have hu₂K : u₂ ∈ K₂ := by
    have h1 : u₁ ∈ M.cj K₂ t := by rw [hIch'.2]; exact hu₁K
    have h2 := M.mem_cj.1 h1
    rw [htinv] at h2
    rw [hu₂def]; exact h2
  have hu₂S : u₂ ∈ S := by rw [hu₂def]; exact mul_mem (mul_mem htS hu₁S) htS
  have hu₂2 : u₂ * u₂ = z := by
    rw [hu₂def]
    calc t * u₁ * t * (t * u₁ * t) = t * (u₁ * (t * t) * u₁) * t := by group
      _ = t * (u₁ * u₁) * t := by rw [ht2]; group
      _ = t * z * t := by rw [hu₁2]
      _ = z * t * t := by rw [htz']
      _ = z := by rw [mul_assoc, ht2, mul_one]
  obtain ⟨hu2, hu1, huz⟩ := hM.prod_facts hu₁S hu₂S hu₁K hu₂K hu₁2 hu₂2
  have huP : u₁ * u₂ ∈ M.Pm S K₁ K₂ :=
    ⟨mul_mem hu₁S hu₂S, mul_mem (mem_sup_left hu₁K) (mem_sup_right hu₂K)⟩
  have hut : u₁ * u₂ ≠ t := by
    intro e
    exact huz (hA' (u₁ * u₂) ((le_sup_left : M.Pm S K₁ K₂ ≤ M.Rm (pPrimeCoreOf 2) S K₁ K₂) huP)
      (e ▸ htz))
  have hIntr : IsIntrinsic z K₁ := intrinsic_of_comp hM h (Or.inl rfl)
  have hcomm : Commute z t := htz'.symm
  have hnorm : t ∉ normalizer (K₁ : Set G) := by
    intro hn
    have h1 : M.cj K₁ t = K₁ := M.cj_eq_iff_normalizer.2 hn
    exact h.ne (h1.symm.trans hIch'.1)
  obtain ⟨hIcomp, hIrk, -, hIsyl⟩ := h327 G h.simple z t hzord htord hcomm K₁ hIntr hnorm
  have hconj1 : conjugate K₁ t = K₂ := hIch.1
  have hTsyl : Thm6.IsSylow2In (M.Pm S K₁ K₂) (K₁ ⊔ conjugate K₁ t) := by
    rw [hconj1]; exact hM.P_syl
  have htT : t ∈ normalizer ((M.Pm S K₁ K₂ : Subgroup G) : Set G) := by
    have hnS : t ∈ normalizer (S : Set G) := Subgroup.le_normalizer htS
    have hnK : t ∈ normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) :=
      M.mem_normalizer_of_both (fun x hx => hM.C_norm_K htC hx) (fun x hx => hM.C_norm_K' htC hx)
    exact TwoThin.mem_normalizer_inf hnS hnK
  obtain ⟨S₀, hS₀, hS₀eq⟩ := hIsyl (M.Pm S K₁ K₂) hTsyl htT
  have huI : u₁ * u₂ ∈ IDiag t K₁ := by
    have hmem : u₁ * u₂ ∈ (S₀ : Set G) := by
      rw [hS₀eq]
      refine ⟨u₁, ⟨⟨hu₁S, mem_sup_left hu₁K⟩, hu₁K⟩, ?_⟩
      show u₁ * (t⁻¹ * u₁ * t) = u₁ * u₂
      rw [htinv, hu₂def]
    exact hS₀.1 hmem
  obtain ⟨w, hw⟩ : ∃ w : G, w = g * z * g⁻¹ := ⟨_, rfl⟩
  have hw2 : w * w = 1 := by
    rw [hw]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hw1 : w ≠ 1 := by
    intro e
    have : z = 1 := by
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [← hw, e]; group
    exact hM.z_ne this
  have hwz : w ≠ z := by
    intro e
    apply htne
    calc t = g⁻¹ * z * g := hg.symm
      _ = g⁻¹ * (g * z * g⁻¹) * g := by rw [← hw, e]
      _ = z := by group
  have hwC : w ∈ centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : g⁻¹ * z * g * z = z * (g⁻¹ * z * g) := by rw [hg]; exact htz'
    calc w * z = g * (z * (g⁻¹ * z * g)) * g⁻¹ := by rw [hw]; group
      _ = g * (g⁻¹ * z * g * z) * g⁻¹ := by rw [h1]
      _ = z * w := by rw [hw]; group
  have hwconj : IsConj z w := isConj_iff.2 ⟨g, hw.symm⟩
  have hwnot : w ∉ M.ZsM (pPrimeCoreOf 2) (K₁ ⊔ K₂) := fun hwZ =>
    (hM.inv_ZsK hwZ hw2).elim hw1 hwz
  have hRk : ∀ K : Subgroup G, (K = K₁ ∨ K = K₂) →
      M.Rk1 (centralizer ({z, w} : Set G) ⊓ M.secCent K (pPrimeCoreOf 2 K)) :=
    fun K hK => hM.hc w hwC hwconj hwnot K hK
  have hperm : ∀ K : Subgroup G, (K = K₁ ∨ K = K₂) → M.cj K w = K₁ ∨ M.cj K w = K₂ := by
    intro K hK
    rcases hM.perm w hwC with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases hK with rfl | rfl
      · exact Or.inl h1
      · exact Or.inr h2
    · rcases hK with rfl | rfl
      · exact Or.inr h1
      · exact Or.inl h2
  have hK₁ : IsPCompIn 2 (centralizer ({z} : Set G)) K₁ := h.comp_isPCompIn (Or.inl rfl)
  have hK₂ : IsPCompIn 2 (centralizer ({z} : Set G)) K₂ := h.comp_isPCompIn (Or.inr rfl)
  have hI₀comp : IsPCompIn 2 (centralizer ({w} : Set G) ⊓ centralizer ({z} : Set G))
      (cmap g (IDiag t K₁)) := by
    have h1 := isPCompIn_cmap hIcomp g
    have e : cmap g (centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G)) =
        centralizer ({w} : Set G) ⊓ centralizer ({z} : Set G) := by
      show Subgroup.map (MulAut.conj g).toMonoidHom _ = _
      rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, map_centralizer_singleton_conj,
        map_centralizer_singleton_conj]
      have e1 : g * t * g⁻¹ = z := by rw [← hg]; group
      rw [e1, ← hw]
    rwa [e] at h1
  have hI₀rk : 2 ≤ pRank 2 ↥(cmap g (IDiag t K₁)) := by rw [pRank_cmap]; exact hIrk
  have hrk : ∀ K : Subgroup G, (K = K₁ ∨ K = K₂) →
      ¬ cmap g (IDiag t K₁) ≤
        centralizer ({z, w} : Set G) ⊓ centralizerSection K (pPrimeCoreOf 2 K) := by
    intro K hK hle
    obtain ⟨a, b, ha, hb, ha2, hb2, hab, hne⟩ := exists_two_involutions_of_two_le_pRank hI₀rk
    rcases hRk K hK a (hle ha) b (hle hb) (mul_self_eq_one_of_orderOf_eq_two ha2)
        (mul_self_eq_one_of_orderOf_eq_two hb2) hab with h1 | h1 | h1
    · exact ne_one_of_orderOf_eq_two ha2 h1
    · exact ne_one_of_orderOf_eq_two hb2 h1
    · exact hne h1
  have hw2' : orderOf w = 2 := M.orderOf_two_iff.2 ⟨hw2, hw1⟩
  have hstep := L45Bal.pumpup_step hw2' hwC hK₁ hK₂ hperm hI₀comp hrk
  have hu₀I : g * (u₁ * u₂) * g⁻¹ ∈ cmap g (IDiag t K₁) := by
    rw [mem_cmap]
    have e : g⁻¹ * (g * (u₁ * u₂) * g⁻¹) * g = u₁ * u₂ := by group
    rw [e]; exact huI
  obtain ⟨k, hkK, hkN⟩ := hstep _ hu₀I
  have hu₀C : g * (u₁ * u₂) * g⁻¹ ∈ centralizer ({z} : Set G) := (hI₀comp.1 hu₀I).2
  have hu₀2 : (g * (u₁ * u₂) * g⁻¹) * (g * (u₁ * u₂) * g⁻¹) = 1 := by
    calc (g * (u₁ * u₂) * g⁻¹) * (g * (u₁ * u₂) * g⁻¹)
        = g * ((u₁ * u₂) * (u₁ * u₂)) * g⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  have hu₀1 : g * (u₁ * u₂) * g⁻¹ ≠ 1 := by
    intro e
    apply hu1
    calc u₁ * u₂ = g⁻¹ * (g * (u₁ * u₂) * g⁻¹) * g := by group
      _ = 1 := by rw [e]; group
  have hu₀z : g * (u₁ * u₂) * g⁻¹ ≠ z := by
    intro e
    apply hut
    calc u₁ * u₂ = g⁻¹ * (g * (u₁ * u₂) * g⁻¹) * g := by group
      _ = g⁻¹ * z * g := by rw [e]
      _ = t := hg
  have hzK : z ∈ K₁ ⊔ K₂ := mem_sup_left (hM.z_mem_comp (Or.inl rfl))
  have hfus := L45Bal.fusion_mod_core hz2 hzK
    (fun u v hu hv hu2 hv2 hu1 hv1 huz hvz => h31 G z S K₁ K₂ h u v hu hv hu2 hv2 hu1 hv1 huz hvz)
    hu₀C hu₀2 hu₀1 hu₀z hkK hkN
  have h1 : IsConj (u₁ * u₂) (g * (u₁ * u₂) * g⁻¹) := isConj_iff.2 ⟨g, rfl⟩
  have h3 : IsConj (z * (g * (u₁ * u₂) * g⁻¹)) (t * (u₁ * u₂)) := by
    refine isConj_iff.2 ⟨g⁻¹, ?_⟩
    calc g⁻¹ * (z * (g * (u₁ * u₂) * g⁻¹)) * g⁻¹⁻¹ = (g⁻¹ * z * g) * (u₁ * u₂) := by group
      _ = t * (u₁ * u₂) := by rw [hg]
  exact h1.trans (hfus.trans h3)

end CFSG.GH74.GLS.Stage1.Thm3.Sec4
