module

public import Mathlib.Data.Finite.Perm

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem relIndex_cent_le_six (V H : Subgroup G) (hV : Nat.card V = 4)
    (hHV : ∀ h ∈ H, ∀ v ∈ V, h * v * h⁻¹ ∈ V) :
    (H ⊓ centralizer (V : Set G) : Subgroup G).relIndex H ≤ 6 := by
  classical
  have hn : H ≤ Subgroup.normalizer (V : Set G) := fun h hh =>
    Subgroup.mem_normalizer_fintype (fun v hv => hHV h hh v hv)
  let T := {y : ↥V // y ≠ 1}
  have hmem : ∀ x : ↥H, ∀ y : ↥V, (x : G) * y * (x : G)⁻¹ ∈ V := fun x y =>
    (Subgroup.mem_normalizer_iff.mp (hn x.2) y).mp y.2
  let f : ↥H → T → T := fun x y =>
    ⟨⟨(x : G) * (y.1 : G) * (x : G)⁻¹, hmem x y.1⟩, fun h => y.2 (by
      have h1 : (x : G) * (y.1 : G) * (x : G)⁻¹ = 1 := congrArg Subtype.val h
      have : (y.1 : G) = 1 := by
        have h2 := congrArg (fun z => (x : G)⁻¹ * z * (x : G)) h1
        simpa [mul_assoc] using h2
      exact Subtype.ext this)⟩
  have hf1 : ∀ y, f 1 y = y := fun y => Subtype.ext (Subtype.ext (by simp [f]))
  have hfm : ∀ a b y, f (a * b) y = f a (f b y) := fun a b y =>
    Subtype.ext (Subtype.ext (by simp [f, mul_assoc]))
  let φ : ↥H →* Equiv.Perm T :=
    { toFun := fun x =>
        { toFun := f x
          invFun := f x⁻¹
          left_inv := fun y => by rw [← hfm, inv_mul_cancel, hf1]
          right_inv := fun y => by rw [← hfm, mul_inv_cancel, hf1] }
      map_one' := Equiv.ext hf1
      map_mul' := fun a b => Equiv.ext (hfm a b) }
  have hker : φ.ker = (H ⊓ Subgroup.centralizer (V : Set G)).subgroupOf H := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_iff]
    constructor
    · intro h
      refine ⟨x.2, fun y hy => ?_⟩
      by_cases hy1 : (⟨y, hy⟩ : ↥V) = 1
      · have : y = 1 := congrArg Subtype.val hy1
        subst this
        simp
      · have := congrArg (fun p : Equiv.Perm T => (p ⟨⟨y, hy⟩, hy1⟩ : T).1.1) h
        simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.coe_fn_mk, f, Equiv.Perm.coe_one,
          id_eq] at this
        have h2 : (x : G) * y * (x : G)⁻¹ = y := this
        calc y * (x : G) = ((x : G) * y * (x : G)⁻¹) * x := by rw [h2]
          _ = x * y := by rw [mul_assoc, inv_mul_cancel, mul_one]
    · rintro ⟨-, h⟩
      refine Equiv.ext fun y => Subtype.ext (Subtype.ext ?_)
      have h2 := h y.1.1 y.1.2
      show (x : G) * y.1.1 * (x : G)⁻¹ = y.1.1
      calc (x : G) * y.1.1 * (x : G)⁻¹ = (y.1.1 * (x : G)) * (x : G)⁻¹ := by rw [h2]
        _ = y.1.1 := by rw [mul_assoc, mul_inv_cancel, mul_one]
  have hT : Nat.card T = 3 := by
    haveI := Fintype.ofFinite V
    haveI : Fintype T := Fintype.ofFinite T
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      ← Nat.card_eq_fintype_card, hV]
  have hdvd := Subgroup.card_subgroup_dvd_card φ.range
  rw [Nat.card_perm, hT] at hdvd
  unfold Subgroup.relIndex
  rw [← hker, Subgroup.index_ker]
  exact Nat.le_of_dvd (by decide) (by simpa [Nat.factorial] using hdvd)

theorem sup_closure_eq_of_index_six (K N : Subgroup G) (hNK : N ≤ K)
    (hNn : ∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N) (h6 : Nat.card K = 6 * Nat.card N) {a b : G}
    (ha : a ∈ K) (hb : b ∈ K) (ha3 : a * a * a ∈ N) (ha' : a ∉ N) (hb2 : b * b ∈ N)
    (hb' : b ∉ N) : N ⊔ closure {a, b} = K := by
  classical
  haveI hN'normal : (N.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mpr
      (fun k hk => Subgroup.mem_normalizer_fintype (fun n hn => hNn k hk n hn))
  let Q := K ⧸ N.subgroupOf K
  have hN'card : Nat.card (N.subgroupOf K) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv
  have hQcard : Nat.card Q = 6 := by
    change (N.subgroupOf K).index = 6
    have hindex := Subgroup.index_mul_card (N.subgroupOf K)
    rw [hN'card, h6] at hindex
    exact Nat.mul_right_cancel (Finite.card_pos_iff.mpr ⟨⟨1, N.one_mem⟩⟩) hindex
  let aK : K := ⟨a, ha⟩
  let bK : K := ⟨b, hb⟩
  have haQ1 : QuotientGroup.mk' (N.subgroupOf K) aK ≠ 1 := by
    intro h
    exact ha' (by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
      rwa [Subgroup.mem_subgroupOf] at h)
  have haQ3 : (QuotientGroup.mk' (N.subgroupOf K) aK) ^ 3 = 1 := by
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa [pow_succ] using ha3
  have hbQ1 : QuotientGroup.mk' (N.subgroupOf K) bK ≠ 1 := by
    intro h
    exact hb' (by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
      rwa [Subgroup.mem_subgroupOf] at h)
  have hbQ2 : (QuotientGroup.mk' (N.subgroupOf K) bK) ^ 2 = 1 := by
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa [pow_two] using hb2
  have horda : orderOf (QuotientGroup.mk' (N.subgroupOf K) aK) = 3 :=
    orderOf_eq_prime haQ3 haQ1
  have hordb : orderOf (QuotientGroup.mk' (N.subgroupOf K) bK) = 2 :=
    orderOf_eq_prime hbQ2 hbQ1
  set aQ : Q := QuotientGroup.mk' (N.subgroupOf K) aK with haQdef
  set bQ : Q := QuotientGroup.mk' (N.subgroupOf K) bK with hbQdef
  set H' : Subgroup Q := closure {aQ, bQ} with hH'def
  have haQmem : aQ ∈ H' := Subgroup.subset_closure (by simp)
  have hbQmem : bQ ∈ H' := Subgroup.subset_closure (by simp)
  have hdvd3 : 3 ∣ Nat.card H' := by
    have := Subgroup.orderOf_dvd_natCard H' haQmem
    rwa [show orderOf aQ = 3 from horda] at this
  have hdvd2 : 2 ∣ Nat.card H' := by
    have := Subgroup.orderOf_dvd_natCard H' hbQmem
    rwa [show orderOf bQ = 2 from hordb] at this
  have hdvd6 : 6 ∣ Nat.card H' := by
    have := Nat.lcm_dvd hdvd3 hdvd2
    rwa [show Nat.lcm 3 2 = 6 by decide] at this
  have hcardH' : Nat.card H' = 6 := by
    have hdiv : Nat.card H' ∣ 6 := by
      have := Subgroup.card_subgroup_dvd_card H'
      rwa [hQcard] at this
    exact (Nat.dvd_antisymm hdvd6 hdiv).symm
  have hH'top : H' = ⊤ :=
    (Subgroup.card_eq_iff_eq_top H').mp (by rw [hcardH', hQcard])
  set M : Subgroup G := N ⊔ closure {a, b} with hMdef
  have hclK : closure ({a, b} : Set G) ≤ K := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  have hMK : M ≤ K := by
    rw [hMdef]; exact sup_le hNK hclK
  have hma : aQ ∈ (M.subgroupOf K).map (QuotientGroup.mk' (N.subgroupOf K)) := by
    refine ⟨aK, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp [aK])))
    · exact haQdef.symm
  have hmb : bQ ∈ (M.subgroupOf K).map (QuotientGroup.mk' (N.subgroupOf K)) := by
    refine ⟨bK, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp [bK])))
    · exact hbQdef.symm
  have hmap_top : (M.subgroupOf K).map (QuotientGroup.mk' (N.subgroupOf K)) = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← hH'top, hH'def]
    rw [Subgroup.closure_le]
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hma
    · exact hmb
  have hker_le : (QuotientGroup.mk' (N.subgroupOf K)).ker ≤ M.subgroupOf K := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr
      ((show N ≤ M by rw [hMdef]; exact le_sup_left) (Subgroup.mem_subgroupOf.mp hx))
  have hMtop : M.subgroupOf K = ⊤ := by
    rw [← Subgroup.comap_map_eq_self hker_le, hmap_top]
    simp
  have hKM : K ≤ M := Subgroup.subgroupOf_eq_top.mp hMtop
  exact le_antisymm hMK hKM

theorem card_sup_zpowers_of_sq (N : Subgroup G) {b : G} (hbN : ∀ n ∈ N, b * n * b⁻¹ ∈ N)
    (hb2 : b * b ∈ N) (hb' : b ∉ N) : Nat.card (N ⊔ zpowers b : Subgroup G) = 2 * Nat.card N := by
  classical
  set M : Subgroup G := N ⊔ zpowers b with hMdef
  have hNM : N ≤ M := le_sup_left
  have hbM : b ∈ M := (le_sup_right : zpowers b ≤ M) (Subgroup.mem_zpowers b)
  have hbNnorm : b ∈ Subgroup.normalizer (N : Set G) :=
    Subgroup.mem_normalizer_fintype (fun n hn => hbN n hn)
  have hznorm : zpowers b ≤ Subgroup.normalizer (N : Set G) := Subgroup.zpowers_le.mpr hbNnorm
  have hMnorm : M ≤ Subgroup.normalizer (N : Set G) := by
    rw [hMdef]; exact sup_le Subgroup.le_normalizer hznorm
  haveI hN'normal : (N.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mpr hMnorm
  have hindex : (N.subgroupOf M).index = 2 := by
    refine Subgroup.index_eq_two_iff_exists_notMem_and.mpr ⟨⟨b, hbM⟩, ?_, ?_⟩
    · exact fun h => hb' (Subgroup.mem_subgroupOf.mp h)
    · intro x
      have hxM : (x : G) ∈ ((N ⊔ zpowers b : Subgroup G) : Set G) := hMdef ▸ x.2
      rw [Subgroup.coe_mul_of_right_le_normalizer_left N (Subgroup.zpowers b) hznorm] at hxM
      obtain ⟨n, hn, k, hk, hnk⟩ := hxM
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hk
      have hb2' : b ^ (2 : ℤ) ∈ N := by
        rw [zpow_two]; exact hb2
      obtain ⟨m, hm | hm⟩ := Int.even_or_odd' j
      · refine Or.inr (Subgroup.mem_subgroupOf.mpr ?_)
        have hx_eq : (x : G) = n * (b ^ (2 : ℤ)) ^ m := by
          rw [← hnk, ← hj, hm, zpow_mul]
        rw [hx_eq]
        exact N.mul_mem hn (N.zpow_mem hb2' m)
      · refine Or.inl (Subgroup.mem_subgroupOf.mpr ?_)
        have hbj : b ^ j * b = (b ^ (2 : ℤ)) ^ (m + 1) := by
          rw [hm, zpow_add_one, mul_assoc, ← zpow_two, zpow_mul]
          exact (zpow_add_one (b ^ (2 : ℤ)) m).symm
        have hx_eq : (((x : M) * ⟨b, hbM⟩ : M) : G) = n * (b ^ (2 : ℤ)) ^ (m + 1) := by
          rw [Subgroup.coe_mul, Subtype.coe_mk, ← hnk, ← hj, mul_assoc, hbj]
        rw [hx_eq]
        exact N.mul_mem hn (N.zpow_mem hb2' (m + 1))
  have hcardN' : Nat.card (N.subgroupOf M) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv
  have hmul := Subgroup.index_mul_card (N.subgroupOf M)
  rw [hindex, hcardN'] at hmul
  change Nat.card M = 2 * Nat.card N
  exact hmul.symm

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
