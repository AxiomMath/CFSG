module

public import CFSG.Quasithin.Recognition.CertTwoF4Table
public import CFSG.Quasithin.Recognition.RuTypeTwoF4M
public import CFSG.Quasithin.Recognition.RuRank3TitsCls

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.Model

open Subgroup CFSG.Sporadic.Schreier.Tits
open CFSG.Quasithin (tπ twoF4M twoF4S twoF4H twoF4N twoF4P tπ_mem_twoF4M)

theorem mul_mem_titsD_iff {x y : Equiv.Perm (Fin 1755)}
    (hx : x ∈ titsA) (hy : y ∈ titsA) : x * y ∈ titsD ↔ (x ∈ titsD ↔ y ∈ titsD) := by
  have h := mul_mem_iff_of_index_two titsD_index (a := (⟨x, hx⟩ : titsA)) (b := ⟨y, hy⟩)
  simpa only [mem_subgroupOf, Subgroup.coe_mul] using h

theorem mul_inv_mem_titsD {x y : Equiv.Perm (Fin 1755)}
    (hx : x ∈ titsA) (hy : y ∈ titsA) (hxD : x ∉ titsD) (hyD : y ∉ titsD) : x * y⁻¹ ∈ titsD :=
  (mul_mem_titsD_iff hx (inv_mem hy)).2 (iff_of_false hxD fun h => hyD (by simpa using inv_mem h))

theorem card_eq_two_mul_inf_titsD
    {X : Subgroup (Equiv.Perm (Fin 1755))} (hX : X ≤ titsA) {q : Equiv.Perm (Fin 1755)}
    (hqX : q ∈ X) (hqD : q ∉ titsD) : Nat.card X = 2 * Nat.card (titsD ⊓ X : Subgroup _) := by
  have h2 : titsD.relIndex X = 2 := by
    rw [relIndex_eq_two_iff]
    refine ⟨q, hqX, fun b hb => ?_⟩
    have hb' := mul_mem_titsD_iff (hX hb) (hX hqX)
    by_cases hbD : b ∈ titsD
    · exact Or.inr ⟨hbD, fun h => hqD ((hb'.1 h).1 hbD)⟩
    · exact Or.inl ⟨hb'.2 (iff_of_false hbD hqD), hbD⟩
  rw [← relIndex_mul_card titsD X, h2]

theorem mul_self_mem_titsD {x : Equiv.Perm (Fin 1755)}
    (hx : x ∈ titsA) : x * x ∈ titsD :=
  (mul_mem_titsD_iff hx hx).2 Iff.rfl

theorem tπ_mem_titsA :
    tπ ∈ titsA :=
  CFSG.Quasithin.RuType.twoF4M_eq_titsA ▸ tπ_mem_twoF4M

theorem mem_zpowers_of_orderOf_two {G : Type*} [Group G] {x y : G} (hx : orderOf x = 2) :
    y ∈ zpowers x ↔ y = 1 ∨ y = x := by
  constructor
  · rintro ⟨k, rfl⟩
    have hk : x ^ (k % 2) = x ^ k := by simpa [hx] using zpow_mod_orderOf x k
    simp only
    rcases Int.emod_two_eq k with h | h <;> rw [← hk, h]
    · exact Or.inl (zpow_zero x)
    · exact Or.inr (zpow_one x)
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers y

theorem mul_tπ_inv_mem_titsD
    {x : Equiv.Perm (Fin 1755)}
    (hx : x ∈ titsA) (hxD : x ∉ titsD) : x * tπ⁻¹ ∈ titsD :=
  mul_inv_mem_titsD hx tπ_mem_titsA hxD CFSG.Quasithin.tπ_not_mem_D

theorem centralizer_titsZ_eq
    : titsA ⊓ centralizer {titsZ} = twoF4H := by
  have hπz := CFSG.Quasithin.tπ_comm_titsZ
  apply le_antisymm
  · intro x hx
    obtain ⟨hxA, hxz⟩ := mem_inf.1 hx
    have hxz' : x * titsZ = titsZ * x := mem_centralizer_singleton_iff.1 hxz
    by_cases hxD : x ∈ titsD
    · refine CFSG.Quasithin.le_extSub ?_
      rw [← titsD_centralizer_z]
      exact ⟨hxD, hxz⟩
    · refine Or.inr ?_
      rw [← titsD_centralizer_z]
      refine ⟨mul_tπ_inv_mem_titsD hxA hxD, mem_centralizer_singleton_iff.2 ?_⟩
      calc x * tπ⁻¹ * titsZ = x * (tπ⁻¹ * titsZ) := mul_assoc _ _ _
        _ = x * (titsZ * tπ⁻¹) := by rw [(Commute.inv_left hπz).eq]
        _ = titsZ * x * tπ⁻¹ := by rw [← mul_assoc, hxz']
        _ = titsZ * (x * tπ⁻¹) := mul_assoc _ _ _
  · intro x hx
    rcases hx with hx | hx
    · exact ⟨titsD_le_titsA (titsH_le_titsD hx), titsH_le_centralizer_z hx⟩
    · have hxA : x ∈ titsA := by
        have := mul_mem (titsD_le_titsA (titsH_le_titsD hx)) tπ_mem_titsA
        rwa [inv_mul_cancel_right] at this
      refine ⟨hxA, mem_centralizer_singleton_iff.2 ?_⟩
      have h1 : x * tπ⁻¹ * titsZ = titsZ * (x * tπ⁻¹) :=
        mem_centralizer_singleton_iff.1 (titsH_le_centralizer_z hx)
      calc x * titsZ = x * tπ⁻¹ * (tπ * titsZ) := by group
        _ = x * tπ⁻¹ * titsZ * tπ := by rw [hπz, mul_assoc (x * tπ⁻¹)]
        _ = titsZ * x := by rw [h1]; group

theorem twoF4H_inf_titsD :
    twoF4H ⊓ titsD = titsH :=
  le_antisymm (fun _ hx => CFSG.Quasithin.mem_of_mem_extSub_of_mem_D titsH_le_titsD hx.1 hx.2)
    (le_inf CFSG.Quasithin.le_extSub titsH_le_titsD)

theorem extSub_tπ_le_titsA
    {X : Subgroup (Equiv.Perm (Fin 1755))} (hX : X ≤ titsA)
    {hq : tπ ∈ normalizer (X : Set (Equiv.Perm (Fin 1755)))} {hq2 : tπ * tπ ∈ X} :
    CFSG.Quasithin.extSub X tπ hq hq2 ≤ titsA := by
  rintro x (hx | hx)
  · exact hX hx
  · have := mul_mem (hX hx) tπ_mem_titsA
    rwa [inv_mul_cancel_right] at this

theorem twoF4H_le_titsA :
    twoF4H ≤ titsA :=
  extSub_tπ_le_titsA (titsH_le_titsD.trans titsD_le_titsA)

theorem twoF4H_le_centralizer_titsZ :
    twoF4H ≤ centralizer {titsZ} := by
  have hπz := CFSG.Quasithin.tπ_comm_titsZ
  rintro x (hx | hx)
  · exact titsH_le_centralizer_z hx
  · refine mem_centralizer_singleton_iff.2 ?_
    have h1 : x * tπ⁻¹ * titsZ = titsZ * (x * tπ⁻¹) :=
      mem_centralizer_singleton_iff.1 (titsH_le_centralizer_z hx)
    calc x * titsZ = x * tπ⁻¹ * (tπ * titsZ) := by group
      _ = x * tπ⁻¹ * titsZ * tπ := by rw [hπz, mul_assoc (x * tπ⁻¹)]
      _ = titsZ * x := by rw [h1]; group

theorem card_twoF4H :
    Nat.card twoF4H = 20480 := by
  have h := relIndex_mul_card titsH twoF4H
  have h2 : titsH.relIndex twoF4H = 2 :=
    CFSG.Quasithin.relIndex_extSub fun h => CFSG.Quasithin.tπ_not_mem_D (titsH_le_titsD h)
  have h3 : titsH ⊓ twoF4H = titsH := inf_of_le_left CFSG.Quasithin.le_extSub
  rw [h2, h3, titsQH_facts.2.2.2] at h
  exact h.symm

theorem pCore_twoF4H :
    CFSG.Open.pCoreOf 2 twoF4H = twoF4P ∧ Nat.card twoF4P = 1024 ∧ twoF4P ⊓ titsD = titsJ ∧
      CFSG.Open.pCoreOf 2 titsH = titsJ ∧ Nat.card twoF4H = 20 * Nat.card twoF4P := by
  have hP : Nat.card twoF4P = 1024 := by
    rw [← CFSG.Quasithin.pCoreOf_twoF4H]
    exact CFSG.Quasithin.card_pCoreOf_twoF4H
  refine ⟨CFSG.Quasithin.pCoreOf_twoF4H, hP, ?_, CFSG.Quasithin.pCoreOf_titsH, ?_⟩
  · exact le_antisymm
      (fun _ hx => CFSG.Quasithin.mem_of_mem_extSub_of_mem_D titsJ_le_titsD hx.1 hx.2)
      (le_inf CFSG.Quasithin.le_extSub titsJ_le_titsD)
  · rw [card_twoF4H, hP]

theorem mem_titsS_of_mem_normalizer
    {y : Equiv.Perm (Fin 1755)} (hyD : y ∈ titsD)
    (hy : y ∈ normalizer (titsS : Set (Equiv.Perm (Fin 1755)))) : y ∈ titsS := by
  have hN : (⟨y, hyD⟩ : titsD) ∈ normalizer (CFSG.Quasithin.titsSD : Set titsD) := by
    rw [mem_normalizer_iff]
    intro h
    simp only [CFSG.Quasithin.titsSD, mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact mem_normalizer_iff.1 hy h
  exact CFSG.Quasithin.titsSD_normalizer_le hN

theorem titsA_centralizer_titsS :
    titsA ⊓ centralizer (titsS : Set (Equiv.Perm (Fin 1755))) = zpowers titsZ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxA, hxC⟩ := mem_inf.1 hx
    have hxN := centralizer_le_normalizer _ hxC
    by_cases hxD : x ∈ titsD
    · have hxS := mem_titsS_of_mem_normalizer hxD hxN
      have hmem : x ∈ ((center titsS).map titsS.subtype : Set (Equiv.Perm (Fin 1755))) := by
        refine ⟨⟨x, hxS⟩, mem_center_iff.2 fun g => ?_, rfl⟩
        exact Subtype.ext (mem_centralizer_iff.1 hxC g g.2)
      rw [titsS_center] at hmem
      exact (mem_zpowers_of_orderOf_two orderOf_titsZ).2 hmem
    · exfalso
      have hyS := mem_titsS_of_mem_normalizer (mul_tπ_inv_mem_titsD hxA hxD)
        (mul_mem hxN (inv_mem CFSG.Quasithin.tπ_norm_S))
      have h := CFSG.Quasithin.mul_pi_not_mem_centralizer_S hyS
      rw [inv_mul_cancel_right] at h
      exact h hxC
  · rw [zpowers_le]
    exact ⟨titsD_le_titsA titsZ_mem_titsD, titsZ_mem_centralizer_S⟩

theorem twoF4S_le_twoF4H :
    twoF4S ≤ twoF4H :=
  CFSG.Quasithin.twoF4S_le_twoF4H

theorem card_twoF4S :
    Nat.card twoF4S = 4096 ∧ twoF4S ⊓ titsD = titsS := by
  refine ⟨?_, le_antisymm (fun _ hx =>
    CFSG.Quasithin.mem_of_mem_extSub_of_mem_D titsS_le_titsD hx.1 hx.2)
    (le_inf CFSG.Quasithin.le_extSub titsS_le_titsD)⟩
  have h := relIndex_mul_card titsS twoF4S
  have h2 : titsS.relIndex twoF4S = 2 :=
    CFSG.Quasithin.relIndex_extSub fun h => CFSG.Quasithin.tπ_not_mem_D (titsS_le_titsD h)
  have h3 : titsS ⊓ twoF4S = titsS := inf_of_le_left CFSG.Quasithin.le_extSub
  rw [h2, h3, titsQS_facts.2.2.2] at h
  exact h.symm

theorem exists_sylow_twoF4S :
    ∃ P : Sylow 2 titsA, (P : Subgroup titsA) = twoF4S.subgroupOf titsA := by
  have hle : twoF4S ≤ titsA := extSub_tπ_le_titsA (titsS_le_titsD.trans titsD_le_titsA)
  have hcard : Nat.card (twoF4S.subgroupOf titsA) = 4096 := by
    rw [← (card_twoF4S).1]
    exact Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv
  have hp : IsPGroup 2 (twoF4S.subgroupOf titsA) :=
    IsPGroup.of_card (n := 12) (by rw [hcard]; norm_num)
  have hidx : ¬ 2 ∣ (twoF4S.subgroupOf titsA).index := by
    have h := card_mul_index (twoF4S.subgroupOf titsA)
    rw [hcard, card_titsA] at h
    have : (twoF4S.subgroupOf titsA).index = 8775 := by omega
    rw [this]
    decide
  exact ⟨hp.toSylow hidx, rfl⟩

theorem exists_titsD_conj_titsZ
    {a : Equiv.Perm (Fin 1755)}
    (ha : a ∈ titsA) : ∃ d ∈ titsD, d * titsZ * d⁻¹ = a * titsZ * a⁻¹ := by
  by_cases haD : a ∈ titsD
  · exact ⟨a, haD, rfl⟩
  · refine ⟨a * tπ⁻¹, mul_tπ_inv_mem_titsD ha haD, ?_⟩
    have hπz : tπ⁻¹ * titsZ = titsZ * tπ⁻¹ := (Commute.inv_left CFSG.Quasithin.tπ_comm_titsZ).eq
    calc a * tπ⁻¹ * titsZ * (a * tπ⁻¹)⁻¹ = a * (tπ⁻¹ * titsZ) * tπ * a⁻¹ := by group
      _ = a * titsZ * a⁻¹ := by rw [hπz]; group

theorem exists_titsD_conj_titsTInv
    {a : Equiv.Perm (Fin 1755)} (ha : a ∈ titsA) :
    ∃ d ∈ titsD, d * titsTInv * d⁻¹ = a * titsTInv * a⁻¹ := by
  by_cases haD : a ∈ titsD
  · exact ⟨a, haD, rfl⟩
  · refine ⟨a * CFSG.Quasithin.RuRank3.titsAux⁻¹, mul_inv_mem_titsD ha
      CFSG.Quasithin.RuRank3.titsAux_mem haD CFSG.Quasithin.RuRank3.titsAux_not_mem_D, ?_⟩
    have hc : CFSG.Quasithin.RuRank3.titsAux⁻¹ * titsTInv =
        titsTInv * CFSG.Quasithin.RuRank3.titsAux⁻¹ :=
      (Commute.inv_left CFSG.Quasithin.RuRank3.titsAux_comm).eq
    calc a * CFSG.Quasithin.RuRank3.titsAux⁻¹ * titsTInv * (a * CFSG.Quasithin.RuRank3.titsAux⁻¹)⁻¹
        = a * (CFSG.Quasithin.RuRank3.titsAux⁻¹ * titsTInv) * CFSG.Quasithin.RuRank3.titsAux *
          a⁻¹ := by group
      _ = a * titsTInv * a⁻¹ := by rw [hc]; group

theorem titsA_involution_conj
    {x : Equiv.Perm (Fin 1755)} (hx : x ∈ titsA) (h2 : orderOf x = 2) :
    x ∈ titsD ∧ ∃ d ∈ titsD, d * titsZ * d⁻¹ = x ∨ d * titsTInv * d⁻¹ = x := by
  have hxD := titsA_involution_mem_D hx h2
  refine ⟨hxD, ?_⟩
  have h2' : orderOf (⟨x, hxD⟩ : titsD) = 2 := by rw [← Subgroup.orderOf_coe]; exact h2
  rcases titsD_involution_conj ⟨x, hxD⟩ h2' with h | h
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    exact ⟨c, c.2, Or.inl (congrArg Subtype.val hc)⟩
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    exact ⟨c, c.2, Or.inr (congrArg Subtype.val hc)⟩

theorem titsA_conj_titsZ_ne_titsTInv
    {a : Equiv.Perm (Fin 1755)} (ha : a ∈ titsA) : a * titsZ * a⁻¹ ≠ titsTInv := by
  intro h
  obtain ⟨d, hd, hdz⟩ := exists_titsD_conj_titsZ ha
  refine CTUC_Tits_two_involution_classes_and_centralizer_two_kernels.2.2.2.2.1
    (isConj_iff.2 ⟨⟨d, hd⟩, Subtype.ext ?_⟩)
  exact hdz.trans h

theorem titsA_class_eq_image {x : titsD}
    (h : ∀ a ∈ titsA, ∃ d ∈ titsD, d * (x : Equiv.Perm (Fin 1755)) * d⁻¹ = a * x * a⁻¹) :
    {y | ∃ a ∈ titsA, a * (x : Equiv.Perm (Fin 1755)) * a⁻¹ = y} =
      Subtype.val '' {y : titsD | IsConj x y} := by
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨d, hd, hdx⟩ := h a ha
    exact ⟨⟨d, hd⟩ * x * ⟨d, hd⟩⁻¹, isConj_iff.2 ⟨⟨d, hd⟩, rfl⟩, hdx⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := isConj_iff.1 hy
    exact ⟨c, titsD_le_titsA c.2, rfl⟩

theorem ncard_titsA_class_titsZ :
    {y | ∃ a ∈ titsA, a * titsZ * a⁻¹ = y}.ncard = 1755 := by
  have h := titsA_class_eq_image (x := titsZD) fun a ha => exists_titsD_conj_titsZ ha
  rw [show ((titsZD : titsD) : Equiv.Perm (Fin 1755)) = titsZ from rfl] at h
  rw [h, Set.ncard_image_of_injective _ Subtype.val_injective, ncard_class_z]

theorem card_centralizer_titsTInv :
    Nat.card (titsA ⊓ centralizer {titsTInv} : Subgroup (Equiv.Perm (Fin 1755))) = 3072 ∧
      titsD ⊓ (titsA ⊓ centralizer {titsTInv}) = titsN ⊓ centralizer {titsTInv} ∧
      ¬ titsA ⊓ centralizer {titsTInv} ≤ titsD := by
  have hD : titsD ⊓ (titsA ⊓ centralizer {titsTInv}) = titsN ⊓ centralizer {titsTInv} := by
    rw [← inf_assoc, inf_of_le_left titsD_le_titsA, ← titsD_centralizer_t.1]
  have haux : CFSG.Quasithin.RuRank3.titsAux ∈ titsA ⊓ centralizer {titsTInv} :=
    ⟨CFSG.Quasithin.RuRank3.titsAux_mem,
      mem_centralizer_singleton_iff.2 CFSG.Quasithin.RuRank3.titsAux_comm⟩
  refine ⟨?_, hD, fun h => CFSG.Quasithin.RuRank3.titsAux_not_mem_D (h haux)⟩
  rw [card_eq_two_mul_inf_titsD inf_le_left haux CFSG.Quasithin.RuRank3.titsAux_not_mem_D, hD,
    card_titsCt]

theorem twoF4N_le_titsA :
    twoF4N ≤ titsA :=
  extSub_tπ_le_titsA (titsN_le_titsD.trans titsD_le_titsA)

theorem card_twoF4N :
    Nat.card twoF4N = 12288 ∧ twoF4N ⊓ titsD = titsN ∧ twoF4H ⊓ twoF4N = twoF4S := by
  refine ⟨?_, le_antisymm (fun _ hx =>
    CFSG.Quasithin.mem_of_mem_extSub_of_mem_D titsN_le_titsD hx.1 hx.2)
    (le_inf CFSG.Quasithin.le_extSub titsN_le_titsD), CFSG.Quasithin.twoF4H_inf_twoF4N⟩
  have h := relIndex_mul_card titsN twoF4N
  have h2 : titsN.relIndex twoF4N = 2 :=
    CFSG.Quasithin.relIndex_extSub fun h => CFSG.Quasithin.tπ_not_mem_D (titsN_le_titsD h)
  have h3 : titsN ⊓ twoF4N = titsN := inf_of_le_left CFSG.Quasithin.le_extSub
  rw [h2, h3, titsQN_facts.2.2.2] at h
  exact h.symm

end CFSG.LocalAnalysis.EvenBN.Tits.Model
