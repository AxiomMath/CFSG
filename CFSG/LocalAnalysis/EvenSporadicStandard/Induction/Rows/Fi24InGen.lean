module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24InGeo

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Sporadic CFSG.Blueprint.Fischer CFSG.Sporadic.Fi24
open CFSG.Fischer hiding OutTwo
open CFSG.EvenSporadicStandard.Solomon78 CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Solomon78.Fi24Row
  (edge_hW LE_trans_W mem_LE_iff ρE tR_mul_mem_JR_of_mem)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


local notation "W" => (LocalClass D24 tR ∩ LocalClass D24 xb)

attribute [local instance] fi24inKAction

theorem fi24in_pretransitive : MulAction.IsPretransitive ↥fi24inK ↥W := by
  obtain ⟨ψ, hψc, hψt⟩ := edgeLocal_of_localPoints pair_R Fi23.pair_J Fi22.pair_D
    localPoints_D24 (Fi23.localPoints_D23 CFSG.Fischer.polarFacts) ⟨tR, tR_mem_D24⟩
    ⟨xb, xb_mem_D24⟩ tR_ne_xb tR_xb_comm
  refine ⟨fun x y => ?_⟩
  obtain ⟨ℓ, hℓ, hℓx⟩ := LE_trans_W ψ hψc hψt x.2 y.2
  obtain ⟨k, hk, rfl⟩ := fi24in_exists_of_mem_LE hℓ
  refine ⟨⟨k, hk⟩, Subtype.ext ?_⟩
  rw [fi24in_smul_val]
  exact hℓx

theorem fi24in_exists_LE_inner (ψ : ↥W ≃ Fi22.D)
    (hψc : ∀ x y : ↥W, (x : R) * y = y * x ↔ (ψ x : Fi22.J) * ψ y = ψ y * ψ x)
    (hψt : ∀ x y : ↥W, ∃ h : (x : R) * y * x ∈ W, (ψ ⟨_, h⟩ : Fi22.J) = ψ x * ψ y * ψ x)
    (g : Fi22.J) :
    ∃ ℓ ∈ Fi24.LE, ∀ (w : ↥W) (hw : ℓ * (w : R) * ℓ⁻¹ ∈ W),
      (ψ ⟨ℓ * w * ℓ⁻¹, hw⟩ : Fi22.J) = g * (ψ w : Fi22.J) * g⁻¹ := by
  have hrangeL := range_edgeHomL pair_R Fi22.pair_D tR_mem_D24 xb_mem_D24 tR_ne_xb tR_xb_comm ψ
    hψc hψt Fi22.center_eq_bot Fi22.index_innerTau_range (inf_le_left : CE ≤ _) commutator_LE
    (by rw [Fi22.card_tauGroup]; exact card_LE) (fun ℓ hℓ h => eq_of_mem_LE_centralizes hℓ h)
  have hmem : innerTau Fi22.pair_D g ∈ (innerTau Fi22.pair_D).range := ⟨g, rfl⟩
  rw [← hrangeL] at hmem
  obtain ⟨ℓ, hℓ⟩ := hmem
  refine ⟨(ℓ : R), ℓ.2, fun w hw => ?_⟩
  have h1 := edgeHom_apply pair_R Fi22.pair_D tR_mem_D24 xb_mem_D24 tR_ne_xb tR_xb_comm ψ hψc
    hψt Fi22.center_eq_bot (Subgroup.inclusion (inf_le_left.trans inf_le_left) ℓ) w
  have h0 : edgeHom pair_R Fi22.pair_D tR_mem_D24 xb_mem_D24 tR_ne_xb tR_xb_comm ψ hψc hψt
      Fi22.center_eq_bot (Subgroup.inclusion (inf_le_left.trans inf_le_left) ℓ) =
      innerTau Fi22.pair_D g := hℓ
  have h1' := congrArg Subtype.val h1
  rw [h0] at h1'
  have h5 : (((innerTau Fi22.pair_D g : tauGroup Fi22.pair_D) : Equiv.Perm Fi22.D) (ψ w) :
      Fi22.J) = g * (ψ w : Fi22.J) * g⁻¹ := innerTau_apply Fi22.pair_D g (ψ w)
  have h3 := h1'.symm.trans h5
  have h4' := edgeHomW_val pair_R Fi22.pair_D tR_mem_D24 xb_mem_D24 tR_ne_xb tR_xb_comm ψ hψc
    Fi22.center_eq_bot (Subgroup.inclusion (inf_le_left.trans inf_le_left) ℓ) w
  simp only [Subgroup.coe_inclusion] at h4'
  have h4 : (⟨(ℓ : R) * w * (ℓ : R)⁻¹, hw⟩ : ↥W) =
      edgeHomW pair_R Fi22.pair_D tR_mem_D24 xb_mem_D24 tR_ne_xb tR_xb_comm ψ hψc
        Fi22.center_eq_bot (Subgroup.inclusion (inf_le_left.trans inf_le_left) ℓ) w :=
    Subtype.ext h4'.symm
  rw [h4]
  exact h3

theorem fi24in_exists_K_inner (ψ : ↥W ≃ Fi22.D)
    (hψc : ∀ x y : ↥W, (x : R) * y = y * x ↔ (ψ x : Fi22.J) * ψ y = ψ y * ψ x)
    (hψt : ∀ x y : ↥W, ∃ h : (x : R) * y * x ∈ W, (ψ ⟨_, h⟩ : Fi22.J) = ψ x * ψ y * ψ x)
    (g : Fi22.J) : ∃ k : ↥fi24inK, ∀ w : ↥W, (ψ (k • w) : Fi22.J) = g * (ψ w : Fi22.J) * g⁻¹ := by
  obtain ⟨ℓ, hℓ, h⟩ := fi24in_exists_LE_inner ψ hψc hψt g
  obtain ⟨k, hk, rfl⟩ := fi24in_exists_of_mem_LE hℓ
  refine ⟨⟨k, hk⟩, fun w => ?_⟩
  have hw := fi24in_conj_mem_W (mem_fi24inK_iff.1 hk).1 w.2
  have e : (⟨jR k * (w : R) * (jR k)⁻¹, hw⟩ : ↥W) = (⟨k, hk⟩ : ↥fi24inK) • w :=
    Subtype.ext (fi24in_smul_val ⟨k, hk⟩ w).symm
  rw [← e]
  exact h w hw

theorem fi24in_exists_fix_move {a b : ↥W} (hne : a ≠ b) :
    ∃ k : ↥fi24inK, k • a = a ∧ k • b ≠ b := by
  obtain ⟨ψ, hψc, hψt⟩ := edgeLocal_of_localPoints pair_R Fi23.pair_J Fi22.pair_D
    localPoints_D24 (Fi23.localPoints_D23 CFSG.Fischer.polarFacts) ⟨tR, tR_mem_D24⟩
    ⟨xb, xb_mem_D24⟩ tR_ne_xb tR_xb_comm
  by_contra hcon
  push Not at hcon
  have hcomm : ∀ g : Fi22.J, g * (ψ a : Fi22.J) = (ψ a : Fi22.J) * g →
      g * (ψ b : Fi22.J) = (ψ b : Fi22.J) * g := by
    intro g hg
    obtain ⟨k, hk⟩ := fi24in_exists_K_inner ψ hψc hψt g
    have h1 : k • a = a := by
      apply ψ.injective
      apply Subtype.ext
      rw [hk a, mul_inv_eq_iff_eq_mul]
      exact hg
    have h3 := hk b
    rw [hcon k h1, eq_comm, mul_inv_eq_iff_eq_mul] at h3
    exact h3
  have hσ := Fi22.eq_of_commute_centralizer (ψ a) (Pair.conjPerm Fi22.pair_D (ψ b : Fi22.J))
    (fun g hg => by
      rw [← map_mul, ← map_mul, hcomm g hg])
  rcases hσ with h | h
  · have h1 := Pair.conjPerm_injective Fi22.pair_D Fi22.center_eq_bot
      (h.trans (map_one (Pair.conjPerm Fi22.pair_D)).symm)
    exact Pair.ne_one Fi22.pair_D (ψ b).2 h1
  · have h1 := Pair.conjPerm_injective Fi22.pair_D Fi22.center_eq_bot h
    exact hne (ψ.injective (Subtype.ext h1)).symm

theorem fi24in_jR_comm_xb {k : J} (hk : k ∈ fi24inK) : jR k * xb = xb * jR k := by
  obtain ⟨hAB, hAt⟩ := mem_fi24inK_iff.1 hk
  have h1 : tR * (jR k * xb) = tR * (xb * jR k) := by
    calc tR * (jR k * xb) = (tR * jR k) * xb := by group
      _ = (jR k * tR) * xb := by rw [hAt]
      _ = jR k * (tR * xb) := by group
      _ = (tR * xb) * jR k := hAB
      _ = tR * (xb * jR k) := by group
  exact mul_left_cancel h1

theorem fi24in_mem_centralizer_iff {a c : R} (ha : a = tR ∨ a = xb) {x : J}
    (hjx : jR x = a * c) {k : J} (hk : k ∈ fi24inK) :
    k * (tJ * x) = (tJ * x) * k ↔ jR k * c = c * jR k := by
  obtain ⟨hAB, hAt⟩ := mem_fi24inK_iff.1 hk
  have hAx := fi24in_jR_comm_xb hk
  have hAa : Commute (jR k) a := by
    rcases ha with rfl | rfl
    · exact hAt
    · exact hAx
  have hA : Commute (jR k) (tR * xb) := hAB
  rw [← jR_injective.eq_iff, map_mul, map_mul, map_mul, map_mul, jR_tJ, hjx,
    hA.left_comm, mul_assoc (tR * xb) (a * c) (jR k), mul_right_inj, hAa.left_comm,
    mul_assoc a c (jR k), mul_right_inj]

theorem fi24in_alpha_lt {a c : R} (ha : a = tR ∨ a = xb) (hc : c ∈ W) {x : J}
    (hjx : jR x = a * c) :
    twoAdic (fi24inK ⊓ centralizer ({tJ * x} : Set J)) < twoAdic fi24inK := by
  have hstab : ∀ k : ↥fi24inK, (k • (⟨c, hc⟩ : ↥W) = ⟨c, hc⟩) ↔
      (k : J) * (tJ * x) = (tJ * x) * k := by
    intro k
    rw [fi24in_mem_centralizer_iff ha hjx k.2, Subtype.ext_iff, fi24in_smul_val,
      mul_inv_eq_iff_eq_mul]
  have hC : fi24inK ⊓ centralizer ({tJ * x} : Set J) =
      (MulAction.stabilizer ↥fi24inK (⟨c, hc⟩ : ↥W)).map fi24inK.subtype := by
    ext y
    constructor
    · intro hy
      obtain ⟨hyK, hyc⟩ := Subgroup.mem_inf.1 hy
      rw [Subgroup.mem_centralizer_singleton_iff] at hyc
      exact ⟨⟨y, hyK⟩, (MulAction.mem_stabilizer_iff).2 ((hstab ⟨y, hyK⟩).2 hyc), rfl⟩
    · rintro ⟨k, hk, rfl⟩
      refine Subgroup.mem_inf.2 ⟨k.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hstab k).1 ((MulAction.mem_stabilizer_iff).1 hk)
  have heven : Even ((fi24inK ⊓ centralizer ({tJ * x} : Set J)).relIndex fi24inK) := by
    rw [hC]
    have h2 : ((MulAction.stabilizer ↥fi24inK (⟨c, hc⟩ : ↥W)).map fi24inK.subtype).relIndex
        fi24inK = (MulAction.stabilizer ↥fi24inK (⟨c, hc⟩ : ↥W)).index := by
      show (((MulAction.stabilizer ↥fi24inK (⟨c, hc⟩ : ↥W)).map fi24inK.subtype).comap
        fi24inK.subtype).index = _
      rw [Subgroup.comap_map_eq_self_of_injective fi24inK.subtype_injective]
    rw [h2]
    have := fi24in_pretransitive
    exact fi24in_even_index_stabilizer_of_transitive ⟨1755, by rw [fi24in_card_W]⟩ _
  exact fi24in_twoAdic_lt_of_even_relIndex inf_le_left heven

theorem fi24in_exists_not_commute {c : R} (hc : c ∈ W) :
    ∃ k : J, k ∈ fi24inK ∧ jR k * c ≠ c * jR k := by
  by_contra h
  push Not at h
  have hz : tR * c ∈ (JR : Subgroup R) := tR_mul_mem_JR_of_mem hc.1.1
  have hcent := fi24in_cent_LE hz (fun ℓ hℓ => by
    obtain ⟨k, hk, rfl⟩ := fi24in_exists_of_mem_LE hℓ
    have h1 := h k hk
    have h2 := (mem_fi24inK_iff.1 hk).2
    calc tR * c * jR k = tR * (c * jR k) := by group
      _ = tR * (jR k * c) := by rw [h1]
      _ = (tR * jR k) * c := by group
      _ = (jR k * tR) * c := by rw [h2]
      _ = jR k * (tR * c) := by group)
  rcases hcent with h1 | h1
  · exact hc.1.2.1 (by
      calc c = tR * (tR * c) := (tR_mul_tR_mul c).symm
        _ = tR := by rw [h1, mul_one])
  · exact hc.2.2.1 (by
      calc c = tR * (tR * c) := (tR_mul_tR_mul c).symm
        _ = tR * (tR * xb) := by rw [h1]
        _ = xb := tR_mul_tR_mul xb)

theorem fi24in_conj_comm_iff {X : Type*} [Group X] (g u v : X) :
    g⁻¹ * u * g * v = v * (g⁻¹ * u * g) ↔ u * (g * v * g⁻¹) = g * v * g⁻¹ * u := by
  constructor
  · intro h
    calc u * (g * v * g⁻¹) = g * (g⁻¹ * u * g * v) * g⁻¹ := by group
      _ = g * (v * (g⁻¹ * u * g)) * g⁻¹ := by rw [h]
      _ = g * v * g⁻¹ * u := by group
  · intro h
    calc g⁻¹ * u * g * v = g⁻¹ * (u * (g * v * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * v * g⁻¹ * u) * g := by rw [h]
      _ = v * (g⁻¹ * u * g) := by group

theorem fi24in_beta_points {Y : R}
    (h₁ : tR * (Y * tR * Y⁻¹) = Y * tR * Y⁻¹ * tR)
    (h₂ : tR * (Y * xb * Y⁻¹) = Y * xb * Y⁻¹ * tR)
    (h₃ : xb * (Y * tR * Y⁻¹) = Y * tR * Y⁻¹ * xb)
    (h₄ : xb * (Y * xb * Y⁻¹) = Y * xb * Y⁻¹ * xb)
    (n₁ : tR ≠ Y * tR * Y⁻¹) (n₂ : tR ≠ Y * xb * Y⁻¹) (n₃ : xb ≠ Y * tR * Y⁻¹)
    (n₄ : xb ≠ Y * xb * Y⁻¹) : Y⁻¹ * tR * Y ∈ W ∧ Y⁻¹ * xb * Y ∈ W := by
  have hT : Y⁻¹ * tR * Y ∈ D24 := by
    have := Pair.conj_mem pair_R tR_mem_D24 Y⁻¹
    rwa [inv_inv] at this
  have hX : Y⁻¹ * xb * Y ∈ D24 := by
    have := Pair.conj_mem pair_R xb_mem_D24 Y⁻¹
    rwa [inv_inv] at this
  refine ⟨⟨⟨hT, fun h => n₁ ?_, (fi24in_conj_comm_iff Y tR tR).2 h₁⟩,
      ⟨hT, fun h => n₂ ?_, (fi24in_conj_comm_iff Y tR xb).2 h₂⟩⟩,
    ⟨⟨hX, fun h => n₃ ?_, (fi24in_conj_comm_iff Y xb tR).2 h₃⟩,
      ⟨hX, fun h => n₄ ?_, (fi24in_conj_comm_iff Y xb xb).2 h₄⟩⟩⟩
  · calc tR = Y * (Y⁻¹ * tR * Y) * Y⁻¹ := by group
      _ = Y * tR * Y⁻¹ := by rw [h]
  · calc tR = Y * (Y⁻¹ * tR * Y) * Y⁻¹ := by group
      _ = Y * xb * Y⁻¹ := by rw [h]
  · calc xb = Y * (Y⁻¹ * xb * Y) * Y⁻¹ := by group
      _ = Y * tR * Y⁻¹ := by rw [h]
  · calc xb = Y * (Y⁻¹ * xb * Y) * Y⁻¹ := by group
      _ = Y * xb * Y⁻¹ := by rw [h]

theorem fi24in_generate_of_W (y : J) (hT : (jR y)⁻¹ * tR * jR y ∈ W)
    (hX : (jR y)⁻¹ * xb * jR y ∈ W) : fi24inK ⊔ fi24inK.map (conjHom y) = ⊤ := by
  have hne : (⟨(jR y)⁻¹ * tR * jR y, hT⟩ : ↥W) ≠ ⟨(jR y)⁻¹ * xb * jR y, hX⟩ := fun h => by
    have h1 := Subtype.mk.inj h
    exact tR_ne_xb (by
      calc tR = jR y * ((jR y)⁻¹ * tR * jR y) * (jR y)⁻¹ := by group
        _ = jR y * ((jR y)⁻¹ * xb * jR y) * (jR y)⁻¹ := by rw [h1]
        _ = xb := by group)
  obtain ⟨k, hk1, hk2⟩ := fi24in_exists_fix_move hne
  have hk1' : jR (k : J) * ((jR y)⁻¹ * tR * jR y) * (jR (k : J))⁻¹ =
      (jR y)⁻¹ * tR * jR y := by
    have := congrArg Subtype.val hk1
    rwa [fi24in_smul_val] at this
  have hk2' : jR (k : J) * ((jR y)⁻¹ * xb * jR y) * (jR (k : J))⁻¹ ≠
      (jR y)⁻¹ * xb * jR y := fun h => hk2 (Subtype.ext (by rw [fi24in_smul_val]; exact h))
  have hmem : y * (k : J) * y⁻¹ ∈ fi24inK.map (conjHom y) := ⟨k, k.2, conjHom_apply y k⟩
  have hg₀M : y * (k : J) * y⁻¹ ∈ Fi24.M := by
    rw [← commute_tR_iff, map_mul, map_mul, map_inv]
    have hKT : jR (k : J) * ((jR y)⁻¹ * tR * jR y) = (jR y)⁻¹ * tR * jR y * jR (k : J) := by
      rw [mul_inv_eq_iff_eq_mul] at hk1'
      exact hk1'
    calc jR y * jR (k : J) * (jR y)⁻¹ * tR =
        jR y * (jR (k : J) * ((jR y)⁻¹ * tR * jR y)) * (jR y)⁻¹ := by group
      _ = jR y * ((jR y)⁻¹ * tR * jR y * jR (k : J)) * (jR y)⁻¹ := by rw [hKT]
      _ = tR * (jR y * jR (k : J) * (jR y)⁻¹) := by group
  have hg₀K : y * (k : J) * y⁻¹ ∉ fi24inK := by
    intro h
    have h1 := (mem_fi24inK_iff.1 h).1
    rw [map_mul, map_mul, map_inv] at h1
    have h2 : jR (k : J) * ((jR y)⁻¹ * tR * jR y * ((jR y)⁻¹ * xb * jR y)) =
        (jR y)⁻¹ * tR * jR y * ((jR y)⁻¹ * xb * jR y) * jR (k : J) := by
      calc jR (k : J) * ((jR y)⁻¹ * tR * jR y * ((jR y)⁻¹ * xb * jR y)) =
          (jR y)⁻¹ * (jR y * jR (k : J) * (jR y)⁻¹ * (tR * xb)) * jR y := by group
        _ = (jR y)⁻¹ * ((tR * xb) * (jR y * jR (k : J) * (jR y)⁻¹)) * jR y := by rw [h1]
        _ = _ := by group
    apply hk2'
    have hKT : jR (k : J) * ((jR y)⁻¹ * tR * jR y) = (jR y)⁻¹ * tR * jR y * jR (k : J) := by
      rw [mul_inv_eq_iff_eq_mul] at hk1'
      exact hk1'
    have h4 : (jR y)⁻¹ * tR * jR y * (jR (k : J) * ((jR y)⁻¹ * xb * jR y)) =
        (jR y)⁻¹ * tR * jR y * ((jR y)⁻¹ * xb * jR y * jR (k : J)) := by
      calc (jR y)⁻¹ * tR * jR y * (jR (k : J) * ((jR y)⁻¹ * xb * jR y)) =
          jR (k : J) * ((jR y)⁻¹ * tR * jR y) * ((jR y)⁻¹ * xb * jR y) := by
            rw [hKT]; group
        _ = jR (k : J) * ((jR y)⁻¹ * tR * jR y * ((jR y)⁻¹ * xb * jR y)) := by group
        _ = _ := h2
        _ = _ := by group
    have h5 := mul_left_cancel h4
    rw [mul_inv_eq_iff_eq_mul]
    exact h5
  have hsb : fi23EquivM ⟨tJ, tJ_mem_M⟩ ∈ Fi23.D23 := by
    rw [fi23EquivM_tJ]
    exact sb_mem_D23
  have hKX : fi24inK ≤ fi24inK ⊔ fi24inK.map (conjHom y) := le_sup_left
  have hmax := maximal_L tJ_mem_M hsb ((fi24inK ⊔ fi24inK.map (conjHom y)) ⊓ Fi24.M)
    (le_inf hKX inf_le_right) inf_le_right
  rcases hmax with h | h
  · exfalso
    have hg : y * (k : J) * y⁻¹ ∈ (fi24inK ⊔ fi24inK.map (conjHom y)) ⊓ Fi24.M :=
      Subgroup.mem_inf.2 ⟨(le_sup_right : fi24inK.map (conjHom y) ≤ _) hmem, hg₀M⟩
    rw [h] at hg
    exact hg₀K hg
  · have hMX : Fi24.M ≤ fi24inK ⊔ fi24inK.map (conjHom y) :=
      calc Fi24.M = (fi24inK ⊔ fi24inK.map (conjHom y)) ⊓ Fi24.M := h.symm
        _ ≤ _ := inf_le_left
    have hnXM : ¬ fi24inK ⊔ fi24inK.map (conjHom y) ≤ Fi24.M := by
      intro hle
      obtain ⟨k₁, hk₁, hk₁c⟩ := fi24in_exists_not_commute hT
      have hg₁ : y * k₁ * y⁻¹ ∈ fi24inK ⊔ fi24inK.map (conjHom y) :=
        (le_sup_right : fi24inK.map (conjHom y) ≤ _) ⟨k₁, hk₁, conjHom_apply y k₁⟩
      have hg₁M := (commute_tR_iff _).2 (hle hg₁)
      rw [map_mul, map_mul, map_inv] at hg₁M
      exact hk₁c (((fi24in_conj_comm_iff (jR y) tR (jR k₁)).2 hg₁M.symm).symm)
    exact isCoatom_M.2 _ (lt_of_le_not_ge hMX hnXM)

theorem fi24in_alpha_core {a c : R} (ha : a = tR ∨ a = xb) (hcD : c ∈ D24) (hca : c ≠ a) {x : J}
    (hxK : x ∈ fi24inK) (hxt : x ≠ tJ) (hjx : jR x = a * c) : c ∈ W := by
  have haD : a ∈ D24 := by
    rcases ha with rfl | rfl
    · exact tR_mem_D24
    · exact xb_mem_D24
  have haa : a * a = 1 := Pair.mul_self pair_R haD
  have hxT : Commute (jR x) tR := (mem_fi24inK_iff.1 hxK).2
  have hxX : Commute (jR x) xb := fi24in_jR_comm_xb hxK
  have haT : Commute a tR := by
    rcases ha with rfl | rfl
    · exact Commute.refl _
    · exact tR_xb_comm.symm
  have haX : Commute a xb := by
    rcases ha with rfl | rfl
    · exact tR_xb_comm
    · exact Commute.refl _
  have hc : c = a * jR x := by rw [hjx, ← mul_assoc, haa, one_mul]
  have hcT : c * tR = tR * c := by rw [hc]; exact (haT.mul_left hxT).eq
  have hcX : c * xb = xb * c := by rw [hc]; exact (haX.mul_left hxX).eq
  have hct : c ≠ tR ∧ c ≠ xb := by
    rcases ha with rfl | rfl
    · refine ⟨hca, fun h => hxt ?_⟩
      apply jR_injective
      rw [hjx, h, jR_tJ]
    · refine ⟨fun h => hxt ?_, hca⟩
      apply jR_injective
      rw [hjx, h, jR_tJ]
      exact tR_xb_comm.symm
  exact ⟨⟨hcD, hct.1, hcT⟩, ⟨hcD, hct.2, hcX⟩⟩

theorem fi24in_generate_pinned
    (hw : ∃ v₀ ∈ vCandidates fi24inK tJ,
      twoAdic fi24inK ≤ twoAdic (fi24inK ⊓ centralizer ({v₀} : Set J)))
    (y : J) (hy : y * tJ * y⁻¹ ∈ vPairs (⊤ : Subgroup J) fi24inK tJ) :
    fi24inK ⊔ fi24inK.map (conjHom y) = ⊤ := by
  obtain ⟨v, hvmax, hxv, -⟩ := hy
  obtain ⟨v₀, hv₀, hv₀2⟩ := hw
  have hvmax' := hvmax.2 v₀ hv₀
  obtain ⟨hvK, hv1, hvt, hvv⟩ := fi24in_mem_vCandidates_K_iff.1 hvmax.1
  obtain ⟨x, hx⟩ : ∃ x : J, x = y * tJ * y⁻¹ := ⟨_, rfl⟩
  have hxv' : x = tJ * v := hx.trans hxv
  have hxK : x ∈ fi24inK := by
    rw [hxv']
    exact fi24inK.mul_mem fi24in_tJ_mem_K hvK
  have hxt : x ≠ tJ := fun h => hv1 (by
    have : tJ * v = tJ * 1 := by rw [← hxv', h, mul_one]
    exact mul_left_cancel this)
  have hvx : tJ * x = v := by rw [hxv', ← mul_assoc, tJ_mul_tJ, one_mul]
  have key : ∀ a c : R, (a = tR ∨ a = xb) → c ∈ D24 → c ≠ a → jR x = a * c → False := by
    intro a c ha hcD hca hjx
    have hlt := fi24in_alpha_lt ha (fi24in_alpha_core ha hcD hca hxK hxt hjx) hjx
    rw [hvx] at hlt
    exact absurd (hv₀2.trans hvmax') (not_le.2 hlt)
  have hT₂ : jR y * tR * (jR y)⁻¹ ∈ D24 := Pair.conj_mem pair_R tR_mem_D24 (jR y)
  have hT₃ : jR y * xb * (jR y)⁻¹ ∈ LocalClass D24 (jR y * tR * (jR y)⁻¹) :=
    (Pair.conj_mem_localClass_iff pair_R (jR y)).2 xb_mem_localClass
  have hjx : jR x = (jR y * tR * (jR y)⁻¹) * (jR y * xb * (jR y)⁻¹) := by
    rw [hx, map_mul, map_mul, map_inv, jR_tJ]
    group
  have hne23 : jR y * tR * (jR y)⁻¹ ≠ jR y * xb * (jR y)⁻¹ := hT₃.2.1.symm
  have hc23 : (jR y * tR * (jR y)⁻¹) * (jR y * xb * (jR y)⁻¹) =
      (jR y * xb * (jR y)⁻¹) * (jR y * tR * (jR y)⁻¹) := hT₃.2.2.symm
  have hdT := (commute_mul_iff pair_R hT₂ hT₃.1 hne23 hc23 tR_mem_D24).1
    (by rw [← hjx]; exact (mem_fi24inK_iff.1 hxK).2.symm)
  have hdX := (commute_mul_iff pair_R hT₂ hT₃.1 hne23 hc23 xb_mem_D24).1
    (by rw [← hjx]; exact (fi24in_jR_comm_xb hxK).symm)
  by_cases hα : tR = jR y * tR * (jR y)⁻¹ ∨ tR = jR y * xb * (jR y)⁻¹ ∨
      xb = jR y * tR * (jR y)⁻¹ ∨ xb = jR y * xb * (jR y)⁻¹
  · exfalso
    rcases hα with h | h | h | h
    · refine key tR _ (Or.inl rfl) hT₃.1 (fun h' => hne23 (h.symm.trans h'.symm)) ?_
      rw [hjx, ← h]
    · refine key tR _ (Or.inl rfl) hT₂ (fun h' => hne23 (h'.trans h)) ?_
      have e := hc23
      rw [← h] at e
      rw [hjx, ← h]
      exact e
    · refine key xb _ (Or.inr rfl) hT₃.1 (fun h' => hne23 (h.symm.trans h'.symm)) ?_
      rw [hjx, ← h]
    · refine key xb _ (Or.inr rfl) hT₂ (fun h' => hne23 (h'.trans h)) ?_
      have e := hc23
      rw [← h] at e
      rw [hjx, ← h]
      exact e
  · push Not at hα
    obtain ⟨n₁, n₂, n₃, n₄⟩ := hα
    have hT' := (hdT.resolve_left n₁).resolve_left n₂
    have hX' := (hdX.resolve_left n₃).resolve_left n₄
    obtain ⟨hT'', hX''⟩ := fi24in_beta_points (Y := jR y) hT'.1.2.2 hT'.2.2.2 hX'.1.2.2 hX'.2.2.2
      n₁ n₂ n₃ n₄
    exact fi24in_generate_of_W y hT'' hX''

end CFSG.EvenSporadicStandard.Induction
