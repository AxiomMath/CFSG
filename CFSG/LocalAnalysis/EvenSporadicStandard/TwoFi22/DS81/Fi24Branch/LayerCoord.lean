module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.LayerBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Layer54NormChain

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

variable {B : Type} [Group B] [Finite B]

structure SelfCentAbelian (Rb : Subgroup B) : Prop where
  comm : ∀ a ∈ Rb, ∀ b ∈ Rb, a * b = b * a
  cent : centralizer (Rb : Set B) ≤ Rb
  le_layer : Rb ≤ CFSG.layer B

private lemma commute_coord_of_commute_layerMul (hodd : CFSG.pPrimeCore 2 B = ⊥)
    (h2 : CFSG.pCore 2 B = ⊥)
    {x g : ∀ K : CFSG.LocalCores.ComponentIndex B, K.1}
    (h : Commute (CFSG.LocalCores.layerMul B x) (CFSG.LocalCores.layerMul B g)) :
    ∀ K, Commute (x K : B) (g K : B) := by
  intro K
  have hker : x * g * (g * x)⁻¹ ∈ (CFSG.LocalCores.layerMul B).ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [h.eq]
    simp
  have hmem : (x * g * (g * x)⁻¹) K ∈ center K.1 :=
    CFSG.LocalCores.layerMul_ker_le hker K (Set.mem_univ K)
  rw [center_component_eq_bot hodd h2 K.2, Subgroup.mem_bot] at hmem
  have h1 : (x K : B) * (g K : B) * ((g K : B) * (x K : B))⁻¹ = 1 := by
    simpa using congrArg Subtype.val hmem
  show (x K : B) * (g K : B) = (g K : B) * (x K : B)
  exact mul_inv_eq_one.mp h1

private lemma coord_mem_of_mem (hodd : CFSG.pPrimeCore 2 B = ⊥) (h2 : CFSG.pCore 2 B = ⊥)
    {Rb : Subgroup B} (hR : SelfCentAbelian Rb) {r : B} (hr : r ∈ Rb)
    {x : ∀ K : CFSG.LocalCores.ComponentIndex B, K.1}
    (hx : CFSG.LocalCores.layerMul B x = r) :
    ∀ K, (x K : B) ∈ Rb := by
  intro K
  apply hR.cent
  rw [mem_centralizer_iff]
  intro s hs
  obtain ⟨g, hg⟩ := CFSG.LocalCores.exists_layerMul_eq (hR.le_layer hs)
  have hcomm : Commute (CFSG.LocalCores.layerMul B x) (CFSG.LocalCores.layerMul B g) := by
    rw [hx, hg]
    exact hR.comm r hr s hs
  have h1 := commute_coord_of_commute_layerMul hodd h2 hcomm K
  have h2' : Commute (x K : B) (CFSG.LocalCores.layerMul B g) :=
    (CFSG.LocalCores.commute_layerMul_iff g K (x K).2).mpr h1
  rw [hg] at h2'
  exact h2'.symm

theorem Rb_le_iSup_inf_component (hodd : CFSG.pPrimeCore 2 B = ⊥) (h2 : CFSG.pCore 2 B = ⊥)
    {Rb : Subgroup B} (hR : SelfCentAbelian Rb) :
    Rb ≤ ⨆ K : {K : Subgroup B // CFSG.IsComponent K}, (Rb ⊓ K.1) := by
  intro r hr
  obtain ⟨x, hx⟩ := CFSG.LocalCores.exists_layerMul_eq (hR.le_layer hr)
  rw [← hx]
  exact CFSG.LocalCores.layerMul_mem x fun K =>
    mem_iSup_of_mem K (mem_inf.mpr ⟨coord_mem_of_mem hodd h2 hR hr hx K, (x K).2⟩)

theorem Rb_inf_component_ne_bot (hodd : CFSG.pPrimeCore 2 B = ⊥) (h2 : CFSG.pCore 2 B = ⊥)
    {Rb : Subgroup B} (hR : SelfCentAbelian Rb) {K : Subgroup B} (hK : CFSG.IsComponent K) :
    Rb ⊓ K ≠ ⊥ := by
  intro hbot
  have hcent : K ≤ centralizer (Rb : Set B) := by
    intro k hk
    rw [mem_centralizer_iff]
    intro s hs
    obtain ⟨x, hx⟩ := CFSG.LocalCores.exists_layerMul_eq (hR.le_layer hs)
    have hxK : (x ⟨K, hK⟩ : B) ∈ Rb ⊓ K :=
      mem_inf.mpr ⟨coord_mem_of_mem hodd h2 hR hs hx ⟨K, hK⟩, (x ⟨K, hK⟩).2⟩
    rw [hbot] at hxK
    have hxK1 : (x ⟨K, hK⟩ : B) = 1 := by simpa using hxK
    have hcomm : Commute k (CFSG.LocalCores.layerMul B x) := by
      rw [CFSG.LocalCores.commute_layerMul_iff x ⟨K, hK⟩ hk, hxK1]
      exact Commute.one_right k
    rw [hx] at hcomm
    exact hcomm.symm
  have hKle : K ≤ Rb := hcent.trans hR.cent
  haveI : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
  haveI : Group.IsPerfect ↥K := hK.1.1
  have hcommK : IsMulCommutative ↥K :=
    IsMulCommutative.of_comm fun a b =>
      Subtype.ext (hR.comm (a : B) (hKle a.2) (b : B) (hKle b.2))
  exact Group.IsPerfect.not_isMulCommutative (↥K) hcommK

theorem card_components_le (hodd : CFSG.pPrimeCore 2 B = ⊥) (h2 : CFSG.pCore 2 B = ⊥)
    {Rb : Subgroup B} (hR : SelfCentAbelian Rb) (hcard : Nat.card ↥Rb ≤ 2 ^ 12) :
    Nat.card {K : Subgroup B // CFSG.IsComponent K} ≤ 12 := by
  classical
  choose a ha using fun K : {K : Subgroup B // CFSG.IsComponent K} =>
    Subgroup.ne_bot_iff_exists_ne_one.mp (Rb_inf_component_ne_bot hodd h2 hR K.2)
  let n : ℕ := Fintype.card {K : Subgroup B // CFSG.IsComponent K}
  let e : Fin n ≃ {K : Subgroup B // CFSG.IsComponent K} :=
    (Fintype.equivFin {K : Subgroup B // CFSG.IsComponent K}).symm
  let Q : ℕ → Subgroup B := fun j => if h : j < n then (e ⟨j, h⟩).1 else ⊥
  let s : ℕ → B := fun j => if h : j < n then (a (e ⟨j, h⟩)).1 else 1
  have hs : ∀ j < n, s j ∈ Q j := by
    intro j hj
    simp only [s, Q, dif_pos hj]
    exact (a (e ⟨j, hj⟩)).2.2
  have hmemRb : ∀ j < n, s j ∈ Rb := by
    intro j hj
    simp only [s, dif_pos hj]
    exact (a (e ⟨j, hj⟩)).2.1
  have hcomm : ∀ j < n, ∀ k < n, j ≠ k → ∀ x ∈ Q j, ∀ y ∈ Q k, x * y = y * x := by
    intro j hj k hk hjk x hx y hy
    have hne : e ⟨j, hj⟩ ≠ e ⟨k, hk⟩ := fun heq =>
      hjk (congrArg Fin.val (e.injective heq))
    have hxy := CFSG.LocalCores.componentIndex_commute hne x y
    simp only [Q, dif_pos hj, dif_pos hk] at hx hy
    exact hxy hx hy
  have hnc : ∀ j < n, ∃ q ∈ Q j, s j * q ≠ q * s j := by
    intro j hj
    let b : ↥(e ⟨j, hj⟩).1 := ⟨(a (e ⟨j, hj⟩)).1, (a (e ⟨j, hj⟩)).2.2⟩
    have hbne : b ≠ 1 := by
      intro h
      have h1 : (a (e ⟨j, hj⟩)).1 = 1 :=
        congrArg (fun y : ↥(e ⟨j, hj⟩).1 => (y : B)) h
      exact ha (e ⟨j, hj⟩) (Subtype.ext h1)
    have hnotmem : b ∉ center ↥(e ⟨j, hj⟩).1 := by
      rw [center_component_eq_bot hodd h2 (e ⟨j, hj⟩).2]
      exact fun h => hbne (Subgroup.mem_bot.mp h)
    rw [mem_center_iff] at hnotmem
    push Not at hnotmem
    obtain ⟨g, hgne⟩ := hnotmem
    refine ⟨(g : B), ?_, ?_⟩
    · simp only [Q, dif_pos hj]
      exact g.2
    · simp only [s, dif_pos hj]
      intro heq
      exact hgne (Subtype.ext heq.symm)
  have htwo := CFSG.EvenSporadicStandard.TwoB.two_pow_le_card_closure_of_noncomm Q s n hs hcomm hnc
  have hcl_le : closure (s '' Set.Iio n) ≤ Rb := by
    rw [closure_le]
    rintro _ ⟨j, hj, rfl⟩
    exact hmemRb j hj
  have hle : Nat.card ↥(closure (s '' Set.Iio n) : Subgroup B) ≤ Nat.card ↥Rb :=
    Subgroup.card_le_of_le hcl_le
  have hmain : 2 ^ n ≤ 2 ^ 12 := le_trans htwo (le_trans hle hcard)
  rw [Nat.card_eq_fintype_card]
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hmain

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
