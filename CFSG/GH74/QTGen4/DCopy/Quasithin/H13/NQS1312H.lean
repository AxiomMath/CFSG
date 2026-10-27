module

public import CFSG.Quasithin.H13.NQS1312H
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3Local1332

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3.NLine

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.SteinbergCB
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem normalizer_le_of_le_Q_F4 (h1332 : Stmt13_3_2_F4) {T L : Subgroup G} (hH : QTH13 G T L)
    {P : Subgroup G} (hP1 : P ≠ ⊥) (hP2 : IsPGroup 2 P) (hPQ : P ≤ pCoreOf 2 (L ⊔ T))
    (hLT : L ⊔ T ≤ normalizer (P : Set G)) : normalizer (P : Set G) ≤ normalizer (L : Set G) :=
  ((u3_original_local_maximality_and_unique_normalizer_of_1332_F4 h1332 hH).2.2.2.2 P hP1 hP2
    (hPQ.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 _)) hLT).1

theorem normalizer_le_of_char_F4 (h1332 : Stmt13_3_2_F4) {T L : Subgroup G} (hH : QTH13 G T L)
    {C : Subgroup G} (hC1 : C ≠ ⊥) (hCQ : C ≤ pCoreOf 2 (L ⊔ T))
    (hCc : (C.subgroupOf (pCoreOf 2 (L ⊔ T))).Characteristic) :
    normalizer (C : Set G) ≤ normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine normalizer_le_of_le_Q_F4 h1332 hH hC1
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le hCQ) hCQ ?_
  have h1 : L ⊔ T ≤ normalizer (pCoreOf 2 (L ⊔ T) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have h2 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    (C.subgroupOf (pCoreOf 2 (L ⊔ T)))
  rw [Subgroup.map_subgroupOf_eq_of_le hCQ] at h2
  exact h1.trans h2

theorem hypC23_line_F4
    (h1332 : Stmt13_3_2_F4) {T L V : Subgroup G} {z : G} [IsElementaryAbelian 2 V]
    (hH : QTH13 G T L) (hF : QTU3InternalFrame T L V z) {Φ : Additive V ≃ₗ[ZMod 2] W6}
    (hΦLs : ∀ j ∈ J6, ∃ (l : G) (hl : l ∈ L), linConj Φ
      (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨l, hF.2.2.2.2.2.2.1 hl⟩) = glLin j)
    (hΦN : ∀ n : normalizer (V : Set G), ∃ k ∈ N6,
      linConj Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl n) = glLin k) :
    HypC23 (centralizer ({ptOf Φ (vecOf 15), ptOf Φ (vecOf 52)} : Set G)) (pCoreOf 2 (L ⊔ T))
      (centralizer ({ptOf Φ (vecOf 15), ptOf Φ (vecOf 52)} : Set G) ⊓
        normalizer (L : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTL, hVT, hVe, hV64, hVQ, -, hLV, hTV, -, -, hTC, -, -⟩ := id hF
  obtain ⟨-, -, -, -, hTI⟩ := u3_selected_local_normalizer_and_TI_of_1332_F4 h1332 hH hF
  set u₁ := ptOf Φ (vecOf 15) with hu₁
  set v₁ := ptOf Φ (vecOf 52) with hv₁
  set H := centralizer ({u₁, v₁} : Set G) with hHdef
  set M := normalizer (L : Set G) with hM
  set Q := pCoreOf 2 (L ⊔ T) with hQ
  have hu₁V : u₁ ∈ V := ptOf_mem _
  have hv₁V : v₁ ∈ V := ptOf_mem _
  have hu₁1 : u₁ ≠ 1 := by
    intro h
    have h0 : vecOf 15 = (0 : W6) := ptOf_injective (h.trans ptOf_zero.symm)
    have := vecOf_injective (by norm_num : 15 < 64) (by norm_num : 0 < 64)
      (h0.trans vecOf_zero.symm)
    norm_num at this
  have hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy => by
    have := hVe.toIsMulCommutative
    exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : V) ⟨y, hy⟩)
  have hset : ({u₁, v₁} : Set G) ⊆ V := by
    rintro _ (rfl | rfl)
    exacts [hu₁V, hv₁V]
  have hCVH : centralizer (V : Set G) ≤ H := Subgroup.centralizer_le hset
  have hHu : H ≤ centralizer ({u₁} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 (Set.mem_insert _ _))
  have hHM : H ⊓ M ≤ normalizer (V : Set G) := fun x hx =>
    hTI u₁ hu₁V hu₁1 ⟨hx.2, hHu hx.1⟩

  have hQp : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hQT : Q ≤ T := hTC ▸ inf_le_left
  have hQC : Q ≤ centralizer (V : Set G) := hTC ▸ inf_le_right
  have hQH : Q ≤ H := hQC.trans hCVH
  have hQM : Q ≤ M := hQT.trans hTL
  have hV1 : V ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hV64
    norm_num at hV64
  have hQ1 : Q ≠ ⊥ := fun h => hV1 (le_bot_iff.1 (h ▸ hVQ))
  have hNQ : normalizer (Q : Set G) ≤ M := normalizer_le_of_le_Q_F4 h1332 hH hQ1 hQp le_rfl
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)

  obtain ⟨k₁, hk₁L, hk₁τ, hk₁15, hk₁52⟩ := exists_k_mem_L hLV hΦLs
  have hmemH : ∀ x : G, x * u₁ * x⁻¹ = u₁ → x * v₁ * x⁻¹ = v₁ → x ∈ H := by
    intro x h15 h52
    rw [hHdef, mem_centralizer_iff]
    rintro _ (rfl | rfl)
    · calc u₁ * x = x * u₁ * x⁻¹ * x := by rw [h15]
        _ = x * u₁ := by group
    · calc v₁ * x = x * v₁ * x⁻¹ * x := by rw [h52]
        _ = x * v₁ := by group
  have hk₁H : k₁ ∈ H := hmemH k₁ hk₁15 hk₁52
  have hk₁Q : k₁ ∈ normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (le_sup_left (b := T) hk₁L)
  have hcen : ∀ x ∈ H, x * u₁ * x⁻¹ = u₁ ∧ x * v₁ * x⁻¹ = v₁ := by
    intro x hx
    rw [hHdef, mem_centralizer_iff] at hx
    refine ⟨?_, ?_⟩
    · rw [← hx u₁ (Set.mem_insert _ _)]; group
    · rw [← hx v₁ (Set.mem_insert_of_mem _ rfl)]; group
  refine
    { sqtk := ?_
      radical := ⟨hQH, hQ1, ?_⟩
      le := inf_le_left
      cgs := ?_
      sylow := ?_ }
  ·
    have := hH.simple
    have hloc := (qtkeCore_of_cat hH.nonabelian hH.qtke).1
    refine InternalSec.sqtkGroup_of_localSQTK hloc ?_
    have hu₁2 : u₁ ^ 2 = 1 := by
      have := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V) u₁ hu₁V
      simpa using this
    have hZ : zpowers u₁ ≤ pCoreOf 2 H := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_
        (isPGroup_zpowers_of_sq hu₁2)
      · rw [zpowers_le]
        exact hmemH u₁ (by group) (by rw [hcomm u₁ hu₁V v₁ hv₁V]; group)
      · intro h hh
        rw [mem_normalizer_iff]
        intro y
        exact (conj_mem_zpowers_iff (hcen h hh).1).symm
    intro h0
    apply hu₁1
    have := hZ (mem_zpowers u₁)
    rw [h0, Subgroup.mem_bot] at this
    exact this
  ·
    set R := pCoreOf 2 (H ⊓ normalizer (Q : Set G)) with hR
    apply le_antisymm
    · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (le_inf hQH Subgroup.le_normalizer)
        inf_le_right hQp
    · have hRp : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
      have hRle : R ≤ H ⊓ normalizer (Q : Set G) := CFSG.LieType.BorelTits.pCoreOf_le 2 _
      have hRHM : R ≤ H ⊓ M :=
        le_inf (hRle.trans inf_le_left) (hRle.trans (inf_le_right.trans hNQ))
      have hkR : ∀ r ∈ R, k₁ * r * k₁⁻¹ ∈ R := fun r hr =>
        (mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
          (Subgroup.mem_inf.2 ⟨hk₁H, hk₁Q⟩)) r).1 hr
      have hRCV : R ≤ centralizer (V : Set G) :=
        le_centralizer_of_isPGroup hΦN (hLV hk₁L) (tau_eq_iff.2 hk₁τ) hRp (hRHM.trans hHM)
          (fun r hr => hcen r (hRle hr).1) hkR
      have hRQ : IsPGroup 2 (R ⊔ Q : Subgroup G) :=
        IsPGroup.to_sup_of_normal_right' hRp hQp (hRle.trans inf_le_right)
      have hle : R ⊔ Q ≤ M ⊓ centralizer (V : Set G) :=
        sup_le (le_inf (hRHM.trans inf_le_right) hRCV) (le_inf hQM hQC)
      have heq := eq_of_isSylowTwoOf_le (isSylowTwoOf_Q hH hF) le_sup_right hle hRQ
      exact le_sup_left.trans heq.le
  ·
    refine iSup_le fun C => iSup_le fun hCQ => iSup_le fun hC1 => iSup_le fun hCc => ?_
    exact inf_le_inf_left H (normalizer_le_of_char_F4 h1332 hH hC1 hCQ hCc)
  ·
    have hcl : conjClosure Q (H ⊓ M) ≤ M ⊓ centralizer (V : Set G) := by
      rw [conjClosure, Subgroup.closure_le]
      rintro _ ⟨h, hh, q, hq, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_inf]
      refine ⟨M.mul_mem (M.mul_mem hh.2 (hQM hq)) (M.inv_mem hh.2), ?_⟩
      exact (mem_normalizer_iff.1 (normalizer_le_normalizer_centralizer V (hHM hh)) q).1 (hQC hq)
    have hQcl : Q ≤ conjClosure Q (H ⊓ M) := fun q hq =>
      Subgroup.subset_closure ⟨1, one_mem _, q, hq, by group⟩
    exact isSylowTwoOf_of_le_of_le (isSylowTwoOf_Q hH hF) hQcl hcl

end CFSG.Quasithin.H13.U3.NLine
