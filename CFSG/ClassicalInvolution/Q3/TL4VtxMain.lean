module

public import CFSG.ClassicalInvolution.Q3.TL4VtxLay
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.RecogE4
public import CFSG.ClassicalInvolution.Q3.TL4OddFrMem
public import CFSG.ClassicalInvolution.Q3.TL4VtxDich

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Asc77.T8 (XMem)
open scoped commutatorElement

@[expose] def E4AutOddFreeR : Prop :=
  ∀ (M : Type) [Group M] [Finite M], PhilipHall.QuaternionBridge.ExLie M → Q3NM.AutOddFree M

namespace Vtx

section Image

variable {Q : Type} [Group Q] [Finite Q]

omit [Finite Q] in
theorem alphaOf_inducedImage_eq_bot_of_autOddFree {L : Subgroup Q} (hL : Q3NM.AutOddFree ↥L)
    {A : Subgroup Q} (hA2 : ∀ x ∈ A, x * x = 1) {x : Q} (hxA : x ∈ A)
    (hxN : x ∈ Subgroup.normalizer (L : Set Q)) (hx1 : toInducedAutOn L ⟨x, hxN⟩ ≠ 1) :
    alphaOf (inducedImage L A) = ⊥ := by
  refine Q3NM.alphaOf_eq_bot_of_on L (fun _ => True) (hL.on _) _ ?_
    ⟨_, Lemma52Proof.toInducedAutOn_mem_inducedImage L A hxA hxN, hx1⟩ fun _ _ _ => trivial
  rintro _ ⟨w, hw, rfl⟩
  have hww : w * w = 1 := Subtype.ext (hA2 _ (Subgroup.mem_subgroupOf.mp hw))
  rw [← map_mul, hww, map_one]

omit [Finite Q] in
theorem inducedImage_closure_le {L : Subgroup Q} {S : Set Q}
    (hS : S ⊆ Subgroup.normalizer (L : Set Q)) (T : Subgroup ↥(inducedAutOn L))
    (hgen : ∀ s (hs : s ∈ S), toInducedAutOn L ⟨s, hS hs⟩ ∈ T) :
    inducedImage L (Subgroup.closure S) ≤ T := by
  have hle : Subgroup.closure S ≤
      (T.comap (toInducedAutOn L)).map (Subgroup.normalizer (L : Set Q)).subtype := by
    rw [Subgroup.closure_le]
    intro s hs
    exact ⟨⟨s, hS hs⟩, hgen s hs, rfl⟩
  rintro _ ⟨m, hm, rfl⟩
  obtain ⟨m', hm', he⟩ := hle (Subgroup.mem_subgroupOf.mp hm)
  have e : m' = m := Subtype.ext he
  rw [← e]
  exact hm'

end Image

section Vertex

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem modOdd_closure_le {c : G} {S : Set G} (hS : S ⊆ Subgroup.centralizer ({c} : Set G)) :
    modOdd c (Subgroup.closure S) ≤
      Subgroup.closure {x | ∃ s, ∃ hs : s ∈ S, oddQuotMk c ⟨s, hS hs⟩ = x} := by
  have hCl : Subgroup.closure S ≤ Subgroup.centralizer ({c} : Set G) :=
    (Subgroup.closure_le _).mpr hS
  rintro _ ⟨k, hk, rfl⟩
  have key : ∀ (g : G) (hg : g ∈ Subgroup.closure S), oddQuotMk c ⟨g, hCl hg⟩ ∈
      Subgroup.closure {x | ∃ s, ∃ hs : s ∈ S, oddQuotMk c ⟨s, hS hs⟩ = x} := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem s hs => exact Subgroup.subset_closure ⟨s, hs, rfl⟩
    | one =>
      have h1 : oddQuotMk c ⟨1, hCl (Subgroup.one_mem _)⟩ = 1 := map_one _
      rw [h1]
      exact Subgroup.one_mem _
    | mul a b ha hb iha ihb =>
      have hab : oddQuotMk c ⟨a * b, hCl (Subgroup.mul_mem _ ha hb)⟩ =
          oddQuotMk c ⟨a, hCl ha⟩ * oddQuotMk c ⟨b, hCl hb⟩ := map_mul (oddQuotMk c)
            (⟨a, hCl ha⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ⟨b, hCl hb⟩
      rw [hab]
      exact Subgroup.mul_mem _ iha ihb
    | inv a ha iha =>
      have hab : oddQuotMk c ⟨a⁻¹, hCl (Subgroup.inv_mem _ ha)⟩ =
          (oddQuotMk c ⟨a, hCl ha⟩)⁻¹ :=
        map_inv (oddQuotMk c) (⟨a, hCl ha⟩ : ↥(Subgroup.centralizer ({c} : Set G)))
      rw [hab]
      exact Subgroup.inv_mem _ iha
  have hk' : (k : G) ∈ Subgroup.closure S := Subgroup.mem_subgroupOf.mp hk
  have e : k = ⟨(k : G), hCl hk'⟩ := rfl
  rw [e]
  exact key k hk'

omit [Finite G] in
theorem oddQuotMk_self_mem_center (c : G) :
    oddQuotMk c ⟨c, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ ∈
      Subgroup.center (OddQuot c) := by
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective _ y
  change oddQuotMk c k * oddQuotMk c _ = oddQuotMk c _ * oddQuotMk c k
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp k.2)

omit [Finite G] in
theorem inducedImage_modOdd_eq {a b c : G} (haC : a ∈ Subgroup.centralizer ({c} : Set G))
    (hbC : b ∈ Subgroup.centralizer ({c} : Set G)) {L : Subgroup (OddQuot c)}
    (haN : oddQuotMk c ⟨a, haC⟩ ∈ Subgroup.normalizer (L : Set (OddQuot c)))
    (hbN : oddQuotMk c ⟨b, hbC⟩ ∈ Subgroup.normalizer (L : Set (OddQuot c))) :
    inducedImage L (modOdd c (Subgroup.closure {a, b, c})) =
      Subgroup.closure {toInducedAutOn L ⟨_, haN⟩, toInducedAutOn L ⟨_, hbN⟩} := by
  have hcC : c ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hS : ({a, b, c} : Set G) ⊆ Subgroup.centralizer ({c} : Set G) := by
    rintro w (rfl | rfl | rfl)
    exacts [haC, hbC, hcC]
  have hcZ := oddQuotMk_self_mem_center c
  have hcN : oddQuotMk c ⟨c, hcC⟩ ∈ Subgroup.normalizer (L : Set (OddQuot c)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [(Subgroup.mem_center_iff.mp hcZ y).symm, mul_inv_cancel_right]
  apply le_antisymm
  · have hmono : inducedImage L (modOdd c (Subgroup.closure {a, b, c})) ≤
        inducedImage L (Subgroup.closure
          {x | ∃ s, ∃ hs : s ∈ ({a, b, c} : Set G), oddQuotMk c ⟨s, hS hs⟩ = x}) :=
      Subgroup.map_mono fun _ hx => modOdd_closure_le hS hx
    refine hmono.trans (inducedImage_closure_le ?_ _ ?_)
    · rintro _ ⟨s, hs, rfl⟩
      rcases hs with rfl | rfl | rfl
      exacts [haN, hbN, hcN]
    · rintro _ ⟨s, hs, rfl⟩
      rcases hs with rfl | rfl | rfl
      · exact Subgroup.subset_closure (Set.mem_insert _ _)
      · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
      · rw [Lemma52Proof.toInducedAutOn_eq_one_of_commute L _ fun y _ =>
          (Subgroup.mem_center_iff.mp hcZ y).symm]
        exact Subgroup.one_mem _
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact Lemma52Proof.toInducedAutOn_mem_inducedImage L _
        (oddQuotMk_mem_modOdd (Subgroup.subset_closure (Set.mem_insert _ _)) haC) haN
    · exact Lemma52Proof.toInducedAutOn_mem_inducedImage L _
        (oddQuotMk_mem_modOdd (Subgroup.subset_closure
          (Set.mem_insert_of_mem _ (Set.mem_insert _ _))) hbC) hbN

variable {Ω : Set (Subgroup G)}

theorem classicalOrQuiet_of_hasLift (h : TypeRFam 3 Ω) {c : G} {M : Subgroup G}
    (hM : XMem Ω c M) {z : G} (hz : IsUniqueInvolution M z)
    (hzc : z ∈ Subgroup.centralizer ({c} : Set G))
    (hlift : TightHasLift (modOdd c (coreAt c M)) (oddQuotMk c ⟨z, hzc⟩)) :
    ClassicalOrQuiet c z hzc := by
  have hR := h.coreFamIn (x := c) (X := Subgroup.centralizer ({c} : Set G)) le_rfl
    fun _ ⟨L, _, hC⟩ => hC ▸ coreAt_le_centralizer c L
  have hRmem : (coreAt c M).subgroupOf (Subgroup.centralizer ({c} : Set G)) ∈
      restrictFamily (coreFam Ω c) (Subgroup.centralizer ({c} : Set G)) :=
    ⟨coreAt c M, coreAt_mem_coreFam hM, coreAt_le_centralizer c M, rfl⟩
  have hzR := isUniqueInvolution_subgroupOf (isUniqueInvolution_coreAt h hM hz)
    (coreAt_le_centralizer c M)
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2
    ↥((coreAt c M).subgroupOf (Subgroup.centralizer ({c} : Set G)))))
  have hd := tightDatum_of_mem hR hRmem hzR S
  have hdq := OddQ.datum (N := componentClassificationOddCore
    ↥(Subgroup.centralizer ({c} : Set G))) hd (CFSG.ComponentClassification.OddCore.odd_card _)
  have hg := OddQ.good_of hd (CFSG.ComponentClassification.OddCore.odd_card _)
    (hdq.good_of_hasLift hlift)
  obtain ⟨L', -, hL'⟩ := tightHasLift_of_good hd hg
  exact Or.inl ⟨_, isSectionMember3_map hL'⟩

end Vertex

end Vtx

end CFSG.ClassicalInvolution.Q3.TL4
