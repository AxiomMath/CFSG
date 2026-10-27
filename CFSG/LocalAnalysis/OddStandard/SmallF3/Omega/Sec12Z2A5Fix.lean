module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z2A5Cent
public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.Dichotomy
public import CFSG.LocalAnalysis.EvenBN.GMSK.FixedRootDatum
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.Sylow

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.EvenSporadicStandard.SolomonRed CFSG.LocalAnalysis.EvenBN.GMSK

variable {Y : Type} [Group Y] {τ : Y}

private theorem z2a5_socle_cent (h : Z2A5Hyp Y τ) {S : Subgroup Y} [S.Normal]
    (hbot : oTwoRes (centralizer ({τ} : Set Y)) ⊓ (S ⊓ centralizer ({τ} : Set Y)) = ⊥)
    {w : Y} (hwS : w ∈ S) (hwC : w ∈ centralizer ({τ} : Set Y)) : w = 1 ∨ w = τ := by
  refine z2a5_cent_cent h hwC fun x hx => ?_
  have hxC : x ∈ centralizer ({τ} : Set Y) := (Subgroup.closure_le _).2 (fun _ hy => hy.1) hx
  have hcX : w * x * w⁻¹ * x⁻¹ ∈ oTwoRes (centralizer ({τ} : Set Y)) :=
    mul_mem ((mem_normalizer_iff.1 (z2a5_cent_le_norm h hwC) x).1 hx) (inv_mem hx)
  have hcW : w * x * w⁻¹ * x⁻¹ ∈ S ⊓ centralizer ({τ} : Set Y) := by
    have h2 : x * w⁻¹ * x⁻¹ ∈ S ⊓ centralizer ({τ} : Set Y) :=
      Subgroup.mem_inf.2 ⟨(inferInstance : S.Normal).conj_mem _ (inv_mem hwS) x,
        mul_mem (mul_mem hxC (inv_mem hwC)) (inv_mem hxC)⟩
    have h3 : w * x * w⁻¹ * x⁻¹ = w * (x * w⁻¹ * x⁻¹) := by group
    rw [h3]
    exact mul_mem (Subgroup.mem_inf.2 ⟨hwS, hwC⟩) h2
  have h4 : w * x * w⁻¹ * x⁻¹ ∈
      oTwoRes (centralizer ({τ} : Set Y)) ⊓ (S ⊓ centralizer ({τ} : Set Y)) :=
    Subgroup.mem_inf.2 ⟨hcX, hcW⟩
  rw [hbot, mem_bot] at h4
  calc w * x = (w * x * w⁻¹ * x⁻¹) * x * w := by group
    _ = x * w := by rw [h4, one_mul]

private theorem z2a5_socle_absurd [Finite Y] (h : Z2A5Hyp Y τ) {S : Subgroup Y}
    (hS : FixedData Y S) (hτS : τ ∈ S)
    (hW : ∀ w ∈ S, w ∈ centralizer ({τ} : Set Y) → w = 1 ∨ w = τ) : False := by
  have hsmall : ∀ U : Subgroup Y, IsPGroup 2 U → U ≤ S → Nat.card U ≤ 2 := by
    intro U hU hUS
    refine CFSG.SeitzReduction.card_le_two_of_forall_le_inf_centralizer hτS h.1 ?_ hU hUS
    intro V _ hV
    have hVz : V ≤ zpowers τ := by
      intro v hv
      rcases hW v (hV hv).1 (hV hv).2 with rfl | rfl
      · exact one_mem _
      · exact mem_zpowers _
    calc Nat.card V ≤ Nat.card (zpowers τ) := Subgroup.card_le_of_le hVz
      _ = 2 := by rw [Nat.card_zpowers, h.1]
  haveI : IsSimpleGroup ↥S := hS.simple
  have hnab : ∃ a b : ↥S, a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := hS.nonab
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h' => hab (congrArg Subtype.val h')⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥S) := inferInstance
  apply CFSG.EvenSporadicStandard.Induction.Junction.not_isCyclic_sylow_two hnab P
  have hPc : Nat.card ↥(P : Subgroup ↥S) ≤ 2 := by
    have h1 := hsmall ((P : Subgroup ↥S).map S.subtype) (P.isPGroup'.map _) (map_subtype_le _)
    rwa [card_map_of_injective S.subtype_injective] at h1
  rcases Nat.lt_or_ge (Nat.card ↥(P : Subgroup ↥S)) 2 with hlt | hge
  · have h1 : Nat.card ↥(P : Subgroup ↥S) = 1 := by
      have := Nat.card_pos (α := ↥(P : Subgroup ↥S))
      omega
    haveI : Subsingleton ↥(P : Subgroup ↥S) := (Nat.card_eq_one_iff_unique.1 h1).1
    exact isCyclic_of_subsingleton
  · exact isCyclic_of_prime_card (p := 2) (le_antisymm hPc hge)

theorem z2a5_le_socle [Finite Y] (h : Z2A5Hyp Y τ) {S : Subgroup Y} (hS : FixedData Y S) :
    oTwoRes (centralizer ({τ} : Set Y)) ≤ S := by
  haveI := hS.normal
  have hXC : oTwoRes (centralizer ({τ} : Set Y)) ≤ centralizer ({τ} : Set Y) :=
    (Subgroup.closure_le _).2 fun _ hx => hx.1
  obtain ⟨φ⟩ := z2a5_X_equiv h
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  have hnorm : ∀ b ∈ oTwoRes (centralizer ({τ} : Set Y)), ∀ x ∈ S ⊓ centralizer ({τ} : Set Y),
      b * x * b⁻¹ ∈ S ⊓ centralizer ({τ} : Set Y) := fun b hb x hx =>
    Subgroup.mem_inf.2 ⟨hS.normal.conj_mem x (Subgroup.mem_inf.1 hx).1 b,
      mul_mem (mul_mem (hXC hb) (Subgroup.mem_inf.1 hx).2) (inv_mem (hXC hb))⟩
  rcases inf_eq_bot_or_le_of_simple φ.isSimpleGroup hnorm with hbot | hle
  · exfalso
    have hW := fun w (hwS : w ∈ S) (hwC : w ∈ centralizer ({τ} : Set Y)) =>
      z2a5_socle_cent h hbot hwS hwC
    by_cases hτS : τ ∈ S
    · exact z2a5_socle_absurd h hS hτS hW
    · have hfix : ∀ w ∈ S, τ * w = w * τ → w = 1 := by
        intro w hwS hc
        rcases hW w hwS (mem_centralizer_singleton_iff.2 hc.symm) with h1 | h1
        · exact h1
        · exact absurd (h1 ▸ hwS) hτS
      have hcomm := fixedPointFree_commute_of_mul_self_eq_one (z2a5_mul_self h)
        (fun w hw => hS.normal.conj_mem w hw τ) hfix
      obtain ⟨a, ha, b, hb, hab⟩ := hS.nonab
      exact hab (hcomm a ha b hb)
  · exact fun x hx => (hle hx).1

theorem z2a5_moves (h : Z2A5Hyp Y τ) {S : Subgroup Y} (hS : FixedData Y S) :
    ∃ d ∈ S, τ⁻¹ * d * τ ≠ d := by
  by_contra hc
  push Not at hc
  have hmem : τ ∈ centralizer (S : Set Y) := by
    rw [mem_centralizer_iff]
    intro d hd
    calc d * τ = τ * (τ⁻¹ * d * τ) := by group
      _ = τ * d := by rw [hc d hd]
  rw [hS.cent, mem_bot] at hmem
  have h2 := h.1
  rw [hmem, orderOf_one] at h2
  omega

theorem z2a5_datum [Finite Y] (h : Z2A5Hyp Y τ) {S : Subgroup Y} [S.Normal]
    (hS : FixedData Y S) :
    ∃ (k : Type) (_ : Field k) (_ : Fintype k), FixedRootDatum ↥S 2 k (MulAut.conjNormal τ)
      ((oTwoRes (centralizer ({τ} : Set Y))).subgroupOf S) := by
  obtain ⟨k, _, _, hk, ⟨φ⟩⟩ := z2a5_sl24 h
  exact ⟨k, inferInstance, inferInstance, fixedRootDatum_of_normal (z2a5_le_socle h hS) h.1
    (z2a5_mem_cent h) (z2a5_cent_le_norm h) (z2a5_moves h hS) (z2a5_cent_rank h) le_rfl hk φ⟩

theorem z2a5_fixed_survivors [Finite Y] (hSel : FixedRootSelector fun D _ => Catalog D)
    (hK : CFSG.SectionRank.IsKGroupCat Y) (h : Z2A5Hyp Y τ) {S : Subgroup Y}
    (hS : FixedData Y S) : FixedRootSurvivors ↥S 2 := by
  haveI := hS.normal
  haveI : IsSimpleGroup ↥S := hS.simple
  obtain ⟨k, _, _, d⟩ := z2a5_datum h hS
  exact hSel.survivors_of_datum hS.simple
    (CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective hK S (MonoidHom.id S)
      Function.surjective_id) d

end CFSG.OddStandard.SmallF3.Omega
