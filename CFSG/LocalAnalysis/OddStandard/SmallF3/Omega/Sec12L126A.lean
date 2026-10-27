module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11Steps
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10BData
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Aux
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L126Base
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4L46

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec126_le_of_alt5 [Finite G] {X H N : Subgroup G}
    (hX : Nonempty (↥X ≃* ↥(alternatingGroup (Fin 5)))) (hXN : X ≤ N) (hHN : H ≤ N)
    (hidx : H.relIndex N ≤ 2) : X ≤ H := by
  obtain ⟨e⟩ := hX
  haveI : IsSimpleGroup ↥X := e.isSimpleGroup
  have hpos : H.relIndex N ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : (H.subgroupOf X).index ≤ 2 :=
    (Subgroup.relIndex_le_of_le_right hXN hpos).trans hidx
  have hne : (H.subgroupOf X).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hcases : (H.subgroupOf X).index = 1 ∨ (H.subgroupOf X).index = 2 := by omega
  rcases hcases with h | h
  · intro x hx
    have htop := Subgroup.index_eq_one.mp h
    have : (⟨x, hx⟩ : ↥X) ∈ H.subgroupOf X := by rw [htop]; trivial
    exact Subgroup.mem_subgroupOf.mp this
  · exfalso
    haveI := Subgroup.normal_of_index_eq_two h
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (H.subgroupOf X) with hb | ht
    · rw [hb, Subgroup.index_bot, Nat.card_congr e.toEquiv, nat_card_alternatingGroup] at h
      simp at h
      revert h
      decide
    · rw [ht, Subgroup.index_top] at h
      omega

theorem sec126_isElemAb2_secA [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    (hctx : Sec10Z G t L S z) :
    secA t S L ≤ S ∧ CFSG.Open.IsElemAbelian 2 (secB S L) ∧ IsElemAb2 (secA t S L) 5 := by
  obtain ⟨hpsp, htC, htL, htS, hSN, hsyl⟩ := hp.basic G t L S z hctx
  obtain ⟨hBL, hB16, -, -, -, φ, hperm, -⟩ := sec10BData_of hp.basic hp.facts.b5 hctx
  have hB : CFSG.Open.IsElemAbelian 2 (secB S L) := by
    obtain ⟨hhom, -, hmem, -⟩ := hperm
    have h0 : IsEvenVec (0 : Fin 5 → ZMod 2) := by simp [IsEvenVec]
    have hzero : φ 0 = 1 := by
      have h := hhom 0 0 h0 h0
      rw [add_zero] at h
      exact (mul_eq_left.mp h.symm)
    have hsq : ∀ v : Fin 5 → ZMod 2, v + v = 0 := fun v => by
      funext i
      exact CharTwo.add_self_eq_zero (v i)
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨v, hv, hva⟩ := (hmem a).1 a.2
      obtain ⟨w, hw, hwb⟩ := (hmem b).1 b.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hva, ← hwb, ← hhom v w hv hw,
        ← hhom w v hw hv, add_comm]
    · obtain ⟨v, hv, rfl⟩ := (hmem x).1 hx
      rw [pow_two, ← hhom v v hv hv, hsq, hzero]
  have hAe : CFSG.Open.IsElemAbelian 2 (secA t S L) :=
    sec4_isElemAbelian_sup_zpowers hBL hB htC hctx.involution
  have hcard : Nat.card ↥(secA t S L) = 2 ^ 5 := by
    change Nat.card ↥(secB S L ⊔ zpowers t) = 2 ^ 5
    rw [sec4_card_sup_zpowers hBL htC htL hctx.involution, hB16]
    norm_num
  exact ⟨sup_le (secB_le_S S L) ((Subgroup.zpowers_le).2 htS), hB, hAe, hcard⟩

theorem sec126_A_eq_jElem [Finite G] (hp : Asc82Pre11) (h122 : Asc82Lemma122)
    (h123 : Asc82Lemma123) {t : G} {L S : Subgroup G} {z : G} {K1 K2 E : Subgroup G}
    (hctx : Sec12Ctx G t L S z K1 K2 E) : secA t S L = JElem S := by
  rcases hp.r10.l107c G t L S z K1 K2 hctx.toSec10Ctx with h | ⟨r, hrS, hr2, hrty, -, -⟩
  · exact h
  exfalso
  obtain ⟨X, hX⟩ := h122 G t L S z K1 K2 E hctx
  obtain ⟨hXA5, -, hXaut, -⟩ := h123 G t L S z K1 K2 E X hctx hX
  obtain ⟨hpsp, htC, htL, htS, hSN, hsyl⟩ := hp.basic G t L S z hctx.toSec10Z
  have hrC : r ∈ centralizer ({t} : Set G) := hctx.sylow.1 hrS
  have hSM : S ≤ secM t S L := fun x hx =>
    hp.r10.l109 G t L S z K1 K2 hctx.toSec10Ctx (Subgroup.le_normalizer hx)
  have hrN : r ∈ normalizer (secA t S L : Set G) := hSM hrS
  have hmemC : (secA t S L).normalizerMonoidHom ⟨r, hrN⟩ ∈
      autIn (secCMt t S L) (secA t S L) := by
    refine Subgroup.mem_map.mpr ⟨⟨r, hrN⟩, ?_, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hSM hrS, hrC⟩)
  rw [← hXaut] at hmemC
  obtain ⟨⟨x, hxN⟩, hxX, hxeq⟩ := Subgroup.mem_map.mp hmemC
  have hxX' : x ∈ X := Subgroup.mem_subgroupOf.mp hxX
  have hact : ∀ a ∈ secA t S L, x * a * x⁻¹ = r * a * r⁻¹ := by
    intro a ha
    exact congrArg (fun φ : MulAut ↥(secA t S L) => ((φ ⟨a, ha⟩ : ↥(secA t S L)) : G)) hxeq
  have hXN : X ≤ normalizer (L : Set G) := by
    have h1 : X ≤ X ⊔ secA t S L := le_sup_left
    rw [hX.sup] at h1
    exact h1.trans (sup_le (inf_le_right.trans Subgroup.le_normalizer) hSN)
  have hcN : x⁻¹ * r ∈ normalizer (L : Set G) :=
    (normalizer (L : Set G)).mul_mem ((normalizer (L : Set G)).inv_mem (hXN hxX')) (hSN hrS)
  have hcB : ∀ b ∈ JElem (S ⊓ L), (x⁻¹ * r) * b = b * (x⁻¹ * r) := by
    intro b hb
    have hbA : b ∈ secA t S L := (le_sup_left : secB S L ≤ secA t S L) hb
    have h1 := hact b hbA
    calc x⁻¹ * r * b = x⁻¹ * (r * b * r⁻¹) * r := by group
      _ = x⁻¹ * (x * b * x⁻¹) * r := by rw [h1]
      _ = b * (x⁻¹ * r) := by group
  have hcmem := hp.facts.centB5 G L hpsp (S ⊓ L) hsyl (x⁻¹ * r) hcN hcB
  have hHN : L ⊔ centralizer (L : Set G) ≤ normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer _)
  have hxH : x ∈ L ⊔ centralizer (L : Set G) :=
    sec126_le_of_alt5 hXA5 hXN hHN (hp.facts.out5 G L hpsp) hxX'
  have hcH : x⁻¹ * r ∈ L ⊔ centralizer (L : Set G) :=
    (sup_le_sup_right (secB_le_L S L) _) hcmem
  have hrH : r ∈ L ⊔ centralizer (L : Set G) := by
    have := (L ⊔ centralizer (L : Set G)).mul_mem hxH hcH
    simpa using this
  have hr2' : r * r = 1 := by
    have := pow_orderOf_eq_one r
    rw [hr2, pow_two] at this
    exact this
  have hrr : r * r ∈ centralizer (L : Set G) := by
    rw [hr2']; exact Subgroup.one_mem _
  exact ((hp.facts.factsC.ty G L hpsp r (hSN hrS) hrr).mpr (Or.inr hrty)) hrH

theorem sec126_jElem_bound [Finite G] {S A : Subgroup G} (hA : IsElemAb2 A 5) (hAS : A ≤ S)
    (hJ : A = JElem S) :
    ∀ F : Subgroup G, F ≤ S → CFSG.Open.IsElemAbelian 2 F →
      Nat.card ↥F ≤ 32 ∧ (Nat.card ↥F = 32 → F = A) := by
  have hfin : Finite (Subgroup G) := Finite.of_injective _ SetLike.coe_injective
  obtain ⟨A0, ⟨hA0S, hA0e⟩, hmax⟩ := Set.exists_max_image
    {B : Subgroup G | B ≤ S ∧ CFSG.Open.IsElemAbelian 2 B} (fun B => Nat.card ↥B)
    (Set.toFinite _) ⟨A, hAS, hA.1⟩
  have hA0max : IsMaxElemAbelianIn S A0 :=
    ⟨hA0S, hA0e, fun B hB hBe => hmax B ⟨hB, hBe⟩⟩
  have hAc : Nat.card ↥A = 32 := by rw [hA.2]; norm_num
  have hA0A : A0 ≤ A := by
    rw [hJ]
    exact fun x hx => Subgroup.subset_closure ⟨A0, hA0max, hx⟩
  have hA0c : A0 = A := Subgroup.eq_of_le_of_card_ge hA0A (hmax A ⟨hAS, hA.1⟩)
  intro F hFS hFe
  have hFle : Nat.card ↥F ≤ 32 := by
    have := hmax F ⟨hFS, hFe⟩
    rwa [hA0c, hAc] at this
  refine ⟨hFle, fun hF32 => ?_⟩
  have hFmax : IsMaxElemAbelianIn S F := ⟨hFS, hFe, fun B hB hBe => by
    have := hmax B ⟨hB, hBe⟩
    rw [hA0c, hAc] at this
    omega⟩
  have hFA : F ≤ A := by
    rw [hJ]
    exact fun x hx => Subgroup.subset_closure ⟨F, hFmax, hx⟩
  exact Subgroup.eq_of_le_of_card_ge hFA (by rw [hAc, hF32])

theorem sec126_rank_ct [Finite G] {t : G} {S A : Subgroup G}
    (hS : IsSylow2Of S (centralizer ({t} : Set G))) (hA : IsElemAb2 A 5) (hAS : A ≤ S)
    (hJ : A = JElem S) :
    ∀ F : Subgroup G, F ≤ centralizer ({t} : Set G) → CFSG.Open.IsElemAbelian 2 F →
      Nat.card ↥F ≤ 32 ∧
        (Nat.card ↥F = 32 → ∃ g ∈ centralizer ({t} : Set G), F = CFSG.conjugate A g) := by
  intro F hFC hFe
  obtain ⟨c, hcC, hc⟩ := sec126_exists_conj_le hS hFe.isPGroup hFC
  have hF'S : CFSG.conjugate F c⁻¹ ≤ S := by
    intro x hx
    rw [mem_conjugate_iff] at hx
    have := hc _ hx
    simpa [mul_assoc] using this
  have hF'e : CFSG.Open.IsElemAbelian 2 (CFSG.conjugate F c⁻¹) :=
    sec4_isElemAbelian_conjugate hFe c⁻¹
  obtain ⟨hle, heq⟩ := sec126_jElem_bound hA hAS hJ _ hF'S hF'e
  rw [sec126_card_conjugate] at hle heq
  refine ⟨hle, fun h32 => ⟨c, hcC, ?_⟩⟩
  have h := heq h32
  have := sec126_conjugate_inv_cancel F c⁻¹
  rw [h, inv_inv] at this
  exact this.symm

end CFSG.OddStandard.SmallF3.Omega
