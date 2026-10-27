module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.AltCentre

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open CFSG.AGLEmbedding CFSG.Open

variable {G : Type} [Group G] [Finite G] {S L : Subgroup G}

theorem inf_centralizer_blockV_le_pCoreOf (hA : Asc81bHyp (L ⊔ S) S)
    (hL : IsTwoPrimeComponent (L ⊔ S) L) (hSL : S ≤ Subgroup.normalizer (L : Set G))
    (hnle : ¬ L ≤ Subgroup.centralizer (blockV S L : Set G))
    (hZ : Subgroup.center ↥(barM (L ⊔ S) L) = ⊥) :
    (L ⊔ S) ⊓ Subgroup.centralizer (blockV S L : Set G) ≤ pCoreOf 2 (L ⊔ S) := by
  classical
  set M := L ⊔ S with hM
  set C := Subgroup.centralizer (blockV S L : Set G) with hC
  have hcentral : barM M (L ⊓ C) ≤ (Subgroup.center ↥(barM M L)).map (barM M L).subtype :=
    Coordinator.barM_inf_le_center_of_core_le hL
      (le_sup_left.trans (Coordinator.le_normalizer_centralizer_blockV S L))
      (inf_le_right.trans (AscTenThree.le_centralizer_omegaOneCenterOf_self _)) hnle
  rw [hZ, Subgroup.map_bot] at hcentral
  have hbar : ∀ l ∈ L ⊓ C, l ∈ pCoreOf 2 M := by
    intro l hl
    have hlM : l ∈ M := (le_sup_left : L ≤ L ⊔ S) hl.1
    have hmem : (QuotientGroup.mk ⟨l, hlM⟩ : ↥M ⧸ CFSG.pCore 2 ↥M) ∈ barM M (L ⊓ C) :=
      (mem_barM _).2 ⟨⟨l, hlM⟩, hl, rfl⟩
    have h1 := hcentral hmem
    rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff] at h1
    exact ⟨⟨l, hlM⟩, by exact h1, rfl⟩
  set K := CFSG.pCore 2 ↥M with hK
  have hS2 : IsPGroup 2 S := hA.twoRadical.isPGroup
  have hMC : M ≤ Subgroup.normalizer ((M ⊓ C : Subgroup G) : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hx, Coordinator.le_normalizer_centralizer_blockV S L hx⟩
  have hN0 : ((M ⊓ C).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hMC
  have hNbar : (((M ⊓ C).subgroupOf M).map (QuotientGroup.mk' K)).Normal :=
    hN0.map _ (QuotientGroup.mk'_surjective _)
  have hp : IsPGroup 2 (((M ⊓ C).subgroupOf M).map (QuotientGroup.mk' K)) := by
    rintro ⟨x, y, hy, rfl⟩
    have hyC : (y : G) ∈ C := (Subgroup.mem_subgroupOf.1 hy).2
    obtain ⟨e, he⟩ := Coordinator.exists_pow_mem_sup hS2 hSL y.2
    have hmem : (y : G) ^ 2 ^ e ∈ pCoreOf 2 M := hbar _ ⟨he, C.pow_mem hyC _⟩
    obtain ⟨k, hk, hke⟩ := hmem
    refine ⟨e, ?_⟩
    apply Subtype.ext
    have hkey : y ^ 2 ^ e = k := Subtype.ext (by simpa using hke.symm)
    show (QuotientGroup.mk' K y) ^ 2 ^ e = 1
    rw [← map_pow, hkey]
    exact (QuotientGroup.eq_one_iff k).2 hk
  have hle : (((M ⊓ C).subgroupOf M).map (QuotientGroup.mk' K)) ≤ CFSG.pCore 2 (↥M ⧸ K) :=
    le_sSup ⟨hNbar, hp⟩
  have hbot : CFSG.pCore 2 (↥M ⧸ K) = ⊥ := Coordinator.StarAux.pCore_quotient_pCore_eq_bot
  intro z hz
  have hzM : z ∈ M := hz.1
  have h1 : (QuotientGroup.mk' K) ⟨z, hzM⟩ ∈
      ((M ⊓ C).subgroupOf M).map (QuotientGroup.mk' K) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hz)
  have h2 := hle h1
  rw [hbot, Subgroup.mem_bot] at h2
  exact ⟨⟨z, hzM⟩, by exact (QuotientGroup.eq_one_iff (N := K) _).1 h2, rfl⟩

section WeakBlock

variable {X : Subgroup G}

theorem inf_centralizer_blockV_le_of_isWeakSBlock (hX : CFSG.Open.IsKGroup ↥X)
    (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L) {m : ℕ} (hm : 8 < m)
    (e : ↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) ≃* alternatingGroup (Fin m)) :
    (L ⊔ S) ⊓ Subgroup.centralizer (blockV S L : Set G) ≤ S := by
  have hSL : S ≤ Subgroup.normalizer (L : Set G) := Coordinator.le_normalizer_of_isWeakSBlock hX hA hL
  have hLs : IsTwoPrimeComponent (L ⊔ S) L :=
    CFSG.HardMathSupport.Cooperstein.Proving.isTwoPrimeComponent_sup hL.toIsTwoPrimeComponent hA.twoRadical.1 hA.twoRadical.isPGroup hSL
  have hA' : Asc81bHyp (L ⊔ S) S := Coordinator.asc81bHyp_sup hA hL.toIsTwoPrimeComponent hSL
  have hZ : Subgroup.center ↥(barM (L ⊔ S) L) = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ (card_center_barM_sup_eq_one hA' hLs hSL hm e)
  exact (inf_centralizer_blockV_le_pCoreOf hA' hLs hSL (Coordinator.not_le_centralizer_blockV hA hL hSL) hZ).trans
    (Coordinator.twoCore_sup_le hA hL hSL)

end WeakBlock

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
