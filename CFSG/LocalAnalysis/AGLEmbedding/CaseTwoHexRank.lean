module

import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeAux
import CFSG.LocalAnalysis.AGLEmbedding.Sp62Key
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R : Subgroup G}

theorem card_le_of_le_centralizer_barM {M : Subgroup G} {z : G} (hzM : z ∈ M) (hz3 : z ^ 3 = 1)
    {n : ℕ} (hrk : ∀ E : Subgroup G, E ≤ Subgroup.centralizer ({z} : Set G) →
      IsElemAbelian 3 E → Nat.card E ≤ n)
    {E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hEC : E ≤ Subgroup.centralizer
      ({QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩} : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hE : IsElemAbelian 3 E) : Nat.card E ≤ n := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set zM : M := ⟨z, hzM⟩ with hzMdef
  set C := Subgroup.centralizer ({zM} : Set M) with hC
  set Cb := Subgroup.centralizer ({mk zM} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hCb
  have hcop : Nat.Coprime 3 (Nat.card (CFSG.pCore 2 ↥M)) := by
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
    rw [hj]
    exact Nat.Coprime.pow_right j (by norm_num)
  have hzM3 : zM ^ 3 = 1 := Subtype.ext (by simpa using hz3)
  have hzMp : IsPGroup 3 (Subgroup.zpowers zM) :=
    isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using hzM3)
  have hmapC : ∀ c : C, mk (c : M) ∈ Cb := fun c => by
    rw [hCb, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp c.2]
  let f : C →* Cb := (mk.comp C.subtype).codRestrict Cb hmapC
  have hfv : ∀ c : C, ((f c : Cb) : ↥M ⧸ CFSG.pCore 2 ↥M) = mk (c : M) := fun c => rfl
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨g, hg, hgx⟩ := exists_mem_centralizer_mk_eq Nat.prime_three (CFSG.pCore 2 ↥M) hcop
      hzMp x.2
    exact ⟨⟨g, hg⟩, Subtype.ext hgx⟩
  set E' := E.subgroupOf Cb with hE'
  have hE3 : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  have hE'3 : IsPGroup 3 E' := hE3.comap_subtype
  obtain ⟨T, hT3, hTE⟩ := exists_isPGroup_map_eq' hf hE'3
  have hker : ∀ a ∈ T, f a = 1 → a = 1 := by
    intro a ha hfa
    have h1 : mk (a : M) = 1 := by
      have := congrArg Subtype.val hfa
      rwa [hfv] at this
    have h2 : (a : M) ∈ CFSG.pCore 2 ↥M := (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨j, hj⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥M) ⟨(a : M), h2⟩
    obtain ⟨k, hk⟩ := hT3 ⟨a, ha⟩
    have hj' : a ^ 2 ^ j = 1 := Subtype.ext (by simpa using congrArg Subtype.val hj)
    have hk' : a ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hcp : Nat.Coprime (3 ^ k) (2 ^ j) := Nat.Coprime.pow k j (by norm_num)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcp
      (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one hj'))
  have hfT : ∀ a ∈ T, f a ∈ E' := fun a ha => hTE ▸ Subgroup.mem_map_of_mem f ha
  have hTe : IsElemAbelian 3 T := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun a ha => ?_⟩
    · have hab : a.1 * b.1 * (b.1 * a.1)⁻¹ ∈ T :=
        T.mul_mem (T.mul_mem a.2 b.2) (T.inv_mem (T.mul_mem b.2 a.2))
      have hc : f (a.1 * b.1 * (b.1 * a.1)⁻¹) = 1 := by
        have hEc := hE.1.is_comm.comm
        have h1 : f a.1 * f b.1 = f b.1 * f a.1 := by
          apply Subtype.ext
          have := congrArg Subtype.val (hEc ⟨((f a.1 : Cb) : ↥M ⧸ CFSG.pCore 2 ↥M), hfT a.1 a.2⟩
            ⟨((f b.1 : Cb) : ↥M ⧸ CFSG.pCore 2 ↥M), hfT b.1 b.2⟩)
          simpa using this
        rw [map_mul, map_mul, map_inv, map_mul, h1, mul_inv_cancel]
      exact mul_inv_eq_one.mp (hker _ hab hc)
    · have h3 : f (a ^ 3) = 1 := by
        rw [map_pow]
        exact Subtype.ext (hE.2 _ (hfT a ha))
      exact hker _ (T.pow_mem ha 3) h3
  set T₂ : Subgroup G := (T.map C.subtype).map M.subtype with hT₂
  have hT₂C : T₂ ≤ Subgroup.centralizer ({z} : Set G) := by
    rintro _ ⟨_, ⟨a, -, rfl⟩, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.mp a.2
    exact congrArg Subtype.val this
  have hT₂e : IsElemAbelian 3 T₂ :=
    CFSG.SectionRank.isElemAbelian_map (CFSG.SectionRank.isElemAbelian_map hTe _) _
  have hcard : Nat.card E ≤ Nat.card T₂ := by
    rw [hT₂, Subgroup.card_map_of_injective M.subtype_injective,
      Subgroup.card_map_of_injective C.subtype_injective]
    have h1 : Nat.card E = Nat.card E' :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEC).toEquiv).symm
    rw [h1, ← hTE]
    exact Nat.card_le_card_of_surjective _ (f.subgroupMap_surjective T)
  exact hcard.trans (hrk T₂ hT₂C hT₂e)

theorem D1PhaseThree.isWeakSBlock_map_conj_of_cyc (h : D1PhaseThree 3 P M H R)
    (hcyc : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ barM M (H ⊓ M) → ⁅V, V⁆ = V →
      ∀ Q : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), Q ≤ V → IsPGroup 3 Q → IsCyclic Q)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    {Q : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hQL : Q ≤ barM M L) (hQ3 : IsPGroup 3 Q)
    (hQc : ¬ IsCyclic Q) {g : G} (hg : g ∈ M) :
    IsWeakSBlock M (pCoreOf 2 H) (L.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨hL.toIsTwoPrimeComponent.map_conj hg, fun hle => ?_⟩
  have hLg := hL.toIsTwoPrimeComponent.map_conj hg
  have hKeq := h.toD1Escape.inf_eq_inf_normalizer_twoCore
  have hY : L.map (MulAut.conj g).toMonoidHom ≤ H ⊓ M := hKeq ▸ le_inf hLg.le hle
  have hper : ⁅L.map (MulAut.conj g).toMonoidHom, L.map (MulAut.conj g).toMonoidHom⁆ =
      L.map (MulAut.conj g).toMonoidHom := by
    rw [← Subgroup.map_commutator, hL.perfect]
  have hV := barM_perfect hLg.le hper
  set gb := QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨g, hg⟩ with hgb
  have hbar : barM M (L.map (MulAut.conj g).toMonoidHom) =
      (barM M L).map (MulAut.conj gb).toMonoidHom := barM_map_conj hg L
  have hQ' : Q.map (MulAut.conj gb).toMonoidHom ≤ barM M (L.map (MulAut.conj g).toMonoidHom) :=
    hbar ▸ Subgroup.map_mono hQL
  have hc := hcyc _ (barM_mono hY) hV _ hQ' (hQ3.map _)
  exact hQc (isCyclic_of_injective
    (Subgroup.equivMapOfInjective Q (MulAut.conj gb).toMonoidHom
      (MulAut.conj gb).injective).toMonoidHom
    (MulEquiv.injective _))

end CFSG.AGLEmbedding
