module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiCoverLocal

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup Cover CFSG.EvenSporadicStandard.Solomon78
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H] {L K : Subgroup H} {u : H}

theorem card_quotient_oddCore_le_bar (hodd : Odd (Nat.card (center ↥L))) (hKL : K ≤ L) :
    Nat.card (↥K ⧸ CFSG.oddCore ↥K) ≤ Nat.card (bar (K.subgroupOf L)) := by
  let f : ↥K →* ↥L ⧸ center ↥L := (QuotientGroup.mk' (center ↥L)).comp (Subgroup.inclusion hKL)
  have hrange : f.range = bar (K.subgroupOf L) := by
    simp [f, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hker : f.ker.Normal := f.normal_ker
  have hodd' : Odd (Nat.card f.ker) := by
    have h1 : (f.ker).map K.subtype ≤ (center ↥L).map L.subtype := by
      rintro _ ⟨k, hk, rfl⟩
      have hk' : f k = 1 := hk
      exact ⟨⟨k, hKL k.2⟩, (QuotientGroup.eq_one_iff _).1 hk', rfl⟩
    have hZ : Odd (Nat.card ((center ↥L).map L.subtype)) := by
      rwa [Subgroup.card_map_of_injective L.subtype_injective]
    rw [← Subgroup.card_map_of_injective K.subtype_injective]
    exact hZ.of_dvd_nat (Subgroup.card_dvd_of_le h1)
  have hle : f.ker ≤ CFSG.oddCore ↥K := le_sSup ⟨hker, hodd'⟩
  have h1 : (CFSG.oddCore ↥K).index ∣ f.ker.index := Subgroup.index_dvd_of_le hle
  rw [Subgroup.index_ker, hrange] at h1
  exact Nat.le_of_dvd Nat.card_pos h1


theorem mem_of_cover (hodd : Odd (Nat.card (center ↥L))) (huL : u ∈ L) (hu2 : orderOf u = 2)
    (hbar : bar (K.subgroupOf L) =
      centralizer ({((⟨u, huL⟩ : ↥L) : ↥L ⧸ center ↥L)} : Set (↥L ⧸ center ↥L))) : u ∈ K := by
  have hu1 := sq_of_orderOf_two huL hu2
  have hmem : ((⟨u, huL⟩ : ↥L) : ↥L ⧸ center ↥L) ∈ bar (K.subgroupOf L) := by
    rw [hbar]
    exact mem_centralizer_singleton_iff.2 rfl
  exact Subgroup.mem_subgroupOf.1 (mem_of_mk_mem hodd hu1 hmem)

theorem twoAdic_inf_centralizer_of_cover (hodd : Odd (Nat.card (center ↥L))) (huL : u ∈ L)
    (hu2 : orderOf u = 2) (hKL : K ≤ L) (hKu : ∀ k ∈ K, k * u = u * k)
    (hbar : bar (K.subgroupOf L) =
      centralizer ({((⟨u, huL⟩ : ↥L) : ↥L ⧸ center ↥L)} : Set (↥L ⧸ center ↥L))) :
    twoAdic (L ⊓ centralizer ({u} : Set H)) = twoAdic K := by
  have hu1 := sq_of_orderOf_two huL hu2
  have hKu' := central_subgroupOf huL hKu
  have hC := centralizer_singleton_eq_sup hodd hu1 hKu' hbar
  have hmap : L ⊓ centralizer ({u} : Set H) =
      (centralizer ({(⟨u, huL⟩ : ↥L)} : Set ↥L)).map L.subtype := by
    ext x
    constructor
    · rintro ⟨hxL, hx⟩
      exact ⟨⟨x, hxL⟩, mem_centralizer_singleton_iff.2
        (Subtype.ext (mem_centralizer_singleton_iff.1 hx)), rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hy))⟩
  have h1 : twoAdic (L ⊓ centralizer ({u} : Set H)) =
      twoAdic (centralizer ({(⟨u, huL⟩ : ↥L)} : Set ↥L)) := by
    unfold twoAdic
    rw [hmap, Subgroup.card_map_of_injective L.subtype_injective]
  have hb : bar (K.subgroupOf L ⊔ center ↥L) = bar (K.subgroupOf L) := by
    unfold bar
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]
  rw [h1, hC, ← twoAdic_bar hodd, hb, twoAdic_bar hodd]
  unfold twoAdic
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv]

theorem characteristic_of_cover (hodd : Odd (Nat.card (center ↥L))) (hKq : CFSG.IsQuasisimple ↥K)
    (huL : u ∈ L) (hu2 : orderOf u = 2) (hKL : K ≤ L) (hKu : ∀ k ∈ K, k * u = u * k)
    (hbar : bar (K.subgroupOf L) =
      centralizer ({((⟨u, huL⟩ : ↥L) : ↥L ⧸ center ↥L)} : Set (↥L ⧸ center ↥L))) :
    (K.subgroupOf (L ⊓ centralizer ({u} : Set H))).Characteristic := by
  have hu1 := sq_of_orderOf_two huL hu2
  have hKu' := central_subgroupOf huL hKu
  have hK' := commutator_subgroupOf_eq_self hKL hKq
  have hC := centralizer_singleton_eq_sup hodd hu1 hKu' hbar
  set C : Subgroup H := L ⊓ centralizer ({u} : Set H) with hCdef
  have hKC : K ≤ C := fun k hk => ⟨hKL hk, mem_centralizer_singleton_iff.2 (hKu k hk)⟩
  have hperf := commutator_subgroupOf_eq_self hKC hKq
  have heq : K.subgroupOf C = commutator ↥C := by
    apply le_antisymm
    · calc K.subgroupOf C = ⁅K.subgroupOf C, K.subgroupOf C⁆ := hperf.symm
        _ ≤ ⁅(⊤ : Subgroup ↥C), (⊤ : Subgroup ↥C)⁆ := Subgroup.commutator_mono le_top le_top
        _ = commutator ↥C := (_root_.commutator_def _).symm
    · rw [_root_.commutator_def]
      refine Subgroup.commutator_le.2 fun x _ y _ => ?_
      have hx' : (⟨(x : H), x.2.1⟩ : ↥L) ∈ centralizer ({(⟨u, huL⟩ : ↥L)} : Set ↥L) :=
        mem_centralizer_singleton_iff.2 (Subtype.ext (mem_centralizer_singleton_iff.1 x.2.2))
      have hy' : (⟨(y : H), y.2.1⟩ : ↥L) ∈ centralizer ({(⟨u, huL⟩ : ↥L)} : Set ↥L) :=
        mem_centralizer_singleton_iff.2 (Subtype.ext (mem_centralizer_singleton_iff.1 y.2.2))
      rw [hC] at hx' hy'
      have h1 := Subgroup.commutator_mem_commutator hx' hy'
      have h2 : ⁅(⟨(x : H), x.2.1⟩ : ↥L), (⟨(y : H), y.2.1⟩ : ↥L)⁆ ∈ K.subgroupOf L :=
        Cover.commutator_le_self _ ((commutator_sup_central_le le_rfl) h1)
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_subgroupOf.1 h2
  rw [heq]
  infer_instance


theorem twoAdic_lt_of_cover (hodd : Odd (Nat.card (center ↥L))) (huL : u ∈ L) (hKL : K ≤ L)
    (hmodel : CentralizerModel (↥L ⧸ center ↥L) ((⟨u, huL⟩ : ↥L) : ↥L ⧸ center ↥L))
    (hbar : bar (K.subgroupOf L) =
      centralizer ({((⟨u, huL⟩ : ↥L) : ↥L ⧸ center ↥L)} : Set (↥L ⧸ center ↥L))) :
    twoAdic K < twoAdic L := by
  have e1 : twoAdic K = twoAdic (K.subgroupOf L) := by
    unfold twoAdic
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv]
  have e2 : twoAdic (K.subgroupOf L) = twoAdic (bar (K.subgroupOf L)) :=
    (twoAdic_bar hodd _).symm
  have e3 : twoAdic (⊤ : Subgroup (↥L ⧸ center ↥L)) = twoAdic L := by
    have h1 := twoAdic_bar hodd (⊤ : Subgroup ↥L)
    have hb : bar (⊤ : Subgroup ↥L) = (⊤ : Subgroup (↥L ⧸ center ↥L)) := by
      unfold bar
      rw [Subgroup.map_top, MonoidHom.range_eq_top]
      exact QuotientGroup.mk_surjective
    rw [hb] at h1
    rw [h1]
    unfold twoAdic
    rw [Subgroup.card_top]
  rw [e1, e2, hbar, ← e3]
  exact hmodel.twoAdic_lt

theorem oddCore_eq_bot_of_equiv {G K : Type*} [Group G] [Group K] (e : G ≃* K)
    (h : CFSG.oddCore K = ⊥) : CFSG.oddCore G = ⊥ := by
  refine sSup_eq_bot.2 fun M hM => ?_
  have hn : (M.map e.toMonoidHom).Normal := hM.1.map _ e.surjective
  have hodd : Odd (Nat.card (M.map e.toMonoidHom)) := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact hM.2
  have hle : M.map e.toMonoidHom ≤ CFSG.oddCore K := le_sSup ⟨hn, hodd⟩
  rw [h, le_bot_iff] at hle
  rw [← Subgroup.map_eq_bot_iff_of_injective (f := e.toMonoidHom) M e.injective]
  exact hle

end CFSG.EvenSporadicStandard.Induction
