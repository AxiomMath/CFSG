module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7RWe
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7RRk
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Walter.W67.W1Basic
public import TauCeti.GroupTheory.PGroup

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] {t : G} {P U : Subgroup G}

private lemma natCard_le_mul_natCard_map_prod {A B : Type*} [Group A] [Group B]
    (F : Subgroup (A × B)) :
    Nat.card ↥F ≤ Nat.card ↥(F.map (MonoidHom.fst A B)) *
      Nat.card ↥(F.map (MonoidHom.snd A B)) := by
  have hinj : Function.Injective (fun x : ↥F =>
      Prod.mk (⟨(x : A × B).1, Subgroup.mem_map_of_mem (MonoidHom.fst A B) x.2⟩ :
        ↥(F.map (MonoidHom.fst A B)))
        (⟨(x : A × B).2, Subgroup.mem_map_of_mem (MonoidHom.snd A B) x.2⟩ :
        ↥(F.map (MonoidHom.snd A B)))) := by
    intro x y hxy
    have h1 : (x : A × B).1 = (y : A × B).1 :=
      congrArg Subtype.val (congrArg Prod.fst hxy)
    have h2 : (x : A × B).2 = (y : A × B).2 :=
      congrArg Subtype.val (congrArg Prod.snd hxy)
    exact Subtype.ext (Prod.ext h1 h2)
  have h0 : Nat.card (↥(F.map (MonoidHom.fst A B)) × ↥(F.map (MonoidHom.snd A B))) = 0 →
      Nat.card ↥F = 0 := by
    intro hzero
    rw [Nat.card_prod] at hzero
    rcases Nat.mul_eq_zero.mp hzero with h1 | h2
    · refine Finite.card_eq_zero_of_surjective (f := fun x : ↥F =>
        (⟨(x : A × B).1, Subgroup.mem_map_of_mem (MonoidHom.fst A B) x.2⟩ :
          ↥(F.map (MonoidHom.fst A B)))) ?_ h1
      rintro ⟨y, hy⟩
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨x, hx⟩, Subtype.ext (by simpa using hxy)⟩
    · refine Finite.card_eq_zero_of_surjective (f := fun x : ↥F =>
        (⟨(x : A × B).2, Subgroup.mem_map_of_mem (MonoidHom.snd A B) x.2⟩ :
          ↥(F.map (MonoidHom.snd A B)))) ?_ h2
      rintro ⟨y, hy⟩
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨x, hx⟩, Subtype.ext (by simpa using hxy)⟩
  calc Nat.card ↥F ≤ Nat.card (↥(F.map (MonoidHom.fst A B)) ×
        ↥(F.map (MonoidHom.snd A B))) := Finite.card_le_of_injective' hinj h0
    _ = Nat.card ↥(F.map (MonoidHom.fst A B)) * Nat.card ↥(F.map (MonoidHom.snd A B)) :=
        Nat.card_prod _ _

private lemma Wr7.e64 (h : Wr7 t P U) {E₁ E₂ : Subgroup G}
    (hE₁ : E₁ ≤ U) (hE₂ : E₂ ≤ conjSub t U)
    (hE₁el : IsElemAbelian 2 E₁) (hE₂el : IsElemAbelian 2 E₂)
    (hE₁card : Nat.card E₁ = 8) (hE₂card : Nat.card E₂ = 8) :
    IsElemAbelian 2 (E₁ ⊔ E₂) ∧ Nat.card ↥(E₁ ⊔ E₂) = 64 ∧ E₁ ⊔ E₂ ≤ P := by
  have hc : ∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a :=
    fun a ha b hb => h.direct.2.2 a (hE₁ ha) b (hE₂ hb)
  have hinf : E₁ ⊓ E₂ = ⊥ :=
    le_bot_iff.mp (inf_le_inf hE₁ hE₂ |>.trans (le_of_eq h.direct.2.1))
  have hcard := (CFSG.Walter.W67.card_sup_mul_card_inf_of_commute E₁ E₂ hc).1
  rw [hinf, Subgroup.card_bot, mul_one] at hcard
  exact ⟨IsElemAbelian.sup_of_commute hE₁el hE₂el hc,
    by rw [hcard, hE₁card, hE₂card],
    sup_le (hE₁.trans h.le_left.1) (hE₂.trans h.le_left.2)⟩

theorem Wr7.rankFacts_left (h : Wr7 t P U) {S : Subgroup G}
    (hc : P ⊓ centralizer ({t} : Set G) = S) (hS : RankFacts S) : RankFacts U :=
  RankFacts.of_mulEquiv h.centEquiv.symm (RankFacts.of_eq hc.symm hS)

theorem Wr7.isPGroup (h : Wr7 t P U) {S : Subgroup G} (hc : P ⊓ centralizer ({t} : Set G) = S)
    (hS : IsPGroup 2 S) : IsPGroup 2 P := by
  have hS' : IsPGroup 2 ↥(P ⊓ centralizer ({t} : Set G)) := hc.symm ▸ hS
  have hU2 : IsPGroup 2 ↥U := hS'.of_equiv h.centEquiv.symm
  have hU'2 : IsPGroup 2 ↥(conjSub t U) :=
    hU2.of_equiv (Subgroup.equivMapOfInjective U (MulAut.conj t).toMonoidHom
      (MulAut.conj t).injective)
  exact (hU2.prod hU'2).of_equiv h.prodEquiv

theorem Wr7.rank_bound (h : Wr7 t P U) (hU : RankFacts U) :
    ∀ E : Subgroup G, E ≤ P → IsElemAbelian 2 E → Nat.card E ≤ 64 := by
  intro E hEP hE
  set F : Subgroup (↥U × ↥(conjSub t U)) :=
    (E.subgroupOf P).map h.prodEquiv.symm.toMonoidHom with hF
  have hFel : IsElemAbelian 2 F := hF.symm ▸ (hE.subgroupOf P).map h.prodEquiv.symm.toMonoidHom
  have hcardEF : Nat.card ↥E = Nat.card ↥F := by
    rw [hF]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEP).toEquiv).symm.trans
      (Nat.card_congr (Subgroup.equivMapOfInjective (E.subgroupOf P)
        h.prodEquiv.symm.toMonoidHom h.prodEquiv.symm.injective).toEquiv)
  have hb₁ : Nat.card ↥((F.map (MonoidHom.fst ↥U ↥(conjSub t U))).map U.subtype) ≤ 8 :=
    hU.bound _ (Subgroup.map_subtype_le _)
      ((hFel.map (MonoidHom.fst ↥U ↥(conjSub t U))).map U.subtype)
  have hb₂ : Nat.card ↥((F.map (MonoidHom.snd ↥U ↥(conjSub t U))).map
      (conjSub t U).subtype) ≤ 8 :=
    (hU.conj t).bound _ (Subgroup.map_subtype_le _)
      ((hFel.map (MonoidHom.snd ↥U ↥(conjSub t U))).map (conjSub t U).subtype)
  have hc₁ : Nat.card ↥(F.map (MonoidHom.fst ↥U ↥(conjSub t U))) ≤ 8 := by
    rw [Nat.card_congr (Subgroup.equivMapOfInjective (F.map (MonoidHom.fst ↥U ↥(conjSub t U)))
      U.subtype U.subtype_injective).toEquiv]
    exact hb₁
  have hc₂ : Nat.card ↥(F.map (MonoidHom.snd ↥U ↥(conjSub t U))) ≤ 8 := by
    rw [Nat.card_congr (Subgroup.equivMapOfInjective (F.map (MonoidHom.snd ↥U ↥(conjSub t U)))
      (conjSub t U).subtype (conjSub t U).subtype_injective).toEquiv]
    exact hb₂
  calc Nat.card ↥E = Nat.card ↥F := hcardEF
    _ ≤ Nat.card ↥(F.map (MonoidHom.fst ↥U ↥(conjSub t U))) *
        Nat.card ↥(F.map (MonoidHom.snd ↥U ↥(conjSub t U))) :=
        natCard_le_mul_natCard_map_prod F
    _ ≤ 8 * 8 := Nat.mul_le_mul hc₁ hc₂
    _ = 64 := by norm_num

theorem Wr7.rank_cover (h : Wr7 t P U) (hU : RankFacts U) {x : G} (hx : x ∈ P) (hx2 : x ^ 2 = 1) :
    ∃ E : Subgroup G, E ≤ P ∧ IsElemAbelian 2 E ∧ Nat.card E = 64 ∧
      E ≤ centralizer ({x} : Set G) := by
  obtain ⟨u, hu, v, hv, rfl⟩ := Wr7.decomp h hx
  have hcomm : Commute u v := h.direct.2.2 u hu v hv
  have h2 : u ^ 2 * v ^ 2 = 1 := by
    rw [Commute.mul_pow hcomm 2] at hx2
    exact hx2
  have hu2 : u ^ 2 = 1 :=
    (Wr7.unique h (U.pow_mem hu 2) U.one_mem ((conjSub t U).pow_mem hv 2)
      (conjSub t U).one_mem (by simpa using h2)).1
  have hv2 : v ^ 2 = 1 :=
    (Wr7.unique h (U.pow_mem hu 2) U.one_mem ((conjSub t U).pow_mem hv 2)
      (conjSub t U).one_mem (by simpa using h2)).2
  obtain ⟨E₁, hE₁U, hE₁el, hE₁card, huE₁⟩ := hU.cover u hu hu2
  obtain ⟨E₂, hE₂U, hE₂el, hE₂card, hvE₂⟩ := (hU.conj t).cover v hv hv2
  obtain ⟨hEel, hEcard, hEP⟩ := Wr7.e64 h hE₁U hE₂U hE₁el hE₂el hE₁card hE₂card
  refine ⟨E₁ ⊔ E₂, hEP, hEel, hEcard, sup_le ?_ ?_⟩
  · intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Commute.mul_right (hE₁el.comm ha huE₁) (h.direct.2.2 a (hE₁U ha) v hv)
  · intro b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Commute.mul_right (h.direct.2.2 u hu b (hE₂U hb)).symm (hE₂el.comm hb hvE₂)

theorem Wr7.rank_gen (h : Wr7 t P U) (hU : RankFacts U) :
    ∀ N : Subgroup G,
      (∀ E : Subgroup G, E ≤ P → IsElemAbelian 2 E → Nat.card E = 64 → E ≤ N) → P ≤ N := by
  intro N hN
  have hUle : U ≤ N := by
    refine hU.gen N ?_
    intro E hEU hEel hEcard
    obtain ⟨E₂, hE₂U, hE₂el, hE₂card, -⟩ :=
      (hU.conj t).cover 1 (one_mem (conjSub t U)) (by simp)
    obtain ⟨hel, hcard, hEP⟩ := Wr7.e64 h hEU hE₂U hEel hE₂el hEcard hE₂card
    exact le_trans le_sup_left (hN (E ⊔ E₂) hEP hel hcard)
  have hU'le : conjSub t U ≤ N := by
    refine (hU.conj t).gen N ?_
    intro E hEU hEel hEcard
    obtain ⟨E₁, hE₁U, hE₁el, hE₁card, -⟩ := hU.cover 1 (one_mem U) (by simp)
    obtain ⟨hel, hcard, hEP⟩ := Wr7.e64 h hE₁U hEU hE₁el hEel hE₁card hEcard
    exact le_trans le_sup_right (hN (E₁ ⊔ E) hEP hel hcard)
  rw [← h.direct.1]
  exact sup_le hUle hU'le

end CFSG.OddStandard.HigherRank.YamadaG23
