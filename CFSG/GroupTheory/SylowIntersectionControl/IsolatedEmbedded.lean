module

public import CFSG.GroupTheory.SylowIntersectionControl.Isolated
public import CFSG.RankThree.PartOne.S12.InputsSec15
import CFSG.ClassicalInvolution.LBalance.Glauberman.SylowTools
import CFSG.LocalAnalysis.StronglyEmbedded.Normalizer
import CFSG.LocalAnalysis.ComponentClassification.Sol78NoStrongEmb

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.ABGLocalTools CFSG.RankThree.PartOne.StrongP
  CFSG.ClassicalInvolution.GlaubermanAut
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type*} [Group G] {p : ℕ}

private theorem eqvGen_of_map {α β : Type*} {r : α → α → Prop} {s : β → β → Prop} (f : α → β)
    (h : ∀ a b, r a b → s (f a) (f b)) {a b : α} (hab : Relation.EqvGen r a b) :
    Relation.EqvGen s (f a) (f b) := by
  induction hab with
  | rel x y hxy => exact .rel _ _ (h x y hxy)
  | refl x => exact .refl _
  | symm x y _ ih => exact .symm _ _ ih
  | trans x y z _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

private theorem map_subtype_subgroupOf {K : Subgroup G} (A : Subgroup K) :
    (A.map K.subtype).subgroupOf K = A :=
  comap_map_eq_self_of_injective K.subtype_injective A

private theorem subgroupOf_map_subtype_of_le {K X : Subgroup G} (h : X ≤ K) :
    (X.subgroupOf K).map K.subtype = X := by
  rw [subgroupOf_map_subtype, inf_eq_left.mpr h]

private theorem conjSub_eq_self {Y : Subgroup G} {g : G} (hg : g ∈ Y) : conjSub g Y = Y := by
  ext x
  rw [mem_conjSub_iff]
  constructor
  · intro hx
    have h := Y.mul_mem (Y.mul_mem hg hx) (Y.inv_mem hg)
    rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at h
  · intro hx
    exact Y.mul_mem (Y.mul_mem (Y.inv_mem hg) hx) hg

section Sylow

variable [Finite G] [Fact p.Prime]

private theorem dvd_card_of_isSylowOf {S K : Subgroup G} (hS : IsSylowOf p S K)
    (hK : p ∣ Nat.card K) : p ∣ Nat.card S := by
  rw [hS.card_eq]
  exact dvd_pow_self p ((Fact.out : p.Prime).factorization_pos_of_dvd Nat.card_pos.ne' hK).ne'

private theorem isSylowOf_conjSub {A : Subgroup G} (hA : IsSylowOf p A ⊤) (g : G) :
    IsSylowOf p (conjSub g A) ⊤ :=
  isSylowOf_of_card le_top (by rw [card_conjSub]; exact hA.card_eq)

private theorem exists_eq_conjSub {A B : Subgroup G} (hA : IsSylowOf p A ⊤)
    (hB : IsSylowOf p B ⊤) : ∃ k : G, B = conjSub k A := by
  obtain ⟨k, -, hk⟩ := isSylowOf_exists_conj hA hB
  exact ⟨k, by ext x; rw [hk x, mem_conjSub_iff]⟩

omit [Finite G] in
private theorem dvd_card_of_bot_lt {A : Subgroup G} (hA : IsPGroup p A) (h : ⊥ < A) :
    p ∣ Nat.card A := by
  rcases hA.card_eq_or_dvd with h1 | h1
  · exact absurd (card_eq_one.mp h1) (bot_lt_iff_ne_bot.mp h)
  · exact h1

private theorem isSylowOf_inf_of_isSubnormal {P Y : Subgroup G} (hP : IsSylowOf p P ⊤)
    (hY : Y.IsSubnormal) : IsSylowOf p (P ⊓ Y) Y := by
  induction hY with
  | top => simpa using hP
  | step H K hHK _ hN ih =>
    have h1 := ih.inf_of_le_normalizer hHK
      ((normal_subgroupOf_iff_le_normalizer hHK).mp hN)
    rwa [inf_assoc, inf_eq_right.mpr hHK] at h1

end Sylow

section SubgroupOf

variable [Finite G] [Fact p.Prime]

private theorem isSylowOf_subgroupOf_iff {K K' : Subgroup G} (hK : K ≤ K') {A : Subgroup K'} :
    IsSylowOf p A (K.subgroupOf K') ↔ IsSylowOf p (A.map K'.subtype) K := by
  rw [← isSylowOf_map_subtype_iff K', subgroupOf_map_subtype, inf_eq_left.mpr hK]

theorem isPIsolatedOver_subgroupOf_iff {H K K' : Subgroup G} (hH : H ≤ K') (hK : K ≤ K') :
    IsPIsolatedOver p (K.subgroupOf K') (H.subgroupOf K') ↔ IsPIsolatedOver p K H := by
  have hinj := K'.subtype_injective
  have hlt : ∀ A B : Subgroup K', H.subgroupOf K' < A ⊓ B ↔
      H < A.map K'.subtype ⊓ B.map K'.subtype := by
    intro A B
    rw [← map_lt_map_iff_of_injective hinj, subgroupOf_map_subtype_of_le hH,
      map_inf_eq _ _ _ hinj]
  constructor
  · rintro ⟨S, T, hS, hT, hST⟩
    refine ⟨S.map K'.subtype, T.map K'.subtype, (isSylowOf_subgroupOf_iff hK).mp hS,
      (isSylowOf_subgroupOf_iff hK).mp hT, fun hE => hST ?_⟩
    have h : Relation.EqvGen (fun A B : Subgroup K' => IsSylowOf p A (K.subgroupOf K') ∧
        IsSylowOf p B (K.subgroupOf K') ∧ H.subgroupOf K' < A ⊓ B)
        ((S.map K'.subtype).subgroupOf K') ((T.map K'.subtype).subgroupOf K') :=
      eqvGen_of_map (fun X : Subgroup G => X.subgroupOf K') (fun X Y hXY => by
        obtain ⟨hX, hY, hXY⟩ := hXY
        have hX' := subgroupOf_map_subtype_of_le (hX.le.trans hK)
        have hY' := subgroupOf_map_subtype_of_le (hY.le.trans hK)
        refine ⟨(isSylowOf_subgroupOf_iff hK).mpr (hX'.symm ▸ hX),
          (isSylowOf_subgroupOf_iff hK).mpr (hY'.symm ▸ hY), ?_⟩
        rw [hlt, hX', hY']
        exact hXY) hE
    simpa only [map_subtype_subgroupOf] using h
  · rintro ⟨S, T, hS, hT, hST⟩
    have hS' := subgroupOf_map_subtype_of_le (hS.le.trans hK)
    have hT' := subgroupOf_map_subtype_of_le (hT.le.trans hK)
    refine ⟨S.subgroupOf K', T.subgroupOf K', (isSylowOf_subgroupOf_iff hK).mpr (hS'.symm ▸ hS),
      (isSylowOf_subgroupOf_iff hK).mpr (hT'.symm ▸ hT), fun hE => hST ?_⟩
    have h : Relation.EqvGen (fun A B : Subgroup G => IsSylowOf p A K ∧ IsSylowOf p B K ∧
        H < A ⊓ B) ((S.subgroupOf K').map K'.subtype) ((T.subgroupOf K').map K'.subtype) :=
      eqvGen_of_map (fun X : Subgroup K' => X.map K'.subtype) (fun X Y hXY => by
        obtain ⟨hX, hY, hXY⟩ := hXY
        exact ⟨(isSylowOf_subgroupOf_iff hK).mp hX, (isSylowOf_subgroupOf_iff hK).mp hY,
          (hlt X Y).mp hXY⟩) hE
    rwa [hS', hT'] at h

end SubgroupOf

private abbrev isoRel (p : ℕ) (A B : Subgroup G) : Prop :=
  IsSylowOf p A ⊤ ∧ IsSylowOf p B ⊤ ∧ ⊥ < A ⊓ B

section Embedded

variable [Finite G] [Fact p.Prime]

private theorem isoRel_conjSub {A B : Subgroup G} (h : isoRel p A B) (g : G) :
    isoRel p (conjSub g A) (conjSub g B) := by
  obtain ⟨hA, hB, hAB⟩ := h
  refine ⟨isSylowOf_conjSub hA g, isSylowOf_conjSub hB g, ?_⟩
  rw [← conjSub_inf, bot_lt_iff_ne_bot, Ne,
    map_eq_bot_iff_of_injective _ (MulAut.conj g).injective]
  exact bot_lt_iff_ne_bot.mp hAB

private theorem eqvGen_conjSub {A B : Subgroup G} (h : Relation.EqvGen (isoRel p) A B) (g : G) :
    Relation.EqvGen (isoRel p) (conjSub g A) (conjSub g B) :=
  eqvGen_of_map (conjSub g) (fun _ _ hab => isoRel_conjSub hab g) h

variable (p) in
private def classStab (S : Subgroup G) : Subgroup G where
  carrier := {g | Relation.EqvGen (isoRel p) S (conjSub g S)}
  one_mem' := by
    simp only [Set.mem_setOf_eq, conjSub_one]
    exact .refl _
  mul_mem' {a b} ha hb := by
    have h := eqvGen_conjSub hb a
    rw [conjSub_mul] at h
    exact .trans _ _ _ ha h
  inv_mem' {a} ha := by
    have h := eqvGen_conjSub ha a⁻¹
    rw [conjSub_mul, inv_mul_cancel, conjSub_one] at h
    exact .symm _ _ h

private theorem mem_classStab {S : Subgroup G} {g : G} :
    g ∈ classStab p S ↔ Relation.EqvGen (isoRel p) S (conjSub g S) := Iff.rfl

private theorem exists_mem_conjSub_of_mem {S M : Subgroup G} (hS : IsSylowOf p S ⊤)
    (hSM : S ≤ M) {x : G} (hx : orderOf x = p) (hxM : x ∈ M) : ∃ m ∈ M, x ∈ conjSub m S := by
  have hZ : IsPGroup p (zpowers x) :=
    isPGroup_zpowers_of_pow_eq_one (by rw [← hx]; exact pow_orderOf_eq_one x)
  obtain ⟨Q, hxQ, hQ⟩ := exists_isSylowOf_ge hZ (zpowers_le.mpr hxM)
  obtain ⟨m, hm, hmem⟩ := isSylowOf_exists_conj (hS.of_le hSM le_top) hQ
  exact ⟨m, hm, mem_conjSub_iff.mpr ((hmem x).mp (hxQ (mem_zpowers x)))⟩

private theorem isStronglyPEmbedded_classStab {S T : Subgroup G} (hS : IsSylowOf p S ⊤)
    (hT : IsSylowOf p T ⊤) (hST : ¬ Relation.EqvGen (isoRel p) S T) :
    IsStronglyPEmbedded p (classStab p S) := by
  have hSM : S ≤ classStab p S := fun s hs => by
    rw [mem_classStab, conjSub_eq_self hs]
    exact .refl _
  obtain ⟨k, hTk⟩ := exists_eq_conjSub hS hT
  refine ⟨fun htop => hST ?_, ?_, fun g hg hdvd => hg ?_⟩
  · rw [hTk]
    exact mem_classStab.mp (htop ▸ mem_top k)
  · have hpS : p ∣ Nat.card S := by
      rcases hS.isPGroup.card_eq_or_dvd with h | h
      · refine absurd ?_ hST
        have h1 : S = ⊥ := card_eq_one.mp h
        have h2 : T = ⊥ := card_eq_one.mp (by rw [hT.card_eq, ← hS.card_eq, h])
        rw [h1, h2]
        exact .refl _
      · exact h
    exact hpS.trans (card_dvd_of_le hSM)
  · obtain ⟨⟨x, hxMg⟩, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
    rw [orderOf_mk] at hx
    obtain ⟨hxM, hxg⟩ := mem_inf.mp hxMg
    obtain ⟨m, hm, hxm⟩ := exists_mem_conjSub_of_mem hS hSM hx hxM
    have hxg' : g⁻¹ * x * g ∈ classStab p S := mem_conjSub_iff.mp hxg
    have hord : orderOf (g⁻¹ * x * g) = p := by
      rw [show g⁻¹ * x * g = MulAut.conj g⁻¹ x by simp, MulEquiv.orderOf_eq,
        hx]
    obtain ⟨m', hm', hxm'⟩ := exists_mem_conjSub_of_mem hS hSM hord hxg'
    have hxB : x ∈ conjSub (g * m') S := by
      rw [← conjSub_mul, mem_conjSub_iff]
      exact hxm'
    have hx1 : x ≠ 1 := fun h1 => (Fact.out : p.Prime).one_lt.ne' (by rw [← hx, h1, orderOf_one])
    have hAB : isoRel p (conjSub m S) (conjSub (g * m') S) := by
      refine ⟨isSylowOf_conjSub hS m, isSylowOf_conjSub hS _, bot_lt_iff_ne_bot.mpr fun h => ?_⟩
      exact hx1 ((mem_bot.mp (h ▸ (⟨hxm, hxB⟩ : x ∈ conjSub m S ⊓ conjSub (g * m') S))))
    have hB : Relation.EqvGen (isoRel p) (conjSub g S) (conjSub (g * m') S) := by
      have h := eqvGen_conjSub (mem_classStab.mp hm') g
      rwa [conjSub_mul] at h
    exact .trans _ _ _ (mem_classStab.mp hm) (.trans _ _ _ (.rel _ _ hAB) (.symm _ _ hB))

private theorem le_of_isoRel {M A B : Subgroup G} (hM : IsStronglyPEmbedded p M)
    (h : isoRel p A B) (hAM : A ≤ M) : B ≤ M := by
  obtain ⟨hA, hB, hAB⟩ := h
  obtain ⟨k, hBk⟩ := exists_eq_conjSub hA hB
  by_cases hkM : k ∈ M
  · calc B = conjSub k A := hBk
      _ ≤ conjSub k M := map_mono hAM
      _ = M := conjSub_eq_self hkM
  · refine absurd ((dvd_card_of_bot_lt (hA.isPGroup.to_le inf_le_left) hAB).trans
      (card_dvd_of_le (inf_le_inf hAM ?_))) (hM.2.2 k hkM)
    rw [hBk]
    exact map_mono hAM

private theorem le_iff_of_eqvGen {M A B : Subgroup G} (hM : IsStronglyPEmbedded p M)
    (h : Relation.EqvGen (isoRel p) A B) : A ≤ M ↔ B ≤ M := by
  induction h with
  | rel X Y hXY =>
    refine ⟨le_of_isoRel hM hXY, le_of_isoRel hM ?_⟩
    obtain ⟨hX, hY, hXY⟩ := hXY
    exact ⟨hY, hX, by rwa [inf_comm]⟩
  | refl X => exact Iff.rfl
  | symm X Y _ ih => exact ih.symm
  | trans X Y Z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem isPIsolatedOver_top_bot_iff :
    IsPIsolatedOver p (⊤ : Subgroup G) ⊥ ↔ ∃ M : Subgroup G, IsStronglyPEmbedded p M := by
  constructor
  · rintro ⟨S, T, hS, hT, hST⟩
    exact ⟨classStab p S, isStronglyPEmbedded_classStab hS hT hST⟩
  · rintro ⟨M, hM⟩
    obtain ⟨S, hS', hSM⟩ := hM.exists_isSylowOf_le
    have hS : IsSylowOf p S ⊤ := isSylowOf_iff.mpr hS'
    obtain ⟨g, hg⟩ : ∃ g : G, g ∉ M := by
      by_contra h
      exact hM.1 (eq_top_iff.mpr fun x _ => not_not.mp fun hx => h ⟨x, hx⟩)
    refine ⟨S, conjSub g S, hS, isSylowOf_conjSub hS g, fun hE => ?_⟩
    have hgS : conjSub g S ≤ M := (le_iff_of_eqvGen hM hE).mp hSM
    have hpS : p ∣ Nat.card (conjSub g S) := by
      rw [card_conjSub]
      exact dvd_card_of_isSylowOf hS (hM.2.1.trans (card_dvd_of_le le_top))
    exact hM.2.2 g hg (hpS.trans (card_dvd_of_le (le_inf hgS (map_mono hSM))))

end Embedded

theorem isStronglyPEmbedded_two_iff_fusionStronglyEmbedded {M : Subgroup G} :
    IsStronglyPEmbedded 2 M ↔ CFSG.Open.fusionStronglyEmbedded M := by
  constructor
  · rintro ⟨hne, hdvd, h⟩
    refine ⟨hne, even_iff_two_dvd.mpr hdvd, fun g hg => Nat.not_even_iff_odd.mp fun he => ?_⟩
    exact h g⁻¹ (fun h' => hg (inv_mem_iff.mp h')) (even_iff_two_dvd.mp he)
  · rintro ⟨hne, hev, h⟩
    refine ⟨hne, even_iff_two_dvd.mp hev, fun g hg hdvd => ?_⟩
    have h' := h g⁻¹ (fun h' => hg (inv_mem_iff.mp h'))
    rw [inv_inv] at h'
    exact Nat.not_even_iff_odd.mpr h' (even_iff_two_dvd.mpr hdvd)

theorem isPIsolatedOver_two_iff_fusionStronglyEmbedded [Finite G] :
    IsPIsolatedOver 2 (⊤ : Subgroup G) ⊥ ↔ ∃ M : Subgroup G, CFSG.Open.fusionStronglyEmbedded M :=
  isPIsolatedOver_top_bot_iff.trans
    (exists_congr fun _ => isStronglyPEmbedded_two_iff_fusionStronglyEmbedded)

section Map

variable [Finite G] [Fact p.Prime] {G' : Type*} [Group G'] [Finite G'] {f : G →* G'}

omit [Finite G'] in
private theorem ker_le_of_isSylowOf (hker : IsPGroup p f.ker) {P K : Subgroup G}
    (hP : IsSylowOf p P K) (hkK : f.ker ≤ K) : f.ker ≤ P := by
  have h := hP.eq_of_le le_sup_left (sup_le hP.le hkK) (hP.isPGroup.to_sup_of_normal_right hker)
  rw [← h]
  exact le_sup_right

private theorem isSylowOf_map {P K : Subgroup G} (hP : IsSylowOf p P K) (hk : f.ker ≤ P) :
    IsSylowOf p (P.map f) (K.map f) := by
  rw [isSylowOf_iff] at hP ⊢
  obtain ⟨hPK, hPp, hidx⟩ := hP
  refine ⟨map_mono hPK, hPp.map f, ?_⟩
  rwa [relIndex_map_map, sup_eq_left.mpr hk, sup_eq_left.mpr (hk.trans hPK)]

private theorem isSylowOf_comap (hf : Function.Surjective f) (hker : IsPGroup p f.ker)
    {Q : Subgroup G'} {K : Subgroup G} (hkK : f.ker ≤ K) (hQ : IsSylowOf p Q (K.map f)) :
    IsSylowOf p (Q.comap f) K := by
  rw [isSylowOf_iff] at hQ ⊢
  obtain ⟨hQK, hQp, hidx⟩ := hQ
  have hkQ : f.ker ≤ Q.comap f := fun x hx => by
    rw [mem_comap, (MonoidHom.mem_ker).mp hx]
    exact Q.one_mem
  refine ⟨?_, hQp.comap_of_ker_isPGroup f hker, ?_⟩
  · calc Q.comap f ≤ (K.map f).comap f := comap_mono hQK
      _ = K := by rw [comap_map_eq, sup_eq_left.mpr hkK]
  · have h := relIndex_map_map f (Q.comap f) K
    rw [map_comap_eq_self_of_surjective hf, sup_eq_left.mpr hkQ, sup_eq_left.mpr hkK] at h
    rwa [← h]

omit [Finite G] [Finite G'] in
private theorem lt_inf_map_iff (hf : Function.Surjective f) {H A B : Subgroup G}
    (hH : f.ker ≤ H) (hA : f.ker ≤ A) (hB : f.ker ≤ B) :
    H.map f < A.map f ⊓ B.map f ↔ H < A ⊓ B := by
  rw [← comap_lt_comap_of_surjective hf, comap_inf, comap_map_eq, comap_map_eq, comap_map_eq,
    sup_eq_left.mpr hH, sup_eq_left.mpr hA, sup_eq_left.mpr hB]

theorem isPIsolatedOver_map_iff (hf : Function.Surjective f) (hker : IsPGroup p f.ker)
    {H K : Subgroup G} (hkH : f.ker ≤ H) (hkK : f.ker ≤ K) :
    IsPIsolatedOver p (K.map f) (H.map f) ↔ IsPIsolatedOver p K H := by
  have hkQ : ∀ Q : Subgroup G', f.ker ≤ Q.comap f := fun Q x hx => by
    rw [mem_comap, (MonoidHom.mem_ker).mp hx]
    exact Q.one_mem
  constructor
  · rintro ⟨S, T, hS, hT, hST⟩
    refine ⟨S.comap f, T.comap f, isSylowOf_comap hf hker hkK hS,
      isSylowOf_comap hf hker hkK hT, fun hE => hST ?_⟩
    have h : Relation.EqvGen (fun A B : Subgroup G' => IsSylowOf p A (K.map f) ∧
        IsSylowOf p B (K.map f) ∧ H.map f < A ⊓ B) ((S.comap f).map f) ((T.comap f).map f) :=
      eqvGen_of_map (Subgroup.map f) (fun A B hAB => by
        obtain ⟨hA, hB, hAB⟩ := hAB
        have hkA := ker_le_of_isSylowOf hker hA hkK
        have hkB := ker_le_of_isSylowOf hker hB hkK
        exact ⟨isSylowOf_map hA hkA, isSylowOf_map hB hkB,
          (lt_inf_map_iff hf hkH hkA hkB).mpr hAB⟩) hE
    rwa [map_comap_eq_self_of_surjective hf, map_comap_eq_self_of_surjective hf] at h
  · rintro ⟨S, T, hS, hT, hST⟩
    have hkS := ker_le_of_isSylowOf hker hS hkK
    have hkT := ker_le_of_isSylowOf hker hT hkK
    refine ⟨S.map f, T.map f, isSylowOf_map hS hkS, isSylowOf_map hT hkT, fun hE => hST ?_⟩
    have h : Relation.EqvGen (fun A B : Subgroup G => IsSylowOf p A K ∧ IsSylowOf p B K ∧
        H < A ⊓ B) ((S.map f).comap f) ((T.map f).comap f) :=
      eqvGen_of_map (Subgroup.comap f) (fun A B hAB => by
        obtain ⟨hA, hB, hAB⟩ := hAB
        refine ⟨isSylowOf_comap hf hker hkK hA, isSylowOf_comap hf hker hkK hB, ?_⟩
        rw [← lt_inf_map_iff hf hkH (hkQ A) (hkQ B), map_comap_eq_self_of_surjective hf,
          map_comap_eq_self_of_surjective hf]
        exact hAB) hE
    rwa [comap_map_eq, comap_map_eq, sup_eq_left.mpr hkS, sup_eq_left.mpr hkT] at h

end Map

section Quotient

variable [Finite G] [Fact p.Prime]

theorem isPIsolatedOver_iff_quotient {H K : Subgroup G} (hHK : H ≤ K) (hH : IsPGroup p H)
    [(H.subgroupOf K).Normal] :
    IsPIsolatedOver p K H ↔ IsPIsolatedOver p (⊤ : Subgroup (K ⧸ H.subgroupOf K)) ⊥ := by
  rw [← isPIsolatedOver_subgroupOf_iff hHK le_rfl, subgroupOf_self]
  have hf : Function.Surjective (QuotientGroup.mk' (H.subgroupOf K)) :=
    QuotientGroup.mk'_surjective _
  have hker := QuotientGroup.ker_mk' (H.subgroupOf K)
  have key := isPIsolatedOver_map_iff (p := p) hf (by rw [hker]; exact hH.comap_subtype)
    (H := H.subgroupOf K) (K := ⊤) hker.le le_top
  rw [map_top_of_surjective _ hf, QuotientGroup.map_mk'_self] at key
  exact key.symm

end Quotient

section Subnormal

variable [Finite G] [Fact p.Prime]

private theorem not_le_and_dvd_of_isSubnormal {M Y : Subgroup G}
    (hM : IsStronglyPEmbedded p M) (hY : Y.IsSubnormal) (hp : p ∣ Nat.card Y) :
    ¬ Y ≤ M ∧ p ∣ Nat.card (Y ⊓ M : Subgroup G) := by
  obtain ⟨S, hS', hSM⟩ := hM.exists_isSylowOf_le
  have hS : IsSylowOf p S ⊤ := isSylowOf_iff.mpr hS'
  have hdvd : ∀ g : G, p ∣ Nat.card (conjSub g S ⊓ Y : Subgroup G) := fun g =>
    dvd_card_of_isSylowOf (isSylowOf_inf_of_isSubnormal (isSylowOf_conjSub hS g) hY) hp
  refine ⟨fun hYM => ?_, ?_⟩
  · obtain ⟨g, hg⟩ : ∃ g : G, g ∉ M := by
      by_contra h
      exact hM.1 (eq_top_iff.mpr fun x _ => not_not.mp fun hx => h ⟨x, hx⟩)
    refine hM.2.2 g hg ((hdvd g).trans (card_dvd_of_le fun x hx => ?_))
    exact ⟨hYM hx.2, map_mono hSM hx.1⟩
  · have h := hdvd 1
    rw [conjSub_one] at h
    exact h.trans (card_dvd_of_le fun x hx => ⟨hx.2, hSM hx.1⟩)

theorem IsPIsolatedOver.of_isSubnormal_le (h : IsPIsolatedOver p (⊤ : Subgroup G) ⊥)
    {Y Z : Subgroup G} (hY : Y.IsSubnormal) (hp : p ∣ Nat.card Y) (hYZ : Y ≤ Z) :
    IsPIsolatedOver p Z ⊥ := by
  obtain ⟨M, hM⟩ := isPIsolatedOver_top_bot_iff.mp h
  obtain ⟨hYM, hYMp⟩ := not_le_and_dvd_of_isSubnormal hM hY hp
  have hZM : ¬ Z ≤ M := fun hZM => hYM (hYZ.trans hZM)
  have hZp : p ∣ Nat.card (Z ⊓ M : Subgroup G) :=
    hYMp.trans (card_dvd_of_le (inf_le_inf_right M hYZ))
  have hZ := isPIsolatedOver_top_bot_iff.mpr ⟨_, hM.subgroupOf hZM hZp⟩
  have key := isPIsolatedOver_subgroupOf_iff (p := p) (H := ⊥) (K := Z) (K' := Z) bot_le le_rfl
  rw [subgroupOf_self, bot_subgroupOf] at key
  exact key.mp hZ

theorem IsPIsolatedOver.of_isSubnormal_le_over {H K Y Z : Subgroup G}
    (h : IsPIsolatedOver p K H) (hH : IsPGroup p H) (hKN : K ≤ normalizer (H : Set G))
    (hHY : H ≤ Y) (hYZ : Y ≤ Z) (hZK : Z ≤ K) (hY : (Y.subgroupOf K).IsSubnormal)
    (hp : p ∣ H.relIndex Y) : IsPIsolatedOver p Z H := by
  have hHK : H ≤ K := hHY.trans (hYZ.trans hZK)
  have : (H.subgroupOf K).Normal := (normal_subgroupOf_iff_le_normalizer hHK).mpr hKN
  have hf : Function.Surjective (QuotientGroup.mk' (H.subgroupOf K)) :=
    QuotientGroup.mk'_surjective _
  have hker := QuotientGroup.ker_mk' (H.subgroupOf K)
  have hcard : Nat.card ((Y.subgroupOf K).map (QuotientGroup.mk' (H.subgroupOf K))) =
      H.relIndex Y := by
    rw [← relIndex_ker, hker, relIndex_subgroupOf (hYZ.trans hZK)]
  have hZbar := ((isPIsolatedOver_iff_quotient hHK hH).mp h).of_isSubnormal_le (hY.map hf)
    (hcard ▸ hp) (map_mono (show Y.subgroupOf K ≤ Z.subgroupOf K from fun x hx => hYZ hx))
  have key := isPIsolatedOver_map_iff (p := p) hf (by rw [hker]; exact hH.comap_subtype)
    (H := H.subgroupOf K) (K := Z.subgroupOf K) hker.le
    (by rw [hker]; exact fun x hx => hHY.trans hYZ hx)
  rw [QuotientGroup.map_mk'_self] at key
  exact (isPIsolatedOver_subgroupOf_iff hHK hZK).mp (key.mp hZbar)

end Subnormal

section Two

variable [Finite G]

private theorem isConj_of_isPIsolatedOver (h : IsPIsolatedOver 2 (⊤ : Subgroup G) ⊥)
    {s t : G} (hs : orderOf s = 2) (ht : orderOf t = 2) : IsConj s t := by
  obtain ⟨M, hM⟩ := isPIsolatedOver_two_iff_fusionStronglyEmbedded.mp h
  exact CFSG.ComponentClassification.Sol78.isConj_of_isStronglyEmbedded hM hs ht

theorem IsPIsolatedOver.mem_of_isSubnormal (h : IsPIsolatedOver 2 (⊤ : Subgroup G) ⊥)
    {Y : Subgroup G} (hY : Y.IsSubnormal) (hev : Even (Nat.card Y)) {t : G}
    (ht : orderOf t = 2) : t ∈ Y := by
  induction hY generalizing t with
  | top => exact mem_top t
  | step H K hHK hK hN ih =>
    have hevK : Even (Nat.card K) :=
      even_iff_two_dvd.mpr ((even_iff_two_dvd.mp hev).trans (card_dvd_of_le hHK))
    have htK : t ∈ K := ih hevK ht
    have hKiso := h.of_isSubnormal_le hK (even_iff_two_dvd.mp hevK) le_rfl
    have key := isPIsolatedOver_subgroupOf_iff (p := 2) (H := ⊥) (K := K) (K' := K) bot_le le_rfl
    rw [subgroupOf_self, bot_subgroupOf] at key
    obtain ⟨⟨s, hsH⟩, hs⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hev)
    rw [orderOf_mk] at hs
    obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_of_isPIsolatedOver (key.mpr hKiso)
      (s := ⟨s, hHK hsH⟩) (t := ⟨t, htK⟩) (by rw [orderOf_mk, hs]) (by rw [orderOf_mk, ht]))
    have hmem := hN.conj_mem ⟨s, hHK hsH⟩ hsH c
    rw [hc] at hmem
    exact hmem

end Two

end CFSG.GroupTheory
