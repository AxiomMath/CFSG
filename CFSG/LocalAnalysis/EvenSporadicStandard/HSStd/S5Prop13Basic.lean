module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5CatOuter
public import CFSG.Walter.AStar.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.GroupLemmas

public section

namespace CFSG.EvenSporadicStandard.HSStd.Prop13

open Subgroup CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Induction.Junction
  CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H]

theorem mem_normalizer_of_even_le {A T : Subgroup H}
    (hA : CFSG.Open.standardComponentIsStandard A) {g : H}
    (hT : T ≤ centralizer (A : Set H) ⊓
      (centralizer (A : Set H)).map (MulAut.conj g).toMonoidHom)
    (hev : 2 ∣ Nat.card T) : g ∈ normalizer (A : Set H) := by
  obtain ⟨-, -, htight, hNC, -⟩ := hA
  by_contra hgN
  have hgC : g ∉ normalizer ((centralizer (A : Set H) : Subgroup H) : Set H) := by
    rw [hNC]
    exact hgN
  have hodd := htight g hgC
  have hdvd := Subgroup.card_dvd_of_le hT
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (hev.trans hdvd))

theorem normal_of_even_normal {A N : Subgroup H} (hA : CFSG.Open.standardComponentIsStandard A)
    [N.Normal] (hN : N ≤ centralizer (A : Set H)) (hev : 2 ∣ Nat.card N) : A.Normal := by
  rw [← Subgroup.normalizer_eq_top_iff]
  refine eq_top_iff.2 fun g _ => mem_normalizer_of_even_le hA (T := N) ?_ hev
  intro n hn
  refine ⟨hN hn, ?_⟩
  have hn' : g⁻¹ * n * g ∈ N := Subgroup.Normal.conj_mem' inferInstance n hn g
  exact ⟨g⁻¹ * n * g, hN hn', by
    show g * (g⁻¹ * n * g) * g⁻¹ = n
    group⟩

theorem eq_bot_of_normal_le_centralizer {A N : Subgroup H}
    (hA : CFSG.Open.standardComponentIsStandard A) (hO : CFSG.oddCore H = ⊥) (hAn : ¬ A.Normal)
    [N.Normal] (hN : N ≤ centralizer (A : Set H)) : N = ⊥ := by
  have hodd : Odd (Nat.card N) := by
    by_contra h
    exact hAn (normal_of_even_normal hA hN (even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 h)))
  have : N ≤ CFSG.oddCore H := le_sSup ⟨inferInstance, hodd⟩
  rwa [hO, le_bot_iff] at this

theorem layerIn_normal : (layerIn (⊤ : Subgroup H)).Normal := by
  refine ⟨fun x hx g => ?_⟩
  have h : layerIn (⊤ : Subgroup H) ≤
      (layerIn (⊤ : Subgroup H)).comap (MulAut.conj g).toMonoidHom := by
    refine layerIn_le_iff.2 fun Z hZ => ?_
    rintro z hz
    exact le_layerIn_of_isCompIn (hZ.map_conj (Subgroup.mem_top g)) ⟨z, hz, rfl⟩
  simpa using h hx

theorem isCompIn_top_iff {M : Subgroup H} :
    IsCompIn M ⊤ ↔ CFSG.IsQuasisimple ↥M ∧ M.IsSubnormal := by
  constructor
  · intro h
    refine ⟨h.isQuasisimple, ?_⟩
    have h1 := h.2.2.map (f := (⊤ : Subgroup H).subtype) (fun x => ⟨⟨x, mem_top x⟩, rfl⟩)
    rwa [map_subgroupOf_eq_of_le le_top] at h1
  · rintro ⟨hq, hs⟩
    exact isCompIn_of_subnormal le_top hq hs.subgroupOf

theorem even_card_of_isQuasisimple {Q : Type*} [Group Q] [Finite Q] (hq : CFSG.IsQuasisimple Q) :
    Even (Nat.card Q) := by
  obtain ⟨-, hs, hnc⟩ := hq
  have h1 := CFSG.Walter.even_card_of_isSimpleGroup (G := Q ⧸ center Q) hnc
  exact (even_iff_two_dvd.2 ((even_iff_two_dvd.1 h1).trans (Subgroup.card_quotient_dvd_card _)))

theorem normal_of_subnormal_standard [Finite H] {A : Subgroup H}
    (hA : CFSG.Open.standardComponentIsStandard A) (hq : CFSG.IsQuasisimple ↥A)
    (hs : A.IsSubnormal) : A.Normal := by
  have hAc : IsCompIn A ⊤ := isCompIn_top_iff.2 ⟨hq, hs⟩
  have hconj : ∀ g : H, A.map (MulAut.conj g).toMonoidHom = A := by
    intro g
    by_contra hne
    have hc := hAc.map_conj (Subgroup.mem_top g)
    apply hA.2.2.2.2 g
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [mem_centralizer_iff]
    intro b hb
    exact (hAc.commute_of_ne hc (fun h => hne h.symm) a ha b hb).symm
  refine ⟨fun n hn g => ?_⟩
  have : g * n * g⁻¹ ∈ A.map (MulAut.conj g).toMonoidHom := ⟨n, hn, rfl⟩
  rwa [hconj g] at this

theorem inf_centralizer_eq_bot_of_isCompIn [Finite H] {A M : Subgroup H}
    (hA : CFSG.Open.standardComponentIsStandard A) (hO : CFSG.oddCore H = ⊥) (hAn : ¬ A.Normal)
    (hAE : A ≤ layerIn (⊤ : Subgroup H)) (hM : IsCompIn M ⊤) :
    M ⊓ centralizer (M : Set H) = ⊥ := by
  have := layerIn_normal (H := H)
  have hZ : layerIn (⊤ : Subgroup H) ⊓
      centralizer ((layerIn (⊤ : Subgroup H) : Subgroup H) : Set H) = ⊥ := by
    refine eq_bot_of_normal_le_centralizer hA hO hAn ?_
    intro z hz
    rw [mem_centralizer_iff]
    intro a ha
    exact mem_centralizer_iff.1 hz.2 a (hAE ha)
  refine eq_bot_iff.2 fun x hx => ?_
  have hxE : x ∈ layerIn (⊤ : Subgroup H) := le_layerIn_of_isCompIn hM hx.1
  have hcomm : layerIn (⊤ : Subgroup H) ≤ centralizer ({x} : Set H) := by
    refine layerIn_le_iff.2 fun Z hZ' y hy => ?_
    rw [mem_centralizer_singleton_iff]
    by_cases hZM : Z = M
    · subst hZM
      exact mem_centralizer_iff.1 hx.2 y hy
    · exact hZ'.commute_of_ne hM hZM y hy x hx.1
  have hxC : x ∈ centralizer ((layerIn (⊤ : Subgroup H) : Subgroup H) : Set H) := by
    rw [mem_centralizer_iff]
    intro e he
    exact mem_centralizer_singleton_iff.1 (hcomm he)
  have : x ∈ layerIn (⊤ : Subgroup H) ⊓
      centralizer ((layerIn (⊤ : Subgroup H) : Subgroup H) : Set H) := ⟨hxE, hxC⟩
  rwa [hZ] at this

theorem center_eq_bot_of_isCompIn [Finite H] {A M : Subgroup H}
    (hA : CFSG.Open.standardComponentIsStandard A) (hO : CFSG.oddCore H = ⊥) (hAn : ¬ A.Normal)
    (hAE : A ≤ layerIn (⊤ : Subgroup H)) (hM : IsCompIn M ⊤) : center ↥M = ⊥ := by
  have h := inf_centralizer_eq_bot_of_isCompIn hA hO hAn hAE hM
  refine eq_bot_iff.2 fun x hx => ?_
  have hx' : (x : H) ∈ M ⊓ centralizer (M : Set H) :=
    Subgroup.mem_inf.2 ⟨x.2, mem_centralizer_iff.2 fun m hm =>
      congrArg Subtype.val (Subgroup.mem_center_iff.1 hx ⟨m, hm⟩)⟩
  rw [h, Subgroup.mem_bot] at hx'
  exact Subgroup.mem_bot.2 (Subtype.ext hx')

theorem isSimpleGroup_of_center_eq_bot {M : Subgroup H} (hq : CFSG.IsQuasisimple ↥M)
    (hc : center ↥M = ⊥) : IsSimpleGroup ↥M := by
  let e : (↥M ⧸ center ↥M) ≃* ↥M :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  have := hq.2.1
  exact e.symm.isSimpleGroup

theorem mem_zpowers_cases {t b : H} (ht : orderOf t = 2) (hb : b ∈ zpowers t) :
    b = 1 ∨ b = t := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
  rw [← zpow_mod_orderOf, ht]
  rcases Int.emod_two_eq_zero_or_one k with h0 | h0
  · left
    simp [h0]
  · right
    simp [h0]

theorem mul_self_eq_one_of_orderOf {t : H} (ht : orderOf t = 2) : t * t = 1 := by
  rw [← pow_two, ← ht]
  exact pow_orderOf_eq_one t

theorem conjClosure_zpowers_eq (M : Subgroup H) {t : H} (ht : orderOf t = 2) :
    conjClosure M (zpowers t) = M ⊔ M.map (MulAut.conj t).toMonoidHom := by
  apply le_antisymm
  · refine iSup₂_le fun g hg => ?_
    rcases mem_zpowers_cases ht hg with rfl | rfl
    · rintro _ ⟨m, hm, rfl⟩
      exact Subgroup.mem_sup_left (by simpa using hm)
    · exact le_sup_right
  · exact sup_le (le_conjClosure M _) (map_conj_le_conjClosure (mem_zpowers t))

theorem exists_mul_of_mem_sup_of_commute {P Q : Subgroup H}
    (h : ∀ x ∈ P, ∀ y ∈ Q, x * y = y * x) {a : H} (ha : a ∈ P ⊔ Q) :
    ∃ x ∈ P, ∃ y ∈ Q, x * y = a := by
  have hle : Q ≤ normalizer (P : Set H) := fun y hy =>
    Subgroup.centralizer_le_normalizer (P : Set H)
      (mem_centralizer_iff.2 fun x hx => h x hx y hy)
  have hco := Subgroup.coe_mul_of_right_le_normalizer_left P Q hle
  have ha' : a ∈ ((P ⊔ Q : Subgroup H) : Set H) := ha
  rw [hco] at ha'
  obtain ⟨x, hx, y, hy, rfl⟩ := ha'
  exact ⟨x, hx, y, hy, rfl⟩

theorem centralizer_singleton_le_normalizer {A : Subgroup H}
    (hA : CFSG.Open.standardComponentIsStandard A) {t : H} (ht : orderOf t = 2)
    (htC : t ∈ centralizer (A : Set H)) :
    centralizer ({t} : Set H) ≤ normalizer (A : Set H) := fun _ hg =>
  mem_normalizer_of_commute_involution hA ht htC (mem_centralizer_singleton_iff.1 hg)

theorem isCompIn_centralizer_singleton [Finite H] {A : Subgroup H}
    (hA : CFSG.Open.standardComponentIsStandard A) {t : H} (ht : orderOf t = 2)
    (htC : t ∈ centralizer (A : Set H)) : IsCompIn A (centralizer ({t} : Set H)) := by
  have hq : CFSG.IsQuasisimple ↥A :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff ↥A).2.2.1.2 hA.1
  have hle : A ≤ centralizer ({t} : Set H) := fun x hx =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC x hx)
  exact isCompIn_of_normal hle hq ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).2
    (centralizer_singleton_le_normalizer hA ht htC))

end CFSG.EvenSporadicStandard.HSStd.Prop13
