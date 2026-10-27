module

public import CFSG.CGT.PushingUpLit.CGT6.EmbLift
public import CFSG.CGT.PushingUpLit.CGT6.EmbK

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS6 CFSG.CGT.PushingUp
open scoped commutatorElement

section Pre

variable {V : Type} [CommGroup V] [Finite V]

structure Emb4Pre (G T Y : Subgroup (MulAut V)) : Prop where
  adm : Adm4 G T Y
  kgroup : CFSG.IsKGroup ↥G
  sylow : ∀ T' : Subgroup (MulAut V), T ≤ T' →
    T' ≤ G ⊓ Subgroup.centralizer (Y : Set (MulAut V)) → IsPGroup 2 ↥T' → T' = T
  nolift : ¬ ∃ X, Lift4 G Y X
  ih : ∀ (V' : Type) [CommGroup V'] [Finite V'], (∀ v : V', v ^ 2 = 1) →
    ∀ G' : Subgroup (MulAut V'), Smaller G' G → CFSG.IsKGroup ↥G' → Emb4At G'
  maxY : ∀ T' Y' : Subgroup (MulAut V), Adm4 G T' Y' → (¬ ∃ X, Lift4 G Y' X) →
    Nat.card ↥Y' ≤ Nat.card ↥Y

structure Emb5Pre (G T Y : Subgroup (MulAut V)) : Prop where
  adm : Adm5 G T Y
  kgroup : CFSG.IsKGroup ↥G
  sylow : ∀ T' : Subgroup (MulAut V), T ≤ T' →
    T' ≤ G ⊓ Subgroup.centralizer (Y : Set (MulAut V)) → IsPGroup 2 ↥T' → T' = T
  nolift : ¬ ∃ X, Lift5 G Y X
  ih : ∀ (V' : Type) [CommGroup V'] [Finite V'], (∀ v : V', v ^ 2 = 1) →
    ∀ G' : Subgroup (MulAut V'), Smaller G' G → CFSG.IsKGroup ↥G' → Emb5At G'

end Pre

theorem exists_lex_min (P : ℕ → ℕ → Prop) (h : ∃ a b, P a b) :
    ∃ a b, P a b ∧ ∀ a' b', P a' b' → ¬ (a' < a ∨ (a' = a ∧ b' < b)) := by
  classical
  have h1 : ∃ a, ∃ b, P a b := h
  have h2 : ∃ b, P (Nat.find h1) b := Nat.find_spec h1
  refine ⟨Nat.find h1, Nat.find h2, Nat.find_spec h2, fun a' b' hP hlt => ?_⟩
  rcases hlt with hlt | ⟨rfl, hlt⟩
  · exact Nat.find_min h1 hlt ⟨b', hP⟩
  · exact Nat.find_min h2 hlt hP

def Fail4 (a b : ℕ) : Prop :=
  ∃ (V : Type) (_ : CommGroup V) (_ : Finite V), (∀ v : V, v ^ 2 = 1) ∧
    ∃ G : Subgroup (MulAut V), CFSG.IsKGroup ↥G ∧ ¬ Emb4At G ∧ Nat.card ↥G = a ∧ Nat.card V = b

def Fail5 (a b : ℕ) : Prop :=
  ∃ (V : Type) (_ : CommGroup V) (_ : Finite V), (∀ v : V, v ^ 2 = 1) ∧
    ∃ G : Subgroup (MulAut V), CFSG.IsKGroup ↥G ∧ ¬ Emb5At G ∧ Nat.card ↥G = a ∧ Nat.card V = b

theorem exists_emb4Pre (h : ¬ Emb4All) :
    ∃ (V : Type) (_ : CommGroup V) (_ : Finite V), (∀ v : V, v ^ 2 = 1) ∧
      ∃ G T Y : Subgroup (MulAut V), Emb4Pre G T Y := by
  classical
  have hex : ∃ a b, Fail4 a b := by
    unfold Emb4All at h
    push Not at h
    obtain ⟨V, _, _, hV, G, hK, hG⟩ := h
    exact ⟨_, _, V, inferInstance, inferInstance, hV, G, hK, hG, rfl, rfl⟩
  obtain ⟨a, b, ⟨V, _, _, hV, G, hK, hfail, rfl, rfl⟩, hmin⟩ := exists_lex_min Fail4 hex
  have ih : ∀ (V' : Type) [CommGroup V'] [Finite V'], (∀ v : V', v ^ 2 = 1) →
      ∀ G' : Subgroup (MulAut V'), Smaller G' G → CFSG.IsKGroup ↥G' → Emb4At G' := by
    intro V' _ _ hV' G' hs hK'
    by_contra hG'
    exact hmin _ _ ⟨V', inferInstance, inferInstance, hV', G', hK', hG', rfl, rfl⟩ hs
  have hpair : ∃ T Y : Subgroup (MulAut V), Adm4 G T Y ∧ ¬ ∃ X, Lift4 G Y X := by
    by_contra hne
    apply hfail
    intro T Y hA
    by_contra hX
    exact hne ⟨T, Y, hA, hX⟩
  obtain ⟨T₀, Y₀, hadm₀, hnl₀⟩ := hpair
  let S : Set ℕ := {n | ∃ T Y : Subgroup (MulAut V),
    Adm4 G T Y ∧ (¬ ∃ X, Lift4 G Y X) ∧ Nat.card ↥Y = n}
  have hne : S.Nonempty := ⟨_, T₀, Y₀, hadm₀, hnl₀, rfl⟩
  have hbdd : BddAbove S := ⟨Nat.card (MulAut V), by
    rintro n ⟨T, Y, -, -, rfl⟩
    exact Nat.card_le_card_of_injective _ Subtype.val_injective⟩
  obtain ⟨T₁, Y, hadm₁, hnl₁, hcard⟩ := Nat.sSup_mem hne hbdd
  have hmax : ∀ T' Y' : Subgroup (MulAut V), Adm4 G T' Y' → (¬ ∃ X, Lift4 G Y' X) →
      Nat.card ↥Y' ≤ Nat.card ↥Y := fun T' Y' hA hn =>
    hcard ▸ le_csSup hbdd ⟨T', Y', hA, hn, rfl⟩
  let Ts : Set (Subgroup (MulAut V)) := {T' | T₁ ≤ T' ∧
    T' ≤ G ⊓ Subgroup.centralizer (Y : Set (MulAut V)) ∧ IsPGroup 2 ↥T'}
  have hT₁ : T₁ ∈ Ts := ⟨le_rfl, le_inf hadm₁.hTG hadm₁.le_centralizer, hadm₁.hT2⟩
  obtain ⟨T, hTs, hTmax⟩ := Set.exists_max_image Ts (fun T' => Nat.card ↥T') (Set.toFinite Ts)
    ⟨T₁, hT₁⟩
  refine ⟨V, inferInstance, inferInstance, hV, G, T, Y, ?_, hK, ?_, hnl₁, ih, hmax⟩
  · exact hadm₁.enlarge hTs.1 hTs.2.1 hTs.2.2
  · intro T' hTT' hT'G hT'2
    have hT' : T' ∈ Ts := ⟨hTs.1.trans hTT', hT'G, hT'2⟩
    exact (Subgroup.eq_of_le_of_card_ge hTT' (hTmax T' hT')).symm

theorem exists_emb5Pre (h : ¬ Emb5All) :
    ∃ (V : Type) (_ : CommGroup V) (_ : Finite V), (∀ v : V, v ^ 2 = 1) ∧
      ∃ G T Y : Subgroup (MulAut V), Emb5Pre G T Y := by
  classical
  have hex : ∃ a b, Fail5 a b := by
    unfold Emb5All at h
    push Not at h
    obtain ⟨V, _, _, hV, G, hK, hG⟩ := h
    exact ⟨_, _, V, inferInstance, inferInstance, hV, G, hK, hG, rfl, rfl⟩
  obtain ⟨a, b, ⟨V, _, _, hV, G, hK, hfail, rfl, rfl⟩, hmin⟩ := exists_lex_min Fail5 hex
  have ih : ∀ (V' : Type) [CommGroup V'] [Finite V'], (∀ v : V', v ^ 2 = 1) →
      ∀ G' : Subgroup (MulAut V'), Smaller G' G → CFSG.IsKGroup ↥G' → Emb5At G' := by
    intro V' _ _ hV' G' hs hK'
    by_contra hG'
    exact hmin _ _ ⟨V', inferInstance, inferInstance, hV', G', hK', hG', rfl, rfl⟩ hs
  have hpair : ∃ T Y : Subgroup (MulAut V), Adm5 G T Y ∧ ¬ ∃ X, Lift5 G Y X := by
    by_contra hne
    apply hfail
    intro T Y hA
    by_contra hX
    exact hne ⟨T, Y, hA, hX⟩
  obtain ⟨T₁, Y, hadm₁, hnl₁⟩ := hpair
  let Ts : Set (Subgroup (MulAut V)) := {T' | T₁ ≤ T' ∧
    T' ≤ G ⊓ Subgroup.centralizer (Y : Set (MulAut V)) ∧ IsPGroup 2 ↥T'}
  have hT₁ : T₁ ∈ Ts := ⟨le_rfl, le_inf hadm₁.hTG hadm₁.le_centralizer, hadm₁.hT2⟩
  obtain ⟨T, hTs, hTmax⟩ := Set.exists_max_image Ts (fun T' => Nat.card ↥T') (Set.toFinite Ts)
    ⟨T₁, hT₁⟩
  refine ⟨V, inferInstance, inferInstance, hV, G, T, Y, ?_, hK, ?_, hnl₁, ih⟩
  · exact hadm₁.enlarge hTs.1 hTs.2.1 hTs.2.2
  · intro T' hTT' hT'G hT'2
    have hT' : T' ∈ Ts := ⟨hTs.1.trans hTT', hT'G, hT'2⟩
    exact (Subgroup.eq_of_le_of_card_ge hTT' (hTmax T' hT')).symm

section Gen

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem isKGroup_of_le {G K : Subgroup (MulAut V)} (hG : CFSG.IsKGroup ↥G) (hKG : K ≤ G) :
    CFSG.IsKGroup ↥K :=
  isKGroup_of_surjective (isKGroup_subgroup hG (K.subgroupOf G))
    (Subgroup.subgroupOfEquivOfLe hKG).toMonoidHom (Subgroup.subgroupOfEquivOfLe hKG).surjective

omit [Finite V] in
theorem conjClosure_mono {Y Xt Xt' : Subgroup (MulAut V)} (h : Xt ≤ Xt') :
    conjClosure Y Xt ≤ conjClosure Y Xt' := by
  rw [conjClosure, Subgroup.closure_le]
  rintro _ ⟨g, hg, y, hy, rfl⟩
  exact mem_conjClosure_of_mem (h hg) hy

theorem Lift5.conjClosure_eq {G Y X : Subgroup (MulAut V)} (hY2 : ¬ IsPGroup 2 ↥Y)
    (h : Lift5 G Y X) : conjClosure Y X = X := by
  obtain ⟨hYX, -, -, hc, -⟩ := h
  have hle : conjClosure Y X ≤ X := conjClosure_le hYX
  have hn : ((conjClosure Y X).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 le_normalizer_conjClosure
  exact eq_of_inClassX_yuHol hle hn hc fun hp => hY2 (hp.to_le le_conjClosure)

omit [Finite V] in
theorem isSubnormal_of_conjClosure {G K Y X : Subgroup (MulAut V)} (hYG : Y ≤ G)
    (hNK : conjClosure Y G ≤ K) (hX : conjClosure Y X = X) (hXG : X ≤ G)
    (hsub : (X.subgroupOf K).IsSubnormal) : (X.subgroupOf G).IsSubnormal := by
  have hXN : X ≤ conjClosure Y G := hX ▸ conjClosure_mono hXG
  have hNG : ((conjClosure Y G).subgroupOf G).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (conjClosure_le hYG)).2 le_normalizer_conjClosure
  exact CFSG.GroupTheory.isSubnormal_subgroupOf_trans hXN (conjClosure_le hYG)
    (CFSG.GroupTheory.isSubnormal_subgroupOf_of_le hNK hsub) hNG.isSubnormal

theorem Emb4Pre.gen (hV : ∀ v : V, v ^ 2 = 1) {G T Y : Subgroup (MulAut V)} (h : Emb4Pre G T Y) :
    conjClosure Y G ⊔ T = G := by
  have hYG : Y ≤ G := fun y hy => (h.adm.hYC hy).1
  have hle : conjClosure Y G ⊔ T ≤ G := sup_le (conjClosure_le hYG) h.adm.hTG
  by_contra hne
  have hYK : Y ≤ conjClosure Y G ⊔ T := le_conjClosure.trans le_sup_left
  have hsm : Smaller (conjClosure Y G ⊔ T) G :=
    Or.inl (lt_of_not_ge fun hge => hne (Subgroup.eq_of_le_of_card_ge hle hge))
  obtain ⟨X, hX⟩ := h.ih V hV _ hsm (isKGroup_of_le h.kgroup hle) T Y
    (h.adm.restrict le_sup_right hle hYK)
  apply h.nolift
  refine ⟨X, ?_⟩
  have hcc : conjClosure Y X = X := hX.conjClosure_eq hV (h.adm.hcls.not_isPGroup hV)
  obtain ⟨hYX, hXK, hXsub, h4⟩ := hX
  exact ⟨hYX, hXK.trans hle, isSubnormal_of_conjClosure hYG le_sup_left hcc (hXK.trans hle)
    hXsub, h4⟩

theorem Emb5Pre.gen {G T Y : Subgroup (MulAut V)} (hV : ∀ v : V, v ^ 2 = 1)
    (h : Emb5Pre G T Y) : conjClosure Y G ⊔ T = G := by
  have hYG : Y ≤ G := fun y hy => (h.adm.hYC hy).1
  have hle : conjClosure Y G ⊔ T ≤ G := sup_le (conjClosure_le hYG) h.adm.hTG
  have hY2 : ¬ IsPGroup 2 ↥Y := by
    intro hp
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
    rw [h.adm.h3] at hk
    rcases k with _ | k
    · simp at hk
    · rw [pow_succ] at hk
      omega
  by_contra hne
  have hYK : Y ≤ conjClosure Y G ⊔ T := le_conjClosure.trans le_sup_left
  have hsm : Smaller (conjClosure Y G ⊔ T) G :=
    Or.inl (lt_of_not_ge fun hge => hne (Subgroup.eq_of_le_of_card_ge hle hge))
  obtain ⟨X, hX⟩ := h.ih V hV _ hsm (isKGroup_of_le h.kgroup hle) T Y
    (h.adm.restrict le_sup_right hle hYK)
  apply h.nolift
  refine ⟨X, ?_⟩
  have hcc : conjClosure Y X = X := hX.conjClosure_eq hY2
  obtain ⟨hYX, hXK, hXsub, h4⟩ := hX
  exact ⟨hYX, hXK.trans hle, isSubnormal_of_conjClosure hYG le_sup_left hcc (hXK.trans hle)
    hXsub, h4⟩

end Gen

end CFSG.CGT.PushingUpLit.CGT6
