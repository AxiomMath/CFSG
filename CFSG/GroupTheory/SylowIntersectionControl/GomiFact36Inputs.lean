module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsGF2
public import CFSG.Quasithin.Background.G6Basic

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 (PstarSet)
open scoped Pointwise

variable {W : Type} [CommGroup W]

@[expose] def GomiFact36Hyp (Y S L : Subgroup (MulAut W)) : Prop :=
  IsSylowIn 2 S Y ∧ L ≤ Y ∧ CFSG.IsComponent (L.subgroupOf Y) ∧ ⁅L, sSup (PstarSet S)⁆ ≠ ⊥ ∧
    ¬ fixV S ≤ fixV L ∧ IsGomiChevTwo ↥L ∧
    (IsGomiL3 (↥L ⧸ Subgroup.center ↥L) ∨ IsGomiSp4 (↥L ⧸ Subgroup.center ↥L))

@[expose] def IsGomiNoncentralFactor (L : Subgroup (MulAut W)) (I Z : Subgroup W) : Prop :=
  XMod.IsInv ↥L I ∧ XMod.IsInv ↥L Z ∧ XMod.IsIrrSec ↥L Z I ∧ ¬ XMod.commOf ↥L I ≤ Z

@[expose] def GomiFact36ChiefFactors : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ Y S L : Subgroup (MulAut W), GomiFact36Hyp Y S L →
      (∀ I Z : Subgroup W, I ≤ G6.submoduleClosure L (fixV S) → IsGomiNoncentralFactor L I Z →
        (∃ a : ℕ, 1 ≤ a ∧ BinaryNaturalSL L I Z 3 a) ∨ (∃ a : ℕ, 2 ≤ a ∧ BinaryNaturalSp4 L I Z a) ∨
          AlternatingNatural L I Z 6 ∨ TripleA6Six L I Z) ∧
      ∀ I Z I' Z' : Subgroup W, I ≤ G6.submoduleClosure L (fixV S) →
        I' ≤ G6.submoduleClosure L (fixV S) →
        IsGomiNoncentralFactor L I Z → IsGomiNoncentralFactor L I' Z' → SecIsoL L I Z I' Z'

@[expose] def GomiFact36Overgroups : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L : Subgroup G), IsSylowIn 2 T L → IsGomiChevTwo ↥L →
    (IsGomiL3 (↥L ⧸ Subgroup.center ↥L) ∨ IsGomiSp4 (↥L ⧸ Subgroup.center ↥L)) →
    ∀ P₁ P₂ P₃ : Subgroup G,
      (∀ P ∈ [P₁, P₂, P₃], L ⊓ Subgroup.normalizer (T : Set G) < P ∧ P < L) →
        P₁ = P₂ ∨ P₁ = P₃ ∨ P₂ = P₃

@[expose] def GomiFact36NatStab : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (L T : Subgroup (MulAut W)) (I Z : Subgroup W), IsSylowIn 2 T L →
      ((∃ a : ℕ, 1 ≤ a ∧ BinaryNaturalSL L I Z 3 a) ∨ (∃ a : ℕ, 2 ≤ a ∧ BinaryNaturalSp4 L I Z a) ∨
        AlternatingNatural L I Z 6 ∨ TripleA6Six L I Z) →
      L ⊓ Subgroup.normalizer (T : Set (MulAut W)) <
          L ⊓ MulAction.stabilizer (MulAut W) (commModSub I T Z) ∧
        L ⊓ MulAction.stabilizer (MulAut W) (commModSub I T Z) < L

section Assembly

private theorem smul_eq_self_iff (l : MulAut W) (C : Subgroup W) :
    l • C = C ↔ (∀ u ∈ C, l u ∈ C) ∧ ∀ u ∈ C, l⁻¹ u ∈ C := by
  constructor
  · intro h
    refine ⟨fun u hu => ?_, fun u hu => ?_⟩
    · have := Subgroup.smul_mem_pointwise_smul u l C hu
      rw [h] at this
      exact this
    · rw [← h] at hu
      exact Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp hu
  · rintro ⟨h1, h2⟩
    ext x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    constructor
    · intro hx
      have := h1 _ hx
      simpa using this
    · intro hx
      exact h2 x hx

private theorem mem_commModSub_iff_of_secIsoL {L T : Subgroup (MulAut W)} (hTL : T ≤ L)
    {I Z I' Z' : Subgroup W} (β : ↥I →* ↥I' ⧸ Z'.subgroupOf I')
    (hβ1 : ∀ u : ↥I, β u = 1 ↔ (u : W) ∈ Z)
    (hβ : ∀ (γ : ↥L) (u : ↥I) (m : ↥I') (hu : (γ : MulAut W) (u : W) ∈ I)
      (hm : (γ : MulAut W) (m : W) ∈ I'),
      β u = QuotientGroup.mk m → β ⟨(γ : MulAut W) (u : W), hu⟩ = QuotientGroup.mk ⟨_, hm⟩)
    (hI : ∀ l ∈ L, ∀ u ∈ I, l u ∈ I) (hI' : ∀ l ∈ L, ∀ v ∈ I', l v ∈ I')
    (u : ↥I) (v : ↥I') (huv : β u = QuotientGroup.mk v) :
    (u : W) ∈ commModSub I T Z ↔ (v : W) ∈ commModSub I' T Z' := by
  constructor
  · rintro ⟨-, hu⟩
    refine ⟨v.2, fun t ht => ?_⟩
    have htu := hβ ⟨t, hTL ht⟩ u v (hI t (hTL ht) u u.2) (hI' t (hTL ht) v v.2) huv
    have h1 : β (⟨t u, hI t (hTL ht) u u.2⟩ * u⁻¹) = 1 := (hβ1 _).mpr (hu t ht)
    rw [map_mul, map_inv, htu, huv, mul_inv_eq_one, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at h1
    have h2 : (t v)⁻¹ * (v : W) ∈ Z' := h1
    have h3 : t v * (v : W)⁻¹ = ((t v)⁻¹ * (v : W))⁻¹ := by rw [mul_inv_rev, inv_inv, mul_comm]
    rw [h3]
    exact Z'.inv_mem h2
  · rintro ⟨-, hv⟩
    refine ⟨u.2, fun t ht => ?_⟩
    have htu := hβ ⟨t, hTL ht⟩ u v (hI t (hTL ht) u u.2) (hI' t (hTL ht) v v.2) huv
    have h2 : (t v)⁻¹ * (v : W) ∈ Z' := by
      have h3 : (t v)⁻¹ * (v : W) = (t v * (v : W)⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv, mul_comm]
      rw [h3]
      exact Z'.inv_mem (hv t ht)
    have h1 : β (⟨t u, hI t (hTL ht) u u.2⟩ * u⁻¹) = 1 := by
      rw [map_mul, map_inv, htu, huv, mul_inv_eq_one, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      exact h2
    exact (hβ1 _).mp h1

private theorem forall_mem_commModSub_iff_of_secIsoL {L T : Subgroup (MulAut W)} (hTL : T ≤ L)
    {I Z I' Z' : Subgroup W} (h : SecIsoL L I Z I' Z') {l : MulAut W} (hl : l ∈ L) :
    (∀ u ∈ commModSub I T Z, l u ∈ commModSub I T Z) ↔
      ∀ v ∈ commModSub I' T Z', l v ∈ commModSub I' T Z' := by
  obtain ⟨-, -, -, hI, -, hI', -, β, hβs, hβ1, hβ⟩ := h
  have hIL : ∀ g ∈ L, ∀ u ∈ I, g u ∈ I := fun g hg u hu => hI ⟨g, hg⟩ u hu
  have hIL' : ∀ g ∈ L, ∀ v ∈ I', g v ∈ I' := fun g hg v hv => hI' ⟨g, hg⟩ v hv
  have hmem := mem_commModSub_iff_of_secIsoL (T := T) hTL β hβ1 hβ hIL hIL'
  constructor
  · intro H v hv
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨v, hv.1⟩)
    have huC : (u : W) ∈ commModSub I T Z := (hmem u ⟨v, hv.1⟩ hu).mpr hv
    have hlu := hβ ⟨l, hl⟩ u ⟨v, hv.1⟩ (hIL l hl u u.2) (hIL' l hl v hv.1) hu
    exact (hmem ⟨_, hIL l hl u u.2⟩ ⟨_, hIL' l hl v hv.1⟩ hlu).mp (H u huC)
  · intro H u hu
    obtain ⟨v, hv⟩ : ∃ v : ↥I', (QuotientGroup.mk v : ↥I' ⧸ Z'.subgroupOf I') = β ⟨u, hu.1⟩ :=
      QuotientGroup.mk_surjective _
    have hvC : (v : W) ∈ commModSub I' T Z' := (hmem ⟨u, hu.1⟩ v hv.symm).mp hu
    have hlu := hβ ⟨l, hl⟩ ⟨u, hu.1⟩ v (hIL l hl u hu.1) (hIL' l hl v v.2) hv.symm
    exact (hmem ⟨_, hIL l hl u hu.1⟩ ⟨_, hIL' l hl v v.2⟩ hlu).mpr (H v hvC)

private theorem smul_commModSub_eq_iff_of_secIsoL {L T : Subgroup (MulAut W)} (hTL : T ≤ L)
    {I Z I' Z' : Subgroup W} (h : SecIsoL L I Z I' Z') {l : MulAut W} (hl : l ∈ L) :
    l • commModSub I T Z = commModSub I T Z ↔ l • commModSub I' T Z' = commModSub I' T Z' := by
  rw [smul_eq_self_iff, smul_eq_self_iff, forall_mem_commModSub_iff_of_secIsoL hTL h hl,
    forall_mem_commModSub_iff_of_secIsoL hTL h (L.inv_mem hl)]

theorem smul_commModSub {T : Subgroup (MulAut W)} {s : MulAut W}
    (hs : s ∈ Subgroup.normalizer (T : Set (MulAut W))) (I Z : Subgroup W) :
    s • commModSub I T Z = commModSub (s • I) T (s • Z) := by
  have hs' : s⁻¹ ∈ Subgroup.normalizer (T : Set (MulAut W)) := Subgroup.inv_mem _ hs
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  change (s⁻¹ • x ∈ I ∧ ∀ t ∈ T, t (s⁻¹ • x) * (s⁻¹ • x)⁻¹ ∈ Z) ↔
    (x ∈ s • I ∧ ∀ t ∈ T, t x * x⁻¹ ∈ s • Z)
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  refine and_congr_right fun _ => ⟨fun h t ht => ?_, fun h t ht => ?_⟩
  · rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have ht' : s⁻¹ * t * s⁻¹⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hs' t).mp ht
    have := h _ ht'
    convert this using 1
    simp [MulAut.smul_def, MulAut.mul_apply]
  · have ht' : s * t * s⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hs t).mp ht
    have := Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp (h _ ht')
    convert this using 1
    simp [MulAut.smul_def, MulAut.mul_apply]

theorem mem_normalizer_stab_commModSub {L T : Subgroup (MulAut W)} (hTL : T ≤ L) {s : MulAut W}
    (hsL : s ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hsT : s ∈ Subgroup.normalizer (T : Set (MulAut W))) {I Z : Subgroup W}
    (h : SecIsoL L I Z (s • I) (s • Z)) :
    s ∈ Subgroup.normalizer
      ((L ⊓ MulAction.stabilizer (MulAut W) (commModSub I T Z) : Subgroup (MulAut W)) :
        Set (MulAut W)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro l
  rw [Subgroup.mem_inf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff,
    MulAction.mem_stabilizer_iff]
  have hLiff : l ∈ L ↔ s * l * s⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hsL) l
  constructor
  · rintro ⟨hl, hlC⟩
    have hl' := hLiff.mp hl
    refine ⟨hl', ?_⟩
    rw [smul_commModSub_eq_iff_of_secIsoL hTL h hl', ← smul_commModSub hsT, mul_smul,
      mul_smul, inv_smul_smul, hlC]
  · rintro ⟨hl', hlC⟩
    refine ⟨hLiff.mpr hl', ?_⟩
    rw [smul_commModSub_eq_iff_of_secIsoL hTL h hl', ← smul_commModSub hsT, mul_smul,
      mul_smul, inv_smul_smul] at hlC
    exact smul_left_cancel s hlC

private theorem commOf_le_iff {L : Subgroup (MulAut W)} {I H : Subgroup W} :
    XMod.commOf ↥L I ≤ H ↔ ∀ l ∈ L, ∀ u ∈ I, l u * u⁻¹ ∈ H := by
  rw [XMod.commOf, Subgroup.closure_le]
  constructor
  · intro h l hl u hu
    exact h ⟨⟨l, hl⟩, u, hu, rfl⟩
  · rintro h _ ⟨a, u, hu, rfl⟩
    exact h a a.2 u hu

private theorem commOf_le_bot_of_perfect {L : Subgroup (MulAut W)} (hL : commutator ↥L = ⊤)
    {I Z : Subgroup W} (hIZ : XMod.commOf ↥L I ≤ Z) (hZ : XMod.commOf ↥L Z ≤ ⊥) :
    XMod.commOf ↥L I ≤ ⊥ := by
  rw [commOf_le_iff] at hIZ hZ ⊢
  intro l hl u hu
  have hfix : ∀ g ∈ L, ∀ z ∈ Z, g z = z := fun g hg z hz => by
    have := Subgroup.mem_bot.mp (hZ g hg z hz)
    exact mul_inv_eq_one.mp this
  let f : ↥L →* W :=
    { toFun := fun g => (g : MulAut W) u * u⁻¹
      map_one' := by simp
      map_mul' := fun g h => by
        have hh : (h : MulAut W) u * u⁻¹ ∈ Z := hIZ h h.2 u hu
        have e : (g : MulAut W) ((h : MulAut W) u * u⁻¹) = (h : MulAut W) u * u⁻¹ :=
          hfix g g.2 _ hh
        have e2 : ((g * h : ↥L) : MulAut W) u = (g : MulAut W) ((h : MulAut W) u) := rfl
        rw [e2]
        calc (g : MulAut W) ((h : MulAut W) u) * u⁻¹
            = (g : MulAut W) ((h : MulAut W) u * u⁻¹ * u) * u⁻¹ := by rw [inv_mul_cancel_right]
          _ = (h : MulAut W) u * u⁻¹ * ((g : MulAut W) u * u⁻¹) := by
              rw [map_mul, e]; group
          _ = (g : MulAut W) u * u⁻¹ * ((h : MulAut W) u * u⁻¹) := mul_comm _ _ }
  have hker : commutator ↥L ≤ f.ker := Abelianization.commutator_subset_ker f
  rw [hL] at hker
  have : f ⟨l, hl⟩ = 1 := hker (Subgroup.mem_top _)
  exact Subgroup.mem_bot.mpr this

theorem isGomiNoncentralFactor_smul {L : Subgroup (MulAut W)} {s : MulAut W}
    (hs : s ∈ Subgroup.normalizer (L : Set (MulAut W))) {I Z : Subgroup W}
    (h : IsGomiNoncentralFactor L I Z) : IsGomiNoncentralFactor L (s • I) (s • Z) := by
  have hs' : s⁻¹ ∈ Subgroup.normalizer (L : Set (MulAut W)) := Subgroup.inv_mem _ hs
  have hconj : ∀ g ∈ L, s⁻¹ * g * s ∈ L := fun g hg => by
    have := (Subgroup.mem_normalizer_iff.mp hs' g).mp hg
    rwa [inv_inv] at this
  have hinv : ∀ {J : Subgroup W}, XMod.IsInv ↥L J → XMod.IsInv ↥L (s • J) := by
    intro J hJ a x hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx ⊢
    have := hJ ⟨s⁻¹ * a * s, hconj a a.2⟩ _ hx
    convert this using 1
    simp [MulAut.smul_def, MulAut.mul_apply, Subgroup.smul_def]
  have hinv' : ∀ {J : Subgroup W}, XMod.IsInv ↥L J → XMod.IsInv ↥L (s⁻¹ • J) := by
    intro J hJ a x hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, inv_inv] at hx ⊢
    have := hJ ⟨s * a * s⁻¹, (Subgroup.mem_normalizer_iff.mp hs a).mp a.2⟩ _ hx
    convert this using 1
    simp [MulAut.smul_def, MulAut.mul_apply, Subgroup.smul_def]
  obtain ⟨hI, hZ, ⟨hZI, hirr⟩, hnc⟩ := h
  refine ⟨hinv hI, hinv hZ, ⟨?_, fun J hJ hZJ hJI => ?_⟩, fun hc => hnc ?_⟩
  · exact lt_of_le_of_ne (Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hZI.le)
      fun he => hZI.ne (MulAction.injective s he)
  · have h1 : Z ≤ s⁻¹ • J := by
      rw [← Subgroup.pointwise_smul_le_pointwise_smul_iff (a := s), smul_inv_smul]; exact hZJ
    have h2 : s⁻¹ • J ≤ I := by
      rw [← Subgroup.pointwise_smul_le_pointwise_smul_iff (a := s), smul_inv_smul]; exact hJI
    rcases hirr _ (hinv' hJ) h1 h2 with he | he
    · left; rw [← he, smul_inv_smul]
    · right; rw [← he, smul_inv_smul]
  · rw [commOf_le_iff] at hc ⊢
    intro l hl u hu
    have h1 := hc (s * l * s⁻¹) ((Subgroup.mem_normalizer_iff.mp hs l).mp hl) (s • u)
      (Subgroup.smul_mem_pointwise_smul u s I hu)
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
    convert h1 using 1
    simp [MulAut.smul_def, MulAut.mul_apply]

private theorem apply_mem_submoduleClosure_fixV {Y S : Subgroup (MulAut W)} {s : MulAut W}
    (hs : s ∈ Y) {x : W} (hx : x ∈ G6.submoduleClosure Y (fixV S)) :
    s x ∈ G6.submoduleClosure Y (fixV S) := by
  have hle : (G6.submoduleClosure Y (fixV S)).map s.toMonoidHom ≤
      G6.submoduleClosure Y (fixV S) := by
    rw [G6.submoduleClosure, Subgroup.map_iSup]
    refine iSup_le fun y => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hy => ?_
    rw [Subgroup.map_map]
    refine le_iSup₂_of_le (s * y) (Y.mul_mem hs hy) (le_of_eq ?_)
    congr 1
  exact hle ⟨x, hx, rfl⟩

private theorem fixV_le_submoduleClosure (Y S : Subgroup (MulAut W)) :
    fixV S ≤ G6.submoduleClosure Y (fixV S) := by
  intro x hx
  refine (le_iSup₂_of_le (1 : MulAut W) Y.one_mem le_rfl :
    (fixV S).map ((1 : MulAut W) : MulAut W).toMonoidHom ≤ G6.submoduleClosure Y (fixV S))
    ⟨x, hx, rfl⟩

theorem apply_mem_submoduleClosure_fixV_of_mem_normalizer {S L : Subgroup (MulAut W)}
    {s : MulAut W} (hsS : s ∈ S) (hsN : s ∈ Subgroup.normalizer (L : Set (MulAut W))) {x : W}
    (hx : x ∈ G6.submoduleClosure L (fixV S)) : s x ∈ G6.submoduleClosure L (fixV S) := by
  have hle : (G6.submoduleClosure L (fixV S)).map s.toMonoidHom ≤
      G6.submoduleClosure L (fixV S) := by
    rw [G6.submoduleClosure, Subgroup.map_iSup]
    refine iSup_le fun g => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hg => ?_
    rw [Subgroup.map_map]
    have e : s.toMonoidHom.comp (g : MulAut W).toMonoidHom = (s * g).toMonoidHom :=
      MonoidHom.ext fun _ => rfl
    rw [e]
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hx
    have hsv : s v = v := (mem_fixV.mp hv) s hsS
    have hsv' : s⁻¹ v = v := by
      simpa using congrArg (fun x => s⁻¹ x) hsv.symm
    have hconj : s * g * s⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hsN g).mp hg
    have heq : (s * g).toMonoidHom v = (s * g * s⁻¹).toMonoidHom v := by
      change (s * g) v = (s * g * s⁻¹) v
      calc (s * g) v = s (g v) := by rw [MulAut.mul_apply]
        _ = s (g (s⁻¹ v)) := by rw [hsv']
        _ = (s * g * s⁻¹) v := by rw [MulAut.mul_apply, MulAut.mul_apply]
    rw [heq]
    exact Subgroup.mem_iSup_of_mem (s * g * s⁻¹)
      (Subgroup.mem_iSup_of_mem hconj ⟨v, hv, rfl⟩)
  exact hle ⟨x, hx, rfl⟩

theorem exists_isGomiNoncentralFactor [Finite W] {L : Subgroup (MulAut W)}
    (hL : commutator ↥L = ⊤) {V : Subgroup W} (hV : XMod.IsInv ↥L V)
    (hne : ¬ XMod.commOf ↥L V ≤ ⊥) :
    ∃ I Z : Subgroup W, I ≤ V ∧ IsGomiNoncentralFactor L I Z := by
  classical
  have : Finite (Subgroup W) :=
    Finite.of_injective (fun H : Subgroup W => (H : Set W)) SetLike.coe_injective
  set 𝒮 : Set (Subgroup W) := {I | I ≤ V ∧ XMod.IsInv ↥L I ∧ ¬ XMod.commOf ↥L I ≤ ⊥}
  obtain ⟨I, ⟨hIV, hIinv, hInc⟩, hImin⟩ :=
    WellFounded.has_min wellFounded_lt 𝒮 ⟨V, le_rfl, hV, hne⟩
  have hIbot : ⊥ < I := by
    refine bot_lt_iff_ne_bot.mpr fun hI => hInc ?_
    rw [commOf_le_iff]
    intro l _ u hu
    rw [hI, Subgroup.mem_bot] at hu
    simp [hu]
  set 𝒯 : Set (Subgroup W) := {Z | Z < I ∧ XMod.IsInv ↥L Z}
  obtain ⟨Z, ⟨hZI, hZinv⟩, hZmax⟩ := WellFounded.has_min wellFounded_gt 𝒯
    ⟨⊥, hIbot, fun a l hl => by rw [Subgroup.mem_bot] at hl ⊢; rw [hl, smul_one]⟩
  refine ⟨I, Z, hIV, hIinv, hZinv, ⟨hZI, fun J hJ hZJ hJI => ?_⟩, fun hc => hInc ?_⟩
  · by_cases hJeq : J = I
    · exact Or.inr hJeq
    · left
      have hJlt : J < I := lt_of_le_of_ne hJI hJeq
      by_contra hJZ
      exact hZmax J ⟨hJlt, hJ⟩ (lt_of_le_of_ne hZJ (Ne.symm hJZ))
  · have hZc : XMod.commOf ↥L Z ≤ ⊥ := by
      by_contra hZc
      exact hImin Z ⟨hZI.le.trans hIV, hZinv, hZc⟩ hZI
    exact commOf_le_bot_of_perfect hL hc hZc

private theorem isSylowIn_inf_of_isSubnormal {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {S Y L : Subgroup G} (hS : IsSylowIn p S Y) (hLY : L ≤ Y)
    (hL : (L.subgroupOf Y).IsSubnormal) : IsSylowIn p (S ⊓ L) L := by
  suffices key : ∀ H : Subgroup ↥Y, H.IsSubnormal →
      IsSylowIn p (S ⊓ H.map Y.subtype) (H.map Y.subtype) by
    have := key _ hL
    rwa [Subgroup.subgroupOf_map_subtype, inf_of_le_left hLY] at this
  intro H hH
  induction hH with
  | top =>
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype, inf_of_le_left hS.1]
    exact hS
  | step H K hle _ hN ih =>
    have hle' : H.map Y.subtype ≤ K.map Y.subtype := Subgroup.map_mono hle
    have hN' : ((H.map Y.subtype).subgroupOf (K.map Y.subtype)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hle']
      rintro _ _ ⟨h, hh, rfl⟩ ⟨k, hk, rfl⟩
      exact ⟨_, (Subgroup.normal_subgroupOf_iff hle).mp hN h k hh hk, by simp⟩
    have := ih.inf_normal hle' hN'
    rwa [inf_assoc, inf_of_le_right hle'] at this

theorem exists_mem_normalizer_of_chiefFactors_natStab (hC : GomiFact36ChiefFactors)
    (hS : GomiFact36NatStab) [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1) {Y S L : Subgroup (MulAut W)}
    (hhyp : GomiFact36Hyp Y S L) {s : MulAut W} (hsS : s ∈ S)
    (hsN : s ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    ∃ P₀ : Subgroup (MulAut W),
      L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup (MulAut W)) : Set (MulAut W)) < P₀ ∧ P₀ < L ∧
        s ∈ Subgroup.normalizer (P₀ : Set (MulAut W)) := by
  have : Finite (MulAut W) := Finite.of_injective (fun e : MulAut W => (e : W → W))
    (fun a b h => MulEquiv.ext (congrFun h))
  obtain ⟨hmod, hiso⟩ := hC W hW2 Y S L hhyp
  obtain ⟨hSY, hLY, hLc, -, hfix, hChev, -⟩ := hhyp
  have hT : IsSylowIn 2 (S ⊓ L) L := isSylowIn_inf_of_isSubnormal hSY hLY hLc.2
  have hsT : s ∈ Subgroup.normalizer ((S ⊓ L : Subgroup (MulAut W)) : Set (MulAut W)) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hsS, hsN⟩
  obtain ⟨w, hwS, hwL⟩ := SetLike.not_le_iff_exists.mp hfix
  have hV : XMod.IsInv ↥L (G6.submoduleClosure L (fixV S)) := fun a x hx =>
    apply_mem_submoduleClosure_fixV a.2 hx
  have hne : ¬ XMod.commOf ↥L (G6.submoduleClosure L (fixV S)) ≤ ⊥ := by
    rw [commOf_le_iff]
    intro h
    refine hwL fun l hl => ?_
    exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp
      (h l hl w (fixV_le_submoduleClosure L S hwS)))
  obtain ⟨I, Z, hIV, hIZ⟩ := exists_isGomiNoncentralFactor hChev.1.1.commutator_eq_top hV hne
  have hsIV : s • I ≤ G6.submoduleClosure L (fixV S) := by
    intro x hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
    have := apply_mem_submoduleClosure_fixV_of_mem_normalizer hsS hsN (hIV hx)
    simpa [MulAut.smul_def] using this
  have hiso' := hiso I Z (s • I) (s • Z) hIV hsIV hIZ (isGomiNoncentralFactor_smul hsN hIZ)
  obtain ⟨h01, h02⟩ := hS W hW2 L (S ⊓ L) I Z hT (hmod I Z hIV hIZ)
  exact ⟨_, h01, h02, mem_normalizer_stab_commModSub inf_le_right hsN hsT hiso'⟩

private theorem mem_normalizer_of_overgroups (hO : GomiFact36Overgroups) {G : Type} [Group G]
    [Finite G] {T L : Subgroup G} (hT : IsSylowIn 2 T L) (hChev : IsGomiChevTwo ↥L)
    (hLie : IsGomiL3 (↥L ⧸ Subgroup.center ↥L) ∨ IsGomiSp4 (↥L ⧸ Subgroup.center ↥L)) {s : G}
    (hsL : s ∈ Subgroup.normalizer (L : Set G)) (hsT : s ∈ Subgroup.normalizer (T : Set G))
    {P₀ P : Subgroup G} (h0 : L ⊓ Subgroup.normalizer (T : Set G) < P₀ ∧ P₀ < L)
    (hs0 : s ∈ Subgroup.normalizer (P₀ : Set G))
    (hP : L ⊓ Subgroup.normalizer (T : Set G) < P ∧ P < L) :
    s ∈ Subgroup.normalizer (P : Set G) := by
  set c : G →* G := (MulAut.conj s).toMonoidHom with hcdef
  have hinj : Function.Injective (Subgroup.map c) :=
    Subgroup.map_injective (f := c) (MulAut.conj s).injective
  have hmapL : L.map c = L := Subgroup.mem_normalizer_iff_map_conj_eq.mp hsL
  have hmapN : (L ⊓ Subgroup.normalizer (T : Set G)).map c = L ⊓ Subgroup.normalizer (T : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hsL, Subgroup.le_normalizer hsT⟩)
  have hP₂1 : L ⊓ Subgroup.normalizer (T : Set G) < P.map c := by
    rw [← hmapN]
    exact lt_of_le_of_ne (Subgroup.map_mono hP.1.le) fun h => hP.1.ne (hinj h)
  have hP₂2 : P.map c < L := by
    rw [← hmapL]
    exact lt_of_le_of_ne (Subgroup.map_mono hP.2.le) fun h => hP.2.ne (hinj h)
  have key := hO G T L hT hChev hLie P (P.map c) P₀ (by
    intro Q hQ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ
    rcases hQ with rfl | rfl | rfl
    · exact hP
    · exact ⟨hP₂1, hP₂2⟩
    · exact h0)
  rcases key with h | h | h
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm
  · rw [h]; exact hs0
  · rw [hinj (h.trans (Subgroup.mem_normalizer_iff_map_conj_eq.mp hs0).symm)]
    exact hs0

theorem gomiFact36_of_inputs (hC : GomiFact36ChiefFactors) (hS : GomiFact36NatStab)
    (hO : GomiFact36Overgroups) : GomiFact36 := by
  intro W _ _ hW2 Y S L hSY hLY hLc hPs hfix hChev hLie
  rintro ⟨s, ⟨hsS, hsN⟩, P, hP1, hP2, hsP⟩
  have : Finite (MulAut W) := Finite.of_injective (fun e : MulAut W => (e : W → W))
    (fun a b h => MulEquiv.ext (congrFun h))
  obtain ⟨P₀, h01, h02, hs0⟩ := exists_mem_normalizer_of_chiefFactors_natStab hC hS hW2
    ⟨hSY, hLY, hLc, hPs, hfix, hChev, hLie⟩ hsS hsN
  exact hsP (mem_normalizer_of_overgroups hO (isSylowIn_inf_of_isSubnormal hSY hLY hLc.2) hChev
    hLie hsN (Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hsS, hsN⟩)
    ⟨h01, h02⟩ hs0 ⟨hP1, hP2⟩)

end Assembly

end CFSG.GroupTheory

end
