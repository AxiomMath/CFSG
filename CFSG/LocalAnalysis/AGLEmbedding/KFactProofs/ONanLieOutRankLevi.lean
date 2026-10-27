module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutBasic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTits
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabHub

public section

namespace CFSG.AGLEmbedding.LieOut

open CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
open CFSG.ComponentClassification

section Node

variable {K : Type*} [Group K]

structure QuasiNode (D : UniversalRootDatum K) (p : ℕ) (i : Fin D.rank) : Prop where
  quasisimple : CFSG.Open.IsQuasisimple ↥(rankOne D.rootGroup i)
  sq_dvd : p ^ 2 ∣ Nat.card ↥(rankOne D.rootGroup i)
  center_coprime : ¬ p ∣ Nat.card ↥(Subgroup.center ↥(rankOne D.rootGroup i))

theorem QuasiNode.map [Finite K] {Y : Type*} [Group Y] {p : ℕ} (hp : p.Prime) (π : K →* Y)
    (hker : π.ker ≤ Subgroup.center K) {D : UniversalRootDatum K} {i : Fin D.rank}
    (h : QuasiNode D p i) :
    CFSG.Open.IsQuasisimple ↥((rankOne D.rootGroup i).map π) ∧
      p ^ 2 ∣ Nat.card ↥((rankOne D.rootGroup i).map π) := by
  set G := rankOne D.rootGroup i with hG
  set φ : ↥G →* Y := π.comp G.subtype with hφ
  have hrange : φ.range = G.map π := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
  have hkerc : φ.ker ≤ Subgroup.center ↥G := by
    intro g hg
    have hgc := hker (show (g : K) ∈ π.ker from hg)
    rw [Subgroup.mem_center_iff] at hgc ⊢
    intro s
    exact Subtype.ext (hgc s)
  have hne : φ.ker ≠ ⊤ := by
    intro htop
    have : Nontrivial ↥G := Quasisimple.nontrivial h.quasisimple
    obtain ⟨g, hg⟩ := exists_ne (1 : ↥G)
    have hab : IsMulCommutative ↥G :=
      ⟨⟨fun a b => ((Subgroup.mem_center_iff.mp (hkerc (htop ▸ Subgroup.mem_top a))) b).symm⟩⟩
    have hperf : Group.IsPerfect ↥G := ⟨h.quasisimple.1⟩
    exact hg (Group.IsPerfect.subsingleton_of_isMulCommutative.elim g 1)
  refine ⟨?_, ?_⟩
  · have := Quasisimple.range_quasisimple_of_ker_ne_top h.quasisimple φ hne
    rwa [hrange] at this
  · have hcard : Nat.card ↥G = Nat.card φ.range * Nat.card φ.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
    have hnd : ¬ p ∣ Nat.card φ.ker := fun hd =>
      h.center_coprime (hd.trans (Subgroup.card_dvd_of_le hkerc))
    have hcop : Nat.Coprime (p ^ 2) (Nat.card φ.ker) :=
      Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd)
    rw [← hrange]
    exact hcop.dvd_of_dvd_mul_right (hcard ▸ h.sq_dvd)

end Node

section Extraction

variable {K Y : Type*} [Group K] [Group Y] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

theorem _root_.CFSG.AGLEmbedding.ParabHub.BorelQuotient.exists_quasisimple_of_lt [Finite K]
    (h : BorelQuotient D n H π M) {p : ℕ}
    (hp : p.Prime) (hnode : ∀ i, QuasiNode D p i) {J : Subgroup Y}
    (hBJ : (borel D H).map π ≤ J) (hne : J ≠ (borel D H).map π) :
    ∃ V : Subgroup Y, V ≤ J ∧ CFSG.Open.IsQuasisimple ↥V ∧ p ^ 2 ∣ Nat.card V := by
  have hBA : borel D H ≤ J.comap π := fun b hb => hBJ ⟨b, hb, rfl⟩
  have hAne : J.comap π ≠ borel D H := by
    intro h'
    apply hne
    rw [← Subgroup.map_comap_eq_self_of_surjective h.surj J, h']
  obtain ⟨i₀, hi₀⟩ := negIndices_nonempty_of_ne h.ct h.extras hBA hAne
  have hle : rankOne D.rootGroup i₀ ≤ J.comap π := rankOne_le_of_mem_negIndices hBA hi₀
  obtain ⟨hq, hsq⟩ := (hnode i₀).map hp π (fun z hz => h.ker_central z hz)
  exact ⟨(rankOne D.rootGroup i₀).map π, Subgroup.map_le_iff_le_comap.2 hle, hq, hsq⟩

end Extraction

section Lift

theorem exists_quasisimple_lift {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y}
    (hJZ : ∀ z ∈ Subgroup.center ↥L, (z : Y) ∈ J)
    {V : Subgroup (↥L ⧸ Subgroup.center ↥L)} (hV : V ≤ quotImage L J)
    (hq : CFSG.Open.IsQuasisimple ↥V) {p : ℕ} (hsq : p ^ 2 ∣ Nat.card V) :
    ∃ X : Subgroup Y, X ≤ J ∧ CFSG.Open.IsQuasisimple ↥X ∧ p ^ 2 ∣ Nat.card X := by
  set θ : ↥L →* ↥L ⧸ Subgroup.center ↥L := QuotientGroup.mk' (Subgroup.center ↥L) with hθ
  have hθs : Function.Surjective θ := QuotientGroup.mk'_surjective _
  set W : Subgroup ↥L := V.comap θ with hW
  set q : ↥W →* ↥V := (θ.comp W.subtype).codRestrict V (fun x => x.2) with hqdef
  have hqs : Function.Surjective q := by
    intro v
    obtain ⟨l, hl⟩ := hθs v
    exact ⟨⟨l, by rw [hW, Subgroup.mem_comap, hl]; exact v.2⟩, Subtype.ext hl⟩
  have hqk : q.ker ≤ Subgroup.center ↥W := by
    intro x hx
    have h1 : θ (x : ↥L) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    have h2 : (x : ↥L) ∈ Subgroup.center ↥L := (QuotientGroup.eq_one_iff _).1 h1
    rw [Subgroup.mem_center_iff] at h2 ⊢
    intro w
    exact Subtype.ext (h2 w)
  have hperf : Group.IsPerfect ↥V := ⟨hq.1⟩
  have hq0 : CFSG.Open.IsQuasisimple ↥(commutator ↥W) :=
    CentralExtensions.derived_quasisimple hq q hqs hqk
  set ι : ↥W →* Y := L.subtype.comp W.subtype with hι
  have hιinj : Function.Injective ι := Subtype.val_injective.comp Subtype.val_injective
  refine ⟨(commutator ↥W).map ι, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    have hxV : θ (x : ↥L) ∈ quotImage L J := hV x.2
    obtain ⟨l, hlJ, hl⟩ := mem_quotImage.1 hxV
    have hz : l⁻¹ * (x : ↥L) ∈ Subgroup.center ↥L := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      have : (QuotientGroup.mk (x : ↥L) : ↥L ⧸ Subgroup.center ↥L) = θ x := rfl
      rw [this, ← hl, inv_mul_cancel]
    have hxe : ((x : ↥L) : Y) = (l : Y) * ((l⁻¹ * (x : ↥L) : ↥L) : Y) := by simp
    show ((x : ↥L) : Y) ∈ J
    rw [hxe]
    exact J.mul_mem hlJ (hJZ _ hz)
  · exact Components.quasisimple_of_equiv
      (Subgroup.equivMapOfInjective (commutator ↥W) ι hιinj).symm hq0
  · have hmap : (commutator ↥W).map q = ⊤ := CentralExtensions.derived_map_eq_top q hqs
    have h1 : Nat.card ↥V ∣ Nat.card ↥(commutator ↥W) := by
      have := Subgroup.card_map_dvd (commutator ↥W) q
      rwa [hmap, Subgroup.card_top] at this
    rw [Subgroup.card_map_of_injective hιinj]
    exact hsq.trans h1

end Lift

section Parabolic

open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.AGLEmbedding.TwoGenInner (sylowOfIsSylowTwoOf mem_normalizer_of_mem_normalizer_map)

theorem exists_quasisimple_of_borelQuotient {Y : Type} [Group Y] [Finite Y] {L T J : Subgroup Y}
    (hT : IsSylowTwoOf T L) (hNJ : L ⊓ Subgroup.normalizer (T : Set Y) ≤ J) (hJL : J ≤ L)
    (hnB : ∀ T' : Subgroup Y, IsSylowTwoOf T' L → J ≠ L ⊓ Subgroup.normalizer (T' : Set Y))
    {K : Type} [Group K] [Finite K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K} {π : K →* ↥L ⧸ Subgroup.center ↥L} {M : ℕ}
    (h : BorelQuotient D n H π M) {p : ℕ} (hp : p.Prime) (hnode : ∀ i, QuasiNode D p i) :
    ∃ X : Subgroup Y, X ≤ J ∧ CFSG.Open.IsQuasisimple ↥X ∧ p ^ 2 ∣ Nat.card X := by
  obtain ⟨π', hπ', hker, hS⟩ := h.exists_conj_eq (barSylow hT)
  have hQ : BorelQuotient D n H π' M :=
    { ct := h.ct, extras := h.extras, pGroup := h.pGroup, surj := hπ', odd := h.odd
      torus_pow := h.torus_pow
      ker_central := fun z hz => h.ker_central z (hker ▸ hz)
      ker_pow := fun z hz => h.ker_pow z (hker ▸ hz) }
  have hNπ := hQ.normalizer_map_posUnipotent
  rw [← hS] at hNπ
  have hBJ : (borel D H).map π' ≤ quotImage L J :=
    hNπ ▸ normalizer_barSylow_le_quotImage hT hNJ
  have hne : quotImage L J ≠ (borel D H).map π' := by
    intro heq
    apply hnB T hT
    refine le_antisymm (fun l hl => ?_) hNJ
    have hlL : l ∈ L := hJL hl
    have hmem : (QuotientGroup.mk (⟨l, hlL⟩ : L) : ↥L ⧸ Subgroup.center ↥L) ∈ quotImage L J :=
      mem_quotImage.2 ⟨⟨l, hlL⟩, hl, rfl⟩
    rw [heq, ← hNπ] at hmem
    have hl' : (⟨l, hlL⟩ : L) ∈ Subgroup.normalizer ((T.subgroupOf L : Subgroup L) : Set L) :=
      mem_normalizer_of_mem_normalizer_map (sylowOfIsSylowTwoOf hT) hmem
    rw [← Subgroup.subgroupOf_normalizer_eq hT.1] at hl'
    exact ⟨hlL, Subgroup.mem_subgroupOf.1 hl'⟩
  obtain ⟨V, hVJ, hVq, hVsq⟩ := hQ.exists_quasisimple_of_lt hp hnode hBJ hne
  exact exists_quasisimple_lift (fun z hz => center_le_of_normalizer_le hT hNJ hz) hVJ hVq hVsq

end Parabolic

end CFSG.AGLEmbedding.LieOut
