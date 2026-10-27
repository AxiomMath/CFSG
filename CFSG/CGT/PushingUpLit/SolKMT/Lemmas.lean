module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Lemma25
public import CFSG.LocalAnalysis.ZStar
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.CGT.Timmesfeld75.Defs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingData

public section

namespace CFSG.CGT.PushingUpLit.SolKMT

open CFSG CFSG.CGT.Timmesfeld75 CFSG.ComponentClassification.AschbacherKnownGroup
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.EvenSporadicStandard.Finkelstein77
open CFSG.Assembly (pCoreOf)

section PCore

theorem map_pCore_le {X Y : Type*} [Group X] [Group Y] (p : ℕ) (f : X →* Y)
    (hf : Function.Surjective f) :
    (CFSG.Assembly.pCore p X).map f ≤ CFSG.Assembly.pCore p Y := by
  rw [CFSG.pCore_eq_iSup p X, CFSG.pCore_eq_iSup p Y]
  rw [Subgroup.map_iSup]
  refine iSup_le fun N => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hN => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hp => ?_
  exact le_iSup_of_le (N.map f) (le_iSup_of_le (hN.map f hf) (le_iSup_of_le (hp.map f) le_rfl))

theorem map_pCore_mulEquiv {X Y : Type*} [Group X] [Group Y] (p : ℕ) (e : X ≃* Y) :
    (CFSG.Assembly.pCore p X).map e.toMonoidHom = CFSG.Assembly.pCore p Y := by
  refine le_antisymm (map_pCore_le p e.toMonoidHom e.surjective) ?_
  have h := Subgroup.map_mono (f := e.toMonoidHom)
    (map_pCore_le p e.symm.toMonoidHom e.symm.surjective (X := Y) (Y := X))
  rw [Subgroup.map_map] at h
  have hid : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id Y := by
    ext x; simp
  rwa [hid, Subgroup.map_id] at h

def conjOnK {G : Type*} [Group G] (K : Subgroup G) (g : G)
    (hg : g ∈ Subgroup.normalizer (K : Set G)) : K ≃* K where
  toFun y := ⟨g * y * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg y).mp y.2⟩
  invFun y := ⟨g⁻¹ * y * g, by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (K : Set G)).inv_mem hg)
      (y : G)).mp y.2
    simpa using this⟩
  left_inv y := by ext; simp [mul_assoc]
  right_inv y := by ext; simp [mul_assoc]
  map_mul' a b := by ext; simp [mul_assoc]

theorem conjSubgroup_pCoreOf {G : Type*} [Group G] (K : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    conjSubgroup g (pCoreOf 2 K) = pCoreOf 2 K := by
  have h1 := map_pCore_mulEquiv 2 (conjOnK K g hg)
  unfold conjSubgroup pCoreOf
  rw [Subgroup.map_map]
  have hcomp : ((MulAut.conj g).toMonoidHom).comp K.subtype =
      K.subtype.comp (conjOnK K g hg).toMonoidHom := by
    ext y
    simp [conjOnK, MulAut.conj_apply]
  rw [hcomp, ← Subgroup.map_map, h1]

theorem pCoreOf_eq_of_card_four {G : Type*} [Group G] (K : Subgroup G)
    (hK : Nat.card K = 4) : pCoreOf 2 K = K := by
  have hp : IsPGroup 2 (⊤ : Subgroup K) :=
    IsPGroup.of_card (n := 2) (by rw [Subgroup.card_top, hK]; norm_num)
  have htop : CFSG.Assembly.pCore 2 K = ⊤ := by
    refine top_le_iff.mp ?_
    exact le_sSup ⟨inferInstance, hp⟩
  unfold pCoreOf
  rw [htop]
  ext x
  simp

end PCore

section ZStar

theorem not_inZStar {G : Type} [Group G] [Finite G] (hsimple : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (heven : Even (Nat.card G)) {t : G} (ht : t ≠ 1)
    (h : InZStar t) : False := by
  obtain ⟨N, hN, hodd, hcomm⟩ := h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
  · have hcent : t ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := hcomm g
      rw [hbot, Subgroup.mem_bot] at h1
      calc g * t = (g * t * g⁻¹ * t⁻¹) * t * g := by group
        _ = t * g := by rw [h1]; group
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hc | hc
    · rw [hc, Subgroup.mem_bot] at hcent
      exact ht hcent
    · obtain ⟨a, b, hab⟩ := hnab
      have : a ∈ Subgroup.center G := by rw [hc]; trivial
      rw [Subgroup.mem_center_iff] at this
      exact hab (this b).symm
  · rw [htop, Subgroup.card_top] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) heven

theorem false_of_isolated_involution {G : Type} [Group G] [Finite G] (hsimple : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {t : G} (ht1 : t ≠ 1) (ht2 : t * t = 1)
    (hiso : ∀ g : G, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t) : False := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have hz := CFSG.ZStar.glauberman_zStar G t ht1 ht2 hiso
  have hord : orderOf t = 2 := orderOf_eq_prime (by rwa [← sq] at ht2) ht1
  have heven : Even (Nat.card G) := by
    rw [even_iff_two_dvd, ← hord]
    exact orderOf_dvd_natCard t
  exact not_inZStar hsimple hnab heven ht1 hz

end ZStar

section Dihedral

theorem hasDihedralSylowTwo_transfer {X Y : Type*} [Group X] [Group Y] [Finite X] (e : X ≃* Y)
    (h : HasDihedralSylowTwo X) : HasDihedralSylowTwo Y := by
  obtain ⟨S, n, hn, ⟨eS⟩⟩ := h
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective, n, hn, ⟨?_⟩⟩
  exact ((S : Subgroup X).equivMapOfInjective e.toMonoidHom e.injective).symm.trans eS

theorem hasSemidihedralSylowTwo_transfer {X Y : Type*} [Group X] [Group Y] [Finite X] (e : X ≃* Y)
    (h : HasSemidihedralSylowTwo X) : HasSemidihedralSylowTwo Y := by
  obtain ⟨S, n, hn, ⟨eS⟩⟩ := h
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective, n, hn, ⟨?_⟩⟩
  exact ((S : Subgroup X).equivMapOfInjective e.toMonoidHom e.injective).symm.trans eS

end Dihedral

section Tight

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conjSubgroup_eq_rightConjugate (K : Subgroup G) (g : G) :
    conjSubgroup g K = rightConjugate K g⁻¹ := by
  unfold conjSubgroup rightConjugate
  rw [inv_inv]

theorem isTI_of_tight {K Rg : Subgroup G} (htight : TightlyEmbedded K) (hRK : Rg ≤ K)
    (h2 : IsPGroup 2 Rg) (hchar : ∀ g ∈ Subgroup.normalizer (K : Set G), conjSubgroup g Rg = Rg) :
    IsTI Rg := by
  intro g
  by_cases hg : g ∈ Subgroup.normalizer (K : Set G)
  · right
    rw [hchar g hg]
    exact inf_idem Rg
  · left
    have hg' : g⁻¹ ∉ Subgroup.normalizer (K : Set G) := fun h =>
      hg ((Subgroup.normalizer (K : Set G)).inv_mem_iff.mp h)
    have hT : IsPGroup 2 (Rg ⊓ conjSubgroup g Rg : Subgroup G) := h2.to_le inf_le_left
    refine two_subgroup_of_odd_eq_bot (Rg ⊓ conjSubgroup g Rg) (K ⊓ rightConjugate K g⁻¹) hT
      (htight.2 g⁻¹ hg') (le_inf (inf_le_left.trans hRK) ?_)
    rw [← conjSubgroup_eq_rightConjugate]
    exact inf_le_right.trans (Subgroup.map_mono hRK)

theorem normalizer_eq_of_tight {K Rg : Subgroup G} (htight : TightlyEmbedded K) (hRK : Rg ≤ K)
    (h2 : IsPGroup 2 Rg) (hne : Rg ≠ ⊥)
    (hchar : ∀ g ∈ Subgroup.normalizer (K : Set G), conjSubgroup g Rg = Rg) :
    Subgroup.normalizer (Rg : Set G) = Subgroup.normalizer (K : Set G) := by
  refine le_antisymm (normalizer_two_subgroup_le K Rg htight h2 hRK hne) ?_
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hc := hchar g hg
  constructor
  · intro hx
    have : g * x * g⁻¹ ∈ conjSubgroup g Rg := by
      rw [mem_conjSubgroup]
      simpa [mul_assoc] using hx
    rwa [hc] at this
  · intro hx
    rw [← hc, mem_conjSubgroup] at hx
    simpa [mul_assoc] using hx

theorem false_of_weakly_closed_order_two (hsimple : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {K Rg : Subgroup G} (htight : TightlyEmbedded K)
    (hRK : Rg ≤ K) (h2 : IsPGroup 2 Rg) (hel : CFSG.Open.IsElemAbelian 2 Rg)
    (hchar : ∀ g ∈ Subgroup.normalizer (K : Set G), conjSubgroup g Rg = Rg)
    (hcard : Nat.card Rg = 2)
    (hwc : ∀ g : G, conjSubgroup g Rg ≤ Subgroup.normalizer (K : Set G) →
      conjSubgroup g Rg = Rg) : False := by
  have hne : Rg ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    omega
  obtain ⟨t', ht'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have ht : (t' : G) ∈ Rg := t'.2
  have ht1 : (t' : G) ≠ 1 := fun h => ht' (Subtype.ext h)
  generalize (t' : G) = t at ht ht1
  have ht2 : t * t = 1 := by
    have := hel.2 t ht
    rwa [sq] at this
  have hord : orderOf t = 2 := orderOf_eq_prime (by rwa [← sq] at ht2) ht1
  have hzp : Subgroup.zpowers t = Rg := by
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr ht) ?_
    rw [Nat.card_zpowers, hord, hcard]
  have hN := normalizer_eq_of_tight htight hRK h2 hne hchar
  have hiso : ∀ g : G, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t := by
    intro g hcomm
    have hsne : g * t * g⁻¹ ≠ 1 := by
      intro h
      apply ht1
      calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    have hsN : g * t * g⁻¹ ∈ Subgroup.normalizer (K : Set G) := by
      rw [← hN]
      apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      rw [← hzp] at hu
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      exact ((Commute.zpow_right (show Commute (g * t * g⁻¹) t from hcomm) k)).symm.eq
    have hconj : conjSubgroup g Rg ≤ Subgroup.normalizer (K : Set G) := by
      rw [← hzp]
      have hz : conjSubgroup g (Subgroup.zpowers t) = Subgroup.zpowers (g * t * g⁻¹) := by
        unfold conjSubgroup
        rw [MonoidHom.map_zpowers]
        simp [MulAut.conj_apply]
      rw [hz]
      exact (Subgroup.zpowers_le).mpr hsN
    have heq := hwc g hconj
    have hsmem : g * t * g⁻¹ ∈ Rg := by
      rw [← heq]
      exact ⟨t, ht, by simp [MulAut.conj_apply]⟩
    rw [← hzp] at hsmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hsmem
    have hmod : t ^ (k % (orderOf t : ℤ)) = t ^ k := zpow_mod_orderOf t k
    rw [hord] at hmod
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · exfalso
      apply hsne
      rw [← hk, ← hmod]
      have : k % ((2 : ℕ) : ℤ) = 0 := by exact_mod_cast h0
      rw [this]
      simp
    · rw [← hk, ← hmod]
      have : k % ((2 : ℕ) : ℤ) = 1 := by exact_mod_cast h1
      rw [this]
      simp
  exact false_of_isolated_involution hsimple hnab ht1 ht2 hiso

end Tight

end CFSG.CGT.PushingUpLit.SolKMT
