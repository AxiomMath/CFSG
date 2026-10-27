module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21bStmt
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21bQ8
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open KFactsSmall
open scoped Pointwise commutatorElement

namespace K21bRedProof

theorem isLThreeTwoPower_of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : IsLThreeTwoPower S) : IsLThreeTwoPower S' := by
  rcases h with ⟨d, hd, ⟨f⟩⟩ | ⟨d, Q, hQ, hd, ⟨f⟩⟩
  · exact Or.inl ⟨d, hd, ⟨e.symm.trans f⟩⟩
  · exact Or.inr ⟨d, Q, hQ, hd, ⟨e.symm.trans f⟩⟩

theorem isClassicalTwoOrG2_of_isLThreeTwoPower {S : Type} [Group S] (h : IsLThreeTwoPower S) :
    CFSG.AGLEmbedding.IsClassicalTwoOrG2 S := by
  rcases h with ⟨d, hd, ⟨f⟩⟩ | ⟨d, Q, hQ, hd, ⟨f⟩⟩
  · exact Or.inr (Or.inr ⟨d, Or.inl hd, ⟨f⟩⟩)
  · refine Or.inl ⟨d, ?_, ⟨f⟩⟩
    rw [hd]
    exact hQ

theorem innAut_normal (S : Type) [Group S] : (innAut S).Normal where
  conj_mem := by
    rintro _ ⟨x, rfl⟩ g
    refine ⟨g x, ?_⟩
    ext y
    simp [MulAut.conj_apply]

theorem ker_conj_eq_center (S : Type) [Group S] :
    (MulAut.conj : S →* MulAut S).ker = Subgroup.center S := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro h g
    have h1 := congrArg (fun φ : MulAut S => φ g) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  · intro h
    ext g
    simp only [MulAut.conj_apply, MulAut.one_apply]
    exact mul_inv_eq_iff_eq_mul.mpr (h g).symm

theorem isLThreeTwoPower_innAut (S : Type) [Group S]
    (h : IsLThreeTwoPower (S ⧸ Subgroup.center S)) : IsLThreeTwoPower ↥(innAut S) :=
  isLThreeTwoPower_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq (ker_conj_eq_center S).symm).trans
      (QuotientGroup.quotientKerEquivRange (MulAut.conj : S →* MulAut S))) h

theorem finite_mulAut (S : Type) [Group S] [Finite S] : Finite (MulAut S) :=
  Finite.of_injective (fun e : MulAut S => (e : S → S)) DFunLike.coe_injective

theorem isElemAbelian_subgroupOf {G : Type} [Group G] {N E : Subgroup G} (hEN : E ≤ N)
    (hE : CFSG.Open.IsElemAbelian 3 E) : CFSG.Open.IsElemAbelian 3 (E.subgroupOf N) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    have h := hE.1.is_comm.comm ⟨a.1.1, a.2⟩ ⟨b.1.1, b.2⟩
    exact congrArg (fun z : ↥E => (z : G)) h
  · apply Subtype.ext
    have h := hE.2 x.1 hx
    simpa using h

theorem isSylowOf_subgroupOf_top {G : Type} [Group G] [Finite G] {N U : Subgroup G}
    (h : CFSG.ABGLocalTools.IsSylowOf 2 U N) :
    CFSG.ABGLocalTools.IsSylowOf 2 (U.subgroupOf N) ⊤ := by
  obtain ⟨_, hP, hdvd⟩ := (CFSG.ABGLocalTools.isSylowOf_iff (G := G)).mp h
  refine (CFSG.ABGLocalTools.isSylowOf_iff (G := ↥N)).mpr ⟨le_top, hP.comap_subtype, ?_⟩
  rw [Subgroup.relIndex_top_right]
  exact hdvd

theorem permutable_subgroupOf {G : Type} [Group G] {N E U : Subgroup G} (hEN : E ≤ N)
    (hUN : U ≤ N) (h : Permutable E U) : Permutable (E.subgroupOf N) (U.subgroupOf N) := by
  have h' : (E : Set G) * (U : Set G) = (U : Set G) * (E : Set G) := h
  show ((E.subgroupOf N : Subgroup ↥N) : Set ↥N) * ((U.subgroupOf N : Subgroup ↥N) : Set ↥N) =
    ((U.subgroupOf N : Subgroup ↥N) : Set ↥N) * ((E.subgroupOf N : Subgroup ↥N) : Set ↥N)
  ext x
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    have hab : (a : G) * b ∈ (U : Set G) * (E : Set G) := by
      rw [← h']
      exact ⟨a, ha, b, hb, rfl⟩
    obtain ⟨u, hu, e, he, hue⟩ := hab
    exact ⟨⟨u, hUN hu⟩, hu, ⟨e, hEN he⟩, he, Subtype.ext hue⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    have hab : (a : G) * b ∈ (E : Set G) * (U : Set G) := by
      rw [h']
      exact ⟨a, ha, b, hb, rfl⟩
    obtain ⟨e, he, u, hu, eu⟩ := hab
    exact ⟨⟨e, hEN he⟩, he, ⟨u, hUN hu⟩, hu, Subtype.ext eu⟩

theorem permutable_inf_of_le {G : Type} [Group G] {N E T : Subgroup G} (hEN : E ≤ N)
    (h : Permutable E T) : Permutable E (T ⊓ N) := by
  have h' : (E : Set G) * (T : Set G) = (T : Set G) * (E : Set G) := h
  show (E : Set G) * ((T ⊓ N : Subgroup G) : Set G) = ((T ⊓ N : Subgroup G) : Set G) * (E : Set G)
  ext x
  constructor
  · rintro ⟨e, he, u, hu, rfl⟩
    have hx : e * u ∈ (T : Set G) * (E : Set G) := by
      rw [← h']
      exact ⟨e, he, u, hu.1, rfl⟩
    obtain ⟨t, ht, e', he', hte⟩ := hx
    refine ⟨t, ⟨ht, ?_⟩, e', he', hte⟩
    have h1 : t = e * u * e'⁻¹ := by
      rw [← hte]
      simp
    rw [h1]
    exact N.mul_mem (N.mul_mem (hEN he) hu.2) (N.inv_mem (hEN he'))
  · rintro ⟨u, hu, e, he, rfl⟩
    have hx : u * e ∈ (E : Set G) * (T : Set G) := by
      rw [h']
      exact ⟨u, hu.1, e, he, rfl⟩
    obtain ⟨e', he', t, ht, hte⟩ := hx
    refine ⟨e', he', t, ⟨ht, ?_⟩, hte⟩
    have h1 : t = e'⁻¹ * (u * e) := by
      rw [← hte]
      simp
    rw [h1]
    exact N.mul_mem (N.inv_mem (hEN he')) (N.mul_mem hu.2 (hEN he))

theorem geom_transport (hG : K21bGeom) {G : Type} [Group G] [Finite G] {N E U : Subgroup G}
    (hS : IsLThreeTwoPower ↥N) (hE : CFSG.Open.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (hEN : E ≤ N) (hU : CFSG.ABGLocalTools.IsSylowOf 2 U N) (hperm : Permutable E U) :
    ∀ e ∈ E, ∀ u ∈ U, e * u * e⁻¹ ∈ U := by
  have hUN : U ≤ N := hU.le
  have hE9' : Nat.card (E.subgroupOf N) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv]
    exact hE9
  have hnorm := hG ↥N hS (E.subgroupOf N) (U.subgroupOf N) (isElemAbelian_subgroupOf hEN hE) hE9'
    (isSylowOf_subgroupOf_top hU) (permutable_subgroupOf hEN hUN hperm)
  intro e he u hu
  have h1 : (⟨e, hEN he⟩ : ↥N) ∈ E.subgroupOf N := he
  have h2 := (Subgroup.mem_normalizer_iff.mp (hnorm h1) ⟨u, hUN hu⟩).mp hu
  exact h2

theorem commute_of_inf_eq_bot {G : Type} [Group G] (N E : Subgroup G) [N.Normal] (h : E ⊓ N = ⊥)
    {g : G} (hgN : g ∈ N) (hgE : g ∈ Subgroup.normalizer (E : Set G)) {e : G} (he : e ∈ E) :
    g * e = e * g := by
  have h1 : g * e * g⁻¹ ∈ E := ((Subgroup.mem_normalizer_iff.mp hgE) e).mp he
  have hcE : g * e * g⁻¹ * e⁻¹ ∈ E := E.mul_mem h1 (E.inv_mem he)
  have hcN : g * e * g⁻¹ * e⁻¹ ∈ N := by
    have h2 : e * g⁻¹ * e⁻¹ ∈ N := Subgroup.Normal.conj_mem inferInstance g⁻¹ (N.inv_mem hgN) e
    have h3 := N.mul_mem hgN h2
    simpa [mul_assoc] using h3
  have h4 : g * e * g⁻¹ * e⁻¹ ∈ E ⊓ N := ⟨hcE, hcN⟩
  rw [h] at h4
  exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp (Subgroup.mem_bot.mp h4))

theorem commute_of_le (hG : K21bGeom) {G : Type} [Group G] [Finite G] {N E T : Subgroup G}
    (hS : IsLThreeTwoPower ↥N) (hE : CFSG.Open.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (hEN : E ≤ N) (hT : IsPGroup 2 T) (hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ N) N)
    (hperm : Permutable E T) {g : G} (hgT : g ∈ T) (hgN : g ∈ N)
    (hgE : g ∈ Subgroup.normalizer (E : Set G)) {e : G} (he : e ∈ E) : g * e = e * g := by
  have hnorm := geom_transport hG hS hE hE9 hEN hSyl (permutable_inf_of_le hEN hperm)
  have hg : g ∈ T ⊓ N := ⟨hgT, hgN⟩
  have h1 : g * e * g⁻¹ ∈ E := ((Subgroup.mem_normalizer_iff.mp hgE) e).mp he
  have hcE : g * e * g⁻¹ * e⁻¹ ∈ E := E.mul_mem h1 (E.inv_mem he)
  have hcU : g * e * g⁻¹ * e⁻¹ ∈ T ⊓ N := by
    have h2 := hnorm e he g⁻¹ ((T ⊓ N).inv_mem hg)
    have h3 := (T ⊓ N).mul_mem hg h2
    simpa [mul_assoc] using h3
  have hc3 : (g * e * g⁻¹ * e⁻¹) ^ 3 = 1 := hE.2 _ hcE
  obtain ⟨k, hk⟩ := hT ⟨_, hcU.1⟩
  have hk' : (g * e * g⁻¹ * e⁻¹) ^ (2 ^ k) = 1 := by
    have h2 := congrArg (fun x : ↥T => (x : G)) hk
    simpa using h2
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have hc1 : g * e * g⁻¹ * e⁻¹ = 1 :=
    orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hc3)
        (orderOf_dvd_of_pow_eq_one hk'))
  exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hc1)

theorem normalizerMonoidHom_coe {G : Type} [Group G] (E : Subgroup G)
    (n : ↥(Subgroup.normalizer (E : Set G))) (x : ↥E) :
    ((E.normalizerMonoidHom n x : ↥E) : G) = (n : G) * x * (n : G)⁻¹ :=
  rfl

theorem claimA (hG : K21bGeom) (Jh : Type) [Group Jh] [Finite Jh]
    (hL : IsLThreeTwoPower (Jh ⧸ Subgroup.center Jh)) (E T' : Subgroup (MulAut Jh))
    (hE : CFSG.Open.IsElemAbelian 3 E) (hE9 : Nat.card E = 9) (hT'p : IsPGroup 2 T')
    (hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (T' ⊓ innAut Jh) (innAut Jh))
    (hperm : Permutable E T') (hQ8 : HasQ8 (autInduced T' E)) {g : MulAut Jh} (hgT : g ∈ T')
    (hgN : g ∈ Subgroup.normalizer (E : Set (MulAut Jh))) (hgI : g ∈ innAut Jh) {e : MulAut Jh}
    (he : e ∈ E) : g * e = e * g := by
  haveI := finite_mulAut Jh
  haveI := innAut_normal Jh
  have hdich : (E ⊓ innAut Jh).subgroupOf E = ⊥ ∨ (E ⊓ innAut Jh).subgroupOf E = ⊤ := by
    refine eq_bot_or_eq_top_of_hasQ8 (V := ↥E) (fun x y => hE.1.is_comm.comm x y)
      (fun x => Subtype.ext (by simpa using hE.2 x.1 x.2)) hE9 hQ8 _ ?_
    rintro a ⟨n, hn, rfl⟩ x hx
    show ((E.normalizerMonoidHom n x : ↥E) : MulAut Jh) ∈ E ⊓ innAut Jh
    rw [normalizerMonoidHom_coe]
    exact ⟨((Subgroup.mem_normalizer_iff.mp n.2) x).mp x.2,
      (innAut_normal Jh).conj_mem x hx.2 n⟩
  rcases hdich with h | h
  · apply commute_of_inf_eq_bot (innAut Jh) E _ hgI hgN he
    rw [eq_bot_iff]
    intro x hx
    have h1 : (⟨x, hx.1⟩ : ↥E) ∈ (E ⊓ innAut Jh).subgroupOf E := hx
    rw [h, Subgroup.mem_bot] at h1
    exact (Subgroup.mem_bot.mpr (congrArg Subtype.val h1))
  · have hEI : E ≤ innAut Jh := fun x hx => by
      have h1 : (⟨x, hx⟩ : ↥E) ∈ (E ⊓ innAut Jh).subgroupOf E := by
        rw [h]
        trivial
      exact h1.2
    exact commute_of_le hG (isLThreeTwoPower_innAut Jh hL) hE hE9 hEI hT'p hSyl hperm hgT hgI hgN he

theorem autInduced_comm {G : Type} [Group G] (T E : Subgroup G)
    (hcomm : ∀ s ∈ T, ∀ t ∈ T, s ∈ Subgroup.normalizer (E : Set G) →
      t ∈ Subgroup.normalizer (E : Set G) → ∀ e ∈ E, ⁅s, t⁆ * e = e * ⁅s, t⁆) :
    ∀ a ∈ autInduced T E, ∀ b ∈ autInduced T E, a * b = b * a := by
  rintro a ⟨s, hs, rfl⟩ b ⟨t, ht, rfl⟩
  rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
  ext x
  rw [normalizerMonoidHom_coe]
  have hc := hcomm s hs t ht s.2 t.2 x x.2
  have h1 : (((⁅s, t⁆ : ↥(Subgroup.normalizer (E : Set G))) : G)) = ⁅(s : G), (t : G)⁆ := rfl
  rw [h1, hc, mul_inv_cancel_right]
  simp

end K21bRedProof

theorem K21b_of_K420 (hK420 : K420) (hG : K21bGeom) : K21b := by
  intro Jh _ _ hqs hL E T' hE hE9 hT'p hSyl hperm hQ8
  have hcl : CFSG.AGLEmbedding.IsClassicalTwoOrG2 (Jh ⧸ Subgroup.center Jh) :=
    K21bRedProof.isClassicalTwoOrG2_of_isLThreeTwoPower hL
  obtain ⟨a, ha, b, hb, hab⟩ := hasQ8_exists_noncomm hQ8
  refine hab (K21bRedProof.autInduced_comm T' E ?_ a ha b hb)
  intro s hs t ht hsN htN e he
  have hst : ⁅s, t⁆ ∈ innAut Jh := hK420 Jh hqs hcl T' hT'p s hs t ht
  exact K21bRedProof.claimA hG Jh hL E T' hE hE9 hT'p hSyl hperm hQ8
    (T'.mul_mem (T'.mul_mem (T'.mul_mem hs ht) (T'.inv_mem hs)) (T'.inv_mem ht))
    (((Subgroup.normalizer (E : Set (MulAut Jh))).mul_mem
      ((Subgroup.normalizer (E : Set (MulAut Jh))).mul_mem
        ((Subgroup.normalizer (E : Set (MulAut Jh))).mul_mem hsN htN)
        ((Subgroup.normalizer (E : Set (MulAut Jh))).inv_mem hsN))
      ((Subgroup.normalizer (E : Set (MulAut Jh))).inv_mem htN))) hst he

end CFSG.LocalAnalysis.RankThreeUC.S15
