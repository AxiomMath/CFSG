module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Hyp
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingData
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.ComponentClassification.Components

public noncomputable section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace SectionSix

namespace Conj

variable {G G' : Type*} [Group G] [Group G']

theorem mem_map_apply_iff (e : G ≃* G') (A : Subgroup G) (x : G) :
    e x ∈ A.map e.toMonoidHom ↔ x ∈ A := by
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

theorem map_symm_map (e : G ≃* G') (A : Subgroup G) :
    (A.map e.toMonoidHom).map e.symm.toMonoidHom = A := by
  ext x
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, mem_map_apply_iff]

theorem apply_mem_center_iff (e : G ≃* G') (x : G) :
    e x ∈ Subgroup.center G' ↔ x ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro hcentral g
    apply e.injective
    rw [map_mul, map_mul]
    exact hcentral (e g)
  · intro hcentral g
    rw [← e.apply_symm_apply g, ← map_mul, ← map_mul, hcentral]

theorem normalizer_map (e : G ≃* G') (D : Subgroup G) :
    Subgroup.normalizer ((D.map e.toMonoidHom : Subgroup G') : Set G') =
      (Subgroup.normalizer (D : Set G)).map e.toMonoidHom :=
  (Subgroup.map_equiv_normalizer_eq D e).symm

theorem map_conj_map (e : G ≃* G') (h : G) (A : Subgroup G) :
    (A.map e.toMonoidHom).map (MulAut.conj (e h)).toMonoidHom =
      (A.map (MulAut.conj h).toMonoidHom).map e.toMonoidHom := by
  ext x
  simp only [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, map_mul, map_inv,
    MulEquiv.symm_apply_apply]

theorem centralizes_map_iff (e : G ≃* G') (O A : Subgroup G) (y : G') :
    aschbacherThm5Centralizes (O.map e.toMonoidHom) (A.map e.toMonoidHom) y ↔
      aschbacherThm5Centralizes O A (e.symm y) := by
  constructor
  · intro hcentral a ha
    have hmem := hcentral (e a) ((mem_map_apply_iff e A a).mpr ha)
    rw [Subgroup.mem_map_equiv] at hmem
    simpa only [map_mul, map_inv, MulEquiv.symm_apply_apply] using hmem
  · intro hcentral a ha
    rw [Subgroup.mem_map_equiv] at ha ⊢
    simpa only [map_mul, map_inv] using hcentral (e.symm a) ha

theorem pRank_map [Finite G] [Finite G'] (e : G ≃* G') {p : ℕ} (hp : 1 < p) (A : Subgroup G) :
    pRank p (A.map e.toMonoidHom) = pRank p A := by
  refine le_antisymm ?_ (SectionRank.pRank_le_map hp e.toMonoidHom e.injective A)
  have hle := SectionRank.pRank_le_map hp e.symm.toMonoidHom e.symm.injective
    (A.map e.toMonoidHom)
  rwa [map_symm_map] at hle

theorem product_map_iff (e : G ≃* G') (D A B : Subgroup G) :
    (∀ d ∈ D.map e.toMonoidHom, ∃ a ∈ A.map e.toMonoidHom, ∃ b ∈ B.map e.toMonoidHom,
      d = a * b) ↔ ∀ d ∈ D, ∃ a ∈ A, ∃ b ∈ B, d = a * b := by
  constructor
  · intro hproduct d hd
    obtain ⟨a, ha, b, hb, hab⟩ := hproduct (e d) ((mem_map_apply_iff e D d).mpr hd)
    rw [Subgroup.mem_map_equiv] at ha hb
    refine ⟨e.symm a, ha, e.symm b, hb, ?_⟩
    rw [← map_mul, ← hab, e.symm_apply_apply]
  · intro hproduct d hd
    rw [Subgroup.mem_map_equiv] at hd
    obtain ⟨a, ha, b, hb, hab⟩ := hproduct (e.symm d) hd
    refine ⟨e a, (mem_map_apply_iff e A a).mpr ha, e b, (mem_map_apply_iff e B b).mpr hb, ?_⟩
    rw [← map_mul, ← hab, e.apply_symm_apply]

theorem involution_map_iff (e : G ≃* G') (O A B : Subgroup G) :
    (∀ a₁ ∈ A.map e.toMonoidHom, ∀ a₂ ∈ B.map e.toMonoidHom,
      orderOf a₁ = 2 → orderOf a₂ = 2 → a₁ * a₂ = a₂ * a₁ →
      aschbacherThm5Centralizes (O.map e.toMonoidHom) (A.map e.toMonoidHom) a₁ →
      aschbacherThm5Centralizes (O.map e.toMonoidHom) (B.map e.toMonoidHom) a₂ →
      a₁ = a₂ ∨ a₁ * a₂ ∈ Subgroup.center G') ↔
    ∀ a₁ ∈ A, ∀ a₂ ∈ B, orderOf a₁ = 2 → orderOf a₂ = 2 → a₁ * a₂ = a₂ * a₁ →
      aschbacherThm5Centralizes O A a₁ → aschbacherThm5Centralizes O B a₂ →
      a₁ = a₂ ∨ a₁ * a₂ ∈ Subgroup.center G := by
  constructor
  · intro hinvolution a₁ ha₁ a₂ ha₂ horder₁ horder₂ hcomm hcentral₁ hcentral₂
    have hcentral₁' := (centralizes_map_iff e O A (e a₁)).mpr
      (by rwa [e.symm_apply_apply])
    have hcentral₂' := (centralizes_map_iff e O B (e a₂)).mpr
      (by rwa [e.symm_apply_apply])
    rcases hinvolution (e a₁) ((mem_map_apply_iff e A a₁).mpr ha₁) (e a₂)
        ((mem_map_apply_iff e B a₂).mpr ha₂) ((e.orderOf_eq a₁).trans horder₁)
        ((e.orderOf_eq a₂).trans horder₂) (by rw [← map_mul, hcomm, map_mul])
        hcentral₁' hcentral₂' with heq | hcenter
    · exact Or.inl (e.injective heq)
    · exact Or.inr ((apply_mem_center_iff e _).mp (by rwa [map_mul]))
  · intro hinvolution a₁ ha₁ a₂ ha₂ horder₁ horder₂ hcomm hcentral₁ hcentral₂
    rw [Subgroup.mem_map_equiv] at ha₁ ha₂
    rw [centralizes_map_iff] at hcentral₁ hcentral₂
    rcases hinvolution (e.symm a₁) ha₁ (e.symm a₂) ha₂ ((e.symm.orderOf_eq a₁).trans horder₁)
        ((e.symm.orderOf_eq a₂).trans horder₂) (by rw [← map_mul, hcomm, map_mul])
        hcentral₁ hcentral₂ with heq | hcenter
    · exact Or.inl (e.symm.injective heq)
    · exact Or.inr ((apply_mem_center_iff e.symm _).mp (by rwa [map_mul]))

theorem isSemisimple_map {Q Q' : Type*} [Group Q] [Group Q'] (f : Q ≃* Q') (X : Subgroup Q)
    (hX : aschbacherThm5IsSemisimple X) : aschbacherThm5IsSemisimple (X.map f.toMonoidHom) := by
  obtain ⟨k, K, hk, hK, hcomm, hgen⟩ := hX
  refine ⟨k, fun l => (K l).map f.toMonoidHom, hk, fun l => ⟨Subgroup.map_mono (hK l).1,
    Components.quasisimple_of_equiv ((K l).equivMapOfInjective f.toMonoidHom f.injective).symm
      (hK l).2⟩, ?_, ?_⟩
  · rintro l m hlm _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, hcomm l m hlm x hx y hy, map_mul]
  · rw [← hgen, Subgroup.map_iSup]

theorem iSup_map_eq_top {Q Q' : Type*} [Group Q] [Group Q'] (f : Q ≃* Q') {ι : Type*}
    (A : ι → Subgroup Q) (hgen : ⨆ i, A i = ⊤) : ⨆ i, (A i).map f.toMonoidHom = ⊤ := by
  rw [← Subgroup.map_iSup, hgen, Subgroup.map_top_of_surjective f.toMonoidHom f.surjective]

@[expose] def subgroupEquiv (e : G ≃* G') (D : Subgroup G) : D ≃* D.map e.toMonoidHom :=
  D.equivMapOfInjective e.toMonoidHom e.injective

theorem subgroupEquiv_apply (e : G ≃* G') (D : Subgroup G) (d : D) :
    (subgroupEquiv e D d : G') = e d :=
  rfl

theorem subtype_comp_subgroupEquiv (e : G ≃* G') (D : Subgroup G) :
    (D.map e.toMonoidHom).subtype.comp (subgroupEquiv e D).toMonoidHom =
      e.toMonoidHom.comp D.subtype := by
  ext d
  rfl

theorem oddCore_map_subgroupEquiv (e : G ≃* G') (D : Subgroup G) :
    (aschbacherThm5OddCore D).map (subgroupEquiv e D).toMonoidHom =
      aschbacherThm5OddCore (D.map e.toMonoidHom) :=
  OddCore.equiv_invariant (subgroupEquiv e D)

@[expose] def quotientEquiv (e : G ≃* G') (D : Subgroup G) :
    D ⧸ aschbacherThm5OddCore D ≃*
      D.map e.toMonoidHom ⧸ aschbacherThm5OddCore (D.map e.toMonoidHom) :=
  QuotientGroup.congr _ _ (subgroupEquiv e D) (oddCore_map_subgroupEquiv e D)

theorem quotientEquiv_mk (e : G ≃* G') (D : Subgroup G) (d : D) :
    quotientEquiv e D (QuotientGroup.mk' (aschbacherThm5OddCore D) d) =
      QuotientGroup.mk' (aschbacherThm5OddCore (D.map e.toMonoidHom)) (subgroupEquiv e D d) :=
  QuotientGroup.congr_mk' _ _ _ _ d

theorem quotientEquiv_symm_mk (e : G ≃* G') (D : Subgroup G) (d : D.map e.toMonoidHom) :
    (quotientEquiv e D).symm
        (QuotientGroup.mk' (aschbacherThm5OddCore (D.map e.toMonoidHom)) d) =
      QuotientGroup.mk' (aschbacherThm5OddCore D) ((subgroupEquiv e D).symm d) := by
  rw [MulEquiv.symm_apply_eq, quotientEquiv_mk, MulEquiv.apply_symm_apply]

theorem preimage_map_quotientEquiv (e : G ≃* G') (D : Subgroup G)
    (Abar : Subgroup (D ⧸ aschbacherThm5OddCore D)) :
    aschbacherThm5Preimage (D.map e.toMonoidHom) (Abar.map (quotientEquiv e D).toMonoidHom) =
      (aschbacherThm5Preimage D Abar).map e.toMonoidHom := by
  have hpreimage : (Abar.comap (QuotientGroup.mk' (aschbacherThm5OddCore D))).map
      (subgroupEquiv e D).toMonoidHom = (Abar.map (quotientEquiv e D).toMonoidHom).comap
        (QuotientGroup.mk' (aschbacherThm5OddCore (D.map e.toMonoidHom))) := by
    ext d
    rw [Subgroup.mem_map_equiv, Subgroup.mem_comap, Subgroup.mem_comap, Subgroup.mem_map_equiv,
      quotientEquiv_symm_mk]
  change ((Abar.map _).comap _).map _ = ((Abar.comap _).map D.subtype).map _
  rw [← hpreimage, Subgroup.map_map, Subgroup.map_map, subtype_comp_subgroupEquiv]

end Conj

@[expose] def transportFactors {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (D : Subgroup G) {ι : Type*} (Abar : ι → Subgroup (D ⧸ aschbacherThm5OddCore D)) (i : ι) :
    Subgroup (D.map e.toMonoidHom ⧸ aschbacherThm5OddCore (D.map e.toMonoidHom)) :=
  (Abar i).map (Conj.quotientEquiv e D).toMonoidHom

theorem preimage_transportFactors {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (D : Subgroup G) {ι : Type*} (Abar : ι → Subgroup (D ⧸ aschbacherThm5OddCore D)) (i : ι) :
    aschbacherThm5Preimage (D.map e.toMonoidHom) (transportFactors e D Abar i) =
      (aschbacherThm5Preimage D (Abar i)).map e.toMonoidHom :=
  Conj.preimage_map_quotientEquiv e D (Abar i)

theorem core_transport {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') (D : Subgroup G) :
    aschbacherThm5Core (D.map e.toMonoidHom) = (aschbacherThm5Core D).map e.toMonoidHom := by
  change (aschbacherThm5OddCore (D.map e.toMonoidHom)).map (D.map e.toMonoidHom).subtype =
    ((aschbacherThm5OddCore D).map D.subtype).map e.toMonoidHom
  rw [← Conj.oddCore_map_subgroupEquiv, Subgroup.map_map, Subgroup.map_map,
    Conj.subtype_comp_subgroupEquiv]

theorem hyp61_transport {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G']
    (e : G ≃* G') {D : Subgroup G} {r : ℕ}
    {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)} (hyp : Hyp61 G D r Abar) :
    Hyp61 G' (D.map e.toMonoidHom) r (transportFactors e D Abar) where
  hr := hyp.hr
  hdistinct := fun i j hij => hyp.hdistinct (Subgroup.map_injective
    (f := (Conj.quotientEquiv e D).toMonoidHom) (Conj.quotientEquiv e D).injective hij)
  hsemisimple := fun i => Conj.isSemisimple_map (Conj.quotientEquiv e D) (Abar i)
    (hyp.hsemisimple i)
  hcomm := by
    rintro i j hij _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, hyp.hcomm i j hij x hx y hy, map_mul]
  hgen := Conj.iSup_map_eq_top (Conj.quotientEquiv e D) Abar hyp.hgen
  hperm := by
    intro h hh i
    rw [Conj.normalizer_map] at hh
    obtain ⟨h₀, hh₀, rfl⟩ := Subgroup.mem_map.mp hh
    obtain ⟨j, hj⟩ := hyp.hperm h₀ hh₀ i
    refine ⟨j, ?_⟩
    rw [preimage_transportFactors, preimage_transportFactors, ← hj]
    exact Conj.map_conj_map e h₀ _
  hi := by
    intro i j t g htwo hcenter hti htj
    rw [core_transport, preimage_transportFactors, Conj.centralizes_map_iff] at hti htj
    rw [Conj.normalizer_map, Subgroup.mem_map_equiv]
    refine hyp.hi i j (e.symm t) (e.symm g) ?_ ?_ hti ?_
    · obtain ⟨k, hk⟩ := htwo
      exact ⟨k, by rw [← map_pow, hk, map_one]⟩
    · intro hmem
      apply hcenter
      rw [← e.apply_symm_apply t]
      exact (Conj.apply_mem_center_iff e _).mpr hmem
    · simpa only [map_mul, map_inv] using htj
  hii := by
    intro i g X hX hprod
    rw [preimage_transportFactors, core_transport] at hprod
    rw [Conj.normalizer_map, Subgroup.mem_map_equiv]
    refine hyp.hii i (e.symm g) (X.comap e.toMonoidHom) ?_ ?_
    · intro x hx
      have hmem := hX (Subgroup.mem_comap.mp hx)
      rw [Conj.normalizer_map, Subgroup.mem_map_equiv, Subgroup.mem_map_equiv,
        MulAut.conj_symm_apply] at hmem
      rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
      simpa only [inv_inv, map_mul, map_inv, MulEquiv.coe_toMonoidHom,
        MulEquiv.symm_apply_apply] using hmem
    · intro a ha
      obtain ⟨x, hx, o, ho, hxo⟩ := hprod (e a) ((Conj.mem_map_apply_iff e _ a).mpr ha)
      rw [Subgroup.mem_map_equiv] at ho
      refine ⟨e.symm x, ?_, e.symm o, ho, ?_⟩
      · show e (e.symm x) ∈ X
        rw [e.apply_symm_apply]
        exact hx
      · rw [← map_mul, ← hxo, e.symm_apply_apply]

theorem conclusion_transport_iff {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G']
    (e : G ≃* G') (D : Subgroup G) {r : ℕ}
    (Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)) :
    Conclusion G' (D.map e.toMonoidHom) r (transportFactors e D Abar) ↔
      Conclusion G D r Abar := by
  unfold Conclusion
  refine or_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun i => forall_congr' fun j =>
    imp_congr_right fun _ => ?_))
  rw [preimage_transportFactors, preimage_transportFactors, core_transport,
    Conj.pRank_map e one_lt_two]
  exact and_congr (Conj.product_map_iff e D _ _)
    (and_congr Iff.rfl (Conj.involution_map_iff e _ _ _))

theorem map_conj_inv_eq_rightConjugate {G : Type*} [Group G] (D : Subgroup G) (g : G) :
    D.map (MulAut.conj g⁻¹).toMonoidHom = rightConjugate D g :=
  rfl

@[expose] def conjFactors {G : Type*} [Group G] (D : Subgroup G) {ι : Type*}
    (Abar : ι → Subgroup (D ⧸ aschbacherThm5OddCore D)) (g : G) :
    ι → Subgroup (rightConjugate D g ⧸ aschbacherThm5OddCore (rightConjugate D g)) :=
  transportFactors (MulAut.conj g⁻¹) D Abar

theorem preimage_conjFactors {G : Type*} [Group G] (D : Subgroup G) {ι : Type*}
    (Abar : ι → Subgroup (D ⧸ aschbacherThm5OddCore D)) (g : G) (i : ι) :
    aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g i) =
      rightConjugate (aschbacherThm5Preimage D (Abar i)) g :=
  preimage_transportFactors (MulAut.conj g⁻¹) D Abar i

theorem core_conj {G : Type*} [Group G] (D : Subgroup G) (g : G) :
    aschbacherThm5Core (rightConjugate D g) = rightConjugate (aschbacherThm5Core D) g :=
  core_transport (MulAut.conj g⁻¹) D

theorem normalizer_rightConjugate {G : Type*} [Group G] (D : Subgroup G) (g : G) :
    Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G) =
      rightConjugate (Subgroup.normalizer (D : Set G)) g :=
  Conj.normalizer_map (MulAut.conj g⁻¹) D

theorem centralizes_conj_iff {G : Type*} [Group G] (D : Subgroup G) {ι : Type*}
    (Abar : ι → Subgroup (D ⧸ aschbacherThm5OddCore D)) (g : G) (i : ι) (t : G) :
    aschbacherThm5Centralizes (aschbacherThm5Core (rightConjugate D g))
        (aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g i)) t ↔
      aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar i))
        (g * t * g⁻¹) := by
  rw [core_conj, preimage_conjFactors]
  exact (Conj.centralizes_map_iff (MulAut.conj g⁻¹) (aschbacherThm5Core D)
    (aschbacherThm5Preimage D (Abar i)) t).trans (by rw [MulAut.conj_symm_apply, inv_inv])

theorem hyp61_conj {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
    {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)} (hyp : Hyp61 G D r Abar) (g : G) :
    Hyp61 G (rightConjugate D g) r (conjFactors D Abar g) :=
  hyp61_transport (MulAut.conj g⁻¹) hyp

theorem conclusion_conj_iff {G : Type} [Group G] [Finite G] (D : Subgroup G) {r : ℕ}
    (Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)) (g : G) :
    Conclusion G (rightConjugate D g) r (conjFactors D Abar g) ↔ Conclusion G D r Abar :=
  conclusion_transport_iff (MulAut.conj g⁻¹) D Abar

end SectionSix

namespace Counterexample

open SectionSix

theorem transport {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G'] {D : Subgroup G}
    {r : ℕ} {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}
    (hC : Counterexample G D r Abar) (e : G ≃* G') :
    Counterexample G' (D.map e.toMonoidHom) r (transportFactors e D Abar) where
  hyp := hyp61_transport e hC.hyp
  proper := by
    rw [Conj.normalizer_map]
    intro htop
    apply hC.proper
    apply eq_top_iff.mpr
    intro x _
    have hx : e x ∈ (Subgroup.normalizer (D : Set G)).map e.toMonoidHom := by
      rw [htop]
      exact Subgroup.mem_top _
    exact (Conj.mem_map_apply_iff e _ x).mp hx
  center := by
    apply eq_bot_iff.mpr
    intro z hz
    have hsymm : e.symm z ∈ Subgroup.center G := by
      rw [← Conj.apply_mem_center_iff e, e.apply_symm_apply]
      exact hz
    rw [hC.center, Subgroup.mem_bot] at hsymm
    rw [Subgroup.mem_bot, ← e.apply_symm_apply z, hsymm, map_one]
  fails := fun hconclusion => hC.fails ((conclusion_transport_iff e D Abar).mp hconclusion)

theorem conj {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
    {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)} (hC : Counterexample G D r Abar)
    (g : G) : Counterexample G (rightConjugate D g) r (conjFactors D Abar g) :=
  hC.transport (G' := G) (MulAut.conj g⁻¹)

end Counterexample

end CFSG.ComponentClassification.AschbacherTheorem5
