module

public import CFSG.LocalAnalysis.AGLEmbedding.ConstrainedEscapeAux
public import CFSG.LocalAnalysis.AGLEmbedding.ConstrainedSLAux
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.SectionRank.Ccomm CFSG.Assembly.LowTwoRank Matrix

namespace ReducedNongeneration

variable {p : ℕ} {X : Type*} [Group X] [Finite X] {R : Sylow p X} {X₀ : Subgroup X}

theorem sylow_not_normal (h : ReducedNongeneration p X R X₀) : ¬ (R : Subgroup X).Normal := by
  intro hn
  exact h.not_normalClosure_le ((Subgroup.normalClosure_eq_self (R : Subgroup X)).le.trans
    h.sylow_le)

theorem not_sylow_le_of_normal (h : ReducedNongeneration p X R X₀) {K : Subgroup X} [K.Normal]
    (hK : IsPGroup p K) : ¬ (R : Subgroup X) ≤ K := by
  intro hRK
  apply h.sylow_not_normal
  rw [← R.is_maximal' hK hRK]
  infer_instance

theorem exists_not_comm_of_witness (h : ReducedNongeneration p X R X₀) {Q : Subgroup X}
    [Q.Normal] (hQ : IsPGroup p Q) (hQc : Subgroup.centralizer (Q : Set X) ≤ Q) {z : X}
    (hz : z ∈ Subgroup.centralizer (R : Set X)) (hzp : orderOf z = p) (D : Subgroup Q)
    [D.Characteristic] (hDp : ∀ x ∈ D, x ^ p = 1) (hzD : z ∈ D.map Q.subtype)
    (hker : IsPGroup p (frattiniAction D).ker) : ∃ a b : D, a * b ≠ b * a := by
  have : Fact p.Prime := ⟨h.prime⟩
  by_contra! hcomm
  have hDe : IsElemAbelian p (D.map Q.subtype) := by
    refine ⟨IsMulCommutative.of_comm fun a b => ?_, ?_⟩
    · obtain ⟨a', ha', ha⟩ := Subgroup.mem_map.mp a.2
      obtain ⟨b', hb', hb⟩ := Subgroup.mem_map.mp b.2
      apply Subtype.ext
      change (a : X) * b = b * a
      rw [← ha, ← hb]
      exact congrArg (fun w : D => ((w : Q) : X)) (hcomm ⟨a', ha'⟩ ⟨b', hb'⟩)
    · rintro _ ⟨d, hd, rfl⟩
      rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, hDp d hd, Subgroup.coe_one]
  have heq : Subgroup.zpowers z = D.map Q.subtype :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzD)
      (by rw [Nat.card_zpowers, hzp]; exact h.card_le_of_normal_isElemAbelian hDe)
  have hK : IsPGroup p ((frattiniAction D).ker.comap (MulAut.conjNormal (H := Q))) :=
    hker.comap_of_ker_isPGroup _ (isPGroup_ker_conjNormal hQ hQc)
  have : ((frattiniAction D).ker.comap (MulAut.conjNormal (H := Q))).Normal :=
    (MonoidHom.normal_ker _).comap _
  refine h.not_sylow_le_of_normal hK fun r hr => ?_
  rw [Subgroup.mem_comap, mem_ker_frattiniAction]
  intro d
  have hdz : ((d : Q) : X) ∈ Subgroup.zpowers z := heq ▸ ⟨(d : Q), d.2, rfl⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hdz
  have hrd : (MulAut.characteristic D) (MulAut.conjNormal r) d = d := by
    apply Subtype.ext
    apply Subtype.ext
    change r * ((d : Q) : X) * r⁻¹ = ((d : Q) : X)
    have hrz : Commute r z := Subgroup.mem_centralizer_iff.mp hz r hr
    rw [← hk, (hrz.zpow_right k).eq, mul_inv_cancel_right]
  rw [hrd, inv_mul_cancel]
  exact Subgroup.one_mem _

theorem exists_nonabelian_witness (h : ReducedNongeneration p X R X₀) {Q : Subgroup X} [Q.Normal]
    (hQ : IsPGroup p Q) (hQc : Subgroup.centralizer (Q : Set X) ≤ Q) {z : X}
    (hz : z ∈ Subgroup.centralizer (R : Set X)) (hzp : orderOf z = p) :
    ∃ D : Subgroup Q, ∃ _ : D.Characteristic, (∀ x ∈ D, x ^ p = 1) ∧ z ∈ D.map Q.subtype ∧
      Nat.card D = p ^ 3 ∧ (∃ a b : D, a * b ≠ b * a) ∧ IsPGroup p (frattiniAction D).ker := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hzQc : z ∈ Subgroup.centralizer (Q : Set X) :=
    Subgroup.centralizer_le (hQ.le_sylow_of_normal R) hz
  let zQ : Q := ⟨z, hQc hzQc⟩
  have hzQp : orderOf zQ = p := (Subgroup.orderOf_mk z _).trans hzp
  have : Nontrivial Q := ⟨⟨zQ, 1, fun h1 => by
    rw [h1, orderOf_one] at hzQp
    exact hp.one_lt.ne hzQp⟩⟩
  obtain ⟨D, hDc, -, hDp, -, htors, hker⟩ := supercritical_witness h.ne_two hQ
  have hzD : zQ ∈ D := htors zQ (Subgroup.mem_centralizer_iff.mpr fun d _ =>
    Subtype.ext (Subgroup.mem_centralizer_iff.mp hzQc d d.2)) hzQp
  have hzmem : z ∈ D.map Q.subtype := ⟨zQ, hzD, rfl⟩
  have hnc := h.exists_not_comm_of_witness hQ hQc hz hzp D hDp hzmem hker
  have hrank : Open.pRank p (⊤ : Subgroup D) ≤ 2 := by
    rw [← pRank_map_of_injective p hp (Q.subtype.comp D.subtype)
      (Q.subtype_injective.comp D.subtype_injective), ← Subgroup.map_map,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact h.pRank_le_two_of_normal_isPGroup (hQ.to_le (Subgroup.map_subtype_le D))
  refine ⟨D, hDc, hDp, hzmem, card_eq_pow_three_of_not_comm (hQ.to_subgroup D)
    (fun x => Subtype.ext (by rw [Subgroup.coe_pow, hDp x x.2, Subgroup.coe_one])) hrank hnc,
    hnc, hker⟩

theorem exists_sl_two_of_witness [Fact p.Prime] (h : ReducedNongeneration p X R X₀)
    {Q : Subgroup X} [Q.Normal] (hQ : IsPGroup p Q) (hQc : Subgroup.centralizer (Q : Set X) ≤ Q)
    {z : X} (hz : z ∈ Subgroup.centralizer (R : Set X)) (hzp : orderOf z = p) (D : Subgroup Q)
    [D.Characteristic] (hZ : Subgroup.center D ≤ frattini D)
    (hker : IsPGroup p (frattiniAction D).ker)
    (e : D ⧸ Subgroup.center D ≃* Multiplicative (Fin 2 → ZMod p)) :
    ∀ a ∈ StatedSL 2 (ZMod p), ∃ x ∈ Subgroup.centralizer (Subgroup.zpowers z : Set X),
      ∀ d : D, Multiplicative.toAdd (e ((MulAut.characteristic D (MulAut.conjNormal x) d : D) :
        D ⧸ Subgroup.center D)) = (a : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ
          Multiplicative.toAdd (e (d : D ⧸ Subgroup.center D)) := by
  set ρD := (autQuotient (Subgroup.center D)).comp
    ((MulAut.characteristic D).comp (MulAut.conjNormal (H := Q))) with hρD
  set ρ : X →* GL (Fin 2) (ZMod p) := (elemAutEquivGL e).toMonoidHom.comp ρD with hρ
  have hkerρ : IsPGroup p ρ.ker := by
    refine (isPGroup_ker_centerQuotient_action hQ hQc D hZ hker).to_le fun x hx => ?_
    rw [MonoidHom.mem_ker] at hx ⊢
    exact (elemAutEquivGL e).injective (by rw [map_one]; exact hx)
  have hzQc : z ∈ Subgroup.centralizer (Q : Set X) :=
    Subgroup.centralizer_le (hQ.le_sylow_of_normal R) hz
  have : (Subgroup.zpowers z).Normal := zpowers_normal_of_mem_centralizer hQc
    (fun A hA hAe => by have := hA; exact h.card_le_of_normal_isElemAbelian hAe) hzQc hzp
  set X₁ := Subgroup.centralizer (Subgroup.zpowers z : Set X) with hX₁
  have hRX₁ : (R : Subgroup X) ≤ X₁ := by
    rw [hX₁, Subgroup.le_centralizer_iff]
    exact Subgroup.zpowers_le.mpr hz
  have hφker : IsPGroup p (ρ.comp X₁.subtype).ker := by
    rw [← MonoidHom.comap_ker]
    exact hkerρ.comap_of_injective _ X₁.subtype_injective
  have hT : ¬ ((R.subtype hRX₁ : Sylow p X₁) : Subgroup X₁).Normal := by
    intro hn
    have := Sylow.characteristic_of_normal _ hn
    apply h.sylow_not_normal
    have hmap : ((R.subtype hRX₁ : Sylow p X₁) : Subgroup X₁).map X₁.subtype = R := by
      rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hRX₁]
    rw [← hmap]
    infer_instance
  have hSL := statedSL_le_range_of_not_normal (ρ.comp X₁.subtype) hφker _ hT
  intro a ha
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp (hSL ha)
  refine ⟨x, x.2, fun d => ?_⟩
  rw [← hx]
  change _ = ((elemAutEquivGL e (ρD x) : GL (Fin 2) (ZMod p)) :
    Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ _
  rw [elemAutEquivGL_mulVec]
  rfl

theorem exists_extraspecial_sl_two [Fact p.Prime] (h : ReducedNongeneration p X R X₀)
    {Q : Subgroup X} [Q.Normal] (hQ : IsPGroup p Q) (hQc : Subgroup.centralizer (Q : Set X) ≤ Q)
    {z : X} (hz : z ∈ Subgroup.centralizer (R : Set X)) (hzp : orderOf z = p) :
    ∃ E : Subgroup X, E.Normal ∧ E ≤ Q ∧ Nat.card E = p ^ 3 ∧ (∀ x ∈ E, x ^ p = 1) ∧
      (Subgroup.center E).map E.subtype = Subgroup.zpowers z ∧
      ∃ e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p),
        ∀ a ∈ StatedSL 2 (ZMod p), ∃ x ∈ Subgroup.centralizer ({z} : Set X),
          ∀ u v : E, (v : X) = x * u * x⁻¹ →
            Multiplicative.toAdd (e (v : E ⧸ Subgroup.center E)) =
              (a : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ
                Multiplicative.toAdd (e (u : E ⧸ Subgroup.center E)) := by
  obtain ⟨D, hDc, hDp, hzD, hcard, hnc, hker⟩ := h.exists_nonabelian_witness hQ hQc hz hzp
  obtain ⟨hZcard, hZ, ⟨e₀⟩⟩ := center_structure_of_card_eq_pow_three hcard hnc
  have hSL := h.exists_sl_two_of_witness hQ hQc hz hzp D hZ hker e₀
  set E := D.map Q.subtype with hE
  set ψ := D.equivMapOfInjective Q.subtype Q.subtype_injective with hψ
  have hψs : ∀ v : E, (((ψ.symm v : D) : Q) : X) = (v : X) := fun v => by
    conv_rhs => rw [← ψ.apply_symm_apply v]
    rfl
  let e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p) :=
    (QuotientGroup.congr (Subgroup.center E) (Subgroup.center D) ψ.symm
      (Subgroup.map_center_eq ψ.symm)).trans e₀
  have he : ∀ v : E, e (v : E ⧸ Subgroup.center E) =
      e₀ ((ψ.symm v : D) : D ⧸ Subgroup.center D) := fun v => rfl
  have hzQc : z ∈ Subgroup.centralizer (Q : Set X) :=
    Subgroup.centralizer_le (hQ.le_sylow_of_normal R) hz
  refine ⟨E, inferInstance, Subgroup.map_subtype_le D, ?_, ?_, ?_, e, fun a ha => ?_⟩
  · rw [Subgroup.card_map_of_injective Q.subtype_injective, hcard]
  · rintro _ ⟨d, hd, rfl⟩
    rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, hDp d hd, Subgroup.coe_one]
  · refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
    · rw [Subgroup.zpowers_le]
      refine ⟨⟨z, hzD⟩, Subgroup.mem_center_iff.mpr fun v => Subtype.ext ?_, rfl⟩
      exact Subgroup.mem_centralizer_iff.mp hzQc v (Subgroup.map_subtype_le D v.2)
    · rw [Subgroup.card_map_of_injective E.subtype_injective, Nat.card_zpowers, hzp,
        ← hZcard]
      exact (Nat.card_congr (Subgroup.centerCongr ψ).toEquiv).ge
  · obtain ⟨x, hx, hxd⟩ := hSL a ha
    refine ⟨x, ?_, fun u v huv => ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hx z (Subgroup.mem_zpowers z)).symm
    · have hv : ψ.symm v = (MulAut.characteristic D (MulAut.conjNormal x)) (ψ.symm u) := by
        apply Subtype.ext
        apply Subtype.ext
        rw [hψs]
        change (v : X) = x * (((ψ.symm u : D) : Q) : X) * x⁻¹
        rw [hψs, huv]
      rw [he, he, hv]
      exact hxd _

end ReducedNongeneration

end CFSG.AGLEmbedding
