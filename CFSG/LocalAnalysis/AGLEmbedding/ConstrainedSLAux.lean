module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.NonabelianCube
public import CFSG.LocalAnalysis.SectionRank.Ccomm.RankTwo
public import CFSG.RankThree.SubgroupLists.DicksonGL2

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.SectionRank.Ccomm CFSG.Assembly.LowTwoRank Matrix

section Sylow

variable {Y W : Type*} [Group Y] [Group W] [Finite W] {p : ℕ} [Fact p.Prime]

theorem sylow_normal_of_isPGroup_ker (φ : Y →* W) (hker : IsPGroup p φ.ker)
    (S : Sylow p φ.range) (hS : (S : Subgroup φ.range).Normal) (T : Sylow p Y) :
    (T : Subgroup Y).Normal := by
  have hN : ((S : Subgroup φ.range).comap φ.rangeRestrict).Normal := hS.comap _
  have hNp : IsPGroup p ((S : Subgroup φ.range).comap φ.rangeRestrict) :=
    S.isPGroup'.comap_of_ker_isPGroup _ (by rwa [MonoidHom.ker_rangeRestrict])
  have hTN : (T : Subgroup Y) ≤ (S : Subgroup φ.range).comap φ.rangeRestrict := by
    obtain ⟨S', hS'⟩ := (T.isPGroup'.map φ.rangeRestrict).exists_le_sylow
    have := Sylow.unique_of_normal S hS
    rw [Subsingleton.elim S' S] at hS'
    exact Subgroup.map_le_iff_le_comap.mp hS'
  rw [le_antisymm hTN (hNp.le_sylow_of_normal T)]
  exact hN

theorem statedSL_le_range_of_not_normal (φ : Y →* GL (Fin 2) (ZMod p)) (hker : IsPGroup p φ.ker)
    (T : Sylow p Y) (hT : ¬ (T : Subgroup Y).Normal) : StatedSL 2 (ZMod p) ≤ φ.range := by
  by_cases hdvd : p ∣ Nat.card φ.range
  · rcases RankThree.SubgroupLists.dickson_gl_two φ.range hdvd with ⟨S, hS, -⟩ | hSL
    · exact absurd (sylow_normal_of_isPGroup_ker φ hker S hS T) hT
    · exact hSL
  · exfalso
    obtain ⟨S⟩ : Nonempty (Sylow p φ.range) := inferInstance
    have hS1 : (S : Subgroup φ.range) = ⊥ := by
      rw [← Subgroup.card_eq_one, S.card_eq_multiplicity,
        Nat.factorization_eq_zero_of_not_dvd hdvd, pow_zero]
    exact hT (sylow_normal_of_isPGroup_ker φ hker S (by rw [hS1]; infer_instance) T)

end Sylow

section Order

variable {S : Type*} [Group S] [Finite S] {p : ℕ} [Fact p.Prime]

theorem card_eq_pow_three_of_not_comm (hS : IsPGroup p S) (hexp : ∀ x : S, x ^ p = 1)
    (hrank : Open.pRank p (⊤ : Subgroup S) ≤ 2) (hnc : ∃ a b : S, a * b ≠ b * a) :
    Nat.card S = p ^ 3 := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨hle, -⟩ := rank_two_exponent_prime_order_bound hS hexp hrank
  obtain ⟨k, hk⟩ := hS.exists_card_eq
  rw [hk] at hle ⊢
  have hk3 : k ≤ 3 := (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
  obtain ⟨a, b, hab⟩ := hnc
  by_contra hne
  have hk2 : k ≤ 2 := by
    rcases Nat.lt_or_ge k 3 with h | h
    · omega
    · exact absurd (by rw [show k = 3 by omega]) hne
  apply hab
  interval_cases k
  · have : Subsingleton S := (Nat.card_eq_one_iff_unique.mp (by rw [hk, pow_zero])).1
    exact Subsingleton.elim _ _
  · have := isCyclic_of_prime_card (hk.trans (pow_one p))
    exact mul_comm' a b
  · have := IsPGroup.isMulCommutative_of_card_eq_prime_sq hk
    exact mul_comm' a b

theorem center_structure_of_card_eq_pow_three (hcard : Nat.card S = p ^ 3)
    (hnc : ∃ a b : S, a * b ≠ b * a) :
    Nat.card (Subgroup.center S) = p ∧ Subgroup.center S ≤ frattini S ∧
      Nonempty (S ⧸ Subgroup.center S ≃* Multiplicative (Fin 2 → ZMod p)) := by
  obtain ⟨hcomm, hZ, hQcomm, hQpow, hQcard, -, -⟩ :=
    nonabelian_prime_cube_central_structure hcard hnc
  have : Fact (IsPGroup p S) := ⟨IsPGroup.of_card hcard⟩
  refine ⟨hZ, ?_, nonempty_mulEquiv_of_elementary hQcomm hQpow hQcard⟩
  rw [← hcomm]
  exact commutator_le_frattini_of_isPGroup (p := p)

end Order

section Kernel

variable {X : Type*} [Group X] {p : ℕ}

theorem isPGroup_ker_conjNormal {Q : Subgroup X} [Q.Normal] (hQ : IsPGroup p Q)
    (hQc : Subgroup.centralizer (Q : Set X) ≤ Q) :
    IsPGroup p (MulAut.conjNormal (H := Q)).ker := by
  refine hQ.to_le fun x hx => hQc (Subgroup.mem_centralizer_iff.mpr fun q hq => ?_)
  have hfix := congrArg (fun σ : MulAut Q => ((σ ⟨q, hq⟩ : Q) : X)) (MonoidHom.mem_ker.mp hx)
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at hfix
  calc q * x = x * q * x⁻¹ * x := by rw [hfix]
    _ = x * q := by group

theorem isPGroup_ker_centerQuotient_action {Q : Subgroup X} [Q.Normal] (hQ : IsPGroup p Q)
    (hQc : Subgroup.centralizer (Q : Set X) ≤ Q) (D : Subgroup Q) [D.Characteristic]
    (hZ : Subgroup.center D ≤ frattini D) (hker : IsPGroup p (frattiniAction D).ker) :
    IsPGroup p ((autQuotient (Subgroup.center D)).comp
      ((MulAut.characteristic D).comp (MulAut.conjNormal (H := Q)))).ker := by
  refine (hker.comap_of_ker_isPGroup _ (isPGroup_ker_conjNormal hQ hQc)).to_le fun x hx => ?_
  rw [Subgroup.mem_comap, mem_ker_frattiniAction]
  intro d
  have hx' : (MulAut.characteristic D) (MulAut.conjNormal x) ∈
      (autQuotient (Subgroup.center D)).ker := hx
  exact hZ ((mem_ker_autQuotient _).mp hx' d)

end Kernel

section Action

variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] {n : ℕ}

@[expose] noncomputable def centerQuotientAction (E : Subgroup G)
    (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin n → ZMod p)) :
    Subgroup.normalizer (E : Set G) →* GL (Fin n) (ZMod p) :=
  (elemAutEquivGL e).toMonoidHom.comp
    ((autQuotient (Subgroup.center E)).comp E.normalizerMonoidHom)

theorem centerQuotientAction_mulVec (E : Subgroup G)
    (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin n → ZMod p))
    (g : Subgroup.normalizer (E : Set G)) {u v : E} (huv : (v : G) = (g : G) * u * (g : G)⁻¹) :
    (centerQuotientAction E e g : Matrix (Fin n) (Fin n) (ZMod p)) *ᵥ
      Multiplicative.toAdd (e (u : E ⧸ Subgroup.center E)) =
        Multiplicative.toAdd (e (v : E ⧸ Subgroup.center E)) := by
  have hv : E.normalizerMonoidHom g u = v := Subtype.ext huv.symm
  change ((elemAutEquivGL e ((autQuotient (Subgroup.center E)) (E.normalizerMonoidHom g)) :
    GL (Fin n) (ZMod p)) : Matrix (Fin n) (Fin n) (ZMod p)) *ᵥ _ = _
  rw [elemAutEquivGL_mulVec, autQuotient_mk, hv]

theorem centerQuotientAction_eq (E : Subgroup G)
    (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin n → ZMod p))
    (g : Subgroup.normalizer (E : Set G)) (a : GL (Fin n) (ZMod p))
    (ha : ∀ u v : E, (v : G) = (g : G) * u * (g : G)⁻¹ →
      Multiplicative.toAdd (e (v : E ⧸ Subgroup.center E)) =
        (a : Matrix (Fin n) (Fin n) (ZMod p)) *ᵥ
          Multiplicative.toAdd (e (u : E ⧸ Subgroup.center E))) :
    centerQuotientAction E e g = a := by
  apply Units.ext
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun w => ?_
  obtain ⟨q, hq⟩ := e.surjective (Multiplicative.ofAdd w)
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
  have hw : w = Multiplicative.toAdd (e (u : E ⧸ Subgroup.center E)) := by
    rw [hq]
    rfl
  have huv : ((E.normalizerMonoidHom g u : E) : G) = (g : G) * u * (g : G)⁻¹ := rfl
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hw, centerQuotientAction_mulVec E e g huv,
    ha u _ huv]

theorem statedSL_le_map_centerQuotientAction (E L : Subgroup G)
    (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p))
    (h : ∀ a ∈ StatedSL 2 (ZMod p), ∃ g ∈ L, g ∈ Subgroup.normalizer (E : Set G) ∧
      ∀ u v : E, (v : G) = g * u * g⁻¹ →
        Multiplicative.toAdd (e (v : E ⧸ Subgroup.center E)) =
          (a : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ
            Multiplicative.toAdd (e (u : E ⧸ Subgroup.center E))) :
    StatedSL 2 (ZMod p) ≤
      (L.subgroupOf (Subgroup.normalizer (E : Set G))).map (centerQuotientAction E e) := by
  intro a ha
  obtain ⟨g, hgL, hgN, hga⟩ := h a ha
  exact ⟨⟨g, hgN⟩, hgL, centerQuotientAction_eq E e ⟨g, hgN⟩ a hga⟩

end Action

end CFSG.AGLEmbedding
