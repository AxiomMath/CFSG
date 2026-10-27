module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3CoverBase

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5
  CFSG.QuasithinUnique.A5.Kc3Cover
open scoped commutatorElement

@[expose] def D5S {G : Type} [Group G] (L : Subgroup G) : Prop :=
  ∃ (V Q : Subgroup G), V ≤ Q ∧ Q ≤ L ∧ IsPGroup 2 Q ∧
    L ≤ Subgroup.normalizer (Q : Set G) ∧ L ≤ Subgroup.normalizer (V : Set G) ∧
    ⁅Q, L⁆ ≤ V ∧
    ∃ α : ↥L →* ↥(alternatingGroup (Fin 5)), Function.Surjective α ∧
      (∀ l : ↥L, α l = 1 ↔ (l : G) ∈ Q) ∧
      ∃ β : ↥V ≃* Multiplicative ↥(evenWeight 5),
        ∀ (l : ↥L) (v w : ↥V), (w : G) = l * v * l⁻¹ →
          Multiplicative.toAdd (β w) =
            Delta5.vact ((α l : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5))
              (Multiplicative.toAdd (β v))

theorem d5S_of_block {G : Type} [Group G] [Finite G] {L : Subgroup G} (hL : IsShort2 L)
    (h5 : IsAltType L 5) : D5S L := by
  have hZ : blockZ L = ⊥ := AppC.blockZ_eq_bot_of_alt5 hL h5
  obtain ⟨α, hα, hαk, β, hβ, hβk, hβe⟩ := h5
  have hinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, hZ, Subgroup.bot_subgroupOf]
  refine ⟨blockU L, blockQ L, C1.blockU_le_blockQ hL, C1.blockQ_le L, C1.blockQ_isPGroup L,
    C1.le_normalizer_blockQ L, C1.le_normalizer_blockU L, le_rfl, α, hα, ?_,
    MulEquiv.ofBijective β ⟨hinj, hβ⟩, ?_⟩
  · intro l
    rw [← MonoidHom.mem_ker, hαk]
    exact AppC.mem_pCore_iff_mem_blockQ l
  · intro l v w hw
    apply Subtype.ext
    funext i
    exact hβe l v w hw i

namespace Kc3G2

variable {G : Type} [Group G] (K : Subgroup G)

theorem commutator_subgroupOf {A B N : Subgroup G} (hA : A ≤ N) (hB : B ≤ N) :
    ⁅A.subgroupOf N, B.subgroupOf N⁆ = ⁅A, B⁆.subgroupOf N := by
  have hAB : ⁅A, B⁆ ≤ N := by
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact N.mul_mem (N.mul_mem (N.mul_mem (hA ha) (hB hb)) (N.inv_mem (hA ha)))
      (N.inv_mem (hB hb))
  apply Subgroup.map_injective N.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hA, inf_eq_left.2 hB, inf_eq_left.2 hAB]

theorem img_commutator_le {A B C : Subgroup G} (hA : A ≤ nK K) (hB : B ≤ nK K)
    (h : ⁅A, B⁆ ≤ C) : ⁅img K A, img K B⁆ ≤ img K C := by
  have h1 : ⁅img K A, img K B⁆ = img K ⁅A, B⁆ := by
    unfold img
    rw [← Subgroup.map_commutator, commutator_subgroupOf hA hB]
  rw [h1]
  exact img_mono K h

end Kc3G2

open Kc3G2 in
theorem d5S_img
    {G : Type} [Group G] (K : Subgroup G) {L : Subgroup G} (hLK : L ≤ K)
    (hZ : IsPGroup 2 (zK K)) (h : D5S L) : D5S (img K L) := by
  classical
  obtain ⟨V, Q, hVQ, hQL, hQ2, hLQ, hLV, hcomm, α, hα, hαQ, β, hβ⟩ := h
  have hLN : L ≤ nK K := hLK.trans (K_le_nK K)
  have hMQ : L ⊓ zK K ≤ Q := inf_zK_le_Q K hLN hZ α hα hαQ
  have hVL : V ≤ L := hVQ.trans hQL
  have hVN : V ≤ nK K := hVL.trans hLN
  have hQN : Q ≤ nK K := hQL.trans hLN
  have hVZ : ∀ v : ↥V, (v : G) ∈ zK K → v = 1 := by
    intro v hv
    have hfix : ∀ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 →
        vact σ (Multiplicative.toAdd (β v)) = Multiplicative.toAdd (β v) := by
      intro σ hσ
      obtain ⟨l, hl⟩ := hα ⟨σ, Equiv.Perm.mem_alternatingGroup.2 hσ⟩
      have hc : (l : G) * (v : G) * (l : G)⁻¹ = v := by
        obtain ⟨hvK, hvc⟩ := (mem_zK K).1 hv
        have h1 := Subgroup.mem_center_iff.1 hvc ⟨l, hLK l.2⟩
        have h2 : (l : G) * (v : G) = (v : G) * l := congrArg Subtype.val h1
        rw [h2]
        group
      have h3 := hβ l v v hc.symm
      rw [hl] at h3
      exact h3.symm
    have h0 := fixed_alt_zero _ hfix
    have h1 : β v = 1 := by
      have : Multiplicative.toAdd (β v) =
          Multiplicative.toAdd (1 : Multiplicative ↥(evenWeight 5)) := h0
      exact Multiplicative.toAdd.injective this
    exact β.injective (by rw [h1, map_one])
  let sL : ↥L →* ↥(img K L) :=
    ((psi K).comp (Subgroup.inclusion hLN)).codRestrict (img K L)
      (fun l => (mem_img K).2 ⟨l, hLN l.2, l.2, rfl⟩)
  have hsL : Function.Surjective sL := by
    intro y
    obtain ⟨a, ha, haL, hay⟩ := (mem_img K).1 y.2
    exact ⟨⟨a, haL⟩, Subtype.ext hay⟩
  have hsL_val : ∀ l : ↥L, ((sL l : ↥(img K L)) : Gbar K) = psi K ⟨l, hLN l.2⟩ := fun _ => rfl
  have hkerL : sL.ker ≤ α.ker := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl ⊢
    have h1 : psi K ⟨l, hLN l.2⟩ = 1 := by
      have := congrArg Subtype.val hl
      rwa [hsL_val] at this
    exact (hαQ l).2 (hMQ ⟨l.2, (psi_eq_one K).1 h1⟩)
  let αbar : ↥(img K L) →* ↥(alternatingGroup (Fin 5)) := sL.liftOfSurjective hsL ⟨α, hkerL⟩
  have hαbar : ∀ l : ↥L, αbar (sL l) = α l := fun l =>
    MonoidHom.liftOfRightInverse_comp_apply sL (Function.surjInv hsL)
      (Function.rightInverse_surjInv hsL) ⟨α, hkerL⟩ l
  let sV : ↥V →* ↥(img K V) :=
    ((psi K).comp (Subgroup.inclusion hVN)).codRestrict (img K V)
      (fun v => (mem_img K).2 ⟨v, hVN v.2, v.2, rfl⟩)
  have hsV : Function.Surjective sV := by
    intro y
    obtain ⟨a, ha, haV, hay⟩ := (mem_img K).1 y.2
    exact ⟨⟨a, haV⟩, Subtype.ext hay⟩
  have hsV_val : ∀ v : ↥V, ((sV v : ↥(img K V)) : Gbar K) = psi K ⟨v, hVN v.2⟩ := fun _ => rfl
  have hsVinj : Function.Injective sV := by
    intro v w hvw
    have h1 : psi K ⟨v, hVN v.2⟩ = psi K ⟨w, hVN w.2⟩ := by
      have := congrArg Subtype.val hvw
      rwa [hsV_val, hsV_val] at this
    have h2 := (psi_eq_iff K).1 h1
    have h3 : v⁻¹ * w = 1 := hVZ (v⁻¹ * w) (by simpa using h2)
    exact inv_mul_eq_one.1 h3
  let eV : ↥V ≃* ↥(img K V) := MulEquiv.ofBijective sV ⟨hsVinj, hsV⟩
  refine ⟨img K V, img K Q, img_mono K hVQ, img_mono K hQL, img_isPGroup K hQ2,
    img_le_normalizer K hLQ, img_le_normalizer K hLV,
    img_commutator_le K hQN hLN hcomm, αbar, ?_, ?_, eV.symm.trans β, ?_⟩
  · intro a
    obtain ⟨l, hl⟩ := hα a
    exact ⟨sL l, by rw [hαbar, hl]⟩
  · intro lb
    obtain ⟨l, rfl⟩ := hsL lb
    rw [hαbar, hsL_val]
    constructor
    · intro h1
      exact (mem_img K).2 ⟨l, hLN l.2, (hαQ l).1 h1, rfl⟩
    · intro h1
      obtain ⟨q, hq, hqQ, hql⟩ := (mem_img K).1 h1
      have h2 := (psi_eq_iff K).1 hql
      have h3 : (q : G)⁻¹ * (l : G) ∈ L ⊓ zK K := ⟨L.mul_mem (L.inv_mem (hQL hqQ)) l.2, h2⟩
      have h4 : (l : G) = q * ((q : G)⁻¹ * l) := by group
      apply (hαQ l).2
      rw [h4]
      exact Q.mul_mem hqQ (hMQ h3)
  · intro lb vb wb hw
    obtain ⟨l, rfl⟩ := hsL lb
    obtain ⟨v, rfl⟩ := hsV vb
    obtain ⟨w, rfl⟩ := hsV wb
    have hw' : psi K ⟨w, hVN w.2⟩ =
        psi K (⟨l, hLN l.2⟩ * ⟨v, hVN v.2⟩ * (⟨l, hLN l.2⟩ : ↥(nK K))⁻¹) := by
      rw [map_mul, map_mul, map_inv]
      simpa [hsV_val, hsL_val] using hw
    have h2 := (psi_eq_iff K).1 hw'
    have hu : (l : G) * (v : G) * (l : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 (hLV l.2) v).1 v.2
    have h3 : (w : G)⁻¹ * ((l : G) * v * (l : G)⁻¹) ∈ zK K := by simpa using h2
    have h4 : w⁻¹ * (⟨(l : G) * v * (l : G)⁻¹, hu⟩ : ↥V) = 1 :=
      hVZ _ (by simpa using h3)
    have h5 : (w : G) = (l : G) * v * (l : G)⁻¹ := by
      have := inv_mul_eq_one.1 h4
      exact congrArg Subtype.val this
    have e1 : (eV.symm.trans β) (sV w) = β w := by
      show β (eV.symm (eV w)) = β w
      rw [eV.symm_apply_apply]
    have e2 : (eV.symm.trans β) (sV v) = β v := by
      show β (eV.symm (eV v)) = β v
      rw [eV.symm_apply_apply]
    rw [e1, e2, hαbar]
    exact hβ l v w h5

@[expose] def Kc3ForS' (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K L S₀ T₀ : Subgroup G),
    CFSG.IsQuasisimple ↥K → P ↥K → Subgroup.center ↥K = ⊥ → L ≤ K → D5S L → ⁅L, L⁆ = L →
    S₀ ≤ Subgroup.normalizer (L : Set G) → IsPGroup 2 S₀ → IsPGroup 2 T₀ → S₀ ≤ T₀ →
    T₀ ≤ Subgroup.normalizer (K : Set G) → IsSylowTwoOf T₀ (K ⊔ T₀) →
    ∃ X S₁ : Subgroup G, CharTwo X ∧ L ⊔ S₀ ≤ X ∧ X ≤ K ⊔ T₀ ∧ IsSylowTwoOf S₁ X ∧ S₀ ≤ S₁ ∧
      ¬ IsSubnormal L (L ⊔ S₁)

theorem kc3For_of_simple' {P : ∀ (X : Type) [Group X], Prop}
    (hP : ∀ (X Y : Type) [Group X] [Group Y], X ≃* Y → P X → P Y) (h : Kc3ForS' P) :
    Kc3For P := by
  intro G _ _ K L S₀ T₀ hq hmod hZ hLK hL h5 hSL hS hT hST hTK hTS
  have hD5 : D5S L := d5S_of_block hL h5
  have hKN : K ≤ nK K := K_le_nK K
  have hLN : L ≤ nK K := hLK.trans hKN
  have hSN : S₀ ≤ nK K := hST.trans hTK
  have hMN : K ⊔ T₀ ≤ nK K := sup_le hKN hTK
  have hZ2 : IsPGroup 2 (zK K) := isPGroup_zK K hZ
  obtain ⟨hKq, hKc⟩ := img_K_quasisimple K hq
  have hKP : P ↥(img K K) := hP _ _ (equivImgK K) hmod
  have hTS' : IsSylowTwoOf (img K T₀) (img K K ⊔ img K T₀) := by
    have := isSylowTwoOf_img K hTS hMN ((zK_le K).trans le_sup_left)
    rwa [img_sup K hKN hTK] at this
  obtain ⟨Xb, Sb, hXb, hLSb, hXKb, hSb, hSSb, hnsb⟩ :=
    h (Gbar K) (img K K) (img K L) (img K S₀) (img K T₀) hKq hKP hKc (img_mono K hLK)
      (d5S_img K hLK hZ2 hD5) (img_commutator K hLN (perfect_of_block hL h5))
      (img_le_normalizer K hSL) (img_isPGroup K hS) (img_isPGroup K hT)
      (img_mono K hST) (img_le_normalizer K hTK) hTS'
  refine ⟨pre K Xb, pre K Sb, charTwo_pre K hZ2 hXb, ?_, ?_, isSylowTwoOf_pre K hZ2 hSb, ?_, ?_⟩
  · refine sup_le ?_ ?_
    · exact (le_pre_img K hLN).trans (pre_mono K (le_sup_left.trans hLSb))
    · exact (le_pre_img K hSN).trans (pre_mono K (le_sup_right.trans hLSb))
  · have h1 : Xb ≤ img K (K ⊔ T₀) := by
      rw [img_sup K hKN hTK]
      exact hXKb
    have := pre_mono K h1
    rwa [pre_img_of_zK_le K hMN ((zK_le K).trans le_sup_left)] at this
  · exact (le_pre_img K hSN).trans (pre_mono K hSSb)
  · intro hloc
    have hsub : IsSubnormal L (L ⊔ pre K Sb) := hloc.2.1.2.2.1
    have h1 := Kc3Gen.isSubnormal_subgroupOf (nK K) hsub
    have h2 := Kc3Gen.isSubnormal_map (psi K) h1
    have h3 : IsSubnormal (img K L) (img K (L ⊔ pre K Sb)) := h2
    rw [img_sup K hLN (pre_le_nK K Sb), img_pre] at h3
    exact hnsb h3

end CFSG.QuasithinUnique.A5
