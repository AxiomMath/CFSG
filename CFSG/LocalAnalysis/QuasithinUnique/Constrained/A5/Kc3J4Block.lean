
module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3CoverBase

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5
open CFSG.QuasithinUnique.A5.Kc3Cover

@[expose] def D5Plus {G : Type} [Group G] (L : Subgroup G) : Prop :=
  ∃ (V Q : Subgroup G), V ≤ Q ∧ Q ≤ L ∧ IsPGroup 2 Q ∧
    L ≤ Subgroup.normalizer (Q : Set G) ∧ L ≤ Subgroup.normalizer (V : Set G) ∧ ⁅Q, L⁆ ≤ V ∧
    ∃ α : ↥L →* ↥(alternatingGroup (Fin 5)), Function.Surjective α ∧
      (∀ l : ↥L, α l = 1 ↔ (l : G) ∈ Q) ∧
      ∃ β : ↥V ≃* Multiplicative ↥(evenWeight 5),
        ∀ (l : ↥L) (v w : ↥V), (w : G) = l * v * l⁻¹ →
          Multiplicative.toAdd (β w) =
            Delta5.vact ((α l : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5))
              (Multiplicative.toAdd (β v))

theorem D5Plus.d5Data {G : Type} [Group G] {L : Subgroup G} (h : D5Plus L) : D5Data L := by
  obtain ⟨V, Q, hVQ, hQL, hQ2, hLQ, hLV, -, α, hα, hαQ, β, hβ⟩ := h
  exact ⟨V, Q, hVQ, hQL, hQ2, hLQ, hLV, α, hα, hαQ, β, hβ⟩

theorem d5Plus_of_block {G : Type} [Group G] [Finite G] {L : Subgroup G} (hL : IsShort2 L)
    (h5 : IsAltType L 5) : D5Plus L := by
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

section Transport

variable {G : Type} [Group G]

theorem le_normalizer_of_conj_mem {S Q : Subgroup G}
    (h : ∀ s ∈ S, ∀ q ∈ Q, s * q * s⁻¹ ∈ Q) : S ≤ Subgroup.normalizer (Q : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h s hs x hx, fun hx => ?_⟩
  have := h s⁻¹ (S.inv_mem hs) _ hx
  simpa [mul_assoc] using this

theorem d5Plus_subgroupOf {K L : Subgroup G} (hLK : L ≤ K) (h : D5Plus L) :
    D5Plus (L.subgroupOf K) := by
  obtain ⟨V, Q, hVQ, hQL, hQ2, hLQ, hLV, hQLV, α, hα, hαQ, β, hβ⟩ := h
  have hVK : V ≤ K := hVQ.trans (hQL.trans hLK)
  have hQK : Q ≤ K := hQL.trans hLK
  let eL : ↥(L.subgroupOf K) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLK
  let eV : ↥(V.subgroupOf K) ≃* ↥V := Subgroup.subgroupOfEquivOfLe hVK
  have hmemL : ∀ l : ↥(L.subgroupOf K), ((eL l : ↥L) : G) = ((l : ↥K) : G) := fun _ => rfl
  have hmemV : ∀ v : ↥(V.subgroupOf K), ((eV v : ↥V) : G) = ((v : ↥K) : G) := fun _ => rfl
  have hconj : ∀ (l : ↥K) (x : ↥K), ((l * x * l⁻¹ : ↥K) : G) = (l : G) * (x : G) * (l : G)⁻¹ :=
    fun _ _ => rfl
  refine ⟨V.subgroupOf K, Q.subgroupOf K, ?_, ?_, ?_, ?_, ?_, ?_, α.comp eL.toMonoidHom, ?_, ?_,
    eV.trans β, ?_⟩
  · intro x hx
    exact Subgroup.mem_subgroupOf.2 (hVQ (Subgroup.mem_subgroupOf.1 hx))
  · intro x hx
    exact Subgroup.mem_subgroupOf.2 (hQL (Subgroup.mem_subgroupOf.1 hx))
  · exact hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQK).symm
  · refine le_normalizer_of_conj_mem fun l hl q hq => ?_
    rw [Subgroup.mem_subgroupOf] at hl hq ⊢
    have := (Subgroup.mem_normalizer_iff.1 (hLQ (Subgroup.mem_subgroupOf.1 hl)) (q : G)).1 hq
    simpa [hconj] using this
  · refine le_normalizer_of_conj_mem fun l hl v hv => ?_
    rw [Subgroup.mem_subgroupOf] at hl hv ⊢
    have := (Subgroup.mem_normalizer_iff.1 (hLV (Subgroup.mem_subgroupOf.1 hl)) (v : G)).1 hv
    simpa [hconj] using this
  · rw [Subgroup.commutator_le]
    intro q hq l hl
    rw [Subgroup.mem_subgroupOf]
    have hq' : (q : G) ∈ Q := Subgroup.mem_subgroupOf.1 hq
    have hl' : (l : G) ∈ L := Subgroup.mem_subgroupOf.1 hl
    have := hQLV (Subgroup.commutator_mem_commutator hq' hl')
    simpa [commutatorElement_def] using this
  · intro a
    obtain ⟨l, hl⟩ := hα a
    exact ⟨eL.symm l, by simp [hl]⟩
  · intro l
    show α (eL l) = 1 ↔ _
    rw [hαQ (eL l), hmemL]
    exact (Subgroup.mem_subgroupOf).symm
  · intro l v w hw
    have hw' : ((eV w : ↥V) : G) = ((eL l : ↥L) : G) * ((eV v : ↥V) : G) * ((eL l : ↥L) : G)⁻¹ := by
      rw [hmemV, hmemL, hmemV, ← hconj]
      exact congrArg Subtype.val hw
    exact hβ (eL l) (eV v) (eV w) hw'

theorem d5Plus_map {G' : Type} [Group G'] (f : G →* G') (hf : Function.Injective f)
    {L : Subgroup G} (h : D5Plus L) : D5Plus (L.map f) := by
  obtain ⟨V, Q, hVQ, hQL, hQ2, hLQ, hLV, hQLV, α, hα, hαQ, β, hβ⟩ := h
  let eL : ↥L ≃* ↥(L.map f) := L.equivMapOfInjective f hf
  let eV : ↥V ≃* ↥(V.map f) := V.equivMapOfInjective f hf
  have hmemL : ∀ l : ↥L, ((eL l : ↥(L.map f)) : G') = f (l : G) := fun _ => rfl
  have hmemV : ∀ v : ↥V, ((eV v : ↥(V.map f)) : G') = f (v : G) := fun _ => rfl
  have hconj : ∀ (l x : G), f (l * x * l⁻¹) = f l * f x * (f l)⁻¹ := fun l x => by simp
  refine ⟨V.map f, Q.map f, Subgroup.map_mono hVQ, Subgroup.map_mono hQL,
    hQ2.of_equiv (Q.equivMapOfInjective f hf), ?_, ?_, ?_, α.comp eL.symm.toMonoidHom, ?_, ?_,
    eV.symm.trans β, ?_⟩
  · refine le_normalizer_of_conj_mem fun l hl q hq => ?_
    obtain ⟨l0, hl0, rfl⟩ := hl
    obtain ⟨q0, hq0, rfl⟩ := hq
    refine ⟨l0 * q0 * l0⁻¹, ?_, hconj l0 q0⟩
    exact (Subgroup.mem_normalizer_iff.1 (hLQ hl0) q0).1 hq0
  · refine le_normalizer_of_conj_mem fun l hl v hv => ?_
    obtain ⟨l0, hl0, rfl⟩ := hl
    obtain ⟨v0, hv0, rfl⟩ := hv
    refine ⟨l0 * v0 * l0⁻¹, ?_, hconj l0 v0⟩
    exact (Subgroup.mem_normalizer_iff.1 (hLV hl0) v0).1 hv0
  · rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono hQLV
  · intro a
    obtain ⟨l, hl⟩ := hα a
    exact ⟨eL l, by simp [hl]⟩
  · intro l'
    obtain ⟨l, rfl⟩ := eL.surjective l'
    show α (eL.symm (eL l)) = 1 ↔ _
    rw [MulEquiv.symm_apply_apply, hαQ l, hmemL]
    constructor
    · intro hq
      exact ⟨l, hq, rfl⟩
    · rintro ⟨q, hq, hql⟩
      have : q = (l : G) := hf hql
      rwa [← this]
  · intro l' v' w' hw'
    obtain ⟨l, rfl⟩ := eL.surjective l'
    obtain ⟨v, rfl⟩ := eV.surjective v'
    obtain ⟨w, rfl⟩ := eV.surjective w'
    have hw : (w : G) = (l : G) * (v : G) * (l : G)⁻¹ := by
      apply hf
      rw [hconj, ← hmemL, ← hmemV, ← hmemV]
      exact hw'
    have e1 : (eV.symm.trans β) (eV w) = β w := by
      show β (eV.symm (eV w)) = β w
      rw [MulEquiv.symm_apply_apply]
    have e2 : (eV.symm.trans β) (eV v) = β v := by
      show β (eV.symm (eV v)) = β v
      rw [MulEquiv.symm_apply_apply]
    have e3 : (α.comp eL.symm.toMonoidHom) (eL l) = α l := by
      show α (eL.symm (eL l)) = α l
      rw [MulEquiv.symm_apply_apply]
    rw [e1, e2, e3]
    exact hβ l v w hw

end Transport

section Image

variable {G : Type} [Group G] (K : Subgroup G)

theorem img_commutator_eq {A B : Subgroup G} (hA : A ≤ nK K) (hB : B ≤ nK K) :
    ⁅img K A, img K B⁆ = img K ⁅A, B⁆ := by
  have hAB : ⁅A.subgroupOf (nK K), B.subgroupOf (nK K)⁆ = (⁅A, B⁆).subgroupOf (nK K) := by
    apply Subgroup.map_injective (nK K).subtype_injective
    have hc : ⁅A, B⁆ ≤ nK K := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      exact (nK K).mul_mem ((nK K).mul_mem ((nK K).mul_mem (hA ha) (hB hb))
        ((nK K).inv_mem (hA ha))) ((nK K).inv_mem (hB hb))
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hA, inf_eq_left.2 hB, inf_eq_left.2 hc]
  unfold img
  rw [← Subgroup.map_commutator, hAB]

theorem d5Plus_img
    {L : Subgroup G} (hLK : L ≤ K) (hZ : IsPGroup 2 (zK K)) (h : D5Plus L) :
    D5Plus (img K L) := by
  classical
  obtain ⟨V, Q, hVQ, hQL, hQ2, hLQ, hLV, hQLV, α, hα, hαQ, β, hβ⟩ := h
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
    img_le_normalizer K hLQ, img_le_normalizer K hLV, ?_, αbar, ?_, ?_, eV.symm.trans β, ?_⟩
  · rw [img_commutator_eq K hQN hLN]
    exact img_mono K hQLV
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

end Image

@[expose] def Kc3ForSPlus (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K L S₀ T₀ : Subgroup G),
    CFSG.IsQuasisimple ↥K → P ↥K → Subgroup.center ↥K = ⊥ → L ≤ K → D5Plus L → ⁅L, L⁆ = L →
    S₀ ≤ Subgroup.normalizer (L : Set G) → IsPGroup 2 S₀ → IsPGroup 2 T₀ → S₀ ≤ T₀ →
    T₀ ≤ Subgroup.normalizer (K : Set G) → IsSylowTwoOf T₀ (K ⊔ T₀) →
    ∃ X S₁ : Subgroup G, CharTwo X ∧ L ⊔ S₀ ≤ X ∧ X ≤ K ⊔ T₀ ∧ IsSylowTwoOf S₁ X ∧ S₀ ≤ S₁ ∧
      ¬ IsSubnormal L (L ⊔ S₁)

theorem kc3For_of_simplePlus {P : ∀ (X : Type) [Group X], Prop}
    (hP : ∀ (X Y : Type) [Group X] [Group Y], X ≃* Y → P X → P Y) (h : Kc3ForSPlus P) :
    Kc3For P := by
  intro G _ _ K L S₀ T₀ hq hmod hZ hLK hL h5 hSL hS hT hST hTK hTS
  have hD5 : D5Plus L := d5Plus_of_block hL h5
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
      (d5Plus_img K hLK hZ2 hD5) (img_commutator K hLN (perfect_of_block hL h5))
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

section Facts

variable {G : Type} [Group G]

theorem le_Q_of_normal_two {L Q D : Subgroup G} (α : ↥L →* ↥(alternatingGroup (Fin 5)))
    (hα : Function.Surjective α) (hαQ : ∀ l : ↥L, α l = 1 ↔ (l : G) ∈ Q) (hDL : D ≤ L)
    (hDn : L ≤ Subgroup.normalizer (D : Set G)) (hD2 : IsPGroup 2 D) : D ≤ Q := by
  classical
  set M : Subgroup ↥L := D.subgroupOf L with hM
  have hMn : M.Normal := by
    refine ⟨fun m hm l => ?_⟩
    have hm' : (m : G) ∈ D := Subgroup.mem_subgroupOf.1 hm
    rw [Subgroup.mem_subgroupOf]
    have := (Subgroup.mem_normalizer_iff.1 (hDn l.2) (m : G)).1 hm'
    simpa using this
  have hM2 : IsPGroup 2 ↥M := hD2.of_equiv (Subgroup.subgroupOfEquivOfLe hDL).symm
  have hMa : IsPGroup 2 ↥(M.map α) :=
    hM2.of_surjective (α.subgroupMap M) (α.subgroupMap_surjective M)
  have hNa : (M.map α).Normal := Subgroup.Normal.map hMn α hα
  have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.map α) with h | h
  · intro x hx
    have hxL : x ∈ L := hDL hx
    have h1 : α ⟨x, hxL⟩ ∈ M.map α := ⟨⟨x, hxL⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    exact (hαQ ⟨x, hxL⟩).1 h1
  · exfalso
    rw [h] at hMa
    have h2 : IsPGroup 2 ↥(alternatingGroup (Fin 5)) := hMa.of_equiv Subgroup.topEquiv
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 h2
    rw [Delta5.a5_card] at hn
    have h3 : 3 ∣ 2 ^ n := by rw [← hn]; norm_num
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega

theorem card_V {V : Subgroup G} (β : ↥V ≃* Multiplicative ↥(evenWeight 5)) :
    Nat.card V = 16 := by
  classical
  rw [Nat.card_congr β.toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (evenWeight 5) ≃ evenWeight 5)]
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun x : Fin 5 → ZMod 2 => mem_evenWeight_iff x))]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem sixty_dvd_card {L : Subgroup G} (α : ↥L →* ↥(alternatingGroup (Fin 5)))
    (hα : Function.Surjective α) : 60 ∣ Nat.card L := by
  have := Subgroup.card_dvd_of_surjective hα
  rwa [Delta5.a5_card] at this

theorem five_dvd_card {L : Subgroup G} (α : ↥L →* ↥(alternatingGroup (Fin 5)))
    (hα : Function.Surjective α) : 5 ∣ Nat.card L :=
  (show 5 ∣ 60 by norm_num).trans (sixty_dvd_card α hα)

theorem exists_orderOf_five [Finite G] {L : Subgroup G} (α : ↥L →* ↥(alternatingGroup (Fin 5)))
    (hα : Function.Surjective α) : ∃ g ∈ L, orderOf g = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := L) 5 (five_dvd_card α hα)
  exact ⟨(x : G), x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

theorem le_of_five_elements [Finite G] {L Q : Subgroup G} (hQ2 : IsPGroup 2 Q) (hQL : Q ≤ L)
    (α : ↥L →* ↥(alternatingGroup (Fin 5))) (hα : Function.Surjective α)
    (hαQ : ∀ l : ↥L, α l = 1 ↔ (l : G) ∈ Q) (hperf : ⁅L, L⁆ = L) {N : Subgroup G}
    (hN : ∀ x ∈ L, orderOf x = 5 → x ∈ N) : L ≤ N := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set S : Set ↥L := {x | orderOf x = 5} with hS
  set M : Subgroup ↥L := Subgroup.closure S with hM
  have hMN : M ≤ N.subgroupOf L := by
    rw [hM, Subgroup.closure_le]
    intro x hx
    refine Subgroup.mem_subgroupOf.2 (hN x x.2 ?_)
    rw [Subgroup.orderOf_coe]
    exact hx
  have hMn : M.Normal := by
    refine ⟨fun n hn g => ?_⟩
    induction hn using Subgroup.closure_induction with
    | mem x hx =>
      refine Subgroup.subset_closure ?_
      show orderOf (g * x * g⁻¹) = 5
      have := (MulAut.conj g).orderOf_eq x
      rw [MulAut.conj_apply] at this
      rw [this]
      exact hx
    | one => simp
    | mul a b _ _ ha hb =>
      have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [this]
      exact M.mul_mem ha hb
    | inv a _ ha =>
      have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [this]
      exact M.inv_mem ha
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := L) 5 (five_dvd_card α hα)
  have hαx : α x ≠ 1 := by
    intro h1
    have hxQ : (x : G) ∈ Q := (hαQ x).1 h1
    obtain ⟨n, hn⟩ := hQ2 ⟨x, hxQ⟩
    have h2 : (x : ↥L) ^ 2 ^ n = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val hn
      simpa using this
    have h3 : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h2
    rw [hx] at h3
    have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) h3
    omega
  have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hNa : (M.map α).Normal := Subgroup.Normal.map hMn α hα
  have hαM : M.map α = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.map α) with h | h
    · exfalso
      have h1 : α x ∈ M.map α := ⟨x, Subgroup.subset_closure hx, rfl⟩
      rw [h, Subgroup.mem_bot] at h1
      exact hαx h1
    · exact h
  have hLMQ : ∀ l : ↥L, ∃ m ∈ M, ∃ q : ↥(Q.subgroupOf L), l = m * q := by
    intro l
    have h1 : α l ∈ M.map α := by rw [hαM]; trivial
    obtain ⟨m, hm, hml⟩ := h1
    refine ⟨m, hm, ⟨m⁻¹ * l, ?_⟩, by simp⟩
    rw [Subgroup.mem_subgroupOf]
    refine (hαQ _).1 ?_
    rw [map_mul, map_inv, hml, inv_mul_cancel]
  let π : ↥L →* ↥L ⧸ M := QuotientGroup.mk' M
  have hQ2' : IsPGroup 2 ↥(Q.subgroupOf L) := hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQL).symm
  have hπQ : Function.Surjective (π.comp (Q.subgroupOf L).subtype) := by
    intro y
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨m, hm, q, hq⟩ := hLMQ l
    refine ⟨q, ?_⟩
    show π (q : ↥L) = (l : ↥L ⧸ M)
    have : (l : ↥L ⧸ M) = ((m * q : ↥L) : ↥L ⧸ M) := by rw [← hq]
    rw [this, QuotientGroup.mk_mul]
    have hm1 : ((m : ↥L) : ↥L ⧸ M) = 1 := (QuotientGroup.eq_one_iff m).2 hm
    rw [hm1, one_mul]
    rfl
  have h2 : IsPGroup 2 (↥L ⧸ M) := hQ2'.of_surjective _ hπQ
  have hperf' : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.2 hperf
  have hperfq : Group.IsPerfect (↥L ⧸ M) := Group.IsPerfect.ofSurjective (f := π)
    QuotientGroup.mk_surjective
  have hnil : Group.IsNilpotent (↥L ⧸ M) := h2.isNilpotent
  have hsub : Subsingleton (↥L ⧸ M) := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    have : Group.IsPerfect (↥L ⧸ M) := hperfq
    exact Group.IsPerfect.not_isNilpotent (↥L ⧸ M) hnil
  intro l hl
  have h3 : (⟨l, hl⟩ : ↥L) ∈ M := by
    rw [← QuotientGroup.eq_one_iff]
    exact Subsingleton.elim _ _
  exact Subgroup.mem_subgroupOf.1 (hMN h3)

end Facts

end CFSG.QuasithinUnique.A5
