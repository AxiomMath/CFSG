
module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Img
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3D5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Families
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Gen

@[expose] public section

namespace CFSG.QuasithinUnique.A5.Kc3Cover

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5

variable {G : Type} [Group G] (K : Subgroup G)

theorem fixed_alt_zero (w : ↥(evenWeight 5)) (hw : ∀ σ : Equiv.Perm (Fin 5),
    Equiv.Perm.sign σ = 1 → vact σ w = w) : w = 0 := by
  have h1 : pact (Equiv.swap 0 1 * Equiv.swap 1 2) w.1 = w.1 :=
    congrArg Subtype.val (hw _ (by decide))
  have h2 : pact (Equiv.swap 2 3 * Equiv.swap 3 4) w.1 = w.1 :=
    congrArg Subtype.val (hw _ (by decide))
  have e1 : w.1 0 = w.1 1 := by
    have := congrFun h1 1
    rwa [pact, show (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 5))⁻¹ 1 = 0 by decide] at this
  have e2 : w.1 1 = w.1 2 := by
    have := congrFun h1 2
    rwa [pact, show (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 5))⁻¹ 2 = 1 by decide] at this
  have e3 : w.1 2 = w.1 3 := by
    have := congrFun h2 3
    rwa [pact, show (Equiv.swap 2 3 * Equiv.swap 3 4 : Equiv.Perm (Fin 5))⁻¹ 3 = 2 by decide] at this
  have e4 : w.1 3 = w.1 4 := by
    have := congrFun h2 4
    rwa [pact, show (Equiv.swap 2 3 * Equiv.swap 3 4 : Equiv.Perm (Fin 5))⁻¹ 4 = 3 by decide] at this
  have hs : ∑ i, w.1 i = 0 := w.2
  rw [Fin.sum_univ_five, ← e1, ← e2, ← e1, ← e3, ← e2, ← e1, ← e4, ← e3, ← e2, ← e1] at hs
  have h0 : w.1 0 = 0 := by
    revert hs
    generalize w.1 0 = a
    revert a
    decide
  apply Subtype.ext
  funext i
  fin_cases i
  · exact h0
  · exact e1 ▸ h0
  · exact e2 ▸ e1 ▸ h0
  · exact e3 ▸ e2 ▸ e1 ▸ h0
  · exact e4 ▸ e3 ▸ e2 ▸ e1 ▸ h0

theorem inf_zK_le_Q {L Q : Subgroup G} (hLN : L ≤ nK K) (hZ : IsPGroup 2 (zK K))
    (α : ↥L →* ↥(alternatingGroup (Fin 5))) (hα : Function.Surjective α)
    (hαQ : ∀ l : ↥L, α l = 1 ↔ (l : G) ∈ Q) : L ⊓ zK K ≤ Q := by
  classical
  set M : Subgroup ↥L := (L ⊓ zK K).subgroupOf L with hM
  have hMn : M.Normal := by
    refine ⟨fun m hm l => ?_⟩
    have hm' : (m : G) ∈ zK K := (Subgroup.mem_subgroupOf.1 hm).2
    rw [Subgroup.mem_subgroupOf]
    exact ⟨L.mul_mem (L.mul_mem l.2 m.2) (L.inv_mem l.2), by
      simpa using zK_conj K (hLN l.2) hm'⟩
  have hM2 : IsPGroup 2 ↥M := by
    intro m
    obtain ⟨k, hk⟩ := hZ ⟨(m : G), (Subgroup.mem_subgroupOf.1 m.2).2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hk
  have hMa : IsPGroup 2 ↥(M.map α) :=
    hM2.of_surjective (α.subgroupMap M) (α.subgroupMap_surjective M)
  have hNa : (M.map α).Normal := Subgroup.Normal.map hMn α hα
  have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.map α) with h | h
  · intro x hx
    have hxL : x ∈ L := hx.1
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

theorem d5_img {L : Subgroup G} (hLK : L ≤ K) (hZ : IsPGroup 2 (zK K)) (h : D5Data L) :
    D5Data (img K L) := by
  classical
  obtain ⟨V, Q, hVQ, hQL, hQ2, hLQ, hLV, α, hα, hαQ, β, hβ⟩ := h
  have hLN : L ≤ nK K := hLK.trans (K_le_nK K)
  have hMQ : L ⊓ zK K ≤ Q := inf_zK_le_Q K hLN hZ α hα hαQ
  have hVL : V ≤ L := hVQ.trans hQL
  have hVN : V ≤ nK K := hVL.trans hLN
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
      have : Multiplicative.toAdd (β v) = Multiplicative.toAdd (1 : Multiplicative ↥(evenWeight 5)) := h0
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
    img_le_normalizer K hLQ, img_le_normalizer K hLV, αbar, ?_, ?_, eV.symm.trans β, ?_⟩
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

@[expose] def sK : ↥K →* ↥(img K K) :=
  ((psi K).comp (Subgroup.inclusion (K_le_nK K))).codRestrict (img K K)
    (fun k => (mem_img K).2 ⟨k, K_le_nK K k.2, k.2, rfl⟩)

theorem sK_surjective : Function.Surjective (sK K) := by
  intro y
  obtain ⟨a, ha, haK, hay⟩ := (mem_img K).1 y.2
  exact ⟨⟨a, haK⟩, Subtype.ext hay⟩

theorem sK_ker : (sK K).ker = Subgroup.center ↥K := by
  ext k
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have h1 : psi K ⟨k, K_le_nK K k.2⟩ = 1 := congrArg Subtype.val h
    exact ((mem_zK K).1 ((psi_eq_one K).1 h1)).2
  · intro hk
    exact Subtype.ext ((psi_eq_one K).2 ((mem_zK K).2 ⟨k.2, hk⟩))

noncomputable def equivImgK : ↥K ⧸ Subgroup.center ↥K ≃* ↥(img K K) :=
  (QuotientGroup.quotientMulEquivOfEq (sK_ker K).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (sK K) (sK_surjective K))

theorem img_K_quasisimple (hq : CFSG.IsQuasisimple ↥K) :
    CFSG.IsQuasisimple ↥(img K K) ∧ Subgroup.center ↥(img K K) = ⊥ := by
  obtain ⟨hperf, hsimple, a, b, hab⟩ := hq
  have hsimple' : IsSimpleGroup ↥(img K K) := (equivImgK K).symm.isSimpleGroup
  have hnonab : ∃ x y : ↥(img K K), x * y ≠ y * x :=
    ⟨equivImgK K a, equivImgK K b, fun h => hab ((equivImgK K).injective (by simpa using h))⟩
  have hc : Subgroup.center ↥(img K K) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(img K K)) with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnonab
      have : x ∈ Subgroup.center ↥(img K K) := by rw [h]; trivial
      exact hxy ((Subgroup.mem_center_iff.1 this y).symm)
  have hperf' : Group.IsPerfect ↥(img K K) := by
    have := hperf
    exact Group.IsPerfect.ofSurjective (f := sK K) (sK_surjective K)
  refine ⟨⟨hperf', ?_, ?_⟩, hc⟩
  · let e : ↥(img K K) ⧸ Subgroup.center ↥(img K K) ≃* ↥(img K K) :=
      (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
    have := hsimple'
    exact e.isSimpleGroup
  · let e : ↥(img K K) ⧸ Subgroup.center ↥(img K K) ≃* ↥(img K K) :=
      (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
    obtain ⟨x, y, hxy⟩ := hnonab
    exact ⟨e.symm x, e.symm y, fun h => hxy (by simpa using congrArg e h)⟩

theorem img_commutator {L : Subgroup G} (hLN : L ≤ nK K) (h : ⁅L, L⁆ = L) :
    ⁅img K L, img K L⁆ = img K L := by
  have hA : ⁅L.subgroupOf (nK K), L.subgroupOf (nK K)⁆ = L.subgroupOf (nK K) := by
    apply Subgroup.map_injective (nK K).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hLN, h]
  unfold img
  rw [← Subgroup.map_commutator, hA]

theorem isSylowTwoOf_img {T M : Subgroup G} (hTM : IsSylowTwoOf T M) (hMN : M ≤ nK K)
    (hZM : zK K ≤ M) : IsSylowTwoOf (img K T) (img K M) := by
  obtain ⟨hTM', hT2, hTi⟩ := hTM
  refine ⟨img_mono K hTM', img_isPGroup K hT2, ?_⟩
  show ¬ 2 ∣ (img K T).relIndex (img K M)
  have hTN : T ≤ nK K := hTM'.trans hMN
  have h1 : pre K (img K M) = M := pre_img_of_zK_le K hMN hZM
  have h2 := relIndex_pre K (img K T) (img K M)
  rw [h1] at h2
  rw [← h2]
  intro hdvd
  exact hTi (dvd_trans hdvd (Subgroup.relIndex_dvd_of_le_left M (le_pre_img K hTN)))

end CFSG.QuasithinUnique.A5.Kc3Cover

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Kc3Cover

@[expose] def Kc3ForS (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K L S₀ T₀ : Subgroup G),
    CFSG.IsQuasisimple ↥K → P ↥K → Subgroup.center ↥K = ⊥ → L ≤ K → D5Data L → ⁅L, L⁆ = L →
    S₀ ≤ Subgroup.normalizer (L : Set G) → IsPGroup 2 S₀ → IsPGroup 2 T₀ → S₀ ≤ T₀ →
    T₀ ≤ Subgroup.normalizer (K : Set G) → IsSylowTwoOf T₀ (K ⊔ T₀) →
    ∃ X S₁ : Subgroup G, CharTwo X ∧ L ⊔ S₀ ≤ X ∧ X ≤ K ⊔ T₀ ∧ IsSylowTwoOf S₁ X ∧ S₀ ≤ S₁ ∧
      ¬ IsSubnormal L (L ⊔ S₁)

theorem kc3For_of_simple {P : ∀ (X : Type) [Group X], Prop}
    (hP : ∀ (X Y : Type) [Group X] [Group Y], X ≃* Y → P X → P Y) (h : Kc3ForS P) : Kc3For P := by
  intro G _ _ K L S₀ T₀ hq hmod hZ hLK hL h5 hSL hS hT hST hTK hTS
  have hD5 : D5Data L := d5Data_of_block hL h5
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
      (d5_img K hLK hZ2 hD5) (img_commutator K hLN (perfect_of_block hL h5))
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
