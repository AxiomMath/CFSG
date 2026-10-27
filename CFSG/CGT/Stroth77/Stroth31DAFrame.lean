module

public import CFSG.CGT.Stroth77.Arch76FrameChar
public import CFSG.CGT.Stroth77.StrothFrameNE
public import CFSG.CGT.Stroth77.StrothFrameAmbient
public import CFSG.CGT.Stroth77.Stroth31

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsE IsSylowIn)

variable {G : Type} [Group G] [Finite G]

theorem closure_singleton_eq_one_or {s : G} (hs : s * s = 1) {x : G}
    (hx : x ∈ Subgroup.closure ({s} : Set G)) : x = 1 ∨ x = s := by
  refine Subgroup.closure_induction (p := fun x _ => x = 1 ∨ x = s) ?_ ?_ ?_ ?_ hx
  · intro y hy
    exact Or.inr (by simpa using hy)
  · exact Or.inl rfl
  · intro a b _ _ ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [hs, mul_assoc]
  · intro a _ ha
    rcases ha with rfl | rfl
    · exact Or.inl inv_one
    · exact Or.inr (inv_eq_of_mul_eq_one_right hs)

theorem card_sup_closure_singleton_le_mul_two (H : Subgroup G) {s : G}
    (hs : s * s = 1) (hN : s ∈ Subgroup.normalizer H) :
    Nat.card (H ⊔ Subgroup.closure ({s} : Set G) : Subgroup G) ≤ 2 * Nat.card H := by
  classical
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hconj : ∀ h ∈ H, s * h * s ∈ H := by
    intro h hh
    have := (Subgroup.mem_normalizer_iff.mp hN h).mp hh
    simpa [hsinv] using this
  let K : Subgroup G :=
    { carrier := {x | ∃ h ∈ H, x = h ∨ x = h * s}
      one_mem' := ⟨1, H.one_mem, Or.inl rfl⟩
      mul_mem' := by
        intro a b ha hb
        rcases ha with ⟨u, hu, hx⟩
        rcases hb with ⟨v, hv, hy⟩
        rcases hx with hx | hx <;> rcases hy with hy | hy
        · exact ⟨u * v, H.mul_mem hu hv, Or.inl (by rw [hx, hy])⟩
        · exact ⟨u * v, H.mul_mem hu hv, Or.inr (by rw [hx, hy]; simp [hs, mul_assoc])⟩
        · refine ⟨u * (s * v * s), H.mul_mem hu (hconj v hv), Or.inr ?_⟩
          rw [hx, hy]; simp [hs, mul_assoc]
        · refine ⟨u * (s * v * s), H.mul_mem hu (hconj v hv), Or.inl ?_⟩
          rw [hx, hy]
          calc (u * s) * (v * s) = u * (s * v * s) * (s * s) := by simp [hs, mul_assoc]
            _ = u * (s * v * s) := by simp [hs, mul_assoc]
      inv_mem' := by
        intro x hx
        rcases hx with ⟨u, hu, hx⟩
        rcases hx with hx | hx
        · exact ⟨u⁻¹, H.inv_mem hu, Or.inl (by simpa [hx])⟩
        · refine ⟨s * u⁻¹ * s, hconj u⁻¹ (H.inv_mem hu), Or.inr ?_⟩
          rw [hx]
          calc (u * s)⁻¹ = s * u⁻¹ := by rw [mul_inv_rev, hsinv]
            _ = (s * u⁻¹) * (s * s) := by simp [hs, mul_assoc]
            _ = (s * u⁻¹) := by simp [hs, mul_assoc]
            _ = (s * u⁻¹ * s) * s := by simp [hs, mul_assoc] }
  have hHK : H ≤ K := fun h hh => ⟨h, hh, Or.inl rfl⟩
  have hsK : s ∈ K := ⟨1, H.one_mem, Or.inr (by simp)⟩
  have hclK : Subgroup.closure ({s} : Set G) ≤ K := by
    rw [Subgroup.closure_le]
    simpa using hsK
  have hsupK : H ⊔ Subgroup.closure ({s} : Set G) ≤ K := sup_le hHK hclK
  let f : H × Fin 2 → K := fun p =>
    ⟨(p.1 : G) * s ^ (p.2 : ℕ), by
      refine K.mul_mem (hHK p.1.2) ?_
      refine pow_mem ?_ (p.2 : ℕ)
      simpa using hsK⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨h, hh, hx | hx⟩ := hx
    · refine ⟨(⟨h, hh⟩, 0), ?_⟩
      apply Subtype.ext
      simp [f, hx]
    · refine ⟨(⟨h, hh⟩, 1), ?_⟩
      apply Subtype.ext
      simp [f, hx]
  have hKcard : Nat.card K ≤ 2 * Nat.card H := by
    have hcard := Nat.card_le_card_of_surjective f hsurj
    rw [Nat.card_prod, Nat.card_fin] at hcard
    simpa [Nat.mul_comm] using hcard
  exact (Subgroup.card_le_of_le hsupK).trans hKcard

namespace StrothFrame

theorem card_T_eq (F : StrothFrame G) :
    Nat.card (F.A ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u} : Subgroup G) = 256 := by
  refine le_antisymm ?_ F.card_T_ge
  exact F.card_le_of_le_normalizer_E F.T_le_normalizer_E
    (F.S.isPGroup'.to_le F.T_le_S)

theorem T_inf_strothR (F : StrothFrame G)
    {τ : StrothTypeIndex} {dD : StrothWeakTypeData F.A τ} (h : F.IsD F.A dD)
    (hH : NoInvolutionsCentralizing (F.S : Subgroup G) F.A) :
    (F.A ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u} : Subgroup G) ⊓
      strothR (F.toAmbient hH) F.A = F.A := by
  apply le_antisymm
  · rintro x ⟨hxT, hxR⟩
    have hxS : x ∈ (F.S : Subgroup G) := F.T_le_S hxT
    have hxN : x ∈ Subgroup.normalizer (F.E : Set G) := F.T_le_normalizer_E hxT
    have hxC : x ∈ Subgroup.centralizer (omegaIn 1 F.A : Set G) := (mem_strothR.mp hxR).2.2
    exact h.mem_of_mem_normalizer_E hxS hxC hxN
  · intro x hx
    have hA_cent : F.A ≤ Subgroup.centralizer (omegaIn 1 F.A : Set G) :=
      ((Subgroup.le_centralizer_iff_isMulCommutative (K := F.A)).mpr
        F.dA.isMulCommutative).trans (Subgroup.centralizer_le (omegaIn_le 1 F.A))
    exact ⟨Subgroup.mem_sup_left hx,
      mem_strothR.mpr ⟨F.A_le_S hx, Subgroup.le_normalizer hx, hA_cent hx⟩⟩

end StrothFrame

theorem no_index_four_D_eq_A (F : StrothFrame G) {D : Subgroup G} {m : ℕ}
    (dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)) (h : F.IsD D dD)
    (hH : NoInvolutionsCentralizing (F.S : Subgroup G) F.A)
    (hDA : D = F.A) (C : Subgroup G)
    (hC : C ≤ strothR (F.toAmbient hH) D)
    (hmin : IsMinimalLModuleMod (h.toDatum hH).dataD C)
    (h4 : ((h.toDatum hH).D.subgroupOf C).index = 4) : False := by
  subst hDA
  have hCA : Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) = F.A := by
    rw [inf_comm]; exact h.cent
  have hCS : C ≤ (F.S : Subgroup G) := hC.trans (strothR_le_sylow (F.toAmbient hH) F.A)
  have hAC : F.A ≤ C := hmin.d_lt.le
  have h4' : (F.A.subgroupOf C).index = 4 := h4
  set T : Subgroup G := F.A ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u} with hTdef
  have hTC : T ⊓ C = F.A := by
    apply le_antisymm
    · rintro x ⟨hxT, hxC⟩
      have hxR : x ∈ strothR (F.toAmbient hH) F.A := hC hxC
      rw [hTdef] at hxT
      exact (le_of_eq (F.T_inf_strothR h hH)) ⟨hxT, hxR⟩
    · exact fun x hx => ⟨Subgroup.mem_sup_left hx, hAC hx⟩
  rcases F.arch76Lemma2 hCA with hT | ⟨s, hsS, hSeq, hs2, hsc, hsa, hsb, hrel⟩
  ·
    have hCT : C ≤ T := by
      rw [hTdef, ← hT]; exact hCS
    have hCleA : C ≤ F.A := by
      intro x hx
      exact (le_of_eq hTC) ⟨hCT hx, hx⟩
    exact (not_le_of_gt hmin.d_lt) hCleA
  ·
    have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
    have hA_mem : ∀ x ∈ F.A, x ∈ T := fun x hx => Subgroup.mem_sup_left hx
    have hUV_mem : F.dA.uv ∈ T :=
      Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    have hT_mem : F.dA.t ∈ T :=
      Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    have hU_mem : F.dA.u ∈ T :=
      Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    have hsuv : s⁻¹ * F.dA.uv * s ∈ T := by
      rcases hrel with ⟨huv, -, -⟩ | ⟨huv, -, -⟩
      · rw [huv]
        exact T.mul_mem (T.mul_mem (hA_mem _ (inv_mem F.dA.a.2))
          (hA_mem _ (inv_mem F.dA.b.2))) hUV_mem
      · rw [huv]
        exact T.mul_mem (T.mul_mem (hA_mem _ F.dA.a.2)
          (hA_mem _ (inv_mem F.dA.b.2))) hUV_mem
    have hst : s⁻¹ * F.dA.t * s ∈ T := by
      rcases hrel with ⟨-, ht, -⟩ | ⟨-, ht, -⟩
      · rw [ht]; exact T.mul_mem (hA_mem _ F.dA.a.2) hT_mem
      · rw [ht]; exact T.mul_mem (T.mul_mem (hA_mem _ F.dA.a.2)
          (hA_mem _ (pow_mem F.dA.b.2 2))) hT_mem
    have hsu : s⁻¹ * F.dA.u * s ∈ T := by
      rcases hrel with ⟨-, -, hu⟩ | ⟨-, -, hu⟩
      · rw [hu]; exact hU_mem
      · rw [hu]; exact T.mul_mem (hA_mem _ F.dA.c.2) hU_mem
    have hTclosure : T = Subgroup.closure
        ((F.A : Set G) ∪ {F.dA.uv, F.dA.t, F.dA.u}) := by
      rw [hTdef]
      apply le_antisymm
      · refine sup_le ?_ ?_
        · intro x hx
          exact Subgroup.subset_closure (Or.inl hx)
        · refine Subgroup.closure_mono ?_
          intro x hx
          exact Or.inr hx
      · rw [Subgroup.closure_le]
        intro x hx
        rcases hx with hx | hx
        · exact Subgroup.mem_sup_left hx
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl | rfl
          · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
          · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
          · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    have hsNA : s ∈ Subgroup.normalizer (F.A : Set G) := F.le_normalizer_A hCA hsS
    have hsNT : s ∈ Subgroup.normalizer T := by
      rw [hTclosure]
      have hle : Subgroup.closure ({s} : Set G) ≤
          Subgroup.normalizer (Subgroup.closure
            ((F.A : Set G) ∪ {F.dA.uv, F.dA.t, F.dA.u})) := by
        rw [Subgroup.le_normalizer_closure_iff]
        intro h hh g hg
        rcases closure_singleton_eq_one_or hs2 hh with h1 | h1
        · subst h
          simpa using Subgroup.subset_closure hg
        · subst h
          rcases hg with hg | hg
          · have hmemA : s * g * s⁻¹ ∈ F.A := by
              have := (Subgroup.mem_normalizer_iff.mp hsNA g).mp hg
              simpa [hsinv] using this
            exact Subgroup.subset_closure (Or.inl hmemA)
          · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
            rcases hg with rfl | rfl | rfl
            · rw [show s * F.dA.uv * s⁻¹ = s⁻¹ * F.dA.uv * s by rw [hsinv], ← hTclosure]
              exact hsuv
            · rw [show s * F.dA.t * s⁻¹ = s⁻¹ * F.dA.t * s by rw [hsinv], ← hTclosure]
              exact hst
            · rw [show s * F.dA.u * s⁻¹ = s⁻¹ * F.dA.u * s by rw [hsinv], ← hTclosure]
              exact hsu
      exact hle (Subgroup.subset_closure (Set.mem_singleton s))
    have hTeq : (F.S : Subgroup G) = T ⊔ Subgroup.closure ({s} : Set G) := by
      rw [hSeq, hTdef]
      rw [show ({F.dA.uv, F.dA.t, F.dA.u, s} : Set G) =
          {F.dA.uv, F.dA.t, F.dA.u} ∪ {s} by
        ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]; tauto]
      rw [Subgroup.closure_union]
      rw [← sup_assoc]
    have hcardS : Nat.card (F.S : Subgroup G) ≤ 2 * Nat.card T := by
      rw [hTeq]
      exact card_sup_closure_singleton_le_mul_two T hs2 hsNT
    have hcardT : Nat.card T = 256 := F.card_T_eq
    have hS_le_normT : (F.S : Subgroup G) ≤ Subgroup.normalizer T := by
      rw [hTeq]
      refine sup_le Subgroup.le_normalizer ?_
      rw [Subgroup.closure_le]
      simpa using hsNT
    haveI hNnormal : (T.subgroupOf (F.S : Subgroup G)).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hS_le_normT
    have hcard_sub : Nat.card (T.subgroupOf (F.S : Subgroup G)) = Nat.card T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe F.T_le_S).toEquiv
    have hIndexLe : (T.subgroupOf (F.S : Subgroup G)).index ≤ 2 := by
      have hmul := Subgroup.card_mul_index (T.subgroupOf (F.S : Subgroup G))
      rw [hcard_sub] at hmul
      have hpos : 0 < Nat.card T := by rw [hcardT]; norm_num
      refine Nat.le_of_mul_le_mul_left ?_ hpos
      rw [hmul]
      simpa [Nat.mul_comm] using hcardS
    let N : Subgroup (F.S : Subgroup G) := T.subgroupOf (F.S : Subgroup G)
    let f : (F.S : Subgroup G) →* ((F.S : Subgroup G) ⧸ N) := QuotientGroup.mk' N
    have hrelIndex : N.relIndex (C.subgroupOf (F.S : Subgroup G)) = 4 := by
      have h1 := Subgroup.relIndex_subgroupOf (H := T) (K := C)
        (L := (F.S : Subgroup G)) hCS
      have h2 : T.relIndex C = (F.A.subgroupOf C).index := by
        rw [← Subgroup.inf_relIndex_right (H := T) (K := C), hTC]
        rfl
      rw [show N.relIndex (C.subgroupOf (F.S : Subgroup G)) = T.relIndex C from h1]
      rw [h2, h4']
    have hMapCard : Nat.card ((C.subgroupOf (F.S : Subgroup G)).map f) = 4 := by
      have hker := Subgroup.relIndex_ker (f := f) (K := C.subgroupOf (F.S : Subgroup G))
      rw [show f.ker = N from QuotientGroup.ker_mk' (N := N), hrelIndex] at hker
      exact hker.symm
    have h4le : 4 ≤ N.index := by
      calc 4 = Nat.card ((C.subgroupOf (F.S : Subgroup G)).map f) := hMapCard.symm
        _ ≤ Nat.card (⊤ : Subgroup ((F.S : Subgroup G) ⧸ N)) :=
            Subgroup.card_le_of_le le_top
        _ = N.index := by rw [Subgroup.card_top]; rfl
    have : (4 : ℕ) ≤ 2 := le_trans h4le hIndexLe
    omega

end CFSG.CGT.Stroth77
