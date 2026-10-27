module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CBlockAbs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T123CB

open CFSG.Open

section Transfer

variable {T T' : Type} [Group T] [Group T']

private theorem map_comap_equiv (e : T ≃* T') (K : Subgroup T') :
    (K.comap e.toMonoidHom).map e.toMonoidHom = K :=
  Subgroup.map_comap_eq_self_of_surjective e.surjective K

private theorem comap_centralizer_image (e : T ≃* T') (S : Set T) :
    (Subgroup.centralizer (e '' S)).comap e.toMonoidHom = Subgroup.centralizer S := by
  ext g
  simp only [Subgroup.mem_comap, Subgroup.mem_centralizer_iff, Set.forall_mem_image,
    MulEquiv.coe_toMonoidHom]
  refine forall₂_congr fun s _ => ?_
  rw [← map_mul, ← map_mul, e.injective.eq_iff]

private theorem symm_mem_comap (e : T ≃* T') {K : Subgroup T'} {m : T'} (hm : m ∈ K) :
    e.symm m ∈ K.comap e.toMonoidHom := by
  rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, e.apply_symm_apply]
  exact hm

private theorem isComponentOf_comap (e : T ≃* T') {P K : Subgroup T'} (h : IsComponentOf P K) :
    IsComponentOf (P.comap e.toMonoidHom) (K.comap e.toMonoidHom) := by
  refine (Y10F.isComponentOf_map_iff (ι := e.toMonoidHom) e.injective).1 ?_
  rwa [map_comap_equiv, map_comap_equiv]

private theorem card_quotient_center_map (e : T ≃* T') (K : Subgroup T) :
    Nat.card (↥(K.map e.toMonoidHom) ⧸ Subgroup.center ↥(K.map e.toMonoidHom)) =
      Nat.card (↥K ⧸ Subgroup.center ↥K) := by
  let e' : K ≃* K.map e.toMonoidHom := K.equivMapOfInjective e.toMonoidHom e.injective
  have hc : (Subgroup.center K).map (e' : K →* K.map e.toMonoidHom) =
      Subgroup.center (K.map e.toMonoidHom) := Subgroup.map_center_eq e'
  exact (Nat.card_congr (QuotientGroup.congr _ _ e' hc).toEquiv).symm

private theorem card_quotient_center_comap (e : T ≃* T') (K : Subgroup T') :
    Nat.card (↥(K.comap e.toMonoidHom) ⧸ Subgroup.center ↥(K.comap e.toMonoidHom)) =
      Nat.card (↥K ⧸ Subgroup.center ↥K) := by
  have h := card_quotient_center_map e (K.comap e.toMonoidHom)
  rw [map_comap_equiv] at h
  exact h.symm

private theorem isElemAbelian_map {p : ℕ} (e : T ≃* T') {A : Subgroup T}
    (hA : IsElemAbelian p A) : IsElemAbelian p (A.map e.toMonoidHom) := by
  haveI : IsMulCommutative ↥A := hA.1
  refine ⟨inferInstance, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [MulEquiv.coe_toMonoidHom, ← map_pow, hA.2 x hx, map_one]

private theorem congr_apply_apply (e : T ≃* T') (α : MulAut T) (t : T) :
    MulAut.congr e α (e t) = e (α t) := by
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

private theorem comap_fixSub (e : T ≃* T') (α : MulAut T) :
    (fixSub (MulAut.congr e α)).comap e.toMonoidHom = fixSub α := by
  ext t
  rw [Subgroup.mem_comap, mem_fixSub, mem_fixSub, MulEquiv.coe_toMonoidHom, congr_apply_apply,
    e.injective.eq_iff]

end Transfer

theorem innerBlockAt_of_mulEquiv {p : ℕ} {T T' : Type} [Group T] [Group T'] (e : T ≃* T')
    (h : InnerBlockAt p T') : InnerBlockAt p T := by
  intro A a hA hAc haA ha1 hns
  have hcA : (Subgroup.centralizer ((A.map e.toMonoidHom : Subgroup T') : Set T')).comap
      e.toMonoidHom = Subgroup.centralizer (A : Set T) := by
    rw [Subgroup.coe_map]
    exact comap_centralizer_image e _
  have hns' : ¬ Group.IsSolvable
      ↥(Subgroup.centralizer ((A.map e.toMonoidHom : Subgroup T') : Set T')) := by
    intro hsol
    rw [← hcA] at hns
    exact hns (Group.isSolvable_of_isSolvable_injective
      (f := e.toMonoidHom.subgroupComap _) (MonoidHom.subgroupComap_injective _ _ e.injective))
  have hcard : Nat.card ↥(A.map e.toMonoidHom) = p ^ 2 :=
    (Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective).trans hAc
  obtain ⟨a'', ha''A, ha''a, P, M, hP, hM, hPM, hPd, hMd, haM⟩ := h _ (e a)
    (isElemAbelian_map e hA) hcard (Subgroup.mem_map_of_mem _ haA)
    (fun h1 => ha1 (e.injective (h1.trans (map_one e).symm))) hns'
  obtain ⟨a', ha'A, rfl⟩ : ∃ a' ∈ A, e a' = a'' :=
    ⟨e.symm a'', Subgroup.mem_map_equiv.1 ha''A, e.apply_symm_apply a''⟩
  refine ⟨a', ha'A, fun hz => ha''a ?_, P.comap e.toMonoidHom, M.comap e.toMonoidHom, ?_, ?_,
    Subgroup.comap_mono hPM, ?_, ?_, fun hc => haM ?_⟩
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact Subgroup.mem_zpowers_iff.2 ⟨k, by rw [← map_zpow, hk]⟩
  · rw [← hcA]
    exact isComponentOf_comap e hP
  · have h1 := comap_centralizer_image e {a'}
    rw [Set.image_singleton] at h1
    rw [← h1]
    exact isComponentOf_comap e hM
  · rw [card_quotient_center_comap]
    exact hPd
  · rw [card_quotient_center_comap]
    exact hMd
  · refine Subgroup.mem_centralizer_iff.2 fun m hm => ?_
    have h2 := congrArg e (Subgroup.mem_centralizer_iff.1 hc _ (symm_mem_comap e hm))
    rw [map_mul, map_mul, e.apply_symm_apply] at h2
    exact h2

theorem fieldBlockAt_of_mulEquiv {p : ℕ} {T T' : Type} [Group T] [Group T'] (e : T ≃* T')
    (h : FieldBlockAt p T') : FieldBlockAt p T := by
  intro α hα hout
  have hpow : MulAut.congr e α ^ p = 1 := by
    rw [← map_pow, hα, map_one]
  have hout' : ∀ t' : T', MulAut.conj t' ≠ MulAut.congr e α := by
    intro t' ht
    apply hout (e.symm t')
    ext x
    apply e.injective
    rw [← congr_apply_apply e α x, ← ht, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul,
      map_inv, e.apply_symm_apply]
  obtain ⟨M, hM, hMd, hperf, hstab⟩ := h (MulAut.congr e α) hpow hout'
  refine ⟨M.comap e.toMonoidHom, ?_, ?_, fun P hP hPP => ?_, fun β hβ => ?_⟩
  · rw [← comap_fixSub e α]
    exact isComponentOf_comap e hM
  · rw [card_quotient_center_comap]
    exact hMd
  · rw [← Subgroup.map_le_iff_le_comap]
    refine hperf _ (Subgroup.map_le_iff_le_comap.2 (by rw [comap_fixSub]; exact hP)) ?_
    rw [← Subgroup.map_commutator, hPP]
  · have hβ' : ∀ m ∈ M, MulAut.congr e β m = m := fun m hm =>
      calc MulAut.congr e β m = MulAut.congr e β (e (e.symm m)) := by rw [e.apply_symm_apply]
        _ = e (β (e.symm m)) := congr_apply_apply e β _
        _ = m := by rw [hβ _ (symm_mem_comap e hm), e.apply_symm_apply]
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hstab _ hβ')
    exact Subgroup.mem_zpowers_iff.2 ⟨j, (MulAut.congr e).injective (by rw [map_zpow, hj])⟩

end CFSG.LocalAnalysis.GLTheoremA.T123CB

end
