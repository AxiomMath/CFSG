module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Quaternion
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.GorensteinWalter

@[expose] def dihedralRot (n : ℕ) : Multiplicative (ZMod n) →* DihedralGroup n where
  toFun i := DihedralGroup.r (Multiplicative.toAdd i)
  map_one' := rfl
  map_mul' i j := by simp [DihedralGroup.r_mul_r]

theorem exists_closure_pair_eq_of_dihedral {n : ℕ} (H : Subgroup (DihedralGroup n)) :
    ∃ a b : DihedralGroup n, Subgroup.closure {a, b} = H := by
  classical
  let C : Subgroup (Multiplicative (ZMod n)) := H.comap (dihedralRot n)
  obtain ⟨c, hc⟩ := IsCyclic.exists_generator (α := C)
  have haH : dihedralRot n c ∈ H := c.2
  have hrot : ∀ i : ZMod n, DihedralGroup.r i ∈ H →
      DihedralGroup.r i ∈ Subgroup.zpowers (dihedralRot n c) := by
    intro i hi
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hc ⟨Multiplicative.ofAdd i, hi⟩)
    refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
    have h := congrArg (fun x : C => dihedralRot n x) hm
    simp only [Subgroup.coe_zpow, map_zpow] at h
    exact h
  have hzp : ∀ b : DihedralGroup n,
      Subgroup.zpowers (dihedralRot n c) ≤ Subgroup.closure {dihedralRot n c, b} :=
    fun b => Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  by_cases hs : ∃ j, DihedralGroup.sr j ∈ H
  · obtain ⟨j, hj⟩ := hs
    refine ⟨dihedralRot n c, DihedralGroup.sr j, le_antisymm ?_ ?_⟩
    · rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact haH
      · exact hj
    · intro x hx
      cases x with
      | r i => exact hzp _ (hrot i hx)
      | sr i =>
        have h1 : DihedralGroup.sr j * DihedralGroup.sr i ∈ H := H.mul_mem hj hx
        rw [DihedralGroup.sr_mul_sr] at h1
        have h2 : DihedralGroup.sr i = DihedralGroup.sr j * DihedralGroup.r (i - j) := by
          rw [DihedralGroup.sr_mul_r, add_sub_cancel]
        rw [h2]
        exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (hzp _ (hrot _ h1))
  · push Not at hs
    refine ⟨dihedralRot n c, dihedralRot n c, le_antisymm ?_ ?_⟩
    · rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl <;> exact haH
    · intro x hx
      cases x with
      | r i => exact hzp _ (hrot i hx)
      | sr i => exact absurd hx (hs i)

theorem exists_closure_pair_eq_of_isPGroup_pgl2 {F : Type} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) {H : Subgroup (PGL2 F)} (hH : IsPGroup 2 H) :
    ∃ a b : PGL2 F, Subgroup.closure {a, b} = H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (PGL2 F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  obtain ⟨S, hHS⟩ := hH.exists_le_sylow
  obtain ⟨S₀, m, ⟨e₀⟩⟩ :=
    CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.pgl2_dihedral_sylow hF
  let e : (S : Subgroup (PGL2 F)) ≃* DihedralGroup (2 ^ m) := (Sylow.equiv S S₀).trans e₀
  obtain ⟨a, b, hab⟩ := exists_closure_pair_eq_of_dihedral ((H.subgroupOf S).map e.toMonoidHom)
  refine ⟨(e.symm a : PGL2 F), (e.symm b : PGL2 F), ?_⟩
  have h1 : Subgroup.closure ({e.symm a, e.symm b} : Set (S : Subgroup (PGL2 F))) =
      H.subgroupOf S := by
    have h := congrArg (Subgroup.map e.symm.toMonoidHom) hab
    rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton, Subgroup.map_map] at h
    have hid : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id _ := by
      ext x
      simp
    rw [hid, Subgroup.map_id] at h
    simpa using h
  have h2 := congrArg (Subgroup.map (S : Subgroup (PGL2 F)).subtype) h1
  rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hHS] at h2
  exact h2

theorem le_range_inl_of_isPGroup {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime)
    (hFcard : Nat.card F = p ^ f) (hf : Odd f) {H : Subgroup (PGammaL2 F)}
    (hH : IsPGroup 2 H) : H ≤ (SemidirectProduct.inl : PGL2 F →* PGammaL2 F).range := by
  intro x hx
  rw [SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
  have hcard := CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.card_ringEquiv_of_card
    hp hFcard
  have : Finite (F ≃+* F) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hf.pos.ne')
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hH) ⟨x, hx⟩
  have h1 : orderOf (SemidirectProduct.rightHom x : F ≃+* F) ∣ 2 ^ k := by
    rw [← hk, Subgroup.orderOf_mk]
    exact orderOf_map_dvd _ _
  have h2 : orderOf (SemidirectProduct.rightHom x : F ≃+* F) ∣ f :=
    hcard ▸ orderOf_dvd_natCard _
  have h3 : Nat.Coprime (2 ^ k) f := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hf)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 h3) h2)

theorem exists_closure_pair_eq_of_isPGroup_pGammaL2 {F : Type} [Field F] [Finite F] {p f : ℕ}
    (hp : p.Prime) (hFcard : Nat.card F = p ^ f) (hF : IsOddPrimePower (Nat.card F))
    (hf : Odd f) {H : Subgroup (PGammaL2 F)} (hH : IsPGroup 2 H) :
    ∃ a b : PGammaL2 F, Subgroup.closure {a, b} = H := by
  have hH' : IsPGroup 2 (H.comap (SemidirectProduct.inl : PGL2 F →* PGammaL2 F)) :=
    hH.comap_of_injective _ SemidirectProduct.inl_injective
  obtain ⟨a, b, hab⟩ := exists_closure_pair_eq_of_isPGroup_pgl2 hF hH'
  refine ⟨SemidirectProduct.inl a, SemidirectProduct.inl b, ?_⟩
  have h := congrArg (Subgroup.map (SemidirectProduct.inl : PGL2 F →* PGammaL2 F)) hab
  rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton, Subgroup.map_comap_eq,
    inf_eq_right.mpr (le_range_inl_of_isPGroup hp hFcard hf hH)] at h
  exact h

end CFSG.ClassicalInvolution.Disconnected.AschTight
