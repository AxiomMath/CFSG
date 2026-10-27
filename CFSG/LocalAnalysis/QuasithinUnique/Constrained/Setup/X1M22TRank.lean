module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22TMu

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint CFSG.Quasithin
  CFSG.QuasithinUnique.Setup.Family

section Rank

variable {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
  (hEn : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (e : CQ L ≃* S22)
  (ι : ↥m22A →* MulAut W)

include hW in
theorem outer_rank
    (hιX : ∀ a : ↥m22A, ∃ x : ↥(L ⊔ E), (x : MulAut W) = ι a ∧ actS hEn e x = muA a)
    (x y : ↥m22A) (hord : orderOf (x * (y * x * y⁻¹)) = 11) :
    2 ^ 5 ≤ (fixV (Subgroup.zpowers (ι x))).index := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨xX, hxX1, hxX2⟩ := hιX x
  obtain ⟨yX, hyX1, hyX2⟩ := hιX y
  have hord' : orderOf (muA x * (muA y * muA x * (muA y)⁻¹)) = 11 := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, orderOf_injective muA muA_injective]
    exact hord
  have hcs : ∀ c ∈ [(1 : MulAut S22), actS hEn e yX], c ∈ (actS hEn e).range := by
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact one_mem _
    · simp only [List.mem_singleton] at hc
      rw [hc]
      exact ⟨yX, rfl⟩
  have hmem : muA x * (muA y * muA x * (muA y)⁻¹) ∈ Subgroup.closure
      {z : MulAut S22 | ∃ c ∈ [(1 : MulAut S22), actS hEn e yX], ∃ b : ↥(L ⊔ E),
        (b : MulAut W) ∈ Subgroup.zpowers (ι x) ∧ z = c * actS hEn e b * c⁻¹} := by
    have h1 : muA x ∈ {z : MulAut S22 | ∃ c ∈ [(1 : MulAut S22), actS hEn e yX], ∃ b : ↥(L ⊔ E),
        (b : MulAut W) ∈ Subgroup.zpowers (ι x) ∧ z = c * actS hEn e b * c⁻¹} :=
      ⟨1, by simp, xX, by rw [hxX1]; exact Subgroup.mem_zpowers _, by rw [hxX2]; simp⟩
    have h2 : muA y * muA x * (muA y)⁻¹ ∈ {z : MulAut S22 | ∃ c ∈ [(1 : MulAut S22),
        actS hEn e yX], ∃ b : ↥(L ⊔ E), (b : MulAut W) ∈ Subgroup.zpowers (ι x) ∧
          z = c * actS hEn e b * c⁻¹} :=
      ⟨actS hEn e yX, by simp, xX, by rw [hxX1]; exact Subgroup.mem_zpowers _, by
        rw [hxX2, hyX2]⟩
    exact Subgroup.mul_mem _ (Subgroup.subset_closure h1) (Subgroup.subset_closure h2)
  have hdisp := two_pow_le_index_pow_of_mem hW (G := L ⊔ E) (actS hEn e)
    (B := Subgroup.zpowers (ι x)) [(1 : MulAut S22), actS hEn e yX] hcs (by norm_num) hord' hmem
  rw [orderOf_two_zmod_11] at hdisp
  exact two_pow_le_of_pow_le (index_fixV_eq_two_pow hW _) hdisp (ρ := 5) (by norm_num)

variable (hirr : IsIrrOn L) (hιinj : Function.Injective ι)

include hW hirr hιinj in
theorem inner_rank
    (hιL : ∀ m : S22, ∃ l : ↥L, (l : MulAut W) = ι ⟨(m : Equiv.Perm (Fin 22)), m22_le_A m.2⟩ ∧
      redHom L e l = m)
    (a : ↥m22A) (ha : (a : Equiv.Perm (Fin 22)) ∈ NativeSporadic.M22) (ha2 : a * a = 1)
    (ha1 : a ≠ 1) : 2 ^ 4 ≤ (fixV (Subgroup.zpowers (ι a))).index := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨l, hl, -⟩ := hιL ⟨(a : Equiv.Perm (Fin 22)), ha⟩
  have hl' : ι a ∈ L := by
    have : (⟨(a : Equiv.Perm (Fin 22)), m22_le_A ha⟩ : ↥m22A) = a := rfl
    rw [this] at hl
    rw [← hl]
    exact l.2
  have hEzL : Subgroup.zpowers (ι a) ≤ L := by
    rw [Subgroup.zpowers_le]
    exact hl'
  have hg2 : ι a * ι a = 1 := by rw [← map_mul, ha2, map_one]
  have hEzel : IsElemAbelian2 (Subgroup.zpowers (ι a)) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨k, rfl⟩ _ ⟨m, rfl⟩
      exact (Commute.zpow_zpow_self (ι a) k m).eq
    · rintro _ ⟨k, rfl⟩
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, sq, hg2, one_zpow]
  have hsq := imgSub_sq (hEL := hEzL) (e := e) hEzel
  have hne : imgSub L (Subgroup.zpowers (ι a)) hEzL e ≠ ⊥ := by
    intro h
    have h1 : Nat.card (imgSub L (Subgroup.zpowers (ι a)) hEzL e) = 1 := by rw [h]; simp
    rw [card_imgSub hW hirr hEzL hEzel e] at h1
    have h2 := Subgroup.card_eq_one.1 h1
    have hmem : ι a ∈ Subgroup.zpowers (ι a) := Subgroup.mem_zpowers _
    rw [h2] at hmem
    exact ha1 (hιinj (by simpa using hmem))
  obtain ⟨cs, hcs, hgen⟩ := m22_gen1 _ hsq hne
  have h := two_pow_le_of_inner_gen hW hEzL e (k := 3) (p := 11) (by norm_num) ⟨cs, hcs, hgen⟩
  rw [orderOf_two_zmod_11] at h
  exact two_pow_le_of_pow_le (index_fixV_eq_two_pow hW _) h (ρ := 4) (by norm_num)

end Rank

end CFSG.QuasithinUnique.Setup.X1
