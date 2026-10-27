module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeDim

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1

section Norm

variable {W : Type} [CommGroup W] [Finite W]

local instance : Finite (MulAut W) :=
  Finite.of_injective (fun σ : MulAut W => (σ : W → W)) DFunLike.coe_injective

noncomputable local instance : Fintype (MulAut W) := Fintype.ofFinite _

open scoped Classical in
noncomputable def normHom (D : Subgroup (MulAut W)) : W →* W :=
  ∏ d : D, ((d : MulAut W) : W ≃* W).toMonoidHom

open scoped Classical in
theorem normHom_apply (D : Subgroup (MulAut W)) (w : W) :
    normHom D w = ∏ d : D, (d : MulAut W) w := by
  simp [normHom, MonoidHom.finsetProd_apply]

open scoped Classical in
theorem normHom_mem_fixV (D : Subgroup (MulAut W)) (w : W) : normHom D w ∈ fixV D := by
  rw [mem_fixV]
  intro g hg
  rw [normHom_apply, map_prod]
  have h1 : ∀ d : D, g ((d : MulAut W) w) = ((⟨g, hg⟩ * d : D) : MulAut W) w := fun d => rfl
  simp only [h1]
  exact Fintype.prod_equiv (Equiv.mulLeft (⟨g, hg⟩ : D)) _ (fun d : D => (d : MulAut W) w)
    fun _ => rfl

open scoped Classical in
theorem normHom_of_mem_fixV (hW : ∀ w : W, w * w = 1) {D : Subgroup (MulAut W)}
    (hD : Odd (Nat.card D)) {v : W} (hv : v ∈ fixV D) : normHom D v = v := by
  rw [normHom_apply]
  have h1 : ∀ d : D, (d : MulAut W) v = v := fun d => mem_fixV.1 hv d d.2
  simp only [h1, Finset.prod_const, Finset.card_univ, Fintype.card_eq_nat_card]
  exact pow_odd_eq_self_W hW hD v

end Norm

section Hyperplane

variable {W : Type} [CommGroup W] [Finite W]

theorem odd_card_of_pow_eq_one {p : ℕ} [Fact p.Prime] (hodd : Odd p) {D : Subgroup (MulAut W)}
    (hD : ∀ d ∈ D, d ^ p = 1) : Odd (Nat.card D) := by
  have hp : IsPGroup p D := fun d => ⟨1, by
    apply Subtype.ext
    simpa using hD d d.2⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hp
  rw [hn]
  exact hodd.pow

theorem sup_eq_of_relIndex_eq_prime {p : ℕ} [Fact p.Prime] {A D D' : Subgroup (MulAut W)}
    (hDA : D ≤ A) (hD'A : D' ≤ A) (hD : D.relIndex A = p) (hD' : D'.relIndex A = p)
    (hne : D ≠ D') : D ⊔ D' = A := by
  have hcard : ∀ E : Subgroup (MulAut W), E ≤ A → E.relIndex A = p →
      p * Nat.card E = Nat.card A := by
    intro E hEA hE
    have := E.relIndex_mul_card A
    rwa [hE, inf_eq_left.2 hEA] at this
  have hpD := hcard D hDA hD
  have hpD' := hcard D' hD'A hD'
  have hSA : D ⊔ D' ≤ A := sup_le hDA hD'A
  have h1 : Nat.card D ∣ Nat.card (D ⊔ D' : Subgroup (MulAut W)) :=
    Subgroup.card_dvd_of_le le_sup_left
  have h2 : Nat.card (D ⊔ D' : Subgroup (MulAut W)) ∣ Nat.card A := Subgroup.card_dvd_of_le hSA
  obtain ⟨c, hc⟩ := h1
  have hDpos : 0 < Nat.card D := Nat.card_pos
  have hcp : c ∣ p := by
    rw [hc, ← hpD, mul_comm p] at h2
    exact Nat.dvd_of_mul_dvd_mul_left hDpos h2
  rcases (Nat.dvd_prime (Fact.out : Nat.Prime p)).1 hcp with h | h
  · exfalso
    rw [h, mul_one] at hc
    have hDS : D = D ⊔ D' := Subgroup.eq_of_le_of_card_ge le_sup_left hc.le
    have hD'D : D' ≤ D := by rw [hDS]; exact le_sup_right
    have hcc : Nat.card D' = Nat.card D :=
      Nat.eq_of_mul_eq_mul_left (Fact.out : Nat.Prime p).pos (hpD'.trans hpD.symm)
    exact hne (Subgroup.eq_of_le_of_card_ge hD'D hcc.symm.le).symm
  · rw [h] at hc
    exact Subgroup.eq_of_le_of_card_ge hSA (by rw [hc, ← hpD, mul_comm])

end Hyperplane

end CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
