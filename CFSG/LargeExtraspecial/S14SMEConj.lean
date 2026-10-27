module

public import CFSG.LargeExtraspecial.S14SMELocal
public import CFSG.LargeExtraspecial.S14C12SmGraph

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

namespace SME

open Subgroup CFSG.Open

variable {G : Type} [Group G]

theorem conj_pow_inv (c x : G) (n : ℕ) : (c⁻¹ * x * c) ^ n = c⁻¹ * x ^ n * c := by
  have h := conj_pow (a := c⁻¹) (b := x) (i := n)
  rwa [inv_inv] at h

theorem orderOf_conj_inv (c x : G) : orderOf (c⁻¹ * x * c) = orderOf x := by
  rw [show c⁻¹ * x * c = MulAut.conj c⁻¹ x by rw [MulAut.conj_apply, inv_inv],
    MulEquiv.orderOf_eq]

theorem conj_conj_inv (c z : G) : c⁻¹ * (c * z * c⁻¹) * c = z := by group

theorem mem_M_conj_iff (S : Setting G) (g x : G) :
    g⁻¹ * x * g ∈ S.M ↔ Commute x (g * S.z * g⁻¹) := by
  rw [mem_centralizer_singleton_iff, ← SmithGraph.commute_conj_iff g x (g * S.z * g⁻¹),
    conj_conj_inv]
  exact ⟨fun h => h, fun h => h⟩

theorem mem_Qa_of_isConj_mul (h34a : SmithE34a) [Finite G] [IsSimpleGroup G] (S : Setting G)
    (hw : S.width = 10) (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) {g x : G}
    (hx : IsConj S.z x) (hxa : Commute x (g * S.z * g⁻¹))
    (hxa' : IsConj S.z (x * (g * S.z * g⁻¹))) : g⁻¹ * x * g ∈ S.QG := by
  by_contra hQ
  apply h34a G S hw hU _ (SmithGraph.isConj_conj hx g) ((mem_M_conj_iff S g x).mpr hxa) hQ
  have h : g⁻¹ * x * g * S.z = g⁻¹ * (x * (g * S.z * g⁻¹)) * g := by group
  rw [h]
  exact SmithGraph.isConj_conj hxa' g

theorem mem_Qa_symm [Finite G] (S : Setting G) {g k : G} (hQ : g⁻¹ * (k * S.z * k⁻¹) * g ∈ S.QG)
    (hne : k * S.z * k⁻¹ ≠ g * S.z * g⁻¹) : k⁻¹ * (g * S.z * g⁻¹) * k ∈ S.QG := by
  have hgt : (g⁻¹ * k) * S.z * (g⁻¹ * k)⁻¹ = g⁻¹ * (k * S.z * k⁻¹) * g := by group
  have hne' : g⁻¹ * (k * S.z * k⁻¹) * g ≠ S.z := by
    intro h
    apply hne
    calc k * S.z * k⁻¹ = g * (g⁻¹ * (k * S.z * k⁻¹) * g) * g⁻¹ := by group
      _ = g * S.z * g⁻¹ := by rw [h]
  have h := (mem_Qa_iff S _ _).mp (S.z_mem_Qa_of_mem_QG hgt hQ hne')
  have he : (g⁻¹ * k)⁻¹ * S.z * (g⁻¹ * k) = k⁻¹ * (g * S.z * g⁻¹) * k := by group
  rwa [he] at h

theorem commute_mul_of_not_commute' [Finite G] (S : Setting G) {d e x : G} (hd : d ∈ S.QG)
    (he : e ∈ S.QG) (hx : x ∈ S.QG) (hdx : ¬ Commute d x) (hex : ¬ Commute e x) :
    Commute (d * e) x := by
  have key : ∀ {f : G}, f ∈ S.QG → ¬ Commute f x → f * x = S.z * x * f := by
    intro f hf hfx
    rcases S.commutator_eq_one_or_z hf hx with h | h
    · exfalso
      apply hfx
      calc f * x = (f * x * f⁻¹ * x⁻¹) * x * f := by group
        _ = x * f := by rw [h, one_mul]
    · calc f * x = (f * x * f⁻¹ * x⁻¹) * x * f := by group
        _ = S.z * x * f := by rw [h]
  have hd' := key hd hdx
  have he' := key he hex
  have hdz : d * S.z = S.z * d := S.z_comm (S.QG_le_M hd)
  calc d * e * x = d * (e * x) := by group
    _ = d * (S.z * x * e) := by rw [he']
    _ = (d * S.z) * x * e := by group
    _ = (S.z * d) * x * e := by rw [hdz]
    _ = S.z * (d * x) * e := by group
    _ = S.z * (S.z * x * d) * e := by rw [hd']
    _ = (S.z * S.z) * x * (d * e) := by group
    _ = x * (d * e) := by rw [S.z_mul_z, one_mul]

theorem commute_mul_of_not_commute [Finite G] (S : Setting G) {g d e x : G}
    (hd : g⁻¹ * d * g ∈ S.QG) (he : g⁻¹ * e * g ∈ S.QG) (hx : g⁻¹ * x * g ∈ S.QG)
    (hdx : ¬ Commute d x) (hex : ¬ Commute e x) : Commute (d * e) x := by
  have h := commute_mul_of_not_commute' S hd he hx
    (fun h => hdx ((SmithGraph.commute_conj_iff g d x).mp h))
    (fun h => hex ((SmithGraph.commute_conj_iff g e x).mp h))
  rw [show g⁻¹ * d * g * (g⁻¹ * e * g) = g⁻¹ * (d * e) * g by group] at h
  exact (SmithGraph.commute_conj_iff g (d * e) x).mp h

theorem isConj_mul_of_mem_Qa [Finite G] (S : Setting G) {g d : G} (hd : g⁻¹ * d * g ∈ S.QG)
    (h1 : d ≠ 1) (ha : d ≠ g * S.z * g⁻¹) : IsConj d (d * (g * S.z * g⁻¹)) := by
  have h1' : g⁻¹ * d * g ≠ 1 := by
    intro h
    apply h1
    calc d = g * (g⁻¹ * d * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hz' : g⁻¹ * d * g ≠ S.z := by
    intro h
    apply ha
    calc d = g * (g⁻¹ * d * g) * g⁻¹ := by group
      _ = g * S.z * g⁻¹ := by rw [h]
  obtain ⟨q, -, hq⟩ := exists_conj_eq_mul_z S hd h1' hz'
  refine isConj_iff.mpr ⟨g * q * g⁻¹, ?_⟩
  have h2 : g * (q * (g⁻¹ * d * g) * q⁻¹) * g⁻¹ = g * ((g⁻¹ * d * g) * S.z) * g⁻¹ := by rw [hq]
  calc g * q * g⁻¹ * d * (g * q * g⁻¹)⁻¹ = g * (q * (g⁻¹ * d * g) * q⁻¹) * g⁻¹ := by group
    _ = g * ((g⁻¹ * d * g) * S.z) * g⁻¹ := h2
    _ = d * (g * S.z * g⁻¹) := by group

theorem pow_four_of_mem_Qa (h34a : SmithE34a) [Finite G] [IsSimpleGroup G] (S : Setting G)
    (hw : S.width = 10) (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) {k a y : G}
    (ha : IsConj S.z a) (hy : IsConj S.z y) (haQ : k⁻¹ * a * k ∈ S.QG)
    (hyw : Commute (k * S.z * k⁻¹) y) : (a * y) ^ 4 = 1 := by
  have hyM : k⁻¹ * y * k ∈ S.M := (mem_M_conj_iff S k y).mpr hyw.symm
  have hc : (k⁻¹ * a * k * (k⁻¹ * y * k)) ^ 4 = 1 := by
    by_cases hyQ : k⁻¹ * y * k ∈ S.QG
    · exact S.pow_four_eq_one (S.QG.mul_mem haQ hyQ)
    · have hai := inv_eq_of_isConj S (SmithGraph.isConj_conj ha k)
      have hyi := inv_eq_of_isConj S (SmithGraph.isConj_conj hy k)
      set a' := k⁻¹ * a * k
      set y' := k⁻¹ * y * k
      have hsq : ((y' * a') ^ 2) ^ 2 = 1 := by
        have he : (y' * a') ^ 2 = y' * a' * y'⁻¹ * a'⁻¹ := by
          rw [hai, hyi, sq]
          simp only [mul_assoc]
        rw [he]
        exact sq_eq_one_of_mem_commutator h34a S hw hU (SmithGraph.isConj_conj hy k) hyM hyQ
          (commutator_mem S y' haQ)
      have h4 : (y' * a') ^ 4 = 1 := by rw [← hsq, ← pow_mul]
      have hconj : a' * y' = a' * (y' * a') * a'⁻¹ := by group
      rw [hconj, conj_pow, h4, mul_one, mul_inv_cancel]
  rw [show k⁻¹ * a * k * (k⁻¹ * y * k) = k⁻¹ * (a * y) * k by group, conj_pow_inv] at hc
  calc (a * y) ^ 4 = k * (k⁻¹ * (a * y) ^ 4 * k) * k⁻¹ := by group
    _ = 1 := by rw [hc]; group

end SME

end CFSG.LargeExtraspecial.S14
