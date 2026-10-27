module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Reduction

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {SL : Subgroup G}

theorem ThCyc.exists_fusing_element (H : ThCyc G L R t) (hS : IsThSylow L SL) :
    ∃ (P : Sylow 2 G) (x : G), SL ⊔ R ≤ (P : Subgroup G) ∧ x ∈ (P : Subgroup G) ∧
      x ∈ normalizer ((SL ⊔ R : Subgroup G) : Set G) ∧ x ∉ SL ⊔ R ∧
      ∃ e ∈ SL, e ≠ 1 ∧ (∀ y ∈ SL, e * y = y * e) ∧ x * t * x⁻¹ = e * t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRSL := H.le_centralizer_sylow hS
  have hSP := H.pgroup_sup hS
  obtain ⟨P, hSP'⟩ := hSP.exists_le_sylow
  have hne : (SL ⊔ R : Subgroup G) ≠ P := fun h => H.not_sylow hS ⟨P, h.symm⟩
  set S := SL ⊔ R with hSdef
  have hex : ∃ x ∈ (P : Subgroup G), x ∈ normalizer (S : Set G) ∧ x ∉ S := by
    by_contra hcon
    push Not at hcon
    exact hne (eq_of_inf_normalizer_le P.isPGroup' hSP' fun x hx hn => hcon x hx hn)
  obtain ⟨x, hxP, hxn, hxS⟩ := hex
  have hx1 : ∀ s, s ∈ S ↔ x * s * x⁻¹ ∈ S := mem_normalizer_iff.1 hxn
  have hxinv : ∀ s ∈ S, x⁻¹ * s * x ∈ S := fun s hs => (hx1 _).2 (by simpa [mul_assoc] using hs)
  have hcommSL : ∀ r ∈ R, ∀ a ∈ SL, r * a = a * r := fun r hr a ha =>
    (mem_centralizer_iff.1 (hRSL hr) a ha).symm
  have htS : t ∈ S := mem_sup_right H.mem
  have htZ : ∀ s ∈ S, t * s = s * t := by
    intro s hs
    obtain ⟨a, ha, r, hr, rfl⟩ := H.exists_mul_of_mem_sylow_sup hS hs
    calc t * (a * r) = (t * a) * r := by rw [mul_assoc]
      _ = (a * t) * r := by rw [hcommSL t H.mem a ha]
      _ = a * (t * r) := by rw [mul_assoc]
      _ = a * (r * t) := by rw [H.mul_comm_of_mem t H.mem r hr]
      _ = (a * r) * t := by rw [mul_assoc]
  have hxt : x * t * x⁻¹ ≠ t := by
    intro heq
    have hxC : x ∈ centralizer ({t} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc x * t = (x * t * x⁻¹) * x := by group
        _ = t * x := by rw [heq]
    have hX : IsPGroup 2 ↥(S ⊔ zpowers x) :=
      P.isPGroup'.to_le (sup_le hSP' (zpowers_le.2 hxP))
    exact hxS (H.sup_max hS (sup_le (H.sup_le_centralizer hS) (zpowers_le.2 hxC)) hX le_sup_left
      (Subgroup.mem_sup_right (mem_zpowers x)))
  obtain ⟨u, hu⟩ : ∃ u : G, u = x * t * x⁻¹ := ⟨_, rfl⟩
  have hxt' : u ≠ t := by rw [hu]; exact hxt
  have huS : u ∈ S := by rw [hu]; exact (hx1 t).1 htS
  have huZ : ∀ s ∈ S, u * s = s * u := by
    intro s hs
    have h1 := htZ _ (hxinv s hs)
    calc u * s = x * (t * (x⁻¹ * s * x)) * x⁻¹ := by rw [hu]; group
      _ = x * ((x⁻¹ * s * x) * t) * x⁻¹ := by rw [h1]
      _ = s * u := by rw [hu]; group
  have hu2 : orderOf u = 2 := by
    have := orderOf_injective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective t
    simpa [hu] using this.trans H.order_two
  obtain ⟨a, ha, r, hr, huar⟩ := H.exists_mul_of_mem_sylow_sup hS huS
  have haZ : ∀ y ∈ SL, a * y = y * a := by
    intro y hy
    have hyS : y ∈ S := Subgroup.mem_sup_left hy
    have h1 := huZ y hyS
    have ha' : a = u * r⁻¹ := by rw [huar]; group
    have hr'y : r⁻¹ * y = y * r⁻¹ := hcommSL _ (R.inv_mem hr) y hy
    calc a * y = u * (r⁻¹ * y) := by rw [ha']; group
      _ = u * (y * r⁻¹) := by rw [hr'y]
      _ = (u * y) * r⁻¹ := by rw [mul_assoc]
      _ = (y * u) * r⁻¹ := by rw [h1]
      _ = y * (u * r⁻¹) := by rw [mul_assoc]
      _ = y * a := by rw [ha']
  have ha2 : a ^ 2 = 1 := hS.center a ha haZ
  have hr2 : r ^ 2 = 1 := by
    have hcomm : a * r = r * a := (hcommSL r hr a ha).symm
    have hu2' : u ^ 2 = 1 := by rw [← hu2]; exact pow_orderOf_eq_one u
    have : u ^ 2 = r ^ 2 := by
      calc u ^ 2 = (a * r) * (a * r) := by rw [huar, sq]
        _ = a * (r * a) * r := by group
        _ = a * (a * r) * r := by rw [← hcomm]
        _ = a ^ 2 * r ^ 2 := by simp only [sq, mul_assoc]
        _ = r ^ 2 := by rw [ha2, one_mul]
    rw [← this]; exact hu2'
  have hrt : r = 1 ∨ r = t := by
    by_cases hr1 : r = 1
    · exact Or.inl hr1
    · right
      have := H.cyclic
      have hro : orderOf (⟨r, hr⟩ : R) = 2 := by
        rw [Subgroup.orderOf_mk]
        exact orderOf_eq_prime (by simpa [sq] using hr2) hr1
      have hto : orderOf (⟨t, H.mem⟩ : R) = 2 := by rw [Subgroup.orderOf_mk]; exact H.order_two
      exact congrArg Subtype.val (eq_of_orderOf_eq_two_of_isCyclic hro hto)
  rcases hrt with rfl | hrt
  · exfalso
    rw [mul_one] at huar
    have haL : u ∈ L := by rw [huar]; exact hS.le ha
    have := H.not_conj_mem x⁻¹
    rw [inv_inv, ← hu] at this
    exact this haL
  · refine ⟨P, x, hSP', hxP, hxn, hxS, a, ha, ?_, haZ, ?_⟩
    · rintro rfl
      apply hxt'
      rw [huar, hrt, one_mul]
    · rw [← hu, huar, hrt]

end CFSG.EvenSporadicStandard.ThStd
