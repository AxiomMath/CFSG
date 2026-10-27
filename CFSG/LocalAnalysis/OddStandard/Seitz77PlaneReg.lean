module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Plane

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools Equiv

namespace IsRegularNormal

variable {G : Type} [Group G] [Finite G] {E : Subgroup G} {t : G} {X : Subgroup G}

theorem exists_sylow (hX : IsRegularNormal E t X) (hE : IsPGroup 2 E)
    (hEC : E ≤ centralizer (E : Set G)) :
    ∃ Q : Subgroup G, IsSylowOf 2 Q X ∧ E < Q ∧ Q ⊔ centralizer (E : Set G) = X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer (E : Set G) with hC
  have hCX : C ≤ X := hX.centralizer_le
  have hEX : E ≤ X := hEC.trans hCX
  have hE' : IsPGroup 2 (E.subgroupOf X) := hE.comap_subtype
  obtain ⟨Q₀, hQ₀⟩ := hE'.exists_le_sylow
  set Q : Subgroup G := (Q₀ : Subgroup ↥X).map X.subtype with hQ
  have hQsyl : IsSylowOf 2 Q X := ⟨Q₀, rfl⟩
  have hEQ : E ≤ Q := fun x hx => ⟨⟨x, hEX hx⟩, hQ₀ (mem_subgroupOf.mpr hx), rfl⟩
  have hQX : Q ≤ X := hQsyl.le
  have hCidx : C.relIndex X = 16 := by
    have := hX.relIndex_eq
    rwa [inf_eq_right.mpr hCX] at this
  have hS : Q ⊔ C = X := by
    have hSX : Q ⊔ C ≤ X := sup_le hQX hCX
    have h1 : ¬ 2 ∣ Q.relIndex X := (isSylowOf_iff.mp hQsyl).2.2
    have h2 : (Q ⊔ C).relIndex X ∣ Q.relIndex X :=
      Dvd.intro_left _ (Subgroup.relIndex_mul_relIndex Q (Q ⊔ C) X le_sup_left hSX)
    have h3 : (Q ⊔ C).relIndex X ∣ 2 ^ 4 := by
      have h := Subgroup.relIndex_mul_relIndex C (Q ⊔ C) X le_sup_right hSX
      rw [hCidx] at h
      have h' : (Q ⊔ C).relIndex X ∣ 16 := Dvd.intro_left _ h
      simpa using h'
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h3
    have hi0 : i = 0 := by
      by_contra hne
      exact h1 ((hi ▸ dvd_pow_self 2 hne).trans h2)
    rw [hi0, pow_zero, Subgroup.relIndex_eq_one] at hi
    exact le_antisymm hSX hi
  refine ⟨Q, hQsyl, lt_of_le_of_ne hEQ fun hEQ' => ?_, hS⟩
  have hQC : Q ≤ C := hEQ' ▸ hEC
  rw [sup_eq_right.mpr hQC] at hS
  rw [hS, Subgroup.relIndex_self] at hCidx
  omega

end IsRegularNormal

theorem exists_fixed_of_isPGroup {G : Type*} [Group G] {Q W : Subgroup G} (hQ : IsPGroup 2 Q)
    (hcard : Nat.card W = 16) (hQW : ∀ q ∈ Q, ∀ w ∈ W, q * w * q⁻¹ ∈ W) :
    ∃ w ∈ W, w ≠ 1 ∧ ∀ q ∈ Q, q * w * q⁻¹ = w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite W := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  let _ : MulAction Q W :=
    { smul := fun q w => ⟨(q : G) * w * (q : G)⁻¹, hQW q q.2 w w.2⟩
      one_smul := fun w => Subtype.ext (by
        show ((1 : Q) : G) * (w : G) * ((1 : Q) : G)⁻¹ = (w : G)
        simp)
      mul_smul := fun q₁ q₂ w => Subtype.ext (by
        show ((q₁ * q₂ : Q) : G) * (w : G) * ((q₁ * q₂ : Q) : G)⁻¹ =
          (q₁ : G) * ((q₂ : G) * (w : G) * (q₂ : G)⁻¹) * (q₁ : G)⁻¹
        simp [mul_assoc]) }
  have hsmul : ∀ (q : Q) (w : W), ((q • w : W) : G) = (q : G) * w * (q : G)⁻¹ := fun _ _ => rfl
  have hfix : (1 : W) ∈ MulAction.fixedPoints Q W := by
    rw [MulAction.mem_fixedPoints]
    intro q
    exact Subtype.ext (by rw [hsmul]; simp)
  obtain ⟨b, hb, hne⟩ :=
    hQ.exists_fixed_point_of_prime_dvd_card_of_fixed_point W
      (by rw [hcard]; norm_num) hfix
  rw [MulAction.mem_fixedPoints] at hb
  refine ⟨b, b.2, fun h => hne ?_, fun q hq => ?_⟩
  · exact Subtype.ext h.symm
  · have := congrArg Subtype.val (hb ⟨q, hq⟩)
    rw [hsmul] at this
    exact this

theorem conj_mem_centralizer_of_mem_normalizer {G : Type*} [Group G] {E : Subgroup G} {n : G}
    (hn : n ∈ normalizer (E : Set G)) {c : G} (hc : c ∈ centralizer (E : Set G)) :
    n * c * n⁻¹ ∈ centralizer (E : Set G) := by
  rw [mem_centralizer_iff]
  intro e he
  have h1 : n⁻¹ * e * n ∈ E := by
    refine (mem_normalizer_iff.mp hn (n⁻¹ * e * n)).mpr ?_
    have e' : n * (n⁻¹ * e * n) * n⁻¹ = e := by group
    rw [e']
    exact he
  have h2 := mem_centralizer_iff.mp hc _ h1
  calc e * (n * c * n⁻¹) = n * ((n⁻¹ * e * n) * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * e * n)) * n⁻¹ := by rw [h2]
    _ = n * c * n⁻¹ * e := by group

theorem normalizer_le_normalizer_centralizer' {G : Type*} [Group G] (E : Subgroup G) :
    normalizer (E : Set G) ≤ normalizer (centralizer (E : Set G) : Set G) := fun n hn => by
  rw [mem_normalizer_iff]
  intro c
  refine ⟨conj_mem_centralizer_of_mem_normalizer hn, fun hc => ?_⟩
  have := conj_mem_centralizer_of_mem_normalizer (inv_mem hn) hc
  simpa [mul_assoc] using this

namespace Facts

section Reg

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {V₁ V₂ W : Subgroup G}

theorem E_pgroup (F : Facts A) (d : Datum A) (hR : Radicals d.V V₁ V₂) (hW : W = V₁ ∨ W = V₂) :
    IsPGroup 2 (d.E W) ∧ d.E W ≤ centralizer ((d.E W : Subgroup G) : Set G) := by
  obtain ⟨hEP, hEe, -⟩ := F.adj_properties d hR hW
  exact ⟨d.hP.isPGroup.to_le hEP, fun x hx => mem_centralizer_iff.mpr fun y hy =>
    L34.comm_of_isElemAbelian hEe hy hx⟩

theorem regularNormal_le_centralizer (F : Facts A) (d : Datum A) (hR : Radicals d.V V₁ V₂)
    (hα : d.Alpha) (hW : W = V₁ ∨ W = V₂) (AS : ASide A d.V W) {X : Subgroup G}
    (hX : IsRegularNormal (d.E W : Subgroup G) d.t X) : ∀ x ∈ X, ∀ w ∈ W, x * w * x⁻¹ = w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hW16⟩ := hR.property hW
  obtain ⟨hE2, hEC⟩ := F.E_pgroup d hR hW
  obtain ⟨Q, hQsyl, -, hQC⟩ := hX.exists_sylow hE2 hEC
  have hXW : ∀ x ∈ X, x ∈ normalizer (W : Set G) := fun x hx =>
    F.normalizer_adj_le d hR hα hW (hX.le_normalizer hx)
  obtain ⟨w₀, hw₀, hw₀1, hw₀Q⟩ := exists_fixed_of_isPGroup hQsyl.isPGroup hW16
    (fun q hq w hw => (mem_normalizer_iff.mp (hXW q (hQsyl.le hq)) w).mp hw)
  have hCW : ∀ c ∈ centralizer ((d.E W : Subgroup G) : Set G), ∀ w ∈ W, c * w * c⁻¹ = w :=
    fun c hc w hw => by
      have := mem_centralizer_iff.mp hc w (mem_sup_left hw)
      rw [mul_inv_eq_iff_eq_mul]
      exact this.symm
  have hw₀X : ∀ x ∈ X, x * w₀ * x⁻¹ = w₀ := by
    intro x hx
    have hQN : Q ≤ normalizer (centralizer ((d.E W : Subgroup G) : Set G) : Set G) :=
      fun q hq => normalizer_le_normalizer_centralizer' _ (hX.le_normalizer (hQsyl.le hq))
    rw [← hQC, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hQN,
      Set.mem_mul] at hx
    obtain ⟨q, hq, c, hc, rfl⟩ := hx
    calc q * c * w₀ * (q * c)⁻¹ = q * (c * w₀ * c⁻¹) * q⁻¹ := by group
      _ = w₀ := by rw [hCW c hc w₀ hw₀, hw₀Q q hq]
  intro x hx w hw
  by_cases hw1 : w = 1
  · rw [hw1]
    group
  obtain ⟨a, haM, haw⟩ := AS.trans w₀ hw₀ w hw hw₀1 hw1
  have haE := d.mem_normalizer_E_of_mem_A hR hW haM
  have hax : a⁻¹ * x * a⁻¹⁻¹ ∈ X :=
    (mem_normalizer_iff.mp (hX.normalizer_le (inv_mem haE)) x).mp hx
  calc x * w * x⁻¹ = x * (a * w₀ * a⁻¹) * x⁻¹ := by rw [haw]
    _ = a * ((a⁻¹ * x * a⁻¹⁻¹) * w₀ * (a⁻¹ * x * a⁻¹⁻¹)⁻¹) * a⁻¹ := by group
    _ = w := by rw [hw₀X _ hax, ← haw]

end Reg

end Facts

end CFSG.OddStandard.Seitz77
