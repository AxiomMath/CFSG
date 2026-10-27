module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.SelfSplitY

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup
open scoped commutatorElement Pointwise

private theorem card_sup_mul_card_inf_of_le_centralizer {X : Type*} [Group X]
    {A B : Subgroup X} (h : A ≤ Subgroup.centralizer (B : Set X)) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card A * Nat.card B := by
  have hn : ∀ x ∈ A, ∀ n ∈ B, x * n * x⁻¹ ∈ B := by
    intro x hx n hn
    have hc : n * x = x * n := Subgroup.mem_centralizer_iff.mp (h hx) n hn
    rw [← hc, mul_assoc, mul_inv_cancel, mul_one]
    exact hn
  have hA : A ≤ Subgroup.normalizer (B : Set X) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    exact ⟨fun hh => hn x hx h hh, fun hh => by
      have hh' := hn x⁻¹ (A.inv_mem hx) (x * h * x⁻¹) hh
      simpa [mul_assoc] using hh'⟩
  haveI : (B.subgroupOf (A ⊔ B)).Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hA
  have h1 := Subgroup.relIndex_sup_right (A.subgroupOf (A ⊔ B)) (B.subgroupOf (A ⊔ B))
  rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self,
    Subgroup.relIndex_top_right, Subgroup.relIndex_subgroupOf le_sup_left] at h1
  have h2 := Subgroup.relIndex_mul_card (H := B) (K := A ⊔ B)
  have h3 := Subgroup.relIndex_mul_card (H := B) (K := A)
  have h4 : B ⊓ (A ⊔ B) = B := inf_eq_left.mpr le_sup_right
  rw [h4] at h2
  have h5 : B.relIndex (A ⊔ B) = B.relIndex A := by rw [← h1]; rfl
  rw [h5] at h2
  rw [inf_comm A B, mul_comm (Nat.card A) (Nat.card B), ← h2, ← h3]
  ring

theorem exists_sylow_split {X : Type} [Group X] [Finite X] {a b : X} {E Y : Subgroup X}
    (hcomm : ⁅E, Y⁆ = ⊥) (hsup : E ⊔ Y = ⊤) (hint : E ⊓ Y = zpowers b)
    (hb2 : b * b = 1) (hb1 : b ≠ 1)
    (haY : a ∈ Y) (ha2 : a * a = 1) (ha1 : a ≠ 1) (haE : a ∉ E)
    (hcent : ∀ y ∈ Y, y * a = a * y → y = 1 ∨ y = a ∨ y = b ∨ y = a * b)
    (hEcard : ∃ m, Odd m ∧ Nat.card E = 2 ^ 10 * m) (h12 : 2 ^ 12 ∣ Nat.card X) :
    ∃ (S : Sylow 2 X) (U A : Subgroup X), a ∈ (S : Subgroup X) ∧ U ≤ (S : Subgroup X) ∧
      U.relIndex (S : Subgroup X) = 2 ∧ a ∉ U ∧ IsCyclic ↥A ∧ b ∈ A ∧ U ⊓ Y ≤ A ∧
      ∀ P : Subgroup X, P ≤ Y → IsPGroup 2 P →
        ∃ M : Subgroup X, M ≤ P ∧ IsCyclic ↥M ∧ M.relIndex P ≤ 2 := by
  classical
  obtain ⟨m, hm_odd, hEm⟩ := hEcard
  have hb_inf : b ∈ E ⊓ Y := by rw [hint]; exact Subgroup.mem_zpowers b
  have hbE : b ∈ E := hb_inf.1
  have hbY : b ∈ Y := hb_inf.2
  have hEY : E ≤ Subgroup.centralizer (Y : Set X) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcomm
  have hYE : Y ≤ Subgroup.centralizer (E : Set X) := by
    apply (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := Y) (H₂ := E)).mp
    rw [Subgroup.commutator_comm]
    exact hcomm
  have hb_comm : ∀ y ∈ Y, y * b = b * y := fun y hy =>
    (Subgroup.mem_centralizer_iff.mp (hEY hbE)) y hy
  have hab : a ≠ b := fun h => haE (h ▸ hbE)
  have hbord : orderOf b = 2 :=
    orderOf_eq_prime (p := 2) (by rw [pow_two]; exact hb2) hb1
  have hcardEY : Nat.card X * 2 = Nat.card E * Nat.card Y := by
    have h := card_sup_mul_card_inf_of_le_centralizer hEY
    rw [hsup, Subgroup.card_top, hint, Nat.card_zpowers, hbord] at h
    exact h
  have hm_ne : m ≠ 0 := by obtain ⟨j, hj⟩ := hm_odd; omega
  have h2m : ¬ 2 ∣ m := by
    rintro ⟨k, hk⟩
    obtain ⟨j, hj⟩ := hm_odd
    omega
  have h8 : 2 ^ 3 ∣ Nat.card Y := by
    have hdvd : (2 : ℕ) ^ 13 ∣ 2 ^ 10 * (m * Nat.card Y) := by
      have h1 : (2 : ℕ) ^ 12 * 2 ∣ Nat.card X * 2 := mul_dvd_mul_right h12 2
      have h2 : Nat.card X * 2 = 2 ^ 10 * (m * Nat.card Y) := by
        rw [hcardEY, hEm]; ring
      rwa [h2, show (2 : ℕ) ^ 12 * 2 = 2 ^ 13 by norm_num] at h1
    have h3 : (2 : ℕ) ^ 3 ∣ m * Nat.card Y := by
      have h13 : (2 : ℕ) ^ 13 = 2 ^ 10 * 2 ^ 3 := by norm_num
      rw [h13] at hdvd
      exact (mul_dvd_mul_iff_left (by positivity : (2 : ℕ) ^ 10 ≠ 0)).mp hdvd
    exact (hm_odd.coprime_two_left.pow_left 3).dvd_of_dvd_mul_left h3
  let aY : ↥Y := ⟨a, haY⟩
  let bY : ↥Y := ⟨b, hbY⟩
  have hbY2 : bY * bY = 1 := Subtype.ext (by simpa using hb2)
  have hbY1 : bY ≠ 1 := fun h => hb1 (congrArg (fun z : ↥Y => (z : X)) h)
  have hbcY : ∀ y : ↥Y, y * bY = bY * y := fun y => Subtype.ext (hb_comm (y : X) y.2)
  have haY2 : aY * aY = 1 := Subtype.ext (by simpa using ha2)
  have haY1 : aY ≠ 1 := fun h => ha1 (congrArg (fun z : ↥Y => (z : X)) h)
  have habY : aY ≠ bY := by
    intro h
    have h' : a = b := congrArg (fun z : ↥Y => (z : X)) h
    exact haE (h'.symm ▸ hbE)
  have hbYord : orderOf bY = 2 :=
    orderOf_eq_prime (p := 2) (by rw [pow_two]; exact hbY2) hbY1
  have hcentY : ∀ y : ↥Y, y * aY = aY * y →
      y = 1 ∨ y = aY ∨ y = bY ∨ y = aY * bY := by
    intro y hy
    have hy' : (y : X) * a = a * (y : X) := by
      have := congrArg (fun z : ↥Y => (z : X)) hy
      simpa using this
    rcases hcent (y : X) y.2 hy' with h1 | ha' | hb' | hab'
    · exact Or.inl (Subtype.ext h1)
    · exact Or.inr (Or.inl (Subtype.ext ha'))
    · exact Or.inr (Or.inr (Or.inl (Subtype.ext hb')))
    · refine Or.inr (Or.inr (Or.inr ?_))
      apply Subtype.ext
      rw [Subgroup.coe_mul]
      exact hab'
  obtain ⟨Q, A₀, haQ, hbQ, hA0Q, hcycA0, hrelA0, haA0, hbA0⟩ :=
    exists_sylow_cyclic_index_two (Y := ↥Y) (a := aY) (b := bY)
      hbY2 hbY1 hbcY haY2 haY1 habY hcentY h8
  let TY : Subgroup X := (Q : Subgroup ↥Y).map Y.subtype
  let A : Subgroup X := A₀.map Y.subtype
  have hTY_le : TY ≤ Y := by rintro x ⟨y, -, rfl⟩; exact y.2
  have hA_le_TY : A ≤ TY := by rintro x ⟨y, hy, rfl⟩; exact ⟨y, hA0Q hy, rfl⟩
  have haTY : a ∈ TY := ⟨aY, haQ, rfl⟩
  have hbTY : b ∈ TY := ⟨bY, hbQ, rfl⟩
  have haA : a ∉ A := by
    rintro ⟨z, hz, hza⟩
    have hz_eq : z = aY := Subtype.ext hza
    exact haA0 (hz_eq ▸ hz)
  have hbA : b ∈ A := ⟨bY, hbA0, rfl⟩
  have hcycA : IsCyclic ↥A :=
    (Subgroup.equivMapOfInjective A₀ Y.subtype Y.subtype_injective).isCyclic.mp hcycA0
  have hrelA_TY : A.relIndex TY = 2 := by
    have h := Subgroup.relIndex_map_map_of_injective A₀ (Q : Subgroup ↥Y) Y.subtype_injective
    exact h.trans hrelA0
  let bE : ↥E := ⟨b, hbE⟩
  have hbE2 : bE ^ 2 = 1 := by rw [pow_two]; exact Subtype.ext (by simpa using hb2)
  have hbE1 : bE ≠ 1 := fun h => hb1 (congrArg (fun w : ↥E => (w : X)) h)
  have hbE_pgroup : IsPGroup 2 (Subgroup.zpowers bE) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, orderOf_eq_prime (p := 2) hbE2 hbE1]
      norm_num)
  obtain ⟨TE, hTE_cont⟩ := IsPGroup.exists_le_sylow hbE_pgroup
  let TE' : Subgroup X := (TE : Subgroup ↥E).map E.subtype
  have hTE'_le_E : TE' ≤ E := by rintro x ⟨y, -, rfl⟩; exact y.2
  have hbTE' : b ∈ TE' := ⟨bE, hTE_cont (Subgroup.mem_zpowers bE), rfl⟩
  have hTE'_pgroup : IsPGroup 2 TE' := IsPGroup.map TE.isPGroup' E.subtype
  have hTY_pgroup : IsPGroup 2 TY := IsPGroup.map Q.isPGroup' Y.subtype
  have hfact : Nat.factorization (Nat.card ↥E) 2 = 10 := by
    rw [hEm, Nat.factorization_mul (by positivity) hm_ne, Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd h2m,
      add_zero]
  have hcardTE : Nat.card TE = 2 ^ 10 := by
    rw [Sylow.card_eq_multiplicity, hfact]
  have hcardTE' : Nat.card TE' = 2 ^ 10 := by
    rw [← hcardTE]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective (TE : Subgroup ↥E) E.subtype
      E.subtype_injective).toEquiv).symm
  have hTE'_inf_TY : TE' ⊓ TY = Subgroup.zpowers b := by
    refine le_antisymm ?_ (Subgroup.zpowers_le.mpr ⟨hbTE', hbTY⟩)
    exact (inf_le_inf hTE'_le_E hTY_le).trans (le_of_eq hint)
  have hTE'_inf_A : TE' ⊓ A = Subgroup.zpowers b := by
    refine le_antisymm ?_ (Subgroup.zpowers_le.mpr ⟨hbTE', hbA⟩)
    exact (inf_le_inf hTE'_le_E (hA_le_TY.trans hTY_le)).trans (le_of_eq hint)
  let S₀ : Subgroup X := TE' ⊔ TY
  let U : Subgroup X := TE' ⊔ A
  have hTE'_cent_TY : TE' ≤ Subgroup.centralizer (TY : Set X) :=
    (hTE'_le_E.trans hEY).trans (Subgroup.centralizer_le hTY_le)
  have hTE'_cent_A : TE' ≤ Subgroup.centralizer (A : Set X) :=
    (hTE'_le_E.trans hEY).trans (Subgroup.centralizer_le (hA_le_TY.trans hTY_le))
  have hTE'_le_norm_A : TE' ≤ Subgroup.normalizer (A : Set X) :=
    hTE'_cent_A.trans (Subgroup.centralizer_le_normalizer _)
  have hS0_pgroup : IsPGroup 2 S₀ :=
    IsPGroup.to_sup_of_normal_right' hTE'_pgroup hTY_pgroup
      (hTE'_cent_TY.trans (Subgroup.centralizer_le_normalizer _))
  have hUS : U ≤ S₀ := sup_le_sup le_rfl hA_le_TY
  have hcardS0 : Nat.card S₀ * 2 = 2 ^ 10 * Nat.card TY := by
    have h := card_sup_mul_card_inf_of_le_centralizer hTE'_cent_TY
    rw [hTE'_inf_TY, Nat.card_zpowers, hbord] at h
    rw [hcardTE'] at h
    exact h
  have hcardU : Nat.card U * 2 = 2 ^ 10 * Nat.card A := by
    have h := card_sup_mul_card_inf_of_le_centralizer hTE'_cent_A
    rw [hTE'_inf_A, Nat.card_zpowers, hbord] at h
    rw [hcardTE'] at h
    exact h
  have hq_odd : ¬ 2 ∣ (Q : Subgroup ↥Y).index := Q.not_dvd_index
  have hYcard : Nat.card ↥Y = Nat.card TY * (Q : Subgroup ↥Y).index := by
    rw [← Subgroup.card_mul_index (H := (Q : Subgroup ↥Y))]
    congr 1
    exact Nat.card_congr (Subgroup.equivMapOfInjective (Q : Subgroup ↥Y) Y.subtype
      Y.subtype_injective).toEquiv
  have hXcard : Nat.card X = Nat.card S₀ * (m * (Q : Subgroup ↥Y).index) := by
    have h2 : Nat.card X * 2 = (Nat.card S₀ * (m * (Q : Subgroup ↥Y).index)) * 2 := by
      calc Nat.card X * 2 = Nat.card E * Nat.card Y := hcardEY
        _ = (2 ^ 10 * m) * (Nat.card TY * (Q : Subgroup ↥Y).index) := by rw [hEm, hYcard]
        _ = (2 ^ 10 * Nat.card TY) * (m * (Q : Subgroup ↥Y).index) := by ring
        _ = (Nat.card S₀ * 2) * (m * (Q : Subgroup ↥Y).index) := by rw [← hcardS0]
        _ = (Nat.card S₀ * (m * (Q : Subgroup ↥Y).index)) * 2 := by ring
    exact mul_right_cancel₀ (by norm_num : (2 : ℕ) ≠ 0) h2
  have hS0pos : 0 < Nat.card S₀ :=
    Nat.card_pos_iff.mpr ⟨⟨⟨1, S₀.one_mem⟩⟩, inferInstance⟩
  have hS0_index : S₀.index = m * (Q : Subgroup ↥Y).index := by
    refine mul_left_cancel₀ hS0pos.ne' ?_
    rw [Subgroup.card_mul_index (H := S₀), hXcard]
  have hS0_index_odd : ¬ 2 ∣ S₀.index := by
    rw [hS0_index]
    exact Nat.prime_two.not_dvd_mul h2m hq_odd
  let S : Sylow 2 X := hS0_pgroup.toSylow hS0_index_odd
  have hrelU : U.relIndex S₀ * Nat.card U = Nat.card S₀ := by
    have h := Subgroup.relIndex_mul_card (H := U) (K := S₀)
    rwa [inf_of_le_left hUS] at h
  have hrelTY : A.relIndex TY * Nat.card A = Nat.card TY := by
    have h := Subgroup.relIndex_mul_card (H := A) (K := TY)
    rwa [inf_of_le_left hA_le_TY] at h
  have hTYcard : Nat.card TY = 2 * Nat.card A := by rw [← hrelTY, hrelA_TY]
  have hS0U : Nat.card S₀ = 2 * Nat.card U := by
    have h4 : Nat.card S₀ * 2 = (2 * Nat.card U) * 2 := by
      calc Nat.card S₀ * 2 = 2 ^ 10 * Nat.card TY := hcardS0
        _ = 2 ^ 10 * (2 * Nat.card A) := by rw [hTYcard]
        _ = 2 * (2 ^ 10 * Nat.card A) := by ring
        _ = 2 * (Nat.card U * 2) := by rw [← hcardU]
        _ = (2 * Nat.card U) * 2 := by ring
    exact mul_right_cancel₀ (by norm_num : (2 : ℕ) ≠ 0) h4
  have hUpos : 0 < Nat.card U :=
    Nat.card_pos_iff.mpr ⟨⟨⟨1, U.one_mem⟩⟩, inferInstance⟩
  have hrelUS : U.relIndex S₀ = 2 := by
    have h := hrelU
    rw [hS0U] at h
    exact mul_right_cancel₀ hUpos.ne' h
  have hUY_le_A : U ⊓ Y ≤ A := by
    intro x hx
    obtain ⟨hxU, hxY⟩ := hx
    have hx' : x ∈ (TE' : Set X) * (A : Set X) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right TE' A hTE'_le_norm_A]
      exact hxU
    obtain ⟨t, ht, α, hα, htα⟩ := hx'
    have hαY : α ∈ Y := hA_le_TY.trans hTY_le hα
    have htY : t ∈ Y := by
      have ht_eq : t = x * α⁻¹ := by rw [← htα]; group
      rw [ht_eq]
      exact Y.mul_mem hxY (Y.inv_mem hαY)
    have htA : t ∈ A := Subgroup.zpowers_le.mpr hbA (by
      have : t ∈ E ⊓ Y := ⟨hTE'_le_E ht, htY⟩
      rwa [hint] at this)
    rw [← htα]
    exact A.mul_mem htA hα
  have haU : a ∉ U := by
    intro ha
    have ha' : a ∈ (TE' : Set X) * (A : Set X) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right TE' A hTE'_le_norm_A]
      exact ha
    obtain ⟨t, ht, α, hα, htα⟩ := ha'
    have hαY : α ∈ Y := hA_le_TY.trans hTY_le hα
    have htY : t ∈ Y := by
      have ht_eq : t = a * α⁻¹ := by rw [← htα]; group
      rw [ht_eq]
      exact Y.mul_mem haY (Y.inv_mem hαY)
    have htA : t ∈ A := Subgroup.zpowers_le.mpr hbA (by
      have : t ∈ E ⊓ Y := ⟨hTE'_le_E ht, htY⟩
      rwa [hint] at this)
    exact haA (by rw [← htα]; exact A.mul_mem htA hα)
  refine ⟨S, U, A, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change a ∈ S₀
    exact (le_sup_right : TY ≤ TE' ⊔ TY) haTY
  · change U ≤ S₀
    exact hUS
  · change U.relIndex S₀ = 2
    exact hrelUS
  · exact haU
  · exact hcycA
  · exact hbA
  · exact hUY_le_A
  · intro P hPY hP
    let P' : Subgroup ↥Y := P.subgroupOf Y
    have hP' : IsPGroup 2 P' := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPY).symm
    obtain ⟨M', hM'P', hcycM', hrelM'⟩ :=
      exists_cyclic_relIndex_le_two (Y := ↥Y) (a := aY) (b := bY)
        hbY2 hbY1 hbcY haY2 haY1 habY hcentY h8 P' hP'
    refine ⟨M'.map Y.subtype, ?_, ?_, ?_⟩
    · have h := Subgroup.map_mono (f := Y.subtype) hM'P'
      rwa [Subgroup.map_subgroupOf_eq_of_le hPY] at h
    · exact (Subgroup.equivMapOfInjective M' Y.subtype Y.subtype_injective).isCyclic.mp hcycM'
    · have h : (M'.map Y.subtype).relIndex P = M'.relIndex P' := by
        rw [← Subgroup.map_subgroupOf_eq_of_le hPY]
        exact Subgroup.relIndex_map_map_of_injective M' P' Y.subtype_injective
      rw [h]
      exact hrelM'

end CFSG.EvenSporadicStandard.Co3Std.CentT
