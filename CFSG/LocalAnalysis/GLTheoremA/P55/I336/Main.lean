module

public import CFSG.LocalAnalysis.GLTheoremA.P55.I336.Q8
public import CFSG.LocalAnalysis.GLTheoremA.P55.I336.Ortho
public import CFSG.LocalAnalysis.GLTheoremA.P55.I336.Symp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.P55.I336

open CFSG.Open
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

section Hyperplanes

theorem normalizer_inf_centralizer {p : ℕ} {T D D₀ : Subgroup G} (hD : IsElemAbelian p D)
    (hDT : D ≤ Subgroup.normalizer (T : Set G)) (hD₀ : D₀ ≤ D) :
    D ≤ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (D₀ : Set G) : Subgroup G) : Set G) := by
  refine le_normalizer_of_forall_mem fun d hd x hx => ?_
  obtain ⟨hxT, hxc⟩ := hx
  refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hDT hd) x).mp hxT, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have had : a * d = d * a := CFSG.Open.IsElemAbelian.comm hD (hD₀ ha) hd
  have hxa : a * x = x * a := Subgroup.mem_centralizer_iff.mp hxc a ha
  exact mul_conj_comm had hxa

theorem exists_hyperplane_comm_ne_bot {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {T D : Subgroup G}
    (hT : IsPGroup 2 T) (hD : IsElemAbelian p D) (hDne : D ≠ ⊥)
    (hDT : D ≤ Subgroup.normalizer (T : Set G)) (hTD : (⁅T, D⁆ : Subgroup G) ≠ ⊥) :
    ∃ D₀ : Subgroup G, D₀ ≤ D ∧ Nat.card D₀ * p = Nat.card D ∧
      (⁅T ⊓ Subgroup.centralizer (D₀ : Set G), D⁆ : Subgroup G) ≠ ⊥ := by
  by_contra hcon
  push Not at hcon
  apply hTD
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  refine (GL83.le_iSup_hyperplane hp hp2 hDne hD hT hDT).trans (iSup₂_le fun A hA => ?_)
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (hcon A hA.1 (card_mul_eq_of_index_eq hA.1 hA.2))

theorem exists_second_hyperplane {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {T D D₀ : Subgroup G}
    (hT : IsPGroup 2 T) (hD : IsElemAbelian p D) (hDne : D ≠ ⊥)
    (hDT : D ≤ Subgroup.normalizer (T : Set G))
    (hTc : ¬ T ≤ Subgroup.centralizer (D₀ : Set G)) :
    ∃ D₁ : Subgroup G, D₁ ≤ D ∧ Nat.card D₁ * p = Nat.card D ∧
      ¬ (T ⊓ Subgroup.centralizer (D₁ : Set G) ≤ Subgroup.centralizer (D₀ : Set G)) := by
  by_contra hcon
  push Not at hcon
  apply hTc
  refine (GL83.le_iSup_hyperplane hp hp2 hDne hD hT hDT).trans (iSup₂_le fun A hA => ?_)
  exact hcon A hA.1 (card_mul_eq_of_index_eq hA.1 hA.2)

theorem card_inf_hyperplanes {p : ℕ} (hp : p.Prime) {D D₀ D₁ : Subgroup G}
    (hD : IsElemAbelian p D) (h₀ : D₀ ≤ D) (h₁ : D₁ ≤ D) (c₀ : Nat.card D₀ * p = Nat.card D)
    (c₁ : Nat.card D₁ * p = Nat.card D) (hne : D₀ ≠ D₁) :
    D₀ ⊔ D₁ = D ∧ Nat.card ↥(D₀ ⊓ D₁) * p ^ 2 = Nat.card D := by
  have hpos₀ : 0 < Nat.card D₀ := Nat.card_pos
  have hposD : 0 < Nat.card D := Nat.card_pos
  have hcard : Nat.card D₁ = Nat.card D₀ := by
    apply Nat.eq_of_mul_eq_mul_right hp.pos
    rw [c₀, c₁]
  have hnle : ¬ D₁ ≤ D₀ := fun h =>
    hne (Subgroup.eq_of_le_of_card_ge h (by rw [hcard])).symm
  have hsupD : D₀ ⊔ D₁ ≤ D := sup_le h₀ h₁
  have hd1 : Nat.card D₀ ∣ Nat.card ↥(D₀ ⊔ D₁) := Subgroup.card_dvd_of_le le_sup_left
  have hd2 : Nat.card ↥(D₀ ⊔ D₁) ∣ Nat.card D := Subgroup.card_dvd_of_le hsupD
  obtain ⟨k, hk⟩ := hd1
  have hkp : k ∣ p := by
    have : Nat.card D₀ * k ∣ Nat.card D₀ * p := by rw [c₀, ← hk]; exact hd2
    exact Nat.dvd_of_mul_dvd_mul_left hpos₀ this
  have hsup : D₀ ⊔ D₁ = D := by
    rcases (Nat.dvd_prime hp).1 hkp with h | h
    · exfalso
      rw [h, mul_one] at hk
      have : D₀ ⊔ D₁ = D₀ :=
        (Subgroup.eq_of_le_of_card_ge (le_sup_left : D₀ ≤ D₀ ⊔ D₁) (by rw [hk])).symm
      exact hnle (this ▸ le_sup_right)
    · rw [h, c₀] at hk
      exact Subgroup.eq_of_le_of_card_ge hsupD (by rw [hk])
  refine ⟨hsup, ?_⟩
  have hD₁ : D₁ ≤ Subgroup.normalizer (D₀ : Set G) := by
    refine le_normalizer_of_forall_mem fun b hb a ha => ?_
    have := CFSG.Open.IsElemAbelian.comm hD (h₁ hb) (h₀ ha)
    rw [this, mul_inv_cancel_right]
    exact ha
  have hform := CFSG.LocalAnalysis.GLTheoremA.card_sup_mul_card_inf_of_le_normalizer hD₁
  rw [hsup] at hform
  apply Nat.eq_of_mul_eq_mul_left hposD
  calc Nat.card D * (Nat.card ↥(D₀ ⊓ D₁) * p ^ 2)
      = (Nat.card D * Nat.card ↥(D₀ ⊓ D₁)) * p ^ 2 := by ring
    _ = (Nat.card D₀ * Nat.card D₁) * p ^ 2 := by rw [hform]
    _ = (Nat.card D₀ * p) * (Nat.card D₁ * p) := by ring
    _ = Nat.card D * Nat.card D := by rw [c₀, c₁]

end Hyperplanes

section Q8

theorem q8_data_of_hyperplane {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {T D D₀ : Subgroup G}
    (hT : IsPGroup 2 T) (hD : IsElemAbelian p D) (hDT : D ≤ Subgroup.normalizer (T : Set G))
    (hD₀ : D₀ ≤ D) (hQ : (⁅T ⊓ Subgroup.centralizer (D₀ : Set G), D⁆ : Subgroup G) ≠ ⊥)
    (e : ↥(T ⊓ Subgroup.centralizer (D₀ : Set G)) ≃* QuaternionGroup 2) :
    ∃ i j z : G, i ∈ T ⊓ Subgroup.centralizer (D₀ : Set G) ∧
      j ∈ T ⊓ Subgroup.centralizer (D₀ : Set G) ∧ z ∈ T ∧ orderOf z = 2 ∧ i ^ 2 = z ∧
      j ^ 2 = z ∧ i * j = z * (j * i) ∧
      T ⊓ Subgroup.centralizer (D : Set G) = Subgroup.zpowers z := by
  set Y : Subgroup G := T ⊓ Subgroup.centralizer (D₀ : Set G) with hY
  obtain ⟨i, j, z, hiY, hjY, hzY, hz, hi, hj, hij, huniq⟩ := exists_q8_data e
  have hY2 : IsPGroup 2 Y := hT.to_le inf_le_left
  have hY8 : Nat.card Y = 8 := card_eq_eight_of_q8 e
  have hDY : D ≤ Subgroup.normalizer (Y : Set G) := normalizer_inf_centralizer hD hDT hD₀
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hzD : z ∈ Subgroup.centralizer (D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have h1 : d * z * d⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hDY hd) z).mp hzY
    have h2 : (d * z * d⁻¹) ^ 2 = 1 := by
      have : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
      calc (d * z * d⁻¹) ^ 2 = d * z ^ 2 * d⁻¹ := by rw [pow_two, pow_two]; group
        _ = 1 := by rw [this]; group
    rcases huniq _ h1 h2 with h | h
    · exfalso
      apply hz1
      have : z = d⁻¹ * (d * z * d⁻¹) * d := by group
      rw [this, h]
      group
    · calc d * z = d * z * d⁻¹ * d := by group
        _ = z * d := by rw [h]
  have hYD : ¬ Y ≤ Subgroup.centralizer (D : Set G) := fun h =>
    hQ (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h)
  have h1 := inf_centralizer_eq_zpowers hp hp2 hY2 hY8 (CFSG.Open.IsElemAbelian.isPGroup hD)
    hDY hYD hzY hzD hz
  refine ⟨i, j, z, hiY, hjY, hzY.1, hz, hi, hj, hij, ?_⟩
  apply le_antisymm
  · intro x hx
    have hxc : x ∈ Subgroup.centralizer (D₀ : Set G) :=
      Subgroup.centralizer_le (show (D₀ : Set G) ⊆ D from hD₀) hx.2
    have : x ∈ Y ⊓ Subgroup.centralizer (D : Set G) := ⟨⟨hx.1, hxc⟩, hx.2⟩
    rw [h1] at this
    exact this
  · rw [← h1]
    exact inf_le_inf inf_le_left le_rfl

end Q8

section ExistsU

theorem eq_one_or_eq_of_mem_zpowers' {z x : G} (hz : orderOf z = 2) (hx : x ∈ Subgroup.zpowers z) :
    x = 1 ∨ x = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h := zpow_mod_orderOf z k
  rw [hz] at h
  have hk : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by
    have := Int.emod_two_eq_zero_or_one k
    simpa using this
  rcases hk with hk | hk
  · left
    rw [← h, hk, zpow_zero]
  · right
    rw [← h, hk, zpow_one]

theorem exists_U {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {T D D₀ D₁ : Subgroup G}
    (hT : IsPGroup 2 T) (hD : IsElemAbelian p D) (hDne : D ≠ ⊥)
    (hDT : D ≤ Subgroup.normalizer (T : Set G))
    (hrk : ∀ D₀ : Subgroup G, D₀ ≤ D → Nat.card D₀ * p = Nat.card D →
      (⁅T ⊓ Subgroup.centralizer (D₀ : Set G), D⁆ : Subgroup G) ≠ ⊥ →
      ∀ U : Subgroup G, U ≤ T ⊓ Subgroup.centralizer (D₀ : Set G) → IsElemAbelian 2 U →
        Nat.card U ≤ 2)
    (hTD : (⁅T, D⁆ : Subgroup G) ≠ ⊥) (hD₀ : D₀ ≤ D) (hD₁ : D₁ ≤ D) (hsup : D₀ ⊔ D₁ = D)
    (hQ₀ : (⁅T ⊓ Subgroup.centralizer (D₀ : Set G), D⁆ : Subgroup G) ≠ ⊥)
    (hQ₁ : (⁅T ⊓ Subgroup.centralizer (D₁ : Set G), D⁆ : Subgroup G) ≠ ⊥)
    (e₀ : ↥(T ⊓ Subgroup.centralizer (D₀ : Set G)) ≃* QuaternionGroup 2)
    (e₁ : ↥(T ⊓ Subgroup.centralizer (D₁ : Set G)) ≃* QuaternionGroup 2) :
    ∃ U : Subgroup G, U ≤ T ⊓ Subgroup.centralizer ((D₀ ⊓ D₁ : Subgroup G) : Set G) ∧
      IsElemAbelian 2 U ∧ Nat.card U = 8 := by
  obtain ⟨i₀, j₀, z, hi₀, hj₀, hzT, hz, hi₀sq, hj₀sq, hij₀, hcent₀⟩ :=
    q8_data_of_hyperplane hp hp2 hT hD hDT hD₀ hQ₀ e₀
  obtain ⟨i₁, j₁, z₁, hi₁, hj₁, hz₁T, hz₁, hi₁sq, hj₁sq, hij₁, hcent₁⟩ :=
    q8_data_of_hyperplane hp hp2 hT hD hDT hD₁ hQ₁ e₁
  have hz₁z : z₁ = z := by
    have hmem : z₁ ∈ Subgroup.zpowers z := by
      rw [← hcent₀, hcent₁]
      exact Subgroup.mem_zpowers z₁
    rcases eq_one_or_eq_of_mem_zpowers' hz hmem with h | h
    · exfalso
      rw [h, orderOf_one] at hz₁
      exact absurd hz₁ (by norm_num)
    · exact h
  rw [hz₁z] at hz₁ hi₁sq hj₁sq hij₁ hcent₁ hz₁T
  obtain ⟨hzc, hcl⟩ := class_two_of_inf_centralizer_eq hp hp2 hT hD hDne hDT hrk hTD hzT hz hcent₀
  have hzD : ∀ a ∈ D, z * a = a * z := by
    intro a ha
    have : z ∈ T ⊓ Subgroup.centralizer (D : Set G) := by
      rw [hcent₀]; exact Subgroup.mem_zpowers z
    exact (Subgroup.mem_centralizer_iff.mp this.2 a ha).symm
  have hZc : ∀ c ∈ Subgroup.zpowers z, ∀ g ∈ T, g * c = c * g := fun c hc g hg =>
    (comm_of_mem_zpowers (y := z) (g := g) (hzc g hg).symm hc).symm
  have hZA : ∀ c ∈ Subgroup.zpowers z, ∀ a ∈ D, a * c * a⁻¹ = c := by
    intro c hc a ha
    have h := comm_of_mem_zpowers (y := z) (g := a) (hzD a ha) hc
    rw [← h, mul_inv_cancel_right]
  have hcomm : ∀ x ∈ T ⊓ Subgroup.centralizer (D₀ : Set G),
      ∀ t ∈ T ⊓ Subgroup.centralizer (D₁ : Set G), x * t = t * x := by
    intro x hx t ht
    refine commute_of_fixed_coset hp hp2 (A := D₁) (T := T)
      (T₀ := T ⊓ Subgroup.centralizer (D₀ : Set G)) (Z := Subgroup.zpowers z) (t := t)
      (CFSG.Open.IsElemAbelian.isPGroup (CFSG.Open.IsElemAbelian.mono hD hD₁)) hT inf_le_left
      (hD₁.trans (normalizer_inf_centralizer hD hDT hD₀)) ht.1 ?_ hZc
      (fun c hc a ha => hZA c hc a (hD₁ ha)) hcl ?_ x hx
    · intro a ha
      have h := Subgroup.mem_centralizer_iff.mp ht.2 a ha
      rw [h, mul_inv_cancel_right]
    · intro y hy hyc
      have hyD : D ≤ Subgroup.centralizer ({y} : Set G) := by
        rw [← hsup]
        refine sup_le (fun d hd => ?_) (fun d hd => ?_)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_iff.mp hy.2 d hd)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_iff.mp hyc d hd)
      have hyc' : y ∈ T ⊓ Subgroup.centralizer (D : Set G) := by
        refine ⟨hy.1, Subgroup.mem_centralizer_iff.mpr fun d hd => ?_⟩
        exact (Subgroup.mem_centralizer_singleton_iff.mp (hyD hd))
      rw [hcent₀] at hyc'
      exact (hZc y hyc' t ht.1).symm
  have hii : i₀ * i₁ = i₁ * i₀ := hcomm i₀ hi₀ i₁ hi₁
  have hij : i₀ * j₁ = j₁ * i₀ := hcomm i₀ hi₀ j₁ hj₁
  have hji : j₀ * i₁ = i₁ * j₀ := hcomm j₀ hj₀ i₁ hi₁
  have hjj : j₀ * j₁ = j₁ * j₀ := hcomm j₀ hj₀ j₁ hj₁
  obtain ⟨hU, hUcard⟩ := elemAbelian_eight hz hi₀sq hj₀sq hij₀ hi₁sq hj₁sq hij₁
    (hzc i₀ hi₀.1).symm (hzc j₀ hj₀.1).symm (hzc i₁ hi₁.1).symm (hzc j₁ hj₁.1).symm
    hii hij hji hjj
  refine ⟨Subgroup.zpowers z ⊔ Subgroup.zpowers (i₀ * i₁) ⊔ Subgroup.zpowers (j₀ * j₁), ?_, hU,
    hUcard⟩
  have hmono : ∀ {A : Subgroup G}, D₀ ⊓ D₁ ≤ A →
      T ⊓ Subgroup.centralizer (A : Set G) ≤
        T ⊓ Subgroup.centralizer ((D₀ ⊓ D₁ : Subgroup G) : Set G) := fun {A} h =>
    inf_le_inf_left _ (Subgroup.centralizer_le (show ((D₀ ⊓ D₁ : Subgroup G) : Set G) ⊆ A from h))
  have hzE : z ∈ T ⊓ Subgroup.centralizer ((D₀ ⊓ D₁ : Subgroup G) : Set G) := by
    refine hmono (A := D) (inf_le_left.trans hD₀) ?_
    rw [hcent₀]
    exact Subgroup.mem_zpowers z
  have hi₀E := hmono (A := D₀) inf_le_left hi₀
  have hj₀E := hmono (A := D₀) inf_le_left hj₀
  have hi₁E := hmono (A := D₁) inf_le_right hi₁
  have hj₁E := hmono (A := D₁) inf_le_right hj₁
  refine sup_le (sup_le (Subgroup.zpowers_le.mpr hzE) (Subgroup.zpowers_le.mpr ?_))
    (Subgroup.zpowers_le.mpr ?_)
  · exact Subgroup.mul_mem _ hi₀E hi₁E
  · exact Subgroup.mul_mem _ hj₀E hj₁E

end ExistsU

end CFSG.LocalAnalysis.GLTheoremA.P55.I336
