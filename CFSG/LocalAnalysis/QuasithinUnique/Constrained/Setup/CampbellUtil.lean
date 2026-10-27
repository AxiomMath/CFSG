module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellElem

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup CFSG CFSG.Quasithin CFSG.Quasithin.BlueprintB2

section Util

variable {G : Type*} [Group G]

theorem cj_eq_of_forall_mem [Finite G] {Y : Subgroup G} {g : G}
    (h : ∀ x ∈ Y, g * x * g⁻¹ ∈ Y) : cj Y g = Y := by
  have hle : Y ≤ cj Y g := fun x hx => mem_cj.mpr (h x hx)
  exact (Subgroup.eq_of_le_of_card_ge hle card_cj.le).symm

theorem mem_normalizer_of_le_cj [Finite G] {Y : Subgroup G} {y : G} (h : Y ≤ cj Y y) :
    y ∈ Subgroup.normalizer (Y : Set G) := by
  have heq : Y = cj Y y := Subgroup.eq_of_le_of_card_ge h card_cj.le
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact mem_cj.mp (h hx)
  · intro hx
    have : x ∈ cj Y y := mem_cj.mpr hx
    rwa [← heq] at this

theorem mem_sup_of_commute [Finite G] {P C : Subgroup G} (hc : ∀ x ∈ P, ∀ y ∈ C, x * y = y * x)
    {u : G} (hu : u ∈ P ⊔ C) : ∃ p ∈ P, ∃ c ∈ C, p * c = u := by
  have h1 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute P C hc).2
  have hu' : u ∈ ((P ⊔ C : Subgroup G) : Set G) := hu
  rw [h1] at hu'
  obtain ⟨p, hp, c, hc', hpc⟩ := hu'
  exact ⟨p, hp, c, hc', hpc⟩

open scoped commutatorElement in
theorem commutator_sup_of_commute [Finite G] {P C X : Subgroup G}
    (hPC : ∀ x ∈ P, ∀ y ∈ C, x * y = y * x) (hCX : ∀ y ∈ C, ∀ w ∈ X, y * w = w * y) :
    ⁅P ⊔ C, X⁆ ≤ ⁅P, X⁆ := by
  rw [Subgroup.commutator_le]
  intro u hu w hw
  obtain ⟨p, hp, c, hc, rfl⟩ := mem_sup_of_commute hPC hu
  have : ⁅p * c, w⁆ = ⁅p, w⁆ := by
    simp only [commutatorElement_def]
    have h1 : c * w * c⁻¹ = w := by rw [hCX c hc w hw]; group
    calc p * c * w * (p * c)⁻¹ * w⁻¹ = p * (c * w * c⁻¹) * p⁻¹ * w⁻¹ := by group
      _ = p * w * p⁻¹ * w⁻¹ := by rw [h1]
  rw [this]
  exact Subgroup.commutator_mem_commutator hp hw

theorem maxElem_le_of_commute [Finite G] {H A Y : Subgroup G} (hA : IsMaxElemAbelian H A)
    (hYH : Y ≤ H) (hY : CFSG.Open.IsElemAbelian 2 Y) (hc : ∀ y ∈ Y, ∀ a ∈ A, y * a = a * y) :
    Y ≤ A := fun y hy =>
  maxElem_mem_of_centralizer hA (hYH hy)
    (Subgroup.mem_centralizer_iff.mpr fun a ha => (hc y hy a ha).symm)
    ((isElemAbelian_iff.mp hY).2 y hy)

theorem mem_normalizer_of_cj_cj_eq {Y : Subgroup G} {g x : G} (hY : cj (cj Y g) x = cj Y g) :
    g * x * g⁻¹ ∈ Subgroup.normalizer (Y : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro w
  have h1 : cj (cj Y g) x = cj Y (g * x) := cj_cj
  rw [h1] at hY
  have key : ∀ z, z ∈ cj Y (g * x) ↔ z ∈ cj Y g := fun z => by rw [hY]
  have := key (g⁻¹ * w * g)
  rw [mem_cj, mem_cj] at this
  have e1 : g * x * (g⁻¹ * w * g) * (g * x)⁻¹ = g * x * g⁻¹ * w * (g * x * g⁻¹)⁻¹ := by group
  have e2 : g * (g⁻¹ * w * g) * g⁻¹ = w := by group
  rw [e1, e2] at this
  exact this.symm

theorem mem_of_central_conj {S₀ V : Subgroup G} (hV : V ≤ Subgroup.centralizer (S₀ : Set G))
    {n v : G} (hn : n ∈ S₀) (hv : v ∈ V) : n * v * n⁻¹ ∈ V := by
  have := Subgroup.mem_centralizer_iff.mp (hV hv) n hn
  rw [this]
  simpa using hv

theorem isMaxElemAbelian_core_of_le_cj [Finite G] {S₀ Q B : Subgroup G} {g : G} [Q.Normal]
    (hQ : Q ≤ S₀) (hB : IsMaxElemAbelian (cj S₀ g) B) (hBQ : B ≤ Q) :
    IsMaxElemAbelian Q B := by
  have hQcj : Q ≤ cj S₀ g := by
    have := cj_mono (g := g) hQ
    rwa [cj_eq_self_of_normal] at this
  exact ⟨hBQ, hB.2.1, fun B'' hB''Q hB''e => maxElem_card_le hB (hB''Q.trans hQcj) hB''e⟩

open scoped commutatorElement in
theorem mul_comm_of_commutator_eq_bot {P P' : Subgroup G} (h : ⁅P, P'⁆ = ⊥) {w y : G}
    (hw : w ∈ P) (hy : y ∈ P') : w * y = y * w := by
  have h1 : ⁅w, y⁆ ∈ (⁅P, P'⁆ : Subgroup G) := Subgroup.commutator_mem_commutator hw hy
  rw [h, Subgroup.mem_bot] at h1
  simp only [commutatorElement_def] at h1
  calc w * y = (w * y * w⁻¹ * y⁻¹) * (y * w) := by group
    _ = y * w := by rw [h1, one_mul]

open scoped commutatorElement in
theorem commutator_eq_bot_of_commute {P P' : Subgroup G}
    (h : ∀ w ∈ P, ∀ y ∈ P', w * y = y * w) : ⁅P, P'⁆ = ⊥ := by
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro w hw y hy
  rw [Subgroup.mem_bot]
  simp only [commutatorElement_def]
  rw [h w hw y hy]
  group

theorem mem_normalizer_sup_of_commutator [Finite G] {F₁ F₂ : Subgroup G} {y : G}
    (h1 : y ∈ Subgroup.normalizer (F₁ : Set G)) (h2 : ∀ w ∈ F₂, y * w * y⁻¹ * w⁻¹ ∈ F₁) :
    y ∈ Subgroup.normalizer ((F₁ ⊔ F₂ : Subgroup G) : Set G) := by
  apply mem_normalizer_of_le_cj
  refine sup_le (fun x hx => mem_cj.mpr ?_) (fun w hw => mem_cj.mpr ?_)
  · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp h1 x).mp hx)
  · have : y * w * y⁻¹ = (y * w * y⁻¹ * w⁻¹) * w := by group
    rw [this]
    exact mul_mem (Subgroup.mem_sup_left (h2 w hw)) (Subgroup.mem_sup_right hw)

theorem mem_normalizer_of_normal (N : Subgroup G) [N.Normal] (y : G) :
    y ∈ Subgroup.normalizer (N : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact (inferInstance : N.Normal).conj_mem x hx y
  · intro hx
    have := (inferInstance : N.Normal).conj_mem _ hx y⁻¹
    simpa [mul_assoc] using this

theorem cj_eq_of_le [Finite G] {Y : Subgroup G} {g : G} (h : cj Y g ≤ Y) : cj Y g = Y :=
  Subgroup.eq_of_le_of_card_ge h card_cj.ge

theorem iSup_cj_eq_normalClosure (S₀ : Subgroup G) :
    (⨆ g : G, cj S₀ g) = Subgroup.normalClosure (S₀ : Set G) := by
  apply le_antisymm
  · refine iSup_le fun g x hx => ?_
    have h1 : g * x * g⁻¹ ∈ S₀ := mem_cj.mp hx
    have h2 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ ∈ Subgroup.normalClosure (S₀ : Set G) :=
      (inferInstance : (Subgroup.normalClosure (S₀ : Set G)).Normal).conj_mem _
        (Subgroup.subset_normalClosure h1) g⁻¹
    simpa [mul_assoc] using h2
  · have hnormal : (⨆ g : G, cj S₀ g).Normal := by
      refine ⟨fun n hn k => ?_⟩
      have : (⨆ g : G, cj S₀ g).map (MulAut.conj k).toMonoidHom ≤ ⨆ g : G, cj S₀ g := by
        rw [Subgroup.map_iSup]
        refine iSup_le fun g => ?_
        have hcj : (cj S₀ g).map (MulAut.conj k).toMonoidHom = cj S₀ (g * k⁻¹) := by
          ext x
          rw [mem_cj]
          constructor
          · rintro ⟨y, hy, rfl⟩
            have := mem_cj.mp hy
            simpa [MulAut.conj_apply, mul_assoc] using this
          · intro hx
            refine ⟨k⁻¹ * x * k, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
            exact mem_cj.mpr (by simpa [mul_assoc] using hx)
        rw [hcj]
        exact le_iSup (fun g => cj S₀ g) (g * k⁻¹)
      exact this ⟨n, hn, rfl⟩
    refine Subgroup.normalClosure_le_normal fun x hx => ?_
    have : x ∈ cj S₀ (1 : G) := by simpa using hx
    exact Subgroup.mem_iSup_of_mem 1 this

theorem commutator_le_of_le {S₀ A B : Subgroup G} (hA : A ≤ S₀) (hB : B ≤ S₀) : ⁅A, B⁆ ≤ S₀ :=
  Subgroup.commutator_le.mpr fun _ ha _ hb =>
    S₀.mul_mem (S₀.mul_mem (S₀.mul_mem (hA ha) (hB hb)) (S₀.inv_mem (hA ha))) (S₀.inv_mem (hB hb))

theorem mul_comm_of_comm_eq_one {a b : G} (h : a * b * a⁻¹ * b⁻¹ = 1) : a * b = b * a := by
  have : a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
  rw [this, h, one_mul]

end Util

end CFSG.QuasithinUnique.Setup.Campbell
