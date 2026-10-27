module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BaseF
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BaseF4

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

open scoped commutatorElement

theorem exists_mul_of_mem_sup_of_comm {G : Type*} [Group G] {H K : Subgroup G}
    (hHK : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, x = h * k := by
  let T : Subgroup G :=
    { carrier := {x | ∃ h ∈ H, ∃ k ∈ K, x = h * k}
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨h, hh, k, hk, rfl⟩ ⟨h', hh', k', hk', rfl⟩
        refine ⟨h * h', mul_mem hh hh', k * k', mul_mem hk hk', ?_⟩
        have : k * h' = h' * k := (hHK h' hh' k hk).symm
        calc h * k * (h' * k') = h * (k * h') * k' := by group
          _ = h * (h' * k) * k' := by rw [this]
          _ = h * h' * (k * k') := by group
      inv_mem' := by
        rintro _ ⟨h, hh, k, hk, rfl⟩
        refine ⟨h⁻¹, inv_mem hh, k⁻¹, inv_mem hk, ?_⟩
        have : h * k = k * h := hHK h hh k hk
        calc (h * k)⁻¹ = (k * h)⁻¹ := by rw [this]
          _ = h⁻¹ * k⁻¹ := by group }
  have hHT : H ≤ T := fun h hh => ⟨h, hh, 1, one_mem _, by simp⟩
  have hKT : K ≤ T := fun k hk => ⟨1, one_mem _, k, hk, by simp⟩
  exact (sup_le hHT hKT) hx

theorem sq_eq_one_of_central_sup {G ι : Type*} [Group G] [DecidableEq ι] (s : Finset ι)
    (f : ι → Subgroup G)
    (hcomm : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ a ∈ f i, ∀ b ∈ f j, a * b = b * a)
    (hcen : ∀ i ∈ s, ∀ a ∈ f i, (∀ b ∈ f i, a * b = b * a) → a * a = 1) :
    ∀ x ∈ s.sup f, (∀ y ∈ s.sup f, x * y = y * x) → x * x = 1 := by
  induction s using Finset.induction_on with
  | empty =>
    intro x hx _
    have : x ∈ (⊥ : Subgroup G) := by simpa using hx
    rw [Subgroup.mem_bot.1 this]
    simp
  | insert i s hi ih =>
    intro x hx hxc
    rw [Finset.sup_insert] at hx hxc
    have hcomm' : ∀ i' ∈ s, ∀ j ∈ s, i' ≠ j → ∀ a ∈ f i', ∀ b ∈ f j, a * b = b * a :=
      fun i' hi' j hj => hcomm i' (Finset.mem_insert_of_mem hi') j (Finset.mem_insert_of_mem hj)
    have hcen' : ∀ i' ∈ s, ∀ a ∈ f i', (∀ b ∈ f i', a * b = b * a) → a * a = 1 :=
      fun i' hi' => hcen i' (Finset.mem_insert_of_mem hi')
    have hAs : ∀ a ∈ f i, ∀ u ∈ s.sup f, a * u = u * a := by
      intro a ha u hu
      have hle : s.sup f ≤ Subgroup.centralizer (f i : Set G) := by
        refine Finset.sup_le fun j hj => ?_
        intro b hb
        rw [Subgroup.mem_centralizer_iff]
        intro a' ha'
        have hne : i ≠ j := fun h => hi (h ▸ hj)
        exact hcomm i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj) hne a' ha' b hb
      exact (Subgroup.mem_centralizer_iff.1 (hle hu)) a ha
    obtain ⟨a, ha, u, hu, rfl⟩ := exists_mul_of_mem_sup_of_comm hAs hx
    have hac : ∀ b ∈ f i, a * b = b * a := by
      intro b hb
      have h1 := hxc b (Subgroup.mem_sup_left hb)
      have h2 : u * b = b * u := (hAs b hb u hu).symm
      have : a * b * u = b * a * u := by
        calc a * b * u = a * (b * u) := by group
          _ = a * (u * b) := by rw [← h2]
          _ = a * u * b := by group
          _ = b * (a * u) := h1
          _ = b * a * u := by group
      exact mul_right_cancel this
    have ha2 : a * a = 1 := hcen i (Finset.mem_insert_self _ _) a ha hac
    have huc : ∀ y ∈ s.sup f, u * y = y * u := by
      intro y hy
      have h1 := hxc y (Subgroup.mem_sup_right hy)
      have h2 : a * y = y * a := hAs a ha y hy
      have : a * (u * y) = a * (y * u) := by
        calc a * (u * y) = a * u * y := by group
          _ = y * (a * u) := h1
          _ = (y * a) * u := by group
          _ = (a * y) * u := by rw [h2]
          _ = a * (y * u) := by group
      exact mul_left_cancel this
    have hu2 : u * u = 1 := ih hcomm' hcen' u hu huc
    have hau : a * u = u * a := hAs a ha u hu
    calc a * u * (a * u) = a * (u * a) * u := by group
      _ = a * (a * u) * u := by rw [← hau]
      _ = (a * a) * (u * u) := by group
      _ = 1 := by rw [ha2, hu2, one_mul]

namespace Sec5Data

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))}

theorem Z_sq_eq_one (h : Sec5Data X n z Z S) {x : X} (hx : x ∈ Z) : x * x = 1 := by
  classical
  have hDN : K0 X n (normalizer (Z : Set X)) ≤ normalizer (Z : Set X) := K0_le n _
  have hND : normalizer (Z : Set X) ≤ normalizer (K0 X n (normalizer (Z : Set X)) : Set X) :=
    Sec5Data.le_normalizer_K0 X n _
  set N : Subgroup X := normalizer (Z : Set X) with hN
  set D : Subgroup X := K0 X n N with hD
  have hOD : oddCoreOf D = D ⊓ oddCoreOf N := oddCoreOf_eq_inf hDN hND
  let π : ↥D →* ↥D ⧸ pPrimeCore 2 ↥D := QuotientGroup.mk' (pPrimeCore 2 ↥D)
  let f : Subgroup X → Subgroup (↥D ⧸ pPrimeCore 2 ↥D) := fun A => (A.subgroupOf D).map π
  have h𝒜fin : {A : Subgroup X | Sec5Comp X n N A}.Finite := Set.toFinite _
  let s : Finset (Subgroup X) := h𝒜fin.toFinset
  have hs : ∀ A, A ∈ s ↔ Sec5Comp X n N A := fun A => by simp [s]
  have hAD : ∀ A, Sec5Comp X n N A → A ≤ D := fun A hA => le_sSup hA
  have hπeq : ∀ α β : ↥D, ⁅(α : X), (β : X)⁆ ∈ oddCoreOf D → π α * π β = π β * π α := by
    intro α β hαβ
    obtain ⟨_, hP⟩ := mem_oddCoreOf_iff.1 hαβ
    have h1 : π ⁅α, β⁆ = 1 := (QuotientGroup.eq_one_iff _).2 hP
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have hπeq' : ∀ α β : ↥D, π α * π β = π β * π α → ⁅(α : X), (β : X)⁆ ∈ oddCoreOf D := by
    intro α β hαβ
    have h1 : π ⁅α, β⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 hαβ
    exact mem_oddCoreOf_iff.2 ⟨(⁅α, β⁆ : ↥D).2, (QuotientGroup.eq_one_iff _).1 h1⟩
  have hcomm : ∀ A ∈ s, ∀ B ∈ s, A ≠ B → ∀ a ∈ f A, ∀ b ∈ f B, a * b = b * a := by
    intro A hA B hB hAB a ha b hb
    obtain ⟨α, hα, rfl⟩ := ha
    obtain ⟨β, hβ, rfl⟩ := hb
    have hA' := (hs A).1 hA
    have hB' := (hs B).1 hB
    have hc := commutator_mem_oddCoreOf_of_ne hA'.isPCompIn hB'.isPCompIn hAB hα hβ
    refine hπeq α β ?_
    rw [hOD]
    exact ⟨(⁅α, β⁆ : ↥D).2, hc⟩
  have hcen : ∀ A ∈ s, ∀ a ∈ f A, (∀ b ∈ f A, a * b = b * a) → a * a = 1 := by
    intro A hA a ha hac
    obtain ⟨α, hα, rfl⟩ := ha
    have hA' := (hs A).1 hA
    have hAN : A ≤ N := hA'.isPCompIn.1
    have hdc := hA'.2
    have hα' : (α : X) ∈ A := hα
    have hcenter : (QuotientGroup.mk (⟨(α : X), hα'⟩ : ↥A) : ↥A ⧸ pPrimeCore 2 ↥A) ∈
        center (↥A ⧸ pPrimeCore 2 ↥A) := by
      rw [Subgroup.mem_center_iff]
      intro k
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective k
      have hb : (⟨(b : X), hAD A hA' b.2⟩ : ↥D) ∈ A.subgroupOf D := b.2
      have h1 := hπeq' α ⟨(b : X), hAD A hA' b.2⟩ (hac _ ⟨_, hb, rfl⟩)
      have h2 : ⁅(α : X), (b : X)⁆ ∈ oddCoreOf A := by
        refine inf_oddCoreOf_le hAN ⟨?_, ?_⟩
        · simp only [commutatorElement_def]
          exact A.mul_mem (A.mul_mem (A.mul_mem hα' b.2) (A.inv_mem hα')) (A.inv_mem b.2)
        · rw [hOD] at h1
          exact h1.2
      obtain ⟨_, hP⟩ := mem_oddCoreOf_iff.1 h2
      have h3 : (⁅(⟨(α : X), hα'⟩ : ↥A), b⁆ : ↥A) ∈ pPrimeCore 2 ↥A := hP
      have h4 : (QuotientGroup.mk' (pPrimeCore 2 ↥A)) ⁅(⟨(α : X), hα'⟩ : ↥A), b⁆ = 1 :=
        (QuotientGroup.eq_one_iff _).2 h3
      rw [map_commutatorElement] at h4
      exact (commutatorElement_eq_one_iff_mul_comm.1 h4).symm
    have hsq := (AhatData.CoverSetup.ofCover hdc).sq_of_mem_center hcenter
    have hsq' : (⟨(α : X), hα'⟩ * ⟨(α : X), hα'⟩ : ↥A) ∈ pPrimeCore 2 ↥A := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul]
      exact hsq
    have h5 : (α : X) * α ∈ oddCoreOf A := mem_oddCoreOf_iff.2 ⟨A.mul_mem hα' hα', hsq'⟩
    have h6 : (α : X) * α ∈ oddCoreOf D := by
      rw [hOD]
      exact ⟨D.mul_mem α.2 α.2, oddCoreOf_le_of_isPCompIn hA'.isPCompIn h5⟩
    obtain ⟨_, hP⟩ := mem_oddCoreOf_iff.1 h6
    show π α * π α = 1
    rw [← map_mul]
    exact (QuotientGroup.eq_one_iff _).2 hP
  have hjoin : ∀ d : ↥D, π d ∈ s.sup f := by
    let W : Subgroup ↥D := (s.sup f).comap π
    have hAW : ∀ A, Sec5Comp X n N A → A ≤ W.map D.subtype := by
      intro A hA a ha
      refine ⟨⟨a, hAD A hA ha⟩, ?_, rfl⟩
      show π ⟨a, hAD A hA ha⟩ ∈ s.sup f
      exact Finset.le_sup (f := f) ((hs A).2 hA) ⟨_, (show (⟨a, hAD A hA ha⟩ : ↥D) ∈
        A.subgroupOf D from ha), rfl⟩
    have hDW : D ≤ W.map D.subtype := by
      have hDeq : D = sSup {A : Subgroup X | Sec5Comp X n N A} := K0_eq_sSup_sec5Comp X n N
      calc D = sSup {A : Subgroup X | Sec5Comp X n N A} := hDeq
        _ ≤ W.map D.subtype := sSup_le fun A hA => hAW A hA
    intro d
    obtain ⟨w, hw, hwd⟩ := hDW d.2
    have : w = d := Subtype.ext hwd
    rw [this] at hw
    exact hw
  have hxD : x ∈ D := h.Z_le_K0 hx
  have hcentral : ∀ y ∈ s.sup f, π ⟨x, hxD⟩ * y = y * π ⟨x, hxD⟩ := by
    intro y _
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective y
    show π ⟨x, hxD⟩ * π d = π d * π ⟨x, hxD⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (h.Z_le_center_K0 hx d.2)
  have hsq := sq_eq_one_of_central_sup s f hcomm hcen (π ⟨x, hxD⟩) (hjoin _) hcentral
  rw [← map_mul] at hsq
  have hxxD : x * x ∈ oddCoreOf D :=
    mem_oddCoreOf_iff.2 ⟨D.mul_mem hxD hxD, (QuotientGroup.eq_one_iff _).1 hsq⟩
  have hodd : Odd (Nat.card (oddCoreOf D)) := odd_card_oddCoreOf D
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 h.isPGroup_Z) (⟨x * x, mul_mem hx hx⟩ : ↥Z)
  have hk' : orderOf (x * x) = 2 ^ k :=
    (Subgroup.orderOf_coe (⟨x * x, mul_mem hx hx⟩ : ↥Z)).trans hk
  have hdvd : orderOf (x * x) ∣ Nat.card (oddCoreOf D) :=
    Subgroup.orderOf_dvd_natCard (oddCoreOf D) hxxD
  have h1 : orderOf (x * x) ∣ 1 := by
    have hcop : Nat.Coprime (2 ^ k) (Nat.card (oddCoreOf D)) :=
      (Nat.coprime_two_left.2 hodd).pow_left k
    rw [hk'] at hdvd ⊢
    exact hcop.dvd_of_dvd_mul_left (by simpa using hdvd)
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1)

theorem orderOf_eq_two_of_mem_Z (h : Sec5Data X n z Z S) {x : X} (hx : x ∈ Z) (hx1 : x ≠ 1) :
    orderOf x = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [sq]; exact h.Z_sq_eq_one hx) hx1

end Sec5Data

end CFSG.OddStandard.Solomon75
