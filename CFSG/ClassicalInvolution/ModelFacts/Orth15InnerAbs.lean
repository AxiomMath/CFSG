module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15Alpha

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15

open CFSG.ClassicalInvolution.Asc77 CFSG.Assembly.Dichotomy
open scoped commutatorElement

section Rigid

variable {G : Type} [Group G] [Finite G]

theorem alphaOf_eq_bot_of_layers_rigid (L : Subgroup G) [L.Normal] (B : Subgroup G)
    (hBL : B ≤ L) (hB2 : ∀ b ∈ B, b * b = 1) (hBne : ∃ b ∈ B, b ≠ 1)
    (Fam : Set (Subgroup G))
    (hatt : ∀ P ∈ Fam, ∃ a ∈ B, a ≠ 1 ∧ P ≤ L ⊓ Subgroup.centralizer ({a} : Set G) ∧
      P ≤ ⁅P, P⁆ ∧
      ∀ N : Subgroup G, N ≤ L ⊓ Subgroup.centralizer ({a} : Set G) →
        (∀ x ∈ L ⊓ Subgroup.centralizer ({a} : Set G), ∀ n ∈ N, x * n * x⁻¹ ∈ N) →
        Odd (Nat.card N) → ⁅N, P⁆ = ⊥)
    (hB : ∀ a ∈ B, a ≠ 1 → ∀ N : Subgroup G, N ≤ L ⊓ Subgroup.centralizer ({a} : Set G) →
      (∀ x ∈ L ⊓ Subgroup.centralizer ({a} : Set G), ∀ n ∈ N, x * n * x⁻¹ ∈ N) →
        Odd (Nat.card N) → ⁅N, B⁆ = ⊥)
    (hrig : ∀ x : G, Odd (orderOf x) → (∀ P ∈ Fam, ∀ p ∈ P, x * p = p * x) → x = 1) :
    alphaOf B = ⊥ := by
  classical
  have hBcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hB2 x hx)
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hB2 y hy)
    have h := inv_eq_of_mul_eq_one_right (hB2 (x * y) (B.mul_mem hx hy))
    rw [mul_inv_rev, hxi, hyi] at h
    exact h.symm
  have hM : ∀ a ∈ B, a ≠ 1 → ∃ M : Subgroup G, M = involutionOddCore a ⊓ L ∧
      M ≤ L ⊓ Subgroup.centralizer ({a} : Set G) ∧
      (∀ x ∈ L ⊓ Subgroup.centralizer ({a} : Set G), ∀ n ∈ M, x * n * x⁻¹ ∈ M) ∧
      Odd (Nat.card M) := by
    intro a ha ha1
    refine ⟨involutionOddCore a ⊓ L, rfl, ?_, ?_, ?_⟩
    · exact fun x hx => ⟨hx.2, involutionOddCore_le_centralizer' a hx.1⟩
    · intro x hx n hn
      exact ⟨conj_mem_involutionOddCore a hx.2 hn.1,
        L.mul_mem (L.mul_mem hx.1 hn.2) (L.inv_mem hx.1)⟩
    · exact Odd.of_dvd_nat (odd_natCard_involutionOddCore a)
        (Subgroup.card_dvd_of_le inf_le_left)
  refine (alphaOf_eq_bot_iff B).mpr ⟨?_, ?_⟩
  ·
    intro a ha ha1
    obtain ⟨M, rfl, hMle, hMnorm, hModd⟩ := hM a ha ha1
    refine commutator_eq_bot_of_comm fun g hg b hb => ?_
    have hbC : b ∈ Subgroup.centralizer ({a} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hBcomm y ha b hb
    have hbL : b ∈ L := hBL hb
    have hcN : ⁅g, b⁆ ∈ involutionOddCore a := by
      have e : (⁅g, b⁆ : G) = g * (b * g⁻¹ * b⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact (involutionOddCore a).mul_mem hg
        (conj_mem_involutionOddCore a hbC ((involutionOddCore a).inv_mem hg))
    have hcL : ⁅g, b⁆ ∈ L := by
      have e : (⁅g, b⁆ : G) = (g * b * g⁻¹) * b⁻¹ := commutatorElement_def g b
      rw [e]
      exact L.mul_mem (Subgroup.Normal.conj_mem ‹L.Normal› b hbL g) (L.inv_mem hbL)
    have hcM : ⁅g, b⁆ ∈ involutionOddCore a ⊓ L := ⟨hcN, hcL⟩
    have hcb : ⁅g, b⁆ * b = b * ⁅g, b⁆ :=
      comm_of_commutator_eq_bot (hB a ha ha1 _ hMle hMnorm hModd) hcM hb
    have e1 : ⁅g, b⁆ * b = g * b * g⁻¹ := by
      simp only [commutatorElement_def]; group
    have e2 : (g * b * g⁻¹) * (g * b * g⁻¹) = 1 := by
      have : (g * b * g⁻¹) * (g * b * g⁻¹) = g * (b * b) * g⁻¹ := by group
      rw [this, hB2 b hb]
      group
    have e3 : ⁅g, b⁆ * ⁅g, b⁆ = 1 := by
      have : (⁅g, b⁆ * b) * (⁅g, b⁆ * b) = ⁅g, b⁆ * ⁅g, b⁆ * (b * b) := by
        calc (⁅g, b⁆ * b) * (⁅g, b⁆ * b) = ⁅g, b⁆ * (b * ⁅g, b⁆) * b := by group
          _ = ⁅g, b⁆ * (⁅g, b⁆ * b) * b := by rw [hcb]
          _ = ⁅g, b⁆ * ⁅g, b⁆ * (b * b) := by group
      rw [e1, e2, hB2 b hb, mul_one] at this
      exact this.symm
    have : ⁅g, b⁆ = 1 := eq_one_of_mul_self_of_odd hModd hcM e3
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  ·
    refine eq_bot_iff.mpr fun x hx => ?_
    rw [Subgroup.mem_bot]
    obtain ⟨b, hbB, hb1⟩ := hBne
    have hxb : x ∈ involutionOddCore b := by
      have := Subgroup.mem_iInf.mp hx b
      have := Subgroup.mem_iInf.mp this hbB
      exact (Subgroup.mem_iInf.mp this hb1)
    have hxodd : Odd (orderOf x) :=
      Odd.of_dvd_nat (odd_natCard_involutionOddCore b) (Subgroup.orderOf_dvd_natCard _ hxb)
    refine hrig x hxodd ?_
    intro P hP p hp
    obtain ⟨a, haB, ha1, hPle, hPperf, hPN⟩ := hatt P hP
    obtain ⟨M, hMe, hMle, hMnorm, hModd⟩ := hM a haB ha1
    have hxa : x ∈ involutionOddCore a := by
      have := Subgroup.mem_iInf.mp hx a
      have := Subgroup.mem_iInf.mp this haB
      exact (Subgroup.mem_iInf.mp this ha1)
    have hNPM : ⁅involutionOddCore a, P⁆ ≤ M := by
      rw [Subgroup.commutator_le]
      intro g hg q hq
      rw [hMe]
      refine ⟨?_, ?_⟩
      · have e : (⁅g, q⁆ : G) = g * (q * g⁻¹ * q⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (involutionOddCore a).mul_mem hg
          (conj_mem_involutionOddCore a (hPle hq).2 ((involutionOddCore a).inv_mem hg))
      · have e : (⁅g, q⁆ : G) = (g * q * g⁻¹) * q⁻¹ := commutatorElement_def g q
        rw [e]
        exact L.mul_mem (Subgroup.Normal.conj_mem ‹L.Normal› q (hPle hq).1 g)
          (L.inv_mem (hPle hq).1)
    have hMP : ⁅M, P⁆ = ⊥ := hPN M hMle hMnorm hModd
    have h1 : ⁅⁅involutionOddCore a, P⁆, P⁆ = ⊥ :=
      eq_bot_iff.mpr ((Subgroup.commutator_mono hNPM le_rfl).trans hMP.le)
    have h2 : ⁅⁅P, involutionOddCore a⁆, P⁆ = ⊥ := by
      rw [Subgroup.commutator_comm P (involutionOddCore a)]
      exact h1
    have h3 : ⁅⁅P, P⁆, involutionOddCore a⁆ = ⊥ :=
      Subgroup.commutator_commutator_eq_bot_of_rotate h2 h1
    have h4 : ⁅P, involutionOddCore a⁆ = ⊥ :=
      eq_bot_iff.mpr ((Subgroup.commutator_mono hPperf le_rfl).trans h3.le)
    exact (comm_of_commutator_eq_bot h4 hp hxa).symm

end Rigid

section Klein

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem klein_mem_closure {x y : X} (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y = y * x)
    {b : X} (hb : b ∈ Subgroup.closure ({x, y} : Set X)) :
    b = 1 ∨ b = x ∨ b = y ∨ b = x * y := by
  have h1 : x * (x * y) = y := by rw [← mul_assoc, hx, one_mul]
  have h2 : y * (x * y) = x := by rw [← mul_assoc, ← hxy, mul_assoc, hy, mul_one]
  have h3 : x * y * x = y := by rw [hxy, mul_assoc, hx, mul_one]
  have h4 : x * y * y = x := by rw [mul_assoc, hy, mul_one]
  have h5 : x * y * (x * y) = 1 := by rw [mul_assoc, h2, hx]
  have h6 : y * x = x * y := hxy.symm
  induction hb using Subgroup.closure_induction with
  | mem b hb =>
    rcases hb with rfl | hb
    · exact Or.inr (Or.inl rfl)
    · rw [Set.mem_singleton_iff] at hb
      subst hb
      exact Or.inr (Or.inr (Or.inl rfl))
  | one => exact Or.inl rfl
  | mul b₁ b₂ _ _ ih₁ ih₂ =>
    rcases ih₁ with rfl | rfl | rfl | rfl <;> rcases ih₂ with rfl | rfl | rfl | rfl <;>
      simp [hx, hy, h1, h2, h3, h4, h5, h6]
  | inv b _ ih =>
    rcases ih with rfl | rfl | rfl | rfl
    · simp
    · rw [inv_eq_of_mul_eq_one_right hx]; simp
    · rw [inv_eq_of_mul_eq_one_right hy]; simp
    · rw [inv_eq_of_mul_eq_one_right h5]; simp

structure LayerData (L B : Subgroup X) (a : X) (P : Subgroup X) : Prop where
  le : P ≤ L ⊓ Subgroup.centralizer ({a} : Set X)
  norm : ∀ x ∈ L ⊓ Subgroup.centralizer ({a} : Set X), ∀ p ∈ P, x * p * x⁻¹ ∈ P
  perf : P ≤ ⁅P, P⁆
  gen : ∃ 𝓗 : Set (Subgroup X), (∀ H ∈ 𝓗, H ≤ P ∧ CFSG.Open.IsQuasisimple ↥H ∧
    ∀ p ∈ P, ∀ h ∈ H, p * h * p⁻¹ ∈ H) ∧ P ≤ ⨆ H ∈ 𝓗, H
  cover : B ≤ Subgroup.zpowers a ⊔ P

variable {L B : Subgroup X} {a : X} {P : Subgroup X}

theorem LayerData.commutator_eq_bot (h : LayerData L B a P) {N : Subgroup X}
    (hNle : N ≤ L ⊓ Subgroup.centralizer ({a} : Set X))
    (hNnorm : ∀ x ∈ L ⊓ Subgroup.centralizer ({a} : Set X), ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (hodd : Odd (Nat.card N)) : ⁅N, P⁆ = ⊥ := by
  obtain ⟨𝓗, h𝓗, hP⟩ := h.gen
  exact commutator_eq_bot_of_layers P N 𝓗 h𝓗 hP (fun p hp o ho => hNnorm p (h.le hp) o ho)
    (fun o ho p hp => h.norm o (hNle ho) p hp) hodd

theorem LayerData.commutator_B_eq_bot (h : LayerData L B a P) {N : Subgroup X}
    (hNle : N ≤ L ⊓ Subgroup.centralizer ({a} : Set X))
    (hNnorm : ∀ x ∈ L ⊓ Subgroup.centralizer ({a} : Set X), ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (hodd : Odd (Nat.card N)) : ⁅N, B⁆ = ⊥ := by
  have hNP := h.commutator_eq_bot hNle hNnorm hodd
  refine commutator_eq_bot_of_comm fun n hn b hb => ?_
  have hle : Subgroup.zpowers a ⊔ P ≤ Subgroup.centralizer ({n} : Set X) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact ((Subgroup.mem_centralizer_iff.mp (hNle hn).2) a rfl).symm
    · intro p hp
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact comm_of_commutator_eq_bot hNP hn hp
  have := hle (h.cover hb)
  rw [Subgroup.mem_centralizer_iff] at this
  exact this n rfl

theorem alphaOf_klein_of_three_layers (L : Subgroup X) [L.Normal] {b₁ b₂ : X} (hb₁ : b₁ ∈ L)
    (hb₂ : b₂ ∈ L) (h1 : b₁ * b₁ = 1) (h2 : b₂ * b₂ = 1) (h12 : b₁ * b₂ = b₂ * b₁)
    (hne₁ : b₁ ≠ 1) (hne₂ : b₂ ≠ 1) (hne₃ : b₁ * b₂ ≠ 1) {P₁ P₂ P₃ : Subgroup X}
    (d₁ : LayerData L (Subgroup.closure ({b₁, b₂} : Set X)) b₁ P₁)
    (d₂ : LayerData L (Subgroup.closure ({b₁, b₂} : Set X)) b₂ P₂)
    (d₃ : LayerData L (Subgroup.closure ({b₁, b₂} : Set X)) (b₁ * b₂) P₃)
    (hrig : ∀ x : X, Odd (orderOf x) → (∀ p ∈ P₁, x * p = p * x) → (∀ p ∈ P₂, x * p = p * x) →
      (∀ p ∈ P₃, x * p = p * x) → x = 1) :
    alphaOf (Subgroup.closure ({b₁, b₂} : Set X)) = ⊥ := by
  set B : Subgroup X := Subgroup.closure ({b₁, b₂} : Set X) with hB
  have hBmem := fun {b : X} (hb : b ∈ B) => klein_mem_closure h1 h2 h12 hb
  have hB2 : ∀ b ∈ B, b * b = 1 := by
    intro b hb
    rcases hBmem hb with rfl | rfl | rfl | rfl
    · simp
    · exact h1
    · exact h2
    · have : (b₁ * b₂) * (b₁ * b₂) = b₁ * (b₂ * b₁) * b₂ := by group
      rw [this, ← h12]
      calc b₁ * (b₁ * b₂) * b₂ = (b₁ * b₁) * (b₂ * b₂) := by group
        _ = 1 := by rw [h1, h2, one_mul]
  have hBL : B ≤ L := by
    rw [hB, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hb₁
    · exact hb₂
  have he₁ : b₁ ∈ B := Subgroup.subset_closure (Set.mem_insert _ _)
  have he₂ : b₂ ∈ B := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have he₃ : b₁ * b₂ ∈ B := B.mul_mem he₁ he₂
  refine alphaOf_eq_bot_of_layers_rigid L B hBL hB2 ⟨b₁, he₁, hne₁⟩ {P₁, P₂, P₃} ?_ ?_ ?_
  · intro P hP
    rcases hP with rfl | hP
    · exact ⟨b₁, he₁, hne₁, d₁.le, d₁.perf,
        fun N hNle hNn hodd => d₁.commutator_eq_bot hNle hNn hodd⟩
    · rcases hP with rfl | hP
      · exact ⟨b₂, he₂, hne₂, d₂.le, d₂.perf,
          fun N hNle hNn hodd => d₂.commutator_eq_bot hNle hNn hodd⟩
      · rw [Set.mem_singleton_iff] at hP
        subst hP
        exact ⟨b₁ * b₂, he₃, hne₃, d₃.le, d₃.perf,
          fun N hNle hNn hodd => d₃.commutator_eq_bot hNle hNn hodd⟩
  · intro a ha ha1 N hNle hNn hodd
    rcases hBmem ha with rfl | rfl | rfl | rfl
    · exact absurd rfl ha1
    · exact d₁.commutator_B_eq_bot hNle hNn hodd
    · exact d₂.commutator_B_eq_bot hNle hNn hodd
    · exact d₃.commutator_B_eq_bot hNle hNn hodd
  · intro x hx hc
    exact hrig x hx (hc P₁ (by simp)) (hc P₂ (by simp)) (hc P₃ (by simp))

end Klein

section Transport

variable {S X : Type} [Group S] [Group X] [Finite X]

omit [Finite X] in
theorem layerData_of_hom (e : S →* X) (hker : e.ker ≤ Subgroup.center S) {a₀ : S}
    {Q : Subgroup S} (B : Subgroup X) (hcomm : ∀ p ∈ Q, p * a₀ = a₀ * p)
    (hnorm : ∀ g : S, e (g * a₀ * g⁻¹) = e a₀ → ∀ p ∈ Q, g * p * g⁻¹ ∈ Q)
    (hperf : Q ≤ ⁅Q, Q⁆)
    (hgen : ∃ 𝓗 : Set (Subgroup S), (∀ H ∈ 𝓗, H ≤ Q ∧ CFSG.IsQuasisimple ↥H ∧
      ∀ p ∈ Q, ∀ h ∈ H, p * h * p⁻¹ ∈ H) ∧ Q ≤ ⨆ H ∈ 𝓗, H)
    (hcover : B ≤ Subgroup.zpowers (e a₀) ⊔ Q.map e) :
    LayerData e.range B (e a₀) (Q.map e) := by
  refine ⟨?_, ?_, ?_, ?_, hcover⟩
  · rintro _ ⟨p, hp, rfl⟩
    refine ⟨⟨p, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    rw [← map_mul, ← map_mul, hcomm p hp]
  · rintro _ ⟨hxr, hxc⟩ _ ⟨p, hp, rfl⟩
    obtain ⟨g, rfl⟩ := hxr
    have hc : e g * e a₀ = e a₀ * e g := (Subgroup.mem_centralizer_iff.mp hxc (e a₀) rfl).symm
    have hg : e (g * a₀ * g⁻¹) = e a₀ := by
      rw [map_mul, map_mul, map_inv, hc]
      group
    exact ⟨g * p * g⁻¹, hnorm g hg p hp, by simp⟩
  · have h1 : (⁅Q, Q⁆).map e = ⁅Q.map e, Q.map e⁆ := Subgroup.map_commutator _ _ _
    rw [← h1]
    exact Subgroup.map_mono hperf
  · obtain ⟨𝓗, h𝓗, hP⟩ := hgen
    refine ⟨{K | ∃ H ∈ 𝓗, K = H.map e}, ?_, ?_⟩
    · rintro K ⟨H, hH, rfl⟩
      obtain ⟨hHP, hHq, hHn⟩ := h𝓗 H hH
      refine ⟨Subgroup.map_mono hHP, ?_, ?_⟩
      · let f : H →* X := e.comp H.subtype
        have hf : f.ker ≤ Subgroup.center H := by
          intro h hh
          rw [Subgroup.mem_center_iff]
          intro h'
          apply Subtype.ext
          have := Subgroup.mem_center_iff.mp (hker hh) (h' : S)
          exact this
        have hrange : f.range = H.map e := by
          ext y
          constructor
          · rintro ⟨h, rfl⟩
            exact ⟨h, h.2, rfl⟩
          · rintro ⟨h, hh, rfl⟩
            exact ⟨⟨h, hh⟩, rfl⟩
        have hsurj : Function.Surjective f.rangeRestrict := f.rangeRestrict_surjective
        have hHnt : ∃ h ∈ H, e h ≠ 1 := by
          by_contra hall
          push Not at hall
          obtain ⟨a, b, hab⟩ := hHq.2.2
          obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
          obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
          apply hab
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
          congr 1
          apply Subtype.ext
          exact Subgroup.mem_center_iff.mp (hker (hall b b.2)) (a : S)
        obtain ⟨h₀, hh₀, hh₀e⟩ := hHnt
        have hne : ∃ k : H, f.rangeRestrict k ≠ 1 := by
          refine ⟨⟨h₀, hh₀⟩, fun hk => hh₀e ?_⟩
          have := congrArg Subtype.val hk
          simpa [f] using this
        have hq := CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hHq hsurj hne
        rw [hrange] at hq
        exact ⟨Group.isPerfect_def.mp hq.1, hq.2.1⟩
      · rintro _ ⟨p, hp, rfl⟩ _ ⟨h, hh, rfl⟩
        exact ⟨p * h * p⁻¹, hHn p hp h hh, by simp⟩
    · refine le_trans (Subgroup.map_mono hP) ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun H => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hH => ?_
      exact le_iSup₂_of_le (H.map e) ⟨H, hH, rfl⟩ le_rfl

end Transport

section SLayer

theorem isQuasisimple_of_equiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (hG : CFSG.IsQuasisimple G) : CFSG.IsQuasisimple H :=
  hG.of_mulEquiv e.symm

variable {S : Type} [Group S]

structure SLayer (a : S) (Q : Subgroup S) : Prop where
  comm : ∀ p ∈ Q, p * a = a * p
  norm : ∀ g : S, g * a * g⁻¹ * a⁻¹ ∈ Subgroup.center S → ∀ p ∈ Q, g * p * g⁻¹ ∈ Q
  perf : Q ≤ ⁅Q, Q⁆
  gen : ∃ 𝓗 : Set (Subgroup S), (∀ H ∈ 𝓗, H ≤ Q ∧ CFSG.IsQuasisimple ↥H ∧
    ∀ p ∈ Q, ∀ h ∈ H, p * h * p⁻¹ ∈ H) ∧ Q ≤ ⨆ H ∈ 𝓗, H

variable {a : S} {Q : Subgroup S}

theorem SLayer.map (h : SLayer a Q) (τ : S ≃* S) : SLayer (τ a) (Q.map τ.toMonoidHom) := by
  have hc : ∀ z : S, τ z ∈ Subgroup.center S ↔ z ∈ Subgroup.center S := fun z => by
    rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
    constructor
    · intro hz g
      apply τ.injective
      rw [map_mul, map_mul]
      exact hz (τ g)
    · intro hz y
      obtain ⟨g, rfl⟩ := τ.surjective y
      rw [← map_mul, ← map_mul, hz g]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    show τ p * τ a = τ a * τ p
    rw [← map_mul, ← map_mul, h.comm p hp]
  · rintro g hg _ ⟨p, hp, rfl⟩
    have hg' : τ.symm g * a * (τ.symm g)⁻¹ * a⁻¹ ∈ Subgroup.center S := by
      rw [← hc]
      simpa using hg
    refine ⟨τ.symm g * p * (τ.symm g)⁻¹, h.norm _ hg' p hp, ?_⟩
    simp
  · have h1 : (⁅Q, Q⁆).map τ.toMonoidHom = ⁅Q.map τ.toMonoidHom, Q.map τ.toMonoidHom⁆ :=
      Subgroup.map_commutator _ _ _
    rw [← h1]
    exact Subgroup.map_mono h.perf
  · obtain ⟨𝓗, h𝓗, hQ⟩ := h.gen
    refine ⟨{K | ∃ H ∈ 𝓗, K = H.map τ.toMonoidHom}, ?_, ?_⟩
    · rintro K ⟨H, hH, rfl⟩
      obtain ⟨hHQ, hHq, hHn⟩ := h𝓗 H hH
      refine ⟨Subgroup.map_mono hHQ, ?_, ?_⟩
      · exact isQuasisimple_of_equiv (Subgroup.equivMapOfInjective H τ.toMonoidHom τ.injective)
          hHq
      · rintro _ ⟨p, hp, rfl⟩ _ ⟨h', hh', rfl⟩
        exact ⟨p * h' * p⁻¹, hHn p hp h' hh', by simp⟩
    · refine le_trans (Subgroup.map_mono hQ) ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun H => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hH => ?_
      exact le_iSup₂_of_le (H.map τ.toMonoidHom) ⟨H, hH, rfl⟩ le_rfl

theorem SLayer.of_central_mul (h : SLayer a Q) {z : S} (hz : z ∈ Subgroup.center S) :
    SLayer (z * a) Q := by
  have hzc : ∀ y : S, y * z = z * y := fun y => (Subgroup.mem_center_iff.mp hz y)
  refine ⟨fun p hp => ?_, fun g hg p hp => ?_, h.perf, h.gen⟩
  · rw [← mul_assoc, hzc p, mul_assoc, h.comm p hp, ← mul_assoc]
  · refine h.norm g ?_ p hp
    have e : g * (z * a) * g⁻¹ * (z * a)⁻¹ = g * a * g⁻¹ * a⁻¹ := by
      calc g * (z * a) * g⁻¹ * (z * a)⁻¹ = g * z * a * g⁻¹ * a⁻¹ * z⁻¹ := by group
        _ = z * (g * a * g⁻¹ * a⁻¹) * z⁻¹ := by rw [hzc g]; group
        _ = g * a * g⁻¹ * a⁻¹ := by
          have h1 : z * (g * a * g⁻¹ * a⁻¹) * z⁻¹ = g * a * g⁻¹ * a⁻¹ := by
            rw [← hzc (g * a * g⁻¹ * a⁻¹)]
            group
          exact h1
    rwa [e] at hg

omit [Group S] in
theorem SLayer.layerData {S X : Type} [Group S] [Group X] [Finite X] {a : S} {Q : Subgroup S}
    (h : SLayer a Q) (e : S →* X) (hker : e.ker ≤ Subgroup.center S) (B : Subgroup X)
    (hcover : B ≤ Subgroup.zpowers (e a) ⊔ Q.map e) :
    LayerData e.range B (e a) (Q.map e) := by
  refine layerData_of_hom e hker B h.comm (fun g hg p hp => ?_) h.perf h.gen hcover
  refine h.norm g (hker ?_) p hp
  rw [MonoidHom.mem_ker, map_mul, hg, map_inv]
  group

end SLayer

end CFSG.ClassicalInvolution.ModelFacts.Orth15
