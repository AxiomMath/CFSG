module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC3TypeA

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

theorem caseC3_normalize_step {K : Type*} [Group K] {X Y M N U V : K} (hX : X * X = 1)
    (hXY : X * Y * X⁻¹ = U * V * Y) (hXM : X * M * X⁻¹ = N) (hYM : Y * M * Y⁻¹ = U * M)
    (hYN : Y * N * Y⁻¹ = V * N) (hNU : Commute N U) (hM : M * M = 1) (hN : N * N = 1)
    (hU : U * U = 1) (hV : V * V = 1) :
    M * N * X * (M * N * X) = 1 ∧ M * N * X * Y = Y * (M * N * X) := by
  have hXi : X⁻¹ = X := inv_eq_of_mul_eq_one_right hX
  have hXN : X * N * X⁻¹ = M := by
    rw [← hXM, hXi, show X * (X * M * X) * X = (X * X) * M * (X * X) by group, hX]
    group
  have hMi : M⁻¹ = M := inv_eq_of_mul_eq_one_right hM
  have hNi : N⁻¹ = N := inv_eq_of_mul_eq_one_right hN
  constructor
  · calc M * N * X * (M * N * X) = M * N * (X * M * X⁻¹) * (X * N * X⁻¹) * (X * X) := by
          group
      _ = 1 := by
          rw [hXM, hXN, hX, mul_one, mul_assoc M N N, hN, mul_one, hM]
  · have key : M * N * X * Y * (M * N * X)⁻¹ = Y := by
      calc M * N * X * Y * (M * N * X)⁻¹ = M * N * (X * Y * X⁻¹) * N⁻¹ * M⁻¹ := by group
        _ = M * N * (U * V) * (Y * N * Y⁻¹) * (Y * M * Y⁻¹) * Y := by
            rw [hXY, hNi, hMi]; group
        _ = M * N * (U * V) * (V * N) * (U * M) * Y := by rw [hYN, hYM]
        _ = Y := by
            have h1 : M * N * (U * V) * (V * N) * (U * M) = 1 := by
              calc M * N * (U * V) * (V * N) * (U * M) = M * (N * U) * (V * V) * N * U * M := by
                    group
                _ = M * (U * N) * N * U * M := by rw [hV, hNU.eq]; group
                _ = M * U * (N * N) * U * M := by group
                _ = M * (U * U) * M := by rw [hN]; group
                _ = 1 := by rw [hU, mul_one, hM]
            rw [h1, one_mul]
    calc M * N * X * Y = M * N * X * Y * (M * N * X)⁻¹ * (M * N * X) := by group
      _ = Y * (M * N * X) := by rw [key]

theorem caseC3_commutator_commute {K : Type*} [Group K] {X Y : K} (hX : X * X = 1)
    (hY : Y * Y = 1) (hw : X * Y * X⁻¹ * Y⁻¹ * (X * Y * X⁻¹ * Y⁻¹) = 1) :
    X * Y * X⁻¹ * Y⁻¹ * Y = Y * (X * Y * X⁻¹ * Y⁻¹) ∧
      X * Y * X⁻¹ * Y⁻¹ * X = X * (X * Y * X⁻¹ * Y⁻¹) := by
  have hXi : X⁻¹ = X := inv_eq_of_mul_eq_one_right hX
  have hYi : Y⁻¹ = Y := inv_eq_of_mul_eq_one_right hY
  rw [hXi, hYi] at hw ⊢
  constructor
  · calc X * Y * X * Y * Y = X * Y * X := by rw [mul_assoc (X * Y * X), hY, mul_one]
      _ = X⁻¹ * Y⁻¹ * X⁻¹ := by rw [hXi, hYi]
      _ = (X * Y * X)⁻¹ := by group
      _ = (X * Y * X)⁻¹ * (X * Y * X * Y * (X * Y * X * Y)) := by rw [hw, mul_one]
      _ = Y * (X * Y * X * Y) := by group
  · calc X * Y * X * Y * X = (X * Y * X * Y * (X * Y * X * Y)) * (Y * X * Y)⁻¹ := by group
      _ = (Y * X * Y)⁻¹ := by rw [hw, one_mul]
      _ = Y⁻¹ * X⁻¹ * Y⁻¹ := by group
      _ = Y * X * Y := by rw [hXi, hYi]
      _ = X * (X * Y * X * Y) := by
          rw [show X * (X * Y * X * Y) = X * X * Y * X * Y by group, hX, one_mul]

variable {G : Type} [Group G] [Finite G] {T Q P₁ S : Subgroup G} {e u y x : G}

namespace CaseC3Top

omit [Finite G] in
theorem of_mul (hs : CaseC3Top T Q P₁ S e u y x) {w : G} (hw : w ∈ T) :
    CaseC3Top T Q P₁ S e u y (w * x) where
  toCaseC3 := hs.toCaseC3
  le_top := hs.le_top
  isPGroup_top := hs.isPGroup_top
  top_le_normalizer := hs.top_le_normalizer
  max := hs.max
  mem_top := S.mul_mem (hs.le_top hw) hs.mem_top
  not_mem_bot := fun h' => hs.not_mem_bot (by simpa using T.mul_mem (T.inv_mem hw) h')
  swap_right := fun p hp => by
    rw [show w * x * p * (w * x)⁻¹ = w * (x * p * x⁻¹) * w⁻¹ by group]
    exact hs.partC.normal_left w hw _ (hs.swap_right p hp)
  swap_left := fun q hq => by
    rw [show w * x * q * (w * x)⁻¹ = w * (x * q * x⁻¹) * w⁻¹ by group]
    exact hs.partC.normal_right w hw _ (hs.swap_left q hq)
  mul_mem := fun s hsS hsT => by
    rw [← mul_assoc]
    exact hs.mul_mem (s * w) (S.mul_mem hsS (hs.le_top hw))
      (fun h' => hsT (by simpa using T.mul_mem h' (T.inv_mem hw)))

variable (Z : Subgroup G) [Z.Normal]

theorem mk_conj_conj_moved (hs : CaseC3Top T Q P₁ S e u y x) (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e)
    {v : G} (hvfix : ∀ w ∈ Q, (y * w * y⁻¹ = w ∨ y * w * y⁻¹ = w * e) →
      w = 1 ∨ w = e ∨ w = v ∨ w = v * e) {m : G} (hm : m ∈ P₁)
    (hm1 : y * m * y⁻¹ ≠ m) (hm2 : y * m * y⁻¹ ≠ m * e) :
    (y : G ⧸ Z) * ((x * m * x⁻¹ : G) : G ⧸ Z) * (y : G ⧸ Z)⁻¹ =
      (v : G ⧸ Z) * ((x * m * x⁻¹ : G) : G ⧸ Z) := by
  have he1 : ((e : G) : G ⧸ Z) = 1 := (QuotientGroup.eq_one_iff e).mpr ((hZ e).mpr (Or.inr rfl))
  have hτM : (y : G ⧸ Z) * (m : G ⧸ Z) * (y : G ⧸ Z)⁻¹ = (u : G ⧸ Z) * (m : G ⧸ Z) := by
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rcases hs.toCaseC3.conj_moved hm hm1 hm2 with h1 | h1 <;> rw [h1]
    · rw [QuotientGroup.mk_mul]
    · rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, he1, mul_one]
  have hσU : (x : G ⧸ Z) * (u : G ⧸ Z) * (x : G ⧸ Z)⁻¹ = (v : G ⧸ Z) := by
    rw [← hs.mk_conj_self Z hZ hvfix, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv]
  have h1 := hs.mk_conj_conj_comm Z hZ (Subgroup.mem_sup_right hm)
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1 ⊢
  rw [← h1, hτM, ← hσU]
  group

theorem exists_normalized (hs : CaseC3Top T Q P₁ S e u y x) (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e)
    (hx2 : x * x ∈ Q ⊔ P₁) :
    ∃ x', CaseC3Top T Q P₁ S e u y x' ∧ ((x' * x' : G) : G ⧸ Z) = 1 ∧
      (x' : G ⧸ Z) * (y : G ⧸ Z) = (y : G ⧸ Z) * (x' : G ⧸ Z) := by
  have hc := hs.partC
  obtain ⟨φ⟩ := hs.quaternion_right
  obtain ⟨v, hvQ, hvv, hyv, hvfix⟩ := hs.toCaseC3.exists_inv_conj_left
  obtain ⟨m, hm, hm1, hm2⟩ := hs.moved
  have he1 : ((e : G) : G ⧸ Z) = 1 := (QuotientGroup.eq_one_iff e).mpr ((hZ e).mpr (Or.inr rfl))
  have hZW := hc.le_sup_of_mem_iff Z hZ
  have hW : ∀ {g : G}, g ∈ Q ⊔ P₁ → (g : G ⧸ Z) ∈ (Q ⊔ P₁).map (QuotientGroup.mk' Z) :=
    fun hg => Subgroup.mem_map_of_mem _ hg
  have hcm : ∀ {a b : G ⧸ Z}, a ∈ (Q ⊔ P₁).map (QuotientGroup.mk' Z) →
      b ∈ (Q ⊔ P₁).map (QuotientGroup.mk' Z) → Commute a b :=
    fun ha hb => hc.mul_comm_of_mem_map_sup Z φ hZ ha hb
  have hsq : ∀ {a : G ⧸ Z}, a ∈ (Q ⊔ P₁).map (QuotientGroup.mk' Z) → a * a = 1 := fun ha => by
    have := hc.pow_two_eq_one_of_mem_map_sup Z φ hZ ha
    rwa [pow_two] at this
  obtain ⟨q, hq, p, hp, hqp⟩ := hc.mem_sup_iff.mp hx2
  have hxq := hs.swap_left q hq
  have hxp := hs.swap_right p hp
  have h1 : (x * p * x⁻¹) * (x * q * x⁻¹) = q * p * 1 := by
    rw [mul_one, hc.commute _ hxp _ hxq,
      show x * q * x⁻¹ * (x * p * x⁻¹) = x * (q * p) * x⁻¹ by group, hqp]
    group
  obtain ⟨hpq, -⟩ := hc.eq_of_mul_eq_mul hq hp hxp hxq (Or.inl rfl) h1
  have hpq' : ((x * p * x⁻¹ : G) : G ⧸ Z) = (q : G ⧸ Z) := by
    rcases hpq with h2 | h2 <;> rw [h2]
    rw [QuotientGroup.mk_mul, he1, mul_one]
  obtain ⟨x₁, hx₁⟩ : ∃ x₁, x₁ = p * x := ⟨_, rfl⟩
  have hs₁ : CaseC3Top T Q P₁ S e u y x₁ := hx₁ ▸ hs.of_mul (hc.right_le hp)
  have hX : (x₁ : G ⧸ Z) * (x₁ : G ⧸ Z) = 1 := by
    rw [← QuotientGroup.mk_mul, hx₁, show p * x * (p * x) = p * (x * p * x⁻¹) * (x * x) by group,
      ← hqp, QuotientGroup.mk_mul, QuotientGroup.mk_mul, hpq', QuotientGroup.mk_mul,
      show (p : G ⧸ Z) * (q : G ⧸ Z) * ((q : G ⧸ Z) * (p : G ⧸ Z)) =
        (p : G ⧸ Z) * ((q : G ⧸ Z) * (q : G ⧸ Z)) * (p : G ⧸ Z) by group,
      hsq (hW (Subgroup.mem_sup_left hq)), mul_one, hsq (hW (Subgroup.mem_sup_right hp))]
  have hy2 : (y : G ⧸ Z) * (y : G ⧸ Z) = 1 := by
    rw [← QuotientGroup.mk_mul, hs.mul_self, he1]
  have hw₀W : (x₁ : G ⧸ Z) * (y : G ⧸ Z) * (x₁ : G ⧸ Z)⁻¹ * (y : G ⧸ Z)⁻¹ ∈
      (Q ⊔ P₁).map (QuotientGroup.mk' Z) := by
    have hN := hs₁.mem_normalizer
    have ha : x₁ * y⁻¹ * x₁⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hN _).mp (T.inv_mem hs.mem)
    have hyW : y⁻¹ ∉ Q ⊔ P₁ := fun h' => hs.not_mem (by simpa using (Q ⊔ P₁).inv_mem h')
    have haW : x₁ * y⁻¹ * x₁⁻¹ ∉ Q ⊔ P₁ := fun h' => hyW (by
      have := hc.conj_mem_sup_of_mem_normalizer φ (Subgroup.inv_mem _ hN) h'
      rwa [show x₁⁻¹ * (x₁ * y⁻¹ * x₁⁻¹) * x₁⁻¹⁻¹ = y⁻¹ by group] at this)
    have := hc.inv_mul_mem _ ha _ (T.inv_mem hs.mem) haW hyW
    rw [show (x₁ * y⁻¹ * x₁⁻¹)⁻¹ * y⁻¹ = x₁ * y * x₁⁻¹ * y⁻¹ by group] at this
    have h' := hW this
    simpa only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] using h'
  obtain ⟨hw₀Y, hw₀X⟩ := caseC3_commutator_commute hX hy2 (hsq hw₀W)
  have hZP : Z ≤ P₁ := fun g hg => by
    rcases (hZ g).mp hg with rfl | rfl
    exacts [P₁.one_mem, hc.mem_right]
  have hZQ : Z ≤ Q := fun g hg => by
    rcases (hZ g).mp hg with rfl | rfl
    exacts [Q.one_mem, hc.mem_left]
  have hcases : (x₁ : G ⧸ Z) * (y : G ⧸ Z) * (x₁ : G ⧸ Z)⁻¹ * (y : G ⧸ Z)⁻¹ = 1 ∨
      (x₁ : G ⧸ Z) * (y : G ⧸ Z) * (x₁ : G ⧸ Z)⁻¹ * (y : G ⧸ Z)⁻¹ =
        (u : G ⧸ Z) * (v : G ⧸ Z) := by
    rcases (hs.toCaseC3.mem_map_sup_inf_centralizer_iff Z hZ hvQ hvv hyv hvfix _).mp
        ⟨hw₀W, Subgroup.mem_centralizer_singleton_iff.mpr hw₀Y⟩ with h2 | h2 | h2 | h2
    · exact Or.inl h2
    · left
      rw [h2] at hw₀X ⊢
      exact hc.mk_eq_one_of_commute Z hZ hZP (fun g hg hg' => hc.mem_inf g hg' hg) hc.self_mem
        (hs₁.swap_right u hc.self_mem) hw₀X
    · left
      rw [h2] at hw₀X ⊢
      exact hc.mk_eq_one_of_commute Z hZ hZQ hc.mem_inf hvQ (hs₁.swap_left v hvQ) hw₀X
    · exact Or.inr h2
  rcases hcases with h2 | h2
  · refine ⟨x₁, hs₁, by rw [QuotientGroup.mk_mul, hX], ?_⟩
    have h3 := h2
    calc (x₁ : G ⧸ Z) * (y : G ⧸ Z) =
          (x₁ : G ⧸ Z) * (y : G ⧸ Z) * (x₁ : G ⧸ Z)⁻¹ * (y : G ⧸ Z)⁻¹ * ((y : G ⧸ Z) *
            (x₁ : G ⧸ Z)) := by group
      _ = (y : G ⧸ Z) * (x₁ : G ⧸ Z) := by rw [h3, one_mul]
  · have hmn : m * (x₁ * m * x₁⁻¹) ∈ T :=
      hc.sup_le ((Q ⊔ P₁).mul_mem (Subgroup.mem_sup_right hm)
        (hs₁.conj_mem_sup (Subgroup.mem_sup_right hm)))
    have hXY : (x₁ : G ⧸ Z) * (y : G ⧸ Z) * (x₁ : G ⧸ Z)⁻¹ =
        (u : G ⧸ Z) * (v : G ⧸ Z) * (y : G ⧸ Z) := by
      rw [← h2]
      group
    have hXM : (x₁ : G ⧸ Z) * (m : G ⧸ Z) * (x₁ : G ⧸ Z)⁻¹ = ((x₁ * m * x₁⁻¹ : G) : G ⧸ Z) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have hYM : (y : G ⧸ Z) * (m : G ⧸ Z) * (y : G ⧸ Z)⁻¹ = (u : G ⧸ Z) * (m : G ⧸ Z) := by
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      rcases hs.toCaseC3.conj_moved hm hm1 hm2 with h3 | h3 <;> rw [h3]
      · rw [QuotientGroup.mk_mul]
      · rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, he1, mul_one]
    have hmW : m ∈ Q ⊔ P₁ := Subgroup.mem_sup_right hm
    obtain ⟨hsq', hcomm⟩ := caseC3_normalize_step hX hXY hXM hYM
      (hs₁.mk_conj_conj_moved Z hZ hvfix hm hm1 hm2)
      (hcm (hW (hs₁.conj_mem_sup hmW)) (hW (Subgroup.mem_sup_right hc.self_mem)))
      (hsq (hW hmW)) (hsq (hW (hs₁.conj_mem_sup hmW)))
      (hsq (hW (Subgroup.mem_sup_right hc.self_mem))) (hsq (hW (Subgroup.mem_sup_left hvQ)))
    refine ⟨m * (x₁ * m * x₁⁻¹) * x₁, hs₁.of_mul hmn, ?_, ?_⟩
    · simp only [QuotientGroup.mk_mul] at hsq' ⊢
      exact hsq'
    · simp only [QuotientGroup.mk_mul] at hcomm ⊢
      exact hcomm

end CaseC3Top

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
