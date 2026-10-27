module

public import CFSG.GH74.GLS.Stage4.HexCScalar

public noncomputable section

open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

section NatQuotSec

variable {F : Type*} [Field F] {G : Type*} [Group G]

structure NatQuot (φ : SL2 F →* G) (Q N A B : Subgroup G) : Prop where
  N_le : N ≤ Q
  A_le : A ≤ Q
  B_le : B ≤ Q
  N_norm : ∀ q ∈ Q, ∀ n ∈ N, q * n * q⁻¹ ∈ N
  commAA : ∀ x ∈ A, ∀ y ∈ A, ⁅x, y⁆ ∈ N
  commBB : ∀ x ∈ B, ∀ y ∈ B, ⁅x, y⁆ ∈ N
  commAB : ∀ x ∈ A, ∀ y ∈ B, ⁅x, y⁆ ∈ N
  UN : ∀ c, ∀ n ∈ N, φ (sl2U c) * n * (φ (sl2U c))⁻¹ ∈ N
  LN : ∀ c, ∀ n ∈ N, φ (sl2L c) * n * (φ (sl2L c))⁻¹ ∈ N
  uA : ∀ c, ∀ a ∈ A, ⁅φ (sl2U c), a⁆ ∈ N
  lB : ∀ c, ∀ b ∈ B, ⁅φ (sl2L c), b⁆ ∈ N
  uB : ∀ c, ∀ b ∈ B, ∃ a ∈ A, a⁻¹ * ⁅φ (sl2U c), b⁆ ∈ N
  lA : ∀ c, ∀ a ∈ A, ∃ b ∈ B, b⁻¹ * ⁅φ (sl2L c), a⁆ ∈ N
  ndU : ∀ b ∈ B, ⁅φ (sl2U 1), b⁆ ∈ N → b ∈ N
  ndL : ∀ a ∈ A, ⁅φ (sl2L 1), a⁆ ∈ N → a ∈ N

namespace NatQuot

variable {φ : SL2 F →* G} {Q N A B : Subgroup G} (h : NatQuot φ Q N A B)

theorem phi_neg_U (c : F) : φ (sl2U (-c)) = (φ (sl2U c))⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← map_mul, ← sl2U_add, neg_add_cancel, sl2U_zero, map_one]

theorem phi_neg_L (c : F) : φ (sl2L (-c)) = (φ (sl2L c))⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← map_mul, ← sl2L_add, neg_add_cancel, sl2L_zero, map_one]

include h in
theorem range_mem_normalizer (g : SL2 F) : φ g ∈ Subgroup.normalizer (N : Set G) := by
  refine sl2_hom_mem φ (Subgroup.normalizer (N : Set G)) (fun c => ?_) (fun c => ?_) g
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => h.UN c x hx, fun hx => ?_⟩
    have := h.UN (-c) _ hx
    have e : φ (sl2U (-c)) * (φ (sl2U c) * x * (φ (sl2U c))⁻¹) * (φ (sl2U (-c)))⁻¹ = x := by
      rw [phi_neg_U]; group
    rwa [e] at this
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => h.LN c x hx, fun hx => ?_⟩
    have := h.LN (-c) _ hx
    have e : φ (sl2L (-c)) * (φ (sl2L c) * x * (φ (sl2L c))⁻¹) * (φ (sl2L (-c)))⁻¹ = x := by
      rw [phi_neg_L]; group
    rwa [e] at this

include h in
theorem ambient_le_normalizer : Q ⊔ φ.range ≤ Subgroup.normalizer (N : Set G) := by
  refine sup_le (fun q hq => ?_) ?_
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => h.N_norm q hq x hx, fun hx => ?_⟩
    have := h.N_norm q⁻¹ (Q.inv_mem hq) _ hx
    simpa [mul_assoc] using this
  · rintro _ ⟨g, rfl⟩
    exact h.range_mem_normalizer g

include h in
theorem normal : (N.subgroupOf (Q ⊔ φ.range)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (h.N_le.trans le_sup_left)]
  intro n t hn ht
  exact (Subgroup.mem_normalizer_iff.1 (h.ambient_le_normalizer ht) n).1 hn

@[expose] def Gq (_h : NatQuot φ Q N A B) : Type _ :=
  ↥(Q ⊔ φ.range) ⧸ N.subgroupOf (Q ⊔ φ.range)

noncomputable instance instGroupGq (h : NatQuot φ Q N A B) : Group h.Gq :=
  haveI := h.normal
  inferInstanceAs (Group (↥(Q ⊔ φ.range) ⧸ N.subgroupOf (Q ⊔ φ.range)))

@[expose] def π (h : NatQuot φ Q N A B) : ↥(Q ⊔ φ.range) →* h.Gq :=
  haveI := h.normal
  QuotientGroup.mk' (N.subgroupOf (Q ⊔ φ.range))

include h in
theorem π_eq_iff (x y : ↥(Q ⊔ φ.range)) : h.π x = h.π y ↔ (x : G)⁻¹ * (y : G) ∈ N := by
  have := h.normal
  show (QuotientGroup.mk x : ↥(Q ⊔ φ.range) ⧸ N.subgroupOf (Q ⊔ φ.range)) = QuotientGroup.mk y ↔ _
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  rfl

@[expose] def Aq : Subgroup h.Gq := (A.subgroupOf (Q ⊔ φ.range)).map h.π

@[expose] def Bq : Subgroup h.Gq := (B.subgroupOf (Q ⊔ φ.range)).map h.π

theorem mem_Aq {x : h.Gq} : x ∈ h.Aq ↔ ∃ y : ↥(Q ⊔ φ.range), (y : G) ∈ A ∧ h.π y = x := by
  simp only [Aq, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem mem_Bq {x : h.Gq} : x ∈ h.Bq ↔ ∃ y : ↥(Q ⊔ φ.range), (y : G) ∈ B ∧ h.π y = x := by
  simp only [Bq, Subgroup.mem_map, Subgroup.mem_subgroupOf]

@[expose] def φq : SL2 F →* h.Gq :=
  h.π.comp (φ.codRestrict (Q ⊔ φ.range) (fun g => Subgroup.mem_sup_right ⟨g, rfl⟩))

theorem φq_apply (g : SL2 F) :
    h.φq g = h.π ⟨φ g, Subgroup.mem_sup_right ⟨g, rfl⟩⟩ := rfl

theorem commut_mem_of {x y : G} (hxy : ⁅y⁻¹, x⁻¹⁆ ∈ N) : (x * y)⁻¹ * (y * x) ∈ N := by
  have e : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by simp only [commutatorElement_def]; group
  rwa [e]

include h in
theorem conj_mem {g x : G} (hx : x ∈ Q) (hk : ⁅g, x⁆ ∈ N) : x⁻¹ * (g * x * g⁻¹) ∈ N := by
  have := h.N_norm (x⁻¹) (Q.inv_mem hx) _ hk
  have e : x⁻¹ * ⁅g, x⁆ * (x⁻¹)⁻¹ = x⁻¹ * (g * x * g⁻¹) := by
    simp only [commutatorElement_def]; group
  rwa [e] at this

include h in
theorem natPair : NatPair h.φq h.Aq h.Bq where
  commA := by
    intro a ha a' ha'
    obtain ⟨y, hy, rfl⟩ := (mem_Aq h).1 ha
    obtain ⟨y', hy', rfl⟩ := (mem_Aq h).1 ha'
    rw [← map_mul, ← map_mul, π_eq_iff]
    exact commut_mem_of (h.commAA _ (A.inv_mem hy') _ (A.inv_mem hy))
  commB := by
    intro a ha a' ha'
    obtain ⟨y, hy, rfl⟩ := (mem_Bq h).1 ha
    obtain ⟨y', hy', rfl⟩ := (mem_Bq h).1 ha'
    rw [← map_mul, ← map_mul, π_eq_iff]
    exact commut_mem_of (h.commBB _ (B.inv_mem hy') _ (B.inv_mem hy))
  commAB := by
    intro a ha b hb
    obtain ⟨y, hy, rfl⟩ := (mem_Aq h).1 ha
    obtain ⟨y', hy', rfl⟩ := (mem_Bq h).1 hb
    rw [← map_mul, ← map_mul, π_eq_iff]
    refine commut_mem_of ?_
    rw [← commutatorElement_inv]
    exact N.inv_mem (h.commAB _ (A.inv_mem hy) _ (B.inv_mem hy'))
  uA := by
    intro c a ha
    obtain ⟨y, hy, rfl⟩ := (mem_Aq h).1 ha
    rw [φq_apply, ← map_inv, ← map_mul, ← map_mul, π_eq_iff]
    have hk := N.inv_mem (h.conj_mem (h.A_le hy) (h.uA c _ hy))
    have e : ((y : G)⁻¹ * (φ (sl2U c) * y * (φ (sl2U c))⁻¹))⁻¹ =
        (φ (sl2U c) * y * (φ (sl2U c))⁻¹)⁻¹ * y := by group
    rw [e] at hk
    exact hk
  lB := by
    intro c b hb
    obtain ⟨y, hy, rfl⟩ := (mem_Bq h).1 hb
    rw [φq_apply, ← map_inv, ← map_mul, ← map_mul, π_eq_iff]
    have hk := N.inv_mem (h.conj_mem (h.B_le hy) (h.lB c _ hy))
    have e : ((y : G)⁻¹ * (φ (sl2L c) * y * (φ (sl2L c))⁻¹))⁻¹ =
        (φ (sl2L c) * y * (φ (sl2L c))⁻¹)⁻¹ * y := by group
    rw [e] at hk
    exact hk
  uB := by
    intro c b hb
    obtain ⟨y, hy, rfl⟩ := (mem_Bq h).1 hb
    obtain ⟨a, ha, hk⟩ := h.uB c _ hy
    refine (mem_Aq h).2 ⟨⟨a, Subgroup.mem_sup_left (h.A_le ha)⟩, ha, ?_⟩
    rw [φq_apply, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, π_eq_iff]
    simpa [commutatorElement_def] using hk
  lA := by
    intro c a ha
    obtain ⟨y, hy, rfl⟩ := (mem_Aq h).1 ha
    obtain ⟨b, hb, hk⟩ := h.lA c _ hy
    refine (mem_Bq h).2 ⟨⟨b, Subgroup.mem_sup_left (h.B_le hb)⟩, hb, ?_⟩
    rw [φq_apply, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, π_eq_iff]
    simpa [commutatorElement_def] using hk
  ndU := by
    intro b hb hfix
    obtain ⟨y, hy, rfl⟩ := (mem_Bq h).1 hb
    rw [φq_apply, ← map_inv, ← map_mul, ← map_mul, π_eq_iff] at hfix
    have hfix' : (φ (sl2U 1) * y * (φ (sl2U 1))⁻¹)⁻¹ * (y : G) ∈ N := hfix
    have hk := h.N_norm (y : G) (h.B_le hy) _ (N.inv_mem hfix')
    have e : (y : G) * ((φ (sl2U 1) * y * (φ (sl2U 1))⁻¹)⁻¹ * y)⁻¹ * (y : G)⁻¹ =
        ⁅φ (sl2U 1), (y : G)⁆ := by
      simp only [commutatorElement_def]; group
    rw [e] at hk
    have hyN := h.ndU _ hy hk
    rw [← map_one h.π, π_eq_iff]
    simpa using N.inv_mem hyN
  ndL := by
    intro a ha hfix
    obtain ⟨y, hy, rfl⟩ := (mem_Aq h).1 ha
    rw [φq_apply, ← map_inv, ← map_mul, ← map_mul, π_eq_iff] at hfix
    have hfix' : (φ (sl2L 1) * y * (φ (sl2L 1))⁻¹)⁻¹ * (y : G) ∈ N := hfix
    have hk := h.N_norm (y : G) (h.A_le hy) _ (N.inv_mem hfix')
    have e : (y : G) * ((φ (sl2L 1) * y * (φ (sl2L 1))⁻¹)⁻¹ * y)⁻¹ * (y : G)⁻¹ =
        ⁅φ (sl2L 1), (y : G)⁆ := by
      simp only [commutatorElement_def]; group
    rw [e] at hk
    have hyN := h.ndL _ hy hk
    rw [← map_one h.π, π_eq_iff]
    simpa using N.inv_mem hyN

include h in
theorem eq_of_π_eq_of_mem {S : Subgroup G} (hS : ∀ x ∈ S, x ∈ N → x = 1) {y y' : ↥(Q ⊔ φ.range)}
    (hy : (y : G) ∈ S) (hy' : (y' : G) ∈ S) (he : h.π y = h.π y') : (y : G) = y' := by
  have hN := (h.π_eq_iff y y').1 he
  have hS1 : (y : G)⁻¹ * y' ∈ S := S.mul_mem (S.inv_mem hy) hy'
  have := hS _ hS1 hN
  exact inv_mul_eq_one.1 this

include h in
theorem exists_coords [Finite F] {F' : Type*} [Field F'] (xB : F' → G)
    (hadd : ∀ y y', xB (y + y') = xB y * xB y') (hinj : Function.Injective xB)
    (hmem : ∀ y, xB y ∈ B) (hsurj : ∀ b ∈ B, ∃ y, xB y = b) (a : Fˣ → F')
    (ha : ∀ (t : Fˣ) (y : F'), φ (sl2D t) * xB y * (φ (sl2D t))⁻¹ = xB (a t * y))
    (hcard : Nat.card F = Nat.card F') (hcardA : Nat.card A = Nat.card F)
    (hBN : ∀ x ∈ B, x ∈ N → x = 1) (hAN : ∀ x ∈ A, x ∈ N → x = 1)
    (hDA : ∀ (t : Fˣ), ∀ x ∈ A, φ (sl2D t) * x * (φ (sl2D t))⁻¹ ∈ A) :
    ∃ x₂ x₄ : F → G, (∀ c d, x₂ (c + d) = x₂ c * x₂ d) ∧ Function.Injective x₂ ∧
      (∀ d, x₂ d ∈ B) ∧ (∀ b ∈ B, ∃ d, x₂ d = b) ∧
      (∀ c d, x₄ (c + d) = x₄ c * x₄ d) ∧ Function.Injective x₄ ∧ (∀ d, x₄ d ∈ A) ∧
      (∀ b ∈ A, ∃ d, x₄ d = b) ∧ (∀ c d, (x₄ (c * d))⁻¹ * ⁅φ (sl2U c), x₂ d⁆ ∈ N) ∧
      (∀ (t : Fˣ) d, φ (sl2D t) * x₂ d * (φ (sl2D t))⁻¹ = x₂ ((t : F)⁻¹ * d)) ∧
      (∀ (t : Fˣ) d, φ (sl2D t) * x₄ d * (φ (sl2D t))⁻¹ = x₄ ((t : F) * d)) := by
  classical
  have hBT : ∀ x ∈ B, x ∈ Q ⊔ φ.range := fun x hx => Subgroup.mem_sup_left (h.B_le hx)
  have hAT : ∀ x ∈ A, x ∈ Q ⊔ φ.range := fun x hx => Subgroup.mem_sup_left (h.A_le hx)
  let xB' : F' → h.Gq := fun y => h.π ⟨xB y, hBT _ (hmem y)⟩
  have hadd' : ∀ y y', xB' (y + y') = xB' y * xB' y' := by
    intro y y'
    show h.π _ = h.π _ * h.π _
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    simp [hadd]
  have hinj' : Function.Injective xB' := by
    intro y y' hy
    exact hinj (h.eq_of_π_eq_of_mem hBN (hmem y) (hmem y') hy)
  have hmem' : ∀ y, xB' y ∈ h.Bq := fun y => (mem_Bq h).2 ⟨_, hmem y, rfl⟩
  have hsurj' : ∀ b ∈ h.Bq, ∃ y, xB' y = b := by
    intro b hb
    obtain ⟨z, hz, rfl⟩ := (mem_Bq h).1 hb
    obtain ⟨y, hy⟩ := hsurj _ hz
    exact ⟨y, by show h.π _ = _; congr 1; exact Subtype.ext hy⟩
  have ha' : ∀ (t : Fˣ) (y : F'), h.φq (sl2D t) * xB' y * (h.φq (sl2D t))⁻¹ = xB' (a t * y) := by
    intro t y
    show h.φq (sl2D t) * h.π _ * (h.φq (sl2D t))⁻¹ = h.π _
    rw [φq_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simpa using ha t y
  have hπA : ∀ {y y' : ↥(Q ⊔ φ.range)}, (y : G) ∈ A → (y' : G) ∈ A → h.π y = h.π y' →
      (y : G) = y' := fun hy hy' he => h.eq_of_π_eq_of_mem hAN hy hy' he
  have hπB : ∀ {y y' : ↥(Q ⊔ φ.range)}, (y : G) ∈ B → (y' : G) ∈ B → h.π y = h.π y' →
      (y : G) = y' := fun hy hy' he => h.eq_of_π_eq_of_mem hBN hy hy' he
  have hcardA' : Nat.card h.Aq = Nat.card F := by
    rw [← hcardA]
    symm
    refine Nat.card_congr (Equiv.ofBijective
      (fun x : ↥A => (⟨h.π ⟨x, hAT _ x.2⟩, (mem_Aq h).2 ⟨_, x.2, rfl⟩⟩ : ↥h.Aq)) ⟨?_, ?_⟩)
    · intro x x' hx
      have := hπA (y := ⟨x, hAT _ x.2⟩) (y' := ⟨x', hAT _ x'.2⟩) x.2 x'.2
        (congrArg Subtype.val hx)
      exact Subtype.ext this
    · rintro ⟨b, hb⟩
      obtain ⟨z, hz, rfl⟩ := (mem_Aq h).1 hb
      exact ⟨⟨z, hz⟩, Subtype.ext rfl⟩
  obtain ⟨x₂', x₄', h2add, h2inj, h2mem, h2surj, h4add, h4inj, h4mem, h4surj, hrel, hw2, hw4⟩ :=
    h.natPair.exists_coords xB' hadd' hinj' hmem' hsurj' a ha' hcard hcardA'
  have hl2 : ∀ d, ∃ z : ↥(Q ⊔ φ.range), (z : G) ∈ B ∧ h.π z = x₂' d := fun d =>
    (mem_Bq h).1 (h2mem d)
  have hl4 : ∀ d, ∃ z : ↥(Q ⊔ φ.range), (z : G) ∈ A ∧ h.π z = x₄' d := fun d =>
    (mem_Aq h).1 (h4mem d)
  choose z₂ hz₂B hz₂π using hl2
  choose z₄ hz₄A hz₄π using hl4
  have hDB : ∀ (t : Fˣ), ∀ x ∈ B, φ (sl2D t) * x * (φ (sl2D t))⁻¹ ∈ B := by
    intro t x hx
    obtain ⟨y, rfl⟩ := hsurj x hx
    rw [ha t y]
    exact hmem _
  have hDmem : ∀ (t : Fˣ), φ (sl2D t) ∈ Q ⊔ φ.range := fun t =>
    Subgroup.mem_sup_right ⟨sl2D t, rfl⟩
  refine ⟨fun d => (z₂ d : G), fun d => (z₄ d : G), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c d
    have : h.π (z₂ (c + d)) = h.π (z₂ c * z₂ d) := by
      rw [map_mul, hz₂π, hz₂π, hz₂π, h2add]
    exact hπB (hz₂B _) (B.mul_mem (hz₂B _) (hz₂B _)) this
  · intro c d hcd
    apply h2inj
    rw [← hz₂π, ← hz₂π, Subtype.ext hcd]
  · exact hz₂B
  · intro b hb
    obtain ⟨d, hd⟩ := h2surj (h.π ⟨b, hBT _ hb⟩) ((mem_Bq h).2 ⟨_, hb, rfl⟩)
    have hd' : h.π (z₂ d) = h.π ⟨b, hBT _ hb⟩ := by rw [hz₂π, hd]
    exact ⟨d, hπB (y' := ⟨b, hBT _ hb⟩) (hz₂B d) hb hd'⟩
  · intro c d
    have : h.π (z₄ (c + d)) = h.π (z₄ c * z₄ d) := by
      rw [map_mul, hz₄π, hz₄π, hz₄π, h4add]
    exact hπA (hz₄A _) (A.mul_mem (hz₄A _) (hz₄A _)) this
  · intro c d hcd
    apply h4inj
    rw [← hz₄π, ← hz₄π, Subtype.ext hcd]
  · exact hz₄A
  · intro b hb
    obtain ⟨d, hd⟩ := h4surj (h.π ⟨b, hAT _ hb⟩) ((mem_Aq h).2 ⟨_, hb, rfl⟩)
    have hd' : h.π (z₄ d) = h.π ⟨b, hAT _ hb⟩ := by rw [hz₄π, hd]
    exact ⟨d, hπA (y' := ⟨b, hAT _ hb⟩) (hz₄A d) hb hd'⟩
  · intro c d
    have h1 := hrel c d
    rw [← hz₂π, ← hz₄π, φq_apply, ← map_commutatorElement] at h1
    exact (h.π_eq_iff _ _).1 h1.symm
  · intro t d
    have h1 := hw2 t d
    rw [← hz₂π, ← hz₂π, φq_apply, ← map_inv, ← map_mul, ← map_mul] at h1
    refine hπB ?_ ?_ h1
    · exact hDB t _ (hz₂B d)
    · exact hz₂B _
  · intro t d
    have h1 := hw4 t d
    rw [← hz₄π, ← hz₄π, φq_apply, ← map_inv, ← map_mul, ← map_mul] at h1
    refine hπA ?_ ?_ h1
    · exact hDA t _ (hz₄A d)
    · exact hz₄A _

end NatQuot

end NatQuotSec

end CFSG.GH74.GLS.Stage4.Hex
