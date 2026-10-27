module

public import CFSG.CGT.PushingUpLit.T2KR.Fus613Rel
public import CFSG.CGT.PushingUpLit.T2KR.Fus613Adj
public import CFSG.CGT.PushingUpLit.T2KR.Fus613Struct

public section

namespace CFSG.CGT.PushingUpLit.T2KR.P613

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.T2K CFSG.CGT.Timmesfeld75
open scoped commutatorElement
open MData (QM)

variable {G : Type} [Group G] [Finite G] {L M : Subgroup G} {n : ℕ}
  {H : MData G L M n} {T' : Subgroup G} {x r b : G} {e₁ e₂ : Fin 2 → Fq n} {ω : Fq n}

theorem f4_cases' {F : Type} [Field F] [CharP F 2] [Fintype F] (hF : Fintype.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) (y : F) : y = 0 ∨ y = 1 ∨ y = ω ∨ y = 1 + ω := by
  rcases f4_cases hF y with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · rcases root_cases hω h with h' | h'
    · exact Or.inr (Or.inr (Or.inl h'))
    · right; right; right
      rw [h', root_sq hω, add_comm]

theorem ringEquiv_mul_eq_one {F : Type} [Field F] [CharP F 2] [Fintype F]
    (hF : Fintype.card F = 4) {ω : F} (hω : ω ^ 2 + ω + 1 = 0) {σ τ : F ≃+* F} (hσ : σ ≠ 1)
    (hτ : τ ≠ 1) : σ * τ = 1 := by
  have h1 := frob_eq_sq hF σ hσ hω
  have h2 := frob_eq_sq hF τ hτ hω
  have hq : (ω ^ 2) ^ 2 = ω := by linear_combination ω * root_cube hω
  refine RingEquiv.ext fun y => ?_
  show σ (τ y) = y
  rcases f4_cases hF y with h | h | h
  · rw [h]; simp
  · rw [h]; simp
  · rcases root_cases hω h with h' | h'
    · rw [h', h2, map_pow, h1, hq]
    · rw [h', map_pow, h2, hq, h1]

structure UData (H : MData G L M n) (T' : Subgroup G) (r b : G) (e₁ e₂ : Fin 2 → Fq n)
    (ω : Fq n) (u : G) : Prop where
  mem_L : u ∈ L
  mem_T : u ∈ T'
  sq : u * u = 1
  comm : r * u = u * r
  tv : IsTv H e₁ e₂ u ω
  conj : b * u * b⁻¹ = r * u

section Final

variable (c : Cfg H T' x r b) (bs : Basis H r b e₁ e₂ ω) {u : G} (hu : UData H T' r b e₁ e₂ ω u)

include c bs hu in
theorem Cfg.S_le_T' :
    Model613.S613 (H.vec e₁) (H.vec (ω • e₁)) (H.vec e₂) (H.vec (ω • e₂)) x r u b ≤ T' := by
  rw [Model613.S613, Subgroup.closure_le]
  have hV : ∀ w : Fin 2 → Fq n, H.vec w ∈ T' := fun w => (c.blockU_le_N0 (H.vec_mem w)).1
  rintro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hV _
  · exact hV _
  · exact hV _
  · exact hV _
  · exact c.Q_le c.x_Q
  · exact c.r_T
  · exact hu.mem_T
  · exact c.b_T

include c bs hu in
theorem Cfg.T'_le_S :
    T' ≤ Model613.S613 (H.vec e₁) (H.vec (ω • e₁)) (H.vec e₂) (H.vec (ω • e₂)) x r u b := by
  set S := Model613.S613 (H.vec e₁) (H.vec (ω • e₁)) (H.vec e₂) (H.vec (ω • e₂)) x r u b with hS
  have hω := bs.ω_eq
  have hF : Fintype.card (Fq n) = 4 := by rw [H.hcard, c.n_eq]; norm_num
  have hrtv : IsTv H e₁ e₂ r 1 := ⟨bs.r1, by rw [one_smul]; exact bs.r2⟩
  have hgen : ∀ g ∈ ({H.vec e₁, H.vec (ω • e₁), H.vec e₂, H.vec (ω • e₂), x, r, u, b} : Set G),
      g ∈ S := fun g hg => Subgroup.subset_closure hg
  have h0 : H.vec e₁ ∈ S := hgen _ (by simp)
  have h1 : H.vec (ω • e₁) ∈ S := hgen _ (by simp)
  have h2 : H.vec e₂ ∈ S := hgen _ (by simp)
  have h3 : H.vec (ω • e₂) ∈ S := hgen _ (by simp)
  have hx : x ∈ S := hgen _ (by simp)
  have hr : r ∈ S := hgen _ (by simp)
  have hu' : u ∈ S := hgen _ (by simp)
  have hb : b ∈ S := hgen _ (by simp)
  have hv1 : ∀ y : Fq n, H.vec (y • e₁) ∈ S := by
    intro y
    rcases f4_cases' hF hω y with h | h | h | h
    · rw [h, zero_smul, H.vec_zero]; exact S.one_mem
    · rw [h, one_smul]; exact h0
    · rw [h]; exact h1
    · rw [h, add_smul, one_smul, H.vec_add]; exact S.mul_mem h0 h1
  have hv2 : ∀ y : Fq n, H.vec (y • e₂) ∈ S := by
    intro y
    rcases f4_cases' hF hω y with h | h | h | h
    · rw [h, zero_smul, H.vec_zero]; exact S.one_mem
    · rw [h, one_smul]; exact h2
    · rw [h]; exact h3
    · rw [h, add_smul, one_smul, H.vec_add]; exact S.mul_mem h2 h3
  have hVS : blockU L ≤ S := by
    intro v hv
    obtain ⟨α, β, hw⟩ := bs.span (H.D.ψe v)
    have : v = H.vec (α • e₁) * H.vec (β • e₂) := by
      rw [← H.vec_add, ← hw, H.vec_ψe hv]
    rw [this]
    exact S.mul_mem (hv1 α) (hv2 β)
  have hQS : QM L M ≤ S := by
    intro q hq
    rcases c.Q_eq q hq with h | h
    · exact hVS h
    · have : q = x * (x⁻¹ * q) := by group
      rw [this]
      exact S.mul_mem hx (hVS h)
  have hNS : ∀ l ∈ T' ⊓ L, l ∈ S := by
    intro l hl
    obtain ⟨s, hs⟩ := c.isTv_of_mem_N0 bs hl
    have key : ∀ (a : G) (t : Fq n), a ∈ L → a ∈ S → IsTv H e₁ e₂ a t → IsTv H e₁ e₂ l t →
        l ∈ S := by
      intro a t haL haS hat hlt
      have hy := c.inv_mul_mem_blockU bs haL hl.2 hat hlt
      have : l = a * (a⁻¹ * l) := by group
      rw [this]
      exact S.mul_mem haS (hVS hy)
    rcases f4_cases' hF hω s with h | h | h | h
    · rw [h] at hs
      exact key 1 0 L.one_mem S.one_mem (IsTv.one e₁ e₂) hs
    · rw [h] at hs
      exact key r 1 c.r_L hr hrtv hs
    · rw [h] at hs
      exact key u ω hu.mem_L hu' hu.tv hs
    · rw [h] at hs
      exact key (r * u) (1 + ω) (L.mul_mem c.r_L hu.mem_L) (S.mul_mem hr hu')
        (hrtv.mul hu.tv c.r_L (H.le hu.mem_L)) hs
  have hMt : ∀ t ∈ T', t ∈ M := fun t ht => c.T'_M ht
  have hT2 : IsPGroup 2 T' := c.syl.isPGroup
  have hLQ : ∀ t (ht : t ∈ T'), H.chi ⟨t, hMt t ht⟩ = 1 → t ∈ S := by
    intro t ht hχ
    obtain ⟨k, hk⟩ := hT2 ⟨t, ht⟩
    have hk0 : t ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hk' : (⟨t, hMt t ht⟩ : ↥M) ^ 2 ^ k = 1 := Subtype.ext hk0
    obtain ⟨l, hl, q, hq, hlq⟩ := H.mem_LQ_iff.1 (H.mem_LQ_of_chi_eq_one hk' hχ)
    have hlq' : l * q = t := hlq
    have hlT : l ∈ T' := by
      have : l = t * q⁻¹ := by rw [← hlq']; group
      rw [this]
      exact T'.mul_mem ht (T'.inv_mem (c.Q_le hq))
    rw [← hlq']
    exact S.mul_mem (hNS l ⟨hlT, hl⟩) (hQS hq)
  intro t ht
  by_cases hχ : H.chi ⟨t, hMt t ht⟩ = 1
  · exact hLQ t ht hχ
  · have htb : t * b ∈ T' := T'.mul_mem ht c.b_T
    have hχb : H.chi ⟨b, c.b_M⟩ ≠ 1 :=
      H.chi_ne_one_of_not_mem (Subtype.ext c.b_sq : (⟨b, c.b_M⟩ : ↥M) * ⟨b, c.b_M⟩ = 1) c.b_LQ
    have hχ' : H.chi ⟨t * b, hMt _ htb⟩ = 1 := by
      have : (⟨t * b, hMt _ htb⟩ : ↥M) = ⟨t, hMt t ht⟩ * ⟨b, c.b_M⟩ := rfl
      rw [this, map_mul]
      exact ringEquiv_mul_eq_one hF hω hχ hχb
    have hS' := hLQ (t * b) htb hχ'
    have : t = (t * b) * b⁻¹ := by group
    rw [this]
    exact S.mul_mem hS' (S.inv_mem hb)

include c bs hu in
theorem Cfg.concl_of_u : Concl613 L T' x r := by
  have hRel := c.rel bs hu.mem_L hu.sq hu.comm hu.tv hu.conj
  have hg0 : H.vec e₁ ≠ 1 := by
    intro h
    exact bs.e₁_ne (H.vec_injective (h.trans H.vec_zero.symm))
  obtain ⟨hZ, hA, hB, hL⟩ := Model613.struct613 hRel hg0
  have hTS : T' = Model613.S613 (H.vec e₁) (H.vec (ω • e₁)) (H.vec e₂) (H.vec (ω • e₂)) x r u b :=
    le_antisymm (c.T'_le_S bs hu) (c.S_le_T' bs hu)
  refine ⟨H.vec e₁, H.vec_mem _, hg0, ?_, ?_, ?_, ?_⟩
  · rw [hTS]; exact hZ.2
  · rw [hTS]; exact hA
  · rw [hTS]; exact hB
  · rw [hTS]
    refine hL.trans ((Subgroup.closure_le L).2 ?_)
    rintro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    · exact blockU_le L (H.vec_mem _)
    · exact blockU_le L (H.vec_mem _)
    · exact blockU_le L (H.vec_mem _)
    · exact blockU_le L (H.vec_mem _)
    · exact c.r_L
    · exact hu.mem_L

end Final

theorem print613 : Print613 := by
  intro G _ _ L M T n D g hE1 hs hP hD4 T' hT'syl hT'M hQT' hBT' x hxD hxV r hrB hrL hrQ
  obtain ⟨b, c⟩ := exists_cfg hE1 hs hP hD4 hT'syl hT'M hQT' hBT' hxD hxV hrB hrL hrQ
  obtain ⟨e₁, e₂, ω, bs⟩ := exists_basis c
  obtain ⟨u, huL, huT, hu2, hru, hutv, hbu⟩ := c.exists_u bs
  exact c.concl_of_u bs ⟨huL, huT, hu2, hru, hutv, hbu⟩

end CFSG.CGT.PushingUpLit.T2KR.P613
