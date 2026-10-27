module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FinalGroup

public section

namespace CFSG.QuasithinUnique

section Bad

variable {G : Type*} [Group G]

@[expose] def Four (F : Subgroup G) : Prop := ElemAb F ∧ Nat.card F = 4

theorem conj_injective' {A B : Subgroup G} {s : G} (h : CFSG.conjugate A s = CFSG.conjugate B s) :
    A = B := by
  have h1 := congrArg (fun C => CFSG.conjugate C s⁻¹) h
  simp only [BenderBranch.conjugate_conjugate, mul_inv_cancel, BenderBranch.conjugate_one] at h1
  exact h1

theorem Four.conjugate {F : Subgroup G} (hF : Four F) (g : G) : Four (CFSG.conjugate F g) :=
  ⟨hF.1.conjugate g, by rw [BenderBranch.card_conjugate]; exact hF.2⟩

structure TwoFour (S SK E E' : Subgroup G) : Prop where
  hS : ∀ s ∈ S, ∀ a ∈ SK, s * a * s⁻¹ ∈ SK
  hEK : E ≤ SK
  hE'K : E' ≤ SK
  hE : Four E
  hE' : Four E'
  hne : E' ≠ E
  hall : ∀ F : Subgroup G, F ≤ SK → Four F → F = E ∨ F = E'

variable {S SK E E' : Subgroup G}

theorem TwoFour.conj_le (W : TwoFour S SK E E') {s : G} (hs : s ∈ S) {F : Subgroup G} (hF : F ≤ SK) :
    CFSG.conjugate F s ≤ SK := by
  intro y hy
  rw [BenderBranch.mem_conjugate_iff] at hy
  have h1 := W.hS s⁻¹ (S.inv_mem hs) _ (hF hy)
  have e : s⁻¹ * (s * y * s⁻¹) * s⁻¹⁻¹ = y := by group
  rwa [e] at h1

theorem TwoFour.conj_eq (W : TwoFour S SK E E') {s : G} (hs : s ∈ S) :
    (CFSG.conjugate E s = E ∨ CFSG.conjugate E s = E') ∧
      (CFSG.conjugate E' s = E ∨ CFSG.conjugate E' s = E') :=
  ⟨W.hall _ (W.conj_le hs W.hEK) (W.hE.conjugate s),
    W.hall _ (W.conj_le hs W.hE'K) (W.hE'.conjugate s)⟩

theorem TwoFour.dichotomy (W : TwoFour S SK E E') {s : G} (hs : s ∈ S) :
    (CFSG.conjugate E s = E ∧ CFSG.conjugate E' s = E') ∨
      (CFSG.conjugate E s = E' ∧ CFSG.conjugate E' s = E) := by
  obtain ⟨h1, h2⟩ := W.conj_eq hs
  rcases h1 with h1 | h1
  · left
    refine ⟨h1, ?_⟩
    rcases h2 with h2 | h2
    · exact absurd (conj_injective' (h2.trans h1.symm)) W.hne
    · exact h2
  · right
    refine ⟨h1, ?_⟩
    rcases h2 with h2 | h2
    · exact h2
    · exact absurd (conj_injective' (h2.trans h1.symm)) W.hne

theorem TwoFour.mem_normalizer_iff (W : TwoFour S SK E E') {s : G} (hs : s ∈ S) :
    s ∈ Subgroup.normalizer (E : Set G) ↔ s ∈ Subgroup.normalizer (E' : Set G) := by
  rw [← BenderBranch.conjugate_eq_iff_mem_normalizer, ← BenderBranch.conjugate_eq_iff_mem_normalizer]
  rcases W.dichotomy hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp [h1, h2]
  · constructor
    · intro h
      exact absurd (h1.symm.trans h) W.hne
    · intro h
      exact absurd (h2.symm.trans h).symm W.hne

theorem TwoFour.swap_mul (W : TwoFour S SK E E') {s t : G} (hs : s ∈ S) (ht : t ∈ S)
    (hsN : s ∉ Subgroup.normalizer (E : Set G)) (htN : t ∉ Subgroup.normalizer (E : Set G)) :
    s * t ∈ Subgroup.normalizer (E : Set G) := by
  rw [← BenderBranch.conjugate_eq_iff_mem_normalizer] at hsN htN ⊢
  have hs' : CFSG.conjugate E s = E' := by
    rcases W.dichotomy hs with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact absurd h1 hsN
    · exact h1
  have ht' : CFSG.conjugate E' t = E := by
    rcases W.dichotomy ht with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact absurd h1 htN
    · exact h2
  rw [← BenderBranch.conjugate_conjugate, hs', ht']

theorem TwoFour.conj_mem_normalizer (W : TwoFour S SK E E') {s q : G} (hs : s ∈ S) (hqS : q ∈ S)
    (hq : q ∈ Subgroup.normalizer (E : Set G)) :
    s * q * s⁻¹ ∈ Subgroup.normalizer (E : Set G) := by
  by_cases hsN : s ∈ Subgroup.normalizer (E : Set G)
  · exact (Subgroup.normalizer (E : Set G)).mul_mem
      ((Subgroup.normalizer (E : Set G)).mul_mem hsN hq)
      ((Subgroup.normalizer (E : Set G)).inv_mem hsN)
  · have hsE : CFSG.conjugate E s = E' := by
      rcases W.dichotomy hs with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact absurd ((BenderBranch.conjugate_eq_iff_mem_normalizer).mp h1) hsN
      · exact h1
    have hqN' : q ∈ Subgroup.normalizer (E' : Set G) := (W.mem_normalizer_iff hqS).mp hq
    have hqE' : CFSG.conjugate E' q = E' := BenderBranch.conjugate_eq_iff_mem_normalizer.mpr hqN'
    have hback : CFSG.conjugate E' s⁻¹ = E := by
      rw [← hsE, BenderBranch.conjugate_conjugate, mul_inv_cancel, BenderBranch.conjugate_one]
    rw [← BenderBranch.conjugate_eq_iff_mem_normalizer, ← BenderBranch.conjugate_conjugate,
      ← BenderBranch.conjugate_conjugate, hsE, hqE', hback]

theorem TwoFour.SK_le_normalizer (W : TwoFour S SK E E') (hcard : Nat.card SK = 8) :
    SK ≤ Subgroup.normalizer (E : Set G) := by
  have hsub : Nat.card (E.subgroupOf SK) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe W.hEK).toEquiv]
    exact W.hE.2
  have hidx : (E.subgroupOf SK).index = 2 := by
    have h1 := Subgroup.card_mul_index (E.subgroupOf SK)
    rw [hsub, hcard] at h1
    omega
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer W.hEK).mp
    (Subgroup.normal_of_index_eq_two hidx)

theorem mem_normalizer_of_mem_normalizer_conjugate {A : Subgroup G} {x s : G}
    (h : s ∈ Subgroup.normalizer ((CFSG.conjugate A x : Subgroup G) : Set G)) :
    x * s * x⁻¹ ∈ Subgroup.normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at h ⊢
  intro y
  have h1 := h (x⁻¹ * y * x)
  rw [BenderBranch.mem_conjugate_iff, BenderBranch.mem_conjugate_iff] at h1
  have e1 : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
  have e2 : x * (s * (x⁻¹ * y * x) * s⁻¹) * x⁻¹ = x * s * x⁻¹ * y * (x * s * x⁻¹)⁻¹ := by group
  rw [e1, e2] at h1
  exact h1

theorem eq_of_dvd_eight {n : ℕ} (h : n ∣ 8) : n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 := by
  obtain ⟨i, hi, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (show n ∣ 2 ^ 3 from h)
  interval_cases i <;> simp_all

theorem elemAb_sup {X Y : Subgroup G} (hc : ∀ a ∈ X, ∀ b ∈ Y, a * b = b * a) (hX : ElemAb X)
    (hY : ElemAb Y) : ElemAb (X ⊔ Y) := by
  refine ⟨fun g hg => ?_, fun g hg g' hg' => ?_⟩
  · obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hc hg
    have h1 := hc a ha b hb
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← h1]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [hX.1 a ha, hY.1 b hb, one_mul]
  · obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hc hg
    obtain ⟨a', ha', b', hb', rfl⟩ := exists_mul_of_mem_sup_of_commute hc hg'
    have e1 := hc a' ha' b hb
    have e2 := hc a ha b' hb'
    have e3 := hX.2 a ha a' ha'
    have e4 := hY.2 b hb b' hb'
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [e1]
      _ = (a * a') * (b * b') := by group
      _ = (a' * a) * (b' * b) := by rw [e3, e4]
      _ = a' * (a * b') * b := by group
      _ = a' * (b' * a) * b := by rw [e2]
      _ = a' * b' * (a * b) := by group

structure BadCtx (S SK : Subgroup G) (x : G) (E E' : Subgroup G) : Prop where
  two : TwoFour S SK E E'
  hSKS : SK ≤ S
  hxN : x ∈ Subgroup.normalizer (S : Set G)
  hx2 : x * x ∈ S
  hSKxS : CFSG.conjugate SK x ≤ S
  hcomm : ∀ a ∈ SK, ∀ b ∈ CFSG.conjugate SK x, a * b = b * a
  hdisj : SK ⊓ CFSG.conjugate SK x = ⊥
  hnonab : ∃ a ∈ SK, ∃ b ∈ SK, a * b ≠ b * a
  hcard8 : Nat.card SK = 8
  hNS : ∀ s ∈ S, s ∈ Subgroup.normalizer (E : Set G) →
    s ∈ Subgroup.normalizer ((CFSG.conjugate E x : Subgroup G) : Set G)
  hS128 : Nat.card S ≤ 128
  hbad : x * x ∉ Subgroup.normalizer (E : Set G)

variable {x : G}

theorem BadCtx.xS (C : BadCtx S SK x E E') {s : G} (hs : s ∈ S) : x * s * x⁻¹ ∈ S :=
  (Subgroup.mem_normalizer_iff.mp C.hxN s).mp hs

theorem BadCtx.SKx_norm (C : BadCtx S SK x E E') {s : G} (hs : s ∈ S) {b : G}
    (hb : b ∈ CFSG.conjugate SK x) : s * b * s⁻¹ ∈ CFSG.conjugate SK x := by
  rw [BenderBranch.mem_conjugate_iff] at hb ⊢
  have h1 := C.two.hS (x * s * x⁻¹) (C.xS hs) _ hb
  have e : x * (s * b * s⁻¹) * x⁻¹ = x * s * x⁻¹ * (x * b * x⁻¹) * (x * s * x⁻¹)⁻¹ := by group
  rw [e]
  exact h1

theorem BadCtx.xQ (C : BadCtx S SK x E E') {s : G} (hs : s ∈ S) :
    s ∈ Subgroup.normalizer (E : Set G) ↔ x * s * x⁻¹ ∈ Subgroup.normalizer (E : Set G) := by
  constructor
  · intro h
    exact mem_normalizer_of_mem_normalizer_conjugate (C.hNS s hs h)
  · intro h
    have hs' : x * s * x⁻¹ ∈ S := C.xS hs
    have h1 := mem_normalizer_of_mem_normalizer_conjugate (C.hNS _ hs' h)
    have hq : x * (x * s * x⁻¹) * x⁻¹ ∈ S := C.xS hs'
    have h2 := C.two.conj_mem_normalizer (S.inv_mem C.hx2) hq h1
    have e : (x * x)⁻¹ * (x * (x * s * x⁻¹) * x⁻¹) * (x * x)⁻¹⁻¹ = s := by group
    rwa [e] at h2

theorem BadCtx.SKx_le_normalizer (C : BadCtx S SK x E E') :
    CFSG.conjugate SK x ≤ Subgroup.normalizer (E : Set G) := by
  intro g hg
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact C.hcomm y (C.two.hEK hy) g hg

variable [Finite G]

theorem BadCtx.Q_eq_R (C : BadCtx S SK x E E') :
    S ⊓ Subgroup.normalizer (E : Set G) = SK ⊔ CFSG.conjugate SK x := by
  have hle : SK ⊔ CFSG.conjugate SK x ≤ S ⊓ Subgroup.normalizer (E : Set G) :=
    sup_le (le_inf C.hSKS (C.two.SK_le_normalizer C.hcard8)) (le_inf C.hSKxS C.SKx_le_normalizer)
  have hR : Nat.card ↥(SK ⊔ CFSG.conjugate SK x) = 64 := by
    rw [BenderBranch.card_sup_of_commute_of_inf_eq_bot C.hcomm C.hdisj, BenderBranch.card_conjugate,
      C.hcard8]
  have hne : S ⊓ Subgroup.normalizer (E : Set G) ≠ S := by
    intro h
    apply C.hbad
    have : x * x ∈ S ⊓ Subgroup.normalizer (E : Set G) := by rw [h]; exact C.hx2
    exact this.2
  have h2 := A6Final.two_mul_card_le_of_lt (inf_le_left : S ⊓ Subgroup.normalizer (E : Set G) ≤ S) hne
  have h3 : Nat.card ↥(S ⊓ Subgroup.normalizer (E : Set G)) ≤
      Nat.card ↥(SK ⊔ CFSG.conjugate SK x) := by
    rw [hR]
    have := C.hS128
    omega
  exact (Subgroup.eq_of_le_of_card_ge hle h3).symm

theorem BadCtx.card_le_two (C : BadCtx S SK x E E') {P : Subgroup G} (hP : P ≤ SK) (hPe : ElemAb P)
    {b : G} (hbS : b ∈ S) (hbN : b ∉ Subgroup.normalizer (E : Set G))
    (hcent : ∀ a ∈ P, b * a = a * b) : Nat.card P ≤ 2 := by
  have hdvd : Nat.card P ∣ 8 := C.hcard8 ▸ Subgroup.card_dvd_of_le hP
  rcases eq_of_dvd_eight hdvd with h | h | h | h
  · omega
  · omega
  · exfalso
    rcases C.two.hall P hP ⟨hPe, h⟩ with rfl | rfl
    · apply hbN
      apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (hcent a ha).symm
    · apply hbN
      rw [C.two.mem_normalizer_iff hbS]
      apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (hcent a ha).symm
  · exfalso
    have hPeq : P = SK := Subgroup.eq_of_le_of_card_ge hP (by rw [h, C.hcard8])
    obtain ⟨a, ha, a', ha', hne⟩ := C.hnonab
    apply hne
    rw [← hPeq] at ha ha'
    exact hPe.2 a ha a' ha'

theorem BadCtx.card_le_two' (C : BadCtx S SK x E E') {P : Subgroup G}
    (hP : P ≤ CFSG.conjugate SK x) (hPe : ElemAb P) {b : G} (hbS : b ∈ S)
    (hbN : b ∉ Subgroup.normalizer (E : Set G)) (hcent : ∀ a ∈ P, b * a = a * b) :
    Nat.card P ≤ 2 := by
  have hP' : CFSG.conjugate P x⁻¹ ≤ SK := by
    intro y hy
    rw [BenderBranch.mem_conjugate_iff] at hy
    have h1 := hP hy
    rw [BenderBranch.mem_conjugate_iff] at h1
    have e : x * (x⁻¹ * y * x⁻¹⁻¹) * x⁻¹ = y := by group
    rwa [e] at h1
  have hb'N : x * b * x⁻¹ ∉ Subgroup.normalizer (E : Set G) := fun h => hbN ((C.xQ hbS).mpr h)
  have hcent' : ∀ a ∈ CFSG.conjugate P x⁻¹, (x * b * x⁻¹) * a = a * (x * b * x⁻¹) := by
    intro a ha
    rw [BenderBranch.mem_conjugate_iff] at ha
    have h1 := hcent _ ha
    have e1 : (x * b * x⁻¹) * a = x * (b * (x⁻¹ * a * x⁻¹⁻¹)) * x⁻¹ := by group
    have e2 : a * (x * b * x⁻¹) = x * ((x⁻¹ * a * x⁻¹⁻¹) * b) * x⁻¹ := by group
    rw [e1, e2, h1]
  have := C.card_le_two hP' (hPe.conjugate x⁻¹) (C.xS hbS) hb'N hcent'
  rwa [BenderBranch.card_conjugate] at this

theorem BadCtx.card_le_four (C : BadCtx S SK x E E') {P : Subgroup G} (hP : P ≤ SK)
    (hPe : ElemAb P) : Nat.card P ≤ 4 := by
  have hdvd : Nat.card P ∣ 8 := C.hcard8 ▸ Subgroup.card_dvd_of_le hP
  rcases eq_of_dvd_eight hdvd with h | h | h | h
  · omega
  · omega
  · omega
  · exfalso
    have hPeq : P = SK := Subgroup.eq_of_le_of_card_ge hP (by rw [h, C.hcard8])
    obtain ⟨a, ha, a', ha', hne⟩ := C.hnonab
    apply hne
    rw [← hPeq] at ha ha'
    exact hPe.2 a ha a' ha'

theorem BadCtx.card_le_four' (C : BadCtx S SK x E E') {P : Subgroup G}
    (hP : P ≤ CFSG.conjugate SK x) (hPe : ElemAb P) : Nat.card P ≤ 4 := by
  have hP' : CFSG.conjugate P x⁻¹ ≤ SK := by
    intro y hy
    rw [BenderBranch.mem_conjugate_iff] at hy
    have h1 := hP hy
    rw [BenderBranch.mem_conjugate_iff] at h1
    have e : x * (x⁻¹ * y * x⁻¹⁻¹) * x⁻¹ = y := by group
    rwa [e] at h1
  have := C.card_le_four hP' (hPe.conjugate x⁻¹)
  rwa [BenderBranch.card_conjugate] at this

theorem BadCtx.E16_le (C : BadCtx S SK x E E') {B : Subgroup G} (hBS : B ≤ S) (hBe : ElemAb B)
    (hB16 : Nat.card B = 16) : B ≤ S ⊓ Subgroup.normalizer (E : Set G) := by
  by_contra hBQ
  obtain ⟨b, hbB, hbQ⟩ := Set.not_subset.mp hBQ
  have hbS : b ∈ S := hBS hbB
  have hbN : b ∉ Subgroup.normalizer (E : Set G) := fun h => hbQ ⟨hbS, h⟩
  set B' : Subgroup G := B ⊓ (S ⊓ Subgroup.normalizer (E : Set G)) with hB'
  have h1 : Nat.card B ≤ 2 * Nat.card B' := by
    apply A6Final.card_le_two_mul_of_cosets (b := b)
    intro g hg
    by_cases hgQ : g ∈ S ⊓ Subgroup.normalizer (E : Set G)
    · exact Or.inl ⟨hg, hgQ⟩
    · right
      have hgS := hBS hg
      have hgN : g ∉ Subgroup.normalizer (E : Set G) := fun h => hgQ ⟨hgS, h⟩
      have hbinvN : b⁻¹ ∉ Subgroup.normalizer (E : Set G) := fun h =>
        hbN ((Subgroup.inv_mem_iff _).mp h)
      exact ⟨B.mul_mem hg (B.inv_mem hbB),
        S.mul_mem hgS (S.inv_mem hbS), C.two.swap_mul hgS (S.inv_mem hbS) hgN hbinvN⟩
  have hB'R : B' ≤ SK ⊔ CFSG.conjugate SK x := by
    rw [← C.Q_eq_R]; exact inf_le_right
  have hd' : CFSG.conjugate SK x ⊓ SK = ⊥ := by rw [inf_comm]; exact C.hdisj
  have hc' : ∀ b ∈ CFSG.conjugate SK x, ∀ a ∈ SK, b * a = a * b :=
    fun b hb a ha => (C.hcomm a ha b hb).symm
  have hB'sq : ∀ g ∈ B', g * g = 1 := fun g hg => hBe.1 g hg.1
  have hB'comm : ∀ g ∈ B', ∀ g' ∈ B', g * g' = g' * g := fun g hg g' hg' => hBe.2 g hg.1 g' hg'.1
  have hcard := card_le_card_projL_mul C.hcomm hB'R
  obtain ⟨hsq1, hcomm1⟩ := projL_elemAb C.hcomm C.hdisj hB'sq hB'comm
  obtain ⟨hsq2, hcomm2⟩ := projL_elemAb hc' hd' hB'sq hB'comm
  have hbB' : ∀ g ∈ B', b * g = g * b := fun g hg => (hBe.2 g hg.1 b hbB).symm
  have hP1 : ∀ a ∈ projL SK (CFSG.conjugate SK x) B' C.hcomm, b * a = a * b := by
    rintro a ⟨ha, c, hc, hac⟩
    have h2 := hbB' _ hac
    have h3 : (b * a * b⁻¹) * (b * c * b⁻¹) = a * c := by
      calc (b * a * b⁻¹) * (b * c * b⁻¹) = b * (a * c) * b⁻¹ := by group
        _ = a * c := by rw [h2]; group
    have := eq_of_mul_eq_of_inf_eq_bot C.hdisj (C.two.hS b hbS a ha) ha
      (C.SKx_norm hbS hc) hc h3
    calc b * a = (b * a * b⁻¹) * b := by group
      _ = a * b := by rw [this.1]
  have hP2 : ∀ c ∈ projL (CFSG.conjugate SK x) SK B' hc', b * c = c * b := by
    rintro c ⟨hc, a, ha, hca⟩
    have h2 := hbB' _ hca
    have h3 : (b * c * b⁻¹) * (b * a * b⁻¹) = c * a := by
      calc (b * c * b⁻¹) * (b * a * b⁻¹) = b * (c * a) * b⁻¹ := by group
        _ = c * a := by rw [h2]; group
    have := eq_of_mul_eq_of_inf_eq_bot hd' (C.SKx_norm hbS hc) hc (C.two.hS b hbS a ha) ha h3
    calc b * c = (b * c * b⁻¹) * b := by group
      _ = c * b := by rw [this.1]
  have hc1 := C.card_le_two projL_le ⟨hsq1, hcomm1⟩ hbS hbN hP1
  have hc2 := C.card_le_two' projL_le ⟨hsq2, hcomm2⟩ hbS hbN hP2
  have : Nat.card B' ≤ 4 := by
    calc Nat.card B' ≤ _ := hcard
      _ ≤ 2 * 2 := Nat.mul_le_mul hc1 hc2
  omega

theorem BadCtx.E16_eq (C : BadCtx S SK x E E') {B : Subgroup G} (hBS : B ≤ S) (hBe : ElemAb B)
    (hB16 : Nat.card B = 16) :
    ∃ F F' : Subgroup G, (F = E ∨ F = E') ∧
      (F' = CFSG.conjugate E x ∨ F' = CFSG.conjugate E' x) ∧ B = F ⊔ F' := by
  have hBR : B ≤ SK ⊔ CFSG.conjugate SK x := by
    rw [← C.Q_eq_R]; exact C.E16_le hBS hBe hB16
  obtain ⟨P₁, P₂, hP₁, hP₂, hP₁e, hP₂e, hc₁, hc₂, hEq⟩ :=
    elemAb_eq_sup C.hcomm C.hdisj hBR hBe (m := 4) (n := 4) (by norm_num) (by norm_num)
      (fun P hP hPe => C.card_le_four hP hPe) (fun P hP hPe => C.card_le_four' hP hPe)
      (by rw [hB16])
  refine ⟨P₁, P₂, C.two.hall P₁ hP₁ ⟨hP₁e, hc₁⟩, ?_, hEq⟩
  have hP₂' : CFSG.conjugate P₂ x⁻¹ ≤ SK := by
    intro y hy
    rw [BenderBranch.mem_conjugate_iff] at hy
    have h1 := hP₂ hy
    rw [BenderBranch.mem_conjugate_iff] at h1
    have e : x * (x⁻¹ * y * x⁻¹⁻¹) * x⁻¹ = y := by group
    rwa [e] at h1
  have hF4 : Four (CFSG.conjugate P₂ x⁻¹) := Four.conjugate (⟨hP₂e, hc₂⟩ : Four P₂) x⁻¹
  have hback : CFSG.conjugate (CFSG.conjugate P₂ x⁻¹) x = P₂ := by
    rw [BenderBranch.conjugate_conjugate, inv_mul_cancel, BenderBranch.conjugate_one]
  rcases C.two.hall _ hP₂' hF4 with h | h
  · left; rw [← hback, h]
  · right; rw [← hback, h]

theorem BadCtx.no_invol (C : BadCtx S SK x E E') {T₀ : Subgroup G} (hST₀ : S ≤ T₀)
    (hcard : Nat.card T₀ = 2 * Nat.card S) (hxT₀ : x ∈ T₀) (hxS : x ∉ S) {g : G} (hg : g ∈ T₀)
    (hgS : g ∉ S) : g * g ≠ 1 := by
  intro hg2
  have hs : g * x⁻¹ ∈ S := mul_inv_mem_of_card_eq_two_mul hST₀ hcard hg hxT₀ hgS hxS
  set s := g * x⁻¹ with hsdef
  have hg' : g = s * x := by rw [hsdef]; group
  have e : g * g = (s * (x * s * x⁻¹)) * (x * x) := by rw [hg']; group
  have h1 : s * (x * s * x⁻¹) ∈ Subgroup.normalizer (E : Set G) := by
    by_cases hsN : s ∈ Subgroup.normalizer (E : Set G)
    · exact (Subgroup.normalizer (E : Set G)).mul_mem hsN ((C.xQ hs).mp hsN)
    · exact C.two.swap_mul hs (C.xS hs) hsN (fun h => hsN ((C.xQ hs).mpr h))
  rw [hg2] at e
  apply C.hbad
  have h2 : x * x = (s * (x * s * x⁻¹))⁻¹ := by
    have : (s * (x * s * x⁻¹)) * (x * x) = 1 := e.symm
    exact eq_inv_of_mul_eq_one_right this
  rw [h2]
  exact (Subgroup.normalizer (E : Set G)).inv_mem h1

theorem BadCtx.T_le_normalizer (C : BadCtx S SK x E E') {T : Subgroup G} (hT2 : IsPGroup 2 T)
    (hST : S ≤ T) (hxT : x ∈ T) (hxS : x ∉ S)
    (hT0 : Nat.card ↥(T ⊓ Subgroup.normalizer (S : Set G)) = 2 * Nat.card S)
    (hQA : S ⊓ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer ((E ⊔ CFSG.conjugate E x : Subgroup G) : Set G))
    (hsyl : ∀ P : Subgroup G, S ⊓ Subgroup.normalizer (E : Set G) ≤ P →
      P ≤ Subgroup.normalizer ((E ⊔ CFSG.conjugate E x : Subgroup G) : Set G) → IsPGroup 2 P →
      P = S ⊓ Subgroup.normalizer (E : Set G)) :
    T ≤ Subgroup.normalizer (S : Set G) := by
  by_contra hTn
  set T₀ : Subgroup G := T ⊓ Subgroup.normalizer (S : Set G) with hT₀def
  have hT₀T : T₀ ≤ T := inf_le_left
  have hT₀ne : T₀ ≠ T := by
    intro h
    exact hTn (calc T = T₀ := h.symm
      _ ≤ Subgroup.normalizer (S : Set G) := inf_le_right)
  have hST₀ : S ≤ T₀ := le_inf hST Subgroup.le_normalizer
  have hxT₀ : x ∈ T₀ := ⟨hxT, C.hxN⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w, hwT, hwN, hwT₀⟩ := exists_mem_normalizer_of_lt (p := 2) hT2 hT₀T hT₀ne
  set W : Subgroup G := T ⊓ Subgroup.normalizer (T₀ : Set G) with hWdef
  have hT₀W : T₀ ≤ W := le_inf hT₀T Subgroup.le_normalizer
  have hWne : T₀ ≠ W := fun h => hwT₀ (h ▸ (⟨hwT, hwN⟩ : w ∈ W))
  have hW2 : 2 * Nat.card T₀ ≤ Nat.card W := A6Final.two_mul_card_le_of_lt hT₀W hWne
  have hFSKx : CFSG.conjugate E x ≤ CFSG.conjugate SK x := BenderBranch.conjugate_mono C.two.hEK x
  have hcEF : ∀ a ∈ E, ∀ b ∈ CFSG.conjugate E x, a * b = b * a := fun a ha b hb =>
    C.hcomm a (C.two.hEK ha) b (hFSKx hb)
  have hAe : ElemAb (E ⊔ CFSG.conjugate E x) :=
    elemAb_sup hcEF C.two.hE.1 (C.two.hE.1.conjugate x)
  have hdEF : E ⊓ CFSG.conjugate E x = ⊥ := by
    rw [eq_bot_iff, ← C.hdisj]
    exact inf_le_inf C.two.hEK hFSKx
  have hAcard : Nat.card ↥(E ⊔ CFSG.conjugate E x) = 16 := by
    rw [BenderBranch.card_sup_of_commute_of_inf_eq_bot hcEF hdEF, BenderBranch.card_conjugate,
      C.two.hE.2]
  have hAS : E ⊔ CFSG.conjugate E x ≤ S := sup_le (C.two.hEK.trans C.hSKS) (hFSKx.trans C.hSKxS)
  let 𝒮 : Set (Subgroup G) := {E ⊔ CFSG.conjugate E x, E ⊔ CFSG.conjugate E' x,
    E' ⊔ CFSG.conjugate E x, E' ⊔ CFSG.conjugate E' x}
  have h𝒮card : 𝒮.ncard ≤ 4 := by
    calc 𝒮.ncard ≤ ({E ⊔ CFSG.conjugate E' x, E' ⊔ CFSG.conjugate E x,
            E' ⊔ CFSG.conjugate E' x} : Set (Subgroup G)).ncard + 1 :=
          Set.ncard_insert_le _ _
      _ ≤ (({E' ⊔ CFSG.conjugate E x, E' ⊔ CFSG.conjugate E' x} : Set (Subgroup G)).ncard + 1) + 1 :=
          Nat.add_le_add_right (Set.ncard_insert_le _ _) 1
      _ ≤ ((({E' ⊔ CFSG.conjugate E' x} : Set (Subgroup G)).ncard + 1) + 1) + 1 :=
          Nat.add_le_add_right (Nat.add_le_add_right (Set.ncard_insert_le _ _) 1) 1
      _ = 4 := by rw [Set.ncard_singleton]
  have key : ∀ P P' : Subgroup G, (P = E ∨ P = E') →
      (P' = CFSG.conjugate E x ∨ P' = CFSG.conjugate E' x) → P ⊔ P' ∈ 𝒮 := by
    intro P P' hP hP'
    rcases hP with hP | hP <;> rcases hP' with hP' | hP' <;> rw [hP, hP']
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  have hmem : ∀ w ∈ W, CFSG.conjugate (E ⊔ CFSG.conjugate E x) w ∈ 𝒮 := by
    intro w hw
    have hwN' : w ∈ Subgroup.normalizer (T₀ : Set G) := hw.2
    have hB_le : CFSG.conjugate (E ⊔ CFSG.conjugate E x) w ≤ T₀ := by
      have h1 : CFSG.conjugate (E ⊔ CFSG.conjugate E x) w ≤ CFSG.conjugate T₀ w :=
        BenderBranch.conjugate_mono (hAS.trans hST₀) w
      rwa [BenderBranch.conjugate_eq_iff_mem_normalizer.mpr hwN'] at h1
    have hBS : CFSG.conjugate (E ⊔ CFSG.conjugate E x) w ≤ S := by
      intro g hg
      by_contra hgS
      exact C.no_invol hST₀ hT0 hxT₀ hxS (hB_le hg) hgS ((hAe.conjugate w).1 g hg)
    have hB16 : Nat.card ↥(CFSG.conjugate (E ⊔ CFSG.conjugate E x) w) = 16 := by
      rw [BenderBranch.card_conjugate, hAcard]
    obtain ⟨P, P', hP, hP', hEq⟩ := C.E16_eq hBS (hAe.conjugate w) hB16
    rw [hEq]
    exact key P P' hP hP'
  have hbound := card_le_mul_card_inf_normalizer 𝒮 hmem
  have hWQ : W ⊓ Subgroup.normalizer ((E ⊔ CFSG.conjugate E x : Subgroup G) : Set G) =
      S ⊓ Subgroup.normalizer (E : Set G) :=
    hsyl _ (le_inf (inf_le_left.trans (hST₀.trans hT₀W)) hQA) inf_le_right
      (hT2.to_le (inf_le_left.trans inf_le_left))
  rw [hWQ] at hbound
  have hne : S ⊓ Subgroup.normalizer (E : Set G) ≠ S := by
    intro h
    apply C.hbad
    have : x * x ∈ S ⊓ Subgroup.normalizer (E : Set G) := by rw [h]; exact C.hx2
    exact this.2
  have h2 := A6Final.two_mul_card_le_of_lt (inf_le_left : S ⊓ Subgroup.normalizer (E : Set G) ≤ S) hne
  have hSpos : 0 < Nat.card S := Nat.card_pos
  have h4 : 𝒮.ncard * Nat.card ↥(S ⊓ Subgroup.normalizer (E : Set G)) ≤
      4 * Nat.card ↥(S ⊓ Subgroup.normalizer (E : Set G)) := Nat.mul_le_mul_right _ h𝒮card
  omega

end Bad

end CFSG.QuasithinUnique
