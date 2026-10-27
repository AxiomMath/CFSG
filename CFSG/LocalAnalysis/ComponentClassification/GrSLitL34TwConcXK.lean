module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwRAFacts
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwConcXFacts

public section

namespace CFSG.ComponentClassification.GrSLit.L34Tw

open CFSG Subgroup CFSG.ComponentClassification.PSL3Four CFSG.ComponentClassification.GrSLit.L34Facts


theorem U_ns {Us : Set (Fin 4 × Fin 4 × Bool)} (hU : Us = U1 ∨ Us = U2) (c d : Fin 4) :
    (c, d, false) ∈ Us ↔ (c = 0 ∧ d = 0) ∨ (c = 3 ∧ d = 3) := by
  rcases hU with rfl | rfl <;> simp [U1, U2] <;> decide +revert

theorem U_sw {Us : Set (Fin 4 × Fin 4 × Bool)} (hU : Us = U1 ∨ Us = U2) {c d : Fin 4}
    (h : (c, d, true) ∈ Us) : c.val ^^^ d.val = 3 := by
  rcases hU with rfl | rfl <;> simp [U1, U2] at h <;> rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    decide

theorem wmul_ns (x y : WrE) (hy : y.e = false) : x * y = ⟨x.a * y.a, x.b * y.b, x.e⟩ := by
  rw [WrE.mul_def, hy]
  simp

theorem wmul_sw (x y : WrE) (hy : y.e = true) : x * y = ⟨x.b * y.a, x.a * y.b, !x.e⟩ := by
  rw [WrE.mul_def, hy]
  simp

theorem wsq_sw (x : WrE) (hx : x.e = true) : x * x = ⟨x.b * x.a, x.a * x.b, false⟩ := by
  rw [wmul_sw x x hx, hx]
  rfl

theorem wsq_ns (x : WrE) (hx : x.e = false) : x * x = ⟨x.a * x.a, x.b * x.b, false⟩ := by
  rw [wmul_ns x x hx, hx]

theorem pow4 (g : WrE) : g ^ 4 = g * g * (g * g) := by
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem ne_of_swap {g h' : WrE} (hg : g.e = true) (hh : h'.e = false) : g ≠ h' := by
  intro e
  rw [e, hh] at hg
  exact absurd hg (by decide)

theorem wE_one {a b : Equiv.Perm (Fin 42)} : (⟨a, b, false⟩ : WrE) = 1 ↔ a = 1 ∧ b = 1 := by
  rw [WrE.one_def]
  constructor
  · intro h
    exact ⟨congrArg WrE.a h, congrArg WrE.b h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

namespace RAHyp

variable (h : RAHyp)
include h

theorem r₄_eq : r₄ = kel true true := by simp [kel, r₄]

theorem cos0_iff {y : Equiv.Perm (Fin 42)} (hy : y ∈ RA) : cosRA y = 0 ↔ y ∈ T0 := by
  obtain ⟨a, b, t, ht, rfl⟩ := h.mem_RA_iff.1 hy
  rw [h.cosRA_kel _ _ ht, h.kel_mul_mem_T0 ht]
  cases a <;> cases b <;> decide

theorem mul_kel (a b : Bool) (x : Equiv.Perm (Fin 42)) :
    x * kel a b = kel a b * (kel a b * x * kel a b) := by
  simp only [← mul_assoc, h.kel_sq, one_mul]

theorem kel_mul' (a b : Bool) (x : Equiv.Perm (Fin 42)) :
    kel a b * x = kel a b * x * kel a b * kel a b := by
  rw [mul_assoc (kel a b * x), h.kel_sq, mul_one]

theorem cos3_iff {y : Equiv.Perm (Fin 42)} (hy : y ∈ RA) : cosRA y = 3 ↔ y ∈ cosT true := by
  constructor
  · intro e
    obtain ⟨a, b, t, ht, rfl⟩ := h.mem_RA_iff.1 hy
    rw [h.cosRA_kel _ _ ht] at e
    have hab : a = true ∧ b = true := by
      cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | exact absurd e (by decide)
    obtain ⟨rfl, rfl⟩ := hab
    refine ⟨kel true true * t * kel true true, h.kel_conj true true ht, ?_⟩
    rw [h.r₄_eq]
    exact h.kel_mul' true true t
  · rintro ⟨x, hx, rfl⟩
    rw [h.r₄_eq, h.mul_kel, h.cosRA_kel _ _ (h.kel_conj true true hx)]
    rfl

theorem r₄_mem_RA : r₄ ∈ RA := by
  rw [h.r₄_eq]
  exact h.kel_mem true true

theorem cosT_mem_RA {i : Bool} {y : Equiv.Perm (Fin 42)} (hy : y ∈ cosT i) : y ∈ RA := by
  cases i
  · exact h.T0_le_RA hy
  · obtain ⟨x, hx, rfl⟩ := hy
    exact RA.mul_mem (h.T0_le_RA hx) h.r₄_mem_RA

theorem cosT_true_not_S {y : Equiv.Perm (Fin 42)} (hy : y ∈ cosT true) : y ∉ S := by
  obtain ⟨x, hx, rfl⟩ := hy
  intro hS
  have := S.mul_mem (S.inv_mem (T0_le_S hx)) hS
  rw [inv_mul_cancel_left] at this
  exact not_mem_S_r₄ this

theorem cosT_true_ne_one {y : Equiv.Perm (Fin 42)} (hy : y ∈ cosT true) : y ≠ 1 := by
  rintro rfl
  exact h.cosT_true_not_S hy S.one_mem

theorem isUni_not_S {u : Equiv.Perm (Fin 42)} (hu : isUni u) : u ∉ S := by
  obtain ⟨c, hc, rfl⟩ := hu
  intro hS
  exact not_mem_S_r₄ (conj_mem_S' hc hS)

theorem codes {Us : Set (Fin 4 × Fin 4 × Bool)} (hU : Us = U1 ∨ Us = U2) {X : Subgroup WrE}
    (hX : ∀ x, x ∈ X ↔ x ∈ Pw ∧ cc x ∈ Us) {x : WrE} (hx : x ∈ X) :
    (x.e = false → (x.a ∈ T0 ∧ x.b ∈ T0) ∨ (x.a ∈ cosT true ∧ x.b ∈ cosT true)) ∧
      (x.e = true → x.a * x.b ∈ cosT true ∧ x.b * x.a ∈ cosT true) := by
  obtain ⟨⟨ha, hb⟩, hc⟩ := (hX x).1 hx
  unfold cc at hc
  constructor
  · intro he
    rw [he, U_ns hU] at hc
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨(h.cos0_iff ha).1 h1, (h.cos0_iff hb).1 h2⟩
    · exact Or.inr ⟨(h.cos3_iff ha).1 h1, (h.cos3_iff hb).1 h2⟩
  · intro he
    rw [he] at hc
    have hs := U_sw hU hc
    refine ⟨(h.cos3_iff (RA.mul_mem ha hb)).1 (Fin.ext ?_),
      (h.cos3_iff (RA.mul_mem hb ha)).1 (Fin.ext ?_)⟩
    · rw [h.cos_mul ha hb, hs]
      rfl
    · rw [h.cos_mul hb ha, Nat.xor_comm, hs]
      rfl

theorem RA_le_cent {z : Equiv.Perm (Fin 42)} (h₅ : z * g₅ = g₅ * z) (h₆ : z * g₆ = g₆ * z)
    (hT : ∀ x ∈ T0, z * x = x * z) : RA ≤ centralizer {z} := by
  unfold RA
  rw [closure_le]
  rintro x (hx | rfl | rfl)
  · exact mem_centralizer_singleton_iff.2 (hT x hx).symm
  · exact mem_centralizer_singleton_iff.2 h₅.symm
  · exact mem_centralizer_singleton_iff.2 h₆.symm

theorem uni_of {F : ConcXFacts} {y : Equiv.Perm (Fin 42)} (hy : y ∈ cosT true) (hyy : y * y = 1) :
    isUni y := by
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨c, hc, e⟩ := F.uni x hx hyy
  refine ⟨c, S_le_R (T0_le_S hc), ?_⟩
  rw [← e, mul_inv_cancel_right]

theorem exists_swap4 (F : ConcXFacts) {Us : Set (Fin 4 × Fin 4 × Bool)} (hU : Us = U1 ∨ Us = U2)
    {X : Subgroup WrE} (hX : ∀ x, x ∈ X ↔ x ∈ Pw ∧ cc x ∈ Us) :
    ∃ g ∈ X, g.e = true ∧ g ^ 4 = 1 := by
  obtain ⟨x, hx, hw⟩ := F.inv
  have hwT : x * r₄ ∈ cosT true := ⟨x, hx, rfl⟩
  have hwR := h.cosT_mem_RA hwT
  have hw3 := (h.cos3_iff hwR).2 hwT
  have h4 : ∀ g : WrE, g ^ 4 = g * g * (g * g) := pow4
  rcases hU with rfl | rfl
  · refine ⟨⟨1, x * r₄, true⟩, (hX _).2 ⟨⟨RA.one_mem, hwR⟩, ?_⟩, rfl, ?_⟩
    · unfold cc
      have h0 : cosRA 1 = 0 := (h.cos0_iff RA.one_mem).2 T0.one_mem
      rw [h0, hw3]
      simp [U1]
    · rw [h4, wsq_sw ⟨1, x * r₄, true⟩ rfl, wmul_ns _ _ rfl]
      simp only [mul_one, one_mul, hw]
      rfl
  · have h5R : g₅ ∈ RA := subset_closure (Or.inr (Or.inl rfl))
    refine ⟨⟨g₅, g₅ * (x * r₄), true⟩, (hX _).2 ⟨⟨h5R, RA.mul_mem h5R hwR⟩, ?_⟩, rfl, ?_⟩
    · unfold cc
      have c5 : cosRA g₅ = 1 := by
        have e := h.cosRA_kel true false T0.one_mem
        simp only [kel, ↓reduceIte, Bool.false_eq_true, mul_one] at e
        exact e
      have c6 : cosRA (g₅ * (x * r₄)) = 2 := by
        apply Fin.ext
        rw [h.cos_mul h5R hwR, c5, hw3]
        rfl
      rw [c5, c6]
      simp [U2]
    · rw [h4, wsq_sw ⟨g₅, g₅ * (x * r₄), true⟩ rfl, wmul_ns _ _ rfl]
      have e1 : g₅ * (x * r₄) * g₅ * (g₅ * (x * r₄) * g₅) = 1 := by
        calc g₅ * (x * r₄) * g₅ * (g₅ * (x * r₄) * g₅)
            = g₅ * (x * r₄) * (g₅ * g₅) * (x * r₄) * g₅ := by group
          _ = 1 := by rw [h.sq₅, mul_one, mul_assoc g₅, hw, mul_one, h.sq₅]
      have e3 : g₅ * (g₅ * (x * r₄)) = x * r₄ := by rw [← mul_assoc, h.sq₅, one_mul]
      have e2 : g₅ * (g₅ * (x * r₄)) * (g₅ * (g₅ * (x * r₄))) = 1 := by rw [e3, hw]
      simp only [e1, e2]
      rfl

theorem card_le_prod {C : Set WrE} (f : Equiv.Perm (Fin 42) × Equiv.Perm (Fin 42) → WrE)
    (hf : Function.Injective f) (A₀ B₀ A₁ B₁ : Set (Equiv.Perm (Fin 42)))
    (hC : ∀ x ∈ C, ∃ p q, x = f (p, q) ∧ ((p ∈ A₀ ∧ q ∈ B₀) ∨ (p ∈ A₁ ∧ q ∈ B₁))) :
    Nat.card C ≤ Nat.card A₀ * Nat.card B₀ + Nat.card A₁ * Nat.card B₁ := by
  have hsub : C ⊆ f '' (A₀ ×ˢ B₀ ∪ A₁ ×ˢ B₁) := by
    intro x hx
    obtain ⟨p, q, rfl, hpq⟩ := hC x hx
    refine ⟨(p, q), ?_, rfl⟩
    rcases hpq with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · exact Or.inl ⟨hp, hq⟩
    · exact Or.inr ⟨hp, hq⟩
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
    Nat.card_coe_set_eq]
  calc C.ncard ≤ (f '' (A₀ ×ˢ B₀ ∪ A₁ ×ˢ B₁)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = (A₀ ×ˢ B₀ ∪ A₁ ×ˢ B₁).ncard := Set.ncard_image_of_injective _ hf
    _ ≤ (A₀ ×ˢ B₀).ncard + (A₁ ×ˢ B₁).ncard := Set.ncard_union_le _ _
    _ = A₀.ncard * B₀.ncard + A₁.ncard * B₁.ncard := by rw [Set.ncard_prod, Set.ncard_prod]

theorem sq_mem_T0 {i : Bool} {y : Equiv.Perm (Fin 42)} (hy : y ∈ cosT i) : y * y ∈ T0 := by
  cases i
  · exact T0.mul_mem hy hy
  · have hR := h.cosT_mem_RA hy
    refine (h.cos0_iff (RA.mul_mem hR hR)).1 (Fin.ext ?_)
    rw [h.cos_mul hR hR, (h.cos3_iff hR).2 hy]
    rfl

theorem mem_X_ns {Us : Set (Fin 4 × Fin 4 × Bool)} (hU : Us = U1 ∨ Us = U2) {X : Subgroup WrE}
    (hX : ∀ x, x ∈ X ↔ x ∈ Pw ∧ cc x ∈ Us) {i : Bool} {p q : Equiv.Perm (Fin 42)}
    (hp : p ∈ cosT i) (hq : q ∈ cosT i) : (⟨p, q, false⟩ : WrE) ∈ X := by
  refine (hX _).2 ⟨⟨h.cosT_mem_RA hp, h.cosT_mem_RA hq⟩, ?_⟩
  unfold cc
  rw [U_ns hU]
  cases i
  · exact Or.inl ⟨(h.cos0_iff (h.T0_le_RA hp)).2 hp, (h.cos0_iff (h.T0_le_RA hq)).2 hq⟩
  · exact Or.inr ⟨(h.cos3_iff (h.cosT_mem_RA hp)).2 hp, (h.cos3_iff (h.cosT_mem_RA hq)).2 hq⟩

theorem T0_of_one {Us : Set (Fin 4 × Fin 4 × Bool)} (hU : Us = U1 ∨ Us = U2) {X : Subgroup WrE}
    (hX : ∀ x, x ∈ X ↔ x ∈ Pw ∧ cc x ∈ Us) {x : WrE} (hx : x ∈ X) (he : x.e = false)
    (h1 : x.a = 1 ∨ x.b = 1) : x.a ∈ T0 ∧ x.b ∈ T0 := by
  rcases (h.codes hU hX hx).1 he with hab | ⟨ha, hb⟩
  · exact hab
  · rcases h1 with h1 | h1
    · exact absurd h1 (h.cosT_true_ne_one ha)
    · exact absurd h1 (h.cosT_true_ne_one hb)

theorem pair_struct (F : ConcXFacts) {Us : Set (Fin 4 × Fin 4 × Bool)} (hU : Us = U1 ∨ Us = U2)
    {X : Subgroup WrE} (hX : ∀ x, x ∈ X ↔ x ∈ Pw ∧ cc x ∈ Us) {a' y' : WrE} (ha' : a' ∈ X)
    (hy' : y' ∈ X) (hA : IsA a') (hY : IsUU y') (hc : a' * y' = y' * a') :
    ∃ t u v : Equiv.Perm (Fin 42), ∃ f : Equiv.Perm (Fin 42) × Equiv.Perm (Fin 42) → WrE,
      Function.Injective f ∧ t ∈ T0 ∧ t * t = 1 ∧ t ≠ 1 ∧ u ∈ cosT true ∧ u * u = 1 ∧
      v ∈ cosT true ∧ v * v = 1 ∧ t * u = u * t ∧ a' = f (t, 1) ∧
      (∀ p q r s, f (p, q) * f (r, s) = f (p * r, q * s)) ∧
      (∀ p q, f (p, q) = 1 ↔ p = 1 ∧ q = 1) ∧
      (∀ s, s ≠ 1 → s ∈ S → s * s = 1 → IsA (f (1, s))) ∧
      (∀ r s, r ≠ 1 → s ≠ 1 → r ∈ S → s ∈ S → r * r = 1 → s * s = 1 → IsD (f (r, s))) ∧
      ∀ x ∈ X ⊓ centralizer ({a'} : Set WrE) ⊓ centralizer ({y'} : Set WrE), ∃ p q,
        x = f (p, q) ∧ ((p ∈ cosC false t u ∧ q ∈ cosC false v v) ∨
          (p ∈ cosC true t u ∧ q ∈ cosC true v v)) := by
  obtain ⟨hye, hyy, hyu, hyv⟩ := hY
  obtain ⟨hyR, -⟩ := h.codes hU hX hy'
  have hyT : y'.a ∈ cosT true ∧ y'.b ∈ cosT true := by
    rcases hyR hye with ⟨ha, -⟩ | hab
    · exact absurd (T0_le_S ha) (h.isUni_not_S hyu)
    · exact hab
  have hy2 := wsq_ns y' hye
  rw [hyy, eq_comm, wE_one] at hy2
  obtain ⟨hae, haa, hA'⟩ := hA
  have ha2 := wsq_ns a' hae
  rw [haa, eq_comm, wE_one] at ha2
  have hy'eq : y' = ⟨y'.a, y'.b, false⟩ := by rw [← hye]
  have ha'eq : a' = ⟨a'.a, a'.b, false⟩ := by rw [← hae]
  have hns : ∀ x ∈ X ⊓ centralizer ({a'} : Set WrE) ⊓ centralizer ({y'} : Set WrE),
      x.e = false ∧ x * a' = a' * x ∧ x * y' = y' * x := by
    intro x hx
    obtain ⟨⟨hxX, hxa⟩, hxy⟩ := hx
    have ca := mem_centralizer_singleton_iff.1 hxa
    have cy := mem_centralizer_singleton_iff.1 hxy
    refine ⟨?_, ca, cy⟩
    cases hxe : x.e
    · rfl
    · exfalso
      rw [wmul_ns _ _ hae, wmul_sw _ _ hxe, hxe] at ca
      have e1 := congrArg WrE.a ca
      have e2 := congrArg WrE.b ca
      simp only at e1 e2
      rcases hA' with ⟨ha1, hb1, -⟩ | ⟨hb1, ha1, -⟩
      · rw [ha1, mul_one] at e1
        exact hb1 (mul_right_cancel (e1.symm.trans (one_mul x.a).symm))
      · rw [hb1, one_mul] at e1
        exact ha1 (mul_left_cancel (e1.trans (mul_one x.a).symm))
  rcases hA' with ⟨ha1, hb1, -⟩ | ⟨hb1, ha1, -⟩
  ·
    have hT := h.T0_of_one hU hX ha' hae (Or.inl ha1)
    have hcomm : a'.b * y'.b = y'.b * a'.b := by
      rw [ha'eq, hy'eq, wmul_ns _ _ rfl, wmul_ns _ _ rfl] at hc
      exact congrArg WrE.b hc
    refine ⟨a'.b, y'.b, y'.a, fun pq => ⟨pq.2, pq.1, false⟩, ?_, hT.2, ha2.2, hb1, hyT.2, hy2.2,
      hyT.1, hy2.1, hcomm, ?_, fun p q r s => by rw [wmul_ns _ _ rfl], fun p q => ?_,
      fun s hs1 hsS hss => ⟨rfl, ?_, Or.inr ⟨rfl, hs1, hsS⟩⟩,
      fun r s hr hs hrS hsS hrr hss => ⟨rfl, ?_, hs, hr, hsS, hrS⟩, fun x hx => ?_⟩
    · rintro ⟨p, q⟩ ⟨p', q'⟩ e
      simp only [WrE.mk.injEq] at e
      rw [e.1, e.2.1]
    · rw [ha'eq, ha1]
    · rw [wE_one]
      exact and_comm
    · rw [wmul_ns _ _ rfl, mul_one, hss]
      rfl
    · rw [wmul_ns _ _ rfl, hrr, hss]
      rfl
    · obtain ⟨hxe, ca, cy⟩ := hns x hx
      rw [ha'eq, wmul_ns _ _ rfl, wmul_ns _ _ hxe] at ca
      rw [hy'eq, wmul_ns _ _ rfl, wmul_ns _ _ hxe] at cy
      have c1 := congrArg WrE.b ca
      have c2 := congrArg WrE.a cy
      have c3 := congrArg WrE.b cy
      simp only at c1 c2 c3
      refine ⟨x.b, x.a, by rw [← hxe], ?_⟩
      rcases (h.codes hU hX hx.1.1).1 hxe with ⟨pa, pb⟩ | ⟨pa, pb⟩
      · exact Or.inl ⟨⟨pb, c1, c3⟩, ⟨pa, c2, c2⟩⟩
      · exact Or.inr ⟨⟨pb, c1, c3⟩, ⟨pa, c2, c2⟩⟩
  ·
    have hT := h.T0_of_one hU hX ha' hae (Or.inr hb1)
    have hcomm : a'.a * y'.a = y'.a * a'.a := by
      rw [ha'eq, hy'eq, wmul_ns _ _ rfl, wmul_ns _ _ rfl] at hc
      exact congrArg WrE.a hc
    refine ⟨a'.a, y'.a, y'.b, fun pq => ⟨pq.1, pq.2, false⟩, ?_, hT.1, ha2.1, ha1, hyT.1, hy2.1,
      hyT.2, hy2.2, hcomm, ?_, fun p q r s => by rw [wmul_ns _ _ rfl], fun p q => ?_,
      fun s hs1 hsS hss => ⟨rfl, ?_, Or.inl ⟨rfl, hs1, hsS⟩⟩,
      fun r s hr hs hrS hsS hrr hss => ⟨rfl, ?_, hr, hs, hrS, hsS⟩, fun x hx => ?_⟩
    · rintro ⟨p, q⟩ ⟨p', q'⟩ e
      simp only [WrE.mk.injEq] at e
      rw [e.1, e.2.1]
    · rw [ha'eq, hb1]
    · exact wE_one
    · rw [wmul_ns _ _ rfl, mul_one, hss]
      rfl
    · rw [wmul_ns _ _ rfl, hrr, hss]
      rfl
    · obtain ⟨hxe, ca, cy⟩ := hns x hx
      rw [ha'eq, wmul_ns _ _ rfl, wmul_ns _ _ hxe] at ca
      rw [hy'eq, wmul_ns _ _ rfl, wmul_ns _ _ hxe] at cy
      have c1 := congrArg WrE.a ca
      have c2 := congrArg WrE.a cy
      have c3 := congrArg WrE.b cy
      simp only at c1 c2 c3
      refine ⟨x.a, x.b, by rw [← hxe], ?_⟩
      rcases (h.codes hU hX hx.1.1).1 hxe with ⟨pa, pb⟩ | ⟨pa, pb⟩
      · exact Or.inl ⟨⟨pa, c1, c2⟩, ⟨pb, c3, c3⟩⟩
      · exact Or.inr ⟨⟨pa, c1, c2⟩, ⟨pb, c3, c3⟩⟩

theorem concX (F : ConcXFacts) {Us : Set (Fin 4 × Fin 4 × Bool)} (hU : Us = U1 ∨ Us = U2)
    {X : Subgroup WrE} (hX : ∀ x, x ∈ X ↔ x ∈ Pw ∧ cc x ∈ Us) : ConcX X := by
  have hXPw : ∀ {x}, x ∈ X → x.a ∈ RA ∧ x.b ∈ RA := fun hx => ((hX _).1 hx).1
  obtain ⟨g₀, hg₀, hg₀e, hg₀4⟩ := h.exists_swap4 F hU hX
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    obtain ⟨z, hz, hzz, hz1, hz5, hz6, hzT⟩ := F.cent
    have hzR := h.RA_le_cent hz5 hz6 hzT
    have hzc : ∀ y ∈ RA, y * z = z * y := fun y hy => mem_centralizer_singleton_iff.1 (hzR hy)
    refine ⟨⟨z, z, false⟩, (hX _).2 ⟨⟨h.T0_le_RA hz, h.T0_le_RA hz⟩, ?_⟩, fun x hx => ?_,
      rfl, by rw [wsq_ns _ rfl, hzz]; rfl, hz1, hz1, T0_le_S hz, T0_le_S hz⟩
    · unfold cc
      rw [(h.cos0_iff (h.T0_le_RA hz)).2 hz]
      rcases hU with rfl | rfl <;> simp [U1, U2]
    · obtain ⟨ha, hb⟩ := hXPw hx
      rw [wmul_ns _ _ rfl, WrE.mul_def]
      cases hxe : x.e
      · simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_xor]
        rw [hzc _ ha, hzc _ hb]
      · simp only [↓reduceIte, Bool.false_xor]
        rw [hzc _ ha, hzc _ hb]
  ·
    intro g hg hge hmin
    obtain ⟨-, hsw⟩ := h.codes hU hX hg
    obtain ⟨hab, hba⟩ := hsw hge
    have hle : orderOf g ≤ 4 :=
      (hmin g₀ hg₀ hg₀e).trans (Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hg₀4))
    have hpos : 0 < orderOf g := orderOf_pos g
    have hpow : g ^ orderOf g = 1 := pow_orderOf_eq_one g
    have hg2 : g * g = ⟨g.b * g.a, g.a * g.b, false⟩ := wsq_sw g hge
    have hp1 : g ≠ 1 := ne_of_swap hge rfl
    have hp2 : g * g ≠ 1 := by
      intro e
      rw [hg2, wE_one] at e
      exact h.cosT_true_ne_one hab e.2
    have hp3 : g * (g * g) ≠ 1 := by
      refine ne_of_swap ?_ rfl
      rw [hg2, wmul_ns _ _ rfl, hge]
    have hord4 : orderOf g = 4 := by
      generalize hn : orderOf g = n at hle hpos hpow
      interval_cases n
      · exact absurd (by simpa using hpow) hp1
      · exact absurd (by simpa [pow_two] using hpow) hp2
      · exact absurd (by simpa [pow_succ, mul_assoc] using hpow) hp3
      · rfl
    have hg4 : g ^ 4 = 1 := by
      have := pow_orderOf_eq_one g
      rwa [hord4] at this
    have hsq4 : g * g * (g * g) = 1 := by rw [← pow4, hg4]
    have hs := hsq4
    rw [hg2, wmul_ns _ _ rfl, wE_one] at hs
    refine ⟨hg4, by rw [hg2], hsq4, ?_, ?_⟩
    · rw [hg2]
      exact h.uni_of (F := F) hba hs.1
    · rw [hg2]
      exact h.uni_of (F := F) hab hs.2
  ·
    intro x hx hxx hx1
    obtain ⟨hns, hsw⟩ := h.codes hU hX hx
    cases hxe : x.e
    · have hsq := wsq_ns x hxe
      rw [hxx, eq_comm, wE_one] at hsq
      rcases hns hxe with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · by_cases ha1 : x.a = 1
        · have hb1 : x.b ≠ 1 := fun hb1 => hx1 (WrE.ext ha1 hb1 hxe)
          exact Or.inl ⟨hxe, hxx, Or.inl ⟨ha1, hb1, T0_le_S hb⟩⟩
        · by_cases hb1 : x.b = 1
          · exact Or.inl ⟨hxe, hxx, Or.inr ⟨hb1, ha1, T0_le_S ha⟩⟩
          · exact Or.inr (Or.inl ⟨hxe, hxx, ha1, hb1, T0_le_S ha, T0_le_S hb⟩)
      · exact Or.inr (Or.inr ⟨hxe, hxx, h.uni_of (F := F) ha hsq.1, h.uni_of (F := F) hb hsq.2⟩)
    · have hsq := wsq_sw x hxe
      rw [hxx, eq_comm, wE_one] at hsq
      exact absurd hsq.2 (h.cosT_true_ne_one (hsw hxe).1)
  ·
    intro b hb hbA
    refine ⟨g₀, hg₀, fun e => ?_⟩
    obtain ⟨hbe, -, hb'⟩ := hbA
    rw [wmul_ns _ _ hbe, wmul_sw _ _ hg₀e, hg₀e] at e
    have e1 := congrArg WrE.a e
    have e2 := congrArg WrE.b e
    simp only at e1 e2
    rcases hb' with ⟨ha1, hb1, -⟩ | ⟨hb1, ha1, -⟩
    · rw [ha1, mul_one] at e1
      exact hb1 (mul_right_cancel (e1.symm.trans (one_mul _).symm))
    · rw [hb1, one_mul] at e1
      exact ha1 (mul_left_cancel (e1.trans (mul_one _).symm))
  ·
    intro b hb hbA
    obtain ⟨hbe, hbb, hb'⟩ := hbA
    have hb2 := wsq_ns b hbe
    rw [hbb, eq_comm, wE_one] at hb2
    have hbeq : b = ⟨b.a, b.b, false⟩ := by rw [← hbe]
    have h1024 : (2 : ℕ) ^ 10 = 64 * 16 := by norm_num
    rw [h1024, ← card_T0]
    rcases hb' with ⟨ha1, -, -⟩ | ⟨hb1, -, -⟩
    · have hT := h.T0_of_one hU hX hb hbe (Or.inl ha1)
      have hbig := F.big _ hT.2 hb2.2
      refine le_trans (Nat.mul_le_mul_left _ hbig) ?_
      rw [← Nat.card_prod]
      refine Nat.card_le_card_of_injective
        (fun pq => ⟨⟨pq.1.1, pq.2.1, false⟩, h.mem_X_ns hU hX (i := false) pq.1.2 pq.2.2.1, ?_⟩)
        ?_
      · refine mem_centralizer_singleton_iff.2 ?_
        have hq := pq.2.2.2.1
        rw [wmul_ns b _ rfl, wmul_ns _ b hbe]
        simp only [ha1, one_mul, mul_one, hbe, hq]
      · rintro ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ ⟨⟨p', hp'⟩, ⟨q', hq'⟩⟩ e
        simp only [Subtype.mk.injEq, WrE.mk.injEq] at e
        obtain ⟨rfl, rfl, -⟩ := e
        rfl
    · have hT := h.T0_of_one hU hX hb hbe (Or.inr hb1)
      have hbig := F.big _ hT.1 hb2.1
      refine le_trans (Nat.mul_le_mul_left _ hbig) ?_
      rw [← Nat.card_prod]
      refine Nat.card_le_card_of_injective
        (fun pq => ⟨⟨pq.2.1, pq.1.1, false⟩, h.mem_X_ns hU hX (i := false) pq.2.2.1 pq.1.2, ?_⟩)
        ?_
      · refine mem_centralizer_singleton_iff.2 ?_
        have hq := pq.2.2.2.1
        rw [wmul_ns b _ rfl, wmul_ns _ b hbe]
        simp only [hb1, one_mul, mul_one, hbe, hq]
      · rintro ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ ⟨⟨p', hp'⟩, ⟨q', hq'⟩⟩ e
        simp only [Subtype.mk.injEq, WrE.mk.injEq] at e
        obtain ⟨rfl, rfl, -⟩ := e
        rfl
  ·
    intro a' ha' y' hy' hA hY hc
    obtain ⟨t, u, v, f, hf, ht, htt, ht1, hu, huu, hv, hvv, htu, -, -, -, -, -, hC⟩ :=
      h.pair_struct F hU hX ha' hy' hA hY hc
    have h128 : (2 : ℕ) ^ 7 = 128 := by norm_num
    rw [h128]
    refine (h.card_le_prod f hf _ _ _ _ hC).trans ?_
    have q0 := F.qcard v hv hvv false
    have q1 := F.qcard v hv hvv true
    have hp := F.pcard t ht htt ht1 u hu huu htu
    nlinarith [Nat.mul_le_mul_left (Nat.card (cosC false t u)) q0,
      Nat.mul_le_mul_left (Nat.card (cosC true t u)) q1]
  ·
    intro a' ha' y' hy' hA hY hc ⟨E, hE, hEel, hE16⟩
    obtain ⟨t, u, v, f, hf, ht, htt, ht1, hu, huu, hv, hvv, htu, -, hmul, hone, -, -, hC⟩ :=
      h.pair_struct F hU hX ha' hy' hA hY hc
    have hC₂ : ∀ x ∈ (E : Set WrE), ∃ p q, x = f (p, q) ∧
        ((p ∈ cosC₂ false t u ∧ q ∈ cosC₂ false v v) ∨ (p ∈ cosC₂ true t u ∧ q ∈ cosC₂ true v v)) := by
      intro x hx
      obtain ⟨p, q, rfl, hpq⟩ := hC _ (hE hx)
      have hsq := hEel.2 _ hx
      rw [hmul, hone] at hsq
      refine ⟨p, q, rfl, ?_⟩
      rcases hpq with ⟨hp, hq⟩ | ⟨hp, hq⟩
      · exact Or.inl ⟨⟨hp, hsq.1⟩, ⟨hq, hsq.2⟩⟩
      · exact Or.inr ⟨⟨hp, hsq.1⟩, ⟨hq, hsq.2⟩⟩
    have hle := h.card_le_prod f hf _ _ _ _ hC₂
    have q0 := F.qinv v hv hvv false
    have q1 := F.qinv v hv hvv true
    have hp := F.pinv t ht htt ht1 u hu huu htu
    have hE' : Nat.card (E : Set WrE) = 16 := hE16
    nlinarith [Nat.mul_le_mul_left (Nat.card (cosC₂ false t u)) q0,
      Nat.mul_le_mul_left (Nat.card (cosC₂ true t u)) q1]
  ·
    intro a' ha' y' hy' hA hY hc x hx hx1
    obtain ⟨t, u, v, f, hf, ht, htt, ht1, hu, huu, hv, hvv, htu, rfl, hmul, hone, hIsA, hIsD, hC⟩ :=
      h.pair_struct F hU hX ha' hy' hA hY hc
    obtain ⟨p, q, rfl, hpq⟩ := hC _ hx
    rw [hmul] at hx1 ⊢
    rw [hmul]
    have hq4 : q * q * (q * q) = 1 ∧ q * q ∈ T0 := by
      rcases hpq with ⟨-, hq⟩ | ⟨-, hq⟩
      · exact ⟨F.qsq v hv hvv false q hq, h.sq_mem_T0 hq.1⟩
      · exact ⟨F.qsq v hv hvv true q hq, h.sq_mem_T0 hq.1⟩
    have hp2 : p * p = 1 ∨ p * p = t := by
      rcases hpq with ⟨hp, -⟩ | ⟨hp, -⟩
      · exact F.psq t ht htt ht1 u hu huu htu false p hp
      · exact F.psq t ht htt ht1 u hu huu htu true p hp
    have htS := T0_le_S ht
    have hqS := T0_le_S hq4.2
    rcases hp2 with hp2 | hp2
    · have hq1 : q * q ≠ 1 := fun e => hx1 ((hone _ _).2 ⟨hp2, e⟩)
      right
      left
      rw [hp2, mul_one]
      exact ⟨hIsA _ hq1 hqS hq4.1, hIsD _ _ ht1 hq1 htS hqS htt hq4.1⟩
    · rw [hp2]
      by_cases hq1 : q * q = 1
      · left
        rw [hq1]
      · right
        right
        rw [htt]
        exact ⟨hIsD _ _ ht1 hq1 htS hqS htt hq4.1, hIsA _ hq1 hqS hq4.1⟩

end RAHyp

end CFSG.ComponentClassification.GrSLit.L34Tw

end
