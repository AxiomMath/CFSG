module

public import CFSG.LargeExtraspecial.S14C13B2Weak38

public section

namespace CFSG.LargeExtraspecial.S14

open Subgroup

variable {O : Type*} [Group O] [Finite O]

namespace WeakSetting

variable {X : Subgroup O} {t : O} {N : Subgroup O}

structure B2Hyp (W : WeakSetting X t N) (A L : Subgroup O) : Prop where
  t_mem_A : t ∈ A
  A_le : A ≤ N
  A_comm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a
  A_norm : ∀ h ∈ X, h * t = t * h → ∀ a ∈ A, h * a * h⁻¹ ∈ A
  t_mem_L : t ∈ L
  L_le : L ≤ X
  L_comm : ∀ a ∈ L, ∀ b ∈ L, a * b = b * a
  L_fus : ∀ k ∈ X, k * t * k⁻¹ ∈ L →
    ∃ k' ∈ X, k' ∈ normalizer (L : Set O) ∧ k' * t * k'⁻¹ = k * t * k⁻¹
  N_norm_L : ∀ n ∈ N, n ∈ normalizer (L : Set O)
  exists_AL : ∃ a ∈ A, a ∈ L ∧ a ≠ 1 ∧ a ≠ t
  tv : ∀ y ∈ L, ∀ c ∈ N, (∀ a ∈ A, y * a * y⁻¹ * a⁻¹ = 1 ∨ y * a * y⁻¹ * a⁻¹ = t ∨
    y * a * y⁻¹ * a⁻¹ = c ∨ y * a * y⁻¹ * a⁻¹ = c * t) →
    ∀ a ∈ A, y * a * y⁻¹ * a⁻¹ ∈ zpowers t
  faith : ∀ y ∈ L, (∀ a ∈ A, y * a * y⁻¹ * a⁻¹ ∈ zpowers t) → y ∈ N

variable {W : WeakSetting X t N} {A L : Subgroup O}

namespace B2Hyp

omit [Finite O] in
theorem map_conj_eq (hB : B2Hyp W A L) {a b : O} (ha : a ∈ X) (hb : b ∈ X)
    (hab : a * t * a⁻¹ = b * t * b⁻¹) :
    A.map (MulAut.conj a).toMonoidHom = A.map (MulAut.conj b).toMonoidHom := by
  have hc : b⁻¹ * a * t = t * (b⁻¹ * a) := by
    calc b⁻¹ * a * t = b⁻¹ * (a * t * a⁻¹) * a := by group
      _ = b⁻¹ * (b * t * b⁻¹) * a := by rw [hab]
      _ = t * (b⁻¹ * a) := by group
  have hc' : (b⁻¹ * a)⁻¹ * t = t * (b⁻¹ * a)⁻¹ := by
    calc (b⁻¹ * a)⁻¹ * t = (b⁻¹ * a)⁻¹ * (t * (b⁻¹ * a)) * (b⁻¹ * a)⁻¹ := by group
      _ = (b⁻¹ * a)⁻¹ * (b⁻¹ * a * t) * (b⁻¹ * a)⁻¹ := by rw [hc]
      _ = t * (b⁻¹ * a)⁻¹ := by group
  ext y
  rw [mem_map_conj_iff, mem_map_conj_iff]
  constructor
  · intro h
    have := hB.A_norm _ (mul_mem (inv_mem hb) ha) hc _ h
    convert this using 1
    group
  · intro h
    have := hB.A_norm _ (inv_mem (mul_mem (inv_mem hb) ha)) hc' _ h
    convert this using 1
    group

omit [Finite O] in
theorem conj_norm (hB : B2Hyp W A L) {k h y : O} (hk : k ∈ X) (hh : h ∈ X)
    (hht : h * (k * t * k⁻¹) = (k * t * k⁻¹) * h)
    (hy : y ∈ A.map (MulAut.conj k).toMonoidHom) :
    h * y * h⁻¹ ∈ A.map (MulAut.conj k).toMonoidHom := by
  rw [mem_map_conj_iff] at hy ⊢
  have h1 : k⁻¹ * h * k * t = t * (k⁻¹ * h * k) := by
    calc k⁻¹ * h * k * t = k⁻¹ * (h * (k * t * k⁻¹)) * k := by group
      _ = k⁻¹ * ((k * t * k⁻¹) * h) * k := by rw [hht]
      _ = t * (k⁻¹ * h * k) := by group
  have := hB.A_norm _ (mul_mem (mul_mem (inv_mem hk) hh) hk) h1 _ hy
  convert this using 1
  group

omit [Finite O] in
theorem conj_mem_conj (hB : B2Hyp W A L) (k : O) :
    k * t * k⁻¹ ∈ A.map (MulAut.conj k).toMonoidHom := by
  rw [mem_map_conj_iff]
  convert hB.t_mem_A using 1
  group

omit [Finite O] in
theorem conj_mem_L {k y : O} (hk : k ∈ normalizer (L : Set O)) (hy : y ∈ L) :
    k * y * k⁻¹ ∈ L :=
  (mem_normalizer_iff.mp hk y).mp hy

omit [Finite O] in
theorem inv_conj_mem_L {k y : O} (hk : k ∈ normalizer (L : Set O)) (hy : y ∈ L) :
    k⁻¹ * y * k ∈ L := by
  have := (mem_normalizer_iff.mp (inv_mem hk) y).mp hy
  simpa using this

theorem mem_A (hB : B2Hyp W A L) {k : O} (hk : k ∈ X) (hxL : k * t * k⁻¹ ∈ L)
    (hxN : k * t * k⁻¹ ∈ N) : k * t * k⁻¹ ∈ A := by
  obtain ⟨k', hk'X, hk'L, hk'⟩ := hB.L_fus k hk hxL
  rw [← hk'] at hxL hxN ⊢
  by_contra hxA
  have hne : k' * t * k'⁻¹ ≠ t := fun h => hxA (by rw [h]; exact hB.t_mem_A)
  have T := W.conj hk'X
  have hx1 : k' * t * k'⁻¹ ≠ 1 := T.t1
  obtain ⟨g', hg'X, hg't, hg'x⟩ := W.exists_swap hk'X hxN hne
  have hAx : A.map (MulAut.conj k').toMonoidHom = A.map (MulAut.conj g').toMonoidHom :=
    hB.map_conj_eq hk'X hg'X hg't.symm
  have htAx : t ∉ A.map (MulAut.conj k').toMonoidHom := by
    rw [hAx, mem_map_conj_iff]
    intro h
    apply hxA
    have e : g'⁻¹ * t * g' = k' * t * k'⁻¹ := by
      calc g'⁻¹ * t * g' = g'⁻¹ * (g' * (k' * t * k'⁻¹) * g'⁻¹) * g' := by rw [hg'x]
        _ = k' * t * k'⁻¹ := by group
    rw [← e]
    exact h
  have hxAx := hB.conj_mem_conj k'
  have hAxN : ∀ b ∈ A.map (MulAut.conj k').toMonoidHom, b ∈ N →
      b = 1 ∨ b = k' * t * k'⁻¹ := by
    intro b hbAx hbN
    by_contra hb
    push Not at hb
    have hbt : b ≠ t := fun h => htAx (h ▸ hbAx)
    have hbxt : b ≠ k' * t * k'⁻¹ * t := fun h => htAx (by
      have e : t = (k' * t * k'⁻¹)⁻¹ * b := by rw [h]; group
      rw [e]
      exact mul_mem (inv_mem hxAx) hbAx)
    have hbc : ¬ ∀ n ∈ N, n * (k' * t * k'⁻¹) = (k' * t * k'⁻¹) * n → b * n = n * b := by
      intro h
      rcases W.mem_centralizer_centralizer hxN hx1 hne hbN h with h1 | h1 | h1 | h1
      exacts [hb.1 h1, hbt h1, hb.2 h1, hbxt h1]
    push Not at hbc
    obtain ⟨n, hnN, hnx, hbn⟩ := hbc
    have hc : n * b * n⁻¹ * b⁻¹ = t := (W.comm_eq hnN hbN).resolve_left fun h =>
      hbn ((comm_eq_one_iff n b).mp h).symm
    have hnb : n * b * n⁻¹ ∈ A.map (MulAut.conj k').toMonoidHom :=
      hB.conj_norm hk'X (W.N_le hnN) hnx hbAx
    exact htAx (by rw [← hc]; exact mul_mem hnb (inv_mem hbAx))
  have hAAx : ∀ y ∈ A, y ∈ A.map (MulAut.conj k').toMonoidHom → y = 1 := fun y hyA hyAx =>
    (hAxN y hyAx (hB.A_le hyA)).resolve_right fun h => hxA (h ▸ hyA)
  obtain ⟨a, haA, haL, ha1, hat⟩ := hB.exists_AL
  set y := k' * a * k'⁻¹ with hy
  have hyAx : y ∈ A.map (MulAut.conj k').toMonoidHom := by
    rw [mem_map_conj_iff]
    convert haA using 1
    rw [hy]
    group
  have hyL : y ∈ L := conj_mem_L hk'L haL
  have hyX : y ∈ X := hB.L_le hyL
  have hyt : y * t = t * y := hB.L_comm y hyL t hB.t_mem_L
  have hcent : ∀ a' ∈ A, a' * (k' * t * k'⁻¹) = (k' * t * k'⁻¹) * a' →
      y * a' * y⁻¹ * a'⁻¹ = 1 := by
    intro a' ha'A ha'x
    refine hAAx _ (mul_mem (hB.A_norm y hyX hyt a' ha'A) (inv_mem ha'A)) ?_
    rw [show y * a' * y⁻¹ * a'⁻¹ = y * (a' * y⁻¹ * a'⁻¹) by group]
    exact mul_mem hyAx (hB.conj_norm hk'X (W.N_le (hB.A_le ha'A)) ha'x (inv_mem hyAx))
  set F := N ⊓ centralizer ({k' * t * k'⁻¹} : Set O) with hF
  have hFi : F.relIndex N = 2 := W.relIndex_centralizer_eq_two hxN hx1 hne
  have hmemF : ∀ b ∈ N, b ∈ F ↔ b * (k' * t * k'⁻¹) = (k' * t * k'⁻¹) * b := fun b hb => by
    rw [hF, mem_inf, mem_centralizer_singleton_iff]
    exact ⟨fun h => h.2, fun h => ⟨hb, h⟩⟩
  have himg : ∃ c ∈ N, ∀ a' ∈ A, y * a' * y⁻¹ * a'⁻¹ = 1 ∨ y * a' * y⁻¹ * a'⁻¹ = t ∨
      y * a' * y⁻¹ * a'⁻¹ = c ∨ y * a' * y⁻¹ * a'⁻¹ = c * t := by
    by_cases h : ∃ a₀ ∈ A, a₀ * (k' * t * k'⁻¹) ≠ (k' * t * k'⁻¹) * a₀
    · obtain ⟨a₀, ha₀A, ha₀x⟩ := h
      refine ⟨y * a₀ * y⁻¹ * a₀⁻¹,
        hB.A_le (mul_mem (hB.A_norm y hyX hyt a₀ ha₀A) (inv_mem ha₀A)), fun a' ha'A => ?_⟩
      by_cases ha' : a' * (k' * t * k'⁻¹) = (k' * t * k'⁻¹) * a'
      · exact Or.inl (hcent a' ha'A ha')
      · right; right; left
        have hd : a' * a₀⁻¹ ∈ F := by
          rw [mul_mem_iff_of_relIndex_eq_two hFi (hB.A_le ha'A) (inv_mem (hB.A_le ha₀A)),
            inv_mem_iff, hmemF a' (hB.A_le ha'A), hmemF a₀ (hB.A_le ha₀A)]
          exact iff_of_false ha' ha₀x
        have h1 := hcent _ (mul_mem ha'A (inv_mem ha₀A)) ((hmemF _ (hB.A_le
          (mul_mem ha'A (inv_mem ha₀A)))).mp hd)
        have hc0 : y * a₀ * y⁻¹ * a₀⁻¹ ∈ A :=
          mul_mem (hB.A_norm y hyX hyt a₀ ha₀A) (inv_mem ha₀A)
        have h2 : y * (a' * a₀⁻¹) * y⁻¹ = a' * a₀⁻¹ := by
          calc y * (a' * a₀⁻¹) * y⁻¹
              = y * (a' * a₀⁻¹) * y⁻¹ * (a' * a₀⁻¹)⁻¹ * (a' * a₀⁻¹) := by group
            _ = a' * a₀⁻¹ := by rw [h1, one_mul]
        have h3 := hB.A_comm _ (mul_mem ha'A (inv_mem ha₀A)) _ hc0
        calc y * a' * y⁻¹ * a'⁻¹
            = (y * (a' * a₀⁻¹) * y⁻¹) * (y * a₀ * y⁻¹ * a₀⁻¹) * (a₀ * a'⁻¹) := by group
          _ = (a' * a₀⁻¹) * (y * a₀ * y⁻¹ * a₀⁻¹) * (a' * a₀⁻¹)⁻¹ := by rw [h2]; group
          _ = y * a₀ * y⁻¹ * a₀⁻¹ := by rw [h3]; group
    · push Not at h
      exact ⟨1, one_mem _, fun a' ha'A => Or.inl (hcent a' ha'A (h a' ha'A))⟩
  obtain ⟨c, hcN, hc⟩ := himg
  have hyN := hB.faith y hyL (hB.tv y hyL c hcN hc)
  rcases hAxN y hyAx hyN with h | h
  · apply ha1
    calc a = k'⁻¹ * y * k' := by rw [hy]; group
      _ = 1 := by rw [h]; group
  · apply hat
    calc a = k'⁻¹ * y * k' := by rw [hy]; group
      _ = t := by rw [h]; group

theorem mem_A_of_mem_conj (hB : B2Hyp W A L) {k : O} (hk : k ∈ X) {w : O} (hwN : w ∈ N)
    (hwAx : w ∈ A.map (MulAut.conj k).toMonoidHom) (hwL : w ∈ L) : w ∈ A := by
  rw [mem_map_conj_iff] at hwAx
  by_cases hD : ∃ h ∈ X, h * t * h⁻¹ = w
  · obtain ⟨h, hh, rfl⟩ := hD
    exact hB.mem_A hh hwL hwN
  push Not at hD
  by_cases hw1 : w = 1
  · rw [hw1]
    exact one_mem _
  have hku : k * (k⁻¹ * w * k) * k⁻¹ = w := by group
  have huN : k⁻¹ * w * k ∈ N := hB.A_le hwAx
  have hu1 : k⁻¹ * w * k ≠ 1 := fun h => hw1 (by rw [← hku, h]; group)
  have huc : ∀ h ∈ X, h * t * h⁻¹ ≠ k⁻¹ * w * k := fun h hh e => hD (k * h) (mul_mem hk hh) (by
    rw [show (k * h) * t * (k * h)⁻¹ = k * (h * t * h⁻¹) * k⁻¹ by group, e, hku])
  have hut : k⁻¹ * w * k ≠ t := fun h => huc 1 (one_mem _) (by rw [h]; group)
  obtain ⟨m, hm, hmt, hmu⟩ := W.janko huN hu1 hut huc hk (by rw [hku]; exact hwN)
  have := hB.A_norm m hm hmt _ hwAx
  rwa [hmu, hku] at this

theorem comm_mem_of_mem_conj (hB : B2Hyp W A L) {k : O} (hk : k ∈ X)
    (hkL : k ∈ normalizer (L : Set O)) (hxA : k * t * k⁻¹ ∈ A)
    (hne : k * t * k⁻¹ ≠ t) {y : O} (hyL : y ∈ L)
    (hyAx : y ∈ A.map (MulAut.conj k).toMonoidHom) :
    ∀ a ∈ A, y * a * y⁻¹ * a⁻¹ ∈ zpowers t := by
  have hxN : k * t * k⁻¹ ∈ N := hB.A_le hxA
  have T := W.conj hk
  have hx1 : k * t * k⁻¹ ≠ 1 := T.t1
  have hyX : y ∈ X := hB.L_le hyL
  have hyt : y * t = t * y := hB.L_comm y hyL t hB.t_mem_L
  have hyit : y⁻¹ * t = t * y⁻¹ := by
    calc y⁻¹ * t = y⁻¹ * (t * y) * y⁻¹ := by group
      _ = y⁻¹ * (y * t) * y⁻¹ := by rw [hyt]
      _ = t * y⁻¹ := by group
  have htNx := W.mem_map_conj_of_conj_mem hk hxN hne
  rw [mem_map_conj_iff] at htNx
  have htAx : t ∈ A.map (MulAut.conj k).toMonoidHom := by
    rw [mem_map_conj_iff]
    have e : k⁻¹ * t * k = k⁻¹ * t * k⁻¹⁻¹ := by group
    rw [e] at htNx ⊢
    exact hB.mem_A (inv_mem hk) (by rw [← e]; exact inv_conj_mem_L hkL hB.t_mem_L) htNx
  have hc' : ∀ n ∈ N, n * (k * t * k⁻¹) = (k * t * k⁻¹) * n → y⁻¹ * n * y * n⁻¹ ∈ A := by
    intro n hnN hnx
    refine hB.mem_A_of_mem_conj hk ?_ ?_ ?_
    · have := W.N_norm y⁻¹ (inv_mem hyX) hyit n hnN
      rw [inv_inv] at this
      exact mul_mem this (inv_mem hnN)
    · rw [show y⁻¹ * n * y * n⁻¹ = y⁻¹ * (n * y * n⁻¹) by group]
      exact mul_mem (inv_mem hyAx) (hB.conj_norm hk (W.N_le hnN) hnx hyAx)
    · rw [show y⁻¹ * n * y * n⁻¹ = y⁻¹ * (n * y * n⁻¹) by group]
      exact mul_mem (inv_mem hyL) (conj_mem_L (hB.N_norm_L n hnN) hyL)
  refine hB.tv y hyL _ hxN fun a haA => ?_
  have haN := hB.A_le haA
  have hyaA : y * a * y⁻¹ ∈ A := hB.A_norm y hyX hyt a haA
  refine W.mem_centralizer_centralizer hxN hx1 hne (hB.A_le (mul_mem hyaA (inv_mem haA)))
    fun n hnN hnx => ?_
  rw [← comm_eq_one_iff, W.comm_mul_left (hB.A_le hyaA) (inv_mem haN) hnN]
  have hm : y⁻¹ * n * y = (y⁻¹ * n * y * n⁻¹) * n := by group
  have h1 : y * a * y⁻¹ * n * (y * a * y⁻¹)⁻¹ * n⁻¹ =
      y * (a * (y⁻¹ * n * y) * a⁻¹ * (y⁻¹ * n * y)⁻¹) * y⁻¹ := by group
  have hmN : y⁻¹ * n * y ∈ N := by
    have := W.N_norm y⁻¹ (inv_mem hyX) hyit n hnN
    rwa [inv_inv] at this
  have h2 : y * (a * (y⁻¹ * n * y) * a⁻¹ * (y⁻¹ * n * y)⁻¹) * y⁻¹ =
      a * (y⁻¹ * n * y) * a⁻¹ * (y⁻¹ * n * y)⁻¹ := by
    have hz := W.comm a haN _ hmN
    rcases eq_one_or_eq_of_mem_zpowers W.tt hz with h | h
    · rw [h]; group
    · rw [h, hyt]
      group
  have hcA := hc' n hnN hnx
  have h3 : a * (y⁻¹ * n * y) * a⁻¹ * (y⁻¹ * n * y)⁻¹ = a * n * a⁻¹ * n⁻¹ := by
    rw [hm, W.comm_mul_right haN (hB.A_le hcA) hnN,
      (comm_eq_one_iff a _).mpr (hB.A_comm a haA _ hcA), one_mul]
  rw [h1, h2, h3]
  have h4 := W.comm_mul_left haN (inv_mem haN) hnN
  simp only [mul_inv_cancel, one_mul, inv_one, mul_one] at h4
  exact h4.symm

theorem false {kτ e : O} (hB : B2Hyp W A L) (hkτ : kτ ∈ X) (hτL : kτ * t * kτ⁻¹ ∈ L)
    (hτN : kτ * t * kτ⁻¹ ∉ N) (heD : ∃ h ∈ X, h * t * h⁻¹ = e) (heL : e ∈ L) (heN : e ∈ N)
    (heNτ : e ∈ N.map (MulAut.conj kτ).toMonoidHom) (het : e ≠ t) : False := by
  obtain ⟨h, hh, rfl⟩ := heD
  obtain ⟨ke, hkeX, hkeL, hke⟩ := hB.L_fus h hh heL
  rw [← hke] at heL heN heNτ het
  have heA := hB.mem_A hkeX heL heN
  have T := W.conj hkτ
  have heτ : ke * t * ke⁻¹ ≠ kτ * t * kτ⁻¹ := fun h' => hτN (h' ▸ heN)
  have he' : (ke * kτ⁻¹) * (kτ * t * kτ⁻¹) * (ke * kτ⁻¹)⁻¹ = ke * t * ke⁻¹ := by group
  have hτNe := T.mem_map_conj_of_conj_mem (k := ke * kτ⁻¹) (mul_mem hkeX (inv_mem hkτ))
    (by rw [he']; exact heNτ) (by rw [he']; exact heτ)
  rw [mem_map_conj_iff, mem_map_conj_iff] at hτNe
  have e1 : ke⁻¹ * (kτ * t * kτ⁻¹) * ke = (ke⁻¹ * kτ) * t * (ke⁻¹ * kτ)⁻¹ := by group
  have hτAe : kτ * t * kτ⁻¹ ∈ A.map (MulAut.conj ke).toMonoidHom := by
    rw [mem_map_conj_iff, e1]
    refine hB.mem_A (mul_mem (inv_mem hkeX) hkτ) ?_ ?_
    · rw [← e1]
      exact inv_conj_mem_L hkeL hτL
    · rw [← e1]
      convert hτNe using 1
      group
  exact hτN (hB.faith _ hτL (hB.comm_mem_of_mem_conj hkeX hkeL heA het hτL hτAe))

end B2Hyp

end WeakSetting

end CFSG.LargeExtraspecial.S14
