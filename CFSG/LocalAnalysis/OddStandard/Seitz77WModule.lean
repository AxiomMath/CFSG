module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.OddStandard.Seitz77

open CFSG.ComponentClassification.PSL3Four

abbrev F4V : Type := Fin 2 → F4

@[expose] def cUp (γ : F4) (v : F4V) : F4V := ![v 0 + γ * v 1, v 1]

@[expose] def cLow (γ : F4) (v : F4V) : F4V := ![v 0, v 1 + γ * v 0]

@[expose] def dTor (v : F4V) : F4V := ![F4.ω * v 0, F4.ω * F4.ω * v 1]

structure ModData (M : Type) [AddCommGroup M] where
  two : ∀ m : M, m + m = 0
  π : M →+ F4V
  m₀ : M
  B : M →+ M →+ F4V
  q : M → F4V
  gU : F4 → (M ≃+ M)
  gL : F4 → (M ≃+ M)
  gT : M ≃+ M
  π_surj : Function.Surjective π
  π_m₀ : π m₀ = 0
  π_ker : ∀ m, π m = 0 → m = 0 ∨ m = m₀
  m₀_ne : m₀ ≠ 0
  B_symm : ∀ m m', B m m' = B m' m
  B_alt : ∀ m, B m m = 0
  q_add : ∀ m m', q (m + m') = q m + q m' + B m m'
  q_m₀ : q m₀ = 0
  B_m₀ : ∀ m, B m m₀ = π m
  gU_add : ∀ γ γ' m, gU (γ + γ') m = gU γ (gU γ' m)
  gL_add : ∀ γ γ' m, gL (γ + γ') m = gL γ (gL γ' m)
  gT_cube : ∀ m, gT (gT (gT m)) = m
  gU_m₀ : ∀ γ, gU γ m₀ = m₀
  gL_m₀ : ∀ γ, gL γ m₀ = m₀
  gT_m₀ : gT m₀ = m₀
  π_U : ∀ γ m, π (gU γ m) = cUp γ (π m)
  π_L : ∀ γ m, π (gL γ m) = cLow γ (π m)
  π_T : ∀ m, π (gT m) = dTor (π m)
  B_U : ∀ γ m m', B (gU γ m) (gU γ m') = cUp γ (B m m')
  B_L : ∀ γ m m', B (gL γ m) (gL γ m') = cLow γ (B m m')
  B_T : ∀ m m', B (gT m) (gT m') = dTor (B m m')
  q_U : ∀ γ m, q (gU γ m) = cUp γ (q m)
  q_L : ∀ γ m, q (gL γ m) = cLow γ (q m)
  q_T : ∀ m, q (gT m) = dTor (q m)

namespace WFacts

local instance decEqF4 : DecidableEq F4 := fun a b =>
  decidable_of_iff (a.code = b.code) ⟨fun h => F4.codeEquiv.injective h, fun h => by rw [h]⟩

theorem two : ∀ v : F4V, v + v = 0 := by decide

theorem exists_ne : ∀ γ₀ : F4, ∃ γ : F4, γ ≠ 0 ∧ γ ≠ γ₀ := by decide

theorem add_ne_zero : ∀ γ γ₀ : F4, γ ≠ γ₀ → γ + γ₀ ≠ 0 := by decide

theorem dTor_ne : ∀ v : F4V, dTor v = v → v = 0 := by decide

theorem dTor_sum : ∀ v : F4V, v + dTor v + dTor (dTor v) = 0 := by decide

theorem line_fact : ∀ (i : Fin 2) (u v : F4V), u i = 0 → v i = 0 → u ≠ 0 →
    v = 0 ∨ v = u ∨ v = dTor u ∨ v = u + dTor u := by decide

theorem decomp : ∀ v : F4V, v + ![v 0, 0] + ![0, v 1] = 0 := by decide

theorem zero_of : ∀ v : F4V, v 0 = 0 → v 1 = 0 → v = 0 := by decide

theorem cUp_fix : ∀ (γ : F4) (v : F4V), v 1 = 0 → cUp γ v = v := by decide

theorem cUp_fix' : ∀ γ : F4, γ ≠ 0 → ∀ v : F4V, cUp γ v = v → v 1 = 0 := by decide

theorem cUp_img : ∀ (γ : F4) (v : F4V), (cUp γ v + v) 1 = 0 := by decide

theorem cUp_pig : ∀ z : F4V, z 1 ≠ 0 → ∀ u : F4V,
    ¬ ∀ γ, cUp γ z + z = 0 ∨ cUp γ z + z = u := by decide

theorem cLow_fix : ∀ (γ : F4) (v : F4V), v 0 = 0 → cLow γ v = v := by decide

theorem cLow_fix' : ∀ γ : F4, γ ≠ 0 → ∀ v : F4V, cLow γ v = v → v 0 = 0 := by decide

theorem cLow_img : ∀ (γ : F4) (v : F4V), (cLow γ v + v) 0 = 0 := by decide

theorem cLow_pig : ∀ z : F4V, z 0 ≠ 0 → ∀ u : F4V,
    ¬ ∀ γ, cLow γ z + z = 0 ∨ cLow γ z + z = u := by decide

@[expose] def basisE : Fin 4 → F4V := ![![1, 0], ![F4.ω, 0], ![0, 1], ![0, F4.ω]]

@[expose] def lowA : Fin 4 → Fin 4 → ℤ :=
  ![![1, 0, 1, 0], ![0, 1, 0, 1], ![0, 0, 1, 0], ![0, 0, 0, 1]]

@[expose] def lowB : Fin 4 → Fin 4 → ℤ :=
  ![![1, 0, 0, 1], ![0, 1, 1, 1], ![0, 0, 1, 0], ![0, 0, 0, 1]]

theorem trans_words : ∀ v w : F4V, v ≠ 0 → w ≠ 0 →
    ∃ a b c e : F4, cUp a (cLow b (cUp c (cLow e v))) = w := by decide

theorem bits_indep : ∀ b : Fin 4 → Fin 2, ∑ i, (b i : ℕ) • basisE i = 0 → ∀ i, b i = 0 := by
  decide

theorem zsmul_cases (n : ℤ) (v : F4V) : (2 ∣ n ∧ n • v = 0) ∨ (¬ 2 ∣ n ∧ n • v = v) := by
  rcases Int.even_or_odd' n with ⟨k, hk | hk⟩
  · left
    refine ⟨⟨k, hk⟩, ?_⟩
    rw [hk, mul_zsmul', two_zsmul, two v, zsmul_zero]
  · right
    refine ⟨by omega, ?_⟩
    rw [hk, add_zsmul, mul_zsmul', two_zsmul, two v, zsmul_zero, zero_add, one_zsmul]

theorem basisE_indep (n : Fin 4 → ℤ) (h : ∑ i, n i • basisE i = 0) : ∀ i, 2 ∣ n i := by
  have hb : ∀ i, ∃ c : Fin 2, (c = 0 → 2 ∣ n i) ∧ ∀ v : F4V, n i • v = (c : ℕ) • v := by
    intro i
    by_cases hi : 2 ∣ n i
    · refine ⟨0, fun _ => hi, fun v => ?_⟩
      rcases zsmul_cases (n i) v with ⟨-, h2⟩ | ⟨h1, -⟩
      · rw [h2]; simp
      · exact absurd hi h1
    · refine ⟨1, fun h1 => absurd h1 (by decide), fun v => ?_⟩
      rcases zsmul_cases (n i) v with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact absurd h1 hi
      · rw [h2]; simp
  choose b hb0 hbv using hb
  have h' : ∑ i, (b i : ℕ) • basisE i = 0 := by
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => (hbv i _).symm
  exact fun i => hb0 i (bits_indep b h' i)

theorem cUp_one_basisE (j : Fin 4) : cUp 1 (basisE j) = ∑ i, lowA i j • basisE i := by
  revert j; decide

theorem cUp_omega_basisE (j : Fin 4) : cUp F4.ω (basisE j) = ∑ i, lowB i j • basisE i := by
  revert j; decide

theorem one_add_one : (1 : F4) + 1 = 0 := by decide

theorem omega_add_omega : F4.ω + F4.ω = 0 := by decide

theorem three_indep : ![(1 : F4), 0] ≠ (0 : F4V) ∧ ![F4.ω, 0] ≠ (0 : F4V) ∧
    ![(0 : F4), 1] ≠ (0 : F4V) ∧ (![(1 : F4), 0] + ![F4.ω, 0] : F4V) ≠ 0 ∧
    (![(1 : F4), 0] + ![(0 : F4), 1] : F4V) ≠ 0 ∧ (![F4.ω, 0] + ![(0 : F4), 1] : F4V) ≠ 0 ∧
    (![(1 : F4), 0] + (![F4.ω, 0] + ![(0 : F4), 1]) : F4V) ≠ 0 := by decide

end WFacts

namespace ModData

variable {M : Type} [AddCommGroup M] (D : ModData M)

include D

theorem neg_eq (m : M) : -m = m := neg_eq_of_add_eq_zero_right (D.two m)

theorem add_eq_zero_iff (a b : M) : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    have := neg_eq_of_add_eq_zero_right h
    rw [D.neg_eq] at this
    exact this
  · rintro rfl; exact D.two a

@[expose] def Nm (m : M) : M := m + D.gT m + D.gT (D.gT m)

theorem Nm_add (a b : M) : D.Nm (a + b) = D.Nm a + D.Nm b := by
  simp only [Nm, map_add]; abel

theorem Nm_zero : D.Nm 0 = 0 := by simp [Nm]

theorem Nm_m₀ : D.Nm D.m₀ = D.m₀ := by
  simp only [Nm, D.gT_m₀]
  rw [D.two, zero_add]

theorem Nm_gT (m : M) : D.Nm (D.gT m) = D.Nm m := by
  simp only [Nm, D.gT_cube]; abel

theorem π_Nm (m : M) : D.π (D.Nm m) = 0 := by
  simp only [Nm, map_add, D.π_T]
  exact WFacts.dTor_sum _

theorem Nm_cases (m : M) : D.Nm m = 0 ∨ D.Nm m = D.m₀ := D.π_ker _ (D.π_Nm m)

@[expose] def C : AddSubgroup M where
  carrier := {m | D.Nm m = 0}
  zero_mem' := D.Nm_zero
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [D.Nm_add, ha, hb, add_zero]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at *
    rw [D.neg_eq]; exact ha

theorem mem_C {m : M} : m ∈ D.C ↔ D.Nm m = 0 := Iff.rfl

theorem gT_mem_C {m : M} (h : m ∈ D.C) : D.gT m ∈ D.C := by
  rw [mem_C] at *; rw [D.Nm_gT]; exact h

theorem C_ker {c : M} (hc : c ∈ D.C) (h : D.π c = 0) : c = 0 := by
  rcases D.π_ker c h with h0 | h0
  · exact h0
  · exfalso
    rw [mem_C, h0, D.Nm_m₀] at hc
    exact D.m₀_ne hc

theorem C_inj {c c' : M} (hc : c ∈ D.C) (hc' : c' ∈ D.C) (h : D.π c = D.π c') : c = c' := by
  have h1 : c + c' ∈ D.C := D.C.add_mem hc hc'
  have h2 : D.π (c + c') = 0 := by
    rw [map_add, h]; exact WFacts.two _
  exact (D.add_eq_zero_iff c c').mp (D.C_ker h1 h2)

theorem C_surj (v : F4V) : ∃ c ∈ D.C, D.π c = v := by
  obtain ⟨m, hm⟩ := D.π_surj v
  rcases D.Nm_cases m with h | h
  · exact ⟨m, h, hm⟩
  · refine ⟨m + D.m₀, ?_, ?_⟩
    · rw [mem_C, D.Nm_add, h, D.Nm_m₀]; exact D.two _
    · rw [map_add, D.π_m₀, add_zero]; exact hm

theorem fiber_fixed (g : F4 → (M ≃+ M)) (c : F4 → F4V → F4V) (i : Fin 2)
    (g_add : ∀ γ γ' m, g (γ + γ') m = g γ (g γ' m))
    (g_m₀ : ∀ γ, g γ D.m₀ = D.m₀)
    (π_g : ∀ γ m, D.π (g γ m) = c γ (D.π m))
    (q_g : ∀ γ m, D.q (g γ m) = c γ (D.q m))
    (c_fix : ∀ γ v, v i = 0 → c γ v = v)
    (c_fix' : ∀ γ, γ ≠ 0 → ∀ v, c γ v = v → v i = 0) :
    ∀ m, (D.π m) i = 0 → ∀ γ, g γ m = m := by
  intro m hm γ₀
  by_contra hne
  have g0 : ∀ m, g 0 m = m := by
    intro m
    have h := g_add 0 0 m
    rw [add_zero] at h
    exact ((g 0).injective h).symm
  have hcases : ∀ γ, g γ m = m ∨ g γ m = m + D.m₀ := by
    intro γ
    have h1 : D.π (g γ m + m) = 0 := by
      rw [map_add, π_g, c_fix γ _ hm]
      exact WFacts.two _
    rcases D.π_ker _ h1 with h | h
    · left; exact (D.add_eq_zero_iff _ _).mp h
    · right
      calc g γ m = (g γ m + m) + m := by rw [add_assoc, D.two, add_zero]
        _ = D.m₀ + m := by rw [h]
        _ = m + D.m₀ := add_comm _ _
  have hγ₀0 : γ₀ ≠ 0 := by rintro rfl; exact hne (g0 m)
  obtain ⟨γ, hγ0, hγγ₀⟩ := WFacts.exists_ne γ₀
  have hγ₀m : g γ₀ m = m + D.m₀ := (hcases γ₀).resolve_left hne
  have hex : ∃ γ₁, γ₁ ≠ 0 ∧ g γ₁ m = m := by
    rcases hcases γ with h | h
    · exact ⟨γ, hγ0, h⟩
    · refine ⟨γ + γ₀, WFacts.add_ne_zero γ γ₀ hγγ₀, ?_⟩
      rw [g_add, hγ₀m, map_add, g_m₀, h, add_assoc, D.two, add_zero]
  obtain ⟨γ₁, hγ₁0, hγ₁⟩ := hex
  have hz1 : c γ₁ (D.q m) = D.q m := by rw [← q_g, hγ₁]
  have hz2 : (D.q m) i = 0 := c_fix' γ₁ hγ₁0 _ hz1
  have hz3 : c γ₀ (D.q m) = D.q m := c_fix γ₀ _ hz2
  have h3 : D.q (m + D.m₀) = D.q m + D.π m := by rw [D.q_add, D.q_m₀, D.B_m₀, add_zero]
  have h4 : D.q (g γ₀ m) = D.q m := by rw [q_g, hz3]
  rw [hγ₀m, h3] at h4
  have h5 : D.π m = 0 := by
    have h6 : D.q m + D.π m = D.q m + 0 := by rw [add_zero]; exact h4
    exact add_left_cancel h6
  rcases D.π_ker m h5 with h | h
  · exact hne (by rw [h, map_zero])
  · exact hne (by rw [h, g_m₀])

theorem B_gT_self {c : M} (hc : c ∈ D.C) : D.B c (D.gT c) = 0 := by
  have h1 : D.gT (D.gT c) = c + D.gT c := by
    have h0 := hc
    rw [mem_C, Nm] at h0
    exact ((D.add_eq_zero_iff (c + D.gT c) (D.gT (D.gT c))).mp h0).symm
  have h2 : D.B (D.gT c) (D.gT (D.gT c)) = dTor (D.B c (D.gT c)) := D.B_T c (D.gT c)
  have h3 : D.B (D.gT c) (D.gT (D.gT c)) = D.B c (D.gT c) := by
    rw [h1, map_add, D.B_alt, add_zero, D.B_symm]
  rw [h3] at h2
  exact WFacts.dTor_ne _ h2.symm

theorem B_zero_on_line (i : Fin 2) {c c' : M} (hc : c ∈ D.C) (hc' : c' ∈ D.C)
    (hi : (D.π c) i = 0) (hi' : (D.π c') i = 0) : D.B c c' = 0 := by
  by_cases hu : D.π c = 0
  · rw [D.C_ker hc hu]; simp
  · rcases WFacts.line_fact i _ _ hi hi' hu with h | h | h | h
    · rw [D.C_ker hc' h]; simp
    · rw [D.C_inj hc' hc h]; exact D.B_alt c
    · have : c' = D.gT c := D.C_inj hc' (D.gT_mem_C hc) (h.trans (D.π_T c).symm)
      rw [this]; exact D.B_gT_self hc
    · have : c' = c + D.gT c :=
        D.C_inj hc' (D.C.add_mem hc (D.gT_mem_C hc)) (by rw [h, map_add, D.π_T])
      rw [this, map_add, D.B_alt, D.B_gT_self hc, add_zero]

theorem claimG (g : F4 → (M ≃+ M)) (c : F4 → F4V → F4V) (i : Fin 2)
    (g_add : ∀ γ γ' m, g (γ + γ') m = g γ (g γ' m))
    (g_m₀ : ∀ γ, g γ D.m₀ = D.m₀)
    (π_g : ∀ γ m, D.π (g γ m) = c γ (D.π m))
    (B_g : ∀ γ m m', D.B (g γ m) (g γ m') = c γ (D.B m m'))
    (q_g : ∀ γ m, D.q (g γ m) = c γ (D.q m))
    (c_fix : ∀ γ v, v i = 0 → c γ v = v)
    (c_fix' : ∀ γ, γ ≠ 0 → ∀ v, c γ v = v → v i = 0)
    (c_img : ∀ γ v, (c γ v + v) i = 0)
    (c_pig : ∀ z : F4V, z i ≠ 0 → ∀ u : F4V, ¬ ∀ γ, c γ z + z = 0 ∨ c γ z + z = u)
    {m : M} (hm : m ∈ D.C) (hmi : (D.π m) i = 0) (hm0 : m ≠ 0) (w : M) :
    (D.B m w) i = 0 ∧ ∀ γ, (g γ w + w ∈ D.C ∧ (D.π (g γ w + w)) i = 0) := by
  have hfix := D.fiber_fixed g c i g_add g_m₀ π_g q_g c_fix c_fix'
  have hπm : D.π m ≠ 0 := fun h => hm0 (D.C_ker hm h)
  have aux : ∀ γ, ∃ c₀ ∈ D.C, (D.π c₀) i = 0 ∧
      ((g γ w + w = c₀ ∧ c γ (D.B m w) + D.B m w = 0) ∨
       (g γ w + w = c₀ + D.m₀ ∧ c γ (D.B m w) + D.B m w = D.π m)) := by
    intro γ
    have h1 : D.B m (g γ w) = c γ (D.B m w) := by
      have := B_g γ m w
      rwa [hfix m hmi γ] at this
    have h2 : D.B m (g γ w + w) = c γ (D.B m w) + D.B m w := by rw [map_add, h1]
    have h3 : (D.π (g γ w + w)) i = 0 := by
      rw [map_add, π_g]; exact c_img γ _
    obtain ⟨c₀, hc₀, hπc₀⟩ := D.C_surj (D.π (g γ w + w))
    have h4 : D.B m c₀ = 0 :=
      D.B_zero_on_line i hm hc₀ hmi (by rw [hπc₀]; exact h3)
    have h5 : g γ w + w = c₀ ∨ g γ w + w = c₀ + D.m₀ := by
      have h6 : D.π (g γ w + w + c₀) = 0 := by
        rw [map_add, hπc₀]; exact WFacts.two _
      rcases D.π_ker _ h6 with h | h
      · left; exact (D.add_eq_zero_iff _ _).mp h
      · right
        calc g γ w + w = (g γ w + w + c₀) + c₀ := by rw [add_assoc, D.two, add_zero]
          _ = D.m₀ + c₀ := by rw [h]
          _ = c₀ + D.m₀ := add_comm _ _
    refine ⟨c₀, hc₀, by rw [hπc₀]; exact h3, ?_⟩
    rcases h5 with h | h
    · left
      refine ⟨h, ?_⟩
      rw [← h2, h, h4]
    · right
      refine ⟨h, ?_⟩
      rw [← h2, h, map_add, h4, D.B_m₀, zero_add]
  have key : ∀ γ, c γ (D.B m w) + D.B m w = 0 ∨ c γ (D.B m w) + D.B m w = D.π m := by
    intro γ
    obtain ⟨c₀, hc₀, -, h | h⟩ := aux γ
    exacts [Or.inl h.2, Or.inr h.2]
  have hz : (D.B m w) i = 0 := by
    by_contra hne
    exact c_pig _ hne (D.π m) key
  refine ⟨hz, fun γ => ?_⟩
  obtain ⟨c₀, hc₀, hci, h | h⟩ := aux γ
  · rw [h.1]; exact ⟨hc₀, hci⟩
  · exfalso
    have h0 : c γ (D.B m w) + D.B m w = 0 := by rw [c_fix γ _ hz]; exact WFacts.two _
    rw [h0] at h
    exact hπm h.2.symm

theorem decomp {x : M} (hx : x ∈ D.C) :
    ∃ x₁ ∈ D.C, ∃ x₂ ∈ D.C, (D.π x₁) 1 = 0 ∧ (D.π x₂) 0 = 0 ∧ x = x₁ + x₂ := by
  obtain ⟨x₁, h1, hπ1⟩ := D.C_surj ![(D.π x) 0, 0]
  obtain ⟨x₂, h2, hπ2⟩ := D.C_surj ![0, (D.π x) 1]
  refine ⟨x₁, h1, x₂, h2, by rw [hπ1]; rfl, by rw [hπ2]; rfl, ?_⟩
  have h3 : D.π (x + x₁ + x₂) = 0 := by
    rw [map_add, map_add, hπ1, hπ2]; exact WFacts.decomp _
  have h4 : x + x₁ + x₂ = 0 := D.C_ker (D.C.add_mem (D.C.add_mem hx h1) h2) h3
  have h5 : x + (x₁ + x₂) = 0 := by rwa [← add_assoc]
  exact (eq_neg_of_add_eq_zero_left h5).trans (D.neg_eq _)

theorem claimG_U {m : M} (hm : m ∈ D.C) (hmi : (D.π m) 1 = 0) (hm0 : m ≠ 0) (w : M) :
    (D.B m w) 1 = 0 ∧ ∀ γ, (D.gU γ w + w ∈ D.C ∧ (D.π (D.gU γ w + w)) 1 = 0) :=
  D.claimG D.gU cUp 1 D.gU_add D.gU_m₀ D.π_U D.B_U D.q_U WFacts.cUp_fix WFacts.cUp_fix'
    WFacts.cUp_img WFacts.cUp_pig hm hmi hm0 w

theorem claimG_L {m : M} (hm : m ∈ D.C) (hmi : (D.π m) 0 = 0) (hm0 : m ≠ 0) (w : M) :
    (D.B m w) 0 = 0 ∧ ∀ γ, (D.gL γ w + w ∈ D.C ∧ (D.π (D.gL γ w + w)) 0 = 0) :=
  D.claimG D.gL cLow 0 D.gL_add D.gL_m₀ D.π_L D.B_L D.q_L WFacts.cLow_fix WFacts.cLow_fix'
    WFacts.cLow_img WFacts.cLow_pig hm hmi hm0 w

theorem fix_U : ∀ m, (D.π m) 1 = 0 → ∀ γ, D.gU γ m = m :=
  D.fiber_fixed D.gU cUp 1 D.gU_add D.gU_m₀ D.π_U D.q_U WFacts.cUp_fix WFacts.cUp_fix'

theorem fix_L : ∀ m, (D.π m) 0 = 0 → ∀ γ, D.gL γ m = m :=
  D.fiber_fixed D.gL cLow 0 D.gL_add D.gL_m₀ D.π_L D.q_L WFacts.cLow_fix WFacts.cLow_fix'

theorem img_U (w : M) (γ : F4) : D.gU γ w + w ∈ D.C := by
  obtain ⟨m, hm, hπ⟩ := D.C_surj ![1, 0]
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    have := congrFun hπ 0
    simp at this
  exact ((D.claimG_U hm (by rw [hπ]; rfl) hm0 w).2 γ).1

theorem img_L (w : M) (γ : F4) : D.gL γ w + w ∈ D.C := by
  obtain ⟨m, hm, hπ⟩ := D.C_surj ![0, 1]
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    have := congrFun hπ 1
    simp at this
  exact ((D.claimG_L hm (by rw [hπ]; rfl) hm0 w).2 γ).1

theorem B_cross {x y : M} (hx : x ∈ D.C) (hy : y ∈ D.C) (hxi : (D.π x) 1 = 0)
    (hyi : (D.π y) 0 = 0) : D.B x y = 0 := by
  by_cases hx0 : x = 0
  · rw [hx0]; simp
  by_cases hy0 : y = 0
  · rw [hy0]; simp
  have h1 : (D.B x y) 1 = 0 := (D.claimG_U hx hxi hx0 y).1
  have h2 : (D.B y x) 0 = 0 := (D.claimG_L hy hyi hy0 x).1
  rw [D.B_symm] at h2
  exact WFacts.zero_of _ h2 h1

theorem exists_complement' :
    ∃ C : AddSubgroup M, (∀ x ∈ C, ∀ y ∈ C, D.B x y = 0) ∧ (∀ γ, ∀ x ∈ C, D.gU γ x ∈ C) ∧
      (∀ γ, ∀ x ∈ C, D.gL γ x ∈ C) ∧ (∀ x ∈ C, D.gT x ∈ C) ∧ (∀ v, ∃ c ∈ C, D.π c = v) ∧
      (∀ c ∈ C, D.π c = 0 → c = 0) := by
  refine ⟨D.C, ?_, ?_, ?_, fun x hx => D.gT_mem_C hx, D.C_surj, fun c hc h => D.C_ker hc h⟩
  · intro x hx y hy
    obtain ⟨x₁, hx₁, x₂, hx₂, hx₁i, hx₂i, rfl⟩ := D.decomp hx
    obtain ⟨y₁, hy₁, y₂, hy₂, hy₁i, hy₂i, rfl⟩ := D.decomp hy
    have e11 := D.B_zero_on_line 1 hx₁ hy₁ hx₁i hy₁i
    have e22 := D.B_zero_on_line 0 hx₂ hy₂ hx₂i hy₂i
    have e12 := D.B_cross hx₁ hy₂ hx₁i hy₂i
    have e21 : D.B x₂ y₁ = 0 := by rw [D.B_symm]; exact D.B_cross hy₁ hx₂ hy₁i hx₂i
    simp only [map_add, AddMonoidHom.add_apply, e11, e22, e12, e21, add_zero]
  · intro γ x hx
    obtain ⟨x₁, hx₁, x₂, hx₂, hx₁i, hx₂i, rfl⟩ := D.decomp hx
    have h1 : D.gU γ x₁ = x₁ := D.fix_U x₁ hx₁i γ
    have h2 : D.gU γ (x₁ + x₂) = x₁ + x₂ + (D.gU γ x₂ + x₂) := by
      rw [map_add, h1,
        show x₁ + x₂ + (D.gU γ x₂ + x₂) = x₁ + D.gU γ x₂ + (x₂ + x₂) by abel, D.two, add_zero]
    rw [h2]
    exact D.C.add_mem (D.C.add_mem hx₁ hx₂) (D.img_U x₂ γ)
  · intro γ x hx
    obtain ⟨x₁, hx₁, x₂, hx₂, hx₁i, hx₂i, rfl⟩ := D.decomp hx
    have h1 : D.gL γ x₂ = x₂ := D.fix_L x₂ hx₂i γ
    have h2 : D.gL γ (x₁ + x₂) = x₁ + x₂ + (D.gL γ x₁ + x₁) := by
      rw [map_add, h1,
        show x₁ + x₂ + (D.gL γ x₁ + x₁) = D.gL γ x₁ + x₂ + (x₁ + x₁) by abel, D.two, add_zero]
    rw [h2]
    exact D.C.add_mem (D.C.add_mem hx₁ hx₂) (D.img_L x₁ γ)

end ModData

end CFSG.OddStandard.Seitz77
