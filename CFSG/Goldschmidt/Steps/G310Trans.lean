module

public import CFSG.Goldschmidt.Steps.G310TransTools
public import CFSG.Goldschmidt.Steps.G310TransQuot

public section

namespace CFSG.Goldschmidt.G310

open CFSG.Open

variable {X : Type*} [Group X] [Finite X]

theorem nconj_of_core_trivial (A : Sylow 2 X) (hAab : IsMulCommutative (A : Subgroup X))
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hO : ∀ N : Subgroup X, N.Normal → Odd (Nat.card N) → N = ⊥)
    (hZ : Subgroup.center X = ⊥)
    (hIH : ∀ C : Subgroup X, C ≠ ⊤ → (A : Subgroup X) ≤ C → ∀ Q Q' : Subgroup C,
      IsMaxInv ((A : Subgroup X).subgroupOf C) p Q →
      IsMaxInv ((A : Subgroup X).subgroupOf C) p Q' → NConj ((A : Subgroup X).subgroupOf C) Q Q')
    {P P' : Subgroup X} (hP : IsMaxInv (A : Subgroup X) p P)
    (hP' : IsMaxInv (A : Subgroup X) p P') : NConj (A : Subgroup X) P P' := by
  classical
  set A' : Subgroup X := (A : Subgroup X) with hA'def
  have hp : p.Prime := Fact.out
  have hoddp : ∀ Q : Subgroup X, IsPGroup p Q → ¬ 2 ∣ Nat.card Q := by
    intro Q hQ h2
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
    rw [hk] at h2
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (Nat.prime_two.dvd_of_dvd_pow h2)
    exact hp2 this.symm
  by_contra hne
  have hfin : Set.Finite {pq : Subgroup X × Subgroup X |
      IsMaxInv A' p pq.1 ∧ IsMaxInv A' p pq.2 ∧ ¬ NConj A' pq.1 pq.2} := Set.toFinite _
  obtain ⟨⟨P₀, P₀'⟩, hmax⟩ := hfin.exists_maximalFor
    (fun pq => Nat.card (pq.1 ⊓ pq.2 : Subgroup X)) _ ⟨(P, P'), hP, hP', hne⟩
  obtain ⟨hP₀, hP₀', hne₀⟩ := hmax.prop
  have key : ∀ Q Q' : Subgroup X, IsMaxInv A' p Q → IsMaxInv A' p Q' →
      Nat.card (P₀ ⊓ P₀' : Subgroup X) < Nat.card (Q ⊓ Q' : Subgroup X) → NConj A' Q Q' := by
    intro Q Q' hQ hQ' hlt
    by_contra hQQ
    have := hmax.2 (j := (Q, Q')) ⟨hQ, hQ', hQQ⟩ hlt.le
    exact absurd this (not_le.mpr hlt)
  have step : ∀ Q Q' : Subgroup X, IsMaxInv A' p Q → IsMaxInv A' p Q' → ∀ C : Subgroup X,
      C ≠ ⊤ → A' ≤ C →
      Nat.card (P₀ ⊓ P₀' : Subgroup X) < Nat.card (Q ⊓ C : Subgroup X) →
      Nat.card (P₀ ⊓ P₀' : Subgroup X) < Nat.card (Q' ⊓ C : Subgroup X) → NConj A' Q Q' := by
    intro Q Q' hQ hQ' C hC hAC h1 h2
    have hAC' : A' ≤ Subgroup.normalizer (C : Set X) := hAC.trans Subgroup.le_normalizer
    have hW : IsInv A' p (Q ⊓ C) :=
      ⟨hQ.isInv.1.to_le inf_le_left, le_normalizer_inf hQ.isInv.2 hAC'⟩
    have hW' : IsInv A' p (Q' ⊓ C) :=
      ⟨hQ'.isInv.1.to_le inf_le_left, le_normalizer_inf hQ'.isInv.2 hAC'⟩
    obtain ⟨y, hy, P₂, hP₂, hyW, hW'P₂⟩ :=
      exists_overgroup_of_le hAC (hIH C hC hAC) hW hW' inf_le_right inf_le_right
    have hQy := hQ.conjSub hy
    have c1 : NConj A' (conjSub y Q) P₂ := by
      refine key _ _ hQy hP₂ (lt_of_lt_of_le h1 ?_)
      rw [← card_conjSub y (Q ⊓ C)]
      exact Subgroup.card_le_of_le (le_inf (conjSub_mono inf_le_left) hyW)
    have c2 : NConj A' P₂ Q' := by
      refine key _ _ hP₂ hQ' (lt_of_lt_of_le h2 ?_)
      exact Subgroup.card_le_of_le (le_inf hW'P₂ inf_le_left)
    exact (nconj_conjSub Q hy).trans (c1.trans c2)
  by_cases hR : P₀ ⊓ P₀' = ⊥
  swap
  ·
    apply hne₀
    set R := P₀ ⊓ P₀' with hRdef
    set C := Subgroup.normalizer (R : Set X) with hCdef
    have hRp : IsPGroup p R := hP₀.isInv.1.to_le inf_le_left
    have hCtop : C ≠ ⊤ := by
      intro h
      have hRn : R.Normal := Subgroup.normalizer_eq_top_iff.mp h
      exact hR (hO R hRn (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (hoddp R hRp))))
    have hAC : A' ≤ C := le_normalizer_inf hP₀.isInv.2 hP₀'.isInv.2
    have hRP₀ : R ≠ P₀ := by
      intro h
      apply hne₀
      have hle : P₀ ≤ P₀' := h ▸ inf_le_right
      rw [hP₀.eq_of_le hP₀'.isInv hle]
      exact NConj.refl _
    have hRP₀' : R ≠ P₀' := by
      intro h
      apply hne₀
      have hle : P₀' ≤ P₀ := h ▸ inf_le_left
      rw [hP₀'.eq_of_le hP₀.isInv hle]
      exact NConj.refl _
    exact step P₀ P₀' hP₀ hP₀' C hCtop hAC
      (Subgroup.card_lt_of_lt (lt_inf_normalizer hP₀.isInv.1 inf_le_left hRP₀))
      (Subgroup.card_lt_of_lt (lt_inf_normalizer hP₀'.isInv.1 inf_le_right hRP₀'))
  have hcard1 : Nat.card (P₀ ⊓ P₀' : Subgroup X) = 1 := by
    rw [hR]; exact Subgroup.card_bot
  have step4 : ∀ Q Q' : Subgroup X, IsMaxInv A' p Q → IsMaxInv A' p Q' → ¬ NConj A' Q Q' →
      ∀ a ∈ A', a ≠ 1 → Q ⊓ Subgroup.centralizer ({a} : Set X) = ⊥ ∨
        Q' ⊓ Subgroup.centralizer ({a} : Set X) = ⊥ := by
    intro Q Q' hQ hQ' hQQ a ha ha1
    by_contra h
    push Not at h
    apply hQQ
    have hCtop : Subgroup.centralizer ({a} : Set X) ≠ ⊤ := by
      intro htop
      apply ha1
      have haZ : a ∈ Subgroup.center X := by
        rw [Subgroup.mem_center_iff]
        intro g
        have hg : g ∈ Subgroup.centralizer ({a} : Set X) := htop ▸ Subgroup.mem_top g
        exact Subgroup.mem_centralizer_singleton_iff.mp hg
      rw [hZ] at haZ
      exact Subgroup.mem_bot.mp haZ
    have hAC : A' ≤ Subgroup.centralizer ({a} : Set X) := fun b hb =>
      Subgroup.mem_centralizer_singleton_iff.mpr (mul_comm_of_isMulCommutative hAab hb ha)
    refine step Q Q' hQ hQ' _ hCtop hAC ?_ ?_
    · rw [hcard1]; exact (Subgroup.one_lt_card_iff_ne_bot _).mpr h.1
    · rw [hcard1]; exact (Subgroup.one_lt_card_iff_ne_bot _).mpr h.2
  have hP₀ne : P₀ ≠ ⊥ := by
    intro h
    apply hne₀
    have hle : P₀ ≤ P₀' := h ▸ bot_le
    rw [hP₀.eq_of_le hP₀'.isInv hle]
    exact NConj.refl _
  have hP₀'ne : P₀' ≠ ⊥ := by
    intro h
    apply hne₀
    have hle : P₀' ≤ P₀ := h ▸ bot_le
    rw [hP₀'.eq_of_le hP₀.isInv hle]
    exact NConj.refl _
  set E : Subgroup X := Omega1 A' with hEdef
  have hEA : E ≤ A' := fun e he => (sq_eq_one_of_mem_omega1 hAab he).1
  have hE2 : ∀ e ∈ E, e ^ 2 = 1 := fun e he => (sq_eq_one_of_mem_omega1 hAab he).2
  have hEab : IsMulCommutative E :=
    ⟨⟨fun a b => Subtype.ext (mul_comm_of_isMulCommutative hAab (hEA a.2) (hEA b.2))⟩⟩
  have hNE : ¬ Subgroup.normalizer (A' : Set X) ≤ Subgroup.centralizer (E : Set X) := by
    intro h
    have htop := eq_top_of_normalizer_le_centralizer_omega1 A hAab hO h
    apply hP₀ne
    have hcen : Subgroup.center X = ⊤ := by
      rw [eq_top_iff]
      intro z _
      rw [Subgroup.mem_center_iff]
      intro g
      have hz : z ∈ A' := by rw [hA'def, htop]; exact Subgroup.mem_top z
      have hg : g ∈ A' := by rw [hA'def, htop]; exact Subgroup.mem_top g
      exact mul_comm_of_isMulCommutative hAab hg hz
    rw [hZ] at hcen
    rw [eq_bot_iff]
    intro z _
    have : z ∈ (⊤ : Subgroup X) := Subgroup.mem_top z
    rwa [← hcen] at this
  obtain ⟨x, hxN, hxE⟩ := IsConcreteLE.not_le_iff_exists.mp hNE
  have hEne : E ≠ ⊥ := by
    intro h
    apply hxE
    rw [h, Subgroup.mem_centralizer_iff]
    intro e he
    rw [Subgroup.coe_bot, Set.mem_singleton_iff] at he
    rw [he, one_mul, mul_one]
  have hEP₀ : E ≤ Subgroup.normalizer (P₀ : Set X) := hEA.trans hP₀.isInv.2
  have hEP₀' : E ≤ Subgroup.normalizer (P₀' : Set X) := hEA.trans hP₀'.isInv.2
  obtain ⟨B₀, hB₀, x₀, hx₀P, hx₀1, hx₀B⟩ :=
    exists_hyperplane_fixed hE2 hEab hEne (hoddp P₀ hP₀.isInv.1) hP₀ne hEP₀
  obtain ⟨B₁, hB₁, x₁, hx₁P, hx₁1, hx₁B⟩ :=
    exists_hyperplane_fixed hE2 hEab hEne (hoddp P₀' hP₀'.isInv.1) hP₀'ne hEP₀'
  have hcent : ∀ {Q : Subgroup X} {z e : X}, z ∈ Q → e * z = z * e →
      z ∈ Q ⊓ Subgroup.centralizer ({e} : Set X) := fun hz he =>
    ⟨hz, Subgroup.mem_centralizer_singleton_iff.mpr he.symm⟩
  by_cases hB : ∃ b ∈ B₀ ⊓ B₁, b ≠ 1
  · obtain ⟨b, hb, hb1⟩ := hB
    have hb1' : (b : X) ≠ 1 := fun h => hb1 (Subtype.ext h)
    rcases step4 P₀ P₀' hP₀ hP₀' hne₀ b (hEA b.2) hb1' with h | h
    · apply hx₀1
      have := hcent hx₀P (hx₀B b hb.1)
      rw [h] at this
      exact Subgroup.mem_bot.mp this
    · apply hx₁1
      have := hcent hx₁P (hx₁B b hb.2)
      rw [h] at this
      exact Subgroup.mem_bot.mp this
  push Not at hB
  have hinf : B₀ ⊓ B₁ = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    rw [Subgroup.mem_bot]
    exact hB b hb
  have hcardE : Nat.card E ≤ 4 := by
    have h := Subgroup.index_inf_le (H := B₀) (K := B₁)
    rw [hinf, Subgroup.index_bot, hB₀, hB₁] at h
    exact h
  have hNEn : Subgroup.normalizer (A' : Set X) ≤ Subgroup.normalizer (E : Set X) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro e
    constructor
    · intro he
      exact mem_omega1 (conj_mem_of_mem_normalizer hy (hEA he))
        (by rw [conj_pow, hE2 e he]; group)
    · intro he
      have he' : e = y⁻¹ * (y * e * y⁻¹) * y := by group
      rw [he']
      exact mem_omega1 (conj_inv_mem_of_mem_normalizer hy (hEA he))
        (by rw [show y⁻¹ * (y * e * y⁻¹) * y = y⁻¹ * (y * e * y⁻¹) * y⁻¹⁻¹ by rw [inv_inv],
          conj_pow, hE2 _ he]; group)
  have hmove : ∃ e ∈ E, x⁻¹ * e * x ≠ e := by
    by_contra h
    push Not at h
    apply hxE
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have := h e he
    calc e * x = x * (x⁻¹ * e * x) := by group
      _ = x * e := by rw [this]
  obtain ⟨e, heE, hxe⟩ := hmove
  have hE2grp : IsPGroup 2 E := A.isPGroup'.to_le hEA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hE2grp
  have hk1 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact hEne ((Subgroup.card_eq_one).mp hk)
  have hk2 : k ≤ 2 := by
    by_contra hk2
    have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have he1 : e ≠ 1 := by
    rintro rfl
    exact hxe (by group)
  have hxeE : x⁻¹ * e * x ∈ E := conj_inv_mem_of_mem_normalizer (hNEn hxN) heE
  have hxe1 : x⁻¹ * e * x ≠ 1 := by
    intro h
    apply he1
    calc e = x * (x⁻¹ * e * x) * x⁻¹ := by group
      _ = 1 := by rw [h]; group
  rcases (show k = 1 ∨ k = 2 by omega) with rfl | rfl
  ·
    have := three_le_card E.one_mem heE hxeE (Ne.symm he1) (Ne.symm hxe1) (Ne.symm hxe)
    rw [hk] at this
    norm_num at this
  ·
    have hE4 : Nat.card E = 4 := by rw [hk]; norm_num
    have hcardB : ∀ B : Subgroup E, B.index = 2 → ∃ b ∈ B, (b : X) ≠ 1 := by
      intro B hB
      have h := B.card_mul_index
      rw [hB, hE4] at h
      have hB2 : Nat.card B = 2 := by omega
      have : B ≠ ⊥ := by
        intro hbot
        rw [hbot, Subgroup.card_bot] at hB2
        norm_num at hB2
      obtain ⟨b, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp this
      exact ⟨b, b.2, fun h => hb1 (Subtype.ext (Subtype.ext h))⟩
    obtain ⟨e₀, he₀B, he₀1⟩ := hcardB B₀ hB₀
    obtain ⟨e₁, he₁B, he₁1⟩ := hcardB B₁ hB₁
    have h01 : (e₀ : X) ≠ e₁ := by
      intro h
      have : e₀ = e₁ := Subtype.ext h
      have := hB e₀ ⟨he₀B, this ▸ he₁B⟩
      exact he₀1 (by rw [this]; rfl)
    set N := Subgroup.normalizer (A' : Set X) with hNdef
    set K := N ⊓ Subgroup.centralizer (E : Set X) with hKdef
    have hAK : A' ≤ K := le_inf Subgroup.le_normalizer (fun b hb =>
      Subgroup.mem_centralizer_iff.mpr fun e he =>
        mul_comm_of_isMulCommutative hAab (hEA he) hb)
    have hKN : K ≤ N := inf_le_left
    have hKnormal : (K.subgroupOf N).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKN).mpr
        (le_normalizer_inf Subgroup.le_normalizer
          (hNEn.trans (normalizer_le_normalizer_centralizer' E)))
    have hsq : ∀ y ∈ N, y ^ 2 ∈ Subgroup.centralizer (E : Set X) →
        y ∈ Subgroup.centralizer (E : Set X) := fun y hyN hy2 =>
      (mem_of_sq_mem_of_odd_index hKnormal (odd_index_of_sylow_le A hAK hKN) hyN
        ⟨N.pow_mem hyN 2, hy2⟩).2
    obtain ⟨y, hyN, hy⟩ := exists_conj_of_card_four hE4 hE2 hNEn hsq hxN hxE e₀.2 e₁.2 h01
      he₀1 he₁1
    have hQ := hP₀.conjSub hyN
    have hnc : ¬ NConj A' (conjSub y P₀) P₀' := fun h => hne₀ ((nconj_conjSub P₀ hyN).trans h)
    rcases step4 _ P₀' hQ hP₀' hnc e₁ (hEA e₁.2) he₁1 with h | h
    · apply hx₀1
      have hmem : y⁻¹ * x₀ * y ∈ conjSub y P₀ ⊓ Subgroup.centralizer ({(e₁ : X)} : Set X) := by
        refine hcent (mem_conjSub.mpr (by group; exact hx₀P)) ?_
        rw [← hy]
        have := hx₀B e₀ he₀B
        calc y⁻¹ * (e₀ : X) * y * (y⁻¹ * x₀ * y) = y⁻¹ * ((e₀ : X) * x₀) * y := by group
          _ = y⁻¹ * (x₀ * e₀) * y := by rw [this]
          _ = y⁻¹ * x₀ * y * (y⁻¹ * e₀ * y) := by group
      rw [h, Subgroup.mem_bot] at hmem
      calc x₀ = y * (y⁻¹ * x₀ * y) * y⁻¹ := by group
        _ = 1 := by rw [hmem]; group
    · apply hx₁1
      have := hcent hx₁P (hx₁B e₁ he₁B)
      rw [h] at this
      exact Subgroup.mem_bot.mp this

end CFSG.Goldschmidt.G310

namespace CFSG.Goldschmidt.G310

open CFSG.Open

theorem nconj_of_isMaxInv : ∀ (n : ℕ) (X : Type) [Group X] [Finite X], Nat.card X = n →
    ∀ (A : Sylow 2 X), IsMulCommutative (A : Subgroup X) → ∀ {p : ℕ} [Fact p.Prime], p ≠ 2 →
    ∀ {P P' : Subgroup X}, IsMaxInv (A : Subgroup X) p P → IsMaxInv (A : Subgroup X) p P' →
    NConj (A : Subgroup X) P P' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X _ _ hn A hA p _ hp2 P P' hP hP'
  by_cases hO : ∃ N : Subgroup X, N.Normal ∧ ¬ 2 ∣ Nat.card N ∧ N ≠ ⊥
  · obtain ⟨N, hNn, hNodd, hNne⟩ := hO
    let Abar : Sylow 2 (X ⧸ N) := A.mapSurjective (QuotientGroup.mk'_surjective N)
    have hAbar : (Abar : Subgroup (X ⧸ N)) = (A : Subgroup X).map (QuotientGroup.mk' N) :=
      Sylow.coe_mapSurjective _ _
    have hcard : Nat.card (X ⧸ N) < n := by
      rw [← hn, Subgroup.card_eq_card_quotient_mul_card_subgroup N]
      have h1 : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).mpr hNne
      have h0 : 0 < Nat.card (X ⧸ N) := Nat.card_pos
      nlinarith
    refine nconj_of_quotient_odd hNodd A hp2 (fun Q Q' hQ hQ' => ?_) hP hP'
    have hAab : IsMulCommutative (Abar : Subgroup (X ⧸ N)) := by
      rw [hAbar]; exact CFSG.Goldschmidt.isMulCommutative_map hA _
    have := ih _ hcard (X ⧸ N) rfl Abar hAab hp2 (P := Q) (P' := Q')
      (by rw [hAbar]; exact hQ) (by rw [hAbar]; exact hQ')
    rwa [hAbar] at this
  push Not at hO
  have hO' : ∀ N : Subgroup X, N.Normal → ¬ 2 ∣ Nat.card N → N = ⊥ := hO
  by_cases hZ : Subgroup.center X = ⊥
  · refine nconj_of_core_trivial A hA hp2 (fun N hN hodd => hO' N hN
      (fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h))) hZ ?_ hP hP'
    intro C hC hAC Q Q' hQ hQ'
    have hcard : Nat.card C < n := by
      rw [← hn, ← Subgroup.card_top (G := X)]
      exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hC)
    let AC : Sylow 2 C := A.subtype hAC
    have hAC' : (AC : Subgroup C) = (A : Subgroup X).subgroupOf C := Sylow.coe_subtype _ _
    have hACab : IsMulCommutative (AC : Subgroup C) := by
      rw [hAC']
      exact ⟨⟨fun a b => Subtype.ext (Subtype.ext
        (mul_comm_of_isMulCommutative hA a.2 b.2))⟩⟩
    have := ih _ hcard C rfl AC hACab hp2 (P := Q) (P' := Q') (by rw [hAC']; exact hQ)
      (by rw [hAC']; exact hQ')
    rwa [hAC'] at this
  · have hZ2 : IsPGroup 2 (Subgroup.center X) := isPGroup_two_center hO'
    let Abar : Sylow 2 (X ⧸ Subgroup.center X) :=
      A.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center X))
    have hAbar : (Abar : Subgroup (X ⧸ Subgroup.center X)) =
        (A : Subgroup X).map (QuotientGroup.mk' (Subgroup.center X)) :=
      Sylow.coe_mapSurjective _ _
    have hcard : Nat.card (X ⧸ Subgroup.center X) < n := by
      rw [← hn, Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)]
      have h1 : 1 < Nat.card (Subgroup.center X) := (Subgroup.one_lt_card_iff_ne_bot _).mpr hZ
      have h0 : 0 < Nat.card (X ⧸ Subgroup.center X) := Nat.card_pos
      nlinarith
    refine nconj_of_quotient_center le_rfl hZ2 A (fun Q Q' hQ hQ' => ?_) hP hP'
    have hAab : IsMulCommutative (Abar : Subgroup (X ⧸ Subgroup.center X)) := by
      rw [hAbar]; exact CFSG.Goldschmidt.isMulCommutative_map hA _
    have := ih _ hcard _ rfl Abar hAab hp2 (P := Q) (P' := Q') (by rw [hAbar]; exact hQ)
      (by rw [hAbar]; exact hQ')
    rwa [hAbar] at this

theorem exists_conj_of_isMaxInvIn {X : Type} [Group X] [Finite X] {Y A : Subgroup X}
    (hAY : A ≤ Y) (hA : IsMulCommutative A) (hAsyl : fusionIsSylowIn 2 A Y) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {P P' : Subgroup X} (hP : IsMaxInvIn Y A p P)
    (hP' : IsMaxInvIn Y A p P') :
    ∃ y ∈ Y ⊓ Subgroup.normalizer (A : Set X), P' = conjSub y P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_sylow_of_fusionIsSylowIn hAsyl
  have hSY : (S : Subgroup Y) = A.subgroupOf Y := by
    rw [← hS]
    exact (Subgroup.comap_map_eq_self_of_injective Y.subtype_injective _).symm
  have hSab : IsMulCommutative (S : Subgroup Y) := by
    rw [hSY]
    exact ⟨⟨fun a b => Subtype.ext (Subtype.ext (mul_comm_of_isMulCommutative hA a.2 b.2))⟩⟩
  obtain ⟨y, hy, hyP⟩ := nconj_of_isMaxInv _ Y rfl S hSab hp2
    (P := P.subgroupOf Y) (P' := P'.subgroupOf Y) (by rw [hSY]; exact isMaxInv_subgroupOf hAY hP)
    (by rw [hSY]; exact isMaxInv_subgroupOf hAY hP')
  rw [hSY] at hy
  refine ⟨y, Subgroup.mem_inf.mpr ⟨y.2, mem_normalizer_of_subgroupOf hAY hy⟩, ?_⟩
  calc P' = (P'.subgroupOf Y).map Y.subtype := (Subgroup.map_subgroupOf_eq_of_le hP'.prop.1).symm
    _ = (conjSub y (P.subgroupOf Y)).map Y.subtype := by rw [hyP]
    _ = conjSub (y : X) ((P.subgroupOf Y).map Y.subtype) := map_subtype_conjSub Y y _
    _ = conjSub (y : X) P := by rw [Subgroup.map_subgroupOf_eq_of_le hP.prop.1]

end CFSG.Goldschmidt.G310
