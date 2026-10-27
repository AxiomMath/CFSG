module

public import CFSG.LieType.Universal.Spin.Forms
public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

section Lines

variable [Finite K] [FiniteDimensional K V]

@[expose] def linesIn (S : Set V) : Set (Submodule K V) :=
  {L | finrank K L = 1 ∧ ∀ x ∈ L, x ≠ 0 → x ∈ S}

omit [Finite K] in
theorem span_singleton_eq_of_mem {L : Submodule K V} (hL : finrank K L = 1) {x : V}
    (hx : x ∈ L) (hx0 : x ≠ 0) : Submodule.span K {x} = L := by
  apply Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem x L).2 hx)
  rw [finrank_span_singleton hx0, hL]

theorem card_line_ne_zero {L : Submodule K V} (hL : finrank K L = 1) :
    Nat.card {x : V // x ∈ L ∧ x ≠ 0} = Nat.card K - 1 := by
  have : Finite V := Module.finite_of_finite K
  have hcard : Nat.card L = Nat.card K := by
    rw [Module.natCard_eq_pow_finrank (K := K), hL, pow_one]
  have h1 : Nat.card {x : V // x ∈ L ∧ x ≠ 0} + 1 = Nat.card L := by
    classical
    let _ := Fintype.ofFinite V
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype,
      Fintype.card_subtype]
    rw [show (Finset.univ.filter fun x : V => x ∈ L ∧ x ≠ 0) =
      (Finset.univ.filter fun x : V => x ∈ L).erase 0 by
        ext x; simp [and_comm]]
    rw [Finset.card_erase_add_one (by simp)]
  have hK : 1 ≤ Nat.card K := Nat.one_le_iff_ne_zero.2 (Nat.card_pos (α := K)).ne'
  omega

theorem card_vectors_eq_mul_card_lines {S : Set V} (hS0 : (0 : V) ∉ S)
    (hSc : ∀ (c : K) (x : V), c ≠ 0 → x ∈ S → c • x ∈ S) :
    Nat.card S = (Nat.card K - 1) * Nat.card (linesIn (K := K) S) := by
  classical
  have : Finite V := Module.finite_of_finite K
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite (Submodule K V)
  let φ : S → linesIn (K := K) S := fun x => ⟨Submodule.span K {(x : V)}, by
    have hx0 : (x : V) ≠ 0 := fun h => hS0 (h ▸ x.2)
    refine ⟨finrank_span_singleton hx0, fun y hy hy0 => ?_⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    have hc : c ≠ 0 := by rintro rfl; exact hy0 (zero_smul K _)
    exact hSc c x hc x.2⟩
  have hmem : ∀ (L : linesIn (K := K) S) (x : S), φ x = L → (x : V) ∈ (L : Submodule K V) := by
    intro L x hx
    rw [← hx]
    exact Submodule.mem_span_singleton_self _
  have hfib : ∀ L : linesIn (K := K) S,
      Nat.card {x : S // φ x = L} = Nat.card K - 1 := by
    intro L
    rw [← card_line_ne_zero L.2.1]
    refine Nat.card_congr ⟨fun x => ⟨x.1, hmem L x.1 x.2, fun h => hS0 (h ▸ x.1.2)⟩,
      fun y => ⟨⟨y.1, L.2.2 y.1 y.2.1 y.2.2⟩, ?_⟩, fun x => rfl, fun y => rfl⟩
    exact Subtype.ext (span_singleton_eq_of_mem L.2.1 y.2.1 y.2.2)
  have hsig := Nat.card_congr (Equiv.sigmaFiberEquiv φ)
  rw [Nat.card_sigma] at hsig
  rw [← hsig, Finset.sum_congr rfl fun L _ => hfib L, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, Nat.card_eq_fintype_card (α := linesIn (K := K) S), mul_comm]

@[expose] def singularLinesIn (Q : QuadraticForm K V) (X : Submodule K V) : Set (Submodule K V) :=
  {L | L ≤ X ∧ finrank K L = 1 ∧ ∀ x ∈ L, Q x = 0}

omit [Finite K] [FiniteDimensional K V] in
theorem singularLinesIn_eq_linesIn (Q : QuadraticForm K V) (X : Submodule K V) :
    singularLinesIn Q X = linesIn (K := K) {v | v ∈ X ∧ v ≠ 0 ∧ Q v = 0} := by
  ext L
  constructor
  · rintro ⟨hLX, hL, hQ⟩
    exact ⟨hL, fun x hx hx0 => ⟨hLX hx, hx0, hQ x hx⟩⟩
  · rintro ⟨hL, h⟩
    refine ⟨fun x hx => ?_, hL, fun x hx => ?_⟩
    · by_cases hx0 : x = 0
      · rw [hx0]; exact X.zero_mem
      · exact (h x hx hx0).1
    · by_cases hx0 : x = 0
      · rw [hx0, map_zero]
      · exact (h x hx hx0).2.2

theorem card_singular_vectors (Q : QuadraticForm K V) (X : Submodule K V) :
    Nat.card {v : V | v ∈ X ∧ v ≠ 0 ∧ Q v = 0} =
      (Nat.card K - 1) * Nat.card (singularLinesIn Q X) := by
  rw [singularLinesIn_eq_linesIn]
  refine card_vectors_eq_mul_card_lines (fun h => h.2.1 rfl) fun c x hc hx => ?_
  exact ⟨X.smul_mem c hx.1, smul_ne_zero hc hx.2.1, by rw [map_smul_eq_sq, hx.2.2, mul_zero]⟩

end Lines

section Hyperbolic

variable {Q : QuadraticForm K V} (P : HypPair Q)

theorem hyp_polar_f {a b : K} {w : V} (hw : w ∈ P.perp) :
    polar Q (a • P.e + b • P.f + w) P.f = a := by
  have hwf : polar Q w P.f = 0 := by rw [polar_comm]; exact (HypPair.mem_perp.1 hw).2
  simp only [polar_add_left, polar_smul_left_eq, P.polar_ef, P.polar_ff, hwf]
  ring

theorem hyp_polar_e {a b : K} {w : V} (hw : w ∈ P.perp) :
    polar Q P.e (a • P.e + b • P.f + w) = b := by
  have hwe : polar Q P.e w = 0 := (HypPair.mem_perp.1 hw).1
  simp only [polar_add_right, polar_smul_right_eq, P.polar_ee, P.polar_ef, hwe]
  ring

theorem hyp_Q {a b : K} {w : V} (hw : w ∈ P.perp) :
    Q (a • P.e + b • P.f + w) = a * b + Q w := by
  have hwe : polar Q P.e w = 0 := (HypPair.mem_perp.1 hw).1
  have hwf : polar Q P.f w = 0 := (HypPair.mem_perp.1 hw).2
  rw [QuadraticMap.map_add Q, QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, P.Q_e,
    P.Q_f]
  simp only [polar_add_left, polar_smul_left_eq, polar_smul_right_eq, P.polar_ef, hwe, hwf]
  ring

theorem hyp_proj {a b : K} {w : V} (hw : w ∈ P.perp) :
    P.proj (a • P.e + b • P.f + w) = w := by
  have h := hyp_polar_e P (a := a) (b := b) hw
  rw [polar_comm] at h
  rw [HypPair.proj, hyp_polar_f P hw, h]
  abel

theorem hyp_decomp (v : V) :
    v = polar Q v P.f • P.e + polar Q P.e v • P.f + P.proj v := by
  have h := P.eq_add_proj v
  rwa [polar_comm Q v P.e] at h

theorem eq_zero_of_hyp {a b : K} {w : V} (hw : w ∈ P.perp)
    (h : a • P.e + b • P.f + w = 0) : a = 0 ∧ b = 0 ∧ w = 0 := by
  have ha := hyp_polar_f P (a := a) (b := b) hw
  have hb := hyp_polar_e P (a := a) (b := b) hw
  have hp := hyp_proj P (a := a) (b := b) hw
  rw [h, polar_zero_left] at ha
  rw [h, polar_zero_right] at hb
  rw [h] at hp
  refine ⟨ha.symm, hb.symm, ?_⟩
  rw [← hp, HypPair.proj]
  simp

theorem hyp_Q_e {a : K} {w : V} (hw : w ∈ P.perp) : Q (a • P.e + w) = Q w := by
  have h := hyp_Q P (a := a) (b := 0) hw
  rwa [zero_smul, add_zero, mul_zero, zero_add] at h

theorem hyp_polar_e_e {a : K} {w : V} (hw : w ∈ P.perp) : polar Q P.e (a • P.e + w) = 0 := by
  have h := hyp_polar_e P (a := a) (b := 0) hw
  rwa [zero_smul, add_zero] at h

theorem hyp_polar_f_e {a : K} {w : V} (hw : w ∈ P.perp) : polar Q (a • P.e + w) P.f = a := by
  have h := hyp_polar_f P (a := a) (b := 0) hw
  rwa [zero_smul, add_zero] at h

theorem hyp_proj_e {a : K} {w : V} (hw : w ∈ P.perp) : P.proj (a • P.e + w) = w := by
  have h := hyp_proj P (a := a) (b := 0) hw
  rwa [zero_smul, add_zero] at h

section Count

variable [Finite K] [FiniteDimensional K V]

omit [Finite K] [FiniteDimensional K V] in
theorem card_hyp_orth_vectors :
    Nat.card {v : V | v ≠ 0 ∧ Q v = 0 ∧ polar Q P.e v = 0 ∧ v ∉ K ∙ P.e} =
      Nat.card K * Nat.card {v : V | v ∈ P.perp ∧ v ≠ 0 ∧ Q v = 0} := by
  rw [← Nat.card_prod]
  have hdec : ∀ v : V, polar Q P.e v = 0 → polar Q v P.f • P.e + P.proj v = v := fun v hv => by
    have h := hyp_decomp P v
    rw [hv, zero_smul, add_zero] at h
    exact h.symm
  have hfwd : ∀ (a : K) (w : V), w ∈ P.perp → w ≠ 0 → Q w = 0 →
      a • P.e + w ≠ 0 ∧ Q (a • P.e + w) = 0 ∧ polar Q P.e (a • P.e + w) = 0 ∧
        a • P.e + w ∉ K ∙ P.e := by
    intro a w hw hw0 hQw
    refine ⟨fun h => hw0 ?_, by rw [hyp_Q_e P hw, hQw], hyp_polar_e_e P hw, fun h => hw0 ?_⟩
    · exact (eq_zero_of_hyp P (a := a) (b := 0) hw (by rw [zero_smul, add_zero]; exact h)).2.2
    · obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h
      refine (eq_zero_of_hyp P (a := a - c) (b := 0) hw ?_).2.2
      rw [zero_smul, add_zero, sub_smul, hc]
      abel
  have hbwd : ∀ v : V, v ≠ 0 → Q v = 0 → polar Q P.e v = 0 → v ∉ K ∙ P.e →
      P.proj v ∈ P.perp ∧ P.proj v ≠ 0 ∧ Q (P.proj v) = 0 := by
    intro v _ hQv hev hvK
    refine ⟨P.proj_mem_perp v, fun h => hvK ?_, ?_⟩
    · rw [← hdec v hev, h, add_zero]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · have h := hyp_Q_e P (a := polar Q v P.f) (P.proj_mem_perp v)
      rw [hdec v hev, hQv] at h
      exact h.symm
  symm
  exact Nat.card_congr
    { toFun := fun x => ⟨x.1 • P.e + (x.2 : V), hfwd x.1 x.2 x.2.2.1 x.2.2.2.1 x.2.2.2.2⟩
      invFun := fun v => (polar Q (v : V) P.f,
        ⟨P.proj v, hbwd v v.2.1 v.2.2.1 v.2.2.2.1 v.2.2.2.2⟩)
      left_inv := fun x => Prod.ext (hyp_polar_f_e P x.2.2.1) (Subtype.ext (hyp_proj_e P x.2.2.1))
      right_inv := fun v => Subtype.ext (hdec v v.2.2.2.1) }

theorem card_hyp_nonorth_vectors :
    Nat.card {v : V | Q v = 0 ∧ polar Q P.e v ≠ 0} =
      (Nat.card K - 1) * Nat.card K ^ finrank K P.perp := by
  have hW : Nat.card P.perp = Nat.card K ^ finrank K P.perp := Module.natCard_eq_pow_finrank
  have hK : Nat.card Kˣ = Nat.card K - 1 := by
    have := Nat.card_eq_card_units_add_one K
    omega
  rw [← hW, ← hK, ← Nat.card_prod]
  have hfwd : ∀ (b : Kˣ) (w : V), w ∈ P.perp →
      Q ((-Q w / b) • P.e + (b : K) • P.f + w) = 0 ∧
        polar Q P.e ((-Q w / b) • P.e + (b : K) • P.f + w) ≠ 0 := by
    intro b w hw
    rw [hyp_Q P hw, hyp_polar_e P hw, div_mul_cancel₀ _ b.ne_zero, neg_add_cancel]
    exact ⟨rfl, b.ne_zero⟩
  have hbwd : ∀ v : V, Q v = 0 → polar Q P.e v ≠ 0 →
      (-Q (P.proj v) / polar Q P.e v) • P.e + polar Q P.e v • P.f + P.proj v = v := by
    intro v hQv hb
    have hd := hyp_decomp P v
    have hQ0 : polar Q v P.f * polar Q P.e v + Q (P.proj v) = 0 := by
      rw [← hyp_Q P (P.proj_mem_perp v), ← hd, hQv]
    have ha : -Q (P.proj v) / polar Q P.e v = polar Q v P.f := by
      rw [div_eq_iff hb]
      linear_combination -hQ0
    rw [ha]
    exact hd.symm
  symm
  exact Nat.card_congr
    { toFun := fun x => ⟨(-Q (x.2 : V) / x.1) • P.e + (x.1 : K) • P.f + x.2,
        hfwd x.1 x.2 x.2.2⟩
      invFun := fun v => (Units.mk0 (polar Q P.e v) v.2.2, ⟨P.proj v, P.proj_mem_perp v⟩)
      left_inv := fun x => Prod.ext (Units.ext (hyp_polar_e P x.2.2))
        (Subtype.ext (hyp_proj P x.2.2))
      right_inv := fun v => Subtype.ext (hbwd v v.2.1 v.2.2) }

theorem orthogonal_geometry_hyperbolic_point_count :
    Nat.card (singularLinesIn Q ⊤) =
        1 + Nat.card K * Nat.card (singularLinesIn Q P.perp) + Nat.card K ^ finrank K P.perp ∧
      Nat.card {L : Submodule K V | L ∈ singularLinesIn Q ⊤ ∧ L ≠ K ∙ P.e ∧
          ∀ x ∈ L, polar Q P.e x = 0} = Nat.card K * Nat.card (singularLinesIn Q P.perp) ∧
      Nat.card {L : Submodule K V | L ∈ singularLinesIn Q ⊤ ∧ ∃ x ∈ L, polar Q P.e x ≠ 0} =
        Nat.card K ^ finrank K P.perp ∧
      (1 ≤ finrank K P.perp → Nat.card (singularLinesIn Q ⊤) ≡ 1 [MOD Nat.card K]) := by
  have : Finite V := Module.finite_of_finite K
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hq1 : 0 < Nat.card K - 1 := by omega
  set A : Set (Submodule K V) := {L | L ∈ singularLinesIn Q ⊤ ∧ L ≠ K ∙ P.e ∧
    ∀ x ∈ L, polar Q P.e x = 0} with hAdef
  set B : Set (Submodule K V) := {L | L ∈ singularLinesIn Q ⊤ ∧ ∃ x ∈ L, polar Q P.e x ≠ 0}
    with hBdef
  have he1 : finrank K (K ∙ P.e) = 1 := finrank_span_singleton P.e_ne_zero
  have hscal : ∀ {L : Submodule K V}, finrank K L = 1 → ∀ {x y : V}, x ∈ L → x ≠ 0 → y ∈ L →
      ∃ c : K, y = c • x := fun hL x y hx hx0 hy => by
    rw [← span_singleton_eq_of_mem hL hx hx0] at hy
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hy
    exact ⟨c, hc.symm⟩
  have hA : A = linesIn (K := K) {v : V | v ≠ 0 ∧ Q v = 0 ∧ polar Q P.e v = 0 ∧ v ∉ K ∙ P.e} := by
    ext L
    constructor
    · rintro ⟨⟨-, hL, hQ⟩, hne, horth⟩
      refine ⟨hL, fun x hx hx0 => ⟨hx0, hQ x hx, horth x hx, fun hxe => hne ?_⟩⟩
      rw [← span_singleton_eq_of_mem hL hx hx0, span_singleton_eq_of_mem he1 hxe hx0]
    · rintro ⟨hL, h⟩
      refine ⟨⟨le_top, hL, fun x hx => ?_⟩, fun hLe => ?_, fun x hx => ?_⟩
      · by_cases hx0 : x = 0
        · rw [hx0, map_zero]
        · exact (h x hx hx0).2.1
      · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := L)
          (fun hb => by rw [hb, finrank_bot] at hL; omega)
        exact (h x hx hx0).2.2.2 (hLe ▸ hx)
      · by_cases hx0 : x = 0
        · rw [hx0, polar_zero_right]
        · exact (h x hx hx0).2.2.1
  have hB : B = linesIn (K := K) {v : V | Q v = 0 ∧ polar Q P.e v ≠ 0} := by
    ext L
    constructor
    · rintro ⟨⟨-, hL, hQ⟩, x₀, hx₀, hx₀e⟩
      refine ⟨hL, fun x hx hx0 => ⟨hQ x hx, fun hxe => hx₀e ?_⟩⟩
      obtain ⟨c, rfl⟩ := hscal hL hx hx0 hx₀
      rw [polar_smul_right_eq, hxe, mul_zero]
    · rintro ⟨hL, h⟩
      refine ⟨⟨le_top, hL, fun x hx => ?_⟩, ?_⟩
      · by_cases hx0 : x = 0
        · rw [hx0, map_zero]
        · exact (h x hx hx0).1
      · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := L)
          (fun hb => by rw [hb, finrank_bot] at hL; omega)
        exact ⟨x, hx, (h x hx hx0).2⟩
  have hcardA : Nat.card A = Nat.card K * Nat.card (singularLinesIn Q P.perp) := by
    have h1 := card_vectors_eq_mul_card_lines (K := K)
      (S := {v : V | v ≠ 0 ∧ Q v = 0 ∧ polar Q P.e v = 0 ∧ v ∉ K ∙ P.e}) (fun h => h.1 rfl)
      (fun c x hc hx => ⟨smul_ne_zero hc hx.1, by rw [map_smul_eq_sq, hx.2.1, mul_zero],
        by rw [polar_smul_right_eq, hx.2.2.1, mul_zero], fun h => hx.2.2.2 (by
          rw [← inv_smul_smul₀ hc x]; exact Submodule.smul_mem _ _ h)⟩)
    rw [card_hyp_orth_vectors, card_singular_vectors, ← hA] at h1
    apply Nat.eq_of_mul_eq_mul_left hq1
    rw [← h1]
    ring
  have hcardB : Nat.card B = Nat.card K ^ finrank K P.perp := by
    have h1 := card_vectors_eq_mul_card_lines (K := K)
      (S := {v : V | Q v = 0 ∧ polar Q P.e v ≠ 0}) (fun h => h.2 (polar_zero_right Q _))
      (fun c x hc hx => ⟨by rw [map_smul_eq_sq, hx.1, mul_zero],
        by rw [polar_smul_right_eq]; exact mul_ne_zero hc hx.2⟩)
    rw [card_hyp_nonorth_vectors, ← hB] at h1
    exact (Nat.eq_of_mul_eq_mul_left hq1 h1).symm
  have hKe : K ∙ P.e ∈ singularLinesIn Q ⊤ := ⟨le_top, he1, fun x hx => by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [map_smul_eq_sq, P.Q_e, mul_zero]⟩
  have hpart : singularLinesIn Q ⊤ = {K ∙ P.e} ∪ (A ∪ B) := by
    ext L
    constructor
    · intro hL
      by_cases horth : ∀ x ∈ L, polar Q P.e x = 0
      · by_cases hLe : L = K ∙ P.e
        · exact Or.inl hLe
        · exact Or.inr (Or.inl ⟨hL, hLe, horth⟩)
      · push Not at horth
        exact Or.inr (Or.inr ⟨hL, horth⟩)
    · rintro (hL | hL | hL)
      · rw [Set.mem_singleton_iff.1 hL]
        exact hKe
      · exact hL.1
      · exact hL.1
  have hdisj1 : Disjoint ({K ∙ P.e} : Set (Submodule K V)) (A ∪ B) := by
    rw [Set.disjoint_singleton_left]
    rintro (hA' | ⟨-, x, hx, hxe⟩)
    · exact hA'.2.1 rfl
    · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
      exact hxe (by rw [polar_smul_right_eq, P.polar_ee, mul_zero])
  have hdisj2 : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro L ⟨-, -, horth⟩ ⟨-, x, hx, hxe⟩
    exact hxe (horth x hx)
  have htotal : Nat.card (singularLinesIn Q ⊤) =
      1 + Nat.card K * Nat.card (singularLinesIn Q P.perp) + Nat.card K ^ finrank K P.perp := by
    rw [Nat.card_coe_set_eq, hpart, Set.ncard_union_eq hdisj1, Set.ncard_singleton,
      Set.ncard_union_eq hdisj2, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hcardA,
      hcardB, add_assoc]
  refine ⟨htotal, hcardA, hcardB, fun hd => ?_⟩
  have hpow : Nat.card K ^ finrank K P.perp =
      Nat.card K * Nat.card K ^ (finrank K P.perp - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [htotal, hpow, add_assoc, ← mul_add]
  exact Nat.add_mul_mod_self_left 1 (Nat.card K) _

end Count

end Hyperbolic

section Split

open CFSG.LieType.Universal.Spin

variable (K) [Finite K]

omit [Finite K] in
theorem card_dotProduct_zero (r : ℕ) :
    Nat.card {y : Fin r → K // ∑ i, (0 : Fin r → K) i * y i = 0} = Nat.card K ^ r := by
  rw [show Nat.card K ^ r = Nat.card (Fin r → K) by rw [Nat.card_fun, Nat.card_fin]]
  exact Nat.card_congr (Equiv.subtypeUnivEquiv fun y => by simp)

omit [Finite K] in
theorem card_dotProduct_ne_zero {r : ℕ} {x : Fin r → K} (hx : x ≠ 0) :
    Nat.card {y : Fin r → K // ∑ i, x i * y i = 0} = Nat.card K ^ (r - 1) := by
  let f : (Fin r → K) →ₗ[K] K :=
    { toFun := fun y => ∑ i, x i * y i
      map_add' := fun a b => by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c a => by simp [Finset.mul_sum, mul_left_comm] }
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
  have hsurj : Function.Surjective f := fun t => ⟨Pi.single i (t / x i), by
    change ∑ j, x j * (Pi.single i (t / x i) : Fin r → K) j = t
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp), Pi.single_eq_same,
      mul_div_cancel₀ _ (show x i ≠ 0 from hi)]⟩
  have hrange : finrank K (LinearMap.range f) = 1 := by
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_self]
  have hker : finrank K (LinearMap.ker f) = r - 1 := by
    have := LinearMap.finrank_range_add_finrank_ker f
    rw [hrange, Module.finrank_fin_fun] at this
    omega
  rw [← hker, ← Module.natCard_eq_pow_finrank]
  rfl

theorem card_quadPlus_eq_zero (r : ℕ) :
    Nat.card {v : Fin r ⊕ Fin r → K // quadPlus r K v = 0} =
      Nat.card K ^ r + (Nat.card K ^ r - 1) * Nat.card K ^ (r - 1) := by
  classical
  let _ := Fintype.ofFinite K
  let e : {v : Fin r ⊕ Fin r → K // quadPlus r K v = 0} ≃
      Σ x : Fin r → K, {y : Fin r → K // ∑ i, x i * y i = 0} :=
    { toFun := fun v => ⟨fun i => (v : Fin r ⊕ Fin r → K) (.inl i),
        fun i => (v : Fin r ⊕ Fin r → K) (.inr i), by rw [← quadPlus_apply]; exact v.2⟩
      invFun := fun p => ⟨Sum.elim p.1 p.2, by rw [quadPlus_apply]; exact p.2.2⟩
      left_inv := fun v => Subtype.ext (funext fun s => by cases s <;> rfl)
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_sigma, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ 0),
    card_dotProduct_zero,
    Finset.sum_congr rfl fun x hx => card_dotProduct_ne_zero K (Finset.ne_of_mem_erase hx),
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ,
    smul_eq_mul, Fintype.card_fun, Fintype.card_fin, ← Nat.card_eq_fintype_card]

theorem orthogonal_geometry_split_point_count (r : ℕ) :
    (Nat.card K - 1) * Nat.card (singularLinesIn (quadPlus r K) ⊤) =
        (Nat.card K ^ r - 1) * (Nat.card K ^ (r - 1) + 1) ∧
      (2 ≤ r → Nat.card (singularLinesIn (quadPlus r K) ⊤) ≡ 1 [MOD Nat.card K]) := by
  classical
  let _ := Fintype.ofFinite K
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hN : Nat.card {v : Fin r ⊕ Fin r → K |
      v ∈ (⊤ : Submodule K (Fin r ⊕ Fin r → K)) ∧ v ≠ 0 ∧ quadPlus r K v = 0} + 1 =
      Nat.card {v : Fin r ⊕ Fin r → K // quadPlus r K v = 0} := by
    have hset : {v : Fin r ⊕ Fin r → K |
        v ∈ (⊤ : Submodule K (Fin r ⊕ Fin r → K)) ∧ v ≠ 0 ∧ quadPlus r K v = 0} =
        {v | quadPlus r K v = 0} \ {0} := by
      ext v
      exact ⟨fun h => ⟨h.2.2, h.2.1⟩, fun h => ⟨Submodule.mem_top, h.2, h.1⟩⟩
    rw [hset, Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_add_one
      (show (0 : Fin r ⊕ Fin r → K) ∈ {v | quadPlus r K v = 0} from map_zero _)]
    exact (Nat.card_coe_set_eq _).symm
  have hpos : 1 ≤ Nat.card K ^ r := Nat.one_le_pow _ _ (by omega)
  have hmain : (Nat.card K - 1) * Nat.card (singularLinesIn (quadPlus r K) ⊤) =
      (Nat.card K ^ r - 1) * (Nat.card K ^ (r - 1) + 1) := by
    rw [← card_singular_vectors]
    rw [card_quadPlus_eq_zero] at hN
    obtain ⟨a, ha⟩ : ∃ a, a = Nat.card K ^ r - 1 := ⟨_, rfl⟩
    rw [← ha] at hN ⊢
    have h1 : Nat.card K ^ r = a + 1 := by omega
    rw [h1] at hN
    linarith
  refine ⟨hmain, fun hr2 => ?_⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  have h := congrArg (Nat.cast : ℕ → ZMod (Nat.card K)) hmain
  have hq0 : ((Nat.card K : ℕ) : ZMod (Nat.card K)) = 0 := ZMod.natCast_self _
  push_cast [Nat.cast_sub (by omega : 1 ≤ Nat.card K), Nat.cast_sub hpos] at h
  rw [hq0, zero_pow (by omega), zero_pow (by omega)] at h
  simp only [zero_sub, neg_mul, one_mul, zero_add, mul_one, neg_inj] at h
  rw [h, Nat.cast_one]

end Split

end CFSG.LocalAnalysis.ComponentInitial
