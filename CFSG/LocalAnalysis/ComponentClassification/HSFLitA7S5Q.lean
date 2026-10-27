module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7S5O2

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

theorem dCols_ddCols' : ∀ i, comp dCols (comp dCols dCols) i = bas i := by decide

theorem xCols_sq : ∀ i, comp xCols xCols i = bas i := by decide

theorem d₂_cols' : ∀ i, comp (comp (comp dCols xCols) (comp dCols dCols)) xCols i =
    comp dCols dCols i := by decide

theorem dd_cube : ∀ i, comp (comp dCols dCols) (comp (comp dCols dCols) (comp dCols dCols)) i =
    bas i := by decide

theorem dd_sq : ∀ i, comp (comp dCols dCols) (comp dCols dCols) i = dCols i := by decide

namespace A7Base

variable {X : Type} [Group X] [Finite X] {S : A7Base X}

namespace Sec5Hyp

variable {T₁ : Subgroup X} (H : S.Sec5Hyp T₁)
include H

theorem card_quot5 (I : S.Inst) :
    Nat.card (normalizer (I.E : Set X) ⧸
      (centralizer (I.E : Set X)).subgroupOf (normalizer (I.E : Set X))) = 24 := by
  obtain ⟨e⟩ := H.automizer I
  rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem centralizer_le_Pre5 (I : S.Inst) :
    (centralizer (I.E : Set X)).subgroupOf (normalizer (I.E : Set X)) ≤ H.Pre5 I := by
  intro n hn
  show H.blockHom5 I n ∈ transl
  rw [H.blockHom5_eq_one_of_mem I hn]
  exact one_mem _

theorem Q_props (I : S.Inst) {R : Subgroup X} (hRN : R ≤ normalizer (I.E : Set X))
    (hR : Nat.card R = 128) (hRC : R ⊓ centralizer (I.E : Set X) = I.E) :
    Nat.card (R ⊓ oddTwoCoreIn (normalizer (I.E : Set X)) : Subgroup X) = 64 ∧
      (R ⊓ oddTwoCoreIn (normalizer (I.E : Set X))) ⊓ centralizer (I.E : Set X) = I.E ∧
      ∀ n ∈ oddTwoCoreIn (normalizer (I.E : Set X)),
        ∃ q ∈ R ⊓ oddTwoCoreIn (normalizer (I.E : Set X)),
        q⁻¹ * n ∈ centralizer (I.E : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (I.E : Set X) with hN
  set P := H.Pre5 I with hP
  have hPn := H.Pre5_normal I
  set Q := R ⊓ oddTwoCoreIn N with hQ
  have hQeq : Q = R ⊓ P.map N.subtype := by rw [hQ, H.oddTwoCoreIn_eq I]
  have hcardS : Nat.card (R.subgroupOf N) = 2 ^ (Nat.card N).factorization 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hRN).toEquiv, hR, H.factorization_normalizer I]
    rfl
  set Syl : Sylow 2 N := Sylow.ofCard _ hcardS with hSyl
  obtain ⟨R', hR'⟩ := CFSG.Glauberman.sylow_inf_normal Syl (N := P)
  have hR'card : Nat.card R' = 64 := by
    rw [Sylow.card_eq_multiplicity, H.factorization_Pre5 I]
    rfl
  have hQcard : Nat.card Q = 64 := by
    rw [← hR'card]
    have e1 : Nat.card R' = Nat.card (((Syl : Subgroup N) ⊓ P).subgroupOf P) := by rw [← hR']
    rw [e1, Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv, hQeq]
    have e2 : ((Syl : Subgroup N) ⊓ P).map N.subtype = R ⊓ P.map N.subtype := by
      rw [Sylow.coe_ofCard, Subgroup.map_inf _ _ _ (subtype_injective _),
        subgroupOf_map_subtype, inf_of_le_left hRN]
    rw [← e2, card_map_of_injective (subtype_injective _)]
  have hER : I.E ≤ R := by
    intro e he
    have : e ∈ R ⊓ centralizer (I.E : Set X) := by rw [hRC]; exact he
    exact this.1
  have hQC : Q ⊓ centralizer (I.E : Set X) = I.E := by
    apply le_antisymm
    · intro x hx
      have : x ∈ R ⊓ centralizer (I.E : Set X) := ⟨hx.1.1, hx.2⟩
      rwa [hRC] at this
    · refine le_inf (le_inf hER ?_) I.E_le_centralizer
      intro e he
      rw [H.oddTwoCoreIn_eq I]
      exact ⟨⟨e, I.centralizer_le_normalizer (I.E_le_centralizer he)⟩,
        H.centralizer_le_Pre5 I (I.E_le_centralizer he), rfl⟩
  refine ⟨hQcard, hQC, ?_⟩
  intro n hn
  set Cn := (centralizer (I.E : Set X)).subgroupOf N with hCn
  have hQN : Q ≤ N := inf_le_left.trans hRN
  set ρ : Q.subgroupOf N →* N ⧸ Cn := (QuotientGroup.mk' Cn).comp (Q.subgroupOf N).subtype
    with hρ
  have hker : Nat.card ρ.ker = 16 := by
    have : ρ.ker.map ((Q.subgroupOf N).subtype) =
        (Q ⊓ centralizer (I.E : Set X)).subgroupOf N := by
      ext x
      simp only [mem_map, MonoidHom.mem_ker, hρ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, Subgroup.coe_subtype, mem_subgroupOf, mem_inf]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, hy⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨x, h1⟩, h2, rfl⟩
    have h1 := congrArg (fun K : Subgroup N => Nat.card K) this
    simp only [card_map_of_injective (subtype_injective _)] at h1
    rw [h1, Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans hQN)).toEquiv, hQC, Inst.E,
      S.card_E I.yi_mem I.yi_sq I.yi_not_mem_B]
  have hrange : Nat.card ρ.range = 4 := by
    have h1 := Subgroup.card_ker_mul_card_range ρ
    rw [hker, Nat.card_congr (subgroupOfEquivOfLe hQN).toEquiv, hQcard] at h1
    omega
  have hPimg : ρ.range ≤ P.map (QuotientGroup.mk' Cn) := by
    rintro _ ⟨q, rfl⟩
    refine ⟨q, ?_, rfl⟩
    have hq : (q : X) ∈ P.map N.subtype := by
      have hq2 : ((q : N) : X) ∈ oddTwoCoreIn N := (mem_subgroupOf.mp q.2).2
      rw [H.oddTwoCoreIn_eq I] at hq2
      exact hq2
    obtain ⟨p, hp, hpq⟩ := hq
    have : (q : N) = p := Subtype.ext hpq.symm
    rw [this]
    exact hp
  have hPcard : Nat.card (P.map (QuotientGroup.mk' Cn)) = 4 := by
    have h1 := (P.map (QuotientGroup.mk' Cn)).card_mul_index
    have hk : (QuotientGroup.mk' Cn).ker ≤ P := by
      rw [QuotientGroup.ker_mk']; exact H.centralizer_le_Pre5 I
    have hidx : (P.map (QuotientGroup.mk' Cn)).index = 6 := by
      have := index_map_eq (H := P) (f := QuotientGroup.mk' Cn) (QuotientGroup.mk'_surjective _) hk
      rw [this, H.index_Pre5 I]
    rw [hidx, H.card_quot5 I] at h1
    omega
  have heq : ρ.range = P.map (QuotientGroup.mk' Cn) :=
    Subgroup.eq_of_le_of_card_ge hPimg (by rw [hrange, hPcard])
  rw [H.oddTwoCoreIn_eq I] at hn
  obtain ⟨n', hn', rfl⟩ := hn
  have : QuotientGroup.mk' Cn n' ∈ ρ.range := heq ▸ ⟨n', hn', rfl⟩
  obtain ⟨q, hq⟩ := this
  refine ⟨(q : N), mem_subgroupOf.mp q.2, ?_⟩
  have h2 : QuotientGroup.mk' Cn (q : N) = QuotientGroup.mk' Cn n' := hq
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h2
  exact h2

theorem exists_transl_Q (I : S.Inst) {R : Subgroup X} (hRN : R ≤ normalizer (I.E : Set X))
    (hR : Nat.card R = 128) (hRC : R ⊓ centralizer (I.E : Set X) = I.E) (a b : Fin 2) :
    ∃ q ∈ R ⊓ oddTwoCoreIn (normalizer (I.E : Set X)), I.Mat q (transCols a b) := by
  obtain ⟨τ, hτ⟩ := H.exists_transl I a b
  have hτO : τ ∈ oddTwoCoreIn (normalizer (I.E : Set X)) := by
    rw [H.oddTwoCoreIn_eq I]
    exact ⟨⟨τ, hτ.1⟩, H.mem_Pre5_of_mat I hτ, rfl⟩
  obtain ⟨-, -, hreal⟩ := H.Q_props I hRN hR hRC
  obtain ⟨q, hq, hqτ⟩ := hreal τ hτO
  refine ⟨q, hq, ?_⟩
  have := hτ.mul_central (inv_mem hqτ)
  rwa [mul_inv_rev, inv_inv, mul_inv_cancel_left] at this

theorem exists_d_normalizer5 (I : S.Inst) {R : Subgroup X}
    (hRN : R ≤ normalizer (I.E : Set X)) (hR : Nat.card R = 128)
    (hRC : R ⊓ centralizer (I.E : Set X) = I.E) :
    ∃ d, I.Mat d dCols ∧
      d ∈ normalizer ((R ⊓ oddTwoCoreIn (normalizer (I.E : Set X)) : Subgroup X) : Set X) := by
  set N := normalizer (I.E : Set X) with hN
  set P := oddTwoCoreIn N with hP
  set Q := R ⊓ P with hQ
  obtain ⟨hQcard, -, hreal⟩ := H.Q_props I hRN hR hRC
  obtain ⟨d₀, hd₀, hd₀c⟩ := I.exists_d_cols
  have hd₀M : I.Mat d₀ dCols := ⟨hd₀.1, hd₀c⟩
  set Q' := Q.map (MulAut.conj d₀).toMonoidHom with hQ'
  have hQP : Q ≤ P := inf_le_right
  have hQ'P : Q' ≤ P := by
    rintro _ ⟨q, hq, rfl⟩
    exact Inst.conj_mem_oddTwoCoreIn' hd₀.1 (hQP hq)
  have hfac : (Nat.card P).factorization 2 = 6 := by
    rw [hP, H.oddTwoCoreIn_eq I, card_map_of_injective (subtype_injective _),
      H.factorization_Pre5 I]
  have hQ'card : Nat.card Q' = 64 := by
    rw [hQ', card_map_of_injective (MulAut.conj d₀).injective, hQcard]
  obtain ⟨h, hhP, hh⟩ := exists_conj_eq_of_card_eq hQ'P hQP
    (by rw [hQ'card, hfac]; rfl) (by rw [hQcard, hfac]; rfl)
  obtain ⟨q, hq, hqh⟩ := hreal h hhP
  refine ⟨q⁻¹ * h * d₀, hd₀M.central_mul hqh, ?_⟩
  refine mem_normalizer_of_conj_mem fun p hp => ?_
  have h1 : h * (d₀ * p * d₀⁻¹) * h⁻¹ ∈ Q := by
    rw [← hh]
    exact ⟨_, ⟨p, hp, rfl⟩, rfl⟩
  have h2 : q⁻¹ * (h * (d₀ * p * d₀⁻¹) * h⁻¹) * q⁻¹⁻¹ ∈ Q :=
    mul_mem (mul_mem (inv_mem hq) h1) (by rw [inv_inv]; exact hq)
  have e : q⁻¹ * h * d₀ * p * (q⁻¹ * h * d₀)⁻¹ =
      q⁻¹ * (h * (d₀ * p * d₀⁻¹) * h⁻¹) * q⁻¹⁻¹ := by group
  rw [e]
  exact h2

omit H in
theorem Mat_pow_three_mul_add_one {I : S.Inst} {n : X} {c : Fin 4 → V4} (h : I.Mat n c)
    (hc : ∀ i, comp c (comp c c) i = bas i) (k : ℕ) : I.Mat (n ^ (3 * k + 1)) c := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have h3 : I.Mat (n ^ 3) bas := by
      have := h.mul (h.mul h)
      rwa [show comp c (comp c c) = bas from funext hc, ← pow_three] at this
    have := ih.mul h3
    rw [show comp c bas = c from funext fun i => lin_bas c i, ← pow_add] at this
    rwa [show 3 * (k + 1) + 1 = 3 * k + 1 + 3 by ring]

theorem exists_d₅ (I : S.Inst) {R : Subgroup X} (hRN : R ≤ normalizer (I.E : Set X))
    (hR : Nat.card R = 128) (hRC : R ⊓ centralizer (I.E : Set X) = I.E) {u : X} (huR : u ∈ R)
    (huM : I.Mat u xCols) (hu2 : u * u = 1) :
    ∃ d, I.Mat d dCols ∧
      d ∈ normalizer ((R ⊓ oddTwoCoreIn (normalizer (I.E : Set X)) : Subgroup X) : Set X) ∧
      (∃ a : ℕ, d ^ (3 ^ a) = 1) ∧ u * d * u⁻¹ = d⁻¹ := by
  obtain ⟨d₀, hd₀, hd₀Q⟩ := H.exists_d_normalizer5 I hRN hR hRC
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have huQ : u ∈
      normalizer ((R ⊓ oddTwoCoreIn (normalizer (I.E : Set X)) : Subgroup X) : Set X) := by
    refine mem_normalizer_of_conj_mem fun q hq => mem_inf.mpr ⟨?_, ?_⟩
    · exact mul_mem (mul_mem huR (mem_inf.mp hq).1) (inv_mem huR)
    · exact Inst.conj_mem_oddTwoCoreIn' (hRN huR) (mem_inf.mp hq).2
  obtain ⟨d₂, hd₂⟩ : ∃ d₂, d₂ = d₀ * u * d₀⁻¹ * u⁻¹ := ⟨_, rfl⟩
  have hd₂M : I.Mat d₂ (comp dCols dCols) := by
    have := ((hd₀.mul huM).mul (hd₀.inv dCols_ddCols')).mul (huM.inv xCols_sq)
    rwa [show comp (comp (comp dCols xCols) (comp dCols dCols)) xCols = comp dCols dCols from
      funext d₂_cols', ← hd₂] at this
  have hd₂inv : u * d₂ * u⁻¹ = d₂⁻¹ := by
    rw [hd₂, huinv]
    calc u * (d₀ * u * d₀⁻¹ * u) * u = u * d₀ * u * d₀⁻¹ * (u * u) := by group
      _ = u * d₀ * u * d₀⁻¹ := by rw [hu2, mul_one]
      _ = (d₀ * u * d₀⁻¹ * u)⁻¹ := by simp only [mul_inv_rev, inv_inv, huinv, mul_assoc]
  have hd₂Q : d₂ ∈
      normalizer ((R ⊓ oddTwoCoreIn (normalizer (I.E : Set X)) : Subgroup X) : Set X) := by
    rw [hd₂]
    exact mul_mem (mul_mem (mul_mem hd₀Q huQ) (inv_mem hd₀Q)) (inv_mem huQ)
  obtain ⟨a, r, hr3, hr⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos d₂).ne' 3 (by norm_num)
  have hpow : d₂ ^ (3 ^ a * r) = 1 := by rw [← hr]; exact pow_orderOf_eq_one d₂
  obtain ⟨m, hm2, hm⟩ : ∃ m : ℕ, m % 3 = 2 ∧ d₂ ^ (3 ^ a * m) = 1 := by
    rcases (by omega : r % 3 = 1 ∨ r % 3 = 2) with h1 | h2
    · refine ⟨2 * r, by omega, ?_⟩
      rw [show 3 ^ a * (2 * r) = 3 ^ a * r * 2 by ring, pow_mul, hpow, one_pow]
    · exact ⟨r, h2, hpow⟩
  refine ⟨d₂ ^ m, ?_, pow_mem hd₂Q m, ⟨a, ?_⟩, ?_⟩
  · have h1 := (Mat_pow_three_mul_add_one hd₂M dd_cube (m / 3)).mul hd₂M
    rwa [show comp (comp dCols dCols) (comp dCols dCols) = dCols from funext dd_sq, ← pow_succ,
      show 3 * (m / 3) + 1 + 1 = m by omega] at h1
  · rw [← pow_mul, mul_comm, hm]
  · rw [← conj_pow, hd₂inv, inv_pow]

end Sec5Hyp

end A7Base

end CFSG.ComponentClassification.HSFLit
