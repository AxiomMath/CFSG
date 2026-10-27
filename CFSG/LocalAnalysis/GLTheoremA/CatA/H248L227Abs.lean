module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H248L227Rank
import CFSG.LocalAnalysis.GLTheoremA.CatA.H248L227Chief
import CFSG.LocalAnalysis.GLTheoremA.CatA.H248L227Lin
import CFSG.LocalAnalysis.GLTheoremA.CatA.H248L227Kl

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H248L227

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator

private theorem card_inf_ker_mul_card_map {X S : Type} [Group X] [Group S] (φ : X →* S)
    (Q : Subgroup X) : Nat.card (Q ⊓ φ.ker : Subgroup X) * Nat.card (Q.map φ) = Nat.card Q := by
  have h := Subgroup.card_ker_mul_card_range (φ.domRestrict Q)
  rw [MonoidHom.domRestrict_range, MonoidHom.ker_domRestrict] at h
  rw [← h, ← Subgroup.inf_subgroupOf_left]
  congr 1
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm

theorem not_four_le_pRank_map {X S : Type} [Group X] [Finite X] [Group S] [Finite S] {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hperf : commutator X = ⊤) (φ : X →* S)
    (hker : ∀ N : Subgroup X, N.Normal → N ≠ ⊤ → N ≤ φ.ker)
    (V : Subgroup X) [V.Normal] (hV : IsPGroup q V)
    (hVab : ∀ E : Subgroup X, E ≤ V → CFSG.Open.IsElemAbelian q E → Nat.card E ≤ q ^ 3)
    (hnc : ∃ g : X, ∃ v ∈ V, g * v ≠ v * g) (Q : Subgroup X) (hQ : IsPGroup q Q) :
    ¬ 4 ≤ CFSG.Open.pRank q (Q.map φ) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hq1 : 1 < q := hq.one_lt
  obtain ⟨U, hUn, hUV, hexp, hcomm, hmin, hne⟩ := exists_chief_factor hq hq2 hperf V hV hnc
  haveI := hUn
  set Z : Subgroup X := U ⊓ Subgroup.center X with hZdef
  have hZU : Z ≤ U := inf_le_left
  have hZc : Z ≤ Subgroup.center X := inf_le_right
  have hCker : quotKer U Z ≤ φ.ker := hker _ inferInstance hne
  have hcl : ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ Z := fun a ha b hb =>
    ⟨U.mul_mem (U.mul_mem (U.mul_mem ha hb) (U.inv_mem ha)) (U.inv_mem hb), hcomm a ha b hb⟩
  have hab : ∀ A : Subgroup X, A ≤ U → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      Nat.card A ≤ q ^ 3 := fun A hAU hAc =>
    hVab A (hAU.trans hUV) ⟨⟨⟨fun a b => Subtype.ext (hAc a a.2 b b.2)⟩⟩,
      fun x hx => hexp x (hAU hx)⟩
  have hZn : ∀ a ∈ U, ∀ z ∈ Z, a * z * a⁻¹ ∈ Z := fun a _ z hz =>
    (inferInstance : Z.Normal).conj_mem z hz a
  have hQU : ∀ t ∈ Q, ∀ a ∈ U, t * a * t⁻¹ ∈ U := fun t _ a ha => hUn.conj_mem a ha t
  have hQZ : ∀ t ∈ Q, ∀ z ∈ Z, t * z * t⁻¹ ∈ Z := fun t _ z hz =>
    (inferInstance : Z.Normal).conj_mem z hz t
  have hpow : ∀ a ∈ U, a ^ q ∈ Z := fun a ha => by rw [hexp a ha]; exact Z.one_mem
  have hrel := card_inf_ker_mul_card_map φ Q
  have hpos : 0 < Nat.card (Q ⊓ φ.ker : Subgroup X) := Nat.card_pos
  have hsmall : Nat.card Q ≤ q ^ 3 * Nat.card (Q ⊓ φ.ker : Subgroup X) →
      ¬ 4 ≤ CFSG.Open.pRank q (Q.map φ) := by
    intro hQc h4
    have hmap : Nat.card (Q.map φ) ≤ q ^ 3 := by
      rw [← hrel, mul_comm] at hQc
      exact Nat.le_of_mul_le_mul_right hQc hpos
    have h3 : CFSG.Open.pRank q (Q.map φ) ≤ 3 :=
      CFSG.SectionRank.pRank_le hq1 fun E hE _ => (Subgroup.card_le_of_le hE).trans hmap
    omega
  have hfix : ∀ C : Subgroup X, C ≤ Q → (∀ c ∈ C, ∀ a ∈ U, a⁻¹ * (c * a * c⁻¹) ∈ Z) →
      Nat.card C ≤ Nat.card (Q ⊓ φ.ker : Subgroup X) := fun C hCQ hCa =>
    Subgroup.card_le_of_le fun c hc => ⟨hCQ hc, hCker (mem_quotKer.2 (hCa c hc))⟩
  have hk : ∀ k : ℕ, Nat.card U ≤ q ^ k * Nat.card Z →
      Nat.card Q ≤ q ^ (k * (k - 1) / 2) * Nat.card (Q ⊓ φ.ker : Subgroup X) := by
    intro k hcard
    obtain ⟨C, hCQ, hCa, hC⟩ :=
      exists_index_le_of_elemAb hq Q U Z hQ hZU hZn hQU hQZ hcl hpow k hcard
    exact hC.trans (Nat.mul_le_mul_left _ (hfix C hCQ hCa))
  obtain ⟨a, ha⟩ := (hV.to_le hUV).exists_card_eq
  obtain ⟨b, hb⟩ := (hV.to_le (hZU.trans hUV)).exists_card_eq
  have hZcent : ∀ u ∈ U, u ∈ Z → ∀ v ∈ U, u * v = v * u := fun u _ hu v _ =>
    (Subgroup.mem_center_iff.1 (hZc hu) v).symm
  obtain ⟨hUle, hUeq⟩ := card_le_of_abelian_le hq U hexp
    (fun a ha b hb c _ => (Subgroup.mem_center_iff.1 (hcomm a ha b hb) c).symm) hab
  set ZU : Subgroup X := U ⊓ Subgroup.centralizer (U : Set X) with hZUdef
  have hZZU : Z ≤ ZU := fun z hz =>
    ⟨hZU hz, Subgroup.mem_centralizer_iff.2 fun v hv => (hZcent z (hZU hz) hz v hv).symm⟩
  by_cases hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a
  ·
    refine hsmall ?_
    have h := hk 3 ((hab U le_rfl hUab).trans (Nat.le_mul_of_pos_right _ Nat.card_pos))
    simpa using h
  ·
    have hZUn : ZU.Normal := Subgroup.normal_inf_normal U _
    have hZUeq : ZU = Z := by
      refine le_antisymm (fun u hu => ⟨hu.1, ?_⟩) hZZU
      rcases hmin ZU hZUn inf_le_left with h | h
      · exfalso
        refine hUab fun a ha b hb => ?_
        have hb' : b ∈ ZU := h ▸ hb
        exact Subgroup.mem_centralizer_iff.1 hb'.2 a ha
      · exact h hu
    rw [hZUeq] at hUle hUeq
    by_cases hU4 : Nat.card U = q ^ 4 * Nat.card Z
    ·
      have hcZ : Nat.card Z = q := hUeq hU4
      have hcU : Nat.card U = q ^ 5 := by rw [hU4, hcZ]; ring
      have hZiff : ∀ u ∈ U, u ∈ Z ↔ ∀ v ∈ U, u * v = v * u := by
        intro u hu
        refine ⟨hZcent u hu, fun h => ?_⟩
        rw [← hZUeq]
        exact ⟨hu, Subgroup.mem_centralizer_iff.2 fun v hv => (h v hv).symm⟩
      have h2 : ∀ A B : Subgroup X, B ≤ A → (∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ ∈ B) →
          (∀ t ∈ Q, ∀ a ∈ A, t * a * t⁻¹ ∈ A) → (∀ t ∈ Q, ∀ b ∈ B, t * b * t⁻¹ ∈ B) →
          (∀ a ∈ A, ∀ a' ∈ A, a * a' * a⁻¹ * a'⁻¹ ∈ B) → (∀ a ∈ A, a ^ q ∈ B) →
          Nat.card A ≤ q ^ 2 * Nat.card B →
          ∃ C : Subgroup X, C ≤ Q ∧ (∀ c ∈ C, ∀ a ∈ A, a⁻¹ * (c * a * c⁻¹) ∈ B) ∧
            Nat.card Q ≤ q * Nat.card C := by
        intro A B hBA hBn hTA hTB hcm hpw hcard
        obtain ⟨C, hCQ, hCa, hC⟩ := exists_index_le_of_elemAb hq Q A B hQ hBA hBn hTA hTB hcm hpw 2
          hcard
        exact ⟨C, hCQ, hCa, by simpa using hC⟩
      obtain ⟨hKl, hKleq⟩ := klingen_bound hq hq2 U Z hZU hexp hcl hcU hcZ hZiff hab Q hQ
        (fun t _ z hz => Subgroup.mem_center_iff.1 (hZc hz) t) h2
      have hQC : Nat.card (Q ⊓ quotKer U Z : Subgroup X) ≤ Nat.card (Q ⊓ φ.ker : Subgroup X) :=
        Subgroup.card_le_of_le (inf_le_inf_left Q hCker)
      intro h4
      obtain ⟨E, hEQ, hEa, hEc⟩ := CFSG.SectionRank.exists_pRank hq1 (Q.map φ)
      have hE4 : q ^ 4 ≤ Nat.card E := hEc ▸ Nat.pow_le_pow_right hq.pos h4
      have hmap : Nat.card (Q.map φ) ≤ q ^ 4 := by
        have h1 := hKl.trans (Nat.mul_le_mul_left (q ^ 4) hQC)
        rw [← hrel, mul_comm] at h1
        exact Nat.le_of_mul_le_mul_right h1 hpos
      have hEle : Nat.card E ≤ Nat.card (Q.map φ) := Subgroup.card_le_of_le hEQ
      have hEeq : E = Q.map φ := Subgroup.eq_of_le_of_card_ge hEQ (by omega)
      have hmap4 : Nat.card (Q.map φ) = q ^ 4 := by omega
      have hQeq : Nat.card Q = q ^ 4 * Nat.card (Q ⊓ quotKer U Z : Subgroup X) := by
        refine le_antisymm hKl ?_
        rw [← hrel, hmap4, mul_comm]
        exact Nat.mul_le_mul_right _ hQC
      obtain ⟨s, hs, t, ht, hst⟩ := hKleq hQeq
      have hinf : (Q ⊓ quotKer U Z : Subgroup X) = Q ⊓ φ.ker := by
        refine Subgroup.eq_of_le_of_card_ge (inf_le_inf_left Q hCker) ?_
        have h1 : Nat.card (Q ⊓ φ.ker : Subgroup X) * q ^ 4 =
            Nat.card (Q ⊓ quotKer U Z : Subgroup X) * q ^ 4 := by
          rw [← hmap4, hrel, hQeq, mul_comm, hmap4]
        exact (Nat.eq_of_mul_eq_mul_right (by positivity) h1).le
      have hcomm' : φ s * φ t = φ t * φ s := by
        have h1 := hEa.1.is_comm.comm
          ⟨φ s, hEeq ▸ Subgroup.mem_map_of_mem φ hs⟩ ⟨φ t, hEeq ▸ Subgroup.mem_map_of_mem φ ht⟩
        exact congrArg Subtype.val h1
      have hk1 : s * t * s⁻¹ * t⁻¹ ∈ (Q ⊓ φ.ker : Subgroup X) := by
        refine Subgroup.mem_inf.2
          ⟨Q.mul_mem (Q.mul_mem (Q.mul_mem hs ht) (Q.inv_mem hs)) (Q.inv_mem ht), ?_⟩
        rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm']
        group
      rw [← hinf] at hk1
      exact hst (Subgroup.mem_inf.1 hk1).2
    ·
      refine hsmall ?_
      have hlt : Nat.card U < q ^ 4 * Nat.card Z := lt_of_le_of_ne hUle hU4
      rw [ha, hb, ← pow_add] at hlt
      have hab' : a ≤ 3 + b := by
        have := (Nat.pow_lt_pow_iff_right hq1).1 hlt
        omega
      have h := hk 3 (by rw [ha, hb, ← pow_add]; exact Nat.pow_le_pow_right hq.pos hab')
      simpa using h

theorem eq_bot_of_four_le_pRank_map {X S : Type} [Group X] [Finite X] [Group S] [Finite S]
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hperf : commutator X = ⊤) (R W : Subgroup X)
    [R.Normal] (hW : W = ⁅R, (⊤ : Subgroup X)⁆) (hcore : CFSG.pPrimeCore q ↥W = ⊥)
    (hnc : NoCompIn W) (φ : X →* S) (hker : ∀ N : Subgroup X, N.Normal → N ≠ ⊤ → N ≤ φ.ker)
    (Q : Subgroup X) (hQ : IsPGroup q Q) (hQc : Nat.card Q = q ^ (Nat.card X).factorization q)
    (hr : CFSG.Open.pRank q (Q ⊓ W) ≤ 3) (hrk : 4 ≤ CFSG.Open.pRank q (Q.map φ)) : W = ⊥ := by
  have : Fact q.Prime := ⟨hq⟩
  haveI hWn : W.Normal := by rw [hW]; infer_instance
  set V : Subgroup X := (CFSG.pCore q ↥W).map W.subtype with hV
  haveI hVn : V.Normal := i227rk_normal_map W (CFSG.pCore q ↥W)
  have hVp : IsPGroup q V :=
    (CFSG.pCore_isPGroup (p := q) (G := W)).of_equiv
      ((CFSG.pCore q ↥W).equivMapOfInjective W.subtype W.subtype_injective)
  have hVQ : V ≤ Q := by
    have := hVp.le_sylow_of_normal (Sylow.ofCard Q hQc)
    simpa using this
  have hVW : V ≤ W := Subgroup.map_subtype_le _
  have hVab : ∀ E : Subgroup X, E ≤ V → CFSG.Open.IsElemAbelian q E → Nat.card E ≤ q ^ 3 := by
    intro E hEV hEa
    have hEp : IsPGroup q E := fun x => ⟨1, Subtype.ext (by simpa using hEa.2 x x.2)⟩
    obtain ⟨n, hn⟩ := hEp.exists_card_eq
    have hnle : n ≤ CFSG.Open.pRank q (Q ⊓ W) :=
      CFSG.SectionRank.le_pRank hq.one_lt (hEV.trans (le_inf hVQ hVW)) hEa hn
    rw [hn]
    exact Nat.pow_le_pow_right hq.pos (hnle.trans hr)
  by_cases hcent : ∀ k : X, ∀ v ∈ V, k * v = v * k
  · exact eq_bot_of_centralizes hq hperf R W hW hcore hnc hcent
  · push Not at hcent
    obtain ⟨g, v, hv, hgv⟩ := hcent
    exact (not_four_le_pRank_map hq hq2 hperf φ hker V hVp hVab ⟨g, v, hv, hgv⟩ Q hQ hrk).elim

end CFSG.LocalAnalysis.GLTheoremA.H248L227
