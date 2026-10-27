module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Reduction

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.SporadicBalance

section Inner

variable {p k : ℕ} {S : Type*} [Group S]

theorem isLocallyBalancedAbs_of_inner_eq_top (hcen : Subgroup.center S = ⊥)
    (hinn : innerAut S = ⊤)
    (h : ∀ E : Subgroup S, IsElemAbelian p E → Nat.card E = p ^ k →
      localDeltaIn p (⊤ : Subgroup S) E = ⊥) : IsLocallyBalancedAbs p k S := by
  have hinj : Function.Injective (MulAut.conj : S →* MulAut S) :=
    conj_injective_of_center_eq_bot hcen
  have hsurj : Function.Surjective (MulAut.conj : S →* MulAut S) := by
    intro σ
    have : σ ∈ innerAut S := hinn ▸ Subgroup.mem_top σ
    obtain ⟨g, hg⟩ := this
    exact ⟨g, hg⟩
  let φ : S ≃* MulAut S := MulEquiv.ofBijective (MulAut.conj : S →* MulAut S) ⟨hinj, hsurj⟩
  let ψ : MulAut S →* S := φ.symm.toMonoidHom
  have hψ : Function.Injective ψ := φ.symm.injective
  intro D hD hcard H hH hDH
  have hHtop : H = ⊤ := by
    rw [eq_top_iff, ← hinn]
    exact hH
  subst hHtop
  have hD' : IsElemAbelian p (D.map ψ) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
      obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
      apply Subtype.ext
      change ψ x * ψ y = ψ y * ψ x
      have := congrArg Subtype.val (hD.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      rw [← map_mul, ← map_mul]
      exact congrArg ψ this
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hD.2 x hx, map_one]
  have hcard' : Nat.card (D.map ψ) = p ^ k := by
    rw [Subgroup.card_map_of_injective hψ, hcard]
  have h0 := h (D.map ψ) hD' hcard'
  have hle := map_localDeltaIn_le p ψ hψ (⊤ : Subgroup (MulAut S)) D
  rw [Subgroup.map_top_of_surjective _ φ.symm.surjective, h0, le_bot_iff,
    Subgroup.map_eq_bot_iff_of_injective _ hψ] at hle
  exact hle

end Inner

section Gamma

variable {p : ℕ} {S : Type*} [Group S] [Finite S]

theorem ne_bot_of_one_le_pRank (hp : p.Prime) {Q : Subgroup S} (hQ : 1 ≤ CFSG.Open.pRank p Q) :
    Q ≠ ⊥ := by
  rintro rfl
  have : CFSG.Open.pRank p (⊥ : Subgroup S) ≤ 0 := by
    refine csSup_le' ?_
    rintro k ⟨E, hE, -, hEc⟩
    have hE1 : E = ⊥ := le_bot_iff.1 hE
    rw [hE1, Subgroup.card_bot] at hEc
    by_contra hk
    exact absurd hEc (ne_of_lt (Nat.one_lt_pow (by omega) hp.one_lt))
  omega

omit [Finite S] in
theorem conj_mem_oPrime_centralizer {y : S} (g d : S)
    (hy : y ∈ GLAPPrimeCoreOf p ((⊤ : Subgroup S) ⊓ Subgroup.centralizer ({d} : Set S))) :
    g * y * g⁻¹ ∈
      GLAPPrimeCoreOf p ((⊤ : Subgroup S) ⊓ Subgroup.centralizer ({g * d * g⁻¹} : Set S)) := by
  have hψ : Function.Injective (MulAut.conj g : S ≃* S).toMonoidHom :=
    (MulAut.conj g : S ≃* S).injective
  have hmap := map_glaPPrimeCoreOf_of_injective p (MulAut.conj g : S ≃* S).toMonoidHom hψ
    ((⊤ : Subgroup S) ⊓ Subgroup.centralizer ({d} : Set S))
  have hc := map_inf_centralizer_of_injective (MulAut.conj g : S ≃* S).toMonoidHom hψ ⊤ d
  rw [Subgroup.map_top_of_surjective _ (MulAut.conj g : S ≃* S).surjective] at hc
  have hs : (MulAut.conj g : S ≃* S).toMonoidHom d = g * d * g⁻¹ := by
    simp [MulAut.conj_apply]
  rw [hs] at hc
  rw [hc] at hmap
  have : (MulAut.conj g : S ≃* S).toMonoidHom y ∈
      (GLAPPrimeCoreOf p ((⊤ : Subgroup S) ⊓ Subgroup.centralizer ({d} : Set S))).map
        (MulAut.conj g : S ≃* S).toMonoidHom := ⟨y, hy, rfl⟩
  rw [hmap] at this
  simpa [MulAut.conj_apply] using this

theorem localDeltaIn_top_eq_bot_of_gamma (hp : p.Prime) (hcen : Subgroup.center S = ⊥)
    {D : Subgroup S} (hD : IsElemAbelian p D) (hgen : GLBCore p 1 D = ⊤)
    (hO : ∀ d : S, orderOf d = p →
      Nat.card (GLAPPrimeCoreOf p (Subgroup.centralizer ({d} : Set S))) ≤ 2) :
    localDeltaIn p (⊤ : Subgroup S) D = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  by_contra hy1
  have hyR : ∀ d ∈ D, d ≠ 1 →
      y ∈ GLAPPrimeCoreOf p ((⊤ : Subgroup S) ⊓ Subgroup.centralizer ({d} : Set S)) := by
    intro d hd hd1
    have := (Subgroup.mem_iInf.1 hy d)
    have := (Subgroup.mem_iInf.1 this hd)
    exact Subgroup.mem_iInf.1 this hd1
  have hfix : ∀ Q : Subgroup S, Q ≤ D → 1 ≤ CFSG.Open.pRank p Q → ∀ g ∈ Subgroup.normalizer (Q : Set S),
      g * y * g⁻¹ = y := by
    intro Q hQD hQ g hg
    obtain ⟨d, hd⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 (ne_bot_of_one_le_pRank hp hQ)
    obtain ⟨d, hdQ', hd1'⟩ : ∃ d : S, d ∈ Q ∧ d ≠ 1 :=
      ⟨d, d.2, fun h => hd (Subtype.ext h)⟩
    have hd'Q : g * d * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 hg d).1 hdQ'
    have hd'1 : g * d * g⁻¹ ≠ 1 := by
      intro h
      apply hd1'
      calc d = g⁻¹ * (g * d * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    have hyd' := hyR _ (hQD hd'Q) hd'1
    have hgy := conj_mem_oPrime_centralizer g d (hyR d (hQD hdQ') hd1')
    have hord : orderOf (g * d * g⁻¹) = p :=
      orderOf_eq_prime (by
        have := hD.2 _ (hQD hd'Q)
        exact this) hd'1
    have hcard : Nat.card (GLAPPrimeCoreOf p ((⊤ : Subgroup S) ⊓
        Subgroup.centralizer ({g * d * g⁻¹} : Set S))) ≤ 2 := by
      rw [top_inf_eq]
      exact hO _ hord
    have hy1' : (⟨y, hyd'⟩ : GLAPPrimeCoreOf p ((⊤ : Subgroup S) ⊓
        Subgroup.centralizer ({g * d * g⁻¹} : Set S))) ≠ 1 := fun h =>
      hy1 (congrArg Subtype.val h)
    have hz1' : (⟨g * y * g⁻¹, hgy⟩ : GLAPPrimeCoreOf p ((⊤ : Subgroup S) ⊓
        Subgroup.centralizer ({g * d * g⁻¹} : Set S))) ≠ 1 := by
      intro h
      apply hy1
      have h' : g * y * g⁻¹ = 1 := congrArg Subtype.val h
      calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
        _ = 1 := by rw [h']; group
    have := eq_of_ne_one_of_card_le_two hcard hz1' hy1'
    exact congrArg Subtype.val this
  have hle : GLBCore p 1 D ≤ Subgroup.centralizer ({y} : Set S) := by
    unfold GLBCore
    refine sSup_le ?_
    rintro N ⟨Q, hQD, hQ, rfl⟩ g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hfix Q hQD hQ g hg
    calc g * y = (g * y * g⁻¹) * g := by group
      _ = y * g := by rw [this]
  rw [hgen, top_le_iff] at hle
  have hyc : y ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro z
    have : z ∈ Subgroup.centralizer ({y} : Set S) := hle ▸ Subgroup.mem_top z
    exact Subgroup.mem_centralizer_singleton_iff.1 this
  rw [hcen, Subgroup.mem_bot] at hyc
  exact hy1 hyc

theorem isLocallyBalancedAbs_two_of_gamma (hp : p.Prime) (hcen : Subgroup.center S = ⊥)
    (hinn : innerAut S = ⊤) (hp3 : ¬ p ^ 3 ∣ Nat.card S)
    (hgen : ∀ T : Sylow p S, GLBCore p 1 (T : Subgroup S) = ⊤)
    (hO : ∀ d : S, orderOf d = p →
      Nat.card (GLAPPrimeCoreOf p (Subgroup.centralizer ({d} : Set S))) ≤ 2) :
    IsLocallyBalancedAbs p 2 S := by
  have : Fact p.Prime := ⟨hp⟩
  refine isLocallyBalancedAbs_of_inner_eq_top hcen hinn fun E hE hEc => ?_
  have hdvd : p ^ 2 ∣ Nat.card S := hEc ▸ Subgroup.card_subgroup_dvd_card E
  have hfac : (Nat.card S).factorization p = 2 := by
    have hpos : Nat.card S ≠ 0 := Nat.card_pos.ne'
    have h2 : 2 ≤ (Nat.card S).factorization p :=
      (hp.pow_dvd_iff_le_factorization hpos).mp hdvd
    have h3 : ¬ 3 ≤ (Nat.card S).factorization p :=
      fun h => hp3 ((hp.pow_dvd_iff_le_factorization hpos).mpr h)
    omega
  let T : Sylow p S := Sylow.ofCard E (by rw [hEc, hfac])
  exact localDeltaIn_top_eq_bot_of_gamma hp hcen hE (hgen T) hO

end Gamma

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
