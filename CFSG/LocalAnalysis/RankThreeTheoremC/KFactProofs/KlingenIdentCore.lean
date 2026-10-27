module

public import CFSG.LocalAnalysis.AGLEmbedding.ConstrainedSLAux
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3CharInv

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.AGLEmbedding CFSG.Open.StatedAPI Matrix

variable {Y : Type*} [Group Y] {p : ℕ} [Fact p.Prime]

theorem eq_bot_or_eq_top_of_statedSL_stable (W : Subgroup (Multiplicative (Fin 2 → ZMod p)))
    (hW : ∀ a ∈ StatedSL 2 (ZMod p), ∀ w ∈ W,
      Multiplicative.ofAdd ((a : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ Multiplicative.toAdd w) ∈
        W) :
    W = ⊥ ∨ W = ⊤ := by
  by_cases h : W = ⊥
  · exact Or.inl h
  right
  obtain ⟨⟨w, hwW⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h
  have hw0 : Multiplicative.toAdd w ≠ 0 := fun h0 =>
    hw1 (Subtype.ext (by simpa using congrArg Multiplicative.ofAdd h0))
  rw [eq_top_iff]
  intro v _
  by_cases hv0 : Multiplicative.toAdd v = 0
  · have hv : v = 1 := by simpa using congrArg Multiplicative.ofAdd hv0
    rw [hv]
    exact W.one_mem
  obtain ⟨A, hA⟩ := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.exists_sl2_mulVec hw0 hv0
  have hAmem : Matrix.SpecialLinearGroup.toGL A ∈ StatedSL 2 (ZMod p) :=
    mem_statedSL_of_det (by simp)
  have h1 := hW _ hAmem w hwW
  have h2 : ((Matrix.SpecialLinearGroup.toGL A : GL (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)) = (A : Matrix (Fin 2) (Fin 2) (ZMod p)) := rfl
  rw [h2, hA] at h1
  simpa using h1

theorem le_or_inf_le_center_of_statedSL {E L N : Subgroup Y} [N.Normal]
    (hEZ : Nat.card (Subgroup.center E) = p) (hEnc : ∃ a b : E, a * b ≠ b * a)
    (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p))
    (hSL : StatedSL 2 (ZMod p) ≤
      (L.subgroupOf (Subgroup.normalizer (E : Set Y))).map (centerQuotientAction E e)) :
    E ≤ N ∨ E ⊓ N ≤ (Subgroup.center E).map E.subtype := by
  set W : Subgroup (Multiplicative (Fin 2 → ZMod p)) :=
    ((N.subgroupOf E).map (QuotientGroup.mk' (Subgroup.center E))).map e.toMonoidHom with hWdef
  have hstable : ∀ a ∈ StatedSL 2 (ZMod p), ∀ w ∈ W,
      Multiplicative.ofAdd ((a : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ Multiplicative.toAdd w) ∈
        W := by
    intro a ha w hw
    obtain ⟨g, -, rfl⟩ := hSL ha
    obtain ⟨_, ⟨u, hu, rfl⟩, rfl⟩ := hw
    have hgE : (g : Y) * (u : Y) * (g : Y)⁻¹ ∈ E := by
      have := (Subgroup.mem_normalizer_iff.mp g.2 (u : Y)).mp u.2
      exact this
    set v : E := ⟨(g : Y) * (u : Y) * (g : Y)⁻¹, hgE⟩
    have hvN : v ∈ N.subgroupOf E := by
      rw [Subgroup.mem_subgroupOf]
      exact ‹N.Normal›.conj_mem _ (Subgroup.mem_subgroupOf.mp hu) _
    have hmul := centerQuotientAction_mulVec E e g (u := u) (v := v) rfl
    refine ⟨QuotientGroup.mk' (Subgroup.center E) v, ⟨v, hvN, rfl⟩, ?_⟩
    show e (v : E ⧸ Subgroup.center E) = Multiplicative.ofAdd
      ((centerQuotientAction E e g : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ
        Multiplicative.toAdd (e (u : E ⧸ Subgroup.center E)))
    rw [hmul]
    rfl
  rcases eq_bot_or_eq_top_of_statedSL_stable W hstable with hbot | htop
  ·
    right
    rintro x ⟨hxE, hxN⟩
    have hmem : e (QuotientGroup.mk' (Subgroup.center E) (⟨x, hxE⟩ : E)) ∈ W :=
      ⟨_, ⟨⟨x, hxE⟩, Subgroup.mem_subgroupOf.mpr hxN, rfl⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot, map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hmem
    exact ⟨⟨x, hxE⟩, hmem, rfl⟩
  ·
    left
    have hsurj : ∀ x : E, ∃ u : E, u ∈ N.subgroupOf E ∧ u⁻¹ * x ∈ Subgroup.center E := by
      intro x
      have hx : e (QuotientGroup.mk' (Subgroup.center E) x) ∈ W := by rw [htop]; trivial
      obtain ⟨_, ⟨u, hu, rfl⟩, hux⟩ := hx
      refine ⟨u, hu, ?_⟩
      have := e.injective hux
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at this
      exact this
    have hnc : ∃ u₁ u₂ : E, u₁ ∈ N.subgroupOf E ∧ u₂ ∈ N.subgroupOf E ∧ u₁ * u₂ ≠ u₂ * u₁ := by
      by_contra hall
      push Not at hall
      obtain ⟨a, b, hab⟩ := hEnc
      obtain ⟨u, hu, hua⟩ := hsurj a
      obtain ⟨u', hu', hub⟩ := hsurj b
      apply hab
      set z := u⁻¹ * a with hzdef
      set z' := u'⁻¹ * b with hz'def
      have ha : a = u * z := by rw [hzdef]; group
      have hb : b = u' * z' := by rw [hz'def]; group
      have hz : ∀ g : E, g * z = z * g := Subgroup.mem_center_iff.mp hua
      have hz' : ∀ g : E, g * z' = z' * g := Subgroup.mem_center_iff.mp hub
      have e1 : u * z * (u' * z') = u * u' * (z * z') := by
        rw [show u * z * (u' * z') = u * (z * u') * z' by group, ← hz u']
        group
      have e2 : u' * z' * (u * z) = u' * u * (z' * z) := by
        rw [show u' * z' * (u * z) = u' * (z' * u) * z by group, ← hz' u]
        group
      rw [ha, hb, e1, e2, hall u u' hu hu', hz z']
    obtain ⟨u₁, u₂, h₁, h₂, h12⟩ := hnc
    set c : E := u₁ * u₂ * u₁⁻¹ * u₂⁻¹ with hc
    have hc1 : c ≠ 1 := by
      intro h1
      apply h12
      have h1' : u₁ * u₂ * u₁⁻¹ * u₂⁻¹ = 1 := h1
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1'
      exact h1'
    have hcN : c ∈ N.subgroupOf E :=
      mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
    have hcZ : c ∈ Subgroup.center E := by
      rw [← QuotientGroup.eq_one_iff, ← map_eq_one_iff _ e.injective]
      have h1 : ((c : E) : E ⧸ Subgroup.center E) = (u₁ : E ⧸ Subgroup.center E) *
          (u₂ : E ⧸ Subgroup.center E) * (u₁ : E ⧸ Subgroup.center E)⁻¹ *
          (u₂ : E ⧸ Subgroup.center E)⁻¹ := by
        rw [hc]
        rfl
      rw [h1, map_mul, map_mul, map_mul, map_inv, map_inv]
      apply Multiplicative.toAdd.injective
      simp only [toAdd_mul, toAdd_inv, toAdd_one]
      abel
    have hZN : Subgroup.center E ≤ N.subgroupOf E := by
      have hp : p.Prime := Fact.out
      haveI : Finite (Subgroup.center E) :=
        Nat.finite_of_card_ne_zero (by rw [hEZ]; exact hp.ne_zero)
      have hZc : Subgroup.zpowers (⟨c, hcZ⟩ : Subgroup.center E) = ⊤ := by
        have hcard : Nat.card (Subgroup.center E) = p := hEZ
        have hne : (⟨c, hcZ⟩ : Subgroup.center E) ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
        have : Nat.card (Subgroup.zpowers (⟨c, hcZ⟩ : Subgroup.center E)) ∣ p :=
          hcard ▸ Subgroup.card_subgroup_dvd_card _
        rcases (Nat.dvd_prime hp).mp this with h1 | hp'
        · exfalso
          apply hne
          rw [Nat.card_zpowers, orderOf_eq_one_iff] at h1
          exact h1
        · exact Subgroup.eq_top_of_card_eq _ (hp'.trans hcard.symm)
      intro z hz
      have hzt : (⟨z, hz⟩ : Subgroup.center E) ∈ Subgroup.zpowers ⟨c, hcZ⟩ := by
        rw [hZc]; trivial
      obtain ⟨k, hk⟩ := hzt
      have : z = c ^ k := by
        have := congrArg Subtype.val hk
        simpa using this.symm
      rw [this]
      exact zpow_mem hcN k
    intro x hxE
    obtain ⟨u, hu, hux⟩ := hsurj ⟨x, hxE⟩
    have h := mul_mem hu (hZN hux)
    rw [mul_inv_cancel_left] at h
    exact Subgroup.mem_subgroupOf.mp h

theorem pow_two_dvd_index_of_card_le {E N : Subgroup Y} (hEcard : Nat.card E = p ^ 3)
    (hN : Nat.card (N.subgroupOf E) ≤ p) : p ^ 2 ∣ (N.subgroupOf E).index := by
  have hp : p.Prime := Fact.out
  have hmul := Subgroup.card_mul_index (N.subgroupOf E)
  rw [hEcard] at hmul
  have hdvd : Nat.card (N.subgroupOf E) ∣ p ^ 3 := ⟨_, hmul.symm⟩
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  rw [hk'] at hmul hN
  have hk1 : k ≤ 1 := by
    by_contra hk1
    have h1 : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.pos (by omega)
    have h2 : p < p ^ 2 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  have hidx : (N.subgroupOf E).index = p ^ (3 - k) := by
    have hpk : 0 < p ^ k := pow_pos hp.pos k
    have : p ^ k * (N.subgroupOf E).index = p ^ k * p ^ (3 - k) := by
      rw [hmul, ← pow_add]
      congr 1
      omega
    exact Nat.eq_of_mul_eq_mul_left hpk this
  rw [hidx]
  exact pow_dvd_pow p (by omega)

theorem le_of_klingen [Finite Y] {K : Subgroup Y} [K.Normal]
    (hC : IsCyclic (Subgroup.centralizer (K : Set Y)))
    (hidx : ¬ p ^ 2 ∣ (K ⊔ Subgroup.centralizer (K : Set Y)).index)
    {E L : Subgroup Y} (hEcard : Nat.card E = p ^ 3) (hEexp : ∀ x ∈ E, x ^ p = 1)
    (hEZ : Nat.card (Subgroup.center E) = p)
    (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p))
    (hSL : StatedSL 2 (ZMod p) ≤
      (L.subgroupOf (Subgroup.normalizer (E : Set Y))).map (centerQuotientAction E e)) :
    E ≤ K := by
  have hp : p.Prime := Fact.out
  have hEnc : ∃ a b : E, a * b ≠ b * a := by
    by_contra hall
    push Not at hall
    have htop : Subgroup.center E = ⊤ := by
      rw [eq_top_iff]
      intro z _
      exact Subgroup.mem_center_iff.mpr fun g => hall g z
    rw [htop, Subgroup.card_top, hEcard] at hEZ
    have h1 : p ^ 1 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    rw [pow_one] at h1
    omega
  have hcard_inf : ∀ N : Subgroup Y, E ⊓ N ≤ (Subgroup.center E).map E.subtype →
      Nat.card (N.subgroupOf E) ≤ p := by
    intro N hN
    rw [← hEZ]
    have hle : N.subgroupOf E ≤ Subgroup.center E := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := hN ⟨x.2, Subgroup.mem_subgroupOf.mp hx⟩
      have : y = x := Subtype.ext hyx
      rw [← this]
      exact hy
    exact Nat.card_mono (Set.toFinite _) hle
  set C : Subgroup Y := Subgroup.centralizer (K : Set Y) with hCdef
  have hKC : E ≤ K ⊔ C := by
    rcases le_or_inf_le_center_of_statedSL (N := K ⊔ C) hEZ hEnc e hSL with h | h
    · exact h
    · exact absurd ((pow_two_dvd_index_of_card_le hEcard (hcard_inf _ h)).trans
        (Subgroup.relIndex_dvd_index_of_normal _ _)) hidx
  rcases le_or_inf_le_center_of_statedSL (N := K) hEZ hEnc e hSL with h | h
  · exact h
  · exfalso
    set π : Y →* Y ⧸ K := QuotientGroup.mk' K
    have hEC : E.map π ≤ C.map π := by
      calc E.map π ≤ (K ⊔ C).map π := Subgroup.map_mono hKC
        _ = K.map π ⊔ C.map π := Subgroup.map_sup _ _ _
        _ = C.map π := by
          rw [show K.map π = ⊥ from (Subgroup.map_eq_bot_iff _).mpr (by
            rw [QuotientGroup.ker_mk']), bot_sup_eq]
    haveI : IsCyclic C := hC
    haveI hcycC : IsCyclic (C.map π) :=
      isCyclic_of_surjective (π.subgroupMap C) (π.subgroupMap_surjective C)
    haveI hcycE : IsCyclic (E.map π) :=
      isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hEC).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hEC).surjective
    have hle : Nat.card (E.map π) ≤ p := by
      obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := E.map π)
      rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
      apply Nat.le_of_dvd hp.pos
      apply orderOf_dvd_of_pow_eq_one
      obtain ⟨_, x, hx, rfl⟩ := g
      apply Subtype.ext
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← map_pow, hEexp x hx, map_one]
    have hker : (π.subgroupMap E).ker = K.subgroupOf E := by
      ext x
      simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro hx
        have h1 : ((π.subgroupMap E x : E.map π) : Y ⧸ K) = 1 := by rw [hx]; rfl
        change QuotientGroup.mk' K (x : Y) = 1 at h1
        rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      · intro hx
        apply Subtype.ext
        change QuotientGroup.mk' K (x : Y) = 1
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hx
    have hidx2 : (K.subgroupOf E).index = Nat.card (E.map π) := by
      rw [← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr (π.subgroupMap_surjective E),
        Subgroup.card_top]
    have h2 := pow_two_dvd_index_of_card_le hEcard (hcard_inf _ h)
    rw [hidx2] at h2
    have h3 := Nat.le_of_dvd Nat.card_pos h2
    have h4 : p < p ^ 2 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
