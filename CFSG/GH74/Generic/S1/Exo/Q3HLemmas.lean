module

public import CFSG.GH74.Generic.S1.Exo.Q3SL2
public import CFSG.GH74.Generic.S1.CompIdent
public import CFSG.GH74.KGroups.L3EpsOuterLin

public section

namespace CFSG.GH74.Generic.S1.Exo

open scoped MatrixGroups commutatorElement
open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.GLS CFSG.GH74.Filter.ClassicalOdd Subgroup

theorem sl23_exists_noncomm_conj : ∀ g : SL(2, ZMod 3), g ^ 2 ≠ 1 → g ^ 4 = 1 →
    ∃ k : SL(2, ZMod 3), g * (k * g * k⁻¹) ≠ (k * g * k⁻¹) * g := by
  decide

theorem sl23_noncomm_conj {X : Type} [Group X] {V : Subgroup X}
    (hV : HasSL2Model ↥V (fun r => r = 3)) {g : X} (hg : g ∈ V) (hg2 : g ^ 2 ≠ 1) (hg4 : g ^ 4 = 1) :
    ∃ k ∈ V, g * (k * g * k⁻¹) ≠ (k * g * k⁻¹) * g := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hV
  obtain ⟨e₀⟩ := sl2_equiv_zmod3 (F₀ := F) hF
  let φ : ↥V ≃* SL(2, ZMod 3) :=
    (e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm).trans e₀
  have h2 : (φ ⟨g, hg⟩) ^ 2 ≠ 1 := by
    intro h
    apply hg2
    have : (⟨g, hg⟩ : ↥V) ^ 2 = 1 := φ.injective (by rw [map_pow, h, map_one])
    simpa using congrArg Subtype.val this
  have h4 : (φ ⟨g, hg⟩) ^ 4 = 1 := by
    rw [← map_pow]
    have : (⟨g, hg⟩ : ↥V) ^ 4 = 1 := Subtype.ext (by simpa using hg4)
    rw [this, map_one]
  obtain ⟨k', hk'⟩ := sl23_exists_noncomm_conj _ h2 h4
  refine ⟨((φ.symm k' : ↥V) : X), (φ.symm k').2, fun hc => hk' ?_⟩
  apply φ.symm.injective
  rw [map_mul, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
  apply Subtype.ext
  simpa using hc


theorem q8Frattini_eq_one_iff : ∀ g : Q8, q8Frattini g = 1 ↔ (g = 1 ∨ g = QuaternionGroup.a 2) := by
  decide

theorem not_gen4_of_elemAb_eight {H : Type} [Group H] [Finite H] (N : Subgroup H) (ψ : Q8 →* H)
    (hcomm : ∀ q : Q8, ∀ n ∈ N, ψ q * n = n * ψ q)
    (hZ : ∀ q : Q8, ψ q ∈ N → q = 1 ∨ q = QuaternionGroup.a 2)
    (E : Subgroup (↥N ⧸ center ↥N)) (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hE2 : ∀ a ∈ E, a * a = 1) (h8 : 8 ≤ Nat.card E) : ¬ Gen4 H := by
  classical
  intro hG
  let π : ↥N →* ↥N ⧸ center ↥N := QuotientGroup.mk' (center ↥N)
  let Ê : Subgroup ↥N := E.comap π
  let α : Q8 × ↥Ê →* H :=
    ψ.noncommCoprod (N.subtype.comp Ê.subtype) (fun q n => hcomm q n n.1.2)
  have hα : ∀ q n, α (q, n) = ψ q * ((n : ↥N) : H) := fun q n => rfl
  let β2 : ↥Ê →* ↥E := (π.comp Ê.subtype).codRestrict E (fun n => n.2)
  have hβ2 : ∀ n : ↥Ê, ((β2 n : ↥E) : ↥N ⧸ center ↥N) = π (n : ↥N) := fun n => rfl
  let β : Q8 × ↥Ê →* V4 × ↥E :=
    (q8Frattini.comp (MonoidHom.fst Q8 ↥Ê)).prod (β2.comp (MonoidHom.snd Q8 ↥Ê))
  have hβ : ∀ q n, β (q, n) = (q8Frattini q, β2 n) := fun q n => rfl
  have hβs : Function.Surjective β := by
    rintro ⟨v, e⟩
    obtain ⟨q, rfl⟩ := q8Frattini_surjective v
    obtain ⟨n, hn⟩ := QuotientGroup.mk_surjective (e : ↥N ⧸ center ↥N)
    have hnÊ : n ∈ Ê := by
      show π n ∈ E
      have : π n = (e : ↥N ⧸ center ↥N) := hn
      rw [this]; exact e.2
    refine ⟨(q, ⟨n, hnÊ⟩), ?_⟩
    rw [hβ]
    refine Prod.ext rfl (Subtype.ext ?_)
    rw [hβ2]
    exact hn
  have hcert : RankCertified H 4 := by
    refine ⟨Q8 × ↥Ê, V4 × ↥E, inferInstance, inferInstance, inferInstance, α, β, hβs, ?_, ?_, ?_, ?_⟩
    · intro a b
      refine Prod.ext (mul_comm _ _) ?_
      exact Subtype.ext (hE _ a.2.2 _ b.2.2)
    · intro a
      rw [pow_two]
      refine Prod.ext ?_ ?_
      · exact (by decide : ∀ v : V4, v * v = 1) a.1
      · exact Subtype.ext (hE2 _ a.2.2)
    · rw [Nat.card_prod, card_V4]
      omega
    · intro k hk
      rcases k with ⟨q, n⟩
      have hk' : ψ q * ((n : ↥N) : H) = 1 := by rw [← hα]; exact hk
      have hn : ((n : ↥N) : H) = (ψ q)⁻¹ := eq_inv_of_mul_eq_one_right hk'
      have hψN : ψ q ∈ N := by
        have h1 : (ψ q) = (((n : ↥N)⁻¹ : ↥N) : H) := by
          rw [Subgroup.coe_inv, hn, inv_inv]
        rw [h1]; exact ((n : ↥N)⁻¹).2
      have hq := hZ q hψN
      have hnc : (n : ↥N) ∈ center ↥N := by
        rw [Subgroup.mem_center_iff]
        intro m
        apply Subtype.ext
        change (m : H) * (n : H) = (n : H) * (m : H)
        rw [hn]
        have := hcomm q m m.2
        calc (m : H) * (ψ q)⁻¹ = (ψ q)⁻¹ * (ψ q * m) * (ψ q)⁻¹ := by group
          _ = (ψ q)⁻¹ * (m * ψ q) * (ψ q)⁻¹ := by rw [this]
          _ = (ψ q)⁻¹ * m := by group
      rw [MonoidHom.mem_ker, hβ]
      refine Prod.ext ((q8Frattini_eq_one_iff q).2 hq) (Subtype.ext ?_)
      rw [hβ2]
      exact (QuotientGroup.eq_one_iff _).2 hnc
  exact hcert.not_gen4 le_rfl hG


theorem exists_commuting_involution_of_le {S : Type} [Group S] [Finite S] (Q : Sylow 2 S) {s : S}
    (hsQ : s ∈ (Q : Subgroup S)) (hs1 : s ≠ 1) (E : Subgroup S)
    (hEQ : E ≤ (Q : Subgroup S)) (hE2 : ∀ a ∈ E, a * a = 1) (h4 : 4 ≤ Nat.card E) :
    ∃ b : S, b ∈ (Q : Subgroup S) ∧ b * b = 1 ∧ b ≠ 1 ∧ b ≠ s ∧ b * s = s * b := by
  classical
  by_cases hcen : ∀ t ∈ (Q : Subgroup S), s * t = t * s
  · by_contra hno
    push Not at hno
    have hsub : (E : Set S) ⊆ {1, s} := by
      intro a ha
      by_contra hna
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hna
      exact hno a (hEQ ha) (hE2 a ha) hna.1 hna.2 (hcen a (hEQ ha)).symm
    have h1 : (E : Set S).ncard ≤ ({1, s} : Set S).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({1, s} : Set S).ncard ≤ 2 := by
      have := Set.ncard_insert_le (1 : S) ({s} : Set S)
      simpa using this
    have h3 : Nat.card E = (E : Set S).ncard := Nat.card_coe_set_eq (E : Set S)
    omega
  · push Not at hcen
    obtain ⟨t, htQ, hst⟩ := hcen
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hQP : IsPGroup 2 (Q : Subgroup S) := Q.isPGroup'
    have hnt : Nontrivial (Q : Subgroup S) := ⟨⟨⟨s, hsQ⟩, 1, fun h => hs1 (congrArg Subtype.val h)⟩⟩
    have hZ := hQP.center_nontrivial
    obtain ⟨k, hk, hkcard⟩ :=
      ((hQP.to_subgroup (Subgroup.center (Q : Subgroup S))).nontrivial_iff_card).mp hZ
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center (Q : Subgroup S)) 2
      (hkcard ▸ dvd_pow_self 2 hk.ne')
    set e : S := (((z : Subgroup.center (Q : Subgroup S)) : (Q : Subgroup S)) : S) with he
    have heQ : e ∈ (Q : Subgroup S) := ((z : (Q : Subgroup S))).2
    have heord : orderOf e = 2 := by
      have h1 : orderOf (z : (Q : Subgroup S)) = 2 :=
        (orderOf_injective (Subgroup.center (Q : Subgroup S)).subtype Subtype.val_injective z).trans hz
      exact (orderOf_injective (Q : Subgroup S).subtype Subtype.val_injective (z : (Q : Subgroup S))).trans h1
    have he1 : e ≠ 1 := by
      intro h; rw [h, orderOf_one] at heord; omega
    have he2 : e * e = 1 := by rw [← sq, ← heord, pow_orderOf_eq_one]
    have hcz := Subgroup.mem_center_iff.1 z.2
    refine ⟨e, heQ, he2, he1, ?_, ?_⟩
    · intro hes
      apply hst
      have h1 := congrArg Subtype.val (hcz ⟨t, htQ⟩)
      have h2 : t * e = e * t := h1
      rw [hes] at h2
      exact h2.symm
    · have h1 := congrArg Subtype.val (hcz ⟨s, hsQ⟩)
      have h2 : s * e = e * s := h1
      exact h2.symm

theorem exists_commuting_involution {S : Type} [Group S] [Finite S] {s : S} (hs : s * s = 1) (hs1 : s ≠ 1)
    (E : Subgroup S) (hE2 : ∀ a ∈ E, a * a = 1) (h4 : 4 ≤ Nat.card E) :
    ∃ b : S, b * b = 1 ∧ b ≠ 1 ∧ b ≠ s ∧ b * s = s * b := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf s = 2 := orderOf_eq_prime (by rw [pow_two]; exact hs) hs1
  have hsP : IsPGroup 2 (Subgroup.zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)
  obtain ⟨Q₀, hsQ₀⟩ := hsP.exists_le_sylow
  have hEP : IsPGroup 2 E := by
    intro g
    refine ⟨1, Subtype.ext ?_⟩
    have := hE2 g g.2
    rw [Subgroup.coe_pow, Subgroup.coe_one, pow_one, pow_two]; exact this
  obtain ⟨Q₁, hEQ₁⟩ := hEP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S Q₀ Q₁
  have hmem : ∀ x : S, x ∈ (Q₀ : Subgroup S) → g * x * g⁻¹ ∈ (Q₁ : Subgroup S) := by
    intro x hx
    rw [← hg]
    rw [Sylow.coe_subgroup_smul]
    exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
  have hs'Q : g * s * g⁻¹ ∈ (Q₁ : Subgroup S) := hmem s (hsQ₀ (Subgroup.mem_zpowers s))
  have hs'1 : g * s * g⁻¹ ≠ 1 := by
    intro h
    apply hs1
    calc s = g⁻¹ * (g * s * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  obtain ⟨b', hb'Q, hb'2, hb'1, hb'ne, hb'c⟩ :=
    exists_commuting_involution_of_le Q₁ hs'Q hs'1 E hEQ₁ hE2 h4
  refine ⟨g⁻¹ * b' * g, ?_, ?_, ?_, ?_⟩
  · calc g⁻¹ * b' * g * (g⁻¹ * b' * g) = g⁻¹ * (b' * b') * g := by group
      _ = 1 := by rw [hb'2]; group
  · intro h
    apply hb'1
    calc b' = g * (g⁻¹ * b' * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  · intro h
    apply hb'ne
    calc b' = g * (g⁻¹ * b' * g) * g⁻¹ := by group
      _ = g * s * g⁻¹ := by rw [h]
  · have := hb'c
    calc g⁻¹ * b' * g * s = g⁻¹ * (b' * (g * s * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * s * g⁻¹) * b') * g := by rw [this]
      _ = s * (g⁻¹ * b' * g) := by group


theorem commutator_bot_of_le_center {N : Type} [Group N] {A B : Subgroup N} (h : ⁅A, B⁆ ≤ center N)
    (C : Subgroup N) : ⁅⁅A, B⁆, C⁆ = ⊥ := by
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro g hg c _
  have hc := Subgroup.mem_center_iff.1 (h hg) c
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact hc.symm

theorem perfect_cent_descent {N : Type} [Group N] [Finite N] (y : N)
    (hy : ∀ M : Subgroup N, ⁅M, M⁆ = M → M ≤ centralizer ({y} : Set N) → M = ⊥)
    (M : Subgroup (N ⧸ center N)) (hM : ⁅M, M⁆ = M)
    (hMc : ∀ m ∈ M, m * (y : N ⧸ center N) = (y : N ⧸ center N) * m) : M = ⊥ := by
  classical
  set π : N →* N ⧸ center N := QuotientGroup.mk' (center N) with hπ
  set Mt : Subgroup N := M.comap π with hMt
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hmap : Mt.map π = M := Subgroup.map_comap_eq_self_of_surjective hπs M
  set M' : Subgroup N := ⁅Mt, Mt⁆ with hM'
  have hM'map : M'.map π = M := by
    rw [hM', Subgroup.map_commutator, hmap, hM]
  have hdec : ∀ g ∈ Mt, ∃ a ∈ M', ∃ z ∈ center N, g = a * z := by
    intro g hg
    have : π g ∈ M'.map π := hM'map ▸ hg
    obtain ⟨a, ha, hag⟩ := this
    refine ⟨a, ha, a⁻¹ * g, ?_, by group⟩
    have hag' : π a = π g := hag
    have hker : π (a⁻¹ * g) = 1 := by rw [map_mul, map_inv, hag', inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).1 hker
  have hperf : ⁅M', M'⁆ = M' := by
    refine le_antisymm (Subgroup.commutator_le_self _) ?_
    rw [hM', Subgroup.commutator_le]
    intro g hg h hh
    obtain ⟨a, ha, z, hz, rfl⟩ := hdec g hg
    obtain ⟨b, hb, z', hz', rfl⟩ := hdec h hh
    rw [commutator_mul_central a b z z' hz hz']
    exact Subgroup.commutator_mem_commutator ha hb
  have hcent : M' ≤ centralizer ({y} : Set N) := by
    have h1 : ⁅Mt, Subgroup.zpowers y⁆ ≤ center N := by
      rw [Subgroup.commutator_le]
      intro g hg w hw
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
      have hgc : π g * π y = π y * π g := hMc _ hg
      have hpw : π g * π (y ^ n) = π (y ^ n) * π g := by
        rw [map_zpow]
        exact ((Commute.zpow_right (show Commute (π g) (π y) from hgc) n)).eq
      apply (QuotientGroup.eq_one_iff _).1
      show π ⁅g, y ^ n⁆ = 1
      rw [commutatorElement_def]
      simp only [map_mul, map_inv]
      rw [hpw]; group
    have h2 : ⁅⁅Mt, Subgroup.zpowers y⁆, Mt⁆ = ⊥ := commutator_bot_of_le_center h1 Mt
    have h3 : ⁅⁅Subgroup.zpowers y, Mt⁆, Mt⁆ = ⊥ := by
      rw [Subgroup.commutator_comm (Subgroup.zpowers y) Mt]; exact h2
    have h4 : ⁅⁅Mt, Mt⁆, Subgroup.zpowers y⁆ = ⊥ :=
      Subgroup.commutator_commutator_eq_bot_of_rotate h2 h3
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    have : ⁅a, y⁆ ∈ ⁅⁅Mt, Mt⁆, Subgroup.zpowers y⁆ :=
      Subgroup.commutator_mem_commutator ha (Subgroup.mem_zpowers y)
    rw [h4, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  have hbot := hy M' hperf hcent
  rw [← hM'map, hbot, Subgroup.map_bot]


end CFSG.GH74.Generic.S1.Exo
