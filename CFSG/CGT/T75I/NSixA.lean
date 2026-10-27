module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3A6Orbits

public section

namespace CFSG.CGT.T75I

open Equiv Equiv.Perm Subgroup

theorem index_eq_one_of_simple_aux {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Subgroup G) (h : (S.index).factorial < Nat.card G) : S.index = 1 := by
  classical
  let φ := MulAction.toPermHom G (G ⧸ S)
  rcases (MonoidHom.normal_ker φ).eq_bot_or_eq_top with hk | hk
  · exfalso
    have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hk
    have h1 := Nat.card_le_card_of_injective φ hinj
    rw [Nat.card_perm] at h1
    change Nat.card G ≤ S.index.factorial at h1
    omega
  · rw [Subgroup.index_eq_one, eq_top_iff]
    intro g _
    have hg : g ∈ φ.ker := hk ▸ Subgroup.mem_top g
    have h1 : φ g (QuotientGroup.mk 1 : G ⧸ S) = QuotientGroup.mk 1 := by
      rw [MonoidHom.mem_ker.mp hg]
      rfl
    have h2 : φ g (QuotientGroup.mk 1 : G ⧸ S) = QuotientGroup.mk g := by
      change g • (QuotientGroup.mk 1 : G ⧸ S) = _
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    rw [h2] at h1
    have h3 := QuotientGroup.eq.mp h1
    rw [mul_one] at h3
    exact inv_mem_iff.mp h3

theorem orbit_card_one_or_six (K : Subgroup (alternatingGroup (Fin 8)))
    (eK : K ≃* alternatingGroup (Fin 6)) (ω : Fin 8) :
    (MulAction.orbit ↥K ω).ncard = 1 ∨ (MulAction.orbit ↥K ω).ncard = 6 := by
  classical
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hsimple : IsSimpleGroup ↥K := eK.isSimpleGroup
  have hcard : Nat.card ↥K = 360 := by
    rw [Nat.card_congr eK.toEquiv]
    exact CFSG.QuasithinUnique.Setup.X3.card_alt6
  set S := MulAction.stabilizer ↥K ω with hS
  have hidx : S.index = (MulAction.orbit ↥K ω).ncard := MulAction.index_stabilizer ↥K ω
  have hprod : S.index * Nat.card S = 360 := by
    rw [← hcard]
    exact S.index_mul_card
  have hle : S.index ≤ 8 := by
    rw [hidx]
    calc (MulAction.orbit ↥K ω).ncard ≤ (Set.univ : Set (Fin 8)).ncard :=
          Set.ncard_le_ncard (Set.subset_univ _)
      _ = 8 := by simp
  by_cases h1 : S.index = 1
  · left
    rw [← hidx]
    exact h1
  · right
    rw [← hidx]
    have h6 : 6 ≤ S.index := by
      by_contra hlt
      push Not at hlt
      apply h1
      refine index_eq_one_of_simple_aux S ?_
      rw [hcard]
      have : S.index.factorial ≤ Nat.factorial 5 := Nat.factorial_le (by omega)
      have h5 : Nat.factorial 5 = 120 := rfl
      omega
    have hdvd : S.index ∣ 360 := ⟨Nat.card S, hprod.symm⟩
    have h78 : S.index ≠ 7 := by
      intro h7
      rw [h7] at hdvd
      revert hdvd
      decide
    by_cases h8 : S.index = 8
    · exfalso
      have hS45 : Nat.card S = 45 := by
        rw [h8] at hprod
        omega
      have hmap : Nat.card (S.map eK.toMonoidHom) = 45 := by
        rw [Subgroup.card_map_of_injective eK.injective, hS45]
      exact CFSG.QuasithinUnique.Setup.X3.no_subgroup_order
        (K := S.map eK.toMonoidHom) (Or.inr (Or.inr hmap))
    · omega

theorem exists_two_fixed (K : Subgroup (alternatingGroup (Fin 8)))
    (eK : K ≃* alternatingGroup (Fin 6)) :
    ∃ p q : Fin 8, p ≠ q ∧ (∀ k ∈ K, (k : Perm (Fin 8)) p = p ∧ (k : Perm (Fin 8)) q = q) ∧
      ∀ ω : Fin 8, (∀ k ∈ K, (k : Perm (Fin 8)) ω = ω) → ω = p ∨ ω = q := by
  classical
  have hcard : Nat.card ↥K = 360 := by
    rw [Nat.card_congr eK.toEquiv]
    exact CFSG.QuasithinUnique.Setup.X3.card_alt6
  have hsmul : ∀ (k : ↥K) (x : Fin 8),
      k • x = ((k : alternatingGroup (Fin 8)) : Perm (Fin 8)) x := fun k x => rfl
  have hsz := orbit_card_one_or_six K eK
  have hfix_iff : ∀ ω : Fin 8, (MulAction.orbit ↥K ω).ncard = 1 ↔ ∀ k : ↥K, k • ω = ω := by
    intro ω
    constructor
    · intro h k
      obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 h
      have h1 : ω ∈ MulAction.orbit ↥K ω := MulAction.mem_orbit_self ω
      have h2 : k • ω ∈ MulAction.orbit ↥K ω := MulAction.mem_orbit ω k
      rw [ha, Set.mem_singleton_iff] at h1 h2
      rw [h2, h1]
    · intro h
      have : MulAction.orbit ↥K ω = {ω} := by
        ext x
        simp only [MulAction.mem_orbit_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨k, rfl⟩
          exact h k
        · rintro rfl
          exact ⟨1, one_smul _ _⟩
      rw [this]
      exact Set.ncard_singleton ω
  have h6 : ∃ ω₀ : Fin 8, (MulAction.orbit ↥K ω₀).ncard = 6 := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ (k : ↥K) (ω : Fin 8), k • ω = ω := fun k ω =>
      (hfix_iff ω).1 ((hsz ω).resolve_right (hcon ω)) k
    have hone : ∀ k : ↥K, k = 1 := fun k => by
      apply Subtype.ext
      apply Subtype.ext
      apply Equiv.ext
      intro x
      exact hall k x
    have : Nat.card ↥K = 1 :=
      Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => (hone a).trans (hone b).symm⟩, ⟨1⟩⟩
    omega
  obtain ⟨ω₀, hω₀⟩ := h6
  set O := MulAction.orbit ↥K ω₀ with hO
  have hout : ∀ ω : Fin 8, ω ∉ O → (MulAction.orbit ↥K ω).ncard = 1 := by
    intro ω hω
    rcases hsz ω with h | h
    · exact h
    · exfalso
      have hdisj : Disjoint (MulAction.orbit ↥K ω) O := by
        rw [Set.disjoint_left]
        intro x hx1 hx2
        have e1 : MulAction.orbit ↥K x = MulAction.orbit ↥K ω := MulAction.orbit_eq_iff.2 hx1
        have e2 : MulAction.orbit ↥K x = MulAction.orbit ↥K ω₀ := MulAction.orbit_eq_iff.2 hx2
        exact hω (by
          rw [hO, ← e2, e1]
          exact MulAction.mem_orbit_self ω)
      have hu := Set.ncard_union_eq hdisj
      have hle : (MulAction.orbit ↥K ω ∪ O).ncard ≤ 8 := by
        calc (MulAction.orbit ↥K ω ∪ O).ncard ≤ (Set.univ : Set (Fin 8)).ncard :=
              Set.ncard_le_ncard (Set.subset_univ _)
          _ = 8 := by simp
      omega
  have hin : ∀ ω : Fin 8, ω ∈ O → (MulAction.orbit ↥K ω).ncard = 6 := by
    intro ω hω
    rw [MulAction.orbit_eq_iff.2 hω]
    exact hω₀
  have hc2 : Oᶜ.ncard = 2 := by
    have := Set.ncard_add_ncard_compl O
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at this
    omega
  obtain ⟨p, q, hpq, hOc⟩ := Set.ncard_eq_two.1 hc2
  have hpO : p ∉ O := by
    have : p ∈ Oᶜ := by rw [hOc]; simp
    exact this
  have hqO : q ∉ O := by
    have : q ∈ Oᶜ := by rw [hOc]; simp
    exact this
  refine ⟨p, q, hpq, ?_, ?_⟩
  · intro k hk
    exact ⟨(hfix_iff p).1 (hout p hpO) ⟨k, hk⟩, (hfix_iff q).1 (hout q hqO) ⟨k, hk⟩⟩
  · intro ω hω
    by_contra hne
    push Not at hne
    have hωO : ω ∈ O := by
      by_contra h
      have : ω ∈ Oᶜ := h
      rw [hOc] at this
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
      rcases this with h1 | h1
      · exact hne.1 h1
      · exact hne.2 h1
    have h1 : (MulAction.orbit ↥K ω).ncard = 1 :=
      (hfix_iff ω).2 fun k => hω k k.2
    have h2 := hin ω hωO
    omega

theorem mem_of_fix (K : Subgroup (alternatingGroup (Fin 8)))
    (eK : K ≃* alternatingGroup (Fin 6)) {p q : Fin 8} (hpq : p ≠ q)
    (hfix : ∀ k ∈ K, (k : Perm (Fin 8)) p = p ∧ (k : Perm (Fin 8)) q = q)
    (g : alternatingGroup (Fin 8)) (hp : (g : Perm (Fin 8)) p = p) (hq : (g : Perm (Fin 8)) q = q) :
    g ∈ K := by
  classical
  have hcard : Nat.card ↥K = 360 := by
    rw [Nat.card_congr eK.toEquiv]
    exact CFSG.QuasithinUnique.Setup.X3.card_alt6
  let β := {x : Fin 8 // x ≠ p ∧ x ≠ q}
  have hβcard : Fintype.card β = 6 := by
    rw [Fintype.card_subtype]
    have : (Finset.univ.filter fun x : Fin 8 => x ≠ p ∧ x ≠ q) = ({p, q} : Finset (Fin 8))ᶜ := by
      ext x
      simp
    rw [this, Finset.card_compl, Finset.card_pair hpq]
    simp
  have : Nontrivial β := by
    rw [← Fintype.one_lt_card_iff_nontrivial, hβcard]
    norm_num
  have hAcard : Nat.card (alternatingGroup β) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, hβcard]
    decide
  let S : Set (alternatingGroup (Fin 8)) :=
    {g | (g : Perm (Fin 8)) p = p ∧ (g : Perm (Fin 8)) q = q}
  have hfixmem : ∀ g : ↥S, ∀ x, (((g : alternatingGroup (Fin 8)) : Perm (Fin 8)) x ≠ p ∧
      ((g : alternatingGroup (Fin 8)) : Perm (Fin 8)) x ≠ q) ↔ (x ≠ p ∧ x ≠ q) := by
    intro g x
    have hg := g.2
    obtain ⟨hgp, hgq⟩ := hg
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h1 (by rw [h]; exact hgp), fun h => h2 (by rw [h]; exact hgq)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h1 (((g : alternatingGroup (Fin 8)) : Perm (Fin 8)).injective
        (h.trans hgp.symm)), fun h => h2 (((g : alternatingGroup (Fin 8)) : Perm (Fin 8)).injective
        (h.trans hgq.symm))⟩
  let f : ↥S → alternatingGroup β := fun g =>
    ⟨((g : alternatingGroup (Fin 8)) : Perm (Fin 8)).subtypePerm (hfixmem g), by
      rw [Equiv.Perm.mem_alternatingGroup,
        Equiv.Perm.sign_subtypePerm _ (hfixmem g) (fun x hx => by
          by_contra hcon
          apply hx
          rw [not_and_or] at hcon
          rcases hcon with h | h
          · push Not at h
            rw [h]
            exact g.2.1
          · push Not at h
            rw [h]
            exact g.2.2)]
      exact Equiv.Perm.mem_alternatingGroup.1 (g : alternatingGroup (Fin 8)).2⟩
  have hf : Function.Injective f := by
    intro g g' h
    apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    intro x
    by_cases hxp : x = p
    · rw [hxp, g.2.1, g'.2.1]
    by_cases hxq : x = q
    · rw [hxq, g.2.2, g'.2.2]
    have hfx : ∀ (g : ↥S) (x : Fin 8) (hx : x ≠ p ∧ x ≠ q),
        ((((f g : alternatingGroup β)) : Perm β) ⟨x, hx⟩ : Fin 8) =
          ((g : alternatingGroup (Fin 8)) : Perm (Fin 8)) x := fun g x hx => rfl
    rw [← hfx g x ⟨hxp, hxq⟩, ← hfx g' x ⟨hxp, hxq⟩, h]
  have hSle : S.ncard ≤ 360 := by
    rw [← Nat.card_coe_set_eq, ← hAcard]
    exact Nat.card_le_card_of_injective f hf
  have hKS : (K : Set (alternatingGroup (Fin 8))) ⊆ S := fun k hk => hfix k hk
  have hKn : (K : Set (alternatingGroup (Fin 8))).ncard = 360 := by
    rw [← hcard, ← Nat.card_coe_set_eq]
    rfl
  have heq : (K : Set (alternatingGroup (Fin 8))) = S :=
    Set.eq_of_subset_of_ncard_le hKS (by rw [hKn]; exact hSle) (Set.toFinite S)
  have : g ∈ S := ⟨hp, hq⟩
  rw [← heq] at this
  exact this

end CFSG.CGT.T75I
