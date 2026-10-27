module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.MaxD2PermSound

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.MaxD2

@[expose] def TorusLocal (p : ℕ) {X : Type*} [Group X] (R : Subgroup X) : Prop :=
  Nat.card R = p ^ 2 ∧
  (∀ Y : Subgroup X, Subgroup.normalizer (R : Set X) ≤ Y →
    Y = Subgroup.normalizer (R : Set X) ∨ Y = ⊤) ∧
  Subgroup.centralizer (R : Set X) ≤ R ∧
  Group.IsSolvable (Subgroup.normalizer (R : Set X)) ∧
  ∃ t, t ∈ Subgroup.normalizer (R : Set X) ∧
    ∃ m lam e : ℕ, 2 ≤ m ∧ orderOf (lam : ZMod p) = p - 1 ∧ 6 ∣ e ∧
    (∀ x ∈ R, t ^ m * x * (t ^ m)⁻¹ = x ^ lam) ∧ (∀ x ∈ R, t ^ e * x * (t ^ e)⁻¹ = x⁻¹) ∧
    ∀ k : ℕ, 0 < k → k < m → ∀ Y₀ : Subgroup X, Y₀ ≤ R → Nat.card Y₀ = p →
      t ^ k ∉ Subgroup.normalizer (Y₀ : Set X)

section Transport

variable {X Y : Type*} [Group X] [Group Y] {p : ℕ}

theorem TorusLocal.map [Finite X] {R : Subgroup X} (e : X ≃* Y) (h : TorusLocal p R) :
    TorusLocal p (R.map e.toMonoidHom) := by
  obtain ⟨hcard, hmax, hcent, hsolv, t, htN, m, lam, k, hm, hlam, hk, hpow, hinv, hline⟩ := h
  have hnorm : Subgroup.normalizer ((R.map e.toMonoidHom : Subgroup Y) : Set Y) =
      (Subgroup.normalizer (R : Set X)).map e.toMonoidHom :=
    (Subgroup.map_equiv_normalizer_eq R e).symm
  refine ⟨?_, ?_, ?_, ?_, e t, ?_, m, lam, k, hm, hlam, hk, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.injective, hcard]
  · intro Y' hY'
    rw [hnorm] at hY' ⊢
    have h1 : Subgroup.normalizer (R : Set X) ≤ Y'.comap e.toMonoidHom := by
      intro x hx
      exact hY' ⟨x, hx, rfl⟩
    rcases hmax _ h1 with h2 | h2
    · left
      rw [← Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective Y', h2]
    · right
      rw [← Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective Y', h2,
        Subgroup.map_top_of_surjective _ e.surjective]
  · intro g hg
    obtain ⟨x, rfl⟩ := e.surjective g
    refine ⟨x, hcent ?_, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have := Subgroup.mem_centralizer_iff.1 hg (e r) ⟨r, hr, rfl⟩
    exact e.injective (by simpa using this)
  · rw [hnorm]
    have := hsolv
    exact Group.isSolvable_of_surjective (f := (Subgroup.equivMapOfInjective _ e.toMonoidHom
      e.injective).toMonoidHom) (Subgroup.equivMapOfInjective _ e.toMonoidHom
      e.injective).surjective
  · rw [hnorm]
    exact ⟨t, htN, rfl⟩
  · rintro _ ⟨r, hr, rfl⟩
    simpa using congrArg e (hpow r hr)
  · rintro _ ⟨r, hr, rfl⟩
    simpa using congrArg e (hinv r hr)
  · intro j hj0 hjm Y₀ hY₀ hcard₀ hn
    have hle : Y₀.comap e.toMonoidHom ≤ R := by
      intro x hx
      obtain ⟨r, hr, hrx⟩ := hY₀ hx
      have : r = x := e.injective hrx
      exact this ▸ hr
    have hcard' : Nat.card (Y₀.comap e.toMonoidHom) = p := by
      rw [← hcard₀, ← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective
        (K := Y₀.comap e.toMonoidHom),
        Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective]
    refine hline j hj0 hjm _ hle hcard' ?_
    refine Subgroup.mem_normalizer_fintype fun n hn' => ?_
    have hen : e n ∈ Y₀ := hn'
    show e (t ^ j * n * (t ^ j)⁻¹) ∈ Y₀
    rw [map_mul, map_mul, map_inv, map_pow]
    exact (Subgroup.mem_normalizer_iff.1 hn (e n)).1 hen

end Transport

section SubgroupOf

variable {Q : Type*} [Group Q] [Finite Q] {p : ℕ}

theorem torusLocal_of_localData {G R : Subgroup Q} {m lam e : ℕ}
    (h : LocalData p m lam e G R) (hm : 2 ≤ m) (hlam : orderOf (lam : ZMod p) = p - 1)
    (he : 6 ∣ e) : TorusLocal p (R.subgroupOf G) := by
  obtain ⟨hRG, hcard, hmax, hcent, hsolv, t, htN, hpow, hinv, hline⟩ := h
  have hnorm : Subgroup.normalizer ((R.subgroupOf G : Subgroup G) : Set G) =
      (Subgroup.normalizer (R : Set Q)).subgroupOf G :=
    (Subgroup.subgroupOf_normalizer_eq hRG).symm
  refine ⟨?_, ?_, ?_, ?_, ⟨t, htN.2⟩, ?_, m, lam, e, hm, hlam, he, ?_, ?_, ?_⟩
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRG).toEquiv, hcard]
  · intro Y hY
    rw [hnorm] at hY ⊢
    have h1 : Subgroup.normalizer (R : Set Q) ⊓ G ≤ Y.map G.subtype := by
      rintro x ⟨hx1, hx2⟩
      exact ⟨⟨x, hx2⟩, hY (Subgroup.mem_subgroupOf.2 hx1), rfl⟩
    have hYY : (Y.map G.subtype).subgroupOf G = Y :=
      Subgroup.comap_map_eq_self_of_injective G.subtype_injective Y
    rcases hmax _ h1 (Subgroup.map_subtype_le Y) with h2 | h2
    · left
      rw [← hYY, h2, Subgroup.inf_subgroupOf_right]
    · right
      rw [← hYY, h2, Subgroup.subgroupOf_self]
  · intro g hg
    rw [Subgroup.mem_subgroupOf]
    refine hcent g g.2 fun r hr => ?_
    have := Subgroup.mem_centralizer_iff.1 hg ⟨r, hRG hr⟩ (Subgroup.mem_subgroupOf.2 hr)
    exact (congrArg Subtype.val this).symm
  · rw [hnorm, ← Subgroup.inf_subgroupOf_right]
    have := hsolv
    exact Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : Subgroup.normalizer (R : Set Q) ⊓ G ≤ G)).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe
        (inf_le_right : Subgroup.normalizer (R : Set Q) ⊓ G ≤ G)).symm.surjective
  · rw [hnorm]
    exact Subgroup.mem_subgroupOf.2 htN.1
  · intro x hx
    have hx' : (x : Q) ∈ R := Subgroup.mem_subgroupOf.1 hx
    exact Subtype.ext (by simpa using hpow x hx')
  · intro x hx
    have hx' : (x : Q) ∈ R := Subgroup.mem_subgroupOf.1 hx
    exact Subtype.ext (by simpa using hinv x hx')
  · intro j hj0 hjm Y₀ hY₀ hcard₀ hn
    have hle : Y₀.map G.subtype ≤ R := by
      rintro _ ⟨y, hy, rfl⟩
      exact Subgroup.mem_subgroupOf.1 (hY₀ hy)
    have hcard' : Nat.card (Y₀.map G.subtype) = p := by
      rw [Subgroup.card_map_of_injective G.subtype_injective, hcard₀]
    refine hline j hj0 hjm _ hle hcard' ?_
    refine Subgroup.mem_normalizer_fintype fun n hn' => ?_
    obtain ⟨y, hy, rfl⟩ := hn'
    refine ⟨_, (Subgroup.mem_normalizer_iff.1 hn y).1 hy, ?_⟩
    simp

end SubgroupOf

section Sylow

variable {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y] {p : ℕ}

theorem torusLocal_sylow [Fact p.Prime] (e : X ≃* Y) {R₀ : Subgroup Y} (h : TorusLocal p R₀)
    (hsyl : Nat.card R₀ = p ^ (Nat.card Y).factorization p) (R : Sylow p X) :
    TorusLocal p (R : Subgroup X) := by
  have h1 := TorusLocal.map e.symm h
  have hcard : Nat.card (R₀.map e.symm.toMonoidHom) = p ^ (Nat.card X).factorization p := by
    rw [Subgroup.card_map_of_injective e.symm.injective, hsyl, Nat.card_congr e.toEquiv]
  let R₁ : Sylow p X := Sylow.ofCard (R₀.map e.symm.toMonoidHom) hcard
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq X R₁ R
  have hRc : (R : Subgroup X) = (R₀.map e.symm.toMonoidHom).map (MulAut.conj c).toMonoidHom := by
    rw [← hc, Sylow.coe_subgroup_smul]
    rfl
  rw [hRc]
  exact TorusLocal.map (MulAut.conj c) h1

end Sylow

theorem rep_getD_of_forall {n : ℕ} {L : List Tab} {P : List (Equiv.Perm (Fin n))}
    (hlen : L.length = P.length)
    (h : ∀ i (hi : i < L.length), TabRep (L[i]) (P[i]'(hlen ▸ hi))) :
    ∀ j, TabRep (L.toArray.getD j (idTab n)) (P.getD j 1) := by
  intro j
  by_cases hj : j < L.length
  · rw [show L.toArray.getD j (idTab n) = L[j] by simp [hj],
      show P.getD j 1 = P[j]'(hlen ▸ hj) by simp [hlen ▸ hj]]
    exact h j hj
  · have h1 : L.toArray.getD j (idTab n) = idTab n := by simp [hj]
    have h2 : P.getD j 1 = 1 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
    rw [h1, h2]
    exact TabRep.idTab

theorem factorization_eq_of_pow_dvd {p k n : ℕ} (hp : p.Prime) (h1 : p ^ k ∣ n)
    (h2 : ¬ p ^ (k + 1) ∣ n) (h0 : n ≠ 0) : n.factorization p = k := by
  have h3 : k ≤ n.factorization p := (hp.pow_dvd_iff_le_factorization h0).1 h1
  have h4 : ¬ k + 1 ≤ n.factorization p := fun h => h2 ((hp.pow_dvd_iff_le_factorization h0).2 h)
  omega

end CFSG.AGLEmbeddingD2
