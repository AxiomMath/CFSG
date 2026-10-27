module

public import CFSG.LocalAnalysis.GL83PartI.I_27_9_3.Rep

public section

namespace GL83.PiGen

open Equiv Equiv.Perm GL83 GL83.CompFam CFSG.Open

section Props

variable {X : Type*} [Group X] {K : Subgroup X} {n : ℕ}

theorem Implements.mem_subAlt_fix_conj {e : ↥K ≃* ↥(alternatingGroup (Fin n))} {g : X}
    {ρ σ : Perm (Fin n)} (h : Implements e g ρ) (hc : σ * ρ = ρ * σ) {x : X}
    (hx : x ∈ subAlt e (fixFinset σ : Set (Fin n))) :
    g * x * g⁻¹ ∈ subAlt e (fixFinset σ : Set (Fin n)) :=
  h.mem_subAlt_conj (fun ω => by
    simpa only [Finset.mem_coe] using apply_mem_fixFinset_iff_of_commute hc ω) hx

theorem subAlt_fix_le {e : ↥K ≃* ↥(alternatingGroup (Fin n))} {d : X} {σ : Perm (Fin n)}
    (hd : Implements e d σ) :
    subAlt e (fixFinset σ : Set (Fin n)) ≤ K ⊓ Subgroup.centralizer ({d} : Set X) := by
  intro x hx
  refine ⟨subAlt_le e _ hx, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
  rw [Set.mem_singleton_iff.1 hh]
  exact hd.comm_of_mem_subAlt (fun ω hω => mem_fixFinset.1 hω) hx

theorem commute_of_implements_of_comm {e : ↥K ≃* ↥(alternatingGroup (Fin n))} {d : X}
    {σ : Perm (Fin n)} (hd : Implements e d σ) {g : X} (hgK : g ∈ K) (hcomm : d * g = g * d) :
    σ * ((e ⟨g, hgK⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) =
      ((e ⟨g, hgK⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) * σ := by
  obtain ⟨z, hz, hσ⟩ := hd ⟨g, hgK⟩
  have hdg : d * g * d⁻¹ = g := by rw [hcomm]; group
  have hz' : z = ⟨g, hgK⟩ := Subtype.ext (hz.trans hdg)
  rw [hz'] at hσ
  calc σ * ((e ⟨g, hgK⟩ : alternatingGroup (Fin n)) : Perm (Fin n))
      = σ * ((e ⟨g, hgK⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) * σ⁻¹ * σ := by group
    _ = ((e ⟨g, hgK⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) * σ := by rw [hσ]

theorem subAlt_fix_normal {e : ↥K ≃* ↥(alternatingGroup (Fin n))} {d : X} {σ : Perm (Fin n)}
    (hd : Implements e d σ) :
    ((subAlt e (fixFinset σ : Set (Fin n))).subgroupOf
      (K ⊓ Subgroup.centralizer ({d} : Set X))).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (subAlt_fix_le hd)]
  intro x g hx hg
  obtain ⟨hgK, hgc⟩ := hg
  have hcomm : d * g = g * d := Subgroup.mem_centralizer_iff.1 hgc d (Set.mem_singleton d)
  exact (implements_of_mem e hgK).mem_subAlt_fix_conj
    (commute_of_implements_of_comm hd hgK hcomm) hx

theorem exists_two_mem_sdiff {S : Finset (Fin n)} {a b : Fin n} (hab : a ≠ b) (h5 : 5 ≤ S.card) :
    ∃ x ∈ S, ∃ y ∈ S, x ≠ a ∧ x ≠ b ∧ y ≠ a ∧ y ≠ b ∧ x ≠ y := by
  have h1 : 1 < (S \ {a, b}).card := by
    have h2 := Finset.le_card_sdiff {a, b} S
    have h3 : ({a, b} : Finset (Fin n)).card = 2 := Finset.card_pair hab
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 h1
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hx hy
  exact ⟨x, hx.1, y, hy.1, hx.2.1, hx.2.2, hy.2.1, hy.2.2, hxy⟩

theorem three_le_card_of_mem {S : Finset (Fin n)} {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) : 3 ≤ S.card := by
  have hsub : ({a, b, c} : Finset (Fin n)) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have h3 : ({a, b, c} : Finset (Fin n)).card = 3 :=
    Finset.card_eq_three.2 ⟨a, b, c, hab, hac, hbc, rfl⟩
  exact h3 ▸ Finset.card_le_card hsub

theorem not_le_centralizer_subAlt {e : ↥K ≃* ↥(alternatingGroup (Fin n))} {T : Subgroup X}
    {a b : Fin n} (hab : a ≠ b) {t₀ : X} (ht₀ : t₀ ∈ T) (hi : Implements e t₀ (swap a b))
    {S : Finset (Fin n)} (ha : a ∈ S) (h5 : 5 ≤ S.card) :
    ¬ T ≤ Subgroup.centralizer ((subAlt e (S : Set (Fin n)) : Subgroup X) : Set X) := by
  intro hle
  obtain ⟨x, hx, y, hy, hxa, hxb, hya, hyb, hxy⟩ := exists_two_mem_sdiff hab h5
  have hz : cyc3 a x y ∈ altOn (S : Set (Fin n)) :=
    cyc3_mem_altOn (Finset.mem_coe.2 ha) (Finset.mem_coe.2 hx) (Finset.mem_coe.2 hy)
      ⟨hxa.symm, hya.symm, hxy⟩
  obtain ⟨w, hw, hwK, hwe⟩ := exists_mem_subAlt_eq e hz
  have hcomm := Subgroup.mem_centralizer_iff.1 (hle ht₀) w hw
  obtain ⟨z, hz1, hz2⟩ := hi ⟨w, hwK⟩
  have hz3 : z = ⟨w, hwK⟩ := Subtype.ext (by
    rw [hz1, ← hcomm]
    group)
  rw [hz3, hwe] at hz2
  exact swap_conj_cyc3_ne hab hxa hxb hya hyb hxy (by simpa [swap_inv] using hz2)

end Props

section Main

variable {X : Type*} [Group X] [Finite X] {K : Subgroup X} {n : ℕ} {p : ℕ} [Fact p.Prime]

theorem exists_subAlt_family (hp3 : 3 ≤ p) {k : ℕ} (hk : 1 ≤ k) (hnk : n = k * p + 2)
    (hn5 : 5 ≤ n) (hn6 : n ≠ 6) (hZ : Subgroup.center K = ⊥) (hK : IsComponentOf K ⊤)
    (e : ↥K ≃* ↥(alternatingGroup (Fin n))) {B : Subgroup X} (hB : IsElemAbelian p B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hrank : GLATwoLocalRank p X ≤ pRank p B)
    {T : Subgroup X} (hBT : B ≤ Subgroup.normalizer (T : Set X))
    (hTN : T ≤ Subgroup.normalizer (K : Set X)) {τ : Perm (Fin n)} (hτ : τ.IsSwap)
    (hT : ∀ t ∈ T, ∃ j : ℤ, Implements e t (τ ^ j)) (hTτ : ∃ t ∈ T, Implements e t τ)
    {D : Subgroup X} (hDB : D ≤ B) (hD : Nat.card D = p ^ 2) :
    ∃ (𝒟 : Set X) (Kf : X → Subgroup X),
      (∀ d ∈ 𝒟, d ∈ D ∧ d ≠ 1) ∧
      (∀ d ∈ 𝒟, Kf d ≤ K ⊓ Subgroup.centralizer ({d} : Set X) ∧
        ((Kf d).subgroupOf (K ⊓ Subgroup.centralizer ({d} : Set X))).Normal ∧
        (∃ k' : ℕ, 1 ≤ k' ∧ Nonempty (↥(Kf d) ≃* ↥(alternatingGroup (Fin (k' * p + 2))))) ∧
        B ⊔ T ≤ Subgroup.normalizer (Kf d : Set X) ∧
        ¬ T ≤ Subgroup.centralizer (Kf d : Set X)) ∧
      K = ⨆ d ∈ 𝒟, Kf d := by
  classical
  have hp := (Fact.out : p.Prime)
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  obtain ⟨a, b, hab, rfl⟩ := hτ
  set π := piRep hZ hn5 hn6 e with hπ
  have himp : ∀ {g : X} (hg : g ∈ Subgroup.normalizer (K : Set X)), Implements e g (π ⟨g, hg⟩) :=
    fun hg => implements_piRep hZ hn5 hn6 e hg
  have hπT : ∀ {t : X} (ht : t ∈ T), π ⟨t, hTN ht⟩ ∈ Subgroup.zpowers (swap a b) := by
    intro t ht
    obtain ⟨j, hj⟩ := hT t ht
    rw [piRep_eq_of_implements hZ hn5 hn6 e (hTN ht) hj]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) j
  obtain ⟨t₀, ht₀, ht₀i⟩ := hTτ
  have hπt₀ : π ⟨t₀, hTN ht₀⟩ = swap a b :=
    piRep_eq_of_implements hZ hn5 hn6 e (hTN ht₀) ht₀i
  have hBcomm : ∀ {c : X} (hc : c ∈ B), π ⟨c, hBN hc⟩ * swap a b = swap a b * π ⟨c, hBN hc⟩ := by
    intro c hc
    have hctc : c * t₀ * c⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 (hBT hc) t₀).1 ht₀
    have h1 := hπT hctc
    have h2 : π ⟨c * t₀ * c⁻¹, hTN hctc⟩ = π ⟨c, hBN hc⟩ * swap a b * (π ⟨c, hBN hc⟩)⁻¹ := by
      rw [← hπt₀, ← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [h2] at h1
    rcases zpowers_swap hab h1 with h3 | h3
    · exfalso
      have h4 : swap a b = 1 := by
        have := mul_inv_eq_one.1 h3
        simpa using this
      have h5 : (swap a b) a = a := by rw [h4]; rfl
      rw [swap_apply_left] at h5
      exact hab h5.symm
    · calc π ⟨c, hBN hc⟩ * swap a b
          = π ⟨c, hBN hc⟩ * swap a b * (π ⟨c, hBN hc⟩)⁻¹ * π ⟨c, hBN hc⟩ := by group
        _ = swap a b * π ⟨c, hBN hc⟩ := by rw [h3]
  have hπpow : ∀ {c : X} (hc : c ∈ B), π ⟨c, hBN hc⟩ ^ p = 1 := by
    intro c hc
    rw [← map_pow]
    have : (⟨c, hBN hc⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ p = 1 :=
      Subtype.ext (by simpa using hB.2 c hc)
    rw [this, map_one]
  have hfix : ∀ {c : X} (hc : c ∈ B), π ⟨c, hBN hc⟩ a = a ∧ π ⟨c, hBN hc⟩ b = b :=
    fun hc => fixes_of_commute_swap hab (hBcomm hc) hpodd (hπpow hc)
  have hBcommB : ∀ {c d : X} (hc : c ∈ B) (hd : d ∈ B),
      π ⟨d, hBN hd⟩ * π ⟨c, hBN hc⟩ = π ⟨c, hBN hc⟩ * π ⟨d, hBN hd⟩ := by
    intro c d hc hd
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (elem_comm hB hd hc)
  obtain ⟨S, hS⟩ : ∃ S : X → Finset (Fin n),
      ∀ {d : X} (hd : d ∈ D), S d = fixFinset (π ⟨d, hBN (hDB hd)⟩) :=
    ⟨fun g => if h : g ∈ D then fixFinset (π ⟨g, hBN (hDB h)⟩) else ∅, fun hd => by simp [hd]⟩
  obtain ⟨𝒟, h𝒟⟩ : ∃ 𝒟 : Set X, ∀ d, d ∈ 𝒟 ↔ d ∈ D ∧ d ≠ 1 ∧ 3 ≤ (S d).card :=
    ⟨{d | d ∈ D ∧ d ≠ 1 ∧ 3 ≤ (S d).card}, fun d => Iff.rfl⟩
  have haS : ∀ {d : X} (hd : d ∈ D), a ∈ S d ∧ b ∈ S d := fun hd => by
    rw [hS hd]
    exact ⟨mem_fixFinset.2 (hfix (hDB hd)).1, mem_fixFinset.2 (hfix (hDB hd)).2⟩
  have hcard : ∀ {d : X}, d ∈ 𝒟 → ∃ k' : ℕ, 1 ≤ k' ∧ (S d).card = k' * p + 2 := by
    intro d hd
    obtain ⟨hdD, -, hd3⟩ := (h𝒟 d).1 hd
    have hmod := card_fixFinset_modEq (p := p) (hπpow (hDB hdD))
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hmod
    rw [hS hdD] at hd3 ⊢
    exact exists_card_eq_of_modEq hp3 hnk hmod hd3
  obtain ⟨Kf, hKf⟩ : ∃ Kf : X → Subgroup X, ∀ d, Kf d = subAlt e (S d : Set (Fin n)) :=
    ⟨fun d => subAlt e (S d : Set (Fin n)), fun d => rfl⟩
  refine ⟨𝒟, Kf, fun d hd => ((h𝒟 d).1 hd).imp_right (fun h => h.1), ?_, ?_⟩
  · intro d hd
    obtain ⟨hdD, hd1, hd3⟩ := (h𝒟 d).1 hd
    have hdN : d ∈ Subgroup.normalizer (K : Set X) := hBN (hDB hdD)
    have hdimp := himp hdN
    obtain ⟨k', hk', hk'c⟩ := hcard hd
    have hSd := hS hdD
    have h5 : 5 ≤ (S d).card := by
      rw [hk'c]
      nlinarith
    rw [hKf d, hSd]
    refine ⟨subAlt_fix_le hdimp, subAlt_fix_normal hdimp, ?_, ?_, ?_⟩
    · refine ⟨k', hk', ?_⟩
      have hc : (fixFinset (π ⟨d, hdN⟩)).card = k' * p + 2 := hSd ▸ hk'c
      exact ⟨(subAltEquiv e _).trans (exists_altOn_equiv_fin _ hc).some⟩
    · refine sup_le (fun c hc => ?_) (fun t ht => ?_)
      · refine Subgroup.mem_normalizer_fintype fun x hx => ?_
        exact (himp (hBN hc)).mem_subAlt_fix_conj (hBcommB hc (hDB hdD)) hx
      · refine Subgroup.mem_normalizer_fintype fun x hx => ?_
        have ha : a ∈ (fixFinset (π ⟨d, hdN⟩) : Set (Fin n)) := by
          have := (haS hdD).1
          rwa [hSd] at this
        have hb : b ∈ (fixFinset (π ⟨d, hdN⟩) : Set (Fin n)) := by
          have := (haS hdD).2
          rwa [hSd] at this
        exact (himp (hTN ht)).mem_subAlt_conj
          (preserves_of_mem_zpowers_swap hab ha hb (hπT ht)) hx
    · have h5' : 5 ≤ (fixFinset (π ⟨d, hdN⟩)).card := hSd ▸ h5
      exact not_le_centralizer_subAlt hab ht₀ (hπt₀ ▸ himp (hTN ht₀) : Implements e t₀ (swap a b))
        (mem_fixFinset.2 (hfix (hDB hdD)).1) h5'
  ·
    have hmem : ∀ ω : Fin n, ω ≠ a → ω ≠ b → ∃ d : X, d ∈ 𝒟 ∧ ω ∈ S d := by
      intro ω hωa hωb
      obtain ⟨d, hdD, hd1, hdω⟩ :=
        exists_fixing_of_plane hp3 hk hnk hn5 hn6 hZ hK e hB hBN hrank hDB hD ω
      have hSd := hS hdD
      refine ⟨d, (h𝒟 d).2 ⟨hdD, hd1, ?_⟩, ?_⟩
      · rw [hSd]
        exact three_le_card_of_mem hab hωa.symm hωb.symm (mem_fixFinset.2 (hfix (hDB hdD)).1)
          (mem_fixFinset.2 (hfix (hDB hdD)).2) (mem_fixFinset.2 hdω)
      · rw [hSd]
        exact mem_fixFinset.2 hdω
    obtain ⟨ω₀, hω₀a, hω₀b⟩ : ∃ ω : Fin n, ω ≠ a ∧ ω ≠ b := by
      have h2 : ({a, b} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
        rw [Finset.card_pair hab, Finset.card_univ, Fintype.card_fin]
        omega
      obtain ⟨ω, -, hω⟩ := Finset.exists_mem_notMem_of_card_lt_card h2
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hω
      exact ⟨ω, hω.1, hω.2⟩
    have hcover : (⋃ i : 𝒟, ((S i.1 : Finset (Fin n)) : Set (Fin n))) = Set.univ := by
      refine Set.eq_univ_of_forall fun ω => Set.mem_iUnion.2 ?_
      by_cases hω : ω = a ∨ ω = b
      · obtain ⟨d, hd, -⟩ := hmem ω₀ hω₀a hω₀b
        refine ⟨⟨d, hd⟩, ?_⟩
        have hdD := ((h𝒟 d).1 hd).1
        rcases hω with rfl | rfl
        · exact (haS hdD).1
        · exact (haS hdD).2
      · obtain ⟨d, hd, hdω⟩ := hmem ω (fun h => hω (Or.inl h)) (fun h => hω (Or.inr h))
        exact ⟨⟨d, hd⟩, hdω⟩
    have hS3 : ∀ i : 𝒟, 3 ≤ ((S i.1 : Finset (Fin n)) : Set (Fin n)).ncard := fun i => by
      rw [Set.ncard_coe_finset]
      exact ((h𝒟 i.1).1 i.2).2.2
    have hconn : ∀ i j : 𝒟, Relation.ReflTransGen (fun x y : 𝒟 =>
        (((S x.1 : Finset (Fin n)) : Set (Fin n)) ∩
          ((S y.1 : Finset (Fin n)) : Set (Fin n))).Nonempty) i j := fun i j =>
      Relation.ReflTransGen.single ⟨a, (haS ((h𝒟 i.1).1 i.2).1).1, (haS ((h𝒟 j.1).1 j.2).1).1⟩
    have : Nonempty (Fin n) := ⟨a⟩
    have hgen := iSup_altOn_eq_alternatingGroup
      (S := fun i : 𝒟 => ((S i.1 : Finset (Fin n)) : Set (Fin n))) hS3 hcover hconn
    have hK' := iSup_subAlt e (fun i : 𝒟 => ((S i.1 : Finset (Fin n)) : Set (Fin n))) hgen
    simp only [hKf]
    rw [iSup_subtype']
    exact hK'.symm

end Main

end GL83.PiGen
