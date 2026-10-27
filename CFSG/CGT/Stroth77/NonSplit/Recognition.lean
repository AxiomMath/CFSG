module

public import CFSG.CGT.Stroth77.NonSplit.Tits

public section

namespace CFSG.CGT.Stroth77

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique Equiv Equiv.Perm
  CFSG.HardMathSupport.Cooperstein.Coordinator CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
  CFSG.Permutation.SymmetricCoxeter

namespace Recognition

theorem eq_top_of_ker_le {H : Type*} [Group H] (θ : H →* Perm (Fin 6)) (s : ℕ → H)
    (hs : ∀ k < 5, θ (s k) = adjSwap 5 k) (S : Subgroup H) (hker : θ.ker ≤ S)
    (hS : ∀ k < 5, s k ∈ S) : S = ⊤ := by
  have hK : (Subgroup.closure (s '' Set.Iio 5)).map θ = ⊤ := by
    rw [MonoidHom.map_closure, ← closure_adjSwap 5]
    congr 1
    ext σ
    simp only [Set.mem_image, Set.mem_Iio]
    constructor
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨k, hk, (hs k hk).symm⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨_, ⟨k, hk, rfl⟩, hs k hk⟩
  have hle : Subgroup.closure (s '' Set.Iio 5) ≤ S := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact hS k hk
  rw [eq_top_iff, ← ker_sup_eq_top θ _ hK]
  exact sup_le hker hle

theorem card_heart : Nat.card (Multiplicative (altHeart 6)) = 16 := by
  rw [Nat.card_congr ψns.toEquiv, card_Qns]

theorem card_eq_of_ker {G : Type*} [Group G] (θ : G →* Perm (Fin 6)) (hθ : Function.Surjective θ)
    (ψ : Multiplicative (altHeart 6) ≃* θ.ker) : Nat.card G = 11520 := by
  have h1 : Nat.card θ.ker = 16 := by rw [← Nat.card_congr ψ.toEquiv, card_heart]
  have h2 : Nat.card (Perm (Fin 6)) = 720 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; rfl
  rw [← Subgroup.card_ker_mul_card_of_surjective hθ, h1, h2]

section Fibre

variable {G : Type*} [Group G] (θ : G →* Perm (Fin 6))

def fibre : Subgroup (G × Mns) where
  carrier := {p | θ p.1 = θns p.2}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Prod.fst_mul, Prod.snd_mul, map_mul] at *
    rw [ha, hb]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, Prod.fst_inv, Prod.snd_inv, map_inv] at *
    rw [ha]

theorem mem_fibre {p : G × Mns} : p ∈ fibre θ ↔ θ p.1 = θns p.2 := Iff.rfl

theorem fibre_ext {a b : fibre θ} (h1 : (a : G × Mns).1 = (b : G × Mns).1)
    (h2 : (a : G × Mns).2 = (b : G × Mns).2) : a = b :=
  Subtype.ext (Prod.ext h1 h2)

variable (ψ : Multiplicative (altHeart 6) ≃* θ.ker)

noncomputable def deltaHom : Multiplicative (altHeart 6) →* fibre θ where
  toFun v := ⟨(((ψ v : θ.ker) : G), (ψns v : Mns)), by
    rw [mem_fibre, MonoidHom.mem_ker.1 (ψ v).2]
    exact (MonoidHom.mem_ker.1 (ψns v).2).symm⟩
  map_one' := fibre_ext θ (by simp) (by simp)
  map_mul' a b := fibre_ext θ (by simp) (by simp)

variable {ψ}

theorem delta_normal
    (hconj : ∀ (g : G) (v : Multiplicative (altHeart 6)), g * (ψ v : G) * g⁻¹ =
      (ψ (Multiplicative.ofAdd (altAct (θ g) v.toAdd)) : G)) :
    (deltaHom θ ψ).range.Normal := by
  refine ⟨fun n hn d => ?_⟩
  obtain ⟨v, rfl⟩ := hn
  refine ⟨Multiplicative.ofAdd (altAct (θ d.1.1) v.toAdd), ?_⟩
  refine fibre_ext θ (hconj d.1.1 v).symm ?_
  have hd : θ d.1.1 = θns d.1.2 := d.2
  show (ψns (Multiplicative.ofAdd (altAct (θ d.1.1) v.toAdd)) : Mns) =
    d.1.2 * (ψns v : Mns) * d.1.2⁻¹
  rw [hd, ψns_conj]

variable (t : ℕ → G) (hθt : ∀ k < 5, θ (t k) = adjSwap 5 k)

def tauD (k : ℕ) : fibre θ :=
  if h : k < 5 then ⟨(t k, tits k), (mem_fibre θ).2 ((hθt k h).trans (θns_tits h).symm)⟩ else 1

variable {t hθt}

theorem tauD_coe {k : ℕ} (hk : k < 5) : (tauD θ t hθt k : G × Mns) = (t k, tits k) := by
  unfold tauD
  rw [dif_pos hk]

theorem tauD_mul_coe {k l : ℕ} (hk : k < 5) (hl : l < 5) :
    ((tauD θ t hθt k * tauD θ t hθt l : fibre θ) : G × Mns) = (t k * t l, tits k * tits l) := by
  rw [Subgroup.coe_mul, tauD_coe θ hk, tauD_coe θ hl, Prod.mk_mul_mk]

theorem tauD_mul_mul_coe {k l : ℕ} (hk : k < 5) (hl : l < 5) :
    ((tauD θ t hθt k * tauD θ t hθt l * tauD θ t hθt k : fibre θ) : G × Mns) =
      (t k * t l * t k, tits k * tits l * tits k) := by
  rw [Subgroup.coe_mul, tauD_mul_coe θ hk hl, tauD_coe θ hk, Prod.mk_mul_mk]

theorem exists_subgroup
    (hconj : ∀ (g : G) (v : Multiplicative (altHeart 6)), g * (ψ v : G) * g⁻¹ =
      (ψ (Multiplicative.ofAdd (altAct (θ g) v.toAdd)) : G))
    (hsq : ∀ (k : ℕ) (hk : k < 5), t k * t k = (ψ (Multiplicative.ofAdd
      ((pairEW ⟨k, by omega⟩ ⟨k + 1, by omega⟩ : evenWeight 6) : altHeart 6)) : G))
    (hbraid : ∀ k, k + 1 < 5 → t k * t (k + 1) * t k = t (k + 1) * t k * t (k + 1))
    (hcomm : ∀ k l, k + 2 ≤ l → l < 5 → t k * t l = t l * t k) :
    ∃ E : Subgroup (fibre θ), Nat.card E ≤ 11520 ∧ (∀ v, deltaHom θ ψ v ∈ E) ∧
      ∀ k (hk : k < 5), tauD θ t hθt k ∈ E := by
  haveI := delta_normal θ hconj
  set Δ := (deltaHom θ ψ).range with hΔ
  have hx : IsCoxeterA 5 (fun k => (QuotientGroup.mk (tauD θ t hθt k) : fibre θ ⧸ Δ)) := by
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i j hij hj => ?_⟩
    · rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
      refine ⟨Multiplicative.ofAdd
        ((pairEW ⟨i, by omega⟩ ⟨i + 1, by omega⟩ : evenWeight 6) : altHeart 6), ?_⟩
      refine fibre_ext θ ?_ ?_
      · rw [tauD_mul_coe θ hi hi]
        exact (hsq i hi).symm
      · rw [tauD_mul_coe θ hi hi]
        exact (tits_sq hi).symm
    · rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_mul]
      congr 1
      refine fibre_ext θ ?_ ?_
      · rw [tauD_mul_mul_coe θ (by omega) hi, tauD_mul_mul_coe θ hi (by omega)]
        exact hbraid i hi
      · rw [tauD_mul_mul_coe θ (by omega) hi, tauD_mul_mul_coe θ hi (by omega)]
        exact tits_braid hi
    · rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      refine fibre_ext θ ?_ ?_
      · rw [tauD_mul_coe θ (by omega) hj, tauD_mul_coe θ hj (by omega)]
        exact hcomm i j hij hj
      · rw [tauD_mul_coe θ (by omega) hj, tauD_mul_coe θ hj (by omega)]
        exact tits_comm hij hj
  obtain ⟨h, hh⟩ := exists_hom_perm 5 _ hx
  refine ⟨h.range.comap (QuotientGroup.mk' Δ), ?_, ?_, ?_⟩
  · set E := h.range.comap (QuotientGroup.mk' Δ)
    let φ : E →* fibre θ ⧸ Δ := (QuotientGroup.mk' Δ).comp E.subtype
    have hV : Finite (Multiplicative (altHeart 6)) :=
      Nat.finite_of_card_ne_zero (by rw [card_heart]; norm_num)
    have hΔc : Nat.card Δ ≤ 16 := by
      rw [← card_heart]
      exact Nat.card_le_card_of_surjective _ (deltaHom θ ψ).rangeRestrict_surjective
    have hΔf : Finite Δ := Finite.of_surjective _ (deltaHom θ ψ).rangeRestrict_surjective
    have hker : Nat.card φ.ker ≤ 16 := by
      refine le_trans (Nat.card_le_card_of_injective
        (fun e : φ.ker => (⟨e.1.1, (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 e.2)⟩ : Δ))
        ?_) hΔc
      intro e1 e2 he
      have h' := Subtype.ext_iff.1 he
      exact Subtype.ext (Subtype.ext h')
    have hrange : Nat.card φ.range ≤ 720 := by
      haveI : Finite h.range := Finite.of_surjective _ h.rangeRestrict_surjective
      have hle : φ.range ≤ h.range := by
        rintro _ ⟨e, rfl⟩
        exact e.2
      calc Nat.card φ.range ≤ Nat.card h.range := Subgroup.card_le_of_le hle
        _ ≤ Nat.card (Perm (Fin 6)) :=
            Nat.card_le_card_of_surjective _ h.rangeRestrict_surjective
        _ = 720 := by
            rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; rfl
    rw [← Subgroup.card_ker_mul_card_range φ]
    calc Nat.card φ.ker * Nat.card φ.range ≤ 16 * 720 := Nat.mul_le_mul hker hrange
      _ = 11520 := by norm_num
  · intro v
    rw [Subgroup.mem_comap]
    have : QuotientGroup.mk' Δ (deltaHom θ ψ v) = 1 :=
      (QuotientGroup.eq_one_iff _).2 ⟨v, rfl⟩
    rw [this]
    exact h.range.one_mem
  · intro k hk
    rw [Subgroup.mem_comap]
    exact ⟨adjSwap 5 k, hh k hk⟩

end Fibre

end Recognition

open Recognition in
theorem exists_mulEquiv_Mns_tits {G : Type*} [Group G] (θ : G →* Perm (Fin 6))
    (hθ : Function.Surjective θ) (ψ : Multiplicative (altHeart 6) ≃* θ.ker)
    (hconj : ∀ (g : G) (v : Multiplicative (altHeart 6)), g * (ψ v : G) * g⁻¹ =
      (ψ (Multiplicative.ofAdd (altAct (θ g) v.toAdd)) : G))
    (t : ℕ → G) (hθt : ∀ k < 5, θ (t k) = adjSwap 5 k)
    (hsq : ∀ (k : ℕ) (hk : k < 5), t k * t k = (ψ (Multiplicative.ofAdd
      ((pairEW ⟨k, by omega⟩ ⟨k + 1, by omega⟩ : evenWeight 6) : altHeart 6)) : G))
    (hbraid : ∀ k, k + 1 < 5 → t k * t (k + 1) * t k = t (k + 1) * t k * t (k + 1))
    (hcomm : ∀ k l, k + 2 ≤ l → l < 5 → t k * t l = t l * t k) :
    ∃ e : Mns ≃* G, (∀ v, e (ψns v : Mns) = (ψ v : G)) ∧ (∀ m, θ (e m) = θns m) ∧
      ∀ k < 5, e (tits k) = t k := by
  obtain ⟨E, hE, hδ, hτ⟩ := exists_subgroup θ hconj hsq hbraid hcomm (hθt := hθt)
  have hcG : Nat.card G = 11520 := card_eq_of_ker θ hθ ψ
  have hcM : Nat.card Mns = 11520 := card_Mns
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hcG]; norm_num)
  haveI : Finite Mns := Nat.finite_of_card_ne_zero (by rw [hcM]; norm_num)
  let pG : E →* G := (MonoidHom.fst G Mns).comp ((fibre θ).subtype.comp E.subtype)
  let pM : E →* Mns := (MonoidHom.snd G Mns).comp ((fibre θ).subtype.comp E.subtype)
  have sG : Function.Surjective pG := by
    refine MonoidHom.range_eq_top.1 (eq_top_of_ker_le θ t hθt pG.range ?_ ?_)
    · intro g hg
      refine ⟨⟨deltaHom θ ψ (ψ.symm ⟨g, hg⟩), hδ _⟩, ?_⟩
      show ((ψ (ψ.symm ⟨g, hg⟩) : θ.ker) : G) = g
      rw [ψ.apply_symm_apply]
    · intro k hk
      refine ⟨⟨tauD θ t hθt k, hτ k hk⟩, ?_⟩
      show (tauD θ t hθt k : G × Mns).1 = t k
      rw [tauD_coe θ hk]
  have sM : Function.Surjective pM := by
    refine MonoidHom.range_eq_top.1 (eq_top_of_ker_le θns tits (fun k hk => θns_tits hk) pM.range
      ?_ ?_)
    · intro m hm
      refine ⟨⟨deltaHom θ ψ (ψns.symm ⟨m, hm⟩), hδ _⟩, ?_⟩
      show ((ψns (ψns.symm ⟨m, hm⟩) : Qns) : Mns) = m
      rw [ψns.apply_symm_apply]
    · intro k hk
      refine ⟨⟨tauD θ t hθt k, hτ k hk⟩, ?_⟩
      show (tauD θ t hθt k : G × Mns).2 = tits k
      rw [tauD_coe θ hk]
  have bG : Function.Bijective pG := sG.bijective_of_nat_card_le (by rw [hcG]; exact hE)
  have bM : Function.Bijective pM := sM.bijective_of_nat_card_le (by rw [hcM]; exact hE)
  let eG := MulEquiv.ofBijective pG bG
  let eM := MulEquiv.ofBijective pM bM
  have key : ∀ ε : E, (eM.symm.trans eG) (pM ε) = pG ε := fun ε => by
    show eG (eM.symm (eM ε)) = pG ε
    rw [eM.symm_apply_apply]
    rfl
  refine ⟨eM.symm.trans eG, fun v => key ⟨deltaHom θ ψ v, hδ v⟩, fun m => ?_, fun k hk => ?_⟩
  · obtain ⟨ε, rfl⟩ := sM m
    rw [key ε]
    exact ε.1.2
  · have h1 : pM ⟨tauD θ t hθt k, hτ k hk⟩ = tits k := by
      show (tauD θ t hθt k : G × Mns).2 = tits k
      rw [tauD_coe θ hk]
    have h2 : pG ⟨tauD θ t hθt k, hτ k hk⟩ = t k := by
      show (tauD θ t hθt k : G × Mns).1 = t k
      rw [tauD_coe θ hk]
    rw [← h1, key, h2]

theorem exists_mulEquiv_Mns {G : Type*} [Group G] (θ : G →* Perm (Fin 6))
    (hθ : Function.Surjective θ) (ψ : Multiplicative (altHeart 6) ≃* θ.ker)
    (hconj : ∀ (g : G) (v : Multiplicative (altHeart 6)), g * (ψ v : G) * g⁻¹ =
      (ψ (Multiplicative.ofAdd (altAct (θ g) v.toAdd)) : G))
    (t : ℕ → G) (hθt : ∀ k < 5, θ (t k) = adjSwap 5 k)
    (hsq : ∀ (k : ℕ) (hk : k < 5), t k * t k = (ψ (Multiplicative.ofAdd
      ((pairEW ⟨k, by omega⟩ ⟨k + 1, by omega⟩ : evenWeight 6) : altHeart 6)) : G))
    (hbraid : ∀ k, k + 1 < 5 → t k * t (k + 1) * t k = t (k + 1) * t k * t (k + 1))
    (hcomm : ∀ k l, k + 2 ≤ l → l < 5 → t k * t l = t l * t k) :
    ∃ e : Mns ≃* G, (∀ v, e (ψns v : Mns) = (ψ v : G)) ∧ ∀ m, θ (e m) = θns m := by
  obtain ⟨e, h1, h2, -⟩ := exists_mulEquiv_Mns_tits θ hθ ψ hconj t hθt hsq hbraid hcomm
  exact ⟨e, h1, h2⟩

end CFSG.CGT.Stroth77
