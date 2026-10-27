module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.TwE6Setup
public import CFSG.HardMathSupport.Malle.E27Lie.ExcTwisted.SylowN

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Timmesfeld.ExceptionalOrders
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross (mactC)
open CFSG.HardMathSupport.Malle.E27Lie (card_graphFixedRootGroup_E6 padicValNat_three_ordTwistedE6)

section TwE6Group

variable (K : Type) [Field K] [Finite K] (σ : K →+* K)

@[expose] def AdjE6 : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ :=
  !![4, 3, 5, 6, 4, 2; 3, 6, 6, 9, 6, 3; 5, 6, 10, 12, 8, 4; 6, 9, 12, 18, 12, 6;
    4, 6, 8, 12, 10, 5; 2, 3, 4, 6, 5, 4]

theorem cartan_mul_AdjE6 : Tag.E6.cartan * AdjE6 = (3 : ℤ) • 1 := by decide +kernel

theorem zpowMatrix_smul_one' {G : Type*} [CommGroup G] {n : ℕ} (c : ℤ) (t : Fin n → G) :
    zpowMatrix (c • (1 : Matrix (Fin n) (Fin n) ℤ)) t = t ^ c := by
  funext j
  rw [zpowMatrix_apply, Pi.pow_apply,
    Finset.prod_eq_single j (fun i _ hij => by
      simp [Matrix.smul_apply, Matrix.one_apply, hij]) (fun h => absurd (Finset.mem_univ j) h)]
  simp [Matrix.smul_apply, Matrix.one_apply]

theorem torusCoord_ker_cube (x : Fin Tag.E6.rank → Kˣ)
    (hx : torusCoordHom Tag.E6 K x = 1) : x ^ 3 = 1 := by
  have h := (torusCoordHom_eq_one_iff (τ := Tag.E6) (K := K) x).1 hx
  have hA := cartan_mul_AdjE6
  have h1 : zpowMatrix ((3 : ℤ) • (1 : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ)) x =
      x ^ (3 : ℤ) := zpowMatrix_smul_one' 3 x
  have h2 : zpowMatrix ((3 : ℤ) • (1 : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ)) x =
      zpowMatrix AdjE6 (zpowMatrix Tag.E6.cartan x) := by
    rw [zpowMatrix_zpowMatrix, hA]
  rw [h, map_one] at h2
  have h3 : x ^ (3 : ℤ) = x ^ 3 := by norm_cast
  rw [← h3, ← h1, h2]

@[expose] def compatE : Subgroup (Fin Tag.E6.rank → Kˣ) := compatSubgroup (t := TwistTag.E6) σ

theorem mem_compatE {c : Fin Tag.E6.rank → Kˣ} :
    c ∈ compatE K σ ↔ ∀ i, c (TwistTag.E6.perm i) = Units.map σ.toMonoidHom (c i) := Iff.rfl

theorem Z0_pm {z : ↥(monomialSub Tag.E6 K)} (hz : z ∈ Z0 Tag.E6 K) :
    ∃ e : Fin Tag.E6.rank → Kˣ, (∀ i, e i * e i = 1) ∧ torusN Tag.E6 K e = z := by
  induction hz using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    refine ⟨Pi.mulSingle i (-1), fun j => ?_, (weylRep_sq_eq_torusN Tag.E6 i).symm⟩
    by_cases hj : j = i
    · subst hj
      rw [Pi.mulSingle_eq_same, neg_mul_neg, one_mul]
    · rw [Pi.mulSingle_eq_of_ne hj, one_mul]
  | one => exact ⟨1, fun i => one_mul 1, map_one _⟩
  | mul a b _ _ ha hb =>
    obtain ⟨e, he, rfl⟩ := ha
    obtain ⟨e', he', rfl⟩ := hb
    refine ⟨e * e', ?_, ?_⟩
    · intro i
      calc (e * e') i * (e * e') i = (e i * e i) * (e' i * e' i) := by
            simp only [Pi.mul_apply]; exact mul_mul_mul_comm _ _ _ _
        _ = 1 := by rw [he, he', one_mul]
    · rw [map_mul]
  | inv a _ ha =>
    obtain ⟨e, he, rfl⟩ := ha
    refine ⟨e⁻¹, ?_, ?_⟩
    · intro i
      simp only [Pi.inv_apply]
      rw [← mul_inv, he, inv_one]
    · rw [map_inv]

theorem sigma_pm {σ : K →+* K} {e : Kˣ} (he : e * e = 1) : Units.map σ.toMonoidHom e = e := by
  have h1 : (e : K) * e = 1 := by
    have := congrArg (fun u : Kˣ => (u : K)) he
    simpa using this
  rcases mul_self_eq_one_iff.1 h1 with h | h
  · refine Units.ext ?_
    simp [h]
  · refine Units.ext ?_
    simp [h]

theorem exists_compat_of_psi1_eq_one {g : ↥(N1 K σ)} (hg : psi1 K σ g = 1) :
    ∃ c ∈ compatE K σ,
      (torusCoordHom Tag.E6 K c : ModGL Tag.E6 K) = (g : ModGL Tag.E6 K) := by
  have hsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  have hmem : (g : ModGL Tag.E6 K) ∈ graphFixedRootTorus TwistTag.E6 K σ := by
    have h0 : g ∈ (graphFixedRootWeylHom TwistTag.E6 K σ).ker := hg
    rw [graphFixedRootWeylHom_ker] at h0
    exact h0
  rw [graphFixedRootTorus_eq_compatTorus hsurj] at hmem
  obtain ⟨c, hc, hcg⟩ := (mem_compatTorus σ).1 hmem
  exact ⟨c, hc, hcg⟩

theorem hrep : ∀ k : Fin 6, repE (oi k) = k ∨ repE (oi k) = TwistTag.E6.perm k := by
  intro k
  fin_cases k <;> first | exact Or.inl rfl | exact Or.inr rfl

theorem mem_range_iota0_of_Z0 {q : ℕ} (hq : 1 < q) (hσ : ∀ c, σ c = c ^ q) {g : ↥(N1 K σ)}
    (hg : jHom K σ g ∈ Z0 Tag.E6 K) : g ∈ (iota0 K σ hq hσ).range := by
  have hψ : psi1 K σ g = 1 := by
    rw [← psi1_eq]
    exact MonoidHom.mem_ker.1 (Z0_le_ker Tag.E6 K hg)
  obtain ⟨e, he, hez⟩ := Z0_pm K hg
  obtain ⟨c, hc, hcg⟩ := exists_compat_of_psi1_eq_one K σ hψ
  have h0 : (torusCoordHom Tag.E6 K e : ModGL Tag.E6 K) = (g : ModGL Tag.E6 K) := by
    have := congrArg (monoι Tag.E6 K) hez
    rw [monoι_torusN, jHom_coe] at this
    exact this
  have h1 : torusCoordHom Tag.E6 K e = torusCoordHom Tag.E6 K c :=
    Subtype.ext (h0.trans hcg.symm)
  have h2 : torusCoordHom Tag.E6 K (e * c⁻¹) = 1 := by
    rw [map_mul, map_inv, h1, mul_inv_cancel]
  have h3 := torusCoord_ker_cube K (e * c⁻¹) h2
  have h4 : e ^ 3 = e := by
    funext i
    simp only [Pi.pow_apply]
    rw [pow_succ, sq]
    exact (by rw [he i, one_mul] : e i * e i * e i = e i)
  have h5 : e = c ^ 3 := by
    rw [mul_pow, inv_pow, h4] at h3
    exact mul_inv_eq_one.1 h3
  have hecompat : e ∈ compatE K σ := by
    rw [h5]; exact pow_mem hc 3
  have hfix : ∀ i, e (TwistTag.E6.perm i) = e i := fun i => by
    have := (mem_compatE K σ).1 hecompat i
    rw [this, sigma_pm K (he i)]
  have hmemCq : ∀ i, e i ∈ Cq K q := fun i => by
    have h6 : Units.map σ.toMonoidHom (e i) = e i := sigma_pm K (he i)
    have h7 : e i ^ q = e i := by
      refine Units.ext ?_
      have := congrArg (fun u : Kˣ => (u : K)) h6
      simp only [Units.coe_map] at this
      show (e i : K) ^ q = e i
      rw [← hσ]
      exact this
    have h8 : e i ^ (q - 1) * e i = e i := by
      rw [← pow_succ, Nat.sub_add_cancel hq.le, h7]
    show e i ^ (q - 1) = 1
    exact mul_eq_right.1 h8
  let e' : Fin 4 → ↥(Cq K q) := fun a => ⟨e (repE a), hmemCq _⟩
  have hunf : unfoldE K q e' = e := by
    funext k
    show e (repE (oi k)) = e k
    rcases hrep k with h | h
    · rw [h]
    · rw [h]; exact hfix k
  refine ⟨e', ?_⟩
  apply Subtype.ext
  show (torusCoordHom Tag.E6 K (unfoldE K q e') : ModGL Tag.E6 K) = (g : ModGL Tag.E6 K)
  rw [hunf]
  exact h0

@[expose] noncomputable def torusT {q : ℕ} (hq : 1 < q) (hσ : ∀ c, σ c = c ^ q) :
    Subgroup ↥(N1 K σ) := (iota0 K σ hq hσ).range

theorem torusT_normal {q : ℕ} (hq : 1 < q) (hσ : ∀ c, σ c = c ^ q) :
    (torusT K σ hq hσ).Normal := ⟨by
  rintro _ ⟨t, rfl⟩ g
  rw [conj_iota0 K σ hq hσ g t]
  exact ⟨_, rfl⟩⟩

@[expose] noncomputable def What1 : Subgroup ↥(N1 K σ) := (What Tag.E6 K).comap (jHom K σ)

@[expose] noncomputable def Z1 : Subgroup ↥(N1 K σ) := (Z0 Tag.E6 K).comap (jHom K σ)

theorem Z1_le_torusT {q : ℕ} (hq : 1 < q) (hσ : ∀ c, σ c = c ^ q) :
    Z1 K σ ≤ torusT K σ hq hσ := fun _ hg => mem_range_iota0_of_Z0 K σ hq hσ hg

theorem psi1_of_What1_ker {w : ↥(N1 K σ)} (hw : w ∈ What1 K σ) (h : psi1 K σ w = 1) :
    w ∈ Z1 K σ := by
  have h1 : monomialSubHom (τ := Tag.E6) (K := K) (jHom K σ w) = 1 := by
    rw [psi1_eq]; exact h
  exact What_ker_le_Z0 Tag.E6 K hw h1

theorem mem_torusT_of_mem_sup {q : ℕ} (hq : 1 < q) (hσ : ∀ c, σ c = c ^ q) {g : ↥(N1 K σ)}
    (hg : g ∈ torusT K σ hq hσ ⊔ What1 K σ) (hψ : psi1 K σ g = 1) : g ∈ torusT K σ hq hσ := by
  haveI := torusT_normal K σ hq hσ
  obtain ⟨t, ht, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hg
  obtain ⟨t', rfl⟩ := ht
  have hw1 : psi1 K σ w = 1 := by
    rw [map_mul, psi1_iota0, one_mul] at hψ
    exact hψ
  exact mul_mem ⟨t', rfl⟩ (Z1_le_torusT K σ hq hσ (psi1_of_What1_ker K σ hw hw1))

theorem What_map_eq : (What Tag.E6 K).map (monoι Tag.E6 K) =
    Subgroup.closure (Set.range fun i : Fin Tag.E6.rank => weylElt Tag.E6 K i 1) := by
  rw [What, MonoidHom.map_closure, ← Set.range_comp]
  congr 1

theorem mem_What_of_closure {x : ↥(monomialSub Tag.E6 K)}
    (h : monoι Tag.E6 K x ∈
      Subgroup.closure (Set.range fun i : Fin Tag.E6.rank => weylElt Tag.E6 K i 1)) :
    x ∈ What Tag.E6 K := by
  rw [← What_map_eq] at h
  have := (Subgroup.comap_map_eq_self_of_injective (monoι_injective Tag.E6 K) (What Tag.E6 K))
  rw [← this]
  exact h

theorem exists_What1_lift {w : WeylGroup TwistTag.E6.tag} (hw : w ∈ relWeylTwist TwistTag.E6) :
    ∃ g ∈ What1 K σ, psi1 K σ g = w := by
  refine ⟨⟨_, canonicalRep_mem_graphFixedRootMonomial TwistTag.E6 K σ hw⟩, ?_,
    graphFixedRootWeylHom_canonicalRep TwistTag.E6 K σ hw⟩
  show jHom K σ ⟨_, canonicalRep_mem_graphFixedRootMonomial TwistTag.E6 K σ hw⟩ ∈ What Tag.E6 K
  apply mem_What_of_closure
  exact canonicalRep_mem_closure (cs := coxeterSystem Tag.E6) K w

theorem jHom_injective : Function.Injective (jHom K σ) := fun a b h =>
  Subtype.ext (congrArg (fun x : ↥(monomialSub Tag.E6 K) => ((x : ↥(adjointGroup Tag.E6 K)) :
    ModGL Tag.E6 K)) h)

theorem card_relWeylTwist : Nat.card (relWeylTwist TwistTag.E6) = 1152 :=
  (Nat.card_congr (foldedWeylEquiv TwistTag.E6).toEquiv).trans
    CFSG.RankThree.PartOne.K133H.card_weylGroup_F4

theorem card_torusT {q : ℕ} (hq : 1 < q) (hσ : ∀ c, σ c = c ^ q) (hK : Nat.card K = q ^ 2) :
    Nat.card (torusT K σ hq hσ) = (q - 1) ^ 4 := by
  rw [torusT, ← Nat.card_congr (MonoidHom.ofInjective (iota0_injective K σ hq hσ)).toEquiv,
    Nat.card_pi, Finset.prod_const, card_Cq K hq hK]
  simp

theorem card_G {q : ℕ} (hq : 1 < q) (hσ : ∀ c, σ c = c ^ q) (hK : Nat.card K = q ^ 2) :
    Nat.card ↥(torusT K σ hq hσ ⊔ What1 K σ) = (q - 1) ^ 4 * 1152 := by
  rw [card_eq_card_inf_ker_mul_card_map (psi1 K σ) (torusT K σ hq hσ ⊔ What1 K σ)]
  have h1 : (torusT K σ hq hσ ⊔ What1 K σ) ⊓ (psi1 K σ).ker = torusT K σ hq hσ := by
    refine le_antisymm (fun g hg => ?_) (fun g hg => ⟨Subgroup.mem_sup_left hg, ?_⟩)
    · exact mem_torusT_of_mem_sup K σ hq hσ hg.1 hg.2
    · obtain ⟨t, rfl⟩ := hg
      exact psi1_iota0 K σ hq hσ t
  have h2 : (torusT K σ hq hσ ⊔ What1 K σ).map (psi1 K σ) = relWeylTwist TwistTag.E6 := by
    ext w
    constructor
    · rintro ⟨g, -, rfl⟩
      exact psi1_mem K σ g
    · intro hw
      obtain ⟨g, hg, hgw⟩ := exists_What1_lift K σ hw
      exact ⟨g, Subgroup.mem_sup_right hg, hgw⟩
  rw [h1, h2, card_torusT K σ hq hσ hK]
  exact congrArg _ card_relWeylTwist

theorem exists_sylow_le_G {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hq3 : (ℓ ^ f) % 3 = 1) :
    ∃ P : Sylow 3 ↥(graphFixedRootGroup TwistTag.E6 K σ),
      (P : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ)) ≤
        (torusT K σ (Nat.one_lt_pow (by omega) hℓ.one_lt) hσ ⊔ What1 K σ).map
          (Subgroup.inclusion (graphFixedRootMonomial_le TwistTag.E6 K σ)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : 1 < ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  have h3 : 3 ∣ ℓ ^ f - 1 := by omega
  refine exists_sylow_three_le_of_factorization_eq _ ?_
  have hmap : Nat.card ↥((torusT K σ hq hσ ⊔ What1 K σ).map
      (Subgroup.inclusion (graphFixedRootMonomial_le TwistTag.E6 K σ))) =
      Nat.card ↥(torusT K σ hq hσ ⊔ What1 K σ) :=
    Subgroup.card_map_of_injective (Subgroup.inclusion_injective _)
  rw [Nat.factorization_def _ Nat.prime_three, Nat.factorization_def _ Nat.prime_three, hmap,
    card_G K σ hq hσ hK, card_graphFixedRootGroup_E6 hℓ hf hK σ hσ,
    padicValNat_three_ordTwistedE6 hq hq3]
  have hz1 : ℓ ^ f - 1 ≠ 0 := by omega
  have e1152 : padicValNat 3 1152 = 2 := by
    rw [show (1152 : ℕ) = 3 ^ 2 * 128 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
  rw [padicValNat.mul (pow_ne_zero 4 hz1) (by norm_num), e1152, padicValNat.pow (ℓ ^ f - 1) 4]

end TwE6Group

end CFSG.HardMathSupport.Curtis.UnitaryLevi

end
