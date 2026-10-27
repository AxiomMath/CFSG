module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.Blocks
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.TwistedABlocks

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb

open CFSG.Open CFSG.AGLEmbedding.LieOut
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus

section Central

variable {S G : Type*} [Group S] [Group G]

private theorem eq_one_of_mem_ker_of_pow_eq_one [Finite S] {p : ℕ} (hp : p.Prime) (π : S →* G)
    (hpk : ¬ p ∣ Nat.card π.ker) {s : S} (hs : π s = 1) (hsp : s ^ p = 1) : s = 1 := by
  set z : π.ker := ⟨s, hs⟩
  have hz : z ^ p = 1 := Subtype.ext hsp
  rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hz) with h | h
  · exact congrArg Subtype.val (orderOf_eq_one_iff.1 h)
  · exact absurd (h ▸ orderOf_dvd_natCard z) hpk

private theorem ker_subgroupMap_le_center (π : S →* G) (hker : π.ker ≤ Subgroup.center S)
    (D : Subgroup S) : (π.subgroupMap D).ker ≤ Subgroup.center ↥D := by
  intro d hd
  have h1 : π (d : S) = 1 := congrArg Subtype.val hd
  have h2 : (d : S) ∈ Subgroup.center S := hker h1
  rw [Subgroup.mem_center_iff]
  intro y
  exact Subtype.ext (Subgroup.mem_center_iff.1 h2 y)

private theorem isQuasisimple_map_of_ker_le_center (π : S →* G) (hker : π.ker ≤ Subgroup.center S)
    {D : Subgroup S} (hD : CFSG.IsQuasisimple ↥D) : CFSG.IsQuasisimple ↥(D.map π) :=
  CFSG.LocalCores.isQuasisimple_of_surjective hD (π.subgroupMap D)
    (MonoidHom.subgroupMap_surjective π D) (ker_subgroupMap_le_center π hker D)

private noncomputable def centerQuotEquiv {P Q : Type*} [Group P] [Group Q] (hP : Group.IsPerfect P)
    (f : P →* Q) (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center P) :
    P ⧸ Subgroup.center P ≃* Q ⧸ Subgroup.center Q :=
  (QuotientGroup.quotientMulEquivOfEq (by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk',
      CFSG.LocalCores.comap_center_eq_of_perfect hP f hf hker])).trans
    (QuotientGroup.quotientKerEquivOfSurjective ((QuotientGroup.mk' (Subgroup.center Q)).comp f)
      ((QuotientGroup.mk'_surjective _).comp hf))

private theorem noAp_map_of_ker_le_center {S G : Type} [Group S] [Group G] {p : ℕ} (π : S →* G)
    (hker : π.ker ≤ Subgroup.center S) {D : Subgroup S} (hD : CFSG.IsQuasisimple ↥D)
    (h : NoAp p (↥D ⧸ Subgroup.center ↥D)) :
    NoAp p (↥(D.map π) ⧸ Subgroup.center ↥(D.map π)) :=
  NoAp.of_mulEquiv (centerQuotEquiv hD.1 (π.subgroupMap D) (MonoidHom.subgroupMap_surjective π D)
    (ker_subgroupMap_le_center π hker D)) h

private theorem isCyclic_of_injective_of_not_sq_dvd {Q H : Type*} [Group Q] [Group H] [Finite H] {p : ℕ}
    (hp : p.Prime) (hQ : IsPGroup p Q) (f : Q →* H) (hf : Function.Injective f)
    (h : ¬ p ^ 2 ∣ Nat.card H) : IsCyclic Q := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite Q := Finite.of_injective f hf
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have hdvd : Nat.card Q ∣ Nat.card H := by
    have h1 := Subgroup.card_dvd_of_le (le_top : f.range ≤ ⊤)
    rw [Nat.card_congr (MonoidHom.ofInjective hf).toEquiv.symm, Subgroup.card_top] at h1
    exact h1
  have hn1 : n ≤ 1 := by
    by_contra hlt
    apply h
    have h1 : p ^ 2 ∣ p ^ n := pow_dvd_pow p (by omega)
    exact h1.trans (hn ▸ hdvd)
  interval_cases n
  · have : Subsingleton Q := by
      rw [← Finite.card_le_one_iff_subsingleton]
      simp [hn]
    infer_instance
  · exact isCyclic_of_prime_card (by simpa using hn)

end Central

section Blocks

variable {S G : Type} [Group S] [Finite S] [Group G] [Finite G] {p : ℕ}

omit [Finite G] in
private theorem dvd_card_map_of_ne_bot (hp : p.Prime) (π : S →* G) (hpk : ¬ p ∣ Nat.card π.ker)
    {D : Subgroup S} (Q : Subgroup ↥D) (hQ : ∀ q ∈ Q, q ^ p = 1) (h : Q ≠ ⊥) :
    p ∣ Nat.card D ∧ p ∣ Nat.card (D.map π) := by
  obtain ⟨q, hqQ, hq1⟩ : ∃ q ∈ Q, q ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact h ((Subgroup.eq_bot_iff_forall Q).2 hcon)
  have hqp : q ^ p = 1 := hQ q hqQ
  have hord : orderOf q = p := by
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hqp) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.1 h1) hq1
    · exact h1
  refine ⟨hord ▸ orderOf_dvd_natCard q, ?_⟩
  set x : ↥(D.map π) := π.subgroupMap D q with hx
  have hxp : x ^ p = 1 := by rw [hx, ← map_pow, hqp, map_one]
  have hx1 : x ≠ 1 := by
    intro h1
    have h2 : π (q : S) = 1 := congrArg Subtype.val h1
    exact hq1 (Subtype.ext (eq_one_of_mem_ker_of_pow_eq_one hp π hpk h2 (congrArg Subtype.val hqp)))
  have hxo : orderOf x = p := by
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hxp) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.1 h1) hx1
    · exact h1
  exact hxo ▸ orderOf_dvd_natCard x

private theorem isCyclic_of_exponent_block (hp : p.Prime) (π : S →* G) (hker : π.ker ≤ Subgroup.center S)
    (hpk : ¬ p ∣ Nat.card π.ker) {Jb : Subgroup G}
    (hA1 : ∀ X : Subgroup G, X ≤ Jb → CFSG.Open.IsQuasisimple ↥X → ¬ p ^ 2 ∣ Nat.card X)
    {D : Subgroup S} (hDJ : D.map π ≤ Jb)
    (hact : p ∣ Nat.card D → CFSG.IsQuasisimple ↥D) (Q : Subgroup ↥D) (hQ : ∀ q ∈ Q, q ^ p = 1) :
    IsCyclic ↥Q := by
  by_cases hpD : p ∣ Nat.card D
  · have hq := isQuasisimple_map_of_ker_le_center π hker (hact hpD)
    have hX := hA1 (D.map π) hDJ ⟨hq.1.commutator_eq_top, hq.2.1⟩
    refine isCyclic_of_injective_of_not_sq_dvd hp (isPGroup_of_pow_eq_one hQ)
      ((π.subgroupMap D).comp Q.subtype) ?_ hX
    rw [injective_iff_map_eq_one]
    intro q hq1
    have h2 : π ((q : ↥D) : S) = 1 := congrArg Subtype.val hq1
    exact Subtype.ext (Subtype.ext
      (eq_one_of_mem_ker_of_pow_eq_one hp π hpk h2 (congrArg Subtype.val (hQ q q.2))))
  · have hbot : Q = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro q hqQ
      have h1 : q ^ p = 1 := hQ q hqQ
      rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one h1) with h | h
      · exact orderOf_eq_one_iff.1 h
      · exact absurd (h ▸ orderOf_dvd_natCard q) hpD
    rw [hbot]
    infer_instance

theorem false_of_blocks (hp : p.Prime) (π : S →* G) (hker : π.ker ≤ Subgroup.center S)
    (hpk : ¬ p ∣ Nat.card π.ker) (Jb : Subgroup G)
    (hA1 : ∀ X : Subgroup G, X ≤ Jb → CFSG.Open.IsQuasisimple ↥X → ¬ p ^ 2 ∣ Nat.card X)
    (hA2 : ∀ X₁ X₂ : Subgroup G, X₁ ≤ Jb → X₂ ≤ Jb → CFSG.Open.IsQuasisimple ↥X₁ →
      CFSG.Open.IsQuasisimple ↥X₂ → X₂ ≤ Subgroup.centralizer (X₁ : Set G) →
      p ∣ Nat.card X₁ → p ∣ Nat.card X₂ → NoAp p (↥X₁ ⧸ Subgroup.center ↥X₁) →
      NoAp p (↥X₂ ⧸ Subgroup.center ↥X₂) → False)
    (t : S) (hfix : ∀ g : G, g * π t = π t * g → g ∈ Jb)
    {ι : Type} [Finite ι] (D : ι → Subgroup S)
    (hcomm : ∀ i j, i ≠ j → ∀ a ∈ D i, ∀ b ∈ D j, Commute a b) (hind : iSupIndep D)
    (hDt : ∀ i, D i ≤ Subgroup.centralizer ({t} : Set S))
    (hact : ∀ i, p ∣ Nat.card (D i) →
      CFSG.IsQuasisimple ↥(D i) ∧ NoAp p (↥(D i) ⧸ Subgroup.center ↥(D i)))
    (E : Subgroup S) (hEp : ∀ e ∈ E, e ^ p = 1) (hEc : Nat.card E = p ^ 2)
    (hEJ : E ≤ ⨆ i, D i) : False := by
  classical
  have := Fintype.ofFinite ι
  set A : Subgroup S := ⨆ i, D i with hA
  have hDJ : ∀ i, (D i).map π ≤ Jb := by
    rintro i _ ⟨d, hd, rfl⟩
    refine hfix _ ?_
    rw [← map_mul, ← map_mul]
    exact congrArg π (Subgroup.mem_centralizer_iff.1 (hDt i hd) t rfl).symm
  let ψ : (∀ i, D i) →* S := Subgroup.noncommPiCoprod (H := D)
    (fun i j hij x y hx hy => hcomm i j hij x hx y hy)
  have hψ : Function.Injective ψ := Subgroup.injective_noncommPiCoprod_of_iSupIndep hind
  have hψr : ψ.range = A := Subgroup.noncommPiCoprod_range
  let e : (∀ i, D i) ≃* A := (MonoidHom.ofInjective hψ).trans (MulEquiv.subgroupCongr hψr)
  let B : FlagBlocks p A :=
    { ι := ι
      H := fun i => ↥(D i)
      grp := fun i => inferInstance
      ρ := fun i => (Pi.evalMonoidHom (fun i => ↥(D i)) i).comp e.symm.toMonoidHom
      inj_of_pow := fun a _ ha => by
        have h1 : e.symm a = 1 := funext fun i => ha i
        exact e.symm.injective (h1.trans (map_one e.symm).symm) }
  set E' : Subgroup A := E.subgroupOf A with hE'
  have hE'p : ∀ x ∈ E', x ^ p = 1 := fun x hx => Subtype.ext (hEp _ (Subgroup.mem_subgroupOf.1 hx))
  have hE'card : Nat.card E' = p ^ 2 := by
    rw [← hEc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEJ).toEquiv
  have hexp : ∀ i, ∀ q ∈ E'.map (B.ρ i), q ^ p = 1 := by
    rintro i _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE'p x hx, map_one]
  refine FlagBlocks.false_of_split B hp (E := E') hE'p (by rw [hE'card]) (fun i => ?_)
    (fun i j hij hi hj => ?_)
  · exact isCyclic_of_exponent_block hp π hker hpk hA1 (hDJ i)
      (fun h => (hact i h).1) _ (hexp i)
  · obtain ⟨hDi, hXi⟩ := dvd_card_map_of_ne_bot hp π hpk _ (hexp i) hi
    obtain ⟨hDj, hXj⟩ := dvd_card_map_of_ne_bot hp π hpk _ (hexp j) hj
    obtain ⟨hqi, hni⟩ := hact i hDi
    obtain ⟨hqj, hnj⟩ := hact j hDj
    refine hA2 ((D i).map π) ((D j).map π) (hDJ i) (hDJ j)
      (let h := isQuasisimple_map_of_ker_le_center π hker hqi; ⟨h.1.commutator_eq_top, h.2.1⟩)
      (let h := isQuasisimple_map_of_ker_le_center π hker hqj; ⟨h.1.commutator_eq_top, h.2.1⟩)
      ?_ hXi hXj (noAp_map_of_ker_le_center π hker hqi hni)
      (noAp_map_of_ker_le_center π hker hqj hnj)
    rintro _ ⟨b, hb, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg π (hcomm i j hij a ha b hb).eq

end Blocks

section Su

open CFSG.Assembly.LowTwoRank

theorem false_of_blocks_su {K : Type} [Field K] [Finite K] [CharP K 2] {n f : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) {p : ℕ} (hp57 : p = 5 ∨ p = 7)
    (hpq : ¬ p ∣ 2 ^ f + 1) {G : Type} [Group G] [Finite G] (π : StatedSU n (2 ^ f) K →* G)
    (hker : π.ker ≤ Subgroup.center (StatedSU n (2 ^ f) K)) (hpk : ¬ p ∣ Nat.card π.ker)
    (Jb : Subgroup G)
    (hA1 : ∀ X : Subgroup G, X ≤ Jb → CFSG.Open.IsQuasisimple ↥X → ¬ p ^ 2 ∣ Nat.card X)
    (hA2 : ∀ X₁ X₂ : Subgroup G, X₁ ≤ Jb → X₂ ≤ Jb → CFSG.Open.IsQuasisimple ↥X₁ →
      CFSG.Open.IsQuasisimple ↥X₂ → X₂ ≤ Subgroup.centralizer (X₁ : Set G) →
      p ∣ Nat.card X₁ → p ∣ Nat.card X₂ → NoAp p (↥X₁ ⧸ Subgroup.center ↥X₁) →
      NoAp p (↥X₂ ⧸ Subgroup.center ↥X₂) → False)
    (t : StatedSU n (2 ^ f) K)
    (hsq : Squarefree (minpoly K (Matrix.mulVecLin ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))))
    (htp : t ^ p = 1) (hfix : ∀ g : G, g * π t = π t * g → g ∈ Jb)
    (V E : Subgroup (StatedSU n (2 ^ f) K))
    (hVc : V ≤ Subgroup.centralizer ({t} : Set (StatedSU n (2 ^ f) K))) (hV : ⁅V, V⁆ = V)
    (hEV : E ≤ V) (hEp : ∀ e ∈ E, e ^ p = 1) (hEc : Nat.card E = p ^ 2) : False := by
  have hp : p.Prime := by rcases hp57 with rfl | rfl <;> norm_num
  obtain ⟨ι, hι, D, hcomm, hind, hDt, hact, hcov⟩ := exists_blocks_su hK hf t hsq hp57 hpq htp
  exact false_of_blocks hp π hker hpk Jb hA1 hA2 t hfix D hcomm hind hDt hact E hEp hEc
    (fun e he => hcov V hVc hV e (hEV he) (hEp e he))

end Su

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb
