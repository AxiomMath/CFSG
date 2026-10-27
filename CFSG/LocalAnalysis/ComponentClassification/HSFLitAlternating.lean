module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitExclusion
public import CFSG.ClassicalInvolution.SmallCases.Alternating.PairSwaps

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv
open scoped commutatorElement

theorem not_isCyclic_of_two_involutions {G : Type*} [Group G] [Finite G] {a b : G}
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : a ≠ b) : ¬ IsCyclic G := by
  intro hc
  classical
  have : Fintype G := Fintype.ofFinite G
  have h := IsCyclic.card_pow_eq_one_le (α := G) (n := 2) (by norm_num)
  have h1 : (1 : G) ≠ a := by
    intro h1; rw [← h1, orderOf_one] at ha; norm_num at ha
  have h2 : (1 : G) ≠ b := by
    intro h2; rw [← h2, orderOf_one] at hb; norm_num at hb
  have hsub : ({1, a, b} : Finset G) ⊆ Finset.univ.filter fun x : G => x ^ 2 = 1 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · simp
    · simp [← ha, pow_orderOf_eq_one]
    · simp [← hb, pow_orderOf_eq_one]
  have h3 := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp [h1, h2]), Finset.card_pair hab] at h3
  omega

theorem eq_top_of_odd_mem_of_perfect {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]
    (A : Subgroup K) [A.Normal] (hA : ∀ x : K, Odd (orderOf x) → x ∈ A) : A = ⊤ := by
  have hp : IsPGroup 2 (K ⧸ A) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    refine ⟨a, ?_⟩
    have hodd : Odd (orderOf (x ^ 2 ^ a)) := by
      rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨m, hord⟩, hord,
        Nat.mul_div_cancel_left _ (by positivity)]
      exact hm
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hA _ hodd)
  have hsolv : Group.IsSolvable (K ⧸ A) := by
    have := hp.isNilpotent
    infer_instance
  have hperf : Group.IsPerfect (K ⧸ A) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' A) (QuotientGroup.mk'_surjective A)
  by_contra hne
  obtain ⟨x, hx⟩ : ∃ x : K, x ∉ A := by
    by_contra h
    push Not at h
    exact hne (eq_top_iff.mpr fun x _ => h x)
  have hnt : Nontrivial (K ⧸ A) :=
    ⟨⟨QuotientGroup.mk x, 1, fun h => hx ((QuotientGroup.eq_one_iff x).mp h)⟩⟩
  have := Group.IsSolvable.commutator_lt_top_of_nontrivial (K ⧸ A)
  rw [hperf.commutator_eq_top] at this
  exact lt_irrefl _ this

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X}

theorem Config.false_of_mulEquiv_alternating {n : ℕ} (e : X ≃* alternatingGroup (Fin n))
    (h : Config t L) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ : X →* Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp e.toMonoidHom with hφ
  have hφinj : Function.Injective φ :=
    (subtype_injective _).comp e.injective
  have hφrange : ∀ u : Perm (Fin n), u ∈ alternatingGroup (Fin n) → ∃ x, φ x = u := by
    intro u hu
    exact ⟨e.symm ⟨u, hu⟩, by simp [hφ]⟩
  set σ : Perm (Fin n) := φ t with hσdef
  have ht2 : t * t = 1 := by rw [← sq, ← h.orderOf_eq, pow_orderOf_eq_one]
  have hσ : σ * σ = 1 := by rw [hσdef, ← map_mul, ht2, map_one]
  have hcommφ : ∀ x : X, x ∈ centralizer ({t} : Set X) → φ x * σ = σ * φ x := by
    intro x hx
    rw [hσdef, ← map_mul, ← map_mul, (mem_centralizer_singleton_iff.mp hx)]
  set Q : Subgroup X := (ClassicalInvolution.pairSwaps σ hσ).comap φ with hQ
  have hQC : Q ≤ centralizer ({t} : Set X) := by
    intro q hq
    rw [mem_centralizer_singleton_iff]
    apply hφinj
    rw [map_mul, map_mul]
    refine Equiv.ext fun a => ?_
    rw [Perm.mul_apply, Perm.mul_apply]
    exact ClassicalInvolution.pairSwaps_apply_z (hz := hσ) hq a
  have hQ2 : IsPGroup 2 Q := by
    intro q
    refine ⟨1, Subtype.ext ?_⟩
    apply hφinj
    rw [Subgroup.coe_pow, pow_one, map_pow, sq, Subgroup.coe_one, map_one]
    exact ClassicalInvolution.pairSwaps_mul_self (hz := hσ) q.2
  have hQn : centralizer ({t} : Set X) ≤ normalizer (Q : Set X) := by
    intro c hc
    rw [mem_normalizer_iff]
    intro q
    have hc' := hcommφ c hc
    have hcinv : c⁻¹ ∈ centralizer ({t} : Set X) := inv_mem hc
    have hc'' := hcommφ c⁻¹ hcinv
    constructor
    · intro hq
      change φ (c * q * c⁻¹) ∈ ClassicalInvolution.pairSwaps σ hσ
      rw [map_mul, map_mul, map_inv]
      exact ClassicalInvolution.conj_mem_pairSwaps (hz := hσ) hq hc'
    · intro hq
      change φ q ∈ ClassicalInvolution.pairSwaps σ hσ
      have hq' : φ (c * q * c⁻¹) ∈ ClassicalInvolution.pairSwaps σ hσ := hq
      have := ClassicalInvolution.conj_mem_pairSwaps (hz := hσ) hq' hc''
      have e1 : φ c⁻¹ * φ (c * q * c⁻¹) * (φ c⁻¹)⁻¹ = φ q := by
        rw [← map_inv, ← map_mul, ← map_mul]
        congr 1
        group
      rw [e1] at this
      exact this
  set C := centralizer ({t} : Set X) with hC
  have hQn' : (Q.subgroupOf C).Normal := (normal_subgroupOf_iff_le_normalizer hQC).mpr hQn
  have hQ2' : IsPGroup 2 (Q.subgroupOf C) := hQ2.comap_of_injective C.subtype (subtype_injective C)
  have hcomm := CatalogueBPrimeJoin.p_component_normal_p_centralizer h.isPComponent hQn' hQ2'
  have hLQ : ∀ l ∈ L, ∀ q ∈ Q, l * q = q * l := by
    intro l hl q hq
    have hmem : ⁅(⟨l, h.le_centralizer hl⟩ : C), (⟨q, hQC hq⟩ : C)⁆ ∈
        ⁅L.subgroupOf C, Q.subgroupOf C⁆ :=
      commutator_mem_commutator (by rw [mem_subgroupOf]; exact hl)
        (by rw [mem_subgroupOf]; exact hq)
    rw [hcomm, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact congrArg Subtype.val hmem
  have hfixodd : ∀ l ∈ L, Odd (orderOf l) → ∀ a, σ a ≠ a → φ l a = a := by
    intro l hl hodd a ha
    by_contra hla
    have hodd' : Odd (orderOf (φ l)) := by rw [orderOf_injective φ hφinj]; exact hodd
    obtain ⟨u, hu, hsign, hne⟩ := ClassicalInvolution.exists_mem_pairSwaps_not_commute (hz := hσ)
      (φ l) (hcommφ l (h.le_centralizer hl)) hodd' ha hla
    obtain ⟨q, rfl⟩ := hφrange u (Equiv.Perm.mem_alternatingGroup.mpr hsign)
    apply hne
    rw [← map_mul, ← map_mul, hLQ l hl q hu]
  have hcommσ : ∀ l ∈ L, ∀ a, σ (φ l a) = φ l (σ a) := by
    intro l hl a
    have := congrArg (fun p : Perm (Fin n) => p a) (hcommφ l (h.le_centralizer hl))
    simpa [Perm.mul_apply] using this.symm
  let A : Subgroup L :=
    { carrier := {l | ∀ a, σ a ≠ a → φ (l : X) a = a}
      one_mem' := by intro a _; simp
      mul_mem' := by
        intro x y hx hy a ha
        change φ ((x : X) * y) a = a
        rw [map_mul, Perm.mul_apply, hy a ha, hx a ha]
      inv_mem' := by
        intro x hx a ha
        change φ ((x : X)⁻¹) a = a
        rw [map_inv, Perm.inv_eq_iff_eq]
        exact (hx a ha).symm }
  have hAn : A.Normal := by
    refine ⟨fun g hg l a ha => ?_⟩
    change φ ((l : X) * g * (l : X)⁻¹) a = a
    have hl := l.2
    have hb : σ (φ (l : X)⁻¹ a) ≠ φ (l : X)⁻¹ a := by
      rw [hcommσ _ (inv_mem hl)]
      exact fun h' => ha ((φ (l : X)⁻¹).injective h')
    rw [map_mul, map_mul, Perm.mul_apply, Perm.mul_apply, hg _ hb, ← Perm.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, Perm.one_apply]
  have hAtop : A = ⊤ := by
    have := h.isPerfect
    exact eq_top_of_odd_mem_of_perfect A fun x hx a ha =>
      hfixodd x x.2 (by rw [Subgroup.orderOf_coe]; exact hx) a ha
  have hfix : ∀ l ∈ L, ∀ a, σ a ≠ a → φ l a = a := by
    intro l hl a ha
    have : (⟨l, hl⟩ : L) ∈ A := by rw [hAtop]; exact mem_top _
    exact this a ha
  have hσ1 : σ ≠ 1 := by
    intro h1
    have ht1 : t = 1 := hφinj (by rw [← hσdef, h1, map_one])
    have := h.orderOf_eq
    rw [ht1, orderOf_one] at this
    norm_num at this
  have hσeven : Perm.sign σ = 1 := (e t).2
  obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
    by_contra h1
    push Not at h1
    exact hσ1 (Equiv.ext h1)
  have hσσ : ∀ x, σ (σ x) = x := fun x => by
    simpa using congrArg (fun p : Perm (Fin n) => p x) hσ
  obtain ⟨b, hb, hba, hba'⟩ : ∃ b, σ b ≠ b ∧ b ≠ a ∧ b ≠ σ a := by
    by_contra h1
    push Not at h1
    apply hσ1
    have hswap : σ = Equiv.swap a (σ a) := by
      refine Equiv.ext fun x => ?_
      by_cases hx : σ x = x
      · rw [hx, Equiv.swap_apply_of_ne_of_ne]
        · rintro rfl; exact ha hx
        · rintro rfl; rw [hσσ] at hx; exact ha hx.symm
      · rcases eq_or_ne x a with rfl | hxa
        · rw [Equiv.swap_apply_left]
        · have := h1 x hx hxa
          rw [this, hσσ, Equiv.swap_apply_right]
    have := hσeven
    rw [hswap, Perm.sign_swap (Ne.symm ha)] at this
    exact absurd this (by decide)
  set a' := σ a with ha'
  set b' := σ b with hb'
  have hb'a : b' ≠ a := by
    intro h1; apply hba'; rw [ha', ← h1, hb', hσσ]
  have hb'a' : b' ≠ a' := by
    intro h1; apply hba; exact σ.injective h1
  have d1 : a ≠ a' := Ne.symm ha
  have d2 : a ≠ b := Ne.symm hba
  have d3 : a ≠ b' := Ne.symm hb'a
  have d4 : a' ≠ b := Ne.symm hba'
  have d5 : a' ≠ b' := Ne.symm hb'a'
  have d6 : b ≠ b' := Ne.symm hb
  have hinj : Function.Injective ![a, a', b, b'] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
        Matrix.tail_cons] at hij ⊢ <;>
      first
        | rfl
        | exact absurd hij d1 | exact absurd hij d2 | exact absurd hij d3
        | exact absurd hij d4 | exact absurd hij d5 | exact absurd hij d6
        | exact absurd hij.symm d1 | exact absurd hij.symm d2 | exact absurd hij.symm d3
        | exact absurd hij.symm d4 | exact absurd hij.symm d5 | exact absurd hij.symm d6
  set ι : Fin 4 ↪ Fin n := ⟨![a, a', b, b'], hinj⟩ with hι
  set ψ := Perm.viaEmbeddingHom ι with hψ
  set k1 : Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3 with hk1
  set k2 : Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3 with hk2
  have hsign : ∀ k : Perm (Fin 4), Perm.sign (ψ k) = Perm.sign k := by
    intro k
    classical
    rw [hψ, Perm.viaEmbeddingHom_apply, Perm.viaEmbedding]
    convert Perm.sign_extendDomain k _
  have hmemA : ∀ k : Perm (Fin 4), Perm.sign k = 1 → ψ k ∈ alternatingGroup (Fin n) := by
    intro k hk
    rw [Perm.mem_alternatingGroup, hsign, hk]
  obtain ⟨x1, hx1⟩ := hφrange (ψ k1) (hmemA k1 (by decide))
  obtain ⟨x2, hx2⟩ := hφrange (ψ k2) (hmemA k2 (by decide))
  have hrange : ∀ j, σ (ι j) ≠ ι j := by
    intro j
    fin_cases j
    · exact ha
    · simp only [hι]; show σ a' ≠ a'; rw [ha', hσσ]; exact Ne.symm ha
    · exact hb
    · simp only [hι]; show σ b' ≠ b'; rw [hb', hσσ]; exact Ne.symm hb
  have hcent : ∀ k : Perm (Fin 4), ∀ l ∈ L, φ l * ψ k = ψ k * φ l := by
    intro k l hl
    refine Equiv.ext fun x => ?_
    rw [Perm.mul_apply, Perm.mul_apply]
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨j, rfl⟩ := hx
      rw [hψ, Perm.viaEmbeddingHom_apply, Perm.viaEmbedding_apply, hfix l hl _ (hrange j),
        hfix l hl _ (hrange (k j)), Perm.viaEmbedding_apply]
    · have hx' : φ l x ∉ Set.range ι := by
        rintro ⟨j, hj⟩
        apply hx
        refine ⟨j, ?_⟩
        apply (φ l).injective
        rw [← hj, hfix l hl _ (hrange j)]
      rw [hψ, Perm.viaEmbeddingHom_apply, Perm.viaEmbedding_apply_of_notMem _ _ _ hx,
        Perm.viaEmbedding_apply_of_notMem _ _ _ hx']
  have hxc : ∀ x : X, (∃ k : Perm (Fin 4), φ x = ψ k) → x ∈ centralizer (L : Set X) := by
    rintro x ⟨k, hk⟩
    rw [mem_centralizer_iff]
    intro l hl
    apply hφinj
    rw [map_mul, map_mul, hk]
    exact hcent k l hl
  have hx1c := hxc x1 ⟨k1, hx1⟩
  have hx2c := hxc x2 ⟨k2, hx2⟩
  have hψinj := Perm.viaEmbeddingHom_injective ι
  have hord : ∀ (x : X) (k : Perm (Fin 4)), φ x = ψ k → orderOf k = 2 → orderOf x = 2 := by
    intro x k hk h2
    rw [← orderOf_injective φ hφinj, hk, orderOf_injective ψ hψinj, h2]
  have h1 : orderOf x1 = 2 := hord x1 k1 hx1 (orderOf_eq_prime (by decide) (by decide))
  have h2 : orderOf x2 = 2 := hord x2 k2 hx2 (orderOf_eq_prime (by decide) (by decide))
  have h12 : x1 * x2 = x2 * x1 := by
    apply hφinj
    rw [map_mul, map_mul, hx1, hx2, ← map_mul, ← map_mul]
    congr 1
    decide
  have hne : x1 ≠ x2 := by
    intro h3
    have : ψ k1 = ψ k2 := by rw [← hx1, ← hx2, h3]
    exact absurd (hψinj this) (by decide)
  set E : Subgroup X := zpowers x2 ⊔ zpowers x1 with hE
  have hE2 : IsPGroup 2 E := GSLit.isPGroup_two_sup_zpowers h1 h2 h12
  have hEc : ¬ IsCyclic E := by
    have hx1E : x1 ∈ E := mem_sup_right (mem_zpowers x1)
    have hx2E : x2 ∈ E := mem_sup_left (mem_zpowers x2)
    exact not_isCyclic_of_two_involutions (a := ⟨x1, hx1E⟩) (b := ⟨x2, hx2E⟩)
      (by rw [Subgroup.orderOf_mk]; exact h1) (by rw [Subgroup.orderOf_mk]; exact h2)
      (fun h3 => hne (congrArg Subtype.val h3))
  have hEL : E ≤ centralizer (L : Set X) :=
    sup_le (zpowers_le.mpr hx2c) (zpowers_le.mpr hx1c)
  refine h.false_of_noncyclic hE2 hEc fun e' he' => ?_
  intro l hl
  rw [mem_centralizer_singleton_iff]
  exact mem_centralizer_iff.mp (hEL he') l hl

end CFSG.ComponentClassification.HSFLit
