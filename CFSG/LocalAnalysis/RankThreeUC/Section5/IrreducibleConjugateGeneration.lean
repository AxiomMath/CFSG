module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.NonzeroInvariantSubgroupContainsQ
public import CFSG.LocalAnalysis.RankThreeUC.Section5.Context
import all CFSG.LocalAnalysis.RankThreeUC.Section5.Context

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.IrreducibleConjugateGeneration

open CFSG.LocalAnalysis.RankThreeUC.Section5

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem relIndex_eq_of_supplement {D H M : Subgroup G} (hDM : D ≤ M)
    (hsupp : ∀ x ∈ M, ∃ d ∈ D, ∃ c ∈ H, x = d * c) : H.relIndex D = H.relIndex M := by
  rw [Subgroup.relIndex, Subgroup.relIndex, Subgroup.index, Subgroup.index]
  refine Nat.card_congr (Equiv.ofBijective (Subgroup.quotientSubgroupOfEmbeddingOfLE H hDM)
    ⟨(Subgroup.quotientSubgroupOfEmbeddingOfLE H hDM).injective, fun y => ?_⟩)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨d, hd, c, hc, hx⟩ := hsupp x x.2
  refine ⟨QuotientGroup.mk ⟨d, hd⟩, ?_⟩
  rw [Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk, QuotientGroup.eq]
  rw [Subgroup.mem_subgroupOf]
  have : ((Subgroup.inclusion hDM ⟨d, hd⟩)⁻¹ * x : M) = (c : G) := by
    simp [hx]
  rw [this]
  exact hc

omit [Finite G] in
private theorem card_mul_card_inf_of_supplement {D H M : Subgroup G} (hDM : D ≤ M) (hHM : H ≤ M)
    (hsupp : ∀ x ∈ M, ∃ d ∈ D, ∃ c ∈ H, x = d * c) :
    Nat.card M * Nat.card (D ⊓ H : Subgroup G) = Nat.card D * Nat.card H := by
  have h1 := Subgroup.relIndex_mul_card (H := H) (K := M)
  have h2 := Subgroup.relIndex_mul_card (H := H) (K := D)
  rw [inf_eq_left.mpr hHM, ← relIndex_eq_of_supplement hDM hsupp] at h1
  rw [inf_comm] at h2
  rw [← h1, ← h2]
  ring

omit [Finite G] in
private theorem sup_supp {B T : Subgroup G} (h : (T : Set G) * (B : Set G) = (B : Set G) * (T : Set G)) :
    ∀ x ∈ B ⊔ T, ∃ d ∈ B, ∃ c ∈ T, x = d * c := by
  let K : Subgroup G :=
    { carrier := (B : Set G) * (T : Set G)
      one_mem' := ⟨1, B.one_mem, 1, T.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨b, hb, t, ht, rfl⟩ ⟨b', hb', t', ht', rfl⟩
        have : t * b' ∈ (T : Set G) * (B : Set G) := ⟨t, ht, b', hb', rfl⟩
        rw [h] at this
        obtain ⟨b'', hb'', t'', ht'', he⟩ := this
        refine ⟨b * b'', B.mul_mem hb hb'', t'' * t', T.mul_mem ht'' ht', ?_⟩
        calc b * b'' * (t'' * t') = b * (b'' * t'') * t' := by simp [mul_assoc]
          _ = b * (t * b') * t' := by rw [show b'' * t'' = t * b' from he]
          _ = _ := by simp [mul_assoc]
      inv_mem' := by
        rintro _ ⟨b, hb, t, ht, rfl⟩
        have : t⁻¹ * b⁻¹ ∈ (T : Set G) * (B : Set G) := ⟨t⁻¹, T.inv_mem ht, b⁻¹, B.inv_mem hb, rfl⟩
        rw [h] at this
        obtain ⟨b'', hb'', t'', ht'', he⟩ := this
        exact ⟨b'', hb'', t'', ht'', by rw [mul_inv_rev]; exact he⟩ }
  have : B ⊔ T ≤ K := sup_le (fun b hb => ⟨b, hb, 1, T.one_mem, by simp⟩)
    (fun t ht => ⟨1, B.one_mem, t, ht, by simp⟩)
  intro x hx
  obtain ⟨b, hb, t, ht, he⟩ := this hx
  exact ⟨b, hb, t, ht, he.symm⟩

private theorem complement {E : Type} [Group E] [Finite E] {p : ℕ} (hp : p.Prime)
    [IsMulCommutative E] (hE : ∀ x : E, x ^ p = 1) (H : Subgroup (MulAut E))
    (hcop : Nat.Coprime (Nat.card H) p) (D : Subgroup E)
    (hHD : ∀ h : H, D.map h.val.toMonoidHom = D) :
    ∃ R : Subgroup E, R ⊓ D = ⊥ ∧ R ⊔ D = ⊤ ∧
      ∀ h : H, R.map h.val.toMonoidHom = R := by
  haveI : Fact p.Prime := ⟨hp⟩
  letI : CommGroup E := { ‹Group E› with mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
  letI := CFSG.LinearAlgebra.CoprimeActions.ElementaryAbelianHyperplaneCounts.moduleOf hE
  haveI : NeZero (Nat.card H : ZMod p) := by
    refine ⟨?_⟩
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm hcop) h
    exact hp.one_lt.ne' this
  let ρ : Representation (ZMod p) H (Additive E) :=
    { toFun := fun h =>
        { toFun := fun x => Additive.ofMul (h.1 (Additive.toMul x))
          map_add' := fun x y => by simp
          map_smul' := fun c x => by
            exact ZMod.map_smul (MonoidHom.toAdditive h.1.toMonoidHom) c x }
      map_one' := by ext; rfl
      map_mul' := fun a b => by ext; rfl }
  have hmem : ∀ (S : Subgroup E) (x : Additive E),
      x ∈ CFSG.LinearAlgebra.CoprimeActions.ElementaryAbelianHyperplaneCounts.subgroupEquiv hE S ↔
        Additive.toMul x ∈ S :=
    fun S x => Iff.rfl
  have hρ : ∀ (h : H) (x : Additive E), ρ h x = Additive.ofMul (h.1 (Additive.toMul x)) :=
    fun h x => rfl
  let D' : Subrepresentation ρ :=
    { toSubmodule := CFSG.LinearAlgebra.CoprimeActions.ElementaryAbelianHyperplaneCounts.subgroupEquiv hE D
      apply_mem_toSubmodule := fun h v hv => by
        rw [hmem] at hv ⊢
        rw [hρ]
        have : h.1 (Additive.toMul v) ∈ D.map h.val.toMonoidHom := ⟨_, hv, rfl⟩
        rwa [hHD h] at this }
  obtain ⟨R', hR'⟩ := exists_isCompl D'
  set e := CFSG.LinearAlgebra.CoprimeActions.ElementaryAbelianHyperplaneCounts.subgroupEquiv hE with he
  have hRe : e (e.symm R'.toSubmodule) = R'.toSubmodule := e.apply_symm_apply _
  have hinf : D'.toSubmodule ⊓ R'.toSubmodule = ⊥ := by
    have := congrArg Subrepresentation.toSubmodule hR'.inf_eq_bot
    exact this
  have hsup : D'.toSubmodule ⊔ R'.toSubmodule = ⊤ := by
    have := congrArg Subrepresentation.toSubmodule hR'.sup_eq_top
    exact this
  have hDe : D'.toSubmodule = e D := rfl
  refine ⟨e.symm R'.toSubmodule, ?_, ?_, ?_⟩
  · apply e.injective
    rw [e.map_inf, hRe, e.map_bot, ← hDe, inf_comm, hinf]
  · apply e.injective
    rw [e.map_sup, hRe, e.map_top, ← hDe, sup_comm, hsup]
  · intro h
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have := R'.apply_mem_toSubmodule h (v := Additive.ofMul y) (by rw [← hRe] at hy; exact hy)
      rw [hρ] at this
      rw [← hRe]; exact this
    · intro hx
      refine ⟨h.1⁻¹ x, ?_, by simp⟩
      have := R'.apply_mem_toSubmodule (h⁻¹) (v := Additive.ofMul x) (by rw [← hRe] at hx; exact hx)
      rw [hρ] at this
      rw [← hRe]; exact this

private theorem eq_of_stable {p : ℕ} (hp : p.Prime) {P Q P1 K : Subgroup G}
    (hPab : IsMulCommutative P) (hPexp : ∀ x ∈ P, x ^ p = 1)
    (hKP : K ≤ Subgroup.normalizer (P : Set G)) (hcop : Nat.Coprime (Nat.card K) p)
    (hP1 : P1 ≤ P) (hKP1 : K ≤ Subgroup.normalizer (P1 : Set G))
    (hQP1 : Q ≤ P1) (hQ : Q ≠ ⊥)
    (hQall : ∀ P0 : Subgroup G, P0 ≤ P → K ≤ Subgroup.normalizer (P0 : Set G) → P0 ≠ ⊥ → Q ≤ P0) :
    P1 = P := by
  let φ : K →* MulAut P := P.normalizerMonoidHom.comp (Subgroup.inclusion hKP)
  have hφ : ∀ (k : K) (x : P), ((φ k x : P) : G) = k * x * (k : G)⁻¹ := fun k x => rfl
  let H : Subgroup (MulAut P) := φ.range
  have hHc : Nat.Coprime (Nat.card H) p :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_range_dvd φ) hcop
  have hmemE : ∀ (k : K) (y : G), k * y * (k : G)⁻¹ ∈ P1 ↔ y ∈ P1 := fun k y =>
    ((Subgroup.mem_normalizer_iff.mp (hKP1 k.2) y)).symm
  have hHD : ∀ h : H, (P1.subgroupOf P).map h.val.toMonoidHom = P1.subgroupOf P := by
    rintro ⟨h, k, rfl⟩
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      show ((φ k y : P) : G) ∈ P1
      rw [hφ, hmemE]; exact hy
    · intro hx
      refine ⟨φ k⁻¹ x, ?_, ?_⟩
      · show ((φ k⁻¹ x : P) : G) ∈ P1
        rw [hφ]
        have := (hmemE k⁻¹ x).mpr hx
        simpa using this
      · show φ k (φ k⁻¹ x) = x
        rw [← MulAut.mul_apply, ← map_mul]; simp
  obtain ⟨R', h1, h2, h4⟩ := complement hp (fun x => Subtype.ext (hPexp x x.2)) H hHc
    (P1.subgroupOf P) hHD
  have hsub : (P1.subgroupOf P).map P.subtype = P1 := by
    rw [Subgroup.subgroupOf_map_subtype]; exact inf_eq_left.mpr hP1
  have hinj : Function.Injective P.subtype := Subtype.val_injective
  set R := R'.map P.subtype with hR
  have hRP : R ≤ P := by rintro _ ⟨x, -, rfl⟩; exact x.2
  have hRinf : R ⊓ P1 = ⊥ := by
    rw [← hsub, ← Subgroup.map_inf _ _ _ hinj, h1, Subgroup.map_bot]
  have hRN : K ≤ Subgroup.normalizer (R : Set G) := by
    intro k hk
    have hmap := h4 ⟨φ ⟨k, hk⟩, ⟨_, rfl⟩⟩
    have hmap' : ∀ y : P, y ∈ R' ↔ φ ⟨k, hk⟩ y ∈ R' := by
      intro y
      constructor
      · intro hy
        have : φ ⟨k, hk⟩ y ∈ R'.map (φ ⟨k, hk⟩).toMonoidHom := ⟨y, hy, rfl⟩
        exact hmap ▸ this
      · intro hy
        have : φ ⟨k, hk⟩ y ∈ R'.map (φ ⟨k, hk⟩).toMonoidHom := by
          rw [show R'.map (φ ⟨k, hk⟩).toMonoidHom = R' from hmap]; exact hy
        obtain ⟨z, hz, hzy⟩ := this
        have : z = y := (φ ⟨k, hk⟩).injective hzy
        exact this ▸ hz
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨φ ⟨k, hk⟩ y, (hmap' y).mp hy, hφ _ _⟩
    · rintro ⟨z, hz, hzx⟩
      have hxP : x ∈ P := by
        rw [Subgroup.mem_normalizer_iff.mp (hKP hk) x, ← hzx]; exact z.2
      refine ⟨⟨x, hxP⟩, ?_, rfl⟩
      show (⟨x, hxP⟩ : P) ∈ R'
      rw [hmap' ⟨x, hxP⟩]
      have : φ ⟨k, hk⟩ ⟨x, hxP⟩ = z := Subtype.ext (by rw [hφ]; exact hzx.symm)
      rw [this]; exact hz
  have hR0 : R = ⊥ := by
    by_contra hne
    have hQR := hQall R hRP hRN hne
    apply hQ
    rw [eq_bot_iff, ← hRinf]
    exact le_inf hQR hQP1
  have hR'0 : R' = ⊥ := by
    rw [hR] at hR0
    exact (Subgroup.map_eq_bot_iff_of_injective R' hinj).mp hR0
  rw [hR'0, bot_sup_eq] at h2
  apply le_antisymm hP1
  intro x hx
  have : (⟨x, hx⟩ : P) ∈ P1.subgroupOf P := by rw [h2]; trivial
  exact this

theorem irreducible_generated {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ) :
    (P = Subgroup.closure {x | ∃ s ∈ twoCoreCommutator T B,
        x ∈ (P ⊓ Subgroup.centralizer (B : Set G)).map (MulAut.conj s).toMonoidHom}) ∧
    (∀ P0 : Subgroup G, P0 ≤ P → twoCoreCommutator T B ≤ Subgroup.normalizer (P0 : Set G) →
      B ≤ Subgroup.normalizer (P0 : Set G) → P0 ≠ ⊥ → P0 = P) := by
  have hS := hc.oddPrimeClassTwoAction.setting
  have hP : P.Normal := hc.faithfulBinaryIrreducibleAction.normal
  have hPN : Subgroup.normalizer (P : Set G) = ⊤ := Subgroup.normalizer_eq_top_iff.mpr hP
  have hel := isElemAbelian_of_binary_rank_counterexample hc
  have hPab : IsMulCommutative P := hel.1
  have hexp : ∀ x ∈ P, x ^ p = 1 := fun x hx => by
    have := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : P)
    rw [hS.exponent] at this
    exact congrArg Subtype.val this
  have h19 := (three_lt_pRank_and_prime_not_dvd_card_actor hc).2
  set Q : Subgroup G := P ⊓ Subgroup.centralizer (B : Set G) with hQdef
  have hQne : Q ≠ ⊥ := (CanonicalBFixedHyperplane.canonical hc).2.1.1
  have hBXs : B ≤ Subgroup.normalizer (twoCoreCommutator T B : Set G) :=
    Subgroup.normalizer_commutator_ge_right _ B
  set M := B ⊔ T with hM
  have hXM : twoCoreCommutator T B ≤ M :=
    (SstarQuotientFaithful.Xs_le_pCoreOf T B le_sup_left).trans (Subgroup.map_subtype_le _)
  have hcardM := card_mul_card_inf_of_supplement (D := B) (H := T) (M := M) le_sup_left le_sup_right
    (sup_supp hS.prod_comm)
  obtain ⟨n, hn⟩ := hS.twoGroup.exists_card_eq
  have hpM : ¬ p ∣ Nat.card M := by
    intro hd
    have : p ∣ Nat.card B * Nat.card T := hcardM ▸ Dvd.dvd.mul_right hd _
    rcases (Nat.Prime.dvd_mul hS.prime).mp this with h | h
    · exact h19 ⟨hS.prime, h⟩
    · rw [hn] at h
      have := (Nat.prime_dvd_prime_iff_eq hS.prime Nat.prime_two).mp (hS.prime.dvd_of_dvd_pow h)
      exact absurd (this ▸ hS.odd) (by decide)
  set K := twoCoreCommutator T B ⊔ B with hK
  have hKM : K ≤ M := sup_le hXM le_sup_left
  have hcop : Nat.Coprime (Nat.card K) p :=
    (Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hKM)
      ((Nat.Prime.coprime_iff_not_dvd hS.prime).mpr hpM).symm)
  have hKP : K ≤ Subgroup.normalizer (P : Set G) := by rw [hPN]; exact le_top
  set P1 : Subgroup G := Subgroup.closure {x | ∃ s ∈ twoCoreCommutator T B,
        x ∈ Q.map (MulAut.conj s).toMonoidHom} with hP1
  have hgen : ∀ s ∈ twoCoreCommutator T B, ∀ q ∈ Q, s * q * s⁻¹ ∈ P1 := fun s hs q hq =>
    Subgroup.subset_closure ⟨s, hs, q, hq, rfl⟩
  have hP1P : P1 ≤ P := by
    rw [hP1, Subgroup.closure_le]
    rintro x ⟨s, -, q, hq, rfl⟩
    exact (hP.conj_mem q hq.1 s)
  have hQP1 : Q ≤ P1 := fun q hq => by
    have := hgen 1 (twoCoreCommutator T B).one_mem q hq
    simpa using this
  have hnormalizer : ∀ A : Subgroup G, (∀ t ∈ A, ∀ x ∈ P1, t * x * t⁻¹ ∈ P1) →
      A ≤ Subgroup.normalizer (P1 : Set G) := by
    intro A hA t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hA t ht x hx, fun hx => ?_⟩
    have := hA t⁻¹ (A.inv_mem ht) _ hx
    simpa [mul_assoc] using this
  have hXsN : twoCoreCommutator T B ≤ Subgroup.normalizer (P1 : Set G) := by
    apply hnormalizer
    intro t ht x hx
    have hx' : x ∈ Subgroup.closure {x | ∃ s ∈ twoCoreCommutator T B,
        x ∈ Q.map (MulAut.conj s).toMonoidHom} := hx
    refine Subgroup.closure_induction (p := fun x _ => t * x * t⁻¹ ∈ P1) ?_ ?_ ?_ ?_ hx'
    · rintro y ⟨s, hs, q, hq, rfl⟩
      have := hgen (t * s) (mul_mem ht hs) q hq
      simpa [mul_assoc] using this
    · simpa using P1.one_mem
    · intro y z _ _ hy hz
      have := P1.mul_mem hy hz
      simpa [mul_assoc] using this
    · intro y _ hy
      have := P1.inv_mem hy
      simpa [mul_assoc] using this
  have hBN : B ≤ Subgroup.normalizer (P1 : Set G) := by
    apply hnormalizer
    intro t ht x hx
    have hx' : x ∈ Subgroup.closure {x | ∃ s ∈ twoCoreCommutator T B,
        x ∈ Q.map (MulAut.conj s).toMonoidHom} := hx
    refine Subgroup.closure_induction (p := fun x _ => t * x * t⁻¹ ∈ P1) ?_ ?_ ?_ ?_ hx'
    · rintro y ⟨s, hs, q, hq, rfl⟩
      have hs' : t * s * t⁻¹ ∈ twoCoreCommutator T B := (Subgroup.mem_normalizer_iff.1 (hBXs ht) s).1 hs
      have hqc : t * q * t⁻¹ = q := by
        have := Subgroup.mem_centralizer_iff.1 hq.2 t ht
        rw [this]; group
      have := hgen _ hs' q hq
      have hqc' : t⁻¹ * q * t = q := by
        calc t⁻¹ * q * t = t⁻¹ * (t * q * t⁻¹) * t := by rw [hqc]
          _ = q := by group
      have e : t * s * t⁻¹ * q * (t * s * t⁻¹)⁻¹ = t * (s * q * s⁻¹) * t⁻¹ := by
        calc t * s * t⁻¹ * q * (t * s * t⁻¹)⁻¹
            = t * s * (t⁻¹ * q * t) * s⁻¹ * t⁻¹ := by group
          _ = t * s * q * s⁻¹ * t⁻¹ := by rw [hqc']
          _ = _ := by group
      show t * (s * q * s⁻¹) * t⁻¹ ∈ P1
      rw [← e]; exact this
    · simpa using P1.one_mem
    · intro y z _ _ hy hz
      have := P1.mul_mem hy hz
      simpa [mul_assoc] using this
    · intro y _ hy
      have := P1.inv_mem hy
      simpa [mul_assoc] using this
  have hKN : K ≤ Subgroup.normalizer (P1 : Set G) := sup_le hXsN hBN
  have hall : ∀ P0 : Subgroup G, P0 ≤ P → K ≤ Subgroup.normalizer (P0 : Set G) →
      P0 ≠ ⊥ → Q ≤ P0 := fun P0 h0 hK0 hne =>
    NonzeroInvariantSubgroupContainsQ.contains hc h0 (le_sup_left.trans hK0)
      (le_sup_right.trans hK0) hne
  have hP1eq : P1 = P := eq_of_stable hS.prime hPab hexp hKP hcop hP1P hKN hQP1 hQne hall
  refine ⟨hP1eq.symm, fun P0 hP0 hX hB hne => ?_⟩
  have hQ0 := NonzeroInvariantSubgroupContainsQ.contains hc hP0 hX hB hne
  have hle : P1 ≤ P0 := by
    rw [hP1, Subgroup.closure_le]
    rintro x ⟨s, hs, q, hq, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 (hX hs) q).1 (hQ0 hq)
  exact le_antisymm hP0 (hP1eq ▸ hle)

end CFSG.LocalAnalysis.RankThreeUC.Section5.IrreducibleConjugateGeneration
end
