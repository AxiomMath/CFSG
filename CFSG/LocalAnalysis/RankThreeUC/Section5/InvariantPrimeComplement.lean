module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.Context
import all CFSG.LocalAnalysis.RankThreeUC.Section5.Context
public import CFSG.LocalAnalysis.RankThreeUC.Section5.ThreeLtPRankAndPrimeNotDvdCardActor
public import CFSG.LinearAlgebra.CoprimeActions.InvariantHyperplaneComplements

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.InvariantPrimeComplement

open CFSG.LocalAnalysis.RankThreeUC.Section5

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem lemA {p : ℕ} (hp : p.Prime) {P E K : Subgroup G} (hPab : IsMulCommutative P)
    (hPexp : ∀ x ∈ P, x ^ p = 1) (hEP : E ≤ P) (hidx : E.relIndex P = p)
    (hKP : K ≤ Subgroup.normalizer (P : Set G)) (hKE : K ≤ Subgroup.normalizer (E : Set G))
    (hcop : Nat.Coprime (Nat.card K) p) :
    ∃ R : Subgroup G, R ≤ P ∧ R ⊓ E = ⊥ ∧ R ⊔ E = P ∧ Nat.card R = p ∧
      K ≤ Subgroup.normalizer (R : Set G) := by
  let φ : K →* MulAut P := P.normalizerMonoidHom.comp (Subgroup.inclusion hKP)
  have hφ : ∀ (k : K) (x : P), ((φ k x : P) : G) = k * x * (k : G)⁻¹ := fun k x => rfl
  let H : Subgroup (MulAut P) := φ.range
  have hHc : Nat.Coprime (Nat.card H) p := by
    refine Nat.Coprime.coprime_dvd_left ?_ hcop
    exact Subgroup.card_range_dvd φ
  have hDidx : (E.subgroupOf P).index = p := hidx
  have hmemE : ∀ (k : K) (y : G), k * y * (k : G)⁻¹ ∈ E ↔ y ∈ E := fun k y =>
    ((Subgroup.mem_normalizer_iff.mp (hKE k.2) y)).symm
  have hHD : ∀ h : H, (E.subgroupOf P).map h.val.toMonoidHom = E.subgroupOf P := by
    rintro ⟨h, k, rfl⟩
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      show ((φ k y : P) : G) ∈ E
      rw [hφ, hmemE]; exact hy
    · intro hx
      refine ⟨φ k⁻¹ x, ?_, ?_⟩
      · show ((φ k⁻¹ x : P) : G) ∈ E
        rw [hφ]
        have := (hmemE k⁻¹ x).mpr hx
        simpa using this
      · show φ k (φ k⁻¹ x) = x
        rw [← MulAut.mul_apply, ← map_mul]; simp
  haveI : Finite P := inferInstance
  obtain ⟨R', h1, h2, h3, h4⟩ := CFSG.LinearAlgebra.CoprimeActions.CoprimeElementaryAbelianInvariantHyperplaneComplement.exists_complement
    hp (fun x => Subtype.ext (hPexp x x.2)) H hHc (E.subgroupOf P) hDidx hHD
  have hsub : (E.subgroupOf P).map P.subtype = E := by
    rw [Subgroup.subgroupOf_map_subtype]; exact inf_eq_left.mpr hEP
  have hinj : Function.Injective P.subtype := Subtype.val_injective
  refine ⟨R'.map P.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩; exact x.2
  · rw [← hsub, ← Subgroup.map_inf _ _ _ hinj, h1, Subgroup.map_bot]
  · rw [← hsub, ← Subgroup.map_sup, h2, Subgroup.map_top, Subgroup.range_subtype]
  · rw [Nat.card_congr (Subgroup.equivMapOfInjective R' P.subtype hinj).toEquiv.symm]; exact h3
  · intro k hk
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

theorem exists_complement {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ)
    (E : Subgroup G) (hE : E ∈ Delta p P ρ)
    (hBN : B ≤ Subgroup.normalizer (E : Set G)) :
    ∃ R : Subgroup G, R ≤ P ∧ R ⊓ E = ⊥ ∧ R ⊔ E = P ∧ Nat.card R = p ∧
      twoCoreCommutator T B ⊓ Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (R : Set G) ∧
      B ≤ Subgroup.normalizer (R : Set G) := by
  have hs := hc.oddPrimeClassTwoAction.setting
  obtain ⟨hEP, hidx, -⟩ := hE
  have hab := isElemAbelian_of_binary_rank_counterexample hc
  have h19 := (three_lt_pRank_and_prime_not_dvd_card_actor hc).2
  have hPN : Subgroup.normalizer (P : Set G) = ⊤ := Subgroup.normalizer_eq_top_iff.mpr hc.faithfulBinaryIrreducibleAction.normal
  set M := B ⊔ T with hM
  have hXM : twoCoreCommutator T B ≤ M :=
    (SstarQuotientFaithful.Xs_le_pCoreOf T B le_sup_left).trans (Subgroup.map_subtype_le _)
  have hcardM := card_mul_card_inf_of_supplement (D := B) (H := T) (M := M) le_sup_left le_sup_right
    (sup_supp hs.prod_comm)
  obtain ⟨n, hn⟩ := hs.twoGroup.exists_card_eq
  have hpM : ¬ p ∣ Nat.card M := by
    intro hd
    have : p ∣ Nat.card B * Nat.card T := hcardM ▸ Dvd.dvd.mul_right hd _
    rcases (Nat.Prime.dvd_mul hs.prime).mp this with h | h
    · exact h19 ⟨hs.prime, h⟩
    · rw [hn] at h
      have := (Nat.prime_dvd_prime_iff_eq hs.prime Nat.prime_two).mp (hs.prime.dvd_of_dvd_pow h)
      exact absurd (this ▸ hs.odd) (by decide)
  set K := (twoCoreCommutator T B ⊓ Subgroup.normalizer (E : Set G)) ⊔ B with hK
  have hKM : K ≤ M := sup_le (inf_le_left.trans hXM) le_sup_left
  have hcop : Nat.Coprime (Nat.card K) p :=
    (Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hKM)
      ((Nat.Prime.coprime_iff_not_dvd hs.prime).mpr hpM).symm)
  obtain ⟨R, h1, h2, h3, h4, h5⟩ := lemA hs.prime hab.1 (fun x hx => by
      have := hab.2 x hx; exact this) hEP hidx (by rw [hPN]; exact le_top)
    (sup_le inf_le_right hBN) hcop
  exact ⟨R, h1, h2, h3, h4, le_sup_left.trans h5, le_sup_right.trans h5⟩

end CFSG.LocalAnalysis.RankThreeUC.Section5.InvariantPrimeComplement
end
