module

public import CFSG.Sporadic.Schreier.MathieuOddCoreAssembly

public section

namespace CFSG.OddStandard

open CFSG.Sporadic.Schreier

inductive OddCoreWitness (n : ℕ) where
  | conjugator (h : Equiv.Perm (Fin n)) (productOrder : ℕ)
  | normalGenerators (gens : List (Equiv.Perm (Fin n))) (generatedOrder : ℕ)

structure OddCoreRow (n : ℕ) where
  prime : ℕ
  representative : Equiv.Perm (Fin n)
  classSize : ℕ
  witness : OddCoreWitness n

structure InnerClassRecord (n : ℕ) where
  representative : Equiv.Perm (Fin n)
  classSize : ℕ
  centralizerOrder : ℕ
  centralizerGenerators : List (Equiv.Perm (Fin n))
  oddCore : List (OddCoreRow n)

@[expose] def HasOddPrimeOrder {M : Type*} [Group M] (x : M) : Prop :=
  ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ orderOf x = p

@[expose] def OddCoreWitness.Holds {n : ℕ} (C : Subgroup (Equiv.Perm (Fin n)))
    (x : Equiv.Perm (Fin n)) : OddCoreWitness n → Prop
  | .conjugator h m => h ∈ C ∧ orderOf (x * (h * x * h⁻¹)) = m ∧ Even m
  | .normalGenerators gs m =>
    (∀ v ∈ gs, v ∈ conjClass C x) ∧ Nat.card (Subgroup.closure {v | v ∈ gs}) = m ∧ Even m

@[expose] def OddCoreRowsValid {n : ℕ} (C : Subgroup (Equiv.Perm (Fin n)))
    (rows : List (OddCoreRow n)) : Prop :=
  (∀ r ∈ rows, r.prime.Prime ∧ r.prime ≠ 2 ∧ r.representative ∈ C ∧
      orderOf r.representative = r.prime ∧
      (conjClass C r.representative).ncard = r.classSize ∧
      r.witness.Holds C r.representative) ∧
    rows.Pairwise (fun r s =>
      Disjoint (conjClass C r.representative) (conjClass C s.representative)) ∧
    ∀ x ∈ C, HasOddPrimeOrder x → ∃ r ∈ rows, x ∈ conjClass C r.representative

@[expose] def InnerClassRecordsValid {n : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))
    (recs : List (InnerClassRecord n)) : Prop :=
  (∀ r ∈ recs, r.representative ∈ G ∧ orderOf r.representative = 2 ∧
      (conjClass G r.representative).ncard = r.classSize ∧
      Nat.card (centralizerIn G r.representative) = r.centralizerOrder ∧
      (∀ g ∈ r.centralizerGenerators, g ∈ centralizerIn G r.representative) ∧
      Subgroup.closure {g | g ∈ r.centralizerGenerators} = centralizerIn G r.representative ∧
      OddCoreRowsValid (centralizerIn G r.representative) r.oddCore) ∧
    recs.Pairwise (fun r s =>
      Disjoint (conjClass G r.representative) (conjClass G s.representative)) ∧
    ∀ u ∈ G, orderOf u = 2 → ∃ r ∈ recs, u ∈ conjClass G r.representative

theorem InnerClassRecordsValid.of_perm {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}
    {recs recs' : List (InnerClassRecord n)} (hp : recs.Perm recs')
    (h : InnerClassRecordsValid G recs) : InnerClassRecordsValid G recs' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun r hr => h1 r (hp.mem_iff.2 hr),
    (hp.pairwise_iff fun hrs => Disjoint.symm hrs).1 h2, fun u hu hu2 => ?_⟩
  obtain ⟨r, hr, hur⟩ := h3 u hu hu2
  exact ⟨r, hp.mem_iff.1 hr, hur⟩

@[expose] def recordShape {n : ℕ} (recs : List (InnerClassRecord n)) : List (ℕ × ℕ) :=
  recs.map fun r => (r.classSize, r.centralizerOrder)

@[expose] def MathieuInnerStatement {n : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))
    (shape : List (ℕ × ℕ)) : Prop :=
  (∃ recs : List (InnerClassRecord n), recordShape recs = shape ∧ InnerClassRecordsValid G recs) ∧
    ∀ t : G, orderOf t = 2 → CFSG.oddCore (Subgroup.centralizer ({t} : Set G)) = ⊥

theorem noOddNormal_of_rowsValid {n : ℕ} {C : Subgroup (Equiv.Perm (Fin n))}
    {rows : List (OddCoreRow n)} (h : OddCoreRowsValid C rows) : NoOddNormal C := by
  obtain ⟨hrows, -, hcov⟩ := h
  intro N hNC hnorm hodd
  by_contra hne
  have hcard1 : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).2 hne
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hcard1.ne'
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := N) p hpdvd
  have hpodd : Odd p := Odd.of_dvd_nat hodd hpdvd
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact absurd hpodd (by decide)
  have hyN : (y : Equiv.Perm (Fin n)) ∈ N := y.2
  have hord : orderOf (y : Equiv.Perm (Fin n)) = p := by rw [Subgroup.orderOf_coe, hy]
  obtain ⟨r, hr, c, hc, hyc⟩ := hcov _ (hNC hyN) ⟨p, hp, hp2, hord⟩
  obtain ⟨-, -, hxC, -, -, hwit⟩ := hrows r hr
  have hxN : r.representative ∈ N := by
    have := hnorm c⁻¹ (C.inv_mem hc) _ hyN
    rw [hyc] at this
    simpa [mul_assoc] using this
  have hdvd : ∀ m : ℕ, (∃ z ∈ N, orderOf z = m) → m ∣ Nat.card N := by
    rintro m ⟨z, hz, rfl⟩
    have := orderOf_dvd_natCard (⟨z, hz⟩ : N)
    rwa [← Subgroup.orderOf_coe] at this
  cases hw : r.witness with
  | conjugator k m =>
    rw [hw] at hwit
    obtain ⟨hkC, hm, hev⟩ := hwit
    have hconj : k * r.representative * k⁻¹ ∈ N := hnorm k hkC _ hxN
    have hmem : r.representative * (k * r.representative * k⁻¹) ∈ N := N.mul_mem hxN hconj
    exact (Nat.not_even_iff_odd.2 (Odd.of_dvd_nat hodd (hdvd m ⟨_, hmem, hm⟩))) hev
  | normalGenerators gs m =>
    rw [hw] at hwit
    obtain ⟨hgs, hm, hev⟩ := hwit
    have hle : Subgroup.closure {v | v ∈ gs} ≤ N := by
      rw [Subgroup.closure_le]
      intro v hv
      obtain ⟨d, hd, rfl⟩ := hgs v hv
      exact hnorm d hd _ hxN
    have := Subgroup.card_dvd_of_le hle
    rw [hm] at this
    exact (Nat.not_even_iff_odd.2 (Odd.of_dvd_nat hodd this)) hev

theorem NoOddNormal.of_map {Y Y' : Type*} [Group Y] [Group Y'] {f : Y →* Y'}
    (hf : Function.Injective f) {K : Subgroup Y} (h : NoOddNormal (K.map f)) : NoOddNormal K := by
  intro N hNK hnorm hodd
  have hmap := h (N.map f) (Subgroup.map_mono hNK) (by
    rintro _ ⟨k, hk, rfl⟩ _ ⟨x, hx, rfl⟩
    exact ⟨k * x * k⁻¹, hnorm k hk x hx, by simp⟩)
    (by rw [Subgroup.card_map_of_injective hf]; exact hodd)
  exact (Subgroup.map_eq_bot_iff_of_injective N hf).1 hmap

theorem noOddNormal_centralizerIn_of_recordsValid {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}
    {recs : List (InnerClassRecord n)} (h : InnerClassRecordsValid G recs)
    {u : Equiv.Perm (Fin n)} (hu : u ∈ G) (hu2 : orderOf u = 2) :
    NoOddNormal (centralizerIn G u) := by
  obtain ⟨hrecs, -, hcov⟩ := h
  obtain ⟨r, hr, c, hc, rfl⟩ := hcov u hu hu2
  obtain ⟨-, -, -, -, -, -, hrows⟩ := hrecs r hr
  rw [centralizerIn_conj G hc]
  exact NoOddNormal.map (MulAut.conj c).injective (noOddNormal_of_rowsValid hrows)

theorem oddCore_centralizer_eq_bot_of_recordsValid {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}
    {recs : List (InnerClassRecord n)} (h : InnerClassRecordsValid G recs) (t : G)
    (ht : orderOf t = 2) : CFSG.oddCore (Subgroup.centralizer ({t} : Set G)) = ⊥ := by
  apply oddCore_eq_bot_of_noOddNormal
  refine NoOddNormal.of_map (f := G.subtype) G.subtype_injective ?_
  rw [map_centralizer_subtype]
  exact noOddNormal_centralizerIn_of_recordsValid h t.2 (by rw [Subgroup.orderOf_coe]; exact ht)

theorem mathieuInnerStatement_of_recordsValid {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}
    {shape : List (ℕ × ℕ)} {recs : List (InnerClassRecord n)} (hshape : recordShape recs = shape)
    (h : InnerClassRecordsValid G recs) : MathieuInnerStatement G shape :=
  ⟨⟨recs, hshape, h⟩, fun t ht => oddCore_centralizer_eq_bot_of_recordsValid h t ht⟩

end CFSG.OddStandard
