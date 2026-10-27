module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniVoid

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped Pointwise

theorem LeviBlock.idxTwistedA_of_at {c : ℕ} {d : TauCeti.LieTypeIndex} (hd : IdxTwistedAAt c d) :
    IdxTwistedA d := by
  cases d with
  | twistedA r₀ q => exact hd.1
  | _ => exact hd.elim

theorem LeviBlock.exists_eq_twistedA_of_at {c : ℕ} {d : TauCeti.LieTypeIndex}
    (hd : IdxTwistedAAt c d) : ∃ r₀ q, d = .twistedA r₀ q ∧ q.p = 2 ∧ q.card = c := by
  cases d with
  | twistedA r₀ q => exact ⟨r₀, q, rfl, hd⟩
  | _ => exact hd.elim

theorem LeviBlock.two_pow_eq_of_at {c f : ℕ} {d : TauCeti.LieTypeIndex} (hd : IdxTwistedAAt c d)
    (hq : ∀ r₀ q, d = .twistedA r₀ q → q.card = 2 ^ f) : 2 ^ f = c := by
  cases d with
  | twistedA r₀ q => exact (hq r₀ q rfl) ▸ hd.2
  | _ => exact hd.elim

theorem LeviBlock.exists_injective_of_hypFlag {Y : Type} [Group Y] {L P : Subgroup Y} {p f : ℕ}
    {K : Type} [Field K] {r ε : ℕ} {h : UnitaryFieldData p f K} {I : Set ℕ}
    (ρ : hypSU h r ε →* ↥L) (hZ : ∀ y, ρ y ∈ Subgroup.center ↥L ↔ y ∈ hypScalars h r ε)
    (g : hypSU h r ε)
    (hJ : ∀ y, y ∈ (P.subgroupOf L).comap ρ ↔
      ∀ i ∈ I, y • (g • hypFlag h r ε i) = g • hypFlag h r ε i)
    {A : Type} [Group A] (φ₀ : A →* hypSU h r ε) (hφ₀ : ∀ a, φ₀ a ∈ flagStabilizer h r ε I)
    (hinj : ∀ a, φ₀ a ∈ hypScalars h r ε → a = 1) :
    ∃ φ : A →* Y, Function.Injective φ ∧ φ.range ≤ P := by
  refine ⟨L.subtype.comp (ρ.comp ((MulAut.conj g).toMonoidHom.comp φ₀)), ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : ρ (MulAut.conj g (φ₀ a)) = 1 := Subtype.ext ha
    have h2 : MulAut.conj g (φ₀ a) ∈ hypScalars h r ε := (hZ _).mp (h1 ▸ Subgroup.one_mem _)
    refine hinj a ?_
    have := (inferInstance : (hypScalars h r ε).Normal).conj_mem _ h2 g⁻¹
    simpa [MulAut.conj_apply, mul_assoc] using this
  · rintro _ ⟨a, rfl⟩
    have hmem : MulAut.conj g (φ₀ a) ∈ (P.subgroupOf L).comap ρ := by
      rw [hJ]
      intro i hi
      rw [MulAut.conj_apply, mul_smul, mul_smul, inv_smul_smul,
        mem_flagStabilizer.mp (hφ₀ a) i hi]
    exact Subgroup.mem_subgroupOf.mp hmem


theorem exists_hypCover_dim {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}
    (hL : IsComponentOf L ⊤) (hodd : Odd (Nat.card (Subgroup.center ↥L)))
    (d : TauCeti.ValidLieTypeIndex) (hd : IdxTwistedA d.1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie d).Group) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (f : ℕ) (h : UnitaryFieldData 2 f K) (r ε : ℕ)
      (ρ : hypSU h r ε →* ↥L), 1 ≤ r ∧ ε ≤ 1 ∧
      (∀ r₀ q, d.1 = .twistedA r₀ q → q.card = 2 ^ f ∧ r₀ + 1 = 2 * r + ε) ∧
      Function.Surjective ρ ∧ ∀ g, ρ g ∈ Subgroup.center ↥L ↔ g ∈ hypScalars h r ε := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | twistedA r₀ q =>
    change q.p = 2 at hd
    have hc := SQTK.statedClassicalModel_twistedA r₀ q hv e
    rw [hd] at hc
    obtain ⟨⟨-, hf, hn3, hnq⟩, K, hK, hKfin, hcard, ⟨e'⟩⟩ := hc
    have hqc : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hd]
    have := Fintype.ofFinite K
    have : CharP K 2 := charP_of_card_eq_prime_pow (f := 2 * q.exponent)
      (by rw [← Nat.card_eq_fintype_card, hcard, ← pow_mul, mul_comm])
    obtain ⟨r, ε, hr, hε, hn⟩ : ∃ r ε, 1 ≤ r ∧ ε ≤ 1 ∧ r₀ + 1 = 2 * r + ε :=
      ⟨(r₀ + 1) / 2, (r₀ + 1) % 2, by omega, by omega, by omega⟩
    rw [hn] at e' hn3 hnq
    obtain ⟨ρ₀, hρ₀, -, hρ₀e⟩ := kFactCoverUnitary Y L hL hodd _ _ K hcard hn3 hnq e'
    have h := ToralCensus.unitaryFieldData_of_card_eq_sq hcard hf
    obtain ⟨R, hR⟩ := exists_isHypTransport h (r := r) (ε := ε)
    refine ⟨K, hK, hKfin, q.exponent, h, r, ε, ρ₀.comp (hypTransport h hR).toMonoidHom, hr, hε,
      fun r₁ q₁ h₁ => ?_, hρ₀.comp (hypTransport h hR).surjective, fun g => ?_⟩
    · injection h₁ with h₃ h₂
      exact ⟨by rw [← h₂, hqc], by rw [← h₃, hn]⟩
    rw [← QuotientGroup.eq_one_iff, ← ker_hypProj, MonoidHom.mem_ker,
      ← (hypPSUEquivStatedProj h hR (by omega)).map_eq_one_iff, hypPSUEquivStatedProj_hypProj,
      ← hρ₀e, e'.map_eq_one_iff]
    rfl
  | _ => exact hd.elim

theorem exists_uniFlag_dim_of_compParab {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y}
    (hCP : CompParab L P) (d : TauCeti.ValidLieTypeIndex) (hd : IdxTwistedA d.1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie d).Group) :
    ∃ (K : Type) (_ : Field K) (f t s ε : ℕ) (h : UnitaryFieldData 2 f K)
      (ρ : hypSU h (t + s) ε →* ↥L) (I : Finset ℕ) (g : hypSU h (t + s) ε),
      ε ≤ 1 ∧ LeviBlock.IsTopCut I t ∧
      (∀ r₀ q, d.1 = .twistedA r₀ q → q.card = 2 ^ f ∧ r₀ + 1 = 2 * (t + s) + ε) ∧
      Function.Surjective ρ ∧ (∀ y, ρ y ∈ Subgroup.center ↥L ↔ y ∈ hypScalars h (t + s) ε) ∧
      ∀ y, y ∈ (P.subgroupOf L).comap ρ ↔
        ∀ i ∈ (↑I : Set ℕ), y • (g • hypFlag h (t + s) ε i) = g • hypFlag h (t + s) ε i := by
  obtain ⟨K, _, _, f, h, r, ε, ρ, hr, hε, hq, hρ, hZ⟩ :=
    exists_hypCover_dim hCP.comp hCP.odd d hd e
  obtain ⟨T, hT⟩ := ToralCensus.exists_sylow_normalizer_le_comap_of_surjective hρ hCP.parab
  obtain ⟨g, I₀, hI₀, hJ⟩ := ToralCensus.exists_eq_stab_hypFlag_of_normalizer_le h hr hε T _ hT
  have hne := ToralCensus.comap_ne_top_of_ne hρ hCP.parab.1 hCP.ne_top
  have hfin : I₀.Finite := (Set.finite_Icc 1 r).subset hI₀
  obtain ⟨I, rfl⟩ : ∃ I : Finset ℕ, (↑I : Set ℕ) = I₀ := ⟨hfin.toFinset, hfin.coe_toFinset⟩
  have hIne : I.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    exact hne (eq_top_iff.mpr fun y _ => (hJ y).mpr fun i hi => absurd hi (by simp))
  obtain ⟨t, htI, htmax⟩ : ∃ t ∈ I, ∀ i ∈ I, i ≤ t :=
    ⟨I.max' hIne, I.max'_mem hIne, fun i hi => I.le_max' i hi⟩
  have htr : t ≤ r := (hI₀ (Finset.mem_coe.mpr htI)).2
  obtain ⟨s, rfl⟩ : ∃ s, r = t + s := ⟨r - t, by omega⟩
  exact ⟨K, inferInstance, f, t, s, ε, h, ρ, I, g, hε,
    ⟨htI, fun i hi => ⟨(hI₀ (Finset.mem_coe.mpr hi)).1, htmax i hi⟩⟩, hq, hρ, hZ, hJ⟩

end CFSG.AGLEmbedding
