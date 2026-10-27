module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fact1019

open CFSG.Open Subgroup CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

theorem characteristic_prime_of_ne_two (d : TauCeti.LieTypeIndex)
    (h : d.characteristic ≠ 2) : d.characteristic.Prime := by
  cases d with
  | A _ q => simpa using q.prime_p
  | twistedA _ q => simpa using q.prime_p
  | B _ q => simpa using q.prime_p
  | C _ q => simpa using q.prime_p
  | D _ q => simpa using q.prime_p
  | twistedD _ q => simpa using q.prime_p
  | E6 q => simpa using q.prime_p
  | E7 q => simpa using q.prime_p
  | E8 q => simpa using q.prime_p
  | F4 q => simpa using q.prime_p
  | G2 q => simpa using q.prime_p
  | twistedE6 q => simpa using q.prime_p
  | trialityD4 q => simpa using q.prime_p
  | suzuki _ => exact absurd (TauCeti.LieTypeIndex.characteristic_suzuki _) h
  | reeG2 _ => rw [TauCeti.LieTypeIndex.characteristic_reeG2]; exact Nat.prime_three
  | reeF4 _ => exact absurd (TauCeti.LieTypeIndex.characteristic_reeF4 _) h
  | tits => exact absurd TauCeti.LieTypeIndex.characteristic_tits h

@[expose] def FamA4 (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ (r : ℕ) (q : TauCeti.PrimePower), 4 ≤ r ∧ d.1 = TauCeti.LieTypeIndex.A r q

@[expose] def FamTwistedA4 (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ (r : ℕ) (q : TauCeti.PrimePower), 4 ≤ r ∧ d.1 = TauCeti.LieTypeIndex.twistedA r q

@[expose] def FamB3 (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ (r : ℕ) (q : TauCeti.PrimePower), 3 ≤ r ∧ d.1 = TauCeti.LieTypeIndex.B r q

@[expose] def FamC3 (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ (r : ℕ) (q : TauCeti.PrimePower), 3 ≤ r ∧ d.1 = TauCeti.LieTypeIndex.C r q

@[expose] def FamD4 (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ (r : ℕ) (q : TauCeti.PrimePower), 4 ≤ r ∧ d.1 = TauCeti.LieTypeIndex.D r q

@[expose] def FamTwistedD4 (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ (r : ℕ) (q : TauCeti.PrimePower), 4 ≤ r ∧ d.1 = TauCeti.LieTypeIndex.twistedD r q

@[expose] def FamE6 (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, d.1 = TauCeti.LieTypeIndex.E6 q

@[expose] def FamTwistedE6 (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, d.1 = TauCeti.LieTypeIndex.twistedE6 q

@[expose] def FamE7 (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, d.1 = TauCeti.LieTypeIndex.E7 q

@[expose] def FamE8 (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, d.1 = TauCeti.LieTypeIndex.E8 q

@[expose] def FamF4 (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, d.1 = TauCeti.LieTypeIndex.F4 q

@[expose] def FamTrialityD4 (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, d.1 = TauCeti.LieTypeIndex.trialityD4 q

@[expose] def InvolutionAt (Fam : TauCeti.ValidLieTypeIndex → Prop) : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex), Fam d →
    Nonempty (K ≃* CFSG.AGLEmbedding.CatGroup d) →
      ∀ p : ℕ, p.Prime → p ≠ 2 → p = d.1.characteristic →
        ∃ t : K, orderOf t = 2 ∧ ∃ E : Subgroup K, E ≤ Subgroup.centralizer {t} ∧
          IsElemAbelian p E ∧ Nat.card E = p ^ 4

theorem cover_families (d : TauCeti.ValidLieTypeIndex) (hodd : d.1.characteristic ≠ 2)
    (hdih : ¬ IsDihedralTypeIndex d.1) (hree : ¬ IsReeIndex d.1)
    (hrk : ¬ IsRankTwoOddIndex d.1) :
    FamA4 d ∨ FamTwistedA4 d ∨ FamB3 d ∨ FamC3 d ∨ FamD4 d ∨ FamTwistedD4 d ∨ FamE6 d ∨
      FamTwistedE6 d ∨ FamE7 d ∨ FamE8 d ∨ FamF4 d ∨ FamTrialityD4 d := by
  obtain ⟨d, hv⟩ := d
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  cases d with
  | A r q =>
    have hr1 : 1 ≤ r := hr.1
    have hodd' : q.p ≠ 2 := by simpa using hodd
    rcases (by omega : r = 1 ∨ r = 2 ∨ r = 3 ∨ 4 ≤ r) with rfl | rfl | rfl | h4
    · exact absurd (hodd' : IsDihedralTypeIndex (TauCeti.LieTypeIndex.A 1 q)) hdih
    · exact absurd (hodd' : IsDihedralTypeIndex (TauCeti.LieTypeIndex.A 2 q)) hdih
    · exact absurd (hodd' : IsRankTwoOddIndex (TauCeti.LieTypeIndex.A 3 q)) hrk
    · exact Or.inl ⟨r, q, h4, rfl⟩
  | twistedA r q =>
    have hr2 : 2 ≤ r := hr.1
    have hodd' : q.p ≠ 2 := by simpa using hodd
    rcases (by omega : r = 2 ∨ r = 3 ∨ 4 ≤ r) with rfl | rfl | h4
    · exact absurd (hodd' : IsDihedralTypeIndex (TauCeti.LieTypeIndex.twistedA 2 q)) hdih
    · exact absurd (hodd' : IsRankTwoOddIndex (TauCeti.LieTypeIndex.twistedA 3 q)) hrk
    · exact Or.inr (Or.inl ⟨r, q, h4, rfl⟩)
  | B r q =>
    have hr2 : 2 ≤ r := hr.1
    have hodd' : q.p ≠ 2 := by simpa using hodd
    rcases (by omega : r = 2 ∨ 3 ≤ r) with rfl | h3
    · exact absurd (hodd' : IsRankTwoOddIndex (TauCeti.LieTypeIndex.B 2 q)) hrk
    · exact Or.inr (Or.inr (Or.inl ⟨r, q, h3, rfl⟩))
  | C r q =>
    have hr3 : 3 ≤ r := hr.1
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨r, q, hr3, rfl⟩)))
  | D r q =>
    have hr4 : 4 ≤ r := hr
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, q, hr4, rfl⟩))))
  | twistedD r q =>
    have hr4 : 4 ≤ r := hr
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, q, hr4, rfl⟩)))))
  | E6 q => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl⟩))))))
  | twistedE6 q =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl⟩)))))))
  | E7 q =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl⟩))))))))
  | E8 q =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨q, rfl⟩)))))))))
  | F4 q =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨q, rfl⟩))))))))))
  | trialityD4 q =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr ⟨q, rfl⟩))))))))))
  | G2 q =>
    have hodd' : q.p ≠ 2 := by simpa using hodd
    exact absurd (hodd' : IsRankTwoOddIndex (TauCeti.LieTypeIndex.G2 q)) hrk
  | suzuki _ => exact absurd (TauCeti.LieTypeIndex.characteristic_suzuki _) hodd
  | reeG2 _ => exact absurd (trivial : IsReeIndex (TauCeti.LieTypeIndex.reeG2 _)) hree
  | reeF4 _ => exact absurd (TauCeti.LieTypeIndex.characteristic_reeF4 _) hodd
  | tits => exact absurd TauCeti.LieTypeIndex.characteristic_tits hodd

theorem le_normalizer_zpowers_of_mem_centralizer {A : Type} [Group A] {t x : A}
    (hx : x ∈ Subgroup.centralizer ({t} : Set A)) :
    x ∈ Subgroup.normalizer ((Subgroup.zpowers t : Subgroup A) : Set A) := by
  have hc : Commute x t := (Subgroup.mem_centralizer_iff.1 hx t (Set.mem_singleton t)).symm
  have key : ∀ s ∈ Subgroup.zpowers t, x * s * x⁻¹ = s := by
    intro s hs
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
    rw [mul_inv_eq_iff_eq_mul]
    exact (hc.zpow_right k).eq
  have key' : ∀ s ∈ Subgroup.zpowers t, x⁻¹ * s * x = s := by
    intro s hs
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
    rw [(hc.inv_left.zpow_right k).eq, mul_assoc, inv_mul_cancel, mul_one]
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [key h hh]
    exact hh
  · intro hh
    have e := key' _ hh
    have e2 : h = x * h * x⁻¹ := by
      calc h = x⁻¹ * (x * h * x⁻¹) * x := by group
        _ = x * h * x⁻¹ := e
    rw [e2]
    exact hh

theorem isPGroup_two_zpowers {A : Type} [Group A] {t : A} (ht : orderOf t = 2) :
    IsPGroup 2 (Subgroup.zpowers t) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])

theorem false_of_involution {A : Type} [Group A] [Finite A] {L : Subgroup A} {p : ℕ}
    [hp : Fact p.Prime]
    (hU : ∀ U : Subgroup A, U ≤ L → U ≠ ⊥ → IsPGroup 2 U →
      CFSG.Open.pRank p (normalizer (U : Set A) ⊓ L) ≤ 3)
    (hinv : ∃ t : L, orderOf t = 2 ∧ ∃ E : Subgroup L, E ≤ Subgroup.centralizer {t} ∧
      IsElemAbelian p E ∧ Nat.card E = p ^ 4) : False := by
  obtain ⟨t, ht, E, hEc, hE, hcard⟩ := hinv
  have hord : orderOf (t : A) = 2 := by
    rw [← ht]
    exact orderOf_injective L.subtype Subtype.val_injective t
  have hE' : IsElemAbelian p (E.map L.subtype) := CFSG.SectionRank.isElemAbelian_map hE L.subtype
  have hcard' : Nat.card (E.map L.subtype) = p ^ 4 := by
    rw [Subgroup.card_map_of_injective L.subtype_injective, hcard]
  have hEL : E.map L.subtype ≤ L := Subgroup.map_subtype_le E
  have hEc' : E.map L.subtype ≤ Subgroup.centralizer {(t : A)} := by
    rintro x ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    have hyt : t * y = y * t := Subgroup.mem_centralizer_iff.1 (hEc hy) t (Set.mem_singleton t)
    show (t : A) * (y : A) = (y : A) * (t : A)
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hyt]
  have hUL : Subgroup.zpowers (t : A) ≤ L := Subgroup.zpowers_le.2 t.2
  have hU0 : Subgroup.zpowers (t : A) ≠ ⊥ := by
    intro h
    have hmem : (t : A) ∈ Subgroup.zpowers (t : A) := Subgroup.mem_zpowers _
    rw [h, Subgroup.mem_bot] at hmem
    rw [orderOf_eq_one_iff.2 hmem] at hord
    norm_num at hord
  have hbound := hU _ hUL hU0 (isPGroup_two_zpowers hord)
  have hsub : E.map L.subtype ≤ normalizer ((Subgroup.zpowers (t : A) : Subgroup A) : Set A) ⊓ L :=
    le_inf (fun x hx => le_normalizer_zpowers_of_mem_centralizer (hEc' hx)) hEL
  have h4 : 4 ≤ CFSG.Open.pRank p (normalizer ((Subgroup.zpowers (t : A) : Subgroup A) : Set A) ⊓
      L) := CFSG.SectionRank.le_pRank hp.out.one_lt hsub hE' hcard'
  omega

theorem involution_in_subgroup {A : Type} [Group A] [Finite A] {L : Subgroup A}
    {Fam : TauCeti.ValidLieTypeIndex → Prop} (hX : InvolutionAt Fam)
    {d : TauCeti.ValidLieTypeIndex} (hF : Fam d) (e : ↥L ≃* CFSG.AGLEmbedding.CatGroup d)
    (hpr : d.1.characteristic.Prime) (hp2 : d.1.characteristic ≠ 2) :
    ∃ t : L, orderOf t = 2 ∧ ∃ E : Subgroup L, E ≤ Subgroup.centralizer {t} ∧
      IsElemAbelian d.1.characteristic E ∧ Nat.card E = d.1.characteristic ^ 4 :=
  hX (↥L) d hF ⟨e⟩ d.1.characteristic hpr hp2 rfl

theorem kFact1019_of_involutionAt
    (hA : InvolutionAt FamA4) (hTA : InvolutionAt FamTwistedA4) (hB : InvolutionAt FamB3)
    (hC : InvolutionAt FamC3) (hD : InvolutionAt FamD4) (hTD : InvolutionAt FamTwistedD4)
    (hE6 : InvolutionAt FamE6) (hTE6 : InvolutionAt FamTwistedE6)
    (hE7 : InvolutionAt FamE7) (hE8 : InvolutionAt FamE8) (hF4 : InvolutionAt FamF4)
    (hTD4 : InvolutionAt FamTrialityD4) :
    KFact1019 := by
  intro A _ _ L d hchar ⟨e⟩ hU
  have hpr : d.1.characteristic.Prime := characteristic_prime_of_ne_two d.1 hchar
  by_contra hcon
  have hdih : ¬ IsDihedralTypeIndex d.1 := fun h => hcon (Or.inl h)
  have hree : ¬ IsReeIndex d.1 := fun h => hcon (Or.inr (Or.inl h))
  have hrk : ¬ IsRankTwoOddIndex d.1 := fun h => hcon (Or.inr (Or.inr h))
  haveI : Fact d.1.characteristic.Prime := ⟨hpr⟩
  rcases cover_families d hchar hdih hree hrk with h | h | h | h | h | h | h | h | h | h | h | h
  · exact false_of_involution hU (involution_in_subgroup hA h e hpr hchar)
  · exact false_of_involution hU (involution_in_subgroup hTA h e hpr hchar)
  · exact false_of_involution hU (involution_in_subgroup hB h e hpr hchar)
  · exact false_of_involution hU (involution_in_subgroup hC h e hpr hchar)
  · exact false_of_involution hU (involution_in_subgroup hD h e hpr hchar)
  · exact false_of_involution hU (involution_in_subgroup hTD h e hpr hchar)
  · exact false_of_involution hU (involution_in_subgroup hE6 h e hpr hchar)
  · exact false_of_involution hU (involution_in_subgroup hTE6 h e hpr hchar)
  · exact false_of_involution hU (involution_in_subgroup hE7 h e hpr hchar)
  · exact false_of_involution hU (involution_in_subgroup hE8 h e hpr hchar)
  · exact false_of_involution hU (involution_in_subgroup hF4 h e hpr hchar)
  · exact false_of_involution hU (involution_in_subgroup hTD4 h e hpr hchar)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fact1019
