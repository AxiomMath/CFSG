module

public import CFSG.RankThree.PartOne.KD4L.TriNu
public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootData
public import CFSG.RankThree.PartOne.KE.A1Main
public import CFSG.RankThree.PartOne.KD4L.TriDescent

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KD4L
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints)

section Commute

variable {τ : Tag} {L : Type} [Field L]

theorem ssTw_iform_single_of_cartan_zero {p q : Fin τ.rank} (h : τ.cartan p q = 0) :
    iform (Pi.single p 1 : Fin τ.rank → ℤ) (Pi.single q 1) = 0 := by
  rw [iform_single_left]
  have : ∑ j, τ.cartan p j * (Pi.single q 1 : Fin τ.rank → ℤ) j = τ.cartan p q := by
    rw [Finset.sum_eq_single q (fun l _ hl => by rw [Pi.single_eq_of_ne hl, mul_zero])
      (fun h => absurd (Finset.mem_univ q) h), Pi.single_eq_same, mul_one]
  rw [this, h, mul_zero]

theorem ssTw_commute_xUnit (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {p q : Fin τ.rank}
    (h : τ.cartan p q = 0) (s t : L) : Commute (xUnit τ L p s) (xUnit τ L q t) :=
  (simply_laced_orthogonal_root_commutation τ hτ).2 L (Pi.single p 1) (Pi.single q 1)
    (isRoot_single τ p) (isRoot_single τ q)
    (by rw [dotProduct_mulVec_eq_iform]; exact ssTw_iform_single_of_cartan_zero h)
    (xUnit τ L p s) (mem_rootSubgroup.2 ⟨s, pinnedX_single τ L p s⟩) (xUnit τ L q t)
    (mem_rootSubgroup.2 ⟨t, pinnedX_single τ L q t⟩)

end Commute

section Norm

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime]
  [CharP L ℓ]

@[expose] noncomputable def ssTwXHom (j : Fin τ.rank) (φ : L →+* L) (K : Subfield L) :
    Multiplicative K →* ModGL τ L where
  toFun c := xUnit τ L j (φ ((c.toAdd : K) : L))
  map_one' := by simp [xUnit_zero]
  map_mul' c d := by simp [xUnit_add]

theorem ssTw_exists_pairGroup (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hf : 1 ≤ f)
    {a b : Fin τ.rank} (hab : a ≠ b) (hc : τ.cartan a b = 0) {n₁ : ModGL τ L}
    (hna : ∀ c : L, n₁ * xUnit τ L a c * n₁⁻¹ = xUnit τ L b c)
    (hnb : ∀ c : L, n₁ * xUnit τ L b c * n₁⁻¹ = xUnit τ L a c) :
    ∃ V : Subgroup (ModGL τ L),
      (∀ g ∈ V, ∃ s t : L, g = xUnit τ L a s * xUnit τ L b t) ∧
      (∀ g ∈ V, n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n₁⁻¹ = g) ∧
      IsPGroup ℓ V ∧ (ℓ ^ f) ^ 2 ≤ Nat.card V := by
  classical
  let K : Subfield L := frobeniusFixedField L ℓ (2 * f)
  have hK : ∀ u : K, ((u : L)) ^ (ℓ ^ f) ^ 2 = u := fun u => by
    have h := mem_frobeniusFixedField.1 u.2
    rwa [show ℓ ^ (2 * f) = (ℓ ^ f) ^ 2 by rw [mul_comm, pow_mul]] at h
  let ψ : Multiplicative K →* ModGL τ L :=
    (MonoidHom.noncommCoprod (ssTwXHom a (RingHom.id L) K)
      (ssTwXHom b (iterateFrobenius L ℓ f) K)
      (fun c d => ssTw_commute_xUnit hτ hc _ _)).comp
      (MonoidHom.prod (MonoidHom.id _) (MonoidHom.id _))
  have hψ : ∀ c : Multiplicative K, ψ c = xUnit τ L a ((c.toAdd : K) : L) *
      xUnit τ L b (((c.toAdd : K) : L) ^ ℓ ^ f) := fun c => by
    simp [ψ, ssTwXHom, iterateFrobenius_def]
  have hfix : ∀ c : Multiplicative K,
      n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (ψ c) * n₁⁻¹ = ψ c := by
    intro c
    have hu2 : ((c.toAdd : K) : L) ^ (ℓ ^ f) ^ 2 = ((c.toAdd : K) : L) := hK c.toAdd
    rw [hψ c, map_mul, entrywise_xUnit, entrywise_xUnit]
    have e : n₁ * (xUnit τ L a (((c.toAdd : K) : L) ^ ℓ ^ f) *
        xUnit τ L b ((((c.toAdd : K) : L) ^ ℓ ^ f) ^ ℓ ^ f)) * n₁⁻¹ =
        (n₁ * xUnit τ L a (((c.toAdd : K) : L) ^ ℓ ^ f) * n₁⁻¹) *
          (n₁ * xUnit τ L b ((((c.toAdd : K) : L) ^ ℓ ^ f) ^ ℓ ^ f) * n₁⁻¹) := by group
    rw [e, hna, hnb, ← pow_mul, ← sq, hu2]
    exact (ssTw_commute_xUnit hτ hc _ _).eq.symm
  have hψp : ∀ c : Multiplicative K, ψ c ^ ℓ = 1 := fun c => by
    rw [← map_pow]
    have : c ^ ℓ = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one, nsmul_eq_mul]
      have : (ℓ : K) = 0 := CharP.cast_eq_zero K ℓ
      rw [this, zero_mul]
    rw [this, map_one]
  have hψinj : Function.Injective ψ := by
    let α : Fin 2 → Fin τ.rank → ℤ := fun i => Pi.single (![a, b] i) 1
    have hα : Function.Injective α := by
      intro i j h
      have := single_eq_single_iff.1 h
      fin_cases i <;> fin_cases j <;> simp_all
    have hpos : ∀ i, IsRoot τ (α i) ∧ 0 < height (α i) := fun i => ⟨isRoot_single τ _, by simp [α]⟩
    have hinj := (positive_root_product_injectivity τ L α hα hpos).2
    have key : ∀ s t : L, (List.ofFn fun i => pinnedX τ L (α i) (![s, t] i)).prod =
        xUnit τ L a s * xUnit τ L b t := by
      intro s t
      simp [α, List.ofFn_succ, pinnedX_single]
    intro c d h
    rw [hψ c, hψ d, ← key, ← key] at h
    have h0 := congrFun (hinj h) 0
    simp only [Matrix.cons_val_zero] at h0
    exact Multiplicative.toAdd.injective (Subtype.ext h0)
  refine ⟨ψ.range, ?_, ?_, ?_, ?_⟩
  · rintro g ⟨c, rfl⟩
    exact ⟨_, _, hψ c⟩
  · rintro g ⟨c, rfl⟩
    exact hfix c
  · rintro ⟨g, c, rfl⟩
    exact ⟨1, Subtype.ext (by simpa using hψp c)⟩
  · have h1 : Nat.card ψ.range = Nat.card (Multiplicative K) :=
      (Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv).symm
    have h2 : Nat.card (Multiplicative K) = Nat.card K := Nat.card_congr Multiplicative.toAdd
    have h3 : Nat.card K = ℓ ^ (2 * f) := card_frobeniusFixedField (by omega)
    rw [h1, h2, h3, show ℓ ^ (2 * f) = (ℓ ^ f) ^ 2 by rw [mul_comm, pow_mul]]

theorem ssTw_exists_tripleGroup (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hf : 1 ≤ f)
    {a b c : Fin τ.rank} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hcab : τ.cartan a b = 0) (hcbc : τ.cartan b c = 0) (hcac : τ.cartan a c = 0)
    {n₁ : ModGL τ L}
    (hna : ∀ t : L, n₁ * xUnit τ L a t * n₁⁻¹ = xUnit τ L b t)
    (hnb : ∀ t : L, n₁ * xUnit τ L b t * n₁⁻¹ = xUnit τ L c t)
    (hnc : ∀ t : L, n₁ * xUnit τ L c t * n₁⁻¹ = xUnit τ L a t) :
    ∃ V : Subgroup (ModGL τ L),
      (∀ g ∈ V, ∃ r s t : L, g = xUnit τ L a r * xUnit τ L b s * xUnit τ L c t) ∧
      (∀ g ∈ V, n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n₁⁻¹ = g) ∧
      IsPGroup ℓ V ∧ (ℓ ^ f) ^ 3 ≤ Nat.card V := by
  classical
  let K : Subfield L := frobeniusFixedField L ℓ (3 * f)
  have hK : ∀ u : K, ((u : L)) ^ ℓ ^ (3 * f) = u := fun u => mem_frobeniusFixedField.1 u.2
  let ψ₂ : Multiplicative K →* ModGL τ L :=
    (MonoidHom.noncommCoprod (ssTwXHom a (RingHom.id L) K)
      (ssTwXHom b (iterateFrobenius L ℓ f) K)
      (fun c d => ssTw_commute_xUnit hτ hcab _ _)).comp
      (MonoidHom.prod (MonoidHom.id _) (MonoidHom.id _))
  let ψ : Multiplicative K →* ModGL τ L :=
    (MonoidHom.noncommCoprod ψ₂ (ssTwXHom c (iterateFrobenius L ℓ (2 * f)) K)
      (fun x y => by
        have h1 : ψ₂ x = xUnit τ L a ((x.toAdd : K) : L) *
            xUnit τ L b (((x.toAdd : K) : L) ^ ℓ ^ f) := by
          simp [ψ₂, ssTwXHom, iterateFrobenius_def]
        rw [h1]
        exact ((ssTw_commute_xUnit hτ hcac _ _).mul_left (ssTw_commute_xUnit hτ hcbc _ _)))).comp
      (MonoidHom.prod (MonoidHom.id _) (MonoidHom.id _))
  have hψ : ∀ x : Multiplicative K, ψ x = xUnit τ L a ((x.toAdd : K) : L) *
      xUnit τ L b (((x.toAdd : K) : L) ^ ℓ ^ f) *
        xUnit τ L c (((x.toAdd : K) : L) ^ ℓ ^ (2 * f)) := fun x => by
    simp [ψ, ψ₂, ssTwXHom, iterateFrobenius_def]
  have hfix : ∀ x : Multiplicative K,
      n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (ψ x) * n₁⁻¹ = ψ x := by
    intro x
    set u : L := ((x.toAdd : K) : L) with hu
    have hu3 : u ^ ℓ ^ (3 * f) = u := hK x.toAdd
    have e1 : (u ^ ℓ ^ f) ^ ℓ ^ f = u ^ ℓ ^ (2 * f) := by
      rw [← pow_mul, ← pow_add, two_mul]
    have e2 : (u ^ ℓ ^ (2 * f)) ^ ℓ ^ f = u := by
      rw [← pow_mul, ← pow_add, show 2 * f + f = 3 * f by ring, hu3]
    rw [hψ x, map_mul, map_mul, entrywise_xUnit, entrywise_xUnit, entrywise_xUnit, e1, e2]
    have e : n₁ * (xUnit τ L a (u ^ ℓ ^ f) * xUnit τ L b (u ^ ℓ ^ (2 * f)) * xUnit τ L c u) *
        n₁⁻¹ = (n₁ * xUnit τ L a (u ^ ℓ ^ f) * n₁⁻¹) *
          (n₁ * xUnit τ L b (u ^ ℓ ^ (2 * f)) * n₁⁻¹) * (n₁ * xUnit τ L c u * n₁⁻¹) := by group
    rw [e, hna, hnb, hnc]
    have hca : Commute (xUnit τ L a u) (xUnit τ L b (u ^ ℓ ^ f) * xUnit τ L c (u ^ ℓ ^ (2 * f))) :=
      (ssTw_commute_xUnit hτ hcab _ _).mul_right (ssTw_commute_xUnit hτ hcac _ _)
    calc xUnit τ L b (u ^ ℓ ^ f) * xUnit τ L c (u ^ ℓ ^ (2 * f)) * xUnit τ L a u
        = xUnit τ L a u * (xUnit τ L b (u ^ ℓ ^ f) * xUnit τ L c (u ^ ℓ ^ (2 * f))) := hca.eq.symm
      _ = _ := by rw [mul_assoc]
  have hψp : ∀ x : Multiplicative K, ψ x ^ ℓ = 1 := fun x => by
    rw [← map_pow]
    have : x ^ ℓ = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one, nsmul_eq_mul]
      have : (ℓ : K) = 0 := CharP.cast_eq_zero K ℓ
      rw [this, zero_mul]
    rw [this, map_one]
  have hψinj : Function.Injective ψ := by
    let α : Fin 3 → Fin τ.rank → ℤ := fun i => Pi.single (![a, b, c] i) 1
    have hba : b ≠ a := hab.symm
    have hcb : c ≠ b := hbc.symm
    have hca' : c ≠ a := hac.symm
    have hα : Function.Injective α := by
      intro i j h
      have := single_eq_single_iff.1 h
      fin_cases i <;> fin_cases j <;> simp_all
    have hpos : ∀ i, IsRoot τ (α i) ∧ 0 < height (α i) := fun i => ⟨isRoot_single τ _, by simp [α]⟩
    have hinj := (positive_root_product_injectivity τ L α hα hpos).2
    have key : ∀ r s t : L, (List.ofFn fun i => pinnedX τ L (α i) (![r, s, t] i)).prod =
        xUnit τ L a r * xUnit τ L b s * xUnit τ L c t := by
      intro r s t
      simp [α, List.ofFn_succ, pinnedX_single, mul_assoc]
    intro x y h
    rw [hψ x, hψ y, ← key, ← key] at h
    have h0 := congrFun (hinj h) 0
    simp only [Matrix.cons_val_zero] at h0
    exact Multiplicative.toAdd.injective (Subtype.ext h0)
  refine ⟨ψ.range, ?_, ?_, ?_, ?_⟩
  · rintro g ⟨x, rfl⟩
    exact ⟨_, _, _, hψ x⟩
  · rintro g ⟨x, rfl⟩
    exact hfix x
  · rintro ⟨g, x, rfl⟩
    exact ⟨1, Subtype.ext (by simpa using hψp x)⟩
  · have h1 : Nat.card ψ.range = Nat.card (Multiplicative K) :=
      (Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv).symm
    have h2 : Nat.card (Multiplicative K) = Nat.card K := Nat.card_congr Multiplicative.toAdd
    have h3 : Nat.card K = ℓ ^ (3 * f) := card_frobeniusFixedField (by omega)
    rw [h1, h2, h3, show ℓ ^ (3 * f) = (ℓ ^ f) ^ 3 by rw [mul_comm, pow_mul]]

theorem ssTw_exists_fixedPairGroup (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hf : 1 ≤ f)
    {a b : Fin τ.rank} (hab : a ≠ b) (hc : τ.cartan a b = 0) {n₁ : ModGL τ L}
    (hna : ∀ c : L, n₁ * xUnit τ L a c * n₁⁻¹ = xUnit τ L a c)
    (hnb : ∀ c : L, n₁ * xUnit τ L b c * n₁⁻¹ = xUnit τ L b c) :
    ∃ V : Subgroup (ModGL τ L),
      (∀ g ∈ V, ∃ s t : L, g = xUnit τ L a s * xUnit τ L b t) ∧
      (∀ g ∈ V, n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n₁⁻¹ = g) ∧
      IsPGroup ℓ V ∧ (ℓ ^ f) ^ 2 ≤ Nat.card V := by
  classical
  let K : Subfield L := frobeniusFixedField L ℓ f
  have hK : ∀ u : K, ((u : L)) ^ ℓ ^ f = u := fun u => mem_frobeniusFixedField.1 u.2
  let ψ : Multiplicative K × Multiplicative K →* ModGL τ L :=
    MonoidHom.noncommCoprod (ssTwXHom a (RingHom.id L) K) (ssTwXHom b (RingHom.id L) K)
      (fun c d => ssTw_commute_xUnit hτ hc _ _)
  have hψ : ∀ x : Multiplicative K × Multiplicative K, ψ x = xUnit τ L a ((x.1.toAdd : K) : L) *
      xUnit τ L b ((x.2.toAdd : K) : L) := fun x => by
    simp [ψ, ssTwXHom]
  have hfix : ∀ x : Multiplicative K × Multiplicative K,
      n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (ψ x) * n₁⁻¹ = ψ x := by
    intro x
    rw [hψ x, map_mul, entrywise_xUnit, entrywise_xUnit, hK, hK]
    have e : n₁ * (xUnit τ L a ((x.1.toAdd : K) : L) * xUnit τ L b ((x.2.toAdd : K) : L)) *
        n₁⁻¹ = (n₁ * xUnit τ L a ((x.1.toAdd : K) : L) * n₁⁻¹) *
          (n₁ * xUnit τ L b ((x.2.toAdd : K) : L) * n₁⁻¹) := by group
    rw [e, hna, hnb]
  have hψp : ∀ x : Multiplicative K × Multiplicative K, ψ x ^ ℓ = 1 := fun x => by
    rw [← map_pow]
    have : x ^ ℓ = 1 := by
      refine Prod.ext ?_ ?_
      · apply Multiplicative.toAdd.injective
        rw [Prod.pow_fst, toAdd_pow, Prod.fst_one, toAdd_one, nsmul_eq_mul]
        have : (ℓ : K) = 0 := CharP.cast_eq_zero K ℓ
        rw [this, zero_mul]
      · apply Multiplicative.toAdd.injective
        rw [Prod.pow_snd, toAdd_pow, Prod.snd_one, toAdd_one, nsmul_eq_mul]
        have : (ℓ : K) = 0 := CharP.cast_eq_zero K ℓ
        rw [this, zero_mul]
    rw [this, map_one]
  have hψinj : Function.Injective ψ := by
    let α : Fin 2 → Fin τ.rank → ℤ := fun i => Pi.single (![a, b] i) 1
    have hα : Function.Injective α := by
      intro i j h
      have := single_eq_single_iff.1 h
      fin_cases i <;> fin_cases j <;> simp_all
    have hpos : ∀ i, IsRoot τ (α i) ∧ 0 < height (α i) := fun i => ⟨isRoot_single τ _, by simp [α]⟩
    have hinj := (positive_root_product_injectivity τ L α hα hpos).2
    have key : ∀ s t : L, (List.ofFn fun i => pinnedX τ L (α i) (![s, t] i)).prod =
        xUnit τ L a s * xUnit τ L b t := by
      intro s t
      simp [α, List.ofFn_succ, pinnedX_single]
    intro x y h
    rw [hψ x, hψ y, ← key, ← key] at h
    have h0 := congrFun (hinj h) 0
    have h1 := congrFun (hinj h) 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h0 h1
    exact Prod.ext (Multiplicative.toAdd.injective (Subtype.ext h0))
      (Multiplicative.toAdd.injective (Subtype.ext h1))
  refine ⟨ψ.range, ?_, ?_, ?_, ?_⟩
  · rintro g ⟨x, rfl⟩
    exact ⟨_, _, hψ x⟩
  · rintro g ⟨x, rfl⟩
    exact hfix x
  · rintro ⟨g, x, rfl⟩
    exact ⟨1, Subtype.ext (by simpa using hψp x)⟩
  · have h1 : Nat.card ψ.range = Nat.card (Multiplicative K × Multiplicative K) :=
      (Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv).symm
    have h2 : Nat.card (Multiplicative K) = Nat.card K := Nat.card_congr Multiplicative.toAdd
    have h3 : Nat.card K = ℓ ^ f := card_frobeniusFixedField (by omega)
    rw [h1, Nat.card_prod, h2, h3, sq]

end Norm

section Transport

@[expose] def SsBig (ℓ : ℕ) {G : Type*} [Group G] (P : Subgroup G) : Prop :=
  ∃ V : Subgroup G, V ≤ P ∧ IsPGroup ℓ V ∧ 8 ≤ Nat.card V

theorem SsBig.mono {ℓ : ℕ} {G : Type*} [Group G] {P Q : Subgroup G} (h : SsBig ℓ P) (hPQ : P ≤ Q) :
    SsBig ℓ Q :=
  let ⟨V, hV, hp, h8⟩ := h
  ⟨V, hV.trans hPQ, hp, h8⟩

theorem SsBig.map {ℓ : ℕ} {G H : Type*} [Group G] [Group H] {P : Subgroup G} (h : SsBig ℓ P)
    (f : G →* H) (hf : Function.Injective f) : SsBig ℓ (P.map f) := by
  obtain ⟨V, hV, hp, h8⟩ := h
  refine ⟨V.map f, Subgroup.map_mono hV, ?_, ?_⟩
  · exact hp.of_surjective (V.equivMapOfInjective f hf).toMonoidHom
      (MulEquiv.surjective _)
  · rwa [Subgroup.card_map_of_injective hf]

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime]
  [CharP L ℓ]

theorem ssTw_map_conj_le {J : Set (Fin τ.rank)} {n n₁ h : ModGL τ L}
    (hh : h ∈ subsystemGroup τ L J)
    (hlang : ∀ g : ModGL τ L,
      n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n⁻¹ = g ↔
        n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (h * g * h⁻¹) * n₁⁻¹ =
          h * g * h⁻¹)
    {V : Subgroup (ModGL τ L)} (hVJ : ∀ g ∈ V, g ∈ subsystemGroup τ L J)
    (hVfix : ∀ g ∈ V, n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n₁⁻¹ = g) :
    V.map (MulAut.conj h⁻¹).toMonoidHom ≤
      subsystemGroup τ L J ⊓ twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
  rintro _ ⟨g, hg, rfl⟩
  have hx : (MulAut.conj h⁻¹).toMonoidHom g = h⁻¹ * g * h := by simp
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [hx]
    exact mul_mem (mul_mem (inv_mem hh) (hVJ g hg)) hh
  · have e : h * (h⁻¹ * g * h) * h⁻¹ = g := by group
    rw [hx, mem_twistedFixedPoints]
    refine (hlang _).2 ?_
    rw [e]
    exact hVfix g hg

theorem ssBig_of_std {J : Set (Fin τ.rank)} {n n₁ h : ModGL τ L}
    (hh : h ∈ subsystemGroup τ L J)
    (hlang : ∀ g : ModGL τ L,
      n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n⁻¹ = g ↔
        n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (h * g * h⁻¹) * n₁⁻¹ =
          h * g * h⁻¹)
    {V : Subgroup (ModGL τ L)} (hVJ : ∀ g ∈ V, g ∈ subsystemGroup τ L J)
    (hVfix : ∀ g ∈ V, n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n₁⁻¹ = g)
    (hp : IsPGroup ℓ V) (h8 : 8 ≤ Nat.card V) :
    SsBig ℓ (subsystemGroup τ L J ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :=
  (SsBig.map ⟨V, le_rfl, hp, h8⟩ (MulAut.conj h⁻¹).toMonoidHom (MulAut.conj h⁻¹).injective).mono
    (ssTw_map_conj_le hh hlang hVJ hVfix)

theorem ssTw_eight_le_pow {ℓ f m : ℕ} (hℓ5 : 5 ≤ ℓ) (hf : 1 ≤ f) (hm : 2 ≤ m) :
    8 ≤ (ℓ ^ f) ^ m := by
  have h5 : 5 ≤ ℓ ^ f := hℓ5.trans (Nat.le_self_pow (by omega) ℓ)
  calc 8 ≤ 5 ^ 2 := by norm_num
    _ ≤ (ℓ ^ f) ^ 2 := Nat.pow_le_pow_left h5 2
    _ ≤ (ℓ ^ f) ^ m := Nat.pow_le_pow_right (by omega) hm

theorem ssTw_mem_sub_pair {J : Set (Fin τ.rank)} {a b : Fin τ.rank} (ha : a ∈ J) (hb : b ∈ J)
    {g : ModGL τ L} (hg : ∃ s t : L, g = xUnit τ L a s * xUnit τ L b t) :
    g ∈ subsystemGroup τ L J := by
  obtain ⟨s, t, rfl⟩ := hg
  exact mul_mem (xUnit_mem_subsystemGroup ha s) (xUnit_mem_subsystemGroup hb t)

theorem ssTw_mem_sub_triple {J : Set (Fin τ.rank)} {a b c : Fin τ.rank} (ha : a ∈ J) (hb : b ∈ J)
    (hc : c ∈ J) {g : ModGL τ L} (hg : ∃ r s t : L, g = xUnit τ L a r * xUnit τ L b s * xUnit τ L c t) :
    g ∈ subsystemGroup τ L J := by
  obtain ⟨r, s, t, rfl⟩ := hg
  exact mul_mem (mul_mem (xUnit_mem_subsystemGroup ha r) (xUnit_mem_subsystemGroup hb s))
    (xUnit_mem_subsystemGroup hc t)

theorem ssBig_of_std_swap (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hℓ5 : 5 ≤ ℓ) (hf : 1 ≤ f)
    {J : Set (Fin τ.rank)} {n n₁ h : ModGL τ L} (hh : h ∈ subsystemGroup τ L J)
    (hlang : ∀ g : ModGL τ L,
      n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n⁻¹ = g ↔
        n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (h * g * h⁻¹) * n₁⁻¹ =
          h * g * h⁻¹)
    {a b : Fin τ.rank} (ha : a ∈ J) (hb : b ∈ J) (hab : a ≠ b) (hc : τ.cartan a b = 0)
    (hna : ∀ c : L, n₁ * xUnit τ L a c * n₁⁻¹ = xUnit τ L b c)
    (hnb : ∀ c : L, n₁ * xUnit τ L b c * n₁⁻¹ = xUnit τ L a c) :
    SsBig ℓ (subsystemGroup τ L J ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) := by
  obtain ⟨V, hV, hfix, hp, hcard⟩ := ssTw_exists_pairGroup hτ hf hab hc hna hnb
  exact ssBig_of_std hh hlang (fun g hg => ssTw_mem_sub_pair ha hb (hV g hg)) hfix hp
    ((ssTw_eight_le_pow hℓ5 hf le_rfl).trans hcard)

theorem ssBig_of_std_cycle (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hℓ5 : 5 ≤ ℓ) (hf : 1 ≤ f)
    {J : Set (Fin τ.rank)} {n n₁ h : ModGL τ L} (hh : h ∈ subsystemGroup τ L J)
    (hlang : ∀ g : ModGL τ L,
      n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n⁻¹ = g ↔
        n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (h * g * h⁻¹) * n₁⁻¹ =
          h * g * h⁻¹)
    {a b c : Fin τ.rank} (ha : a ∈ J) (hb : b ∈ J) (hc : c ∈ J) (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) (hcab : τ.cartan a b = 0) (hcbc : τ.cartan b c = 0) (hcac : τ.cartan a c = 0)
    (hna : ∀ t : L, n₁ * xUnit τ L a t * n₁⁻¹ = xUnit τ L b t)
    (hnb : ∀ t : L, n₁ * xUnit τ L b t * n₁⁻¹ = xUnit τ L c t)
    (hnc : ∀ t : L, n₁ * xUnit τ L c t * n₁⁻¹ = xUnit τ L a t) :
    SsBig ℓ (subsystemGroup τ L J ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) := by
  obtain ⟨V, hV, hfix, hp, hcard⟩ :=
    ssTw_exists_tripleGroup hτ hf hab hbc hac hcab hcbc hcac hna hnb hnc
  exact ssBig_of_std hh hlang (fun g hg => ssTw_mem_sub_triple ha hb hc (hV g hg)) hfix hp
    ((ssTw_eight_le_pow hℓ5 hf (by norm_num)).trans hcard)

theorem ssBig_of_std_fixed (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hℓ5 : 5 ≤ ℓ) (hf : 1 ≤ f)
    {J : Set (Fin τ.rank)} {n n₁ h : ModGL τ L} (hh : h ∈ subsystemGroup τ L J)
    (hlang : ∀ g : ModGL τ L,
      n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n⁻¹ = g ↔
        n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (h * g * h⁻¹) * n₁⁻¹ =
          h * g * h⁻¹)
    {a b : Fin τ.rank} (ha : a ∈ J) (hb : b ∈ J) (hab : a ≠ b) (hc : τ.cartan a b = 0)
    (hna : ∀ c : L, n₁ * xUnit τ L a c * n₁⁻¹ = xUnit τ L a c)
    (hnb : ∀ c : L, n₁ * xUnit τ L b c * n₁⁻¹ = xUnit τ L b c) :
    SsBig ℓ (subsystemGroup τ L J ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) := by
  obtain ⟨V, hV, hfix, hp, hcard⟩ := ssTw_exists_fixedPairGroup hτ hf hab hc hna hnb
  exact ssBig_of_std hh hlang (fun g hg => ssTw_mem_sub_pair ha hb (hV g hg)) hfix hp
    ((ssTw_eight_le_pow hℓ5 hf le_rfl).trans hcard)

end Transport

end CFSG.HardMathSupport.Dickson.Sec6
