module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltTA
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltPerm
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltHypII

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.ABGLocalTools
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoSporadic CFSG.ComponentClassification.RankTwoHypIIY
  CFSG.ComponentClassification.RankTwoClassical
  CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull

@[expose] noncomputable def rootVP (n : ℕ) : Subgroup (Perm (Fin n)) :=
  (rootV n).map (alternatingGroup (Fin n)).subtype

@[expose] noncomputable def rootAltP (n : ℕ) : Subgroup (Perm (Fin n)) :=
  (rootAlt n).map (alternatingGroup (Fin n)).subtype

theorem viaEmbeddingHom_mem_alternatingGroup' {n : ℕ} (ι : Fin 4 ↪ Fin n) {k : Perm (Fin 4)}
    (hk : k ∈ alternatingGroup (Fin 4)) : viaEmbeddingHom ι k ∈ alternatingGroup (Fin n) := by
  rw [mem_alternatingGroup, sign_viaEmbeddingHom]
  exact hk

theorem rootVP_eq {n : ℕ} (h : 4 ≤ n) : rootVP n = kleinFour.map (viaEmbeddingHom (fourEmb h)) := by
  ext σ
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    obtain ⟨k, hk, hkτ⟩ := (mem_rootV_iff h τ).mp hτ
    exact ⟨k, hk, hkτ⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨⟨_, viaEmbeddingHom_mem_alternatingGroup' _ (kleinFour_le_alternatingGroup hk)⟩, ?_, rfl⟩
    exact (mem_rootV_iff h _).mpr ⟨k, hk, rfl⟩

theorem rootAltP_eq {n : ℕ} (h : 4 ≤ n) :
    rootAltP n = (alternatingGroup (Fin 4)).map (viaEmbeddingHom (fourEmb h)) := by
  ext σ
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    obtain ⟨k, hk, hkτ⟩ := (mem_rootAlt_iff h τ).mp hτ
    exact ⟨k, hk, hkτ⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨⟨_, viaEmbeddingHom_mem_alternatingGroup' _ hk⟩, ?_, rfl⟩
    exact (mem_rootAlt_iff h _).mpr ⟨k, hk, rfl⟩

section Transport

variable {G : Type} [Group G] {W : Type*} [Group W]

@[expose] def conjN (A : Subgroup G) (g : G) :
    normalizer (rightConjugate A g : Set G) →* normalizer (A : Set G) where
  toFun y := ⟨g * y * g⁻¹, (mem_normalizer_rightConjugate_iff A g y).mp y.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem conjN_coe (A : Subgroup G) (g : G) (y : normalizer (rightConjugate A g : Set G)) :
    ((conjN A g y : normalizer (A : Set G)) : G) = g * y * g⁻¹ :=
  rfl

theorem isActionHom_comp_conjN {A : Subgroup G} {X : Subgroup W} {ψ : normalizer (A : Set G) →* W}
    (hψ : IsActionHom A X ψ) (g : G) : IsActionHom (rightConjugate A g) X (ψ.comp (conjN A g)) where
  map_mem b hb := by
    have hb' : g * b * g⁻¹ ∈ A := (mem_rightConjugate_iff A g b).mp hb
    have := hψ.map_mem _ hb'
    exact this
  exists_eq x hx := by
    obtain ⟨a, ha, hax⟩ := hψ.exists_eq x hx
    refine ⟨g⁻¹ * a * g, (mem_rightConjugate_iff A g _).mpr (by group; exact ha), ?_⟩
    rw [MonoidHom.comp_apply, ← hax]
    congr 1
    apply Subtype.ext
    rw [conjN_coe]
    group
  eq_one_iff y := by
    rw [MonoidHom.comp_apply, hψ.eq_one_iff, conjN_coe, centralizer_rightConjugate,
      mem_rightConjugate_iff]

@[expose] def conjNInv (A : Subgroup G) (g : G) :
    normalizer (A : Set G) →* normalizer (rightConjugate A g : Set G) where
  toFun a := ⟨g⁻¹ * a * g, by
    rw [mem_normalizer_rightConjugate_iff]
    simp [mul_assoc]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem conjNInv_coe (A : Subgroup G) (g : G) (a : normalizer (A : Set G)) :
    ((conjNInv A g a : normalizer (rightConjugate A g : Set G)) : G) = g⁻¹ * a * g :=
  rfl

theorem isActionHom_comp_conjNInv {A : Subgroup G} {X : Subgroup W} {g : G}
    {ψ : normalizer (rightConjugate A g : Set G) →* W} (hψ : IsActionHom (rightConjugate A g) X ψ) :
    IsActionHom A X (ψ.comp (conjNInv A g)) where
  map_mem a ha := by
    have hb : g⁻¹ * a * g ∈ rightConjugate A g := by
      rw [mem_rightConjugate_iff]
      simpa [mul_assoc] using ha
    exact hψ.map_mem _ hb
  exists_eq x hx := by
    obtain ⟨b, hb, hbx⟩ := hψ.exists_eq x hx
    refine ⟨g * b * g⁻¹, (mem_rightConjugate_iff A g b).mp hb, ?_⟩
    rw [MonoidHom.comp_apply, ← hbx]
    congr 1
    apply Subtype.ext
    rw [conjNInv_coe]
    group
  eq_one_iff y := by
    rw [MonoidHom.comp_apply, hψ.eq_one_iff, conjNInv_coe, centralizer_rightConjugate,
      mem_rightConjugate_iff]
    constructor
    · intro h
      simpa [mul_assoc] using h
    · intro h
      simpa [mul_assoc] using h

theorem isActionHom_conj {A : Subgroup G} {n : ℕ} {ψ : normalizer (A : Set G) →* Perm (Fin n)}
    (hψ : IsActionHom A (alternatingGroup (Fin n)) ψ) (σ : Perm (Fin n)) :
    IsActionHom A (alternatingGroup (Fin n)) ((MulAut.conj σ).toMonoidHom.comp ψ) where
  map_mem a ha := by
    have h := hψ.map_mem a ha
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (alternatingGroup.normal (α := Fin n)).conj_mem _ h σ
  exists_eq x hx := by
    obtain ⟨a, ha, hax⟩ := hψ.exists_eq (σ⁻¹ * x * σ)
      (by simpa using (alternatingGroup.normal (α := Fin n)).conj_mem _ hx σ⁻¹)
    refine ⟨a, ha, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hax]
    group
  eq_one_iff y := by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hψ.eq_one_iff]
    constructor
    · intro h
      have : ψ y = σ⁻¹ * (σ * ψ y * σ⁻¹) * σ := by group
      rw [this, h]
      group
    · intro h
      rw [h]
      group

theorem map_conj_comp {A T : Subgroup G} {n : ℕ} (ψ : normalizer (A : Set G) →* Perm (Fin n))
    (σ : Perm (Fin n)) :
    (T.subgroupOf (normalizer (A : Set G))).map ((MulAut.conj σ).toMonoidHom.comp ψ) =
      ((T.subgroupOf (normalizer (A : Set G))).map ψ).map (MulAut.conj σ).toMonoidHom :=
  (Subgroup.map_map _ _ _).symm

theorem center_rightConjugate_eq_bot {A : Subgroup G} (hZ : center ↥A = ⊥) (g : G) :
    center ↥(rightConjugate A g) = ⊥ := by
  let e : ↥A ≃* ↥(rightConjugate A g) :=
    A.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
  rw [← Subgroup.map_center_eq e, hZ, Subgroup.map_bot]

end Transport

variable {G : Type} [Group G] [Finite G]

structure NormPair (A R T : Subgroup G) (g : G) (n : ℕ) where
  ψA : normalizer (A : Set G) →* Perm (Fin n)
  ψB : normalizer (rightConjugate A g : Set G) →* Perm (Fin n)
  hψA : IsActionHom A (alternatingGroup (Fin n)) ψA
  hψB : IsActionHom (rightConjugate A g) (alternatingGroup (Fin n)) ψB
  le_A : T ≤ A
  le_B : R ≤ rightConjugate A g
  map_T : (T.subgroupOf (normalizer (A : Set G))).map ψA = rootVP n
  map_R : (R.subgroupOf (normalizer (rightConjugate A g : Set G))).map ψB = rootVP n
  center_eq_bot : center ↥A = ⊥

section Exists

variable {A R T : Subgroup G} {g : G}
variable (hc : Sec3 A R T g) (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34)
  (h2 : Asc76Theorem2) (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
include hc h32 h4 h34 h2 hOut

theorem exists_normalized {n : ℕ} (hn : 7 ≤ n) {ψ : normalizer (A : Set G) →* Perm (Fin n)}
    (hψ : IsActionHom A (alternatingGroup (Fin n)) ψ) :
    ∃ ψ' : normalizer (A : Set G) →* Perm (Fin n), IsActionHom A (alternatingGroup (Fin n)) ψ' ∧
      (T.subgroupOf (normalizer (A : Set G))).map ψ' = rootVP n := by
  obtain ⟨ι, hι⟩ := exists_eq_kleinFour_map hc h32 h4 h34 h2 hOut hn hψ
  obtain ⟨σ, hσ⟩ := exists_perm_comp_eq ι (fourEmb (by omega : 4 ≤ n))
  refine ⟨_, isActionHom_conj hψ σ, ?_⟩
  rw [map_conj_comp, hι, Subgroup.map_map, rootVP_eq (by omega : 4 ≤ n)]
  congr 1
  ext k : 1
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact conj_viaEmbeddingHom_of_comp ι hσ k

theorem exists_normPair {n : ℕ} (hn : 7 ≤ n) (e : ↥A ⧸ center ↥A ≃* alternatingGroup (Fin n))
    (hZ : center ↥A = ⊥) : Nonempty (NormPair A R T g n) := by
  obtain ⟨ψ, hψ⟩ := exists_isActionHom (autModel_perm (Or.inr hn)) hc.hyp.standard.1.1 e
  obtain ⟨ψ₁, hψ₁, hT⟩ := exists_normalized hc h32 h4 h34 h2 hOut hn hψ
  obtain ⟨ψ₂, hψ₂, hR⟩ := exists_normalized hc.swap h32 h4 h34 h2 hOut hn hψ
  have hTA := le_of_center_eq_bot hc h32 h4 h34 h2 hOut hn hψ hZ
  have hRA := le_of_center_eq_bot hc.swap h32 h4 h34 h2 hOut hn hψ hZ
  refine ⟨⟨ψ₁, ψ₂.comp (conjN A g), hψ₁, isActionHom_comp_conjN hψ₂ g, hTA, ?_, hT, ?_, hZ⟩⟩
  · intro r hr
    rw [mem_rightConjugate_iff]
    apply hRA
    rw [mem_rightConjugate_iff]
    simpa [mul_assoc] using hr
  · rw [← hR]
    ext σ
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨conjN A g y, ?_, rfl⟩
      show g * (y : G) * g⁻¹ ∈ rightConjugate R g⁻¹
      rw [mem_rightConjugate_iff]
      simpa [mul_assoc] using (mem_subgroupOf.mp hy)
    · rintro ⟨x, hx, rfl⟩
      have hx' : g⁻¹ * (x : G) * g ∈ R := by
        have := (mem_rightConjugate_iff R g⁻¹ x).mp hx
        simpa using this
      have hxN : g⁻¹ * (x : G) * g ∈ normalizer (rightConjugate A g : Set G) := by
        rw [mem_normalizer_rightConjugate_iff]
        simp [mul_assoc]
      refine ⟨⟨_, hxN⟩, hx', ?_⟩
      rw [MonoidHom.comp_apply]
      congr 1
      apply Subtype.ext
      rw [conjN_coe]
      group

end Exists

namespace NormPair

variable {A R T : Subgroup G} {g : G} {n : ℕ} (np : NormPair A R T g n)
include np

omit [Finite G] in
theorem center_B_eq_bot : center ↥(rightConjugate A g) = ⊥ :=
  center_rightConjugate_eq_bot np.center_eq_bot g

omit [Finite G] in
theorem injA {u v : normalizer (A : Set G)} (hu : (u : G) ∈ A) (hv : (v : G) ∈ A)
    (huv : np.ψA u = np.ψA v) : u = v := by
  have hk : (restrictA np.hψA).ker = ⊥ := by rw [ker_restrictA, np.center_eq_bot]
  have h := (MonoidHom.ker_eq_bot_iff _).mp hk (a₁ := ⟨u, hu⟩) (a₂ := ⟨v, hv⟩) (Subtype.ext huv)
  have h' : (u : G) = v := congrArg (fun z : ↥A => (z : G)) h
  exact Subtype.ext h'

omit [Finite G] in
theorem injB {u v : normalizer (rightConjugate A g : Set G)} (hu : (u : G) ∈ rightConjugate A g)
    (hv : (v : G) ∈ rightConjugate A g) (huv : np.ψB u = np.ψB v) : u = v := by
  have hk : (restrictA np.hψB).ker = ⊥ := by rw [ker_restrictA, np.center_B_eq_bot]
  have h := (MonoidHom.ker_eq_bot_iff _).mp hk (a₁ := ⟨u, hu⟩) (a₂ := ⟨v, hv⟩) (Subtype.ext huv)
  have h' : (u : G) = v := congrArg (fun z : ↥(rightConjugate A g) => (z : G)) h
  exact Subtype.ext h'

@[expose] noncomputable def swap : NormPair A (rightConjugate T g⁻¹) (rightConjugate R g⁻¹) g⁻¹ n where
  ψA := np.ψB.comp (conjNInv A g)
  ψB := np.ψA.comp (conjN A g⁻¹)
  hψA := isActionHom_comp_conjNInv np.hψB
  hψB := isActionHom_comp_conjN np.hψA g⁻¹
  le_A := by
    intro x hx
    rw [mem_rightConjugate_iff] at hx
    have := (mem_rightConjugate_iff A g _).mp (np.le_B hx)
    simpa [mul_assoc] using this
  le_B := by
    intro x hx
    rw [mem_rightConjugate_iff] at hx ⊢
    exact np.le_A hx
  map_T := by
    rw [← np.map_R]
    ext σ
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : g⁻¹ * (x : G) * g ∈ R := by
        have := (mem_rightConjugate_iff R g⁻¹ x).mp hx
        simpa using this
      exact ⟨conjNInv A g x, hx', rfl⟩
    · rintro ⟨y, hy, rfl⟩
      have hyA : g * (y : G) * g⁻¹ ∈ normalizer (A : Set G) :=
        (mem_normalizer_rightConjugate_iff A g y).mp y.2
      refine ⟨⟨_, hyA⟩, ?_, ?_⟩
      · show g * (y : G) * g⁻¹ ∈ rightConjugate R g⁻¹
        rw [mem_rightConjugate_iff]
        simpa [mul_assoc] using (mem_subgroupOf.mp hy)
      · simp only [MonoidHom.comp_apply]
        congr 1
        apply Subtype.ext
        rw [conjNInv_coe]
        group
  map_R := by
    rw [← np.map_T]
    ext σ
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨conjN A g⁻¹ y, ?_, rfl⟩
      show g⁻¹ * (y : G) * g⁻¹⁻¹ ∈ T
      have := (mem_rightConjugate_iff T g⁻¹ y).mp hy
      simpa using this
    · rintro ⟨x, hx, rfl⟩
      have hxN : g * (x : G) * g⁻¹ ∈ normalizer (rightConjugate A g⁻¹ : Set G) := by
        rw [mem_normalizer_rightConjugate_iff]
        simp [mul_assoc]
      refine ⟨⟨_, hxN⟩, ?_, ?_⟩
      · show g * (x : G) * g⁻¹ ∈ rightConjugate T g⁻¹
        rw [mem_rightConjugate_iff]
        simpa [mul_assoc] using (mem_subgroupOf.mp hx)
      · simp only [MonoidHom.comp_apply]
        congr 1
        apply Subtype.ext
        rw [conjN_coe]
        group
  center_eq_bot := np.center_eq_bot

omit [Finite G] in
theorem swap_ψA (a : normalizer (A : Set G)) : np.swap.ψA a = np.ψB (conjNInv A g a) :=
  rfl

omit [Finite G] in
theorem swap_ψB (y : normalizer (rightConjugate A g⁻¹ : Set G)) :
    np.swap.ψB y = np.ψA (conjN A g⁻¹ y) :=
  rfl

end NormPair

end CFSG.ComponentClassification.RankTwoAlt
