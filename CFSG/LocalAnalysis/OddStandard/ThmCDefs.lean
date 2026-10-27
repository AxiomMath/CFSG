module

public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisInputs

public section

namespace CFSG.OddStandard.ThmC

open CFSG Subgroup CFSG.GH74.GLS.Bg.TwoGroups

@[expose] def Concl (X : Type) [Group X] [Finite X] (T : Sylow 2 X) : Prop :=
  letI : (pCore 2 X).Normal := pCore_normal
  centralizer (pCore 2 X : Set X) ≤ pCore 2 X ∧
      ((pCore 2 X = T ∧ (T : Subgroup X).index ∣ 9 ∧
          ∀ B : Subgroup X, B ≤ T → (∀ b ∈ B, b * b = 1) →
            (∀ b ∈ B, ∀ c ∈ B, b * c = c * b) → Nat.card B = 16 → B.Normal) ∨
        ((pCore 2 X : Subgroup X) ≤ T ∧ Nat.card (pCore 2 X) = 16 ∧
          (∀ b ∈ pCore 2 X, b * b = 1) ∧ (∀ b ∈ pCore 2 X, ∀ c ∈ pCore 2 X, b * c = c * b) ∧
          (Nonempty (X ⧸ pCore 2 X ≃* alternatingGroup (Fin 5)) ∨
            Nonempty (X ⧸ pCore 2 X ≃* Multiplicative (ZMod 3) × alternatingGroup (Fin 5))) ∧
          ∀ u ∈ pCore 2 X, ∀ v ∈ pCore 2 X, u ≠ 1 → v ≠ 1 → ∃ g : X, g⁻¹ * u * g = v))

@[expose] def O2Structure : Prop :=
  ∀ (X : Type) [Group X] [Finite X], pPrimeCore 2 X = ⊥ → pCore 2 X ≠ ⊥ →
    ∀ T : Sylow 2 X, Nonempty ((T : Subgroup X) ≃* SylSL3_4) → Concl X T

structure TFacts : Prop where
  elem16 : ∃ E : Subgroup SylSL3_4, CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 16
  gen4 : ∀ P : Subgroup SylSL3_4,
    ∃ s : Finset SylSL3_4, s.card ≤ 4 ∧ Subgroup.closure (s : Set SylSL3_4) = P

@[expose] def GH74Concl (G : Type) [Group G] : Prop :=
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      (CFSG.Blueprint.LieModel G .G2 0 p f ∨ CFSG.Blueprint.LieModel G .trialityD4 0 p f)) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ CFSG.Blueprint.LieModel G .PSp 2 p f) ∨
    (∃ f : ℕ, CFSG.Blueprint.LieModel G .twistedG2 0 3 f) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 8 ≠ 1 ∧
      CFSG.Blueprint.LieModel G .PSL 4 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 8 ≠ 7 ∧
      CFSG.Blueprint.LieModel G .PSU 4 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ^ f % 4 = 3 ∧ CFSG.Blueprint.LieModel G .PSL 5 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ^ f % 4 = 1 ∧ CFSG.Blueprint.LieModel G .PSU 5 p f) ∨
    (CFSG.Blueprint.LieModel G .PSL 2 2 3 ∨ CFSG.Blueprint.LieModel G .PSL 2 2 4 ∨
      CFSG.Blueprint.LieModel G .PSL 3 2 2 ∨ CFSG.Blueprint.LieModel G .twistedB2 0 2 3) ∨
    (∃ n : ℕ, 8 ≤ n ∧ n ≤ 11 ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨
    (CFSG.Blueprint.NativeSporadic.IsSporadic G .M12 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic G .M22 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic G .M23 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic G .J1 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic G .J2 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic G .J3 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic G .McL ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic G .Ly)

@[expose] def SylowComparison : Prop :=
  ∀ (K : Type) [Group K] [Finite K] [IsSimpleGroup K], GH74Concl K →
    ∀ T : Sylow 2 K, Nonempty ((T : Subgroup K) ≃* SylSL3_4) →
      CFSG.Blueprint.LieModel K .PSL 3 2 2

@[expose] def SimpleCase : Prop :=
  ∀ (K : Type) [Group K] [Finite K] [IsSimpleGroup K], (∃ a b : K, a * b ≠ b * a) →
    ∀ T : Sylow 2 K, Nonempty ((T : Subgroup K) ≃* SylSL3_4) →
      CFSG.Blueprint.LieModel K .PSL 3 2 2

@[expose] def NormalSimpleCore : Prop :=
  ∀ (X : Type) [Group X] [Finite X], pPrimeCore 2 X = ⊥ → pCore 2 X = ⊥ →
    ∀ T : Sylow 2 X, Nonempty ((T : Subgroup X) ≃* SylSL3_4) →
      ∃ K : Subgroup X, K.Normal ∧ IsSimpleGroup K ∧ (T : Subgroup X) ≤ K

@[expose] def ThmCFull : Prop :=
  ∀ (X : Type) [Group X] [Finite X], pPrimeCore 2 X = ⊥ →
    ∀ T : Sylow 2 X, Nonempty ((T : Subgroup X) ≃* SylSL3_4) →
      (pCore 2 X ≠ ⊥ ∧ Concl X T) ∨
      (pCore 2 X = ⊥ ∧ ∃ K : Subgroup X, K.Normal ∧ CFSG.Blueprint.LieModel K .PSL 3 2 2 ∧
          (T : Subgroup X) ≤ K ∧ K.index ∣ 3)

@[expose] def L34IndexThree : Prop :=
  ∀ (X : Type) [Group X] [Finite X], pPrimeCore 2 X = ⊥ →
    ∀ K : Subgroup X, K.Normal → CFSG.Blueprint.LieModel K .PSL 3 2 2 →
      ∀ T : Sylow 2 X, (T : Subgroup X) ≤ K → K.index ∣ 3

@[expose] def L34OneClass : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), K.Normal →
    CFSG.Blueprint.LieModel K .PSL 3 2 2 → K.index ∣ 3 →
      ∀ u v : X, orderOf u = 2 → orderOf v = 2 → IsConj u v

@[expose] def ConclTwoClasses : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Sylow 2 X), Nonempty ((T : Subgroup X) ≃* SylSL3_4) →
    Concl X T → ∃ u v : X, orderOf u = 2 ∧ orderOf v = 2 ∧ ¬ IsConj u v

theorem three_le_twoRank {K : Type} [Group K] [Finite K] (hT : TFacts) (T : Sylow 2 K)
    (e : (T : Subgroup K) ≃* SylSL3_4) : 3 ≤ CFSG.Open.twoRank K := by
  obtain ⟨E, ⟨hcomm, hsq⟩, hcard⟩ := hT.elem16
  set f : SylSL3_4 →* K := (T : Subgroup K).subtype.comp e.symm.toMonoidHom with hf
  have hinj : Function.Injective f := by
    intro x y hxy
    have h1 : e.symm x = e.symm y := Subtype.ext hxy
    exact e.symm.injective h1
  set EK : Subgroup K := E.map f with hEK
  have hcardK : Nat.card EK = 2 ^ 4 := by
    rw [hEK, Subgroup.card_map_of_injective hinj, hcard]; norm_num
  have hKe : CFSG.Open.IsElemAbelian 2 EK := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a', ha', ha⟩ := a.2
      obtain ⟨b', hb', hb⟩ := b.2
      apply Subtype.ext
      show (a : K) * b = b * a
      rw [← ha, ← hb, ← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val (hcomm.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩)
    · obtain ⟨x', hx', rfl⟩ := hx
      rw [← map_pow]
      have := hsq x' hx'
      rw [this, map_one]
  have hmem : 4 ∈ {k | ∃ E : Subgroup K, E ≤ (⊤ : Subgroup K) ∧ CFSG.Open.IsElemAbelian 2 E ∧
      Nat.card E = 2 ^ k} := ⟨EK, le_top, hKe, hcardK⟩
  have hbdd : BddAbove {k | ∃ E : Subgroup K, E ≤ (⊤ : Subgroup K) ∧
      CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k} := by
    refine ⟨Nat.card K, ?_⟩
    rintro k ⟨E, -, -, hE⟩
    have h1 : 2 ^ k ≤ Nat.card K := by
      rw [← hE]; exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card E)
    exact (Nat.lt_pow_self (by norm_num : 1 < 2)).le.trans h1
  exact le_trans (by norm_num) (le_csSup hbdd hmem)

theorem gen4_of_sylow {K : Type} [Group K] [Finite K] (hT : TFacts) (T : Sylow 2 K)
    (e : (T : Subgroup K) ≃* SylSL3_4) :
    ∀ P : Subgroup K, IsPGroup 2 P →
      ∃ s : Finset K, s.card ≤ 4 ∧ Subgroup.closure (s : Set K) = P := by
  classical
  intro P hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T', hPT'⟩ := hP.exists_le_sylow
  let e' : (T' : Subgroup K) ≃* SylSL3_4 := (Sylow.equiv T' T).trans e
  set f : SylSL3_4 →* K := (T' : Subgroup K).subtype.comp e'.symm.toMonoidHom with hf
  set Q : Subgroup SylSL3_4 := (P.subgroupOf (T' : Subgroup K)).map e'.toMonoidHom with hQ
  obtain ⟨s, hs, hsQ⟩ := hT.gen4 Q
  refine ⟨s.image f, (Finset.card_image_le).trans hs, ?_⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, hsQ, hQ, Subgroup.map_map]
  have h1 : f.comp e'.toMonoidHom = (T' : Subgroup K).subtype := by
    ext x; simp [hf]
  rw [h1, Subgroup.subgroupOf_map_subtype]
  exact inf_eq_left.2 hPT'

theorem T_nonabelian : ∃ u v : SylSL3_4, u * v ≠ v * u := by
  refine ⟨⟨1, 0, 0⟩, ⟨0, 1, 0⟩, fun h => ?_⟩
  have := congrArg UT3.c h
  simp [UT3.mul_def] at this

theorem simple_core_data {X : Type} [Group X] {K : Subgroup X} {T : Sylow 2 X}
    (hTK : (T : Subgroup X) ≤ K) (e : (T : Subgroup X) ≃* SylSL3_4) :
    (∃ a b : K, a * b ≠ b * a) ∧
      Nonempty (((T.subtype hTK : Sylow 2 K) : Subgroup K) ≃* SylSL3_4) := by
  refine ⟨?_, ⟨(Subgroup.subgroupOfEquivOfLe hTK).trans e⟩⟩
  obtain ⟨x, y, hxy⟩ := T_nonabelian
  refine ⟨⟨(e.symm x : X), hTK (e.symm x).2⟩, ⟨(e.symm y : X), hTK (e.symm y).2⟩, fun h => hxy ?_⟩
  have h1 : (e.symm x : X) * (e.symm y : X) = (e.symm y : X) * (e.symm x : X) :=
    congrArg Subtype.val h
  have h2 : e.symm x * e.symm y = e.symm y * e.symm x := Subtype.ext h1
  have h3 : e.symm (x * y) = e.symm (y * x) := by rw [map_mul, map_mul]; exact h2
  exact e.symm.injective h3

theorem thmCFull_of_route (h1 : O2Structure) (hN : NormalSimpleCore) (hS : SimpleCase)
    (hL : L34IndexThree) : ThmCFull := by
  intro X _ _ hO T hT
  by_cases h : pCore 2 X = ⊥
  · right
    refine ⟨h, ?_⟩
    obtain ⟨K, hKn, hKs, hTK⟩ := hN X hO h T hT
    obtain ⟨e⟩ := hT
    have : IsSimpleGroup K := hKs
    obtain ⟨hnonab, hTKiso⟩ := simple_core_data hTK e
    have hLie := hS K hnonab (T.subtype hTK) hTKiso
    exact ⟨K, hKn, hLie, hTK, hL X hO K hKn hLie T hTK⟩
  · exact Or.inl ⟨h, h1 X hO h T hT⟩

theorem leaf_of_full (hF : ThmCFull) (h1 : L34OneClass) :
    CFSG.ComponentClassification.GHarris.GorensteinHaradaThmCInput := by
  intro X _ _ hO T hT htwo
  rcases hF X hO T hT with ⟨-, hC⟩ | ⟨-, K, hKn, hKL, -, hidx⟩
  · exact hC
  · exfalso
    obtain ⟨u, v, hu, hv, hnc⟩ := htwo
    exact hnc (h1 X K hKn hKL hidx u v hu hv)

theorem onan_use_of_full (hF : ThmCFull) (hc : ConclTwoClasses) {X : Type} [Group X] [Finite X]
    (hO : pPrimeCore 2 X = ⊥) (T : Sylow 2 X) (hT : Nonempty ((T : Subgroup X) ≃* SylSL3_4))
    (hone : ∀ u v : X, orderOf u = 2 → orderOf v = 2 → IsConj u v) :
    ∃ K : Subgroup X, K.Normal ∧ CFSG.Blueprint.LieModel K .PSL 3 2 2 ∧
      (T : Subgroup X) ≤ K ∧ K.index ∣ 3 := by
  rcases hF X hO T hT with ⟨-, hC⟩ | ⟨-, K, hKn, hKL, hTK, hidx⟩
  · exfalso
    obtain ⟨u, v, hu, hv, hnc⟩ := hc X T hT hC
    exact hnc (hone u v hu hv)
  · exact ⟨K, hKn, hKL, hTK, hidx⟩

end CFSG.OddStandard.ThmC
