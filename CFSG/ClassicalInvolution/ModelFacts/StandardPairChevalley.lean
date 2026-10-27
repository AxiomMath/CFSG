module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairModels
public import CFSG.ClassicalInvolution.WeakCT.DLLevis
public import CFSG.LieType.Steinberg.Classical.SpinPlus
public import CFSG.LieType.Steinberg.Classical.SpinOdd

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.WeakCT CFSG.LieType CFSG.LieType.RootSystem
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.Timmesfeld

theorem standardPair_of_chevalleyExtras {K : Type} [Group K] {D : UniversalRootDatum K}
    {F : Type} [Field F] [Finite F] {x : (Fin D.rank → ℤ) → F → K}
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : Steinberg.CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hE : Steinberg.ChevalleyExtras D F x C O) (hdiv : D.divisible = ∅) {i j k : Fin D.rank}
    (hij : i ≠ j) (hcij : D.cartan i j = -1) (hcji : D.cartan j i = -1)
    (hk : ¬ (3 : ℤ) ∣ D.cartan i k + 2 * D.cartan j k) :
    IsPartner D.isFiniteType (Pi.single i 1) (Pi.single j 1) ∧
      ∃ W, LinearBlockStandardPair F W (rankOne D.rootGroup i) (rankOne D.rootGroup j) := by
  refine ⟨isPartner_single_single _ hcij hcji, ?_⟩
  obtain ⟨emb, hinj, -, hx⟩ := exists_sl3Levi hE hdiv hij hcij hcji hk
  have hset : ∀ γ ∈ D.roots, (D.rootGroup γ : Set K) = Set.range (x γ) := fun γ hγ =>
    Set.ext fun g => (hE.param γ hγ).1 g
  have hΦ := isCTRootSystem D.isFiniteType D.divisible
  have hneg : ∀ l : Fin D.rank, -Pi.single l 1 ∈ D.roots := fun l =>
    CFSG.LieType.Steinberg.OfCartan.neg_mem_roots D.isFiniteType (hΦ.single_mem l)
  refine ⟨_, linearBlockStandardPair_rankOne D.rootGroup x (hset _ (hΦ.single_mem i))
    (hset _ (hneg i)) (hset _ (hΦ.single_mem j)) (hset _ (hneg j)) emb ?_ hx⟩
  rw [(MonoidHom.ker_eq_bot_iff _).mpr hinj]
  exact bot_le

section Datum

variable {F : Type} [Field F] [Finite F]

theorem standardPair_plusDatum {n : ℕ} (hn3 : 3 ≤ n) (hn : 4 ≤ n) :
    IsPartner (Spin.plusDatum n F hn3).isFiniteType
      (Pi.single (⟨0, by show 0 < n; omega⟩ : Fin (Spin.plusDatum n F hn3).rank) 1)
      (Pi.single (⟨1, by show 1 < n; omega⟩ : Fin (Spin.plusDatum n F hn3).rank) 1) ∧
    ∃ W, LinearBlockStandardPair F W
      (rankOne (Spin.plusDatum n F hn3).rootGroup ⟨0, by show 0 < n; omega⟩)
      (rankOne (Spin.plusDatum n F hn3).rootGroup ⟨1, by show 1 < n; omega⟩) := by
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan (Spin.plusDatum n F hn3).isFiniteType
    (Dv := (Spin.plusDatum n F hn3).divisible) rfl
  have hE := Steinberg.SpinPlus.chevalleyExtras hn3 O Steinberg.SpinPlus.commC
    (Steinberg.SpinPlus.commutatorFormula hn3 O)
  refine standardPair_of_chevalleyExtras hE rfl (k := ⟨2, by show 2 < n; omega⟩) ?_ ?_ ?_ ?_
  · intro h
    have := congrArg Fin.val h
    simp at this
  · show Spin.cartanD n ⟨0, by omega⟩ ⟨1, by omega⟩ = -1
    simp [Spin.cartanD, Fin.ext_iff]
    omega
  · show Spin.cartanD n ⟨1, by omega⟩ ⟨0, by omega⟩ = -1
    simp [Spin.cartanD, Fin.ext_iff]
    omega
  · show ¬ (3 : ℤ) ∣ Spin.cartanD n ⟨0, by omega⟩ ⟨2, by omega⟩ +
      2 * Spin.cartanD n ⟨1, by omega⟩ ⟨2, by omega⟩
    simp [Spin.cartanD, Fin.ext_iff]
    omega

theorem standardPair_oddDatum {n : ℕ} (hn : 3 ≤ n) :
    IsPartner (Spin.oddDatum n F).isFiniteType
      (Pi.single (⟨0, by show 0 < n; omega⟩ : Fin (Spin.oddDatum n F).rank) 1)
      (Pi.single (⟨1, by show 1 < n; omega⟩ : Fin (Spin.oddDatum n F).rank) 1) ∧
    ∃ W, LinearBlockStandardPair F W
      (rankOne (Spin.oddDatum n F).rootGroup ⟨0, by show 0 < n; omega⟩)
      (rankOne (Spin.oddDatum n F).rootGroup ⟨1, by show 1 < n; omega⟩) := by
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan (Spin.oddDatum n F).isFiniteType
    (Dv := (Spin.oddDatum n F).divisible) rfl
  have hE := Steinberg.SpinOdd.chevalleyExtras (by omega : 2 ≤ n) O Steinberg.SpinOdd.commC
    (Steinberg.SpinOdd.commutatorFormula O)
  refine standardPair_of_chevalleyExtras hE rfl (k := ⟨2, by show 2 < n; omega⟩) ?_ ?_ ?_ ?_
  · intro h
    have := congrArg Fin.val h
    simp at this
  · show Spin.cartanB n ⟨0, by omega⟩ ⟨1, by omega⟩ = -1
    simp [Spin.cartanB, Fin.ext_iff]
    omega
  · show Spin.cartanB n ⟨1, by omega⟩ ⟨0, by omega⟩ = -1
    simp [Spin.cartanB, Fin.ext_iff]
    omega
  · show ¬ (3 : ℤ) ∣ Spin.cartanB n ⟨0, by omega⟩ ⟨2, by omega⟩ +
      2 * Spin.cartanB n ⟨1, by omega⟩ ⟨2, by omega⟩
    simp [Spin.cartanB, Fin.ext_iff]
    omega

theorem standardPair_e6Datum :
    IsPartner (Steinberg.Minuscule.e6Datum F).isFiniteType
      (Pi.single (⟨0, by show 0 < 6; decide⟩ : Fin (Steinberg.Minuscule.e6Datum F).rank) 1)
      (Pi.single (⟨2, by show 2 < 6; decide⟩ : Fin (Steinberg.Minuscule.e6Datum F).rank) 1) ∧
    ∃ W, LinearBlockStandardPair F W
      (rankOne (Steinberg.Minuscule.e6Datum F).rootGroup ⟨0, by show 0 < 6; decide⟩)
      (rankOne (Steinberg.Minuscule.e6Datum F).rootGroup ⟨2, by show 2 < 6; decide⟩) := by
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan (Steinberg.Minuscule.e6Datum F).isFiniteType
    (Dv := (Steinberg.Minuscule.e6Datum F).divisible) rfl
  have hE := Steinberg.Minuscule.e6_chevalleyExtras F O _
    (Steinberg.Minuscule.e6Data_valid.commutatorFormula_commC F
      Steinberg.Minuscule.posDef_cartan_E6 _
      (Steinberg.Minuscule.roots_eq Steinberg.Minuscule.isFiniteType_cartan_E6) O)
  have hdiv : (Steinberg.Minuscule.e6Datum F).divisible = ∅ := rfl
  refine standardPair_of_chevalleyExtras hE hdiv (k := ⟨3, by show 3 < 6; decide⟩)
    ?_ ?_ ?_ ?_
  · intro h
    have := congrArg Fin.val h
    simp at this
  · show Blueprint.Chevalley.Tag.cartan .E6 ⟨0, by decide⟩ ⟨2, by decide⟩ = -1
    decide
  · show Blueprint.Chevalley.Tag.cartan .E6 ⟨2, by decide⟩ ⟨0, by decide⟩ = -1
    decide
  · show ¬ (3 : ℤ) ∣ Blueprint.Chevalley.Tag.cartan .E6 ⟨0, by decide⟩ ⟨3, by decide⟩ +
      2 * Blueprint.Chevalley.Tag.cartan .E6 ⟨2, by decide⟩ ⟨3, by decide⟩
    decide

theorem standardPair_e7Datum :
    IsPartner (Steinberg.Minuscule.e7Datum F).isFiniteType
      (Pi.single (⟨0, by show 0 < 7; decide⟩ : Fin (Steinberg.Minuscule.e7Datum F).rank) 1)
      (Pi.single (⟨2, by show 2 < 7; decide⟩ : Fin (Steinberg.Minuscule.e7Datum F).rank) 1) ∧
    ∃ W, LinearBlockStandardPair F W
      (rankOne (Steinberg.Minuscule.e7Datum F).rootGroup ⟨0, by show 0 < 7; decide⟩)
      (rankOne (Steinberg.Minuscule.e7Datum F).rootGroup ⟨2, by show 2 < 7; decide⟩) := by
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan (Steinberg.Minuscule.e7Datum F).isFiniteType
    (Dv := (Steinberg.Minuscule.e7Datum F).divisible) rfl
  have hE := Steinberg.Minuscule.e7_chevalleyExtras F O _
    (Steinberg.Minuscule.e7Data_valid.commutatorFormula_commC F
      Steinberg.Minuscule.posDef_cartan_E7 _
      (Steinberg.Minuscule.roots_eq Steinberg.Minuscule.isFiniteType_cartan_E7) O)
  have hdiv : (Steinberg.Minuscule.e7Datum F).divisible = ∅ := rfl
  refine standardPair_of_chevalleyExtras hE hdiv (k := ⟨3, by show 3 < 7; decide⟩)
    ?_ ?_ ?_ ?_
  · intro h
    have := congrArg Fin.val h
    simp at this
  · show Blueprint.Chevalley.Tag.cartan .E7 ⟨0, by decide⟩ ⟨2, by decide⟩ = -1
    decide
  · show Blueprint.Chevalley.Tag.cartan .E7 ⟨2, by decide⟩ ⟨0, by decide⟩ = -1
    decide
  · show ¬ (3 : ℤ) ∣ Blueprint.Chevalley.Tag.cartan .E7 ⟨0, by decide⟩ ⟨3, by decide⟩ +
      2 * Blueprint.Chevalley.Tag.cartan .E7 ⟨2, by decide⟩ ⟨3, by decide⟩
    decide

theorem standardPair_e8Datum :
    IsPartner (Steinberg.Adjoint.e8Datum F).isFiniteType
      (Pi.single (⟨0, by show 0 < 8; decide⟩ : Fin (Steinberg.Adjoint.e8Datum F).rank) 1)
      (Pi.single (⟨2, by show 2 < 8; decide⟩ : Fin (Steinberg.Adjoint.e8Datum F).rank) 1) ∧
    ∃ W, LinearBlockStandardPair F W
      (rankOne (Steinberg.Adjoint.e8Datum F).rootGroup ⟨0, by show 0 < 8; decide⟩)
      (rankOne (Steinberg.Adjoint.e8Datum F).rootGroup ⟨2, by show 2 < 8; decide⟩) := by
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan (Steinberg.Adjoint.e8Datum F).isFiniteType
    (Dv := (Steinberg.Adjoint.e8Datum F).divisible) rfl
  have hE := Steinberg.Adjoint.e8_chevalleyExtras F O _
    (Steinberg.Adjoint.commutatorFormula_commC Steinberg.Adjoint.e8Data_valid
      Steinberg.Adjoint.noG2_E8 _ (Steinberg.Adjoint.adjDatum_roots _ F) O)
  have hdiv : (Steinberg.Adjoint.e8Datum F).divisible = ∅ := rfl
  refine standardPair_of_chevalleyExtras hE hdiv (k := ⟨3, by show 3 < 8; decide⟩)
    ?_ ?_ ?_ ?_
  · intro h
    have := congrArg Fin.val h
    simp at this
  · show Blueprint.Chevalley.Tag.cartan .E8 ⟨0, by decide⟩ ⟨2, by decide⟩ = -1
    decide
  · show Blueprint.Chevalley.Tag.cartan .E8 ⟨2, by decide⟩ ⟨0, by decide⟩ = -1
    decide
  · show ¬ (3 : ℤ) ∣ Blueprint.Chevalley.Tag.cartan .E8 ⟨0, by decide⟩ ⟨3, by decide⟩ +
      2 * Blueprint.Chevalley.Tag.cartan .E8 ⟨2, by decide⟩ ⟨3, by decide⟩
    decide

theorem standardPair_f4Datum :
    IsPartner (Steinberg.Adjoint.f4Datum F).isFiniteType
      (Pi.single (⟨0, by show 0 < 4; decide⟩ : Fin (Steinberg.Adjoint.f4Datum F).rank) 1)
      (Pi.single (⟨1, by show 1 < 4; decide⟩ : Fin (Steinberg.Adjoint.f4Datum F).rank) 1) ∧
    ∃ W, LinearBlockStandardPair F W
      (rankOne (Steinberg.Adjoint.f4Datum F).rootGroup ⟨0, by show 0 < 4; decide⟩)
      (rankOne (Steinberg.Adjoint.f4Datum F).rootGroup ⟨1, by show 1 < 4; decide⟩) := by
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan (Steinberg.Adjoint.f4Datum F).isFiniteType
    (Dv := (Steinberg.Adjoint.f4Datum F).divisible) rfl
  obtain ⟨C, -, hC⟩ := Steinberg.Adjoint.f4_commutatorFormula F O
  have hE := Steinberg.Adjoint.f4_chevalleyExtras F O C hC
  have hdiv : (Steinberg.Adjoint.f4Datum F).divisible = ∅ := rfl
  refine standardPair_of_chevalleyExtras hE hdiv (k := ⟨2, by show 2 < 4; decide⟩)
    ?_ ?_ ?_ ?_
  · intro h
    have := congrArg Fin.val h
    simp at this
  · show Blueprint.Chevalley.Tag.cartan .F4 ⟨0, by decide⟩ ⟨1, by decide⟩ = -1
    decide
  · show Blueprint.Chevalley.Tag.cartan .F4 ⟨1, by decide⟩ ⟨0, by decide⟩ = -1
    decide
  · show ¬ (3 : ℤ) ∣ Blueprint.Chevalley.Tag.cartan .F4 ⟨0, by decide⟩ ⟨2, by decide⟩ +
      2 * Blueprint.Chevalley.Tag.cartan .F4 ⟨1, by decide⟩ ⟨2, by decide⟩
    decide

end Datum

section Tags

variable (p f : ℕ) [hp : Fact p.Prime]

theorem exists_standardPair_partner_POmegaPlus (n : ℕ)
    (hadm : StatedLieAdmissible .POmegaPlus n p f)
    {γ : Fin (modelUniv .POmegaPlus n p f hp.out).D.rank → ℤ}
    (hγ : IsLongestRoot (modelUniv .POmegaPlus n p f hp.out).D γ) :
    ∃ δ : Fin (modelUniv .POmegaPlus n p f hp.out).D.rank → ℤ,
      IsLongestRoot (modelUniv .POmegaPlus n p f hp.out).D δ ∧
      IsPartner (modelUniv .POmegaPlus n p f hp.out).D.isFiniteType γ δ ∧
      ∃ W, LinearBlockStandardPair (GaloisField p f) W
        ((modelUniv .POmegaPlus n p f hp.out).D.rootGroup γ ⊔
          (modelUniv .POmegaPlus n p f hp.out).D.rootGroup (-γ))
        ((modelUniv .POmegaPlus n p f hp.out).D.rootGroup δ ⊔
          (modelUniv .POmegaPlus n p f hp.out).D.rootGroup (-δ)) := by
  have hn : 4 ≤ n := hadm.2.2
  have hn3 : 3 ≤ n := by omega
  have hbd := hasBruhatDatum .POmegaPlus n p f hp.out trivial hadm
  have hok := cartanOK .POmegaPlus n p f hp.out trivial hadm
  have hl := isLongestRoot_single .POmegaPlus n p f hp.out trivial hadm
  revert hbd hok hl γ
  rw [modelUniv_POmegaPlus hn3]
  intro γ hγ hbd hok hl
  obtain ⟨hp01, hpair⟩ := standardPair_plusDatum (F := GaloisField p f) hn3 hn
  exact exists_standardPair_partner_of_nodes hbd hok
    (hl ⟨0, by show 0 < n; omega⟩ trivial) (hl ⟨1, by show 1 < n; omega⟩ trivial) hp01 hpair hγ

theorem exists_standardPair_partner_POmegaOdd (n : ℕ)
    (hadm : StatedLieAdmissible .POmegaOdd n p f)
    {γ : Fin (modelUniv .POmegaOdd n p f hp.out).D.rank → ℤ}
    (hγ : IsLongestRoot (modelUniv .POmegaOdd n p f hp.out).D γ) :
    ∃ δ : Fin (modelUniv .POmegaOdd n p f hp.out).D.rank → ℤ,
      IsLongestRoot (modelUniv .POmegaOdd n p f hp.out).D δ ∧
      IsPartner (modelUniv .POmegaOdd n p f hp.out).D.isFiniteType γ δ ∧
      ∃ W, LinearBlockStandardPair (GaloisField p f) W
        ((modelUniv .POmegaOdd n p f hp.out).D.rootGroup γ ⊔
          (modelUniv .POmegaOdd n p f hp.out).D.rootGroup (-γ))
        ((modelUniv .POmegaOdd n p f hp.out).D.rootGroup δ ⊔
          (modelUniv .POmegaOdd n p f hp.out).D.rootGroup (-δ)) := by
  have hn : 3 ≤ n := hadm.2.2.1
  obtain ⟨hp01, hpair⟩ := standardPair_oddDatum (F := GaloisField p f) hn
  exact exists_standardPair_partner_of_nodes
    (hasBruhatDatum .POmegaOdd n p f hp.out trivial hadm)
    (cartanOK .POmegaOdd n p f hp.out trivial hadm)
    (isLongestRoot_single .POmegaOdd n p f hp.out trivial hadm ⟨0, by show 0 < n; omega⟩
      (by show 0 + 1 < n; omega))
    (isLongestRoot_single .POmegaOdd n p f hp.out trivial hadm ⟨1, by show 1 < n; omega⟩
      (by show 1 + 1 < n; omega)) hp01 hpair hγ

theorem exists_standardPair_partner_E6 (hadm : StatedLieAdmissible .E6 0 p f)
    {γ : Fin (modelUniv .E6 0 p f hp.out).D.rank → ℤ}
    (hγ : IsLongestRoot (modelUniv .E6 0 p f hp.out).D γ) :
    ∃ δ : Fin (modelUniv .E6 0 p f hp.out).D.rank → ℤ,
      IsLongestRoot (modelUniv .E6 0 p f hp.out).D δ ∧
      IsPartner (modelUniv .E6 0 p f hp.out).D.isFiniteType γ δ ∧
      ∃ W, LinearBlockStandardPair (GaloisField p f) W
        ((modelUniv .E6 0 p f hp.out).D.rootGroup γ ⊔
          (modelUniv .E6 0 p f hp.out).D.rootGroup (-γ))
        ((modelUniv .E6 0 p f hp.out).D.rootGroup δ ⊔
          (modelUniv .E6 0 p f hp.out).D.rootGroup (-δ)) := by
  obtain ⟨hp01, hpair⟩ := standardPair_e6Datum (F := GaloisField p f)
  exact exists_standardPair_partner_of_nodes (hasBruhatDatum .E6 0 p f hp.out trivial hadm)
    (cartanOK .E6 0 p f hp.out trivial hadm)
    (isLongestRoot_single .E6 0 p f hp.out trivial hadm ⟨0, by show 0 < 6; decide⟩ trivial)
    (isLongestRoot_single .E6 0 p f hp.out trivial hadm ⟨2, by show 2 < 6; decide⟩ trivial)
    hp01 hpair hγ

theorem exists_standardPair_partner_E7 (hadm : StatedLieAdmissible .E7 0 p f)
    {γ : Fin (modelUniv .E7 0 p f hp.out).D.rank → ℤ}
    (hγ : IsLongestRoot (modelUniv .E7 0 p f hp.out).D γ) :
    ∃ δ : Fin (modelUniv .E7 0 p f hp.out).D.rank → ℤ,
      IsLongestRoot (modelUniv .E7 0 p f hp.out).D δ ∧
      IsPartner (modelUniv .E7 0 p f hp.out).D.isFiniteType γ δ ∧
      ∃ W, LinearBlockStandardPair (GaloisField p f) W
        ((modelUniv .E7 0 p f hp.out).D.rootGroup γ ⊔
          (modelUniv .E7 0 p f hp.out).D.rootGroup (-γ))
        ((modelUniv .E7 0 p f hp.out).D.rootGroup δ ⊔
          (modelUniv .E7 0 p f hp.out).D.rootGroup (-δ)) := by
  obtain ⟨hp01, hpair⟩ := standardPair_e7Datum (F := GaloisField p f)
  exact exists_standardPair_partner_of_nodes (hasBruhatDatum .E7 0 p f hp.out trivial hadm)
    (cartanOK .E7 0 p f hp.out trivial hadm)
    (isLongestRoot_single .E7 0 p f hp.out trivial hadm ⟨0, by show 0 < 7; decide⟩ trivial)
    (isLongestRoot_single .E7 0 p f hp.out trivial hadm ⟨2, by show 2 < 7; decide⟩ trivial)
    hp01 hpair hγ

theorem exists_standardPair_partner_E8 (hadm : StatedLieAdmissible .E8 0 p f)
    {γ : Fin (modelUniv .E8 0 p f hp.out).D.rank → ℤ}
    (hγ : IsLongestRoot (modelUniv .E8 0 p f hp.out).D γ) :
    ∃ δ : Fin (modelUniv .E8 0 p f hp.out).D.rank → ℤ,
      IsLongestRoot (modelUniv .E8 0 p f hp.out).D δ ∧
      IsPartner (modelUniv .E8 0 p f hp.out).D.isFiniteType γ δ ∧
      ∃ W, LinearBlockStandardPair (GaloisField p f) W
        ((modelUniv .E8 0 p f hp.out).D.rootGroup γ ⊔
          (modelUniv .E8 0 p f hp.out).D.rootGroup (-γ))
        ((modelUniv .E8 0 p f hp.out).D.rootGroup δ ⊔
          (modelUniv .E8 0 p f hp.out).D.rootGroup (-δ)) := by
  obtain ⟨hp01, hpair⟩ := standardPair_e8Datum (F := GaloisField p f)
  exact exists_standardPair_partner_of_nodes (hasBruhatDatum .E8 0 p f hp.out trivial hadm)
    (cartanOK .E8 0 p f hp.out trivial hadm)
    (isLongestRoot_single .E8 0 p f hp.out trivial hadm ⟨0, by show 0 < 8; decide⟩ trivial)
    (isLongestRoot_single .E8 0 p f hp.out trivial hadm ⟨2, by show 2 < 8; decide⟩ trivial)
    hp01 hpair hγ

theorem exists_standardPair_partner_F4 (hadm : StatedLieAdmissible .F4 0 p f)
    {γ : Fin (modelUniv .F4 0 p f hp.out).D.rank → ℤ}
    (hγ : IsLongestRoot (modelUniv .F4 0 p f hp.out).D γ) :
    ∃ δ : Fin (modelUniv .F4 0 p f hp.out).D.rank → ℤ,
      IsLongestRoot (modelUniv .F4 0 p f hp.out).D δ ∧
      IsPartner (modelUniv .F4 0 p f hp.out).D.isFiniteType γ δ ∧
      ∃ W, LinearBlockStandardPair (GaloisField p f) W
        ((modelUniv .F4 0 p f hp.out).D.rootGroup γ ⊔
          (modelUniv .F4 0 p f hp.out).D.rootGroup (-γ))
        ((modelUniv .F4 0 p f hp.out).D.rootGroup δ ⊔
          (modelUniv .F4 0 p f hp.out).D.rootGroup (-δ)) := by
  obtain ⟨hp01, hpair⟩ := standardPair_f4Datum (F := GaloisField p f)
  exact exists_standardPair_partner_of_nodes (hasBruhatDatum .F4 0 p f hp.out trivial hadm)
    (cartanOK .F4 0 p f hp.out trivial hadm)
    (isLongestRoot_single .F4 0 p f hp.out trivial hadm ⟨0, by show 0 < 4; decide⟩
      (by show 0 < 2; decide))
    (isLongestRoot_single .F4 0 p f hp.out trivial hadm ⟨1, by show 1 < 4; decide⟩
      (by show 1 < 2; decide)) hp01 hpair hγ

end Tags

end CFSG.ClassicalInvolution.ModelFacts
