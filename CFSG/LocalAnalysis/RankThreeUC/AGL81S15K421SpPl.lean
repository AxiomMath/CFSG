module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421SpB
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421SpCW

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421SpProof

open Matrix K421MonoProof K421OrbProof K421LinProof K421CGProof K421SpCWProof

section Hom

variable {F : Type} [Field F] [CharP F 2]

@[expose] def spHom {G : Type} [Group G] (M : G → Matrix Idx Idx F)
    (hmul : ∀ g h, M (g * h) = M g * M h) (hone : M 1 = 1)
    (hs : ∀ g, (M g)ᵀ * JF F * M g = JF F) : G →* ↥(SpI F) where
  toFun g := ⟨⟨M g, M g⁻¹, by rw [← hmul, mul_inv_cancel, hone],
    by rw [← hmul, inv_mul_cancel, hone]⟩, hs g⟩
  map_one' := Subtype.ext (Units.ext hone)
  map_mul' g h := Subtype.ext (Units.ext (hmul g h))

theorem sl2_symp (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    (g : Matrix (Fin 2) (Fin 2) F)ᵀ * !![0, 1; 1, 0] * (g : Matrix (Fin 2) (Fin 2) F) =
      !![0, 1; 1, 0] := by
  have h2 := two_eq_zero_F F
  have hdet : (g : Matrix (Fin 2) (Fin 2) F).det = 1 := g.2
  rw [Matrix.det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination ((g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 0) * h2
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination hdet + ((g : Matrix (Fin 2) (Fin 2) F) 0 1 * (g : Matrix (Fin 2) (Fin 2) F) 1 0) * h2
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination hdet + ((g : Matrix (Fin 2) (Fin 2) F) 0 1 * (g : Matrix (Fin 2) (Fin 2) F) 1 0) * h2
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination ((g : Matrix (Fin 2) (Fin 2) F) 0 1 * (g : Matrix (Fin 2) (Fin 2) F) 1 1) * h2

end Hom

section Place

variable {F : Type} [Field F] [CharP F 2]

@[expose] def bd3 (a b c : Matrix (Fin 2) (Fin 2) F) : Matrix Idx Idx F := bd ![a, b, c]

theorem bd3_mul (a b c a' b' c' : Matrix (Fin 2) (Fin 2) F) :
    bd3 a b c * bd3 a' b' c' = bd3 (a * a') (b * b') (c * c') := by
  unfold bd3
  rw [bd_mul]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem bd3_one : bd3 (1 : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
  unfold bd3
  rw [← bd_one]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem bd3_transpose (a b c : Matrix (Fin 2) (Fin 2) F) : (bd3 a b c)ᵀ = bd3 aᵀ bᵀ cᵀ := by
  unfold bd3
  rw [bd_transpose]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem bd3_inj {a b c a' b' c' : Matrix (Fin 2) (Fin 2) F} (h : bd3 a b c = bd3 a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  have h1 := bd_injective h
  exact ⟨congrFun h1 0, congrFun h1 1, congrFun h1 2⟩

theorem JF_eq_bd3 : JF F = bd3 !![0, 1; 1, 0] !![0, 1; 1, 0] !![0, 1; 1, 0] := by
  rw [JF_eq_bd]
  unfold bd3
  congr 1
  funext j
  fin_cases j <;> rfl

variable {G : Type} [Group G]

@[expose] def placeHom (f0 f1 f2 : G →* Matrix.SpecialLinearGroup (Fin 2) F) : G →* ↥(SpI F) :=
  spHom (fun g => bd3 (f0 g : Matrix (Fin 2) (Fin 2) F) (f1 g) (f2 g))
    (fun g h => by simp only [map_mul, Matrix.SpecialLinearGroup.coe_mul, bd3_mul])
    (by simp only [map_one, Matrix.SpecialLinearGroup.coe_one, bd3_one])
    (fun g => by
      rw [bd3_transpose, JF_eq_bd3, bd3_mul, bd3_mul, sl2_symp, sl2_symp, sl2_symp])

theorem placeHom_val (f0 f1 f2 : G →* Matrix.SpecialLinearGroup (Fin 2) F) (g : G) :
    (((placeHom f0 f1 f2 g : ↥(SpI F)) : GL Idx F) : Matrix Idx Idx F) =
      bd3 (f0 g : Matrix (Fin 2) (Fin 2) F) (f1 g) (f2 g) := rfl

theorem placeHom_injective {f0 f1 f2 : G →* Matrix.SpecialLinearGroup (Fin 2) F}
    (h : ∀ g, f0 g = 1 → f1 g = 1 → f2 g = 1 → g = 1) :
    Function.Injective (placeHom f0 f1 f2) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 : bd3 (f0 g : Matrix (Fin 2) (Fin 2) F) (f1 g) (f2 g) = bd3 1 1 1 := by
    rw [bd3_one, ← placeHom_val, hg]
    rfl
  obtain ⟨e0, e1, e2⟩ := bd3_inj h1
  exact h g (Subtype.ext e0) (Subtype.ext e1) (Subtype.ext e2)

theorem mem_centralizer_of_bd3 {x g : ↥(SpI F)} {u v w a b c : Matrix (Fin 2) (Fin 2) F}
    (hx : ((x : GL Idx F) : Matrix Idx Idx F) = bd3 u v w)
    (hg : ((g : GL Idx F) : Matrix Idx Idx F) = bd3 a b c)
    (hu : u * a = a * u) (hv : v * b = b * v) (hw : w * c = c * w) :
    g ∈ Subgroup.centralizer ({x} : Set ↥(SpI F)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  apply Subtype.ext
  apply Units.ext
  show ((h : GL Idx F) : Matrix Idx Idx F) * ((g : GL Idx F) : Matrix Idx Idx F) =
    ((g : GL Idx F) : Matrix Idx Idx F) * ((h : GL Idx F) : Matrix Idx Idx F)
  rw [hx, hg, bd3_mul, bd3_mul, hu, hv, hw]

theorem zmod3_val_one : (1 : ZMod 3).val = 1 := rfl

theorem av_val (x : V3) :
    ((((monoSp F).av x : ↥(SpI F)) : GL Idx F) : Matrix Idx Idx F) =
      bd (fun j => (tm F 0 1) ^ (x j).val) := bc_aMat x

theorem av_rep0 :
    ((((monoSp F).av (rep 0) : ↥(SpI F)) : GL Idx F) : Matrix Idx Idx F) =
      bd3 (tm F 0 1) 1 1 := by
  rw [av_val]
  unfold bd3
  congr 1
  funext j
  fin_cases j <;> simp [rep, zmod3_val_one]

theorem av_rep1 :
    ((((monoSp F).av (rep 1) : ↥(SpI F)) : GL Idx F) : Matrix Idx Idx F) =
      bd3 (tm F 0 1) (tm F 0 1) 1 := by
  rw [av_val]
  unfold bd3
  congr 1
  funext j
  fin_cases j <;> simp [rep, zmod3_val_one]

theorem av_rep2 :
    ((((monoSp F).av (rep 2) : ↥(SpI F)) : GL Idx F) : Matrix Idx Idx F) =
      bd3 (tm F 0 1) (tm F 0 1) (tm F 0 1) := by
  rw [av_val]
  unfold bd3
  congr 1
  funext j
  fin_cases j <;> simp [rep, zmod3_val_one]

end Place

section Wit

variable {F : Type} [Field F] [CharP F 2]

theorem tall_comm_C (y : ↥(Tall F)) :
    tm F 0 1 * ((y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * tm F 0 1 := by
  have h := congrArg (fun z : ↥(Tall F) => ((z : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
    (tall_comm (Cu : ↥(Tall F)) y)
  simpa [Cu_val] using h

@[expose] def tallSL : ↥(Tall F) →* Matrix.SpecialLinearGroup (Fin 2) F where
  toFun g := ⟨((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F), by
    obtain ⟨α, β, hn, hg⟩ := g.2
    rw [hg, det_tm]
    exact hn⟩
  map_one' := Subtype.ext rfl
  map_mul' g h := Subtype.ext rfl

theorem tallSL_val (g : ↥(Tall F)) :
    ((tallSL g : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := rfl

theorem tallSL_injective : Function.Injective (tallSL (F := F)) := fun g h hgh =>
  Subtype.ext (Units.ext (congrArg Subtype.val hgh))

instance instFiniteSL2 [Finite F] : Finite (Matrix.SpecialLinearGroup (Fin 2) F) :=
  Finite.of_injective (fun g : Matrix.SpecialLinearGroup (Fin 2) F =>
    (g : Matrix (Fin 2) (Fin 2) F)) Subtype.val_injective

theorem rankTwoAt_rep0 [Finite F] {p : ℕ}
    (hp : p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F)) :
    RankTwoAt p ((monoSp F).av (rep 0)) := by
  refine ⟨Matrix.SpecialLinearGroup (Fin 2) F, Matrix.SpecialLinearGroup (Fin 2) F, inferInstance,
    inferInstance, inferInstance, inferInstance,
    placeHom (F := F) 1 (MonoidHom.fst _ _) (MonoidHom.snd _ _), ?_, ?_, hp, hp⟩
  · apply placeHom_injective
    intro g _ h1 h2
    exact Prod.ext h1 h2
  · rintro _ ⟨g, rfl⟩
    exact mem_centralizer_of_bd3 av_rep0 (placeHom_val _ _ _ g) (by simp) (by simp) (by simp)

theorem rankTwoAt_rep1 [Finite F] {p : ℕ} (hT : p ∣ Nat.card ↥(Tall F))
    (hp : p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F)) :
    RankTwoAt p ((monoSp F).av (rep 1)) := by
  refine ⟨↥(Tall F), Matrix.SpecialLinearGroup (Fin 2) F, inferInstance, inferInstance,
    inferInstance, inferInstance,
    placeHom (F := F) (tallSL.comp (MonoidHom.fst _ _)) 1 (MonoidHom.snd _ _), ?_, ?_, hT, hp⟩
  · apply placeHom_injective
    intro g h0 _ h2
    exact Prod.ext (tallSL_injective (by simpa using h0)) h2
  · rintro _ ⟨g, rfl⟩
    exact mem_centralizer_of_bd3 av_rep1 (placeHom_val _ _ _ g)
      (by simpa [tallSL_val] using tall_comm_C g.1) (by simp) (by simp)

theorem rankTwoAt_rep2 [Finite F] {p : ℕ} (hT : p ∣ Nat.card ↥(Tall F)) :
    RankTwoAt p ((monoSp F).av (rep 2)) := by
  refine ⟨↥(Tall F), ↥(Tall F), inferInstance, inferInstance, inferInstance, inferInstance,
    placeHom (F := F) (tallSL.comp (MonoidHom.fst _ _)) (tallSL.comp (MonoidHom.snd _ _)) 1,
    ?_, ?_, hT, hT⟩
  · apply placeHom_injective
    intro g h0 h1 _
    exact Prod.ext (tallSL_injective (by simpa using h0)) (tallSL_injective (by simpa using h1))
  · rintro _ ⟨g, rfl⟩
    exact mem_centralizer_of_bd3 av_rep2 (placeHom_val _ _ _ g)
      (by simpa [tallSL_val] using tall_comm_C g.1) (by simpa [tallSL_val] using tall_comm_C g.2)
      (by simp)

theorem simpleAt_rep01 [Finite F] {p : ℕ} (hS : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F))
    (hp : p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F))
    (hne : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) ≠ p) :
    SimpleAt p ((monoSp F).av (rep 0)) ∧ SimpleAt p ((monoSp F).av (rep 1)) := by
  have hinj : Function.Injective (placeHom (F := F) (1 : Matrix.SpecialLinearGroup (Fin 2) F →*
      Matrix.SpecialLinearGroup (Fin 2) F) 1 (MonoidHom.id _)) := by
    apply placeHom_injective
    intro g _ _ h2
    exact h2
  constructor
  · refine ⟨Matrix.SpecialLinearGroup (Fin 2) F, inferInstance, inferInstance, hS,
      placeHom (F := F) 1 1 (MonoidHom.id _), hinj, ?_, hp, hne⟩
    rintro _ ⟨g, rfl⟩
    exact mem_centralizer_of_bd3 av_rep0 (placeHom_val _ _ _ g) (by simp) (by simp) (by simp)
  · refine ⟨Matrix.SpecialLinearGroup (Fin 2) F, inferInstance, inferInstance, hS,
      placeHom (F := F) 1 1 (MonoidHom.id _), hinj, ?_, hp, hne⟩
    rintro _ ⟨g, rfl⟩
    exact mem_centralizer_of_bd3 av_rep1 (placeHom_val _ _ _ g) (by simp) (by simp) (by simp)

end Wit

end K421SpProof

end CFSG.LocalAnalysis.RankThreeUC.S15
