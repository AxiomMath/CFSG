module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusPieces
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCoverFork
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueStep3Basic
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaIota

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG Subgroup Matrix
open CFSG.Assembly.LowTwoRank
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.OmegaPilot (diagOmega diagOmega_coe omegaBlock siegelBlockGL flipGL
  levelParam mem_levelParam)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

section Transport

theorem kOmega_map_subtype_perfectCore_centralizer {r f : ℕ} (hr : 2 ≤ r) (hr3 : 3 ≤ r)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (P : Subgroup (Fin r → Kˣ)) :
    (perfectCore (centralizer ((((P.map (diagSp K r)).map (kOmegaIota hr hr3 hKc hf) :
      Subgroup (StatedOmega (StatedQuadPlus (r + 1) K))) :
        Set (StatedOmega (StatedQuadPlus (r + 1) K)))))).map
          (StatedOmega (StatedQuadPlus (r + 1) K)).subtype =
      perfectCore (StatedOmega (StatedQuadPlus (r + 1) K) ⊓
        centralizer (diagOmega K (r + 1) '' (kOmegaSnoc K '' (P : Set (Fin r → Kˣ))))) := by
  rw [← F4Pilot.perfectCore_range_inf_centralizer_map
    (StatedOmega (StatedQuadPlus (r + 1) K)).subtype_injective, range_subtype]
  congr 3
  ext x
  constructor
  · rintro ⟨_, ⟨_, ⟨t, ht, rfl⟩, rfl⟩, rfl⟩
    exact ⟨kOmegaSnoc K t, ⟨t, ht, rfl⟩, (coe_kOmegaIota_diagSp hr hr3 hKc hf t).symm⟩
  · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨_, ⟨_, ⟨t, ht, rfl⟩, rfl⟩, coe_kOmegaIota_diagSp hr hr3 hKc hf t⟩

end Transport

section Pieces

omit [Finite K] [CharP K 2] in
theorem kOmegaSnoc_init_mul {r : ℕ} (t : Fin (r + 1) → Kˣ) :
    t = kOmegaSnoc K (Fin.init t) * Pi.mulSingle (Fin.last r) (t (Fin.last r)) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [kOmegaSnoc]
  · simp [kOmegaSnoc, Fin.init]

omit [CharP K 2] in
theorem perfectCore_kOmega_short (hK : 4 ≤ Nat.card K) {r : ℕ} {a b : Fin r} (hab : a ≠ b)
    {P : Subgroup (Fin r → Kˣ)} (hP : ∀ t, t ∈ P ↔ t a = t b) :
    perfectCore (StatedOmega (StatedQuadPlus (r + 1) K) ⊓
      centralizer (diagOmega K (r + 1) '' (kOmegaSnoc K '' (P : Set (Fin r → Kˣ))))) =
      siegelBlockGL K {a.castSucc, b.castSucc} := by
  obtain ⟨κ, hκ⟩ := exists_units_mul_self_ne_one_of_four_le hK
  have hκ1 : κ ≠ 1 := units_ne_one_of_mul_self_ne_one hκ
  have hab' : a.castSucc ≠ b.castSucc := fun h => hab (Fin.castSucc_injective r h)
  have hJc : ({a.castSucc, b.castSucc} : Finset (Fin (r + 1))).card = 2 := Finset.card_pair hab'
  set J' : Finset (Fin (r + 1)) := {a.castSucc, b.castSucc} with hJ'
  have hlev : ∀ s : Fin (r + 1) → Kˣ, s ∈ levelParam (K := K) J' ↔ s a.castSucc = s b.castSucc := by
    intro s
    rw [mem_levelParam]
    constructor
    · intro h
      exact h _ (by simp [hJ']) _ (by simp [hJ'])
    · intro h i hi j hj
      simp only [hJ', Finset.mem_insert, Finset.mem_singleton] at hi hj
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
      · rfl
      · exact h
      · exact h.symm
      · rfl
  have hsub : kOmegaSnoc K '' (P : Set (Fin r → Kˣ)) ⊆ (levelParam (K := K) J' : Set _) := by
    rintro _ ⟨t, ht, rfl⟩
    rw [SetLike.mem_coe, hlev, kOmegaSnoc_castSucc, kOmegaSnoc_castSucc]
    exact (hP t).1 ht
  have hDj : ∀ s ∈ kOmegaSnoc K '' (P : Set (Fin r → Kˣ)), s (Fin.last r) = 1 := by
    rintro _ ⟨t, -, rfl⟩
    exact kOmegaSnoc_last K t
  have hsep : ∀ c : Fin (r + 1) ⊕ Fin (r + 1), planeOf c ≠ Fin.last r →
      ∃ s ∈ kOmegaSnoc K '' (P : Set (Fin r → Kˣ)), diagSpEntry s c ≠ 1 := by
    intro c hc
    refine ⟨kOmegaSnoc K (fun _ => κ), ⟨_, (hP _).2 rfl, rfl⟩, ?_⟩
    have hci : ∀ i : Fin (r + 1), i ≠ Fin.last r → kOmegaSnoc K (fun _ => κ) i = κ := by
      intro i hi
      obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.2 hi
      exact kOmegaSnoc_castSucc K _ j
    rcases c with i | i
    · rw [diagSpEntry_inl, hci i hc]
      exact fun h => hκ1 (Units.ext h)
    · rw [diagSpEntry_inr, hci i hc]
      exact fun h => hκ1 (inv_eq_one.1 (Units.ext h))
  have hD' : ∀ t ∈ (levelParam (K := K) J' : Set (Fin (r + 1) → Kˣ)),
      ∃ s ∈ kOmegaSnoc K '' (P : Set (Fin r → Kˣ)), ∃ c : Kˣ,
        t = s * Pi.mulSingle (Fin.last r) c := by
    intro t ht
    refine ⟨kOmegaSnoc K (Fin.init t), ⟨Fin.init t, (hP _).2 ?_, rfl⟩, t (Fin.last r),
      kOmegaSnoc_init_mul t⟩
    simp only [Fin.init]
    exact (hlev t).1 ht
  rw [F4Pilot.perfectCore_statedOmega_inf_centralizer_eq_of_plane (Fin.last r) hsub hDj hsep hD',
    OmegaPilot.perfectCore_statedOmega_inf_centralizer_eq_level hK (J := J') (by rw [hJc]) _
      (fun s hs => mem_levelParam.1 hs)
      (fun a b hab hJ => OmegaPilot.exists_mem_levelParam_diagSpEntry_ne hκ hab hJ),
    OmegaPilot.siegelBlockGL_eq_map_omegaLeviSL hK (by rw [hJc])]

omit [CharP K 2] in
theorem perfectCore_kOmega_long (hK : 4 ≤ Nat.card K) {r : ℕ} {c : Fin r}
    {P : Subgroup (Fin r → Kˣ)} (hP : ∀ t, t ∈ P ↔ t c = 1) :
    perfectCore (StatedOmega (StatedQuadPlus (r + 1) K) ⊓
      centralizer (diagOmega K (r + 1) '' (kOmegaSnoc K '' (P : Set (Fin r → Kˣ))))) =
      perfectCore (omegaBlock K {c.castSucc, Fin.last r}) := by
  have hset : kOmegaSnoc K '' (P : Set (Fin r → Kˣ)) =
      (planeTorusParam K ({c.castSucc, Fin.last r} : Finset (Fin (r + 1))) :
        Set (Fin (r + 1) → Kˣ)) := by
    ext s
    simp only [Set.mem_image, SetLike.mem_coe, mem_planeTorusParam, Finset.mem_insert,
      Finset.mem_singleton, forall_eq_or_imp, forall_eq]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨by rw [kOmegaSnoc_castSucc]; exact (hP t).1 ht, kOmegaSnoc_last K t⟩
    · rintro ⟨h1, h2⟩
      refine ⟨Fin.init s, (hP _).2 h1, ?_⟩
      have h3 := kOmegaSnoc_init_mul s
      rw [h2, Pi.mulSingle_one, mul_one] at h3
      exact h3.symm
  rw [hset, F4Pilot.perfectCore_statedOmega_inf_centralizer_planeTorusParam hK]

end Pieces

section Fork

omit [Finite K] [CharP K 2] in
theorem kOmega_card_sup_eq_mul {G : Type*} [Group G] {A B : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, Commute a b) (hdisj : Disjoint A B) :
    Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B := by
  set φ := A.subtype.noncommCoprod B.subtype (fun a b => hAB a a.2 b b.2) with hφ
  have hinj : Function.Injective φ := (MonoidHom.noncommCoprod_injective _ _ _).2
    ⟨A.subtype_injective, B.subtype_injective, by rwa [range_subtype, range_subtype]⟩
  have hrange : φ.range = A ⊔ B := by
    have h := MonoidHom.noncommCoprod_range A.subtype B.subtype (fun a b => hAB a a.2 b b.2)
    rw [range_subtype, range_subtype] at h
    exact h
  rw [← hrange, ← Nat.card_prod]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

omit [Finite K] in
theorem kOmega_eq_one_of_mem_siegelBlockGL {m : ℕ} {I : Finset (Fin m)} (hI : I.card = 2)
    {x : GL (Fin m ⊕ Fin m) K} (hx : x ∈ siegelBlockGL K I)
    (hc : ∀ y ∈ siegelBlockGL K I, Commute x y) : x = 1 := by
  set ψ : siegelBlockGL K I ≃* Matrix.SpecialLinearGroup (Fin I.card) K :=
    ((siegelBlock K I).equivMapOfInjective (StatedSp m K).subtype
      (StatedSp m K).subtype_injective).symm.trans (siegelBlockEquiv I).symm with hψ
  have hz : ψ ⟨x, hx⟩ ∈ center (Matrix.SpecialLinearGroup (Fin I.card) K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := ψ.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc y y.2).eq.symm
  obtain ⟨ρ, hρ, hρs⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
  rw [Fintype.card_fin, hI] at hρ
  have hρ1 : ρ = 1 := by
    have h1 : (ρ + 1) ^ 2 = 0 := by
      rw [add_sq, hρ, mul_one, one_pow, CharTwo.two_eq_zero, zero_mul, add_zero,
        CharTwo.add_self_eq_zero]
    have h2 : ρ + 1 = 0 := (pow_eq_zero_iff (n := 2) (by norm_num)).1 h1
    rw [eq_neg_of_add_eq_zero_left h2, CharTwo.neg_eq]
  have h1 : ψ ⟨x, hx⟩ = 1 := by
    apply Subtype.ext
    rw [← hρs, hρ1, map_one, Matrix.SpecialLinearGroup.coe_one]
  have h2 : (⟨x, hx⟩ : siegelBlockGL K I) = 1 := ψ.injective (by rw [h1, map_one])
  exact congrArg Subtype.val h2

theorem kOmega_perfectCore_omegaBlock_pair_eq_sup (hK : 4 ≤ Nat.card K) {m : ℕ} {i j : Fin m}
    (hij : i ≠ j) :
    perfectCore (omegaBlock K {i, j}) = siegelBlockGL K {i, j} ⊔
      (siegelBlockGL K {i, j}).map (MulAut.conj (flipGL K {j})).toMonoidHom := by
  have hI : ({i, j} : Finset (Fin m)).card = 2 := Finset.card_pair hij
  set A := siegelBlockGL K {i, j} with hA
  set B := (siegelBlockGL K {i, j}).map (MulAut.conj (flipGL K {j})).toMonoidHom with hB
  have hPB : ({i, j} : Finset (Fin m)) ∩ {j} = {j} := by
    rw [Finset.inter_eq_right]
    simp
  have hcomm : ∀ a ∈ A, ∀ b ∈ B, Commute a b := fun a ha b hb =>
    OmegaPilot.commute_siegelBlockGL_flip hK hI hPB ha hb
  have hAperf : ⁅A, A⁆ = A := OmegaPilot.commutator_siegelBlockGL hK (by rw [hI])
  have hBperf : ⁅B, B⁆ = B := by rw [hB, ← Subgroup.map_commutator, hAperf]
  have hAle : A ≤ omegaBlock K {i, j} :=
    le_inf (OmegaPilot.siegelBlockGL_le_statedOmega hK (by rw [hI]))
      (OmegaPilot.siegelBlockGL_le_suppGL _)
  have hBle : B ≤ omegaBlock K {i, j} := by
    refine le_inf ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact (mem_normalizer_iff.1 (OmegaPilot.flipGL_mem_normalizer (F := K) {j}) x).1
        (OmegaPilot.siegelBlockGL_le_statedOmega hK (by rw [hI]) hx)
    · exact (map_mono (OmegaPilot.siegelBlockGL_le_suppGL _)).trans
        (OmegaPilot.map_flipGL_suppGL_le _ _)
  have hle : A ⊔ B ≤ perfectCore (omegaBlock K {i, j}) :=
    sup_le (CFSG.Quasithin.le_perfectCore_of_perfect hAle hAperf)
      (CFSG.Quasithin.le_perfectCore_of_perfect hBle hBperf)
  have hdisj : Disjoint A B := by
    rw [disjoint_iff, eq_bot_iff]
    intro x hx
    rw [mem_bot]
    exact kOmega_eq_one_of_mem_siegelBlockGL hI hx.1
      fun y hy => (hcomm y hy x hx.2).symm
  have hcardA : Nat.card A = F4Pilot.ordSL 2 (Nat.card K) := by
    rw [hA, OmegaPilot.natCard_siegelBlockGL, hI, F4Pilot.natCard_specialLinearGroup_eq_ordSL
      (by norm_num)]
  have hcardB : Nat.card B = F4Pilot.ordSL 2 (Nat.card K) := by
    rw [hB, Subgroup.card_map_of_injective (MulAut.conj _).injective, ← hA, hcardA]
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [kOmega_card_sup_eq_mul hcomm hdisj, hcardA, hcardB,
    F4Pilot.natCard_perfectCore_omegaBlock_of_card_two hK hI, sq]

end Fork

end CFSG.SeitzReduction.SymplecticPilot
