module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BFiveAWitness
public import CFSG.Sporadic.Bridge.HSSurj
public import Certificates.Certificate17535
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Monster.B CFSG.Monster.B.Bin CFSG.Monster.B.Primes.Native CFSG.Monster.B.Pinned
  CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Native
  CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen
open TauCeti.Sporadic (hsPresentation)

section Words

theorem relVal_map {G M : Type*} [Group G] [Monoid M] (f : G →* M) {a b : G} (ha : a * a = 1)
    (hb : b ^ 5 = 1) (v : List (ℕ × Bool)) :
    CFSG.KC.BM.HS.relVal (f a) (f b) v = f (wordProd (img2 a b) v) := by
  have hai : a⁻¹ = a := (eq_inv_of_mul_eq_one_left ha).symm
  have hbi : b⁻¹ = b ^ 4 := (eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hb)).symm
  induction v with
  | nil => simp [CFSG.KC.BM.HS.relVal, wordProd]
  | cons l v ih =>
    simp only [CFSG.KC.BM.HS.relVal, wordProd, List.map_cons, List.prod_cons, map_mul] at ih ⊢
    rw [ih]
    congr 1
    obtain ⟨i, s⟩ := l
    unfold CFSG.KC.BM.HS.letter img2
    by_cases hi : i = 0 <;> cases s <;> simp [hi, hai, hbi]

theorem hsA_map {G : Type*} [Monoid G] (f : G →* Matrix (Fin 4370) (Fin 4370) (ZMod 2))
    (g₁ g₂ : G) : CFSG.KC.BM.HS.hsA (f g₁) (f g₂) =
      f (g₂ ^ 15 * g₂ ^ 15 * (g₁ * g₂ ^ 15 * g₁ ^ 3) ^ 12) := by
  simp only [CFSG.KC.BM.HS.hsA, map_mul, map_pow]

theorem hsB_map {G : Type*} [Monoid G] (f : G →* Matrix (Fin 4370) (Fin 4370) (ZMod 2))
    (g₁ g₂ : G) : CFSG.KC.BM.HS.hsB (f g₁) (f g₂) = f (g₂ ^ 15 * (g₁ * g₂ ^ 15 * g₁ ^ 3) ^ 9) := by
  simp only [CFSG.KC.BM.HS.hsB, map_mul, map_pow]

end Words

section Recognition

theorem nonempty_mulEquiv_HS_of_relators
    {G : Type} [Group G] (u v : G)
    (hrel : ∀ w ∈ hsPresentation.relatorLetters, wordProd (img2 u v) w = 1)
    (hu : u ≠ 1) :
    Nonempty (↥(Subgroup.closure ({u, v} : Set G)) ≃* NativeSporadic.HS) := by
  set L : Subgroup G := Subgroup.closure ({u, v} : Set G) with hLdef
  have hu' : u ∈ L := Subgroup.subset_closure (by simp)
  have hv' : v ∈ L := Subgroup.subset_closure (by simp)
  let img : ℕ → ↥L := fun i => if i = 0 then ⟨u, hu'⟩ else ⟨v, hv'⟩
  have himg0 : img 0 = ⟨u, hu'⟩ := by simp [img]
  have himg1 : img 1 = ⟨v, hv'⟩ := by simp [img]
  have hrelL : ∀ w ∈ hsPresentation.relatorLetters, wordProd img w = 1 := by
    intro w hw
    apply Subtype.ext
    rw [coe_wordProd]
    have himg : (fun i => ((img i : ↥L) : G)) = img2 u v := by
      funext i
      by_cases hi : i = 0 <;> simp [img, img2, hi]
    rw [himg]
    exact hrel w hw
  have hgc : hsPresentation.generatorCount = 2 :=
    CFSG.Sporadic.Bridge.HS.generatorCount_eq
  let φ : hsPresentation.Group →* ↥L := presHom hsPresentation img hrelL
  have hφ0 : φ (presGen hsPresentation 0) = ⟨u, hu'⟩ := by
    rw [presHom_presGen hsPresentation img hrelL (by rw [hgc]; norm_num), himg0]
  have hφ1 : φ (presGen hsPresentation 1) = ⟨v, hv'⟩ := by
    rw [presHom_presGen hsPresentation img hrelL (by rw [hgc]; norm_num), himg1]
  have hsurj : Function.Surjective φ := by
    refine MonoidHom.range_eq_top.1 ?_
    rw [eq_top_iff, ← Subgroup.closure_closure_coe_preimage (k := ({u, v} : Set G))]
    refine (Subgroup.closure_le _).2 ?_
    intro x hx
    rcases hx with hx | hx
    · exact ⟨presGen hsPresentation 0, by rw [hφ0]; exact (Subtype.ext hx).symm⟩
    · rw [Set.mem_singleton_iff] at hx
      exact ⟨presGen hsPresentation 1, by rw [hφ1]; exact (Subtype.ext hx).symm⟩
  obtain ⟨e⟩ : Nonempty (NativeSporadic.HS ≃* hsPresentation.Group) :=
    CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  haveI : IsSimpleGroup hsPresentation.Group :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.HS.isSimpleGroup_HS e.symm
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exact h
    · exfalso
      have hmem : presGen hsPresentation 0 ∈ φ.ker := by
        rw [h]; exact Subgroup.mem_top _
      rw [MonoidHom.mem_ker, hφ0] at hmem
      exact hu (congrArg Subtype.val hmem)
  exact ⟨(MulEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm.trans e.symm⟩

end Recognition

section Elements


@[expose] noncomputable def hsAFive : NativeSporadic.B := (gTwoM ^ 15 * gTwoM ^ 15) * yOneFiveA ^ 12

@[expose] noncomputable def hsBFive : NativeSporadic.B := gTwoM ^ 15 * yOneFiveA ^ 9

theorem coe_runG_max15_one :
    ((Pinned.runG (max15Prog ()) glA₁ glA₂ 1 : GL (Fin 4370) (ZMod 2)) :
      Matrix (Fin 4370) (Fin 4370) (ZMod 2)) = bMat gOneM := by
  rw [gOneM, ← coe_bSeedGL, bSeedGL_runG]

theorem coe_runG_max15_two :
    ((Pinned.runG (max15Prog ()) glA₁ glA₂ 2 : GL (Fin 4370) (ZMod 2)) :
      Matrix (Fin 4370) (Fin 4370) (ZMod 2)) = bMat gTwoM := by
  rw [gTwoM, ← coe_bSeedGL, bSeedGL_runG]

theorem bFiveHS_parts :
    hsAFive * hsAFive = 1 ∧ hsAFive ≠ 1 ∧ hsBFive ^ 5 = 1 ∧
      hsAFive * sFiveA = sFiveA * hsAFive ∧ hsBFive * sFiveA = sFiveA * hsBFive ∧
      ∀ v ∈ hsPresentation.relatorLetters, wordProd (img2 hsAFive hsBFive) v = 1 := by
  have h := Certificates.certificate17535
  rw [coe_runG_max15_one, coe_runG_max15_two] at h
  obtain ⟨haa, ha1, hb5, has, hbs, hrels⟩ := h
  have hA : CFSG.KC.BM.HS.hsA (bMat gOneM) (bMat gTwoM) = bMat hsAFive := by
    unfold hsAFive yOneFiveA
    exact hsA_map bMat gOneM gTwoM
  have hB : CFSG.KC.BM.HS.hsB (bMat gOneM) (bMat gTwoM) = bMat hsBFive := by
    unfold hsBFive yOneFiveA
    exact hsB_map bMat gOneM gTwoM
  have hS : bMat gTwoM ^ 14 = bMat sFiveA := (map_pow bMat gTwoM 14).symm
  rw [hA] at haa ha1 has hrels
  rw [hB] at hb5 hbs hrels
  rw [hS] at has hbs
  have hAA : hsAFive * hsAFive = 1 := bMat_injective (by rw [map_mul, map_one]; exact haa)
  have hB5 : hsBFive ^ 5 = 1 := bMat_injective (by rw [map_pow, map_one]; exact hb5)
  refine ⟨hAA, fun e => ha1 (by rw [e, map_one]), hB5,
    bMat_injective (by rw [map_mul, map_mul]; exact has),
    bMat_injective (by rw [map_mul, map_mul]; exact hbs), fun v hv => ?_⟩
  have e := hrels v hv
  rw [relVal_map bMat hAA hB5] at e
  exact bMat_injective (by rw [e, map_one])

end Elements

end CFSG.HardMathSupport.Dickson.I271
