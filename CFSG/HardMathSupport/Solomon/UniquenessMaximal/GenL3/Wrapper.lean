module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Toral
public import CFSG.LocalAnalysis.GLTheoremB.InputPiGenProof
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Narrow

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns CFSG.RankThree.PartTwo.KFacts
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.HardMathSupport.Solomon.LocalBalance.AutL3

theorem c25Fix_map_congr {Q P : Type*} [Group Q] [Group P] (ε : Q ≃* P)
    (T : Subgroup (MulAut Q)) :
    c25Fix (T.map (MulAut.congr ε).toMonoidHom) = (c25Fix T).map ε.toMonoidHom := by
  ext y
  simp only [Subgroup.mem_map, mem_c25Fix]
  constructor
  · intro hy
    refine ⟨ε.symm y, fun s hs => ?_, by simp⟩
    have h : ε (s (ε.symm y)) = y := hy _ ⟨s, hs, rfl⟩
    exact ε.injective (by rw [h]; simp)
  · rintro ⟨x, hx, rfl⟩ _ ⟨s, hs, rfl⟩
    show ε (s (ε.symm (ε x))) = ε x
    rw [MulEquiv.symm_apply_apply]
    exact congrArg ε (hx s hs)

theorem GenP_of_equiv {Q P : Type*} [Group Q] [Group P] (ε : Q ≃* P) (A : Subgroup (MulAut Q))
    (h : GenP (A.map (MulAut.congr ε).toMonoidHom)) : GenP A := by
  set c : MulAut Q →* MulAut P := (MulAut.congr ε).toMonoidHom with hc
  have hcinj : Function.Injective c := (MulAut.congr ε).injective
  have hcsurj : Function.Surjective c := (MulAut.congr ε).surjective
  set Big := ⨆ (S : Subgroup (MulAut Q)) (_ : S ≤ A ∧ Nat.card A ≤ 3 * Nat.card S),
    dPart 3 (c25Fix S) with hBig
  have hcardA : Nat.card (A.map c) = Nat.card A := Subgroup.card_map_of_injective hcinj
  have hle : (⨆ (S : Subgroup (MulAut P))
      (_ : S ≤ A.map c ∧ Nat.card (A.map c) ≤ 3 * Nat.card S), dPart 3 (c25Fix S)) ≤
        Big.map ε.toMonoidHom := by
    refine iSup₂_le fun S' hS' => ?_
    set S : Subgroup (MulAut Q) := S'.comap c with hS
    have hSS' : S.map c = S' := Subgroup.map_comap_eq_self_of_surjective hcsurj S'
    have hSA : S ≤ A := by
      intro x hx
      have hx' : c x ∈ A.map c := hS'.1 hx
      obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.1 hx'
      rw [← hcinj hax]
      exact ha
    have hcard : Nat.card S = Nat.card S' := by
      rw [← hSS']
      exact (Subgroup.card_map_of_injective hcinj).symm
    have hmem : dPart 3 (c25Fix S) ≤ Big :=
      le_iSup₂_of_le S ⟨hSA, by rw [hcard, ← hcardA]; exact hS'.2⟩ le_rfl
    calc dPart 3 (c25Fix S') = dPart 3 (c25Fix (S.map c)) := by rw [hSS']
      _ = dPart 3 ((c25Fix S).map ε.toMonoidHom) := by rw [hc, c25Fix_map_congr]
      _ = (dPart 3 (c25Fix S)).map ε.toMonoidHom := dPart_map_equiv ε 3 (c25Fix S)
      _ ≤ Big.map ε.toMonoidHom := Subgroup.map_mono hmem
  intro x _
  have hx : ε x ∈ Big.map ε.toMonoidHom := hle (h (Subgroup.mem_top (ε x)))
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
  have : y = x := ε.injective hyx
  rw [← this]
  exact hy

theorem gen_Y_of_GenP_quot {Y : Type} [Group Y] [Finite Y]
    (hperf : ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ = ⊤)
    (hZ : IsPGroup 3 (Subgroup.center Y)) (hinj : Function.Injective (centerDescend Y))
    (A : Subgroup (MulAut Y)) (h : GenP (A.map (centerDescend Y))) :
    ⊤ ≤ ⨆ (S : Subgroup (MulAut Y)) (_ : S ≤ A ∧ Nat.card A ≤ 3 * Nat.card S), c25Fix S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine gen_of_dPart (p := 3) hperf hZ {S | S ≤ A ∧ Nat.card A ≤ 3 * Nat.card S} ?_
  refine h.trans (iSup₂_le fun S' hS' => ?_)
  set S : Subgroup (MulAut Y) := S'.comap (centerDescend Y) ⊓ A with hS
  have hmap : S.map (centerDescend Y) = S' := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact hs.1
    · intro hx
      obtain ⟨a, haA, rfl⟩ := Subgroup.mem_map.1 (hS'.1 hx)
      exact ⟨a, ⟨hx, haA⟩, rfl⟩
  have hSA : S ≤ A := inf_le_right
  have hcardS : Nat.card S = Nat.card S' := by
    rw [← hmap]
    exact (Subgroup.card_map_of_injective hinj).symm
  have hcardA : Nat.card (A.map (centerDescend Y)) = Nat.card A :=
    Subgroup.card_map_of_injective hinj
  refine le_iSup₂_of_le S ⟨hSA, ?_⟩ (le_of_eq (by rw [hmap]))
  rw [hcardS, ← hcardA]
  exact hS'.2

@[expose] def L364Rank3Heis : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → GLAPPrimeCore 3 Y = ⊥ →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = 64 →
    ∀ (ε : (Y ⧸ Subgroup.center Y) ≃* projectiveSL 3 K),
    ∀ A : Subgroup (MulAut Y), IsElemAbelian 3 A → Nat.card A = 27 →
    (∃ α ∈ A, α ≠ 1 ∧ ¬ IsInnDiagThree α) →
    ¬ LiftsCommute (A.map ((MulAut.congr ε).toMonoidHom.comp (centerDescend Y))) →
      ⊤ ≤ ⨆ (S : Subgroup (MulAut Y)) (_ : S ≤ A ∧ Nat.card A ≤ 3 * Nat.card S), c25Fix S

theorem l364Rank3Gen_of_heis (hH : L364Rank3Heis) : L364Rank3Gen := by
  intro Y _ _ hY hcore K _ _ hK hne A hA h27 hα
  obtain ⟨e⟩ := hne
  set ε : (Y ⧸ Subgroup.center Y) ≃* projectiveSL 3 K := e.trans (psiO K) with hε
  set Φ : MulAut Y →* MulAut (projectiveSL 3 K) :=
    (MulAut.congr ε).toMonoidHom.comp (centerDescend Y) with hΦ
  by_cases hL : LiftsCommute (A.map Φ)
  · have h3 : 3 ∣ Nat.card K - 1 := by rw [hK]; norm_num
    have hinjΦ : Function.Injective Φ := phi_injective hY ε
    have hAel' : IsElemAbelian 3 (A.map Φ) := isElemAbelian_map Φ hA
    have hcard' : Nat.card (A.map Φ) = 27 := by
      rw [Subgroup.card_map_of_injective hinjΦ, h27]
    obtain ⟨α, hαA, hα1, hαn⟩ := hα
    have hb : ∃ b ∈ A.map Φ, b ∉ linearAutGroup 3 K := by
      refine ⟨Φ α, ⟨α, hαA, rfl⟩, fun hD => hαn (Or.inl ?_)⟩
      exact isInnDiagPSL3_of_model ε hD
    have hGen := gen_toral h3 (A.map Φ) hAel' hcard' hb hL
    have hGen' : GenP (A.map (centerDescend Y)) := by
      refine GenP_of_equiv ε _ ?_
      rw [Subgroup.map_map]
      exact hGen
    have hcen : IsPGroup 3 (Subgroup.center Y) :=
      CFSG.LocalAnalysis.GLTheoremB.isPGroup_center Nat.prime_three hcore
    have hinj : Function.Injective (centerDescend Y) := by
      intro a b hab
      apply hinjΦ
      show MulAut.congr ε (centerDescend Y a) = MulAut.congr ε (centerDescend Y b)
      rw [hab]
    have hperf : ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ = ⊤ := hY.1
    exact gen_Y_of_GenP_quot hperf hcen hinj A hGen'
  · exact hH Y hY hcore K hK ε A hA h27 hα hL

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3
