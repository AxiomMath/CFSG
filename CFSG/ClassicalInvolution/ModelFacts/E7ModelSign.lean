module

public import CFSG.ClassicalInvolution.ModelFacts.E7ModelCA
public import CFSG.ClassicalInvolution.ModelFacts.E7ModelPair
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import CFSG.ClassicalInvolution.ModelFacts.E7ModelLeviRat
public import CFSG.ClassicalInvolution.ModelFacts.E7ModelWeyl

public section

namespace CFSG.ClassicalInvolution.ModelFacts.E7Model

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.ModelFacts.Levi CFSG.ClassicalInvolution.ModelFacts

@[expose] def Jsign : Set (Fin (Tag.rank .E7)) := {j | j.val ≠ 0 ∧ j.val ≠ 2}

@[expose] def lamSign : V7 := ![7, 2, 3, 4, 3, 2, 1]

theorem lamSign_J : ∀ j ∈ Jsign, iform lamSign (Pi.single j 1) = 0 := by
  intro j hj
  obtain ⟨h0, h2⟩ := hj
  have : ∀ j : Fin (Tag.rank .E7), j.val ≠ 0 → j.val ≠ 2 → iform lamSign (Pi.single j 1) = 0 := by
    decide +kernel
  exact this j h0 h2

theorem lamSign_B : ∀ σ ∈ rootFinset .E7, |iform lamSign σ| ≤ 12 := by decide +kernel

theorem lamSign_ker : ∀ σ ∈ rootFinset .E7, iform lamSign σ = 0 →
    σ ∈ parabolicRoots .E7 Jsign := by
  have h : ∀ σ ∈ rootFinset .E7, iform lamSign σ = 0 → σ (e7Idx 0) = 0 ∧ σ (e7Idx 2) = 0 := by
    decide +kernel
  intro σ hσ h0
  obtain ⟨h1, h2⟩ := h σ hσ h0
  refine ⟨mem_rootFinset.1 hσ, fun i hi => ?_⟩
  have : i.val = 0 ∨ i.val = 2 := by
    by_contra hne
    exact hi ⟨fun h => hne (Or.inl h), fun h => hne (Or.inr h)⟩
  rcases this with h | h
  · have : i = e7Idx 0 := Fin.ext (by simpa [e7Idx] using h)
    rw [this]; exact h1
  · have : i = e7Idx 2 := Fin.ext (by simpa [e7Idx] using h)
    rw [this]; exact h2


theorem sign_cut : ∀ σ ∈ rootFinset .E7, iform thetaE7 σ = 0 →
    Even (iform (Pi.single (e7Idx 0) 1) σ) → σ ∈ parabolicRoots .E7 Jsign := by
  have h : ∀ σ ∈ rootFinset .E7, iform thetaLit σ = 0 →
      Even (iform (Pi.single (e7Idx 0) 1 : V7) σ) → σ (e7Idx 0) = 0 ∧ σ (e7Idx 2) = 0 := by
    decide +kernel
  intro σ hσ h0 hev
  rw [thetaE7_eq] at h0
  obtain ⟨h1, h2⟩ := h σ hσ h0 hev
  refine ⟨mem_rootFinset.1 hσ, fun i hi => ?_⟩
  have : i.val = 0 ∨ i.val = 2 := by
    by_contra hne
    exact hi ⟨fun h => hne (Or.inl h), fun h => hne (Or.inr h)⟩
  rcases this with h | h
  · have : i = e7Idx 0 := Fin.ext (by simpa [e7Idx] using h)
    rw [this]; exact h1
  · have : i = e7Idx 2 := Fin.ext (by simpa [e7Idx] using h)
    rw [this]; exact h2

theorem Jsign_thetaDiag_one : ∀ j ∈ Jsign, iform thetaE7 (Pi.single j 1) = 0 ∧
    iform (Pi.single (e7Idx 0) 1 : V7) (Pi.single j 1) = 0 := by
  have h : ∀ j : Fin (Tag.rank .E7), j.val ≠ 0 → j.val ≠ 2 → iform thetaLit (Pi.single j 1) = 0 ∧
      iform (Pi.single (e7Idx 0) 1 : V7) (Pi.single j 1) = 0 := by decide +kernel
  intro j hj
  rw [thetaE7_eq]
  exact h j hj.1 hj.2


section Core

variable {p f : ℕ} [Fact p.Prime]

theorem exists_unit_sq_ne_one (hq : 5 ≤ p ^ f) :
    ∃ a : (GaloisField p f)ˣ, a ^ 2 ≠ 1 := by
  have : NeZero f := ⟨by rintro rfl; simp at hq⟩
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := (GaloisField p f)ˣ)
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (NeZero.ne f)
  have hord : orderOf ζ = Nat.card (GaloisField p f) - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hζ, Nat.card_units]
  refine ⟨ζ, fun h => ?_⟩
  have := orderOf_dvd_of_pow_eq_one h
  have h2 := Nat.le_of_dvd (by norm_num) this
  omega

theorem sign_core (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {y g : ModGL .E7 (GaloisField p f)}
    (hyG : y ∈ adjointGroup .E7 (GaloisField p f))
    (hgG : g ∈ adjointGroup .E7 (GaloisField p f)) (hy2 : y * y = 1)
    (hgy : g * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField p f)ˣ)) * g⁻¹ = y)
    (hyd : y * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField p f)ˣ)) =
      rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField p f)ˣ)) * y)
    (hye : ∀ A : SL2 (GaloisField p f),
      y * rootSL2 .E7 (GaloisField p f) (Pi.single (e7Idx 0) 1) A =
        rootSL2 .E7 (GaloisField p f) (Pi.single (e7Idx 0) 1) A * y) :
    ∃ δ, IsRoot .E7 δ ∧ ∃ u ∈ adjointGroup .E7 (GaloisField p f),
      u * y * u⁻¹ = rootDiagUnit .E7 (thetaDiag δ (-1 : (GaloisField p f)ˣ)) ∧
      u * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField p f)ˣ)) =
        rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField p f)ˣ)) * u ∧
      u * rootDiagUnit .E7 (thetaDiag (Pi.single (e7Idx 0) 1) (-1 : (GaloisField p f)ˣ)) =
        rootDiagUnit .E7 (thetaDiag (Pi.single (e7Idx 0) 1) (-1 : (GaloisField p f)ˣ)) * u := by
  have : NeZero f := ⟨by rintro rfl; simp at hq⟩
  have hF : ringChar (GaloisField p f) ≠ 2 := ringChar_galoisField_ne_two hp2
  obtain ⟨hodd, h5⟩ := odd_and_five_le_card_galoisField hp2 hq
  have he0 : IsRoot .E7 (Pi.single (e7Idx 0) 1 : V7) := isRoot_single .E7 (e7Idx 0)
  obtain ⟨a, ha⟩ := exists_unit_sq_ne_one (p := p) (f := f) hq
  have hchar : rootChar (thetaDiag (Pi.single (e7Idx 0) 1 : V7) a) thetaE7 = a := by
    rw [rootChar_thetaDiag, iform_comm, iform_thetaE7_single]
    simp [e7Idx]
  have hyb : y * rootDiagUnit .E7 (thetaDiag (Pi.single (e7Idx 0) 1 : V7) a) =
      rootDiagUnit .E7 (thetaDiag (Pi.single (e7Idx 0) 1 : V7) a) * y := by
    rw [← rootTorusSL2_eq_thetaDiag_gen he0]
    exact hye (HSL a)
  have hyJ : y ∈ parabolicLevi .E7 (GaloisField p f) JE7 :=
    mem_parabolicLevi_of_commute_diag hF hyG hyd (by rw [hchar]; exact ha) hyb
  set k := AlgebraicClosure (GaloisField p f) with hkdef
  set ι := algebraMap (GaloisField p f) k with hι
  have hpk : CharP k p := charP_of_injective_algebraMap ι.injective p
  have hkF : ringChar k ≠ 2 := by rw [ringChar.eq k p]; exact hp2
  have hk2 : (-1 : kˣ) ≠ 1 := fun h =>
    Ring.neg_one_ne_one_of_char_ne_two hkF (by simpa using congrArg Units.val h)
  have hyL : baseChangeGL ι y ∈ parabolicLevi .E7 k JE7 := baseChangeGL_mem_parabolicLevi ι hyJ
  have hyG' : baseChangeGL ι y ∈ adjointGroup .E7 k := baseChangeGL_mem_adjointGroup ι hyG
  have hyde : y * rootDiagUnit .E7
      (thetaDiag (Pi.single (e7Idx 0) 1 : V7) (-1 : (GaloisField p f)ˣ)) =
      rootDiagUnit .E7 (thetaDiag (Pi.single (e7Idx 0) 1 : V7) (-1 : (GaloisField p f)ˣ)) * y := by
    rw [← rootTorusSL2_eq_thetaDiag_gen he0]
    exact hye (HSL (-1))
  have hyde' : baseChangeGL ι y * rootDiagUnit .E7
      (thetaDiag (Pi.single (e7Idx 0) 1 : V7) (-1 : kˣ)) = rootDiagUnit .E7
      (thetaDiag (Pi.single (e7Idx 0) 1 : V7) (-1 : kˣ)) * baseChangeGL ι y := by
    rw [← baseChangeGL_rootDiagUnit_thetaDiag_E7 ι, ← map_mul, ← map_mul, hyde]
  have hyJ'' : baseChangeGL ι y ∈ parabolicLevi .E7 k Jsign :=
    mem_levi_of_commute_signdiag hk2 (fun j hj => iform_thetaE7_single_of_mem hj)
      (fun σ hσ => abs_iform_thetaE7_le σ hσ) he0 sign_cut hyG' hyL hyde'
  obtain ⟨δ, hδ, u, huG, hu, hucomm⟩ := exists_rational_levi_conj hodd lamSign_J lamSign_B
    lamSign_ker hyG hgG hy2 hyJ'' hgy
  refine ⟨δ, hδ, u, huG, hu, hucomm _ fun j hj => ?_, hucomm _ fun j hj => ?_⟩
  · simp [thetaDiag, (Jsign_thetaDiag_one j hj).1]
  · simp [thetaDiag, (Jsign_thetaDiag_one j hj).2]

end Core

end CFSG.ClassicalInvolution.ModelFacts.E7Model
