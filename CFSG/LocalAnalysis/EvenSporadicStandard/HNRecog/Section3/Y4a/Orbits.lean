module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Y4a.Setup
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Y4a.CentCard
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Y4a.Exists
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Y4a.OrbitCount
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Y4a.OrbitB

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem y4a_orbits (hI : TwoHSInterface) {G : Type} [Group G] [Finite G] {a z : G}
    (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z) (hF2 : Vert Fusion2Facts a z)
    (hF3 : Vert Fusion3Facts a z) (hPic : Vert A8Pictures a z) (hCls : GzClassFacts a z)
    {a₁ : G} (ha₁ : a₁ ∈ Gx z) (ha₁A : IsConj a a₁) (ha₁z : IsConj z (a₁ * z)) :
    (∀ m ∈ CFSG.Open.pCoreOf 2 (derivedOf (Gxy a₁ z)), m ≠ 1 → IsConj a m ∨ IsConj z m) ∧
      (∀ t ∈ CFSG.Open.pCoreOf 2 (derivedOf (Gxy a₁ z)), IsConj a t →
        Nat.card ↥(Gx t ⊓ derivedOf (Gxy a₁ z)) = 96) ∧
      IsConjOrbit (derivedOf (Gxy a₁ z))
        {t | t ∈ CFSG.Open.pCoreOf 2 (derivedOf (Gxy a₁ z)) ∧ IsConj a t} ∧
      Nat.card ↥{t | t ∈ CFSG.Open.pCoreOf 2 (derivedOf (Gxy a₁ z)) ∧ IsConj a t} = 10 ∧
      IsConjOrbit (derivedOf (Gxy a₁ z))
        {t | t ∈ CFSG.Open.pCoreOf 2 (derivedOf (Gxy a₁ z)) ∧ IsConj z t} ∧
      Nat.card ↥{t | t ∈ CFSG.Open.pCoreOf 2 (derivedOf (Gxy a₁ z)) ∧ IsConj z t} = 5 := by
  classical
  obtain ⟨hshape, -, hMeq, hM4, h960, hconj, hψex⟩ :=
    y4a_setup hI h hF1.self hF2.self hF3 ha₁ ha₁A ha₁z
  set Y' := derivedOf (Gxy a₁ z) with hY'
  set M := CFSG.Open.pCoreOf 2 Y' with hMdef
  obtain ⟨ψ, hψ, hker⟩ := hψex
  set A : Set G := {t | t ∈ M ∧ IsConj a t} with hAdef
  set B : Set G := {t | t ∈ M ∧ IsConj z t} with hBdef
  have hMY : M ≤ Y' := Subgroup.map_subtype_le _
  have hY'Y : Y' ≤ Gxy a₁ z := derivedOf_le _
  have hNot : ¬ IsConj a z := not_isConj_of_isF5Type hI h
  have hcomm : a₁ * z = z * a₁ := (mem_Gx.mp ha₁).symm
  have hMQ : ∀ m ∈ M, m ∈ Qz z := by
    intro m hm
    rw [hMeq] at hm
    exact (Subgroup.mem_inf.mp hm).1
  have hMsq : ∀ m ∈ M, m ^ 2 = 1 := fun m hm => hM4.1.2 m hm
  have hMab : ∀ m₁ ∈ M, ∀ m₂ ∈ M, m₁ * m₂ = m₂ * m₁ := by
    intro m₁ h₁ m₂ h₂
    haveI : IsMulCommutative ↥M := hM4.1.1
    exact congrArg Subtype.val (mul_comm' (M := ↥M) ⟨m₁, h₁⟩ ⟨m₂, h₂⟩)
  have h16 : Nat.card ↥M = 16 := by
    rw [hM4.2]
    norm_num
  have hcover : ∀ m ∈ M, m ≠ 1 → IsConj a m ∨ IsConj z m := fun m hm hm1 =>
    (y4a_types hI h hF2 hCls ha₁ ha₁A ha₁z (hMY hm) (hMQ m hm) (hMsq m hm) hm1).imp
      (fun h' => h'.1) (fun h' => h'.1)
  have hY : Nat.card ↥(Gxy a₁ z) = 3840 := card_of_isShapeTwoTwoTimesTwoFourA5 hshape
  have h96' : ∀ t ∈ M, IsConj a t → Nat.card ↥(Y' ⊓ Gx t) = 96 := by
    intro t ht htA
    have h384 := y4a_card_cent hI h hF2 hF3 hPic hCls ha₁ ha₁A ha₁z (hMY ht) (hMQ t ht)
      (hMsq t ht) htA
    have htr := y4a_card_stab_transfer hY'Y hconj ht
    rw [hY, h384, h960] at htr
    omega
  have h96 : ∀ t ∈ M, IsConj a t → Nat.card ↥(Gx t ⊓ Y') = 96 := by
    intro t ht htA
    rw [inf_comm]
    exact h96' t ht htA
  have h1A : (1 : G) ∉ A := by
    rintro ⟨-, h1⟩
    have ha1 : a = 1 := isConj_one_left.mp h1
    have h2 := h.orderOf_a
    rw [ha1, orderOf_one] at h2
    exact absurd h2 (by decide)
  have h1B : (1 : G) ∉ B := by
    rintro ⟨-, h1⟩
    have hz1 : z = 1 := isConj_one_left.mp h1
    have h2 := h.orderOf_z
    rw [hz1, orderOf_one] at h2
    exact absurd h2 (by decide)
  have hAB : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hxA⟩ ⟨-, hxB⟩
    exact hNot (hxA.trans hxB.symm)
  have hcover' : ∀ m ∈ M, m ≠ 1 → m ∈ A ∨ m ∈ B := fun m hm hm1 =>
    (hcover m hm hm1).imp (fun h' => ⟨hm, h'⟩) (fun h' => ⟨hm, h'⟩)
  have hinvA : ∀ l ∈ Y', ∀ c ∈ A, l * c * l⁻¹ ∈ A := by
    rintro l hl c ⟨hcM, hcw⟩
    exact ⟨y4a_conj_mem_pCoreOf hl hcM, hcw.trans (isConj_iff.mpr ⟨l, rfl⟩)⟩
  have hinvB : ∀ l ∈ Y', ∀ c ∈ B, l * c * l⁻¹ ∈ B := by
    rintro l hl c ⟨hcM, hcw⟩
    exact ⟨y4a_conj_mem_pCoreOf hl hcM, hcw.trans (isConj_iff.mpr ⟨l, rfl⟩)⟩
  have hAne : A.Nonempty := by
    obtain ⟨t, htM, htA⟩ :=
      y4a_exists_mem_2A hI h hF1 hF2 hF3 hPic ha₁A (IsConj.refl z) hcomm ha₁z
    refine ⟨t, ?_, htA⟩
    rw [hMeq]
    exact htM
  have hsum := y4a_card_add h16 (fun x hx => hx.1) (fun x hx => hx.1) h1A h1B hAB hcover'
  obtain ⟨hAorb, hAcard⟩ := y4a_isConjOrbit_of_card hinvA hAne
    (fun c hc => by rw [h960, h96' c hc.1 hc.2]) (by omega)
  have hBcard : Nat.card ↥B = 5 := by omega
  have hAnf : ∀ c ∈ A, ¬ Y' ≤ Gx c := by
    intro c hc hle
    have h1 := h96' c hc.1 hc.2
    rw [inf_eq_left.mpr hle, h960] at h1
    omega
  have hBorb := y4a_isConjOrbit_B h16 (fun x hx => hx.1) h1B hcover' hBcard hinvB hAnf
    (fun c hc => y4a_orbit_size ψ hψ hker hMY hMab hc.1)
  exact ⟨hcover, h96, hAorb, hAcard, hBorb, hBcard⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
