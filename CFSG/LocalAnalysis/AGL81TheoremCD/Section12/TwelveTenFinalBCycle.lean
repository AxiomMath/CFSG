module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveEightA9
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveTenWreath
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveTenFinalCorrected
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KParabolics
import CFSG.GroupTheory.SubgroupCardInf
import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81Basic
public import CFSG.ClassicalInvolution.Q3.Q3MFOU4F9
public import CFSG.GroupTheory.ConjTransport
public import CFSG.HardMathSupport.RichardWeiss.Proving.ConjugateGenerator
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveTenNine
public import CFSG.Quasithin.EmptyFaithful.SzN17Basic

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435

variable {G : Type} [Group G] [Finite G]
variable {M Q H : Subgroup G} {p d : ℕ} {L₁ L₂ L₃ : Subgroup G} {n₁ n₂ n₃ : ℕ}

private theorem one_le_pRank_centerIn_of_isThreeOnePlusTwo {D : Subgroup G}
    (hD : IsThreeOnePlusTwo ↥D) : 1 ≤ CFSG.Open.pRank 3 (CFSG.centerIn D) := by
  have hZcard : Nat.card (CFSG.centerIn D) = 3 := IsThreeOnePlusTwo.card_centerIn hD
  have hZel : IsElemAbelian 3 (CFSG.centerIn D) := by
    rw [CFSG.centerIn_eq_map_center]
    have hcenter : IsElemAbelian 3 (Subgroup.center ↥D) := by
      refine ⟨inferInstance, fun x _ => ?_⟩
      simpa using hD.2.2 x
    exact hcenter.map D.subtype
  have h := CFSG.SectionRank.le_pRank (p := 3) (by norm_num : 1 < 3)
    (H := CFSG.centerIn D) (E := CFSG.centerIn D) le_rfl hZel (k := 1)
    (by rw [hZcard]; norm_num)
  simpa using h

private theorem centerIn_not_le_of_normalizer {M E D : Subgroup G} {x : G}
    (hD : IsThreeOnePlusTwo ↥D) (hΓ : rankThreeGamma 1 3 E ≤ M)
    (hx : x ∈ normalizer (D : Set G)) (hxM : x ∉ M) :
    ¬ CFSG.centerIn D ≤ E := by
  intro hZE
  have hne : (CFSG.centerIn D).map (MulAut.conj x).toMonoidHom ≠ CFSG.centerIn D :=
    map_conj_ne_of_gamma_normalizer hZE (one_le_pRank_centerIn_of_isThreeOnePlusTwo hD) hΓ hxM
  exact hne ((Subgroup.mem_normalizer_iff_map_conj_eq).mp
    (normalizer_le_normalizer_centerIn D hx))

private theorem le_baseIn_of_isThreeOnePlusTwo {Q E D : Subgroup G} (e : ↥Q ≃* W3)
    (hEQ : E ≤ Q) (hE : IsElemAbelian 3 E) (hEcard : Nat.card E = 9)
    (hQcard : Nat.card Q = 81) (hZQ : CFSG.centerIn D = CFSG.centerIn Q)
    (hZnotE : ¬ CFSG.centerIn D ≤ E) : E ≤ baseIn e := by
  by_contra hEnle
  obtain ⟨s, hsE, hsA⟩ := Set.not_subset.mp hEnle
  have hsQ : s ∈ Q := hEQ hsE
  have hle : E ⊓ baseIn e ≤ CFSG.centerIn Q := by
    intro a ha
    have hcomm : Commute a s :=
      (commute_iff_eq a s).mpr (congrArg Subtype.val
        (hE.1.is_comm.comm (⟨a, ha.1⟩ : ↥E) (⟨s, hsE⟩ : ↥E)))
    exact mem_centerIn_of_commute_of_not_mem_baseIn e hsQ hsA ha.2 hcomm
  have hge : 3 ≤ Nat.card ↥(E ⊓ baseIn e) := by
    have h := CFSG.card_mul_card_le_card_inf_mul_card_of_le hEQ (baseIn_le e)
    rw [hEcard, card_baseIn e, hQcard] at h
    omega
  have hcenter : Nat.card (CFSG.centerIn Q) = 3 := card_centerIn_of_mulEquiv_W3 e
  have hEq : E ⊓ baseIn e = CFSG.centerIn Q :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcenter]; exact hge)
  exact hZnotE (by rw [hZQ, ← hEq]; exact inf_le_left)

private theorem card_inf_eq_nine {A D Q : Subgroup G}
    (hAQ : A ≤ Q) (hDQ : D ≤ Q) (hAcard : Nat.card A = 27) (hDcard : Nat.card D = 27)
    (hQcard : Nat.card Q = 81) (hAD : A ≠ D) : Nat.card ↥(A ⊓ D) = 9 := by
  have hge : 9 ≤ Nat.card ↥(A ⊓ D) := by
    have h := CFSG.card_mul_card_le_card_inf_mul_card_of_le hAQ hDQ
    rw [hAcard, hDcard, hQcard] at h
    omega
  have hlt : Nat.card ↥(A ⊓ D) < 27 := by
    have hle : Nat.card ↥(A ⊓ D) ≤ Nat.card A := Subgroup.card_le_of_le inf_le_left
    rw [hAcard] at hle
    refine lt_of_le_of_ne hle ?_
    intro heq
    have hEq : A ⊓ D = A :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [heq, hAcard])
    have hAleD : A ≤ D := by rw [← hEq]; exact inf_le_right
    exact hAD (Subgroup.eq_of_le_of_card_ge hAleD (by rw [hDcard, hAcard]))
  have hdvd : Nat.card ↥(A ⊓ D) ∣ 3 ^ 3 := by
    have h27 : (3 : ℕ) ^ 3 = 27 := by norm_num
    rw [h27, ← hAcard]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k, hk_le, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hge' : 9 ≤ 3 ^ k := by rw [← hk]; exact hge
  have hlt' : 3 ^ k < 27 := by rw [← hk]; exact hlt
  interval_cases k
  · norm_num at hge'
  · norm_num at hge'
  · rw [hk]; norm_num
  · norm_num at hlt'

private theorem not_le_of_card_inf {A D E : Subgroup G}
    (hEA : E ≤ A) (hEcard : Nat.card E = 9) (hADcard : Nat.card ↥(A ⊓ D) = 9)
    (hZleA : CFSG.centerIn D ≤ A) (hZnotE : ¬ CFSG.centerIn D ≤ E) : ¬ E ≤ D := by
  intro hED
  have hEinf : E ≤ A ⊓ D := le_inf hEA hED
  have hEq : E = A ⊓ D :=
    Subgroup.eq_of_le_of_card_ge hEinf (by rw [hEcard, hADcard])
  have hZle : CFSG.centerIn D ≤ E := by
    rw [hEq]
    exact le_inf hZleA inf_le_left
  exact hZnotE hZle

private theorem not_le_and_card_inf_of_base {Q E D : Subgroup G} (e : ↥Q ≃* W3)
    (hEQ : E ≤ Q) (hDQ : D ≤ Q) (hEcard : Nat.card E = 9)
    (hD : IsThreeOnePlusTwo ↥D) (hQcard : Nat.card Q = 81)
    (hZnotE : ¬ CFSG.centerIn D ≤ E) (hEbase : E ≤ baseIn e)
    (hZle : CFSG.centerIn D ≤ baseIn e) :
    ¬ E ≤ D ∧ Nat.card ↥(E ⊓ D) = 3 := by
  have hAc : IsMulCommutative (baseIn e) :=
    ⟨⟨fun a b => Subtype.ext (baseIn_comm e a.2 b.2)⟩⟩
  have hDnc : ¬ IsMulCommutative D :=
    CFSG.ComponentClassification.CatFC.DS81.not_isMulCommutative_of_isExtraspecialPGroup
      hD.1 (by rw [hD.2.1]; norm_num)
  have hAD : baseIn e ≠ D := by
    intro hEq
    exact hDnc (hEq ▸ hAc)
  have hADcard : Nat.card ↥(baseIn e ⊓ D) = 9 :=
    card_inf_eq_nine (baseIn_le e) hDQ (card_baseIn e) hD.2.1 hQcard hAD
  have hEnle : ¬ E ≤ D :=
    not_le_of_card_inf hEbase hEcard hADcard hZle hZnotE
  have hDcard' : Nat.card D = 3 ^ 3 := by rw [hD.2.1]; norm_num
  have hQcard' : Nat.card Q = 3 ^ 4 := by rw [hQcard]; norm_num
  have hBcard : Nat.card ↥(E ⊓ D) = 3 :=
    card_inf_eq_of_not_le (p := 3) Nat.prime_three (by rw [hEcard]; norm_num)
      hDcard' hQcard' hEQ hDQ hEnle
  exact ⟨hEnle, hBcard⟩

private theorem sup_map_conj_eq_of_twelveSix
    {M H Q D B : Subgroup G} {p : ℕ} {x : G}
    (h8 : CFSG.Blueprint.LieModel (modTwoCore (kSub p M H)) .PSp 2 3 1)
    (hQK : CFSG.ABGLocalTools.IsSylowOf 3 Q (kSub p M H))
    (hDQ : D ≤ Q) (hD : IsThreeOnePlusTwo ↥D)
    (hKM : kSub p M H ⊓ M =
      (kSub p M H ⊓ normalizer (thompsonSubgroup Q : Set G)) ⊔ pCoreOf 2 (kSub p M H))
    (hB : B ≤ thompsonSubgroup Q ⊓ D) (hBZ : ¬ B ≤ CFSG.centerIn D)
    (hx : x ∈ kSub p M H ⊓ normalizer (D : Set G)) (hxM : x ∉ M) :
    thompsonSubgroup Q ⊔ B.map (MulAut.conj x).toMonoidHom = Q := by
  refine thompsonSubgroup_sup_map_conj_eq_of_isThreeOnePlusTwo h8 hQK hDQ hD hB hBZ hx ?_
  intro hxA
  have hxKM : x ∈ kSub p M H ⊓ M := by
    rw [hKM]
    exact hxA
  exact hxM hxKM.2

private theorem map_conj_eq_self_of_fixed_of_three {b : G} (hb3 : b ^ 3 = 1)
    {X Y Z : Subgroup G} (hXY : X ≠ Y) (hXZ : X ≠ Z) (hYZ : Y ≠ Z)
    (hX : X.map (MulAut.conj b).toMonoidHom = X)
    (hY : Y.map (MulAut.conj b).toMonoidHom ∈ ({X, Y, Z} : Set (Subgroup G)))
    (hZ : Z.map (MulAut.conj b).toMonoidHom ∈ ({X, Y, Z} : Set (Subgroup G))) :
    Y.map (MulAut.conj b).toMonoidHom = Y ∧ Z.map (MulAut.conj b).toMonoidHom = Z := by
  have hinj : Function.Injective
      (fun L : Subgroup G => L.map (MulAut.conj b).toMonoidHom) :=
    Subgroup.map_injective (MulAut.conj b).injective
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hY hZ
  rcases hY with hYX | hYY | hYZ'
  · exfalso
    have h1 := CFSG.Quasithin.SzN17.map_conj_three (K := Y) hb3
    simp only [hYX, hX] at h1
    exact hXY h1
  · refine ⟨hYY, ?_⟩
    rcases hZ with hZX | hZY | hZZ
    · exfalso
      exact hXZ (hinj (hZX.trans hX.symm)).symm
    · exfalso
      exact hYZ (hinj (hZY.trans hYY.symm)).symm
    · exact hZZ
  · exfalso
    rcases hZ with hZX | hZY | hZZ
    · exact hXZ (hinj (hZX.trans hX.symm)).symm
    · have h1 := CFSG.Quasithin.SzN17.map_conj_three (K := Y) hb3
      simp only [hYZ', hZY] at h1
      exact hYZ h1.symm
    · exact hYZ (hinj (hYZ'.trans hZZ.symm))

private theorem false_of_fixed_all {Q A : Subgroup G} {b : G}
    (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃)
    (hn : n₁ = 1 ∧ n₂ = 1 ∧ n₃ = 1) (h3 : CFSG.Open.pRank 3 M ≤ 3)
    (hcard : (weakBlockSet M H).ncard = 3) (hQM : Q ≤ M) (hQ3 : IsPGroup 3 Q)
    (hQcard : Nat.card Q = 81) (hsup : A ⊔ Subgroup.zpowers b = Q)
    (hAle : A ≤ normalizer (L₁ : Set G) ⊓ normalizer (L₂ : Set G) ⊓
      normalizer (L₃ : Set G))
    (h1 : L₁.map (MulAut.conj b).toMonoidHom = L₁)
    (h2 : L₂.map (MulAut.conj b).toMonoidHom = L₂)
    (h3' : L₃.map (MulAut.conj b).toMonoidHom = L₃) : False := by
  have hb1 : b ∈ normalizer (L₁ : Set G) := (Subgroup.mem_normalizer_iff_map_conj_eq).mpr h1
  have hb2 : b ∈ normalizer (L₂ : Set G) := (Subgroup.mem_normalizer_iff_map_conj_eq).mpr h2
  have hb3 : b ∈ normalizer (L₃ : Set G) := (Subgroup.mem_normalizer_iff_map_conj_eq).mpr h3'
  have hble : Subgroup.zpowers b ≤
      normalizer (L₁ : Set G) ⊓ normalizer (L₂ : Set G) ⊓ normalizer (L₃ : Set G) :=
    Subgroup.zpowers_le.mpr ⟨⟨hb1, hb2⟩, hb3⟩
  have hQle : Q ≤ normalizer (L₁ : Set G) ⊓ normalizer (L₂ : Set G) ⊓
      normalizer (L₃ : Set G) := by
    rw [← hsup]
    exact sup_le hAle hble
  have hle := hd.card_le_of_le_normalizers hn h3 hcard hQM hQ3 hQle
  omega

private theorem map_conj_eq_third_of_eq_second {b : G} (hb3 : b ^ 3 = 1)
    (hne : L₁ ≠ L₂ ∧ L₁ ≠ L₃ ∧ L₂ ≠ L₃)
    (h12 : L₁.map (MulAut.conj b).toMonoidHom = L₂)
    (hfix2 : L₂.map (MulAut.conj b).toMonoidHom ≠ L₂)
    (hfix3 : L₃.map (MulAut.conj b).toMonoidHom ≠ L₃)
    (h2mem : L₂.map (MulAut.conj b).toMonoidHom ∈ ({L₁, L₂, L₃} : Set (Subgroup G)))
    (h3mem : L₃.map (MulAut.conj b).toMonoidHom ∈ ({L₁, L₂, L₃} : Set (Subgroup G))) :
    L₂.map (MulAut.conj b).toMonoidHom = L₃ ∧
      L₃.map (MulAut.conj b).toMonoidHom = L₁ := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h2mem h3mem
  have h23 : L₂.map (MulAut.conj b).toMonoidHom = L₃ := by
    rcases h2mem with h21 | h22 | h23
    · exfalso
      have h := CFSG.Quasithin.SzN17.map_conj_three (K := L₁) hb3
      simp only [h12, h21] at h
      exact hne.1 h.symm
    · exact absurd h22 hfix2
    · exact h23
  refine ⟨h23, ?_⟩
  rcases h3mem with h31 | h32 | h33
  · exact h31
  · exfalso
    have h := CFSG.Quasithin.SzN17.map_conj_three (K := L₂) hb3
    simp only [h23, h32] at h
    exact hfix2 (h23.trans h)
  · exact absurd h33 hfix3

private theorem map_conj_eq_second_of_eq_third {b : G} (hb3 : b ^ 3 = 1)
    (hne : L₁ ≠ L₂ ∧ L₁ ≠ L₃ ∧ L₂ ≠ L₃)
    (h13 : L₁.map (MulAut.conj b).toMonoidHom = L₃)
    (hfix2 : L₂.map (MulAut.conj b).toMonoidHom ≠ L₂)
    (hfix3 : L₃.map (MulAut.conj b).toMonoidHom ≠ L₃)
    (h2mem : L₂.map (MulAut.conj b).toMonoidHom ∈ ({L₁, L₂, L₃} : Set (Subgroup G)))
    (h3mem : L₃.map (MulAut.conj b).toMonoidHom ∈ ({L₁, L₂, L₃} : Set (Subgroup G))) :
    L₂.map (MulAut.conj b).toMonoidHom = L₁ ∧
      L₃.map (MulAut.conj b).toMonoidHom = L₂ := by
  have hinj : Function.Injective
      (fun L : Subgroup G => L.map (MulAut.conj b).toMonoidHom) :=
    Subgroup.map_injective (MulAut.conj b).injective
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h2mem h3mem
  have h21 : L₂.map (MulAut.conj b).toMonoidHom = L₁ := by
    rcases h2mem with h21 | h22 | h23
    · exact h21
    · exact absurd h22 hfix2
    · exfalso
      exact hne.1 (hinj (h13.trans h23.symm))
  refine ⟨h21, ?_⟩
  rcases h3mem with h31 | h32 | h33
  · exfalso
    exact hne.2.2 (hinj (h21.trans h31.symm))
  · exact h32
  · exact absurd h33 hfix3

private theorem map_conj_cycle_or_inverse {b : G} (hb3 : b ^ 3 = 1)
    (hne : L₁ ≠ L₂ ∧ L₁ ≠ L₃ ∧ L₂ ≠ L₃)
    (hmem : ∀ L ∈ ({L₁, L₂, L₃} : Set (Subgroup G)),
      L.map (MulAut.conj b).toMonoidHom ∈ ({L₁, L₂, L₃} : Set (Subgroup G)))
    (hfix1 : L₁.map (MulAut.conj b).toMonoidHom ≠ L₁)
    (hfix2 : L₂.map (MulAut.conj b).toMonoidHom ≠ L₂)
    (hfix3 : L₃.map (MulAut.conj b).toMonoidHom ≠ L₃) :
    (L₁.map (MulAut.conj b).toMonoidHom = L₂ ∧
      L₂.map (MulAut.conj b).toMonoidHom = L₃ ∧
      L₃.map (MulAut.conj b).toMonoidHom = L₁) ∨
    (L₁.map (MulAut.conj b⁻¹).toMonoidHom = L₂ ∧
      L₂.map (MulAut.conj b⁻¹).toMonoidHom = L₃ ∧
      L₃.map (MulAut.conj b⁻¹).toMonoidHom = L₁) := by
  have h1mem := hmem L₁ (by simp)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1mem
  rcases h1mem with h11 | h12 | h13
  · exact absurd h11 hfix1
  · obtain ⟨h23, h31⟩ := map_conj_eq_third_of_eq_second hb3 hne h12 hfix2 hfix3
      (hmem L₂ (by simp)) (hmem L₃ (by simp))
    exact Or.inl ⟨h12, h23, h31⟩
  · obtain ⟨h21, h32⟩ := map_conj_eq_second_of_eq_third hb3 hne h13 hfix2 hfix3
      (hmem L₂ (by simp)) (hmem L₃ (by simp))
    refine Or.inr ⟨?_, ?_, ?_⟩
    · rw [← h21, CFSG.GroupTheory.map_conj_map_conj_inv]
    · rw [← h32, CFSG.GroupTheory.map_conj_map_conj_inv]
    · rw [← h13, CFSG.GroupTheory.map_conj_map_conj_inv]

private theorem exists_generator_of_sup {Q E D : Subgroup G} {x : G}
    (hBcard : Nat.card ↥(E ⊓ D) = 3)
    (hsup : thompsonSubgroup Q ⊔ (E ⊓ D).map (MulAut.conj x).toMonoidHom = Q)
    (hQM : Q ≤ M) :
    ∃ b : G, (E ⊓ D).map (MulAut.conj x).toMonoidHom = Subgroup.zpowers b ∧
      b ^ 3 = 1 ∧ b ∈ M ∧ thompsonSubgroup Q ⊔ Subgroup.zpowers b = Q := by
  obtain ⟨b, hborder, hBx⟩ :=
    CFSG.HardMathSupport.RichardWeiss.Proving.exists_gen_map_conj hBcard x
  have hb3 : b ^ 3 = 1 := by
    rw [← hborder]
    exact pow_orderOf_eq_one b
  have hbC : b ∈ (E ⊓ D).map (MulAut.conj x).toMonoidHom := by
    rw [hBx]
    exact Subgroup.mem_zpowers b
  have hCQ : (E ⊓ D).map (MulAut.conj x).toMonoidHom ≤ Q := by
    rw [← hsup]
    exact le_sup_right
  have hsup' : thompsonSubgroup Q ⊔ Subgroup.zpowers b = Q := by
    rw [← hBx]
    exact hsup
  exact ⟨b, hBx, hb3, hQM (hCQ hbC), hsup'⟩

private theorem map_conj_mem_swaps {b : G}
    (hmem : ∀ L ∈ ({L₁, L₂, L₃} : Set (Subgroup G)),
      L.map (MulAut.conj b).toMonoidHom ∈ ({L₁, L₂, L₃} : Set (Subgroup G))) :
    (∀ L ∈ ({L₂, L₁, L₃} : Set (Subgroup G)),
        L.map (MulAut.conj b).toMonoidHom ∈ ({L₂, L₁, L₃} : Set (Subgroup G))) ∧
      ∀ L ∈ ({L₃, L₁, L₂} : Set (Subgroup G)),
        L.map (MulAut.conj b).toMonoidHom ∈ ({L₃, L₁, L₂} : Set (Subgroup G)) := by
  have hswap21 : ({L₂, L₁, L₃} : Set (Subgroup G)) = {L₁, L₂, L₃} := by
    ext L
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hswap31 : ({L₃, L₁, L₂} : Set (Subgroup G)) = {L₁, L₂, L₃} := by
    ext L
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  refine ⟨?_, ?_⟩
  · intro L hL
    rw [hswap21] at hL ⊢
    exact hmem L hL
  · intro L hL
    rw [hswap31] at hL ⊢
    exact hmem L hL

private theorem map_conj_ne_self_of_sup {Q : Subgroup G} {b : G}
    (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃)
    (h6 : TwelveSix M H p d L₁ L₂ L₃ n₁ n₂ n₃)
    (h3 : CFSG.Open.pRank 3 M ≤ 3) (hcard : (weakBlockSet M H).ncard = 3)
    (hQM : Q ≤ M) (hQ3 : IsPGroup 3 Q) (hQcard : Nat.card Q = 81)
    (hb3 : b ^ 3 = 1) (hsupA : (Q ⊓ jSub M H) ⊔ Subgroup.zpowers b = Q)
    (hbM : b ∈ M) :
    L₁.map (MulAut.conj b).toMonoidHom ≠ L₁ ∧
      L₂.map (MulAut.conj b).toMonoidHom ≠ L₂ ∧
      L₃.map (MulAut.conj b).toMonoidHom ≠ L₃ := by
  have hAle : Q ⊓ jSub M H ≤ normalizer (L₁ : Set G) ⊓ normalizer (L₂ : Set G) ⊓
      normalizer (L₃ : Set G) := by
    refine le_inf (le_inf ?_ ?_) ?_
    · exact le_trans inf_le_right hd.jSub_le_normalizer_left
    · exact le_trans inf_le_right hd.jSub_le_normalizer_middle
    · exact le_trans inf_le_right hd.jSub_le_normalizer_right
  have hmapmem : ∀ L ∈ ({L₁, L₂, L₃} : Set (Subgroup G)),
      L.map (MulAut.conj b).toMonoidHom ∈ ({L₁, L₂, L₃} : Set (Subgroup G)) :=
    fun L hL => hd.map_conj_mem hbM hL
  have hn : n₁ = 1 ∧ n₂ = 1 ∧ n₃ = 1 :=
    ⟨TwelveSix.n₁_eq_one hd h6, TwelveSix.n₂_eq_one hd h6, TwelveSix.n₃_eq_one hd h6⟩
  have hne := hd.pairwise_ne hcard
  obtain ⟨hmapmem21, hmapmem31⟩ := map_conj_mem_swaps hmapmem
  have hfix1 : L₁.map (MulAut.conj b).toMonoidHom ≠ L₁ := by
    intro h1
    have h23 := map_conj_eq_self_of_fixed_of_three hb3 hne.1 hne.2.1 hne.2.2 h1
      (hmapmem L₂ (by simp)) (hmapmem L₃ (by simp))
    exact false_of_fixed_all hd hn h3 hcard hQM hQ3 hQcard hsupA hAle h1 h23.1 h23.2
  refine ⟨hfix1, ?_, ?_⟩
  · intro h2
    have h13 := map_conj_eq_self_of_fixed_of_three hb3 hne.1.symm hne.2.2 hne.2.1 h2
      (hmapmem21 L₁ (by simp)) (hmapmem21 L₃ (by simp))
    exact false_of_fixed_all hd hn h3 hcard hQM hQ3 hQcard hsupA hAle h13.1 h2 h13.2
  · intro h3'
    have h12 := map_conj_eq_self_of_fixed_of_three hb3 hne.2.1.symm hne.2.2.symm hne.1 h3'
      (hmapmem31 L₁ (by simp)) (hmapmem31 L₂ (by simp))
    exact false_of_fixed_all hd hn h3 hcard hQM hQ3 hQcard hsupA hAle h12.1 h12.2 h3'

private theorem exists_base_of_twelveSix (h : TwelveCtx G M p Q H)
    (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃) (h6 : TwelveSix M H p d L₁ L₂ L₃ n₁ n₂ n₃)
    (h3 : CFSG.Open.pRank 3 M ≤ 3) (hcard : (weakBlockSet M H).ncard = 3)
    {E D : Subgroup G} (hEQ : E ≤ Q) (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2)
    (hΓ : rankThreeGamma 1 p E ≤ M) (hD : IsThreeOnePlusTwo ↥D) (hDQ : D ≤ Q) {x : G}
    (hx : x ∈ kSub p M H ⊓ normalizer (D : Set G)) (hxM : x ∉ M) :
    p = 3 ∧ ∃ e : ↥Q ≃* W3,
      E ≤ baseIn e ∧ baseIn e = Q ⊓ jSub M H ∧
      thompsonSubgroup Q = Q ⊓ jSub M H ∧
      CFSG.ABGLocalTools.IsSylowOf 3 Q (kSub p M H) ∧
      Nat.card Q = 81 ∧ CFSG.centerIn D = CFSG.centerIn Q ∧
      CFSG.centerIn D ≤ baseIn e ∧ ¬ CFSG.centerIn D ≤ E := by
  obtain ⟨hp3, -, hQsylK, -, hA⟩ := twelveSevenData h hd h6 h3 hcard
  subst hp3
  obtain ⟨e, hAcomm_raw, hAcard_raw⟩ := hA
  have hJ : thompsonSubgroup Q = Q ⊓ jSub M H := by
    change thompsonSubgroup Q = Q ⊓ jSub M H
    exact thompsonSubgroup_eq_inf_of_twelveSevenA ⟨e, hAcomm_raw, hAcard_raw⟩
  have hbase : baseIn e = Q ⊓ jSub M H := by
    have h1 : thompsonSubgroup Q = baseIn e := by
      rw [CFSG.thompsonSubgroup_eq_ambientOrderThompson,
        ← CFSG.Open.thompsonSubgroup_eq_ambientOrderThompson]
      exact thompsonSubgroup_eq_baseIn e
    rw [← h1, hJ]
  have hQcard : Nat.card Q = 81 := card_of_equiv e
  have hEcard9 : Nat.card E = 9 := by simpa using hEcard
  have hZQ : CFSG.centerIn D = CFSG.centerIn Q := centerIn_eq_of_isThreeOnePlusTwo e hDQ hD
  have hZnotE : ¬ CFSG.centerIn D ≤ E := centerIn_not_le_of_normalizer hD hΓ hx.2 hxM
  have hEbase : E ≤ baseIn e :=
    le_baseIn_of_isThreeOnePlusTwo e hEQ hE hEcard9 hQcard hZQ hZnotE
  have hZle : CFSG.centerIn D ≤ baseIn e := by
    rw [hZQ]
    exact centerIn_le_baseIn e
  exact ⟨rfl, e, hEbase, hbase, hJ, hQsylK, hQcard, hZQ, hZle, hZnotE⟩

private theorem map_conj_cycle_of_twelveSix (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃)
    (hcard : (weakBlockSet M H).ncard = 3) {b : G} (hbM : b ∈ M) (hb3 : b ^ 3 = 1)
    (hfix1 : L₁.map (MulAut.conj b).toMonoidHom ≠ L₁)
    (hfix2 : L₂.map (MulAut.conj b).toMonoidHom ≠ L₂)
    (hfix3 : L₃.map (MulAut.conj b).toMonoidHom ≠ L₃) :
    (L₁.map (MulAut.conj b).toMonoidHom = L₂ ∧
      L₂.map (MulAut.conj b).toMonoidHom = L₃ ∧
      L₃.map (MulAut.conj b).toMonoidHom = L₁) ∨
    (L₁.map (MulAut.conj b⁻¹).toMonoidHom = L₂ ∧
      L₂.map (MulAut.conj b⁻¹).toMonoidHom = L₃ ∧
      L₃.map (MulAut.conj b⁻¹).toMonoidHom = L₁) :=
  map_conj_cycle_or_inverse hb3 (hd.pairwise_ne hcard)
    (fun L hL => hd.map_conj_mem hbM hL) hfix1 hfix2 hfix3

theorem exists_threeCycle_of_twelveSix (h : TwelveCtx G M p Q H)
    (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃) (h6 : TwelveSix M H p d L₁ L₂ L₃ n₁ n₂ n₃)
    (h3 : CFSG.Open.pRank 3 M ≤ 3) (hcard : (weakBlockSet M H).ncard = 3)
    {E D : Subgroup G} (hEQ : E ≤ Q) (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2)
    (hΓ : rankThreeGamma 1 p E ≤ M) (hD : IsThreeOnePlusTwo ↥D) (hDQ : D ≤ Q) {x : G}
    (hx : x ∈ kSub p M H ⊓ normalizer (D : Set G)) (hxM : x ∉ M) :
    ∃ b : G, (E ⊓ D).map (MulAut.conj x).toMonoidHom = Subgroup.zpowers b ∧ b ^ 3 = 1 ∧
      b ∈ M ∧ L₁.map (MulAut.conj b).toMonoidHom = L₂ ∧
      L₂.map (MulAut.conj b).toMonoidHom = L₃ ∧ L₃.map (MulAut.conj b).toMonoidHom = L₁ := by
  obtain ⟨hp3, e, hEbase, hbase, hJ, hQsylK, hQcard, hZQ, hZle, hZnotE⟩ :=
    exists_base_of_twelveSix h hd h6 h3 hcard hEQ hE hEcard hΓ hD hDQ hx hxM
  subst hp3
  have hEcard9 : Nat.card E = 9 := by simpa using hEcard
  obtain ⟨hEnle, hBcard⟩ :=
    not_le_and_card_inf_of_base e hEQ hDQ hEcard9 hD hQcard hZnotE hEbase hZle
  have hKM : kSub 3 M H ⊓ M =
      (kSub 3 M H ⊓ normalizer (thompsonSubgroup Q : Set G)) ⊔ pCoreOf 2 (kSub 3 M H) :=
    TwelveSix.part_six hd h6 Q (isSylowOf_three_inf h hd h6 h3 hcard)
  have hBle : E ⊓ D ≤ thompsonSubgroup Q ⊓ D := by
    refine le_inf ?_ inf_le_right
    rw [hJ, ← hbase]
    exact le_trans inf_le_left hEbase
  have hBZ : ¬ E ⊓ D ≤ CFSG.centerIn D := by
    intro hBleZ
    have hZcard : Nat.card (CFSG.centerIn D) = 3 := IsThreeOnePlusTwo.card_centerIn hD
    have hEq : E ⊓ D = CFSG.centerIn D :=
      Subgroup.eq_of_le_of_card_ge hBleZ (by rw [hBcard, hZcard])
    exact hZnotE (by rw [← hEq]; exact inf_le_left)
  have hsup : thompsonSubgroup Q ⊔ (E ⊓ D).map (MulAut.conj x).toMonoidHom = Q :=
    sup_map_conj_eq_of_twelveSix (twelveEight_of_twelveSix h hd h6 h3 hcard) hQsylK hDQ hD
      hKM hBle hBZ hx hxM
  obtain ⟨b, hBx, hb3, hbM, hsup'⟩ := exists_generator_of_sup hBcard hsup h.Q_le_M
  have hsupA : (Q ⊓ jSub M H) ⊔ Subgroup.zpowers b = Q := by
    rw [← hJ]
    exact hsup'
  obtain ⟨hfix1, hfix2, hfix3⟩ :=
    map_conj_ne_self_of_sup hd h6 h3 hcard h.Q_le_M h.Q_isPGroup hQcard hb3 hsupA hbM
  rcases map_conj_cycle_of_twelveSix hd hcard hbM hb3 hfix1 hfix2 hfix3 with
    ⟨h12, h23, h31⟩ | ⟨h1inv, h2inv, h3inv⟩
  · exact ⟨b, hBx, hb3, hbM, h12, h23, h31⟩
  · refine ⟨b⁻¹, ?_, ?_, M.inv_mem hbM, h1inv, h2inv, h3inv⟩
    · rw [hBx, Subgroup.zpowers_inv]
    · rw [inv_pow, hb3, inv_one]

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
