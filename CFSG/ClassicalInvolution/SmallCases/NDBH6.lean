module

public import CFSG.ClassicalInvolution.SmallCases.NDB2Vertex
public import CFSG.ClassicalInvolution.AschTight.Hall196Idx
public import CFSG.ClassicalInvolution.SmallCases.NDBH2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.AscP1Nine3 CFSG.ClassicalInvolution.Asc77.T8
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen CFSG.ClassicalInvolution.Asc77.T8R
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.Assembly.Dichotomy (involutionOddCore odd_card_involutionOddCore)
open scoped commutatorElement

namespace T8R.Loc

section Shape

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}


@[expose] def ShapeAt (p f : ℕ) [Fact p.Prime] (Ω : Set (Subgroup G)) (z : G)
    (J : Subgroup G) : Prop :=
  ∀ M ∈ tqMembers Ω z, ∀ m : G, IsClassicalMember p f M m → m ≠ z →
    modOdd z (exactCore z M) = modOdd z (exactCore z J)

theorem eq_of_modOdd_le {A E : Subgroup G} (hA : IsPGroup 2 ↥A)
    (hAC : A ≤ Subgroup.centralizer ({z} : Set G)) (hTA : T ≤ A) (hTE : IsSylow2In T E)
    (hEC : E ≤ Subgroup.centralizer ({z} : Set G)) (hle : modOdd z A ≤ modOdd z E) : A = T := by
  have hsyl : IsSylow2In (modOdd z T) (modOdd z E) :=
    Disconnected.AschTight.Hall196.isSylow2In_map_hom (oddQuotMk z) (hTE.subgroupOf hEC)
  have hA2 : IsPGroup 2 ↥(modOdd z A) := (hA.comap_subtype.map _)
  have hTA' : modOdd z T ≤ modOdd z A :=
    Subgroup.map_mono fun _ hx => Subgroup.mem_subgroupOf.mpr (hTA (Subgroup.mem_subgroupOf.mp hx))
  have heq : modOdd z A = modOdd z T := hsyl.eq_of_le hA2 hle hTA'
  refine le_antisymm (fun a ha => ?_) hTA
  have hmem : oddQuotMk z ⟨a, hAC ha⟩ ∈ modOdd z A :=
    ⟨⟨a, hAC ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
  rw [heq] at hmem
  obtain ⟨τ, hτ, hπ⟩ := hmem
  have hτT : (τ : G) ∈ T := Subgroup.mem_subgroupOf.mp hτ
  have hdC : a * (τ : G)⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mul_mem _ (hAC ha) (Subgroup.inv_mem _ τ.2)
  have hd1 : oddQuotMk z ⟨a * (τ : G)⁻¹, hdC⟩ = 1 := by
    have e : (⟨a * (τ : G)⁻¹, hdC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) = ⟨a, hAC ha⟩ * τ⁻¹ :=
      rfl
    rw [e, map_mul, map_inv, ← hπ, mul_inv_cancel]
  have hdO : a * (τ : G)⁻¹ ∈ involutionOddCore z :=
    Lemma52Proof.mem_involutionOddCore_of_oddQuotMk_eq_one hdC hd1
  have hdA : a * (τ : G)⁻¹ ∈ A := A.mul_mem ha (A.inv_mem (hTA hτT))
  have hd : a * (τ : G)⁻¹ = 1 := eq_one_of_isPGroup_of_mem_odd (odd_card_involutionOddCore z) hdO
    (hA.to_le (Subgroup.zpowers_le.mpr hdA))
  have : a = τ := by
    calc a = a * (τ : G)⁻¹ * τ := by group
      _ = τ := by rw [hd, one_mul]
  rw [this]
  exact hτT

theorem classical_of_unique (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {L : Subgroup G} (hL : L ∈ Ω) {y : G} (hy : IsUniqueInvolution L y) :
    IsClassicalMember p f L y := by
  obtain ⟨x, hx⟩ := hΩ.classical L hL
  rwa [← (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hx).eq hy]

theorem ne_of_std8Core (hs : Std8Core p f Ω K J S R T W z t) : t ≠ z := fun h =>
  hs.hJ.2.1 (hs.noTwins J ⟨hs.hJ.1, z, hs.hz, h ▸ hs.ht⟩)

theorem mem_tqMembers_of_nbr (hs : Std8Core p f Ω K J S R T W z t) {L : Subgroup G}
    (hL : L ∈ omegaNbr Ω K) : L ∈ tqMembers Ω z :=
  NDB.NDBH.mem_tqMembers_of_dAdj hs.stand.odd hs.stand.five hs.stand.hyp hs.stand.mem hL.1
    (Or.inl hL) (classical_of_unique hs.stand.odd hs.stand.five hs.stand.hyp hs.stand.mem hs.hz)

theorem zt_of_shape (C : XCtx p f Ω z) (hs : Std8Core p f Ω K J S R T W z t)
    (hsh : ShapeAt p f Ω z J) {y : G} (hy : y ∈ Subgroup.centralizer ({z} : Set G)) :
    y * (z * t) * y⁻¹ * (z * t)⁻¹ ∈ involutionOddCore z := by
  have hp := hs.stand.odd
  have hq := hs.stand.five
  have hΩ := hs.stand.hyp
  have hJz := mem_tqMembers_of_nbr hs hs.hJ
  have hJt : IsClassicalMember p f J t := classical_of_unique hp hq hΩ hs.hJ.1 hs.ht
  have hJy : conjSub y J ∈ tqMembers Ω z := conjSub_mem_tqMembers hΩ.conjInvariant hy hJz
  have hJyt := hJt.conj y
  have hyz : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp hy
  have htz : t * z = z * t := (T8.mul_comm_of_mem_omegaNbr hp hΩ hs.hz hs.hJ hs.ht).symm
  have hyt : y * t * y⁻¹ ≠ z := fun h => ne_of_std8Core hs (by
    calc t = y⁻¹ * (y * t * y⁻¹) * y := by group
      _ = y⁻¹ * z * y := by rw [h]
      _ = y⁻¹ * (y * z) := by rw [hyz]; group
      _ = z := by group)
  have u1 := C.isUniqueInvolution_modOdd hJy hJyt
  rw [hsh _ hJy _ hJyt hyt] at u1
  have heq := u1.eq (C.isUniqueInvolution_modOdd hJz hJt)
  have hgC : y * t * y⁻¹ * t⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mul_mem _ (C.involution_mem_centralizer hJy hJyt)
      (Subgroup.inv_mem _ (C.involution_mem_centralizer hJz hJt))
  have hg : y * t * y⁻¹ * t⁻¹ ∈ involutionOddCore z := by
    refine Lemma52Proof.mem_involutionOddCore_of_oddQuotMk_eq_one hgC ?_
    have e : (⟨y * t * y⁻¹ * t⁻¹, hgC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) =
        ⟨y * t * y⁻¹, C.involution_mem_centralizer hJy hJyt⟩ *
          (⟨t, C.involution_mem_centralizer hJz hJt⟩)⁻¹ := rfl
    rw [e, map_mul, map_inv, heq, mul_inv_cancel]
  have hzc : Commute z (y * t * y⁻¹ * t⁻¹) := by
    have h1 : Commute z y := hyz.symm
    have h2 : Commute z t := htz.symm
    exact ((h1.mul_right h2).mul_right h1.inv_right).mul_right h2.inv_right
  have e : y * (z * t) * y⁻¹ * (z * t)⁻¹ = y * t * y⁻¹ * t⁻¹ := by
    calc y * (z * t) * y⁻¹ * (z * t)⁻¹ = (y * z) * t * y⁻¹ * t⁻¹ * z⁻¹ := by group
      _ = z * (y * t * y⁻¹ * t⁻¹) * z⁻¹ := by rw [hyz]; group
      _ = (y * t * y⁻¹ * t⁻¹) * z * z⁻¹ := by rw [hzc.eq]
      _ = y * t * y⁻¹ * t⁻¹ := by group
  rw [e]
  exact hg

theorem invol_of_shape (C : XCtx p f Ω z) (hs : Std8Core p f Ω K J S R T W z t)
    (hsh : ShapeAt p f Ω z J) {L : Subgroup G} (hL : L ∈ omegaNbr Ω K) {y : G}
    (hy : IsUniqueInvolution L y) : y * t⁻¹ ∈ involutionOddCore z := by
  have hp := hs.stand.odd
  have hq := hs.stand.five
  have hΩ := hs.stand.hyp
  have hJz := mem_tqMembers_of_nbr hs hs.hJ
  have hJt : IsClassicalMember p f J t := classical_of_unique hp hq hΩ hs.hJ.1 hs.ht
  have hLz := mem_tqMembers_of_nbr hs hL
  have hLy : IsClassicalMember p f L y := classical_of_unique hp hq hΩ hL.1 hy
  have hyz : y ≠ z := fun h => hL.2.1 (hs.noTwins L ⟨hL.1, z, hs.hz, h ▸ hy⟩)
  have u1 := C.isUniqueInvolution_modOdd hLz hLy
  rw [hsh _ hLz _ hLy hyz] at u1
  have heq := u1.eq (C.isUniqueInvolution_modOdd hJz hJt)
  have hgC : y * t⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mul_mem _ (C.involution_mem_centralizer hLz hLy)
      (Subgroup.inv_mem _ (C.involution_mem_centralizer hJz hJt))
  refine Lemma52Proof.mem_involutionOddCore_of_oddQuotMk_eq_one hgC ?_
  have e : (⟨y * t⁻¹, hgC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) =
      ⟨y, C.involution_mem_centralizer hLz hLy⟩ *
        (⟨t, C.involution_mem_centralizer hJz hJt⟩)⁻¹ := rfl
  rw [e, map_mul, map_inv, heq, mul_inv_cancel]

theorem modOdd_sup {A B : Subgroup G} (hA : A ≤ Subgroup.centralizer ({z} : Set G))
    (hB : B ≤ Subgroup.centralizer ({z} : Set G)) :
    modOdd z (A ⊔ B) = modOdd z A ⊔ modOdd z B := by
  show ((A ⊔ B).subgroupOf _).map _ = (A.subgroupOf _).map _ ⊔ (B.subgroupOf _).map _
  rw [Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

theorem modOdd_mono {A B : Subgroup G} (h : A ≤ B) : modOdd z A ≤ modOdd z B :=
  Subgroup.map_mono fun _ hx => Subgroup.mem_subgroupOf.mpr (h (Subgroup.mem_subgroupOf.mp hx))

theorem rset_of_shape (hs : Std8Core p f Ω K J S R T W z t) (hsh : ShapeAt p f Ω z J)
    {P : Subgroup G} (hP : P ∈ RSet Ω) (hPS : P ≤ (S : Subgroup G)) : P = R ∨ P = T := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hRsyl : IsSylow2In R K := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hK hRΩ hRK
  have hTsyl : IsSylow2In T J := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hJΩ hTΩ hTJ
  by_contra hcon
  push Not at hcon
  obtain ⟨M, hM, hPM⟩ := exists_isSylow2In_of_mem_RSet hP
  have hMK : M ≠ K := by
    rintro rfl
    exact hcon.1 (eq_of_isSylow2In_of_le_sylow hPM hRsyl hPS hRS)
  have hzR : z ∈ R := T3.mem_of_isPGroup hs.hz hRK hRsyl.2.1
    (by have := hΩ.eight_le_of_mem_RSet hp hRΩ; omega)
  have hcomm : Commutes P R :=
    l6_7_proved p f hp hq G Ω hΩ S P hP R hRΩ hPS hRS hcon.1
  have hPc : P ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx z hzR)
  have hcommT : Commutes T R :=
    l6_7_proved p f hp hq G Ω hΩ S T hTΩ R hRΩ hTS hRS (R_ne_T hs).symm
  have hTc : T ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcommT x hx z hzR)
  have hP8 := hΩ.eight_le_of_mem_RSet hp hP
  have hPN : P ≤ Subgroup.normalizer (K : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hp hq hK hM (Ne.symm hMK) hs.hz hPM.1 hPM.2.1
      (by omega) hPc
  have hMnbr : M ∈ omegaNbr Ω K := ⟨hM, hMK, P, hP, hPM.1, hPN⟩
  have hMz := mem_tqMembers_of_nbr hs hMnbr
  have hJz := mem_tqMembers_of_nbr hs hs.hJ
  obtain ⟨m, hm⟩ := hΩ.classical M hM
  have hmz : m ≠ z := fun h => hMK (hs.noTwins M ⟨hM, z, hs.hz,
    h ▸ ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hm⟩)
  have hsh' := hsh M hMz m hm hmz
  have hz2 : IsPGroup 2 (Subgroup.zpowers z) := isPGroup_zpowers_of_sq_eq_one hs.hz.sq
  have hPE : P ≤ exactCore z M := ((isSylow2In_exactCore_iff hΩ hz2 hM hMz.2).mpr ⟨hPM, hPc⟩).1
  have hTE : IsSylow2In T (exactCore z J) :=
    (isSylow2In_exactCore_iff hΩ hz2 hJΩ hJz.2).mpr ⟨hTsyl, hTc⟩
  have hle : modOdd z (P ⊔ T) ≤ modOdd z (exactCore z J) := by
    rw [modOdd_sup hPc hTc]
    exact sup_le (hsh' ▸ modOdd_mono hPE) (modOdd_mono hTE.1)
  have hAT := eq_of_modOdd_le (S.isPGroup'.to_le (sup_le hPS hTS)) (sup_le hPc hTc) le_sup_right
    hTE (exactCore_le_centralizer z J) hle
  have hPT : P ≤ T := hAT ▸ le_sup_left
  have hcardP : Nat.card P = Nat.card T := by
    rw [hΩ.natCard_isSylow2In hM hPM, hΩ.natCard_isSylow2In hJΩ hTsyl]
  exact hcon.2 (Subgroup.eq_of_le_of_card_ge hPT (le_of_eq hcardP.symm))

theorem four_of_shape (hs : Std8Core p f Ω K J S R T W z t) (hsh : ShapeAt p f Ω z J)
    {M : Subgroup G} (hM : M ∈ Ω) (h4 : 4 ≤ Nat.card ↥(M ⊓ (S : Subgroup G))) (hMJ : M ≠ J) :
    M ∉ omegaNbr Ω K := by
  intro hmem
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hcl := hΩ.conjInvariant
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hRsyl : IsSylow2In R K := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hK hRΩ hRK
  have hTsyl : IsSylow2In T J := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hJΩ hTΩ hTJ
  have h8T := hΩ.eight_le_of_mem_RSet hp hTΩ
  have hMz := mem_tqMembers_of_nbr hs hmem
  have hJz := mem_tqMembers_of_nbr hs hs.hJ
  obtain ⟨m, hm⟩ := hΩ.classical M hM
  have hmz : m ≠ z := fun h => hmem.2.1 (hs.noTwins M ⟨hM, z, hs.hz,
    h ▸ ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hm⟩)
  have hsh' := hsh M hMz m hm hmz
  have hz2 : IsPGroup 2 (Subgroup.zpowers z) := isPGroup_zpowers_of_sq_eq_one hs.hz.sq
  have hzt : z ≠ t := fun h => ne_of_std8Core hs h.symm
  have hztc : z * t = t * z := T8.mul_comm_of_mem_omegaNbr hp hΩ hs.hz hs.hJ hs.ht
  have hzR : z ∈ R := T3.mem_of_isPGroup hs.hz hRK hRsyl.2.1
    (by have := hΩ.eight_le_of_mem_RSet hp hRΩ; omega)
  have hcommT : Commutes T R :=
    l6_7_proved p f hp hq G Ω hΩ S T hTΩ R hRΩ hTS hRS (R_ne_T hs).symm
  have hTc : T ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcommT x hx z hzR)
  have hMSc : M ⊓ (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
    intro s hs'
    have hsS : s ∈ (S : Subgroup G) := hs'.2
    have hsS' : ∀ P ≤ (S : Subgroup G), conjSub s P ≤ (S : Subgroup G) := by
      intro P hP
      have := conjSub_mono (n := s) hP
      rwa [conjSub_eq_self_of_mem hsS] at this
    rcases rset_of_shape hs hsh (RSet.conj hcl hRΩ s) (hsS' R hRS) with hR' | hR'
    · have hK' : conjSub s K = K := T8.conjSub_eq_of_conjSub_eq hp hΩ hK hRΩ hRK hR'
      have h1 := hs.hz.conj_eq hK'
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc s * z = (s * z * s⁻¹) * s := by group
        _ = z * s := by rw [h1]
    · exfalso
      have hK' : conjSub s K = J := hΩ.eq_of_le_of_le (hcl s K hK) hJΩ hTsyl.2.1 (by omega)
        (hR' ▸ conjSub_mono (n := s) hRK) hTJ
      have h1 : s * z * s⁻¹ = t := (hs.ht.eq (hK' ▸ hs.hz.conj s)).symm
      have hcm : ⁅z, s⁆ ∈ oddCoreIn M := (mem_trivialOnQuot_iff.mp hMz.2).2 s hs'.1
      have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hs.hz.sq
      have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right hs.ht.sq
      have e : ⁅z, s⁆ = z * t := by
        rw [commutatorElement_def, hzinv]
        calc z * s * z * s⁻¹ = z * (s * z * s⁻¹) := by group
          _ = z * t := by rw [h1]
      rw [e] at hcm
      have hzt2 : (z * t) * (z * t) = 1 := by
        calc z * t * (z * t) = z * (t * z) * t := by group
          _ = z * (z * t) * t := by rw [hztc]
          _ = (z * z) * (t * t) := by group
          _ = 1 := by rw [hs.hz.sq, hs.ht.sq, one_mul]
      have h1' : z * t = 1 := eq_one_of_isPGroup_of_mem_odd (odd_card_oddCoreIn M) hcm
        (isPGroup_zpowers_of_sq_eq_one hzt2)
      exact hzt (by
        calc z = z * t * t⁻¹ := by group
          _ = t⁻¹ := by rw [h1', one_mul]
          _ = t := htinv)
  have hMSE : M ⊓ (S : Subgroup G) ≤ exactCore z M := fun s hs' =>
    NDB.Vertex.mem_exactCore_of_isPGroup hΩ hp hq hz2 hMz hs'.1
      (Subgroup.mem_centralizer_singleton_iff.mp (hMSc hs'))
      (S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hs'.2))
  have hTE : IsSylow2In T (exactCore z J) :=
    (isSylow2In_exactCore_iff hΩ hz2 hJΩ hJz.2).mpr ⟨hTsyl, hTc⟩
  have hle : modOdd z (M ⊓ (S : Subgroup G) ⊔ T) ≤ modOdd z (exactCore z J) := by
    rw [modOdd_sup hMSc hTc]
    exact sup_le (hsh' ▸ modOdd_mono hMSE) (modOdd_mono hTE.1)
  have hAT := eq_of_modOdd_le (S.isPGroup'.to_le (sup_le inf_le_right hTS)) (sup_le hMSc hTc)
    le_sup_right hTE (exactCore_le_centralizer z J) hle
  have hMST : M ⊓ (S : Subgroup G) ≤ J := (hAT ▸ le_sup_left : M ⊓ (S : Subgroup G) ≤ T).trans hTJ
  exact hMJ (hΩ.eq_of_le_of_le hM hJΩ S.isPGroup'.to_inf_right (by omega) inf_le_left hMST)

theorem loc26_of_shape (C : XCtx p f Ω z) (hs : Std8Core p f Ω K J S R T W z t)
    (hsh : ShapeAt p f Ω z J) : Loc26 Ω K J S R T z t (involutionOddCore z) :=
  ⟨odd_card_involutionOddCore z, rset_of_shape hs hsh, four_of_shape hs hsh,
    invol_of_shape C hs hsh, zt_of_shape C hs hsh⟩

end Shape

end T8R.Loc

end CFSG.ClassicalInvolution.Asc77
