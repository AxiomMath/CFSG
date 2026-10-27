module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpE4Dict
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpYLift
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SubSecLiftAux
public import CFSG.GH74.GLS.Stage2.Local.Lemma23e
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpE4Loc

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Sl2Cl

variable {B : Type} [Group B]

@[expose] def Sl2Cl (p : ℕ) (z : B) (X K : Subgroup B) : Prop := C42a p z X K ∨ C42b p z X K

theorem Sl2Cl.X_le {p : ℕ} {z : B} {X K : Subgroup B} (h : Sl2Cl p z X K) : X ≤ K := by
  rcases h with ⟨-, -, -, h, -⟩ | ⟨n, -, -, ⟨Q, rfl⟩, -⟩
  · exact h
  · exact Subgroup.map_subtype_le _

theorem Sl2Cl.norm {p : ℕ} {z : B} {X K : Subgroup B} (h : Sl2Cl p z X K) :
    K ⊓ normalizer (X : Set B) ≤ X ⊔ K ⊓ centralizer ({z} : Set B) := by
  rcases h with ⟨-, -, -, -, h⟩ | ⟨n, -, -, -, h⟩
  · exact h
  · exact h

theorem Sl2Cl.model {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {z : B} {X K : Subgroup B}
    (h : Sl2Cl p z X K) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Odd (Nat.card F) ∧ 3 < Nat.card F ∧
      Nonempty (↥K ≃* IVK.SL2 F) ∧ (Nat.card F = 9 → p = 3) := by
  rcases h with ⟨hK, -, -, -, -⟩ | ⟨n, hn3, hK, -, -⟩
  · obtain ⟨F, x, hF, hP, ⟨e⟩⟩ := hK
    refine ⟨F, x, hF, ?_, ?_, ⟨e⟩, ?_⟩
    · rw [hP]; decide
    · rw [hP]; decide
    · intro h9; rw [hP] at h9; omega
  · obtain ⟨F, x, hF, hP, ⟨e⟩⟩ := hK
    have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
    refine ⟨F, x, hF, ?_, ?_, ⟨e⟩, ?_⟩
    · rw [hP]; exact hpodd.pow
    · rw [hP]; exact hn3
    · intro h9
      rw [hP] at h9
      have hn0 : n ≠ 0 := by rintro rfl; simp at h9
      have hdvd : p ∣ 3 ^ 2 := by
        rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← h9]
        exact dvd_pow_self p hn0
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow hdvd)

theorem center_ne_bot_of_sl2 {Q : Type} [Group Q] {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (e : Q ≃* IVK.SL2 F) : center Q ≠ ⊥ := by
  intro hbot
  let e' : Q ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm
  have hc : (center Q).map e'.toMonoidHom = center (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Subgroup.map_center_eq e'
  have hF : ringChar F ≠ 2 := by
    have := Fintype.ofFinite F
    intro h2
    have h0 : Fintype.card F % 2 = 0 := FiniteField.even_card_iff_char_two.mp h2
    rw [← Nat.card_eq_fintype_card] at h0
    have h1 := Nat.odd_iff.mp hodd
    omega
  have h2 := CFSG.GH74.GLS.Stage2.Local.card_center_SL2_eq_two' (F := F) hF
  rw [← hc, hbot, Subgroup.map_bot] at h2
  simp at h2

end Sl2Cl

section SubSl2

variable {G : Type} [Group G] {z : G} {k : Kind}
variable {A : Type} [Group A] [Finite A] {a : A} {p : ℕ} {X : Subgroup A}

theorem pPrimeCoreOf_le_N {J : Subgroup A} (h : SubHyp a p X J) {w : A} (hw : w ∈ pPrimeCoreOf 2 J) :
    ∃ hwY : w ∈ secY a X J, (⟨w, hwY⟩ : ↥(secY a X J)) ∈ pPrimeCore 2 ↥(secY a X J) := by
  have hJY : J ≤ secY a X J := J_le_secY a X J
  have hMJ : pPrimeCoreOf 2 J ≤ J := Subgroup.map_subtype_le _
  have hMY : pPrimeCoreOf 2 J ≤ secY a X J := hMJ.trans hJY
  have hnormY : secY a X J ≤ normalizer (J : Set A) :=
    sup_le (sup_le le_normalizer h.XJ) (zpowers_le.mpr h.zJ)
  have hYM : secY a X J ≤ normalizer ((pPrimeCoreOf 2 J : Subgroup A) : Set A) :=
    hnormY.trans (subsec_normalizer_le_normalizer_pPrimeCoreOf J)
  have hn : ((pPrimeCoreOf 2 J).subgroupOf (secY a X J)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMY).mpr hYM
  have hcardM : Nat.card ↥(pPrimeCoreOf 2 J) = Nat.card ↥(pPrimeCore 2 ↥J) :=
    (Nat.card_congr ((pPrimeCore 2 ↥J).equivMapOfInjective J.subtype J.subtype_injective).toEquiv).symm
  have hodd : Odd (Nat.card ↥((pPrimeCoreOf 2 J).subgroupOf (secY a X J))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMY).toEquiv, hcardM]
    exact SubAbs.pPrimeCore_odd
  have hle := SubAbs.le_pPrimeCore_of_odd _ hodd
  exact ⟨hMY hw, hle hw⟩

theorem SubData.X_le_sup_of_le {c : E4Ctx G z A a p X} {J : Subgroup A} (d : SubData c J)
    (h : secX a X J ≤ secJ a X J) : X ≤ J ⊔ centralizer (J : Set A) := by
  intro x hx
  obtain ⟨j, hj, he⟩ := mem_secJ_iff.mp (h (secMk_mem_secX hx))
  have hmem := (secMk_eq_iff (X_le_secY a X J hx) (J_le_secY a X J hj)).mp he
  have hcomm : ∀ j' ∈ J, ((x : A)⁻¹ * j) * j' = j' * ((x : A)⁻¹ * j) := fun j' hj' =>
    N_comm_J d.hyp hmem hj'
  have hc : (x : A)⁻¹ * j ∈ centralizer (J : Set A) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j' hj'
    exact (hcomm j' hj').symm
  have hx' : x = j * ((x : A)⁻¹ * j)⁻¹ := by group
  rw [hx']
  exact Subgroup.mul_mem_sup hj (inv_mem hc)

theorem SubData.X_le_sup {c : E4Ctx G z A a p X} {J : Subgroup A} (d : SubData c J)
    (h : Sl2Cl p (secZ a X J) (secX a X J) (secJ a X J)) : X ≤ J ⊔ centralizer (J : Set A) :=
  d.X_le_sup_of_le h.X_le

theorem SubData.exists_nt {c : E4Ctx G z A a p X} {J : Subgroup A} (d : SubData c J)
    (h : Sl2Cl p (secZ a X J) (secX a X J) (secJ a X J)) :
    ∃ j ∈ J, a * j * a⁻¹ * j⁻¹ ∉ pPrimeCoreOf 2 J := by
  by_contra hcon
  push Not at hcon
  have hA4 := secB_Sig4A d.hyp
  have hz1 : ∀ b ∈ secJ a X J, secZ a X J * b = b * secZ a X J := by
    intro b hb
    obtain ⟨j, hj, rfl⟩ := mem_secJ_iff.mp hb
    obtain ⟨hwY, hwN⟩ := pPrimeCoreOf_le_N d.hyp (hcon j hj)
    have hz2 : a * a = 1 := c.z2
    have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right hz2
    have h1 := (secMk_eq_one_iff hwY).mpr hwN
    have h2 : secMk a X J (a * j * a⁻¹ * j⁻¹) hwY =
        secZ a X J * secMk a X J j (J_le_secY a X J hj) * (secZ a X J)⁻¹ *
          (secMk a X J j (J_le_secY a X J hj))⁻¹ := rfl
    rw [h1] at h2
    have h3 : secZ a X J * secMk a X J j (J_le_secY a X J hj) * (secZ a X J)⁻¹ =
        secMk a X J j (J_le_secY a X J hj) := mul_inv_eq_one.mp h2.symm
    calc secZ a X J * secMk a X J j (J_le_secY a X J hj)
        = secZ a X J * secMk a X J j (J_le_secY a X J hj) * (secZ a X J)⁻¹ * secZ a X J := by group
      _ = secMk a X J j (J_le_secY a X J hj) * secZ a X J := by rw [h3]
  have hbot : ⁅secX a X J, zpowers (secZ a X J)⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hc1 : secZ a X J * x = x * secZ a X J := hz1 x (h.X_le hx)
    have hcm : Commute (secZ a X J) x := hc1
    exact (hcm.zpow_left m).eq
  have := hA4.comm
  rw [hbot] at this
  exact hA4.ne_bot this.symm

theorem SubData.exists_y {c : E4Ctx G z A a p X} {J : Subgroup A} (d : SubData c J)
    (h : Sl2Cl p (secZ a X J) (secX a X J) (secJ a X J)) :
    ∃ y ∈ J, y * y ≠ 1 ∧ (y * y) * (y * y) = 1 ∧ (∀ j ∈ J, (y * y) * j = j * (y * y)) ∧
      a * y * a⁻¹ = y⁻¹ := by
  obtain ⟨F, hF, hFin, hodd, h3, ⟨eK⟩, -⟩ := Sl2Cl.model c.A4.prime c.A4.odd h
  obtain ⟨eS⟩ := secJ_equiv d.hyp
  exact exists_inverted_lift d.comp d.zJ c.z2 F hodd h3 (eS.symm.trans eK) (d.exists_nt h)

end SubSl2

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
