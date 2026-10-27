module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1132Good
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I113Y

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1132

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld.ComponentBalance
  CFSG.LocalAnalysis.GLTheoremA.I113

variable {Q : Type} [Group Q] [Finite Q]

@[expose] def ehat (c y w : Q) : Subgroup Q :=
  t113Y12 c y ⊔ Subgroup.zpowers (c⁻¹ * w * c)

theorem Y12_le_ehat (c y w : Q) : t113Y12 c y ≤ ehat c y w := le_sup_left

theorem ehat_central {c y w z : Q} (h1 : z * (c⁻¹ * y * c) = (c⁻¹ * y * c) * z)
    (h2 : z * ((c ^ 2)⁻¹ * y * c ^ 2) = ((c ^ 2)⁻¹ * y * c ^ 2) * z)
    (h3 : z * (c⁻¹ * w * c) = (c⁻¹ * w * c) * z) : ∀ e ∈ ehat c y w, z * e = e * z := by
  intro e he
  have hle : ehat c y w ≤ Subgroup.centralizer ({z} : Set Q) := by
    refine sup_le (sup_le ?_ ?_) ?_ <;>
      refine Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 ?_)
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle he)).symm

private theorem inf_zpowers_eq_bot {P : Subgroup Q} {g : Q} (hg : orderOf g = 3) (hgP : g ∉ P) :
    P ⊓ Subgroup.zpowers g = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hzP, hzg⟩
  rw [Subgroup.mem_bot]
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hzg
  have h3 : g ^ 3 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have e := zpow_eq_zpow_emod' (x := g) k h3
  have hr : k % (3 : ℕ) = 0 ∨ k % (3 : ℕ) = 1 ∨ k % (3 : ℕ) = 2 := by omega
  rw [e] at hzP ⊢
  rcases hr with h | h | h
  · rw [h]; simp
  · rw [h] at hzP
    exact absurd (by simpa using hzP) hgP
  · rw [h] at hzP
    refine absurd ?_ hgP
    have h4 : g = (g ^ (2 : ℤ)) ^ (2 : ℤ) := by
      calc g = g ^ 3 * g := by rw [h3, one_mul]
        _ = (g ^ (2 : ℤ)) ^ (2 : ℤ) := by group
    rw [h4]
    exact P.zpow_mem hzP 2

section

variable {B M : Subgroup Q} {c : Q}

theorem Triple3.ehat_spec (Tr : Triple3 B M c) {y w : Q} (hy : y ∈ M) (ho : orderOf y = 3)
    (hnc : ∃ m ∈ M, y * m ≠ m * y) (hw : w ∈ M) (hw3 : w ^ 3 = 1) (hwy : y * w = w * y)
    (hwn : w ∉ Subgroup.zpowers y) :
    ehat c y w ≤ t113K B M ∧ IsElemAbelian 3 (ehat c y w) ∧ Nat.card ↥(ehat c y w) = 27 ∧
      ∀ e ∈ ehat c y w, ∀ m ∈ M, e * m = m * e := by
  obtain ⟨hYel, hYcard, hYK, -⟩ := Tr.Y12_spec hy ho hnc
  have hw1 : w ≠ 1 := fun h => hwn (by rw [h]; exact Subgroup.one_mem _)
  have how : orderOf w = 3 := orderOf_eq_prime hw3 hw1
  have how2 : orderOf (c⁻¹ * w * c) = 3 := by rw [t113_orderOf_conj, how]
  obtain ⟨hWel, hWcard⟩ := t113_zpowers_elem how2
  have hw2M : c⁻¹ * w * c ∈ GLBConj c M := Tr.conj1_mem hw
  have hy3M : (c ^ 2)⁻¹ * y * c ^ 2 ∈ GLBConj (c ^ 2) M := Tr.conj2_mem hy
  have h1 : Subgroup.zpowers (c⁻¹ * y * c) ≤ GLBConj c M := Subgroup.zpowers_le.2 (Tr.conj1_mem hy)
  have h2 : Subgroup.zpowers ((c ^ 2)⁻¹ * y * c ^ 2) ≤ GLBConj (c ^ 2) M :=
    Subgroup.zpowers_le.2 hy3M
  have hYw : t113Y12 c y ≤ Subgroup.centralizer ({c⁻¹ * w * c} : Set Q) := by
    refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc (c⁻¹ * y * c) * (c⁻¹ * w * c) = c⁻¹ * (y * w) * c := by group
        _ = c⁻¹ * (w * y) * c := by rw [hwy]
        _ = (c⁻¹ * w * c) * (c⁻¹ * y * c) := by group
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Tr.comm12 _ hw2M _ hy3M).symm
  have hcomm : ∀ p ∈ t113Y12 c y, ∀ r ∈ Subgroup.zpowers (c⁻¹ * w * c), p * r = r * p := by
    intro p hp r hr
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
    have hpc : Commute p (c⁻¹ * w * c) := Subgroup.mem_centralizer_singleton_iff.1 (hYw hp)
    exact (hpc.zpow_right k).eq
  have hw2nY : c⁻¹ * w * c ∉ t113Y12 c y := by
    intro hmem
    have o2 : orderOf ((c ^ 2)⁻¹ * y * c ^ 2) = 3 := by rw [t113_orderOf_conj, ho]
    obtain ⟨v, hv, u, hu, hvu⟩ := t113_mem_sup (P := Subgroup.zpowers (c⁻¹ * y * c))
      (R := Subgroup.zpowers ((c ^ 2)⁻¹ * y * c ^ 2))
      (fun p hp r hr => Tr.comm12 p (h1 hp) r (h2 hr)) hmem
    have huc : u ∈ GLBConj c M := by
      have e : u = v⁻¹ * (c⁻¹ * w * c) := by rw [← hvu]; group
      rw [e]
      exact (GLBConj c M).mul_mem ((GLBConj c M).inv_mem (h1 hv)) hw2M
    have hu1 : u = 1 :=
      zpowers_eq_one_of_centralizes o2 (noncentral_conj (c ^ 2) hnc) u hu
        (fun m hm => Tr.comm12 u huc m hm)
    rw [hu1, mul_one] at hvu
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hv
    apply hwn
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    have e1 : y = c * (c⁻¹ * y * c) * c⁻¹ := by group
    rw [e1, conj_zpow, hk, hvu]
    group
  have hi : t113Y12 c y ⊓ Subgroup.zpowers (c⁻¹ * w * c) = ⊥ := inf_zpowers_eq_bot how2 hw2nY
  obtain ⟨hel, hcard⟩ := t113_sup_elemAbelian hYel hWel hcomm hi
  have hE : ehat c y w = t113Y12 c y ⊔ Subgroup.zpowers (c⁻¹ * w * c) := rfl
  refine ⟨?_, hel, ?_, ?_⟩
  · rw [hE]
    exact sup_le hYK (Subgroup.zpowers_le.2 (Tr.conj_le_K Tr.mem hw2M))
  · rw [hYcard, hWcard] at hcard
    rw [hE]
    omega
  · intro e he m hm
    have hle : ehat c y w ≤ Subgroup.centralizer ({m} : Set Q) := by
      refine sup_le (fun u hu => ?_) (Subgroup.zpowers_le.2 ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact Tr.Y12_comm_M hy u hu m hm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Tr.comm01 m hm _ hw2M).symm
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle he)

theorem Triple3.B0_sup_zpowers (Tr : Triple3 B M c) {a : Q} (ha : a ∈ t113A B M)
    (ha1 : a ∉ t113B0 B M) :
    IsElemAbelian 3 (t113B0 B M ⊔ Subgroup.zpowers a) ∧
      Nat.card ↥(t113B0 B M ⊔ Subgroup.zpowers a) = 3 * Nat.card ↥(t113B0 B M) ∧
      t113B0 B M ⊔ Subgroup.zpowers a ≤ B ∧
      t113B0 B M ⊔ Subgroup.zpowers a ≤ Subgroup.normalizer (M : Set Q) := by
  have haN : a ∈ Subgroup.normalizer (M : Set Q) := ha.1
  have haB : a ∈ B := ha.2
  have ha1' : a ≠ 1 := fun h => ha1 (by rw [h]; exact Subgroup.one_mem _)
  have hoa : orderOf a = 3 := orderOf_eq_prime (Tr.elem.2 a haB) ha1'
  obtain ⟨hAel, hAcard⟩ := t113_zpowers_elem hoa
  have hcomm : ∀ p ∈ t113B0 B M, ∀ r ∈ Subgroup.zpowers a, p * r = r * p :=
    fun p hp r hr => Tr.comm_B hp.1 (Subgroup.zpowers_le.2 haB hr)
  obtain ⟨hel, hcard⟩ := t113_sup_elemAbelian Tr.B0_elem hAel hcomm (inf_zpowers_eq_bot hoa ha1)
  refine ⟨hel, by rw [hcard, hAcard, mul_comm], sup_le inf_le_left (Subgroup.zpowers_le.2 haB),
    sup_le (fun b hb => (Tr.B0_mem_A hb).1) (Subgroup.zpowers_le.2 haN)⟩

theorem Triple3.a_comm_ehat (Tr : Triple3 B M c) {a y w : Q} (ha : a ∈ B)
    (hay : ∀ l ∈ M, a * l * a⁻¹ = y * l * y⁻¹) (hy : y ∈ M) (hw : w ∈ M)
    (hwy : y * w = w * y) : ∀ e ∈ ehat c y w, a * e = e * a := by
  have hay' : a * y = y * a := by
    calc a * y = a * y * a⁻¹ * a := by group
      _ = y * y * y⁻¹ * a := by rw [hay y hy]
      _ = y * a := by group
  have haw : a * w = w * a := by
    calc a * w = a * w * a⁻¹ * a := by group
      _ = y * w * y⁻¹ * a := by rw [hay w hw]
      _ = w * a := by rw [hwy]; group
  exact ehat_central (Tr.commute_conj Tr.mem ha hay')
    (Tr.commute_conj (B.pow_mem Tr.mem 2) ha hay') (Tr.commute_conj Tr.mem ha haw)

theorem Triple3.goodData_of_ehat (Tr : Triple3 B M c) {y w : Q} (hy : y ∈ M) (ho : orderOf y = 3)
    (hnc : ∃ m ∈ M, y * m ≠ m * y) (hw : w ∈ M) (hw3 : w ^ 3 = 1) (hwy : y * w = w * y)
    (hwn : w ∉ Subgroup.zpowers y) {D : Subgroup Q} (hDB : D ≤ B) (hB0D : t113B0 B M ≤ D)
    (hDN : D ≤ Subgroup.normalizer (M : Set Q))
    (hDE : ∀ z ∈ D, ∀ e ∈ ehat c y w, z * e = e * z) (hcard : Nat.card B ≤ 9 * Nat.card D) :
    GoodData B M D (ehat c y w) ⊥ M := by
  obtain ⟨hEK, hEel, hEcard, hEM⟩ := Triple3.ehat_spec Tr hy ho hnc hw hw3 hwy hwn
  obtain ⟨hYel, hYcard, -, hYB0⟩ := Tr.Y12_spec hy ho hnc
  have hDYi : D ⊓ t113Y12 c y = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hzD, hzY⟩
    refine Subgroup.mem_bot.2 (hYB0 z hzY ⟨hDB hzD, Subgroup.mem_centralizer_iff.2 ?_⟩)
    exact Tr.centralizes_K (hDB hzD) (fun l hl => (Tr.Y12_comm_M hy z hzY l hl).symm)
  obtain ⟨-, hDYcard⟩ := t113_sup_elemAbelian (t113_elemAbelian_of_le Tr.elem hDB) hYel
    (fun p hp r hr => hDE p hp r (Y12_le_ehat c y w hr)) hDYi
  refine
    { D_le := hDB
      B0_le := hB0D
      D_norm := hDN
      E1_le := hEK
      E1_el := hEel
      E1_cent := hEM
      E1_dvd := by simp [hEcard]
      D_E1 := hDE
      M4_comp := Tr.comp
      E2_le := bot_le
      E2_el := t113_bot_elem.1
      E2_cent := fun e he m _ => by rw [Subgroup.mem_bot.1 he, one_mul, mul_one]
      DE1_norm := sup_le hDN fun e he => t113_mem_normalizer_of_commute fun j hj => hEM e he j hj
      DE1_E2 := fun z _ e he => by rw [Subgroup.mem_bot.1 he, one_mul, mul_one]
      card_le := ?_ }
  rw [sup_bot_eq]
  calc Nat.card B ≤ 9 * Nat.card D := hcard
    _ = Nat.card ↥(D ⊔ t113Y12 c y) := by rw [hDYcard, hYcard]; ring
    _ ≤ Nat.card ↥(D ⊔ ehat c y w) :=
        Subgroup.card_le_of_le (sup_le_sup_left (Y12_le_ehat c y w) D)

theorem Triple3.goodData_of_M4 (Tr : Triple3 B M c) {y w : Q} (hy : y ∈ M) (ho : orderOf y = 3)
    (hnc : ∃ m ∈ M, y * m ≠ m * y) (hw : w ∈ M) (hw3 : w ^ 3 = 1) (hwy : y * w = w * y)
    (hwn : w ∉ Subgroup.zpowers y) {M4 : Subgroup Q} (hM4 : IsComponentOf M4 ⊤)
    (hcomm : ∀ b ∈ B, ∀ u ∈ GLBConj b M, ∀ v ∈ M4, u * v = v * u)
    (hB0 : ∀ z ∈ t113B0 B M, ∀ v ∈ M4, z * v = v * z) {y4 : Q} (hy4 : y4 ∈ M4)
    (ho4 : orderOf y4 = 3) (hnc4 : ∃ m ∈ M4, y4 * m ≠ m * y4)
    (hcard : Nat.card B ≤ 27 * Nat.card ↥(t113B0 B M)) :
    GoodData B M (t113B0 B M) (ehat c y w) (Subgroup.zpowers y4) M4 := by
  obtain ⟨hEK, hEel, hEcard, hEM⟩ := Triple3.ehat_spec Tr hy ho hnc hw hw3 hwy hwn
  obtain ⟨hYel, hYcard, hYK, hYB0⟩ := Tr.Y12_spec hy ho hnc
  have hSM4 : ∀ z ∈ t113B0 B M ⊔ ehat c y w, ∀ v ∈ M4, z * v = v * z := by
    intro z hz v hv
    have hKv : t113K B M ≤ Subgroup.centralizer ({v} : Set Q) :=
      iSup₂_le fun g hg u hu => Subgroup.mem_centralizer_singleton_iff.2 (hcomm g hg u hu v hv)
    have hle : t113B0 B M ⊔ ehat c y w ≤ Subgroup.centralizer ({v} : Set Q) :=
      sup_le (fun z hz => Subgroup.mem_centralizer_singleton_iff.2 (hB0 z hz v hv)) (hEK.trans hKv)
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hz)
  have hSE2 : ∀ z ∈ t113B0 B M ⊔ ehat c y w, ∀ e ∈ Subgroup.zpowers y4, z * e = e * z := by
    intro z hz e he
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
    have hz4 : Commute z y4 := hSM4 z hz y4 hy4
    exact (hz4.zpow_right k).eq
  have hB0Yi : t113B0 B M ⊓ t113Y12 c y = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hzB, hzY⟩
    exact Subgroup.mem_bot.2 (hYB0 z hzY hzB)
  obtain ⟨hTel, hTcard⟩ := t113_sup_elemAbelian Tr.B0_elem hYel
    (fun p hp r hr => (Tr.B0_comm_K hp r (hYK hr)).symm) hB0Yi
  have hTS : t113B0 B M ⊔ t113Y12 c y ≤ t113B0 B M ⊔ ehat c y w :=
    sup_le_sup_left (Y12_le_ehat c y w) _
  have hTi : (t113B0 B M ⊔ t113Y12 c y) ⊓ Subgroup.zpowers y4 = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hzT, hz4⟩
    exact Subgroup.mem_bot.2 (zpowers_eq_one_of_centralizes ho4 hnc4 z hz4
      (fun v hv => hSM4 z (hTS hzT) v hv))
  obtain ⟨-, hT4card⟩ := t113_sup_elemAbelian hTel (t113_zpowers_elem ho4).1
    (fun p hp r hr => hSE2 p (hTS hp) r hr) hTi
  refine
    { D_le := inf_le_left
      B0_le := le_rfl
      D_norm := fun b hb => (Tr.B0_mem_A hb).1
      E1_le := hEK
      E1_el := hEel
      E1_cent := hEM
      E1_dvd := by simp [hEcard]
      D_E1 := fun z hz e he => (Tr.B0_comm_K hz e (hEK he)).symm
      M4_comp := hM4
      E2_le := Subgroup.zpowers_le.2 hy4
      E2_el := (t113_zpowers_elem ho4).1
      E2_cent := ?_
      DE1_norm := fun z hz => t113_mem_normalizer_of_commute fun j hj => hSM4 z hz j hj
      DE1_E2 := hSE2
      card_le := ?_ }
  · intro e he m hm
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
    have h4m : Commute y4 m :=
      (hcomm 1 B.one_mem m (by rw [gLBConj_one]; exact hm) y4 hy4).symm
    exact (h4m.zpow_left k).eq
  · calc Nat.card B ≤ 27 * Nat.card ↥(t113B0 B M) := hcard
      _ = Nat.card ↥(t113B0 B M ⊔ t113Y12 c y ⊔ Subgroup.zpowers y4) := by
          rw [hT4card, hTcard, hYcard, (t113_zpowers_elem ho4).2]; ring
      _ ≤ Nat.card ↥(t113B0 B M ⊔ ehat c y w ⊔ Subgroup.zpowers y4) :=
          Subgroup.card_le_of_le (sup_le_sup_right hTS _)

end

end CFSG.LocalAnalysis.GLTheoremA.I1132
