module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResHyp51
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResE3S3Lem77
public import CFSG.ClassicalInvolution.Q3.TL4OddMu4F

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Asc77.T8 (XMem)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4

section Cit3


theorem hyp51At_of_twinPair_four_le {r n : ℕ} (hr : 4 ≤ r) (hNo : NoQ16E4) (h4 : Thm4RBelow r n)
    (hB : TightBelowR r n) {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    (hZ : Subgroup.center G = ⊥) (hGn : Nat.card G ≤ n) (hΩ : TypeRFam r Ω) {B : Subgroup G}
    (hBe : IsElemAbelian 2 B) {a b c : G} (haB : a ∈ B) (hcB : c ∈ B) (hc1 : c ≠ 1) (ha1 : a ≠ 1)
    (hac : a ≠ c) (habc : a * b = c) {Ma Mb : Subgroup G} (hMa : XMem Ω c Ma)
    (hMb : XMem Ω c Mb) (ha : IsUniqueInvolution Ma a) (hb : IsUniqueInvolution Mb b)
    {P : Subgroup G} (hP : IsSylow2In P Mb) (hPc : P ≤ Subgroup.centralizer ({c} : Set G))
    (hPN : P ≤ Subgroup.normalizer (Ma : Set G)) : Hyp51At B c := by
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hBe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hsq : ∀ x ∈ B, x * x = 1 := fun x hx => (sq x).symm.trans (hBe.2 x hx)
  have hac' : a * c = c * a := hBc a haB c hcB
  have haC : a ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hac'
  have hbe : b = a * c := by
    calc b = a * (a * b) := by rw [← mul_assoc, hsq a haB, one_mul]
      _ = a * c := by rw [habc]
  have hcC : c ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hbC : b ∈ Subgroup.centralizer ({c} : Set G) := by
    rw [hbe]
    exact Subgroup.mul_mem _ haC hcC
  have hΦ : TypeRFam r (vtxFam Ω c) := hΩ.vtxFam
  have hO := oddQuot_oddCore_eq_bot c
  have hQn : Nat.card (OddQuot c) < n := lt_of_lt_of_le (natCard_oddQuot_lt hZ hc1) hGn
  have hKa := modOdd_coreAt_mem_vtxFam hMa
  have haz := isUniqueInvolution_modOdd_coreAt hΩ hMa ha haC
  have hbz := isUniqueInvolution_modOdd_coreAt hΩ hMb hb hbC
  have haB' := oddQuotMk_mem_modOdd haB haC
  have haZ := Lemma52Proof.oddQuotMk_not_mem_zpowers hBe hcB hc1 haB ha1 hac haC
  have hba : (⟨b, hbC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) * ⟨a, haC⟩⁻¹ = ⟨c, hcC⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hbe]
    calc a * c * a⁻¹ = c * a * a⁻¹ := by rw [hac']
      _ = c := by group
  have hcZ : oddQuotMk c ⟨c, hcC⟩ ∈ Subgroup.center (OddQuot c) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective _ y
    change oddQuotMk c k * oddQuotMk c _ = oddQuotMk c _ * oddQuotMk c k
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp k.2)
  have hne : modOdd c (coreAt c Ma) ≠ modOdd c (coreAt c Mb) := by
    intro e
    have he := haz.eq (e ▸ hbz)
    have h1 : oddQuotMk c ⟨c, hcC⟩ = 1 := by
      rw [← hba, map_mul, map_inv, ← he, mul_inv_cancel]
    exact hc1 (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one (Subtype.ext (hsq c hcB)) h1))
  have hnbr := modOdd_coreAt_mem_omegaNbr hMb hP hPc hPN hne
  have hnone : ∀ L : Subgroup (OddQuot c), IsComponent L → ¬ MovedByAll B c L := by
    intro L hL hm
    obtain ⟨y₁, hy₁, hne₁⟩ := hm _ haB' haZ
    rcases commute_of_adj_four_le hr hNo h4 hB hΦ hO hQn hKa hnbr haz hbz hL with h1 | h1
    · exact hne₁ (h1 y₁ hy₁)
    · apply hne₁
      have hmem : oddQuotMk c ⟨c, hcC⟩ = oddQuotMk c ⟨b, hbC⟩ * (oddQuotMk c ⟨a, haC⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, hba]
      have hy := h1 y₁ hy₁
      have hcy : oddQuotMk c ⟨c, hcC⟩ * y₁ = y₁ * oddQuotMk c ⟨c, hcC⟩ :=
        (Subgroup.mem_center_iff.mp hcZ y₁).symm
      have hb : oddQuotMk c ⟨b, hbC⟩ = oddQuotMk c ⟨c, hcC⟩ * oddQuotMk c ⟨a, haC⟩ := by
        rw [hmem]
        group
      rw [hb] at hy
      calc oddQuotMk c ⟨a, haC⟩ * y₁
          = (oddQuotMk c ⟨c, hcC⟩)⁻¹ * (oddQuotMk c ⟨c, hcC⟩ * oddQuotMk c ⟨a, haC⟩ * y₁) := by
            group
        _ = (oddQuotMk c ⟨c, hcC⟩)⁻¹ * (y₁ * (oddQuotMk c ⟨c, hcC⟩ * oddQuotMk c ⟨a, haC⟩)) := by
            rw [hy]
        _ = (oddQuotMk c ⟨c, hcC⟩)⁻¹ * (y₁ * oddQuotMk c ⟨c, hcC⟩) * oddQuotMk c ⟨a, haC⟩ := by
            group
        _ = (oddQuotMk c ⟨c, hcC⟩)⁻¹ * (oddQuotMk c ⟨c, hcC⟩ * y₁) * oddQuotMk c ⟨a, haC⟩ := by
            rw [hcy]
        _ = y₁ * oddQuotMk c ⟨a, haC⟩ := by group
  exact ⟨fun L₁ L₂ h₁ h₂ m₁ m₂ => (hnone L₁ h₁ m₁).elim, fun L hL m => (hnone L hL m).elim⟩

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem hyp51At_mul_of_edge_four_le (hr : 4 ≤ r) (hNo : NoQ16E4) (h4 : Thm4RBelow r n)
    (hL : TightLargeHypR r n Y R S t) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) {u : Y}
    (hu : IsUniqueInvolution J u) {B : Subgroup Y} (hB : IsElemAbelian 2 B) (htB : t ∈ B)
    (huB : u ∈ B) : Hyp51At B (t * u) := by
  have h := TightLargeHypR.typeRFam hL
  have ht := hL.datum.isUniqueInvolution_core
  have hK₀ : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have htu : t ≠ u := fun e =>
    hJ.2.1 (eq_core_of_isUniqueInvolution hL hJ.1 (e ▸ hu))
  have hc1 : t * u ≠ 1 := by
    intro e
    apply htu
    calc t = t * u * u := by rw [mul_assoc, hu.sq, mul_one]
      _ = u := by rw [e, one_mul]
  have hac : t ≠ t * u := by
    intro e
    apply hu.ne_one
    have e' : t * u = t * 1 := by rw [mul_one]; exact e.symm
    exact mul_left_cancel e'
  have ctu : t * u = u * t := Q3CL.T8.mul_comm_of_mem_omegaNbr h.hyp ht hJ hu
  obtain ⟨hJΩ, -, T, hT, hTJ, hTN⟩ := id hJ
  have hTs : IsSylow2In T J := Q3CL.T3.isSylow2In_of_mem_RSet_of_le h.hyp hJΩ hT hTJ
  have hTc : T ≤ Subgroup.centralizer ({t * u} : Set Y) := by
    intro x hx
    have hxt : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp
      (S1916.normalizer_le_centralizer_of_isUniqueInvolution ht (hTN hx))
    have hxu : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.mp
      (S1916.normalizer_le_centralizer_of_isUniqueInvolution hu
        (Subgroup.le_normalizer (hTJ hx)))
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * (t * u) = x * t * u := by group
      _ = t * x * u := by rw [hxt]
      _ = t * (x * u) := by group
      _ = t * (u * x) := by rw [hxu]
      _ = t * u * x := by group
  exact hyp51At_of_twinPair_four_le hr hNo h4 hL.tbelow hL.center hL.card.le h hB
    htB (Subgroup.mul_mem _ htB huB) hc1 ht.ne_one hac rfl
    (xMem_mul_of_mem_omegaNbr' h hK₀ hJ ht hu) (xMem_mul_of_mem_omegaNbr h hJ ht hu) ht hu hTs hTc hTN

theorem hyp51At_of_commonNbr_four_le (hr : 4 ≤ r) (hNo : NoQ16E4) (h4 : Thm4RBelow r n)
    (hL : TightLargeHypR r n Y R S t) {J K' : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hK'₀ : K' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hK'J : K' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J) {u : Y}
    (hu : IsUniqueInvolution J u) (hz' : IsUniqueInvolution K' (t * u)) {B : Subgroup Y}
    (hB : IsElemAbelian 2 B) (htB : t ∈ B) (huB : u ∈ B) :
    Hyp51At B t ∧ Hyp51At B u ∧ Hyp51At B (t * u) := by
  have h := TightLargeHypR.typeRFam hL
  have ht := hL.datum.isUniqueInvolution_core
  have hK₀ : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have htu : t ≠ u := fun e => hJ.2.1 (eq_core_of_isUniqueInvolution hL hJ.1 (e ▸ hu))
  refine ⟨?_, ?_, hyp51At_mul_of_edge_four_le hr hNo h4 hL hJ hu hB htB huB⟩
  ·
    obtain ⟨hK'Ω, -, T, hT, hTK', hTN⟩ := id hK'J
    have hTs : IsSylow2In T K' := Q3CL.T3.isSylow2In_of_mem_RSet_of_le h.hyp hK'Ω hT hTK'
    have hTc : T ≤ Subgroup.centralizer ({t} : Set Y) := by
      intro x hx
      have hx1 : x * (t * u) = (t * u) * x := Subgroup.mem_centralizer_singleton_iff.mp
        (S1916.normalizer_le_centralizer_of_isUniqueInvolution hz'
          (Subgroup.le_normalizer (hTK' hx)))
      have hx2 : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.mp
        (S1916.normalizer_le_centralizer_of_isUniqueInvolution hu (hTN hx))
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc x * t = x * t * (u * u) := by rw [hu.sq, mul_one]
        _ = x * (t * u) * u := by group
        _ = (t * u) * x * u := by rw [hx1]
        _ = (t * u) * (x * u) := by group
        _ = (t * u) * (u * x) := by rw [hx2]
        _ = t * x := by rw [← mul_assoc, mul_assoc t u u, hu.sq, mul_one]
    refine hyp51At_of_twinPair_four_le hr hNo h4 hL.tbelow hL.center hL.card.le h hB huB htB
      ht.ne_one hu.ne_one htu.symm ?_ (xMem_of_mem_omegaNbr_core hL hJ)
      (xMem_of_mem_omegaNbr_core hL hK'₀) hu hz' hTs hTc hTN
    calc u * (t * u) = u * (u * t) := by
          rw [Q3CL.T8.mul_comm_of_mem_omegaNbr h.hyp ht hJ hu]
      _ = t := by rw [← mul_assoc, hu.sq, one_mul]
  ·
    obtain ⟨hK'Ω, -, T, hT, hTK', hTN⟩ := id hK'₀
    have hTs : IsSylow2In T K' := Q3CL.T3.isSylow2In_of_mem_RSet_of_le h.hyp hK'Ω hT hTK'
    have hTc : T ≤ Subgroup.centralizer ({u} : Set Y) := by
      intro x hx
      have hx1 : x * (t * u) = (t * u) * x := Subgroup.mem_centralizer_singleton_iff.mp
        (S1916.normalizer_le_centralizer_of_isUniqueInvolution hz'
          (Subgroup.le_normalizer (hTK' hx)))
      have hx2 : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp
        (S1916.normalizer_le_centralizer_of_isUniqueInvolution ht (hTN hx))
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc x * u = x * t * (t * u) := by
            rw [mul_assoc x t, ← mul_assoc t t u, ht.sq, one_mul]
        _ = t * x * (t * u) := by rw [hx2]
        _ = t * (x * (t * u)) := by group
        _ = t * ((t * u) * x) := by rw [hx1]
        _ = u * x := by rw [← mul_assoc, ← mul_assoc, ht.sq, one_mul]
    refine hyp51At_of_twinPair_four_le hr hNo h4 hL.tbelow hL.center hL.card.le h hB htB huB
      hu.ne_one ht.ne_one htu ?_ (xMem_of_mem_omegaNbr_nbr h hK₀ hJ ht hu)
      (xMem_of_mem_omegaNbr_gen h hK'J hu) ht hz' hTs hTc hTN
    rw [← mul_assoc, ht.sq, one_mul]

theorem hyp51At_of_noGNbr_four_le (hr : 4 ≤ r) (hNo : NoQ16E4) (h4 : Thm4RBelow r n)
    (hL : TightLargeHypR r n Y R S t) {J K' : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hbad : NoGNbr R t J)
    (hK'₀ : K' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hK'J : K' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J) {u : Y}
    (hu : IsUniqueInvolution J u) {B : Subgroup Y} (hB : IsElemAbelian 2 B) (htB : t ∈ B)
    (huB : u ∈ B) : Hyp51At B t ∧ Hyp51At B u ∧ Hyp51At B (t * u) := by
  obtain ⟨z', hz'⟩ := Sec6Gen.exists_uniqueInvolution hL.datum.hypOmegaGen hK'₀.1
  have e : z' = t * u := hbad K' hK'₀ hK'J u z' hu hz'
  rw [e] at hz'
  exact hyp51At_of_commonNbr_four_le hr hNo h4 hL hJ hK'₀ hK'J hu hz' hB htB huB

end Cit3

section Edge

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}


theorem secInO2_of_edge (hr : 4 ≤ r) (h4 : Thm4RBelow r n) (hNo : NoQ16E4)
    (hL : TightLargeHypR r n Y Rd Sd z) {J : Subgroup Y}
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)) {t : Y}
    (ht : IsUniqueInvolution J t) :
    SecInO2 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (z * t) z := by
  obtain ⟨S, R, T, W, hs⟩ := CFSG.ClassicalInvolution.Q3.TL4.TightLargeHypR.exists_std8 hL hJ ht
  exact secInO2_of_four_le hr h4 hL.tbelow hNo hs

end Edge

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
