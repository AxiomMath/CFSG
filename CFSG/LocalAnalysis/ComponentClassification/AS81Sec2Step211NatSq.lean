module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step211Str
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step211NatTot

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard Hexa
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def sqE {E A : Subgroup G} (rep : Fin 64 → G) (hsq : ∀ v, rep v * rep v ∈ E ⊓ A)
    (v : Fin 64) : ↥(E ⊓ A) :=
  ⟨rep v * rep v, hsq v⟩

@[expose] def cmE {E A : Subgroup G} (rep : Fin 64 → G) (hcm : ∀ v w, ⁅rep w, rep v⁆ ∈ E ⊓ A)
    (v w : Fin 64) : ↥(E ⊓ A) :=
  ⟨⁅rep w, rep v⁆, hcm v w⟩

omit [Finite G] in
theorem mul_mul_eq_of_commute {x y : G} (hcx : ⁅y, x⁆ * x = x * ⁅y, x⁆) :
    x * y * (x * y) = ⁅y, x⁆ * (x * x) * (y * y) := by
  have hyx : y * x = ⁅y, x⁆ * x * y := by rw [commutatorElement_def]; group
  calc x * y * (x * y) = x * (y * x) * y := by group
    _ = x * (⁅y, x⁆ * x * y) * y := by rw [hyx]
    _ = (x * ⁅y, x⁆) * x * y * y := by group
    _ = (⁅y, x⁆ * x) * x * y * y := by rw [hcx]
    _ = ⁅y, x⁆ * (x * x) * (y * y) := by group

omit [Finite G] in
theorem mul_mul_mul_eq_of_central {x y d : G} (hdx : d * x = x * d) (hdy : d * y = y * d)
    (hdd : d * d = 1) : x * y * d * (x * y * d) = x * y * (x * y) := by
  calc x * y * d * (x * y * d) = x * y * (d * x) * y * d := by group
    _ = x * y * (x * d) * y * d := by rw [hdx]
    _ = x * y * x * (d * y) * d := by group
    _ = x * y * x * (y * d) * d := by rw [hdy]
    _ = x * y * (x * y) * (d * d) := by group
    _ = x * y * (x * y) := by rw [hdd, mul_one]

omit [Finite G] in
theorem commutator_mul_mul_left {x y d z : G} (hdz : d * z = z * d)
    (hcx : x * ⁅y, z⁆ = ⁅y, z⁆ * x) : ⁅x * y * d, z⁆ = ⁅y, z⁆ * ⁅x, z⁆ := by
  have h1 : d * z * d⁻¹ = z := by rw [hdz]; group
  calc ⁅x * y * d, z⁆ = x * y * (d * z * d⁻¹) * y⁻¹ * x⁻¹ * z⁻¹ := by
        rw [commutatorElement_def]; group
    _ = x * ⁅y, z⁆ * z * x⁻¹ * z⁻¹ := by rw [h1, commutatorElement_def]; group
    _ = ⁅y, z⁆ * x * z * x⁻¹ * z⁻¹ := by rw [hcx]
    _ = ⁅y, z⁆ * ⁅x, z⁆ := by rw [commutatorElement_def x z]; group

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem isMulCommutative_inf (hF : Frame G A A R g E F) : IsMulCommutative ↥(E ⊓ A) := by
  obtain ⟨hEe, -⟩ := isElemAbelian_and_card_of_mem_planes hF
    (⟨1, Or.inl (rightConjugate_one E).symm⟩ : E ∈ planes E F)
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  have h := congrArg (fun z : ↥E => (z : G)) (hEe.1.is_comm.comm ⟨a, a.2.1⟩ ⟨b, b.2.1⟩)
  exact h

variable (h11 : Step11)
  {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
  (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))
  {x : G} (hx : x ∈ sec2P F) (hxS : x ∉ sec2S A R E F)
  (h4 : 4 ^ 4 ≤ Nat.card (conjClosure (E ⊓ A) (sec2P F))) (e : ↥(sec2PlanesP E F) ≃ Fin 6)
  {rep : Fin 64 → G} {ψ : ↥(normalizer (sec2P E : Set G)) →* Equiv.Perm (Fin 64)}
  (hc : Sec2HexaCoord E A F rep e ψ)

include h11 hE16 hF hL hodd hx hxS h4 hc

theorem sq_rep_mem (v : Fin 64) : rep v * rep v ∈ E ⊓ A :=
  (sq_mem_and_commutator_mem_inf h11 hE16 hF hL hodd hx hxS h4 (hc.mem v) (hc.mem v)).1

theorem commutator_rep_mem (v w : Fin 64) : ⁅rep w, rep v⁆ ∈ E ⊓ A := by
  rw [commutatorElement_def]
  exact (sq_mem_and_commutator_mem_inf h11 hE16 hF hL hodd hx hxS h4 (hc.mem w) (hc.mem v)).2

variable [IsMulCommutative ↥(E ⊓ A)]

theorem isQuadMap_sqE :
    IsQuadMap (sqE rep (sq_rep_mem h11 hE16 hF hL hodd hx hxS h4 e hc))
      (cmE rep (commutator_rep_mem h11 hE16 hF hL hodd hx hxS h4 e hc)) := by
  have hPC := sec2P_le_centralizer_inf h11 hE16 hF hL hodd
  have hEAP : E ⊓ A ≤ sec2P E := inf_le_left.trans (le_sec2P_of_frame hF)
  obtain ⟨hEe, -⟩ := isElemAbelian_and_card_of_mem_planes hF
    (⟨1, Or.inl (rightConjugate_one E).symm⟩ : E ∈ planes E F)
  have hsq2 : ∀ d ∈ E ⊓ A, d * d = 1 := fun d hd => by rw [← sq]; exact hEe.2 d hd.1
  have hcen : ∀ d ∈ E ⊓ A, ∀ p ∈ sec2P E, d * p = p * d := fun d hd p hp =>
    mem_centralizer_iff.mp (hPC hp) d hd
  have hrep : ∀ v w : Fin 64, ∃ d ∈ E ⊓ A, rep (xorF v w) = rep v * rep w * d := fun v w => by
    refine ⟨(rep v * rep w)⁻¹ * rep (xorF v w), ?_, by group⟩
    have h1 := hc.add v w
    have h2 := inv_mem h1
    simpa [mul_assoc] using h2
  have hcm := commutator_rep_mem h11 hE16 hF hL hodd hx hxS h4 e hc
  refine ⟨fun a => Subtype.ext (hsq2 a a.2), fun v w => Subtype.ext ?_, fun u v w => Subtype.ext ?_,
    fun v w => Subtype.ext ?_⟩
  ·
    obtain ⟨d, hd, hdeq⟩ := hrep v w
    show rep (xorF v w) * rep (xorF v w) = rep v * rep v * (rep w * rep w) * ⁅rep w, rep v⁆
    have hcv := hcen _ (hcm v w) _ (hc.mem v)
    have hcw := hcen _ (hcm v w) _ (hc.mem w)
    have hcvw : ⁅rep w, rep v⁆ * (rep v * rep v) = rep v * rep v * ⁅rep w, rep v⁆ :=
      hcen _ (hcm v w) _ (mul_mem (hc.mem v) (hc.mem v))
    rw [hdeq, mul_mul_mul_eq_of_central (hcen d hd _ (hc.mem v)) (hcen d hd _ (hc.mem w))
      (hsq2 d hd), mul_mul_eq_of_commute hcv]
    calc ⁅rep w, rep v⁆ * (rep v * rep v) * (rep w * rep w)
        = rep v * rep v * ⁅rep w, rep v⁆ * (rep w * rep w) := by rw [hcvw]
      _ = rep v * rep v * (⁅rep w, rep v⁆ * (rep w * rep w)) := by group
      _ = rep v * rep v * ((rep w * rep w) * ⁅rep w, rep v⁆) := by
          rw [hcen _ (hcm v w) _ (mul_mem (hc.mem w) (hc.mem w))]
      _ = rep v * rep v * (rep w * rep w) * ⁅rep w, rep v⁆ := by group
  ·
    obtain ⟨d, hd, hdeq⟩ := hrep v w
    show ⁅rep (xorF v w), rep u⁆ = ⁅rep v, rep u⁆ * ⁅rep w, rep u⁆
    rw [hdeq, commutator_mul_mul_left (hcen d hd _ (hc.mem u))
      (hcen _ (hcm u w) _ (hc.mem v)).symm]
    exact mem_centralizer_iff.mp (hPC (hEAP (hcm u v))) _ (hcm u w)
  ·
    show ⁅rep w, rep v⁆ = ⁅rep v, rep w⁆
    have h1 : ⁅rep w, rep v⁆ = ⁅rep v, rep w⁆⁻¹ := by rw [commutatorElement_inv]
    rw [h1]
    have h2 := hsq2 _ (hcm w v)
    exact (inv_eq_of_mul_eq_one_right h2)

omit [IsMulCommutative ↥(E ⊓ A)] in
theorem sqE_eq_one_of_mem_oval {o : Fin 64} (ho : ∃ i : Fin 6, o.val ∈ hexaOval[(i : ℕ)]!) :
    sqE rep (sq_rep_mem h11 hE16 hF hL hodd hx hxS h4 e hc) o = 1 := by
  obtain ⟨i, hi⟩ := ho
  set V := e.symm i with hV
  have hoV : rep o ∈ (V : Subgroup G) := by
    rw [hc.plane, hV, Equiv.apply_symm_apply]
    exact hi
  obtain ⟨hVe, -⟩ := isElemAbelian_and_card_of_mem_planes hF V.2.1
  apply Subtype.ext
  show rep o * rep o = 1
  rw [← sq]
  exact hVe.2 _ hoV

omit [IsMulCommutative ↥(E ⊓ A)] in
theorem conj_sqE (n : ↥(normalizer (sec2P E : Set G))) (v : Fin 64) :
    (n : G) * (sqE rep (sq_rep_mem h11 hE16 hF hL hodd hx hxS h4 e hc) v : G) * (n : G)⁻¹ =
      sqE rep (sq_rep_mem h11 hE16 hF hL hodd hx hxS h4 e hc) (ψ n v) := by
  have hPC := sec2P_le_centralizer_inf h11 hE16 hF hL hodd
  obtain ⟨hEe, -⟩ := isElemAbelian_and_card_of_mem_planes hF
    (⟨1, Or.inl (rightConjugate_one E).symm⟩ : E ∈ planes E F)
  set d := (rep (ψ n v))⁻¹ * ((n : G) * rep v * (n : G)⁻¹) with hd
  have hdE : d ∈ E ⊓ A := hc.conj n v
  have hdd : d * d = 1 := by rw [← sq]; exact hEe.2 d hdE.1
  have hda : d * rep (ψ n v) = rep (ψ n v) * d := mem_centralizer_iff.mp (hPC (hc.mem _)) d hdE
  have e1 : (n : G) * rep v * (n : G)⁻¹ = rep (ψ n v) * d := by rw [hd]; group
  show (n : G) * (rep v * rep v) * (n : G)⁻¹ = rep (ψ n v) * rep (ψ n v)
  calc (n : G) * (rep v * rep v) * (n : G)⁻¹
      = ((n : G) * rep v * (n : G)⁻¹) * ((n : G) * rep v * (n : G)⁻¹) := by group
    _ = rep (ψ n v) * d * (rep (ψ n v) * d) := by rw [e1]
    _ = rep (ψ n v) * (d * rep (ψ n v)) * d := by group
    _ = rep (ψ n v) * (rep (ψ n v) * d) * d := by rw [hda]
    _ = rep (ψ n v) * rep (ψ n v) * (d * d) := by group
    _ = rep (ψ n v) * rep (ψ n v) := by rw [hdd, mul_one]

omit [IsMulCommutative ↥(E ⊓ A)] in
theorem sqE_omegaF (v : Fin 64) :
    sqE rep (sq_rep_mem h11 hE16 hF hL hodd hx hxS h4 e hc) (omegaF v) =
      sqE rep (sq_rep_mem h11 hE16 hF hL hodd hx hxS h4 e hc) v := by
  set q := sqE rep (sq_rep_mem h11 hE16 hF hL hodd hx hxS h4 e hc) with hq
  obtain ⟨n, hnc, hρn, hnω⟩ := exists_sec2K_omega h11 hE16 hF hL hodd hx hxS h4 e hc
  have hnK : (n : G) ∈ sec2K E := Subgroup.commutator_le_self _ hnc
  have hnC := mem_centralizer_of_sec2KAction_eq_one h11 hE16 hF hL hodd hx hxS h4 e hc
    (t := ⟨n, hnK⟩) (Subtype.ext hρn)
  have hfix : ∀ w : Fin 64, q (ψ n w) = q w := fun w => by
    apply Subtype.ext
    rw [← conj_sqE h11 hE16 hF hL hodd hx hxS h4 e hc n w]
    have h1 := mem_centralizer_iff.mp hnC _ (q w).2
    calc (n : G) * (q w : G) * (n : G)⁻¹ = (q w : G) * n * (n : G)⁻¹ := by rw [h1]
      _ = q w := by group
  rcases hnω with h | h
  · have := hfix v
    rwa [h, omegaPerm_apply] at this
  · have h2 : ∀ w : Fin 64, q (omegaF (omegaF w)) = q w := fun w => by
      have := hfix w
      rwa [h, Equiv.Perm.mul_apply, omegaPerm_apply, omegaPerm_apply] at this
    calc q (omegaF v) = q (omegaF (omegaF (omegaF (omegaF v)))) := by
          rw [omegaF_omegaF_omegaF]
      _ = q (omegaF (omegaF v)) := h2 _
      _ = q v := h2 v

omit [IsMulCommutative ↥(E ⊓ A)] hx hxS h4 in
theorem inSecM_psi (n : ↥(normalizer (sec2P E : Set G))) {x y : Fin 6} (hxy : x ≠ y)
    {a c : Fin 64} (ha : a ∈ ovalNz x) (hc' : c ∈ ovalNz y) :
    inSecM (sec2PlanesActionFin E F e n x) (sec2PlanesActionFin E F e n y) (ψ n (xorF a c)) =
      true := by
  obtain ⟨ha0, ha'⟩ := ovalNz_spec x a ha
  obtain ⟨hc0, hc''⟩ := ovalNz_spec y c hc'
  have h0 : ψ n 0 = 0 := map_zero_of_add (hc.psi_add n)
  have hne : ∀ w : Fin 64, w ≠ 0 → ψ n w ≠ 0 := fun w hw h => hw ((ψ n).injective (h.trans h0.symm))
  rw [hc.psi_add]
  exact inSecM_of_mem (fun h => hxy ((sec2PlanesActionFin E F e n).injective h)) (hne a ha0)
    (hne c hc0) (psi_mem_oval h11 hE16 hF hL hodd hc n x a ha')
    (psi_mem_oval h11 hE16 hF hL hodd hc n y c hc'')

omit [IsMulCommutative ↥(E ⊓ A)] hx hxS h4 in
theorem psi_rep2 (n : ↥(normalizer (sec2P E : Set G))) {j j' : Fin 6} (h : j ≠ j') :
    let σ := sec2PlanesActionFin E F e n
    ψ n (rep2 j j') = rep2 (CFSG.CharacterTheory.SteinbergBY.AlternatingSix.totalPerm σ j)
        (CFSG.CharacterTheory.SteinbergBY.AlternatingSix.totalPerm σ j') ∨
      ψ n (rep2 j j') = omegaF (rep2 (CFSG.CharacterTheory.SteinbergBY.AlternatingSix.totalPerm σ j)
        (CFSG.CharacterTheory.SteinbergBY.AlternatingSix.totalPerm σ j')) ∨
      ψ n (rep2 j j') = omegaF (omegaF (rep2
        (CFSG.CharacterTheory.SteinbergBY.AlternatingSix.totalPerm σ j)
        (CFSG.CharacterTheory.SteinbergBY.AlternatingSix.totalPerm σ j'))) := by
  intro σ
  have hne : CFSG.CharacterTheory.SteinbergBY.AlternatingSix.totalPerm σ j ≠
      CFSG.CharacterTheory.SteinbergBY.AlternatingSix.totalPerm σ j' := fun h' =>
    h ((CFSG.CharacterTheory.SteinbergBY.AlternatingSix.totalPerm σ).injective h')
  refine eq_rep2_of_inSecM hne fun y => ?_
  obtain ⟨a, ha, c, hc', hac⟩ := rep2_decomp h (σ⁻¹ y)
  have h1 := inSecM_psi h11 hE16 hF hL hodd e hc n
    (synT_ne j j' h (σ⁻¹ y)).symm ha hc'
  rw [hac] at h1
  have hy : σ (σ⁻¹ y) = y := σ.apply_symm_apply y
  rw [hy, conj_synT σ h y] at h1
  exact h1

end Frame

end CFSG.ComponentClassification.AS81
