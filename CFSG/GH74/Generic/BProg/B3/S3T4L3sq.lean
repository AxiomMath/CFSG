module

public import CFSG.GH74.Generic.BProg.B3.S3T4H175
public import CFSG.GH74.Generic.BProg.B2.PumpupTableOutL3
public import CFSG.GH74.Generic.BProg.B3.S3Sec29D1
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvStar

public section

namespace CFSG.GH74.Generic.BProg.B3

open Matrix Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg
  CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.KGroups.L3Eps
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped MatrixGroups commutatorElement

namespace S3T4

theorem mul_normal_form {F : Type} [Field F] (A A' : GL (Fin 3) F) (σ σ' : F ≃+* F)
    {ε ε' : ℕ} (hε : ε ≤ 1) :
    ∃ B : GL (Fin 3) F, (conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F ^ ε) *
      (conjAut 3 F A' * fieldAut 3 F σ' * dualAut 3 F ^ ε') =
        conjAut 3 F B * fieldAut 3 F (σ * σ') * dualAut 3 F ^ (ε + ε') := by
  obtain ⟨hcc, hff, -, -, -⟩ := standard_automorphism_transport (n := 3) (K := F)
  interval_cases ε
  · refine ⟨A * GeneralLinearGroup.map (σ : F →+* F) A', ?_⟩
    calc conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F ^ 0 *
          (conjAut 3 F A' * fieldAut 3 F σ' * dualAut 3 F ^ ε')
        = conjAut 3 F A * (fieldAut 3 F σ * conjAut 3 F A') * fieldAut 3 F σ' *
            dualAut 3 F ^ ε' := by rw [pow_zero, mul_one]; simp only [mul_assoc]
      _ = conjAut 3 F A * conjAut 3 F (GeneralLinearGroup.map (σ : F →+* F) A') *
            (fieldAut 3 F σ * fieldAut 3 F σ') * dualAut 3 F ^ ε' := by
          rw [fieldAut_mul_conjAut]; simp only [mul_assoc]
      _ = _ := by rw [hcc, hff, zero_add]
  · refine ⟨A * GeneralLinearGroup.map (σ : F →+* F) (GeneralLinearGroup.inverseTranspose A'), ?_⟩
    calc conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F ^ 1 *
          (conjAut 3 F A' * fieldAut 3 F σ' * dualAut 3 F ^ ε')
        = conjAut 3 F A * fieldAut 3 F σ * (dualAut 3 F * conjAut 3 F A') * fieldAut 3 F σ' *
            dualAut 3 F ^ ε' := by rw [pow_one]; simp only [mul_assoc]
      _ = conjAut 3 F A * (fieldAut 3 F σ *
            conjAut 3 F (GeneralLinearGroup.inverseTranspose A')) *
            (dualAut 3 F * fieldAut 3 F σ') * dualAut 3 F ^ ε' := by
          rw [dualAut_mul_conjAut]; simp only [mul_assoc]
      _ = conjAut 3 F A * conjAut 3 F (GeneralLinearGroup.map (σ : F →+* F)
            (GeneralLinearGroup.inverseTranspose A')) * (fieldAut 3 F σ * fieldAut 3 F σ') *
            (dualAut 3 F * dualAut 3 F ^ ε') := by
          rw [fieldAut_mul_conjAut, dualAut_mul_fieldAut]; simp only [mul_assoc]
      _ = _ := by rw [hcc, hff, ← pow_succ', add_comm]
section Certified


theorem false_of_inner_qShape3 {N : Type} [Group N] [Finite N] {H L : Subgroup N} {t : N}
    (hs : B2.ShapeInCent H t L) (htH : t ∈ H) (h3 : QShape3 ↥H) : False := by
  classical
  have := hs.simple
  have hZ : ∀ z : ↥H, (∀ g, g * z = z * g) → z = 1 := by
    intro z hz
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥H) with hc | hc
    · have hzc : z ∈ center ↥H := Subgroup.mem_center_iff.2 fun g => hz g
      rw [hc] at hzc
      exact Subgroup.mem_bot.1 hzc
    · exfalso
      have hall : ∀ h : ↥H, h = 1 := fun h => by
        have h1 : ((h : ↥H) : N) = 1 := hs.faithful _ fun k hk => by
          have hmem : h ∈ center ↥H := by rw [hc]; trivial
          exact congrArg Subtype.val ((Subgroup.mem_center_iff.1 hmem) ⟨k, hk⟩).symm
        exact Subtype.ext h1
      obtain ⟨a, b, hab⟩ := exists_pair_ne ↥H
      exact hab ((hall a).trans (hall b).symm)
  set u : ↥H := ⟨t, htH⟩ with hu
  have hu2 : orderOf u = 2 := by
    rw [hu, Subgroup.orderOf_mk]
    exact hs.inv
  obtain ⟨F, _, _, S, hodd, -, ⟨eS⟩, -, -, hcomm, -, -⟩ :=
    S3L3KGroup.exists_sl2_component h3 hZ hu2
  have hSL := S3Sec29D1.SL2Data.of_equiv eS (S3Sec29D1.sl2Data_sl2 hodd)
  have hLH : L ≤ H := hs.comp.1.trans inf_le_left
  have hLq : IsQuasisimple ↥L := B2.Prop31.isQuasisimple_of_isCompIn hs.comp
  have hLperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.1 hLq.1
  set L' : Subgroup ↥H := L.subgroupOf H with hL'
  have hL'perf : ⁅L', L'⁆ = L' := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hLH, hLperf]
  have hL'C : ∀ l ∈ L', l ∈ centralizer ({u} : Set ↥H) := by
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.1 (hs.comp.1 (Subgroup.mem_subgroupOf.1 hl)).2
  have hL'S : L' ≤ S := by
    rw [← hL'perf, Subgroup.commutator_le]
    intro a ha b hb
    exact hcomm a (hL'C a ha) b (hL'C b hb)
  obtain ⟨a, haL, b, hbL, ha2, hb2, ha1, hb1, hab⟩ :=
    B2.PumpupTableTwoInv.hasTwoInvolutions_of_shapeInCent hs
  have hinv : ∀ (c : N) (hc : c ∈ L), c * c = 1 → c ≠ 1 → ∀ hcS : (⟨c, hLH hc⟩ : ↥H) ∈ S,
      (⟨⟨c, hLH hc⟩, hcS⟩ : ↥S) = eS.symm (-1) := by
    intro c hc hc2 hc1 hcS
    have hsq : (⟨⟨c, hLH hc⟩, hcS⟩ : ↥S) * ⟨⟨c, hLH hc⟩, hcS⟩ = 1 := by
      have h1 : (⟨c, hLH hc⟩ : ↥H) * ⟨c, hLH hc⟩ = 1 := Subtype.ext hc2
      exact Subtype.ext h1
    rcases hSL.invol_eq _ hsq with h | h
    · exact absurd (congrArg (fun x : ↥S => ((x : ↥H) : N)) h) hc1
    · exact h
  have h1 := hinv a haL ha2 ha1 (hL'S (Subgroup.mem_subgroupOf.2 haL))
  have h2 := hinv b hbL hb2 hb1 (hL'S (Subgroup.mem_subgroupOf.2 hbL))
  exact hab (congrArg (fun x : ↥S => ((x : ↥H) : N)) (h1.trans h2.symm))


theorem false_of_graph {N : Type} [Group N] [Finite N] {H L : Subgroup N} {t : N} [H.Normal]
    {F : Type} [Field F] [Finite F] {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n)
    (hF : Nat.card F = p ^ n) (h5 : 5 ≤ Nat.card F) (hs : B2.ShapeInCent H t L)
    (e : ↥H ≃* projectiveSL 3 F) {A : GL (Fin 3) F} (hAs : (A : Matrix (Fin 3) (Fin 3) F)ᵀ = A)
    (hA : conjAutEquiv e (MulAut.conjNormal t) = conjAut 3 F A * dualAut 3 F) : False := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hFodd : Odd (Nat.card F) := by rw [hF]; exact hpodd.pow
  have h2 : (2 : F) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hFodd
  have hF2 : ringChar F ≠ 2 := fun h => h2 (by
    have : CharP F 2 := h ▸ ringChar.charP F
    exact CharTwo.two_eq_zero)
  have h3 : Nat.card F ≠ 3 := by omega
  set c : MulAut ↥H := MulAut.conjNormal t with hcdef
  obtain ⟨N0, hq, hfix, hconj, hcomm, ⟨eN⟩⟩ :=
    B2.PumpupTableOutL3.lin_graph_centralizer_psl2 hF2 h3 hAs
  rw [← hA] at hfix hconj hcomm
  have hfixK : ∀ x : ↥H, c x = x → conjAutEquiv e c (e x) = e x := fun x hx => by
    rw [conjAutEquiv_apply, hx]
  set S : Subgroup ↥H := N0.map (e.symm : projectiveSL 3 F →* ↥H) with hSdef
  have hmemS : ∀ x : ↥H, x ∈ S ↔ e x ∈ N0 := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨e x, hx, by simp⟩
  have hSq : IsQuasisimple ↥S :=
    LocalCores.isQuasisimple_of_mulEquiv (MulEquiv.subgroupMap e.symm N0) hq
  set C : Subgroup ↥H := (H ⊓ Subgroup.centralizer ({t} : Set N)).subgroupOf H with hC
  have hmemC : ∀ x : ↥H, x ∈ C ↔ c x = x := by
    intro x
    rw [hC, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨-, hx⟩
      apply Subtype.ext
      change t * (x : N) * t⁻¹ = x
      rw [← hx]
      group
    · intro hx
      refine ⟨x.2, ?_⟩
      have := congrArg Subtype.val hx
      change t * (x : N) * t⁻¹ = x at this
      calc (x : N) * t = (t * (x : N) * t⁻¹) * t := by rw [this]
        _ = t * x := by group
  have hSC : S ≤ C := by
    intro x hx
    rw [hmemC]
    have hx' := (hmemS x).1 hx
    apply e.injective
    have h1 := hfix (e x) hx'
    rw [conjAutEquiv_apply] at h1
    exact h1
  have hSn : ∀ x ∈ C, ∀ s ∈ S, x * s * x⁻¹ ∈ S := by
    intro x hx s hs
    rw [hmemS] at hs ⊢
    rw [map_mul, map_mul, map_inv]
    exact hconj (e x) (hfixK x ((hmemC x).1 hx)) (e s) hs
  have hSc : ∀ x ∈ C, ∀ z ∈ C, ⁅x, z⁆ ∈ S := by
    intro x hx z hz
    rw [hmemS, map_commutatorElement]
    exact hcomm (e x) (e z) (hfixK x ((hmemC x).1 hx)) (hfixK z ((hmemC z).1 hz))
  have hB : IsCompIn C (L.subgroupOf H) := by
    have hCH : H ⊓ Subgroup.centralizer ({t} : Set N) ≤ H := inf_le_left
    exact ⟨Subgroup.comap_mono hs.comp.1,
      (CFSG.GH74.GLS.LU.Local.isComponent_subgroupOf_iff' (K := L)
        (M := H ⊓ Subgroup.centralizer ({t} : Set N)) (H := H) hCH).2 hs.comp.2⟩
  have hLS : L.subgroupOf H = S :=
    CFSG.GH74.GLS.IVK.GHInv.eq_of_isCompIn_of_normal_quasisimple hSq hSC hSn hSc hB
  have hLH : L ≤ H := hs.comp.1.trans inf_le_left
  let eL : ↥L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    (Subgroup.subgroupOfEquivOfLe hLH).symm.trans ((MulEquiv.subgroupCongr hLS).trans
      ((MulEquiv.subgroupMap e.symm N0).symm.trans eN))
  exact B2.PumpupTableOmega3.false_of_psl2_component hs hp hp2
    (B2.PumpupTableOmega3.lieModel_psl2_of_equiv hp hn (by omega) hF eL)

end Certified

end S3T4

open S3T4

section CertifiedLeaf


theorem leaf514Fam_l3sq : Leaf514Fam (fun X _ => B2.PuL3sq X) := by
  intro N _ _ H L v w _ hP _ hvw hne hsv hsw hsvw
  obtain ⟨p, f, hp, hp2, hf, hLie⟩ := hP
  have hnorm : H.Normal := hsv.normal
  have hst := B2.PumpupTableBasic.stated_of_lieModel (Or.inl rfl) hLie
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_projectiveSL_equiv hst
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hFodd : Odd (Nat.card F) := by rw [hF]; exact hpodd.pow
  have h2 : (2 : F) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hFodd
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have h9 : 9 ≤ p ^ (2 * f) :=
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
      _ ≤ p ^ (2 * f) := Nat.pow_le_pow_right hp.pos (by omega)
  have hq3 : QShape3 ↥H := ⟨p, 2 * f, hp, hp2, by omega, Or.inl hLie⟩
  have hinv2 : ∀ t : N, B2.ShapeInCent H t L →
      conjAutEquiv e (MulAut.conjNormal t) * conjAutEquiv e (MulAut.conjNormal t) = 1 := by
    intro t hs
    have ht2 : t * t = 1 := by
      have := hs.inv
      rw [← pow_two]
      exact orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq this)
    rw [← conjAutEquiv_mul, ← map_mul, ht2, map_one, conjAutEquiv_one]
  have key : ∀ t : N, B2.ShapeInCent H t L → ∀ (B : GL (Fin 3) F) (ε : ℕ), ε ≤ 1 →
      conjAutEquiv e (MulAut.conjNormal t) = conjAut 3 F B * dualAut 3 F ^ ε → False := by
    intro t hs B ε hε hB
    have hc2 := hinv2 t hs
    interval_cases ε
    · rw [pow_zero, mul_one] at hB
      have hsq : conjAut 3 F (B * B) * fieldAut 3 F 1 = 1 := by
        rw [map_one, mul_one, map_mul, ← hB]
        exact hc2
      obtain ⟨-, u, hu⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one le_rfl (B * B) 1 hsq
      have hscal : ((GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) = (u : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
        rw [smul_one_eq_diagonal]; rfl
      have hBB : (B : Matrix (Fin 3) (Fin 3) F) * B = (u : F) • 1 := by
        rw [← hscal, hu, Units.val_mul]
      have hin : conjAutEquiv e (MulAut.conjNormal t) ∈ inner (projectiveSL 3 F) := by
        rw [hB]
        exact conjAut_mem_inner_of_sq_scalar B u hBB
      exact false_of_inner_qShape3 hs (B2.PumpupTableOutL3.mem_of_conjNormal_mem_inner H
        hs.faithful (conjAutEquiv_mem_inner e hin)) hq3
    · rw [pow_one] at hB
      have hsq : (conjAut 3 F B * fieldAut 3 F 1 * dualAut 3 F) ^ 2 = 1 := by
        rw [map_one, mul_one, pow_two, ← hB]
        exact hc2
      rcases OddHigherLinear.transpose_eq_or_eq_neg_of_sq le_rfl B hsq with h | h
      · exact false_of_graph hp hp2 (by omega) hF (by omega) hs e h hB
      · have hdet := congrArg Matrix.det h
        rw [Matrix.det_transpose, Matrix.det_neg] at hdet
        have hd0 : (B : Matrix (Fin 3) (Fin 3) F).det ≠ 0 :=
          ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit B)).ne_zero
        simp only [Fintype.card_fin] at hdet
        apply hd0
        have h22 : (2 : F) * (B : Matrix (Fin 3) (Fin 3) F).det = 0 := by
          linear_combination hdet
        exact (mul_eq_zero.1 h22).resolve_left h2
  have hform : ∀ t : N, B2.ShapeInCent H t L → ∃ (A : GL (Fin 3) F) (σ : F ≃+* F) (ε : ℕ),
      ε ≤ 1 ∧ σ ≠ 1 ∧ σ * σ = 1 ∧ conjAutEquiv e (MulAut.conjNormal t) =
        conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F ^ ε := by
    intro t hs
    have hc2 := hinv2 t hs
    obtain ⟨-, hgen⟩ := automorphism_generation (K := F) (n := 3) le_rfl
    obtain ⟨A, σ, ε, hε, hcA⟩ := hgen (conjAutEquiv e (MulAut.conjNormal t))
    have hσ2 : σ * σ = 1 := by
      obtain ⟨B, hB⟩ := sq_eq_conj_field A σ hε
      have h1 : conjAut 3 F B * fieldAut 3 F (σ ^ 2) = 1 := by
        rw [← hB, ← hcA, pow_two]
        exact hc2
      have := (eq_one_of_conjAut_mul_fieldAut_eq_one le_rfl B _ h1).1
      rwa [pow_two] at this
    refine ⟨A, σ, ε, hε, fun hσ1 => key t hs A ε hε ?_, hσ2, hcA⟩
    rw [hcA, hσ1, map_one, mul_one]
  obtain ⟨Av, σv, εv, hεv, hσv1, hσv2, hv⟩ := hform v hsv
  obtain ⟨Aw, σw, εw, hεw, hσw1, hσw2, hw⟩ := hform w hsw
  have hσ : σv = σw := by
    obtain ⟨-, hv'⟩ := even_and_eq_pow_of_involution_prime hp (by omega : 1 ≤ 2 * f) hF hσv1 hσv2
    obtain ⟨-, hw'⟩ := even_and_eq_pow_of_involution_prime hp (by omega : 1 ≤ 2 * f) hF hσw1 hσw2
    exact RingEquiv.ext fun x => (hv' x).trans (hw' x).symm
  obtain ⟨B, hB⟩ := mul_normal_form Av Aw σv σw (ε' := εw) hεv
  have hδδ : dualAut 3 F * dualAut 3 F = 1 :=
    (standard_automorphism_transport (n := 3) (K := F)).2.2.2.1
  have hpow : dualAut 3 F ^ (εv + εw) = dualAut 3 F ^ ((εv + εw) % 2) := by
    interval_cases εv <;> interval_cases εw <;> simp [pow_two, hδδ]
  have hvw' : conjAutEquiv e (MulAut.conjNormal (v * w)) =
      conjAut 3 F B * dualAut 3 F ^ ((εv + εw) % 2) := by
    rw [map_mul, conjAutEquiv_mul, hv, hw, hB, ← hσ, hσv2, map_one, mul_one, hpow]
  exact key (v * w) hsvw B _ (by omega) hvw'

end CertifiedLeaf

end CFSG.GH74.Generic.BProg.B3
