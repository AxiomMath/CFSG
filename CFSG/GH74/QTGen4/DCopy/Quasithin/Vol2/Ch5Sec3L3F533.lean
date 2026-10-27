module

public import CFSG.Quasithin.Vol2.Ch5Sec3L3F533
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec3Facts533
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec3L3ExcCoords
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec3L3Semi
import CFSG.Quasithin.Vol2.Ch3Sec1Thm311

public section

namespace CFSG.Quasithin.H13.Sec53L3

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F1
  CFSG.Quasithin.SL2Semilinear CFSG.LieType.BorelTits

open scoped commutatorElement

section L3

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D L₂ : Subgroup G} {n f : ℕ}
  {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in

theorem mem_S_of_linear'_F4 (h527 : Stmt5_2_7_F4) (h531 : Stmt5_3_1_F4)
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hty : IsOfLieType52 M L H B D T .PSL 3 f)
    (hf : 2 ≤ f) {G₁ B₁ L' V₁ V₂ : Subgroup G} (C : V1Coords G₁ B₁ L' V₁ V₂ (sec53ZS T L) F)
    {t : G} (htT : t ∈ T) {τ : F × F ≃+ F × F} (hτ : ∀ p, C.ι (τ p) = t * C.ι p * t⁻¹)
    (hlin : ∀ (c : F) (p : F × F), τ (c • p) = c • τ p) (hZ : (τ (0, 1)).1 = 0) :
    t ∈ sec53S T L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_1_8.toHyp5_0_1
  set E := (τ (0, 1)).2 with hE
  have hiter : ∀ m : ℕ, (⇑τ)^[m] ((0 : F), (1 : F)) = (0, E ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Function.iterate_succ_apply', ih, zero_form hlin hZ, pow_succ, mul_comm]
  obtain ⟨k, hk⟩ := h.sylow.1 ⟨t, htT⟩
  have hk' : t ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hE1 : E = 1 := by
    have h1 := C.iterate_conj hτ (2 ^ k) (0, 1)
    rw [hk', one_mul, inv_one, mul_one, hiter] at h1
    have h2 := congrArg Prod.snd (C.inj h1)
    exact eq_one_of_pow_two_pow' h2.symm
  have hfix : ∀ c : F, τ (0, c) = (0, c) := fun c => by
    rw [zero_form hlin hZ, ← hE, hE1, mul_one]
  have htC : t ∈ Subgroup.centralizer (sec53ZS T L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨c, rfl⟩ := (C.center y).mp hy
    have h3 : t * C.ι (0, c) * t⁻¹ = C.ι (0, c) := by rw [← hτ, hfix]
    calc C.ι (0, c) * t = t * C.ι (0, c) * t⁻¹ * t := by rw [h3]
      _ = t * C.ι (0, c) := by group
  rw [← l3facts_one_F4 h527 h531 hyp hty hf]
  exact Subgroup.mem_inf.mpr ⟨htT, htC⟩

omit [Finite F] in

theorem mem_S_iff_uni_F4 (h527 : Stmt5_2_7_F4) (h531 : Stmt5_3_1_F4)
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hty : IsOfLieType52 M L H B D T .PSL 3 f)
    (hf : 2 ≤ f)
    (C : V1Coords (sec53G1 M L H B) (sec53G1 M L H B ⊓ sec53G2 M L H D) L (pCoreOf 2 L)
      (pCoreOf 2 (oTwoUpper H)) (sec53ZS T L) F) {y : G} (hyL : y ∈ L) :
    y ∈ sec53S T L ↔ ∃ β : F, ∀ u v, y * C.ι (u, v) * y⁻¹ = C.ι (u, β * u + v) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_1_8.toHyp5_0_1
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hpar : IsSec53Param .PSL 3 f := ⟨hf, Or.inl ⟨rfl, rfl⟩⟩
  obtain ⟨-, ⟨hCT, hO2, -, -⟩, -, -⟩ := h531 G T M L V H B D L₂ n .PSL 3 f hyp hty hpar
  have hLG : L ≤ sec53G1 M L H B := le_sup_left.trans le_sup_left
  have hsup := sup_sec53_F4 h527 hyp hty hf
  have hV₁S : pCoreOf 2 L ≤ sec53S T L := le_sup_left.trans hsup.le
  have hV₂S : pCoreOf 2 (oTwoUpper H) ≤ sec53S T L := le_sup_right.trans hsup.le
  have hV₂L : pCoreOf 2 (oTwoUpper H) ≤ L := hV₂S.trans inf_le_right
  constructor
  · intro hyS
    obtain ⟨α, β, γ, δ, hlin⟩ := C.lin y (hLG hyL)

    have hz : y * C.ι (0, 1) * y⁻¹ = C.ι (0, 1) := by
      have hc := Subgroup.mem_centralizer_iff.mp
        ((inf_le_right : centerOf (sec53S T L) ≤ Subgroup.centralizer (sec53S T L : Set G))
          ((C.center _).mpr ⟨1, rfl⟩)) y hyS
      rw [hc]
      group
    rw [hlin] at hz
    have hz' := C.inj hz
    simp only [mul_zero, mul_one, zero_add, Prod.mk.injEq] at hz'
    obtain ⟨hβ, hδ⟩ := hz'

    have hyV : y ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
      normalizer_le_normalizer_pCoreOf 2 L (Subgroup.le_normalizer hyL)
    obtain ⟨τ, hτ⟩ := C.exists_conj_equiv hyV
    have hform : ∀ p, τ p = (α * p.1 + β * p.2, γ * p.1 + δ * p.2) := fun p =>
      C.inj (by rw [hτ]; exact hlin p.1 p.2)
    obtain ⟨k, hk⟩ := h.sylow.1 ⟨y, (inf_le_left : sec53S T L ≤ T) hyS⟩
    have hk' : y ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hα : α = 1 := C.eq_one_of_two_power hτ (fun p => by rw [hform, hβ]; ring) hk'
    refine ⟨γ, fun u v => ?_⟩
    rw [hlin, hα, hβ, hδ]
    congr 2 <;> ring
  · rintro ⟨β, hβ⟩
    have hye : ∀ u v, (C.ye β)⁻¹ * C.ι (u, v) * C.ye β = C.ι (u, β * u + v) := by
      intro u v
      have h1 := C.ye_act β (u, β * u + v)
      rw [tvY_apply] at h1
      have e : C.ι ((u, β * u + v).1, (u, β * u + v).2 + β * (u, β * u + v).1) = C.ι (u, v) := by
        congr 1
        ext
        · rfl
        · show β * u + v + β * u = v
          linear_combination (β * u) * h2
      rw [e] at h1
      rw [← h1]
      group
    have hxC : y * (C.ye β)⁻¹ ∈ Subgroup.centralizer (pCoreOf 2 L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      obtain ⟨⟨u, v⟩, rfl⟩ := C.surj w hw
      have e : y * (C.ye β)⁻¹ * C.ι (u, v) * (y * (C.ye β)⁻¹)⁻¹ = C.ι (u, v) := by
        calc y * (C.ye β)⁻¹ * C.ι (u, v) * (y * (C.ye β)⁻¹)⁻¹ =
            y * ((C.ye β)⁻¹ * C.ι (u, v) * C.ye β) * y⁻¹ := by group
          _ = C.ι (u, v) := by
            rw [hye, hβ]
            congr 2
            linear_combination (β * u) * h2
      calc C.ι (u, v) * (y * (C.ye β)⁻¹) =
          y * (C.ye β)⁻¹ * C.ι (u, v) * (y * (C.ye β)⁻¹)⁻¹ * (y * (C.ye β)⁻¹) := by rw [e]
        _ = y * (C.ye β)⁻¹ * C.ι (u, v) := by group
    have hxM : y * (C.ye β)⁻¹ ∈ sec53M1 L :=
      (sec53M1 L).mul_mem (Subgroup.le_normalizer hyL)
        ((sec53M1 L).inv_mem (Subgroup.le_normalizer (hV₂L (C.ye_mem β))))
    have hxV : y * (C.ye β)⁻¹ ∈ pCoreOf 2 L := by
      have h1 := hCT (Subgroup.mem_inf.mpr ⟨hxM, by rw [hO2]; exact hxC⟩)
      rwa [hO2] at h1
    have e : y = y * (C.ye β)⁻¹ * C.ye β := by group
    rw [e]
    exact (sec53S T L).mul_mem (hV₁S hxV) (hV₂S (C.ye_mem β))

omit [Finite F] in

theorem exists_diag_mem_F4 (h527 : Stmt5_2_7_F4) (h531 : Stmt5_3_1_F4)
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hty : IsOfLieType52 M L H B D T .PSL 3 f)
    (hf : 2 ≤ f)
    (C : V1Coords (sec53G1 M L H B) (sec53G1 M L H B ⊓ sec53G2 M L H D) L (pCoreOf 2 L)
      (pCoreOf 2 (oTwoUpper H)) (sec53ZS T L) F) {t : F} (ht : t ≠ 0) :
    ∃ d ∈ sec53M12 L H, ∀ u v, d * C.ι (u, v) * d⁻¹ = C.ι (t * u, t⁻¹ * v) := by
  have hpar : IsSec53Param .PSL 3 f := ⟨hf, Or.inl ⟨rfl, rfl⟩⟩
  obtain ⟨-, -, ⟨hN, -, -⟩, -⟩ := h531 G T M L V H B D L₂ n .PSL 3 f hyp hty hpar
  have hsup := sup_sec53_F4 h527 hyp hty hf
  have hV₂L : pCoreOf 2 (oTwoUpper H) ≤ L :=
    (le_sup_right.trans hsup.le).trans (inf_le_right : sec53S T L ≤ L)
  set d := (C.xe t * C.ye t⁻¹ * C.xe t) * (C.xe 1 * C.ye 1⁻¹ * C.xe 1)⁻¹ with hd
  have hdL : d ∈ L := by
    have hw : ∀ a : F, C.xe a * C.ye a⁻¹ * C.xe a ∈ L := fun a =>
      L.mul_mem (L.mul_mem (C.xe_mem a) (hV₂L (C.ye_mem a⁻¹))) (C.xe_mem a)
    exact L.mul_mem (hw t) (L.inv_mem (hw 1))
  have hdact : ∀ u v, d * C.ι (u, v) * d⁻¹ = C.ι (t * u, t⁻¹ * v) := C.d_act ht
  have hdinv : ∀ u v, d⁻¹ * C.ι (u, v) * d = C.ι (t⁻¹ * u, t * v) := by
    intro u v
    have h1 := hdact (t⁻¹ * u) (t * v)
    have e : C.ι (t * (t⁻¹ * u), t⁻¹ * (t * v)) = C.ι (u, v) := by
      congr 2 <;> field_simp
    rw [e] at h1
    rw [← h1]
    group

  have hS1 : ∀ y ∈ sec53S T L, d * y * d⁻¹ ∈ sec53S T L := by
    intro y hy
    have hyL : y ∈ L := (inf_le_right : sec53S T L ≤ L) hy
    obtain ⟨β, hβ⟩ := (mem_S_iff_uni_F4 h527 h531 hyp hty hf C hyL).mp hy
    refine (mem_S_iff_uni_F4 h527 h531 hyp hty hf C
      (L.mul_mem (L.mul_mem hdL hyL) (L.inv_mem hdL))).mpr ⟨β * t⁻¹ * t⁻¹, fun u v => ?_⟩
    calc d * y * d⁻¹ * C.ι (u, v) * (d * y * d⁻¹)⁻¹ =
        d * (y * (d⁻¹ * C.ι (u, v) * d) * y⁻¹) * d⁻¹ := by group
      _ = C.ι (u, β * t⁻¹ * t⁻¹ * u + v) := by
        rw [hdinv, hβ, hdact]
        congr 2
        · field_simp
        · field_simp
  have hS2 : ∀ y ∈ sec53S T L, d⁻¹ * y * d ∈ sec53S T L := by
    intro y hy
    have hyL : y ∈ L := (inf_le_right : sec53S T L ≤ L) hy
    obtain ⟨β, hβ⟩ := (mem_S_iff_uni_F4 h527 h531 hyp hty hf C hyL).mp hy
    refine (mem_S_iff_uni_F4 h527 h531 hyp hty hf C
      (L.mul_mem (L.mul_mem (L.inv_mem hdL) hyL) hdL)).mpr ⟨β * t * t, fun u v => ?_⟩
    calc d⁻¹ * y * d * C.ι (u, v) * (d⁻¹ * y * d)⁻¹ =
        d⁻¹ * (y * (d * C.ι (u, v) * d⁻¹) * y⁻¹) * d := by group
      _ = C.ι (u, β * t * t * u + v) := by
        rw [hdact, hβ, hdinv]
        congr 2
        · field_simp
        · field_simp
  refine ⟨d, ?_, fun u v => ?_⟩
  · rw [← hN, Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hS1 y, fun hy => ?_⟩
    have := hS2 _ hy
    simpa [mul_assoc] using this
  · exact hdact u v

theorem isSolvable_M12_F4 (h527 : Stmt5_2_7_F4) (h531 : Stmt5_3_1_F4)
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hty : IsOfLieType52 M L H B D T .PSL 3 f)
    (hf : 2 ≤ f) : Group.IsSolvable (sec53M12 L H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpar : IsSec53Param .PSL 3 f := ⟨hf, Or.inl ⟨rfl, rfl⟩⟩
  obtain ⟨-, ⟨hCT, hO2, -, -⟩, ⟨hN, -, -⟩, -⟩ :=
    h531 G T M L V H B D L₂ n .PSL 3 f hyp hty hpar
  obtain ⟨F, _, _, _, -, ⟨C⟩⟩ := exists_v1Coords_F4 h527 hyp hty hf
  have hLG : L ≤ sec53G1 M L H B := le_sup_left.trans le_sup_left
  have hsup := sup_sec53_F4 h527 hyp hty hf
  have hV₂L : pCoreOf 2 (oTwoUpper H) ≤ L :=
    (le_sup_right.trans hsup.le).trans (inf_le_right : sec53S T L ≤ L)
  set X := sec53M12 L H with hX
  have hXL : ∀ g ∈ X, g ∈ Subgroup.normalizer (L : Set G) := fun g hg =>
    (Subgroup.mem_inf.mp hg).1
  have hXV : ∀ g ∈ X, g ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) := fun g hg =>
    normalizer_le_normalizer_pCoreOf 2 L (hXL g hg)
  have hZ : ∀ g ∈ X, ∀ τ : F × F ≃+ F × F, (∀ p, C.ι (τ p) = g * C.ι p * g⁻¹) →
      (τ (0, 1)).1 = 0 := by
    intro g hg τ hτ
    have hgN : g ∈ Subgroup.normalizer (sec53S T L : Set G) := by rw [hN]; exact hg
    have h1 : C.ι (τ (0, 1)) ∈ sec53ZS T L := by
      rw [hτ]
      exact conj_mem_centerOf hgN ((C.center _).mpr ⟨1, rfl⟩)
    obtain ⟨c, hc⟩ := (C.center _).mp h1
    rw [C.inj hc]
  have hD1 : derivedSeriesOf X 1 ≤ C.linSub X := by
    rw [derivedSeriesOf_succ, derivedSeriesOf_zero, Subgroup.commutator_le]
    intro g hg h hh
    obtain ⟨τg, σg, hτg, hσg⟩ := C.exists_semilinear hLG hV₂L (hXL g hg) (hXV g hg)
    obtain ⟨τh, σh, hτh, hσh⟩ := C.exists_semilinear hLG hV₂L (hXL h hh) (hXV h hh)
    exact C.comm_mem_linSub hg hh hτg hσg hτh hσh
  have hD2 : derivedSeriesOf X 2 ≤ C.uniSub X := by
    rw [derivedSeriesOf_succ]
    refine (Subgroup.commutator_mono hD1 hD1).trans ?_
    rw [Subgroup.commutator_le]
    intro g hg h hh
    exact C.comm_mem_uniSub hZ hg hh
  have hD3 : derivedSeriesOf X 3 ≤ pCoreOf 2 L := by
    rw [derivedSeriesOf_succ]
    refine (Subgroup.commutator_mono hD2 hD2).trans ?_
    rw [Subgroup.commutator_le]
    rintro g ⟨hgX, β, hβ⟩ h ⟨hhX, β', hβ'⟩
    have hgM : g ∈ sec53M1 L := hXL g hgX
    have hhM : h ∈ sec53M1 L := hXL h hhX
    have hc : ⁅g, h⁆ ∈ sec53M1 L := by
      rw [commutatorElement_def]
      exact (sec53M1 L).mul_mem ((sec53M1 L).mul_mem ((sec53M1 L).mul_mem hgM hhM)
        ((sec53M1 L).inv_mem hgM)) ((sec53M1 L).inv_mem hhM)
    have hcC : ⁅g, h⁆ ∈ Subgroup.centralizer (pCoreOf 2 L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨⟨u, v⟩, rfl⟩ := C.surj y hy
      have h1 := C.comm_uni hβ hβ' u v
      calc C.ι (u, v) * ⁅g, h⁆ = ⁅g, h⁆ * C.ι (u, v) * ⁅g, h⁆⁻¹ * ⁅g, h⁆ := by rw [h1]
        _ = ⁅g, h⁆ * C.ι (u, v) := by group
    have h1 := hCT (Subgroup.mem_inf.mpr ⟨hc, by rw [hO2]; exact hcC⟩)
    rwa [hO2] at h1
  have hD4 : derivedSeriesOf X 4 = ⊥ := by
    rw [derivedSeriesOf_succ, eq_bot_iff]
    refine (Subgroup.commutator_mono hD3 hD3).trans (le_of_eq ?_)
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val
      ((l3facts_two_F4 h527 hyp hty hf).1.1.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩)
  exact (isSolvable_iff_exists_derivedSeriesOf_eq_bot X).mpr ⟨4, hD4⟩

theorem perfectCore_M1_F4 (h527 : Stmt5_2_7_F4) (h531 : Stmt5_3_1_F4)
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hty : IsOfLieType52 M L H B D T .PSL 3 f)
    (hf : 2 ≤ f) : perfectCore (sec53M1 L) = L := by
  have hpar : IsSec53Param .PSL 3 f := ⟨hf, Or.inl ⟨rfl, rfl⟩⟩
  obtain ⟨-, -, -, h4, -⟩ := h531 G T M L V H B D L₂ n .PSL 3 f hyp hty hpar
  obtain ⟨F, _, _, _, -, ⟨Mo⟩⟩ := exists_l3Model hty hf
  apply le_antisymm
  · exact perfectCore_le_of_sup_solvable (Subgroup.le_normalizer)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl)
      h4.symm (isSolvable_M12_F4 h527 h531 hyp hty hf)
  · calc L = perfectCore (sec53G1 M L H B) := (Mo.perfectCore_G1 hyp).symm
      _ ≤ perfectCore (sec53M1 L) := perfectCore_mono (G1_le_normalizer hyp)

theorem perfectCore_M2_F4 (h527 : Stmt5_2_7_F4) (h531 : Stmt5_3_1_F4)
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hty : IsOfLieType52 M L H B D T .PSL 3 f)
    (hf : 2 ≤ f) : perfectCore (sec53M2 H) = oTwoUpper H := by
  have hpar : IsSec53Param .PSL 3 f := ⟨hf, Or.inl ⟨rfl, rfl⟩⟩
  obtain ⟨-, -, -, -, h4⟩ := h531 G T M L V H B D L₂ n .PSL 3 f hyp hty hpar
  obtain ⟨F, _, _, _, -, ⟨Mo⟩⟩ := exists_l3Model hty hf
  apply le_antisymm
  · exact perfectCore_le_of_sup_solvable (Subgroup.le_normalizer)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl)
      h4.symm (isSolvable_M12_F4 h527 h531 hyp hty hf)
  · calc oTwoUpper H = perfectCore (sec53G2 M L H D) := (Mo.perfectCore_G2 hyp hty).symm
      _ ≤ perfectCore (sec53M2 H) := perfectCore_mono (G2_le_normalizer hyp)

theorem pCoreOf_M12_F4 (h527 : Stmt5_2_7_F4) (h531 : Stmt5_3_1_F4)
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hty : IsOfLieType52 M L H B D T .PSL 3 f)
    (hf : 2 ≤ f) : pCoreOf 2 (sec53M12 L H) = sec53S T L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_1_8.toHyp5_0_1
  have hpar : IsSec53Param .PSL 3 f := ⟨hf, Or.inl ⟨rfl, rfl⟩⟩
  obtain ⟨-, -, ⟨hN, -, -⟩, -⟩ := h531 G T M L V H B D L₂ n .PSL 3 f hyp hty hpar
  obtain ⟨F, _, _, _, -, ⟨C⟩⟩ := exists_v1Coords_F4 h527 hyp hty hf
  have hLG : L ≤ sec53G1 M L H B := le_sup_left.trans le_sup_left
  have hsup := sup_sec53_F4 h527 hyp hty hf
  have hV₂L : pCoreOf 2 (oTwoUpper H) ≤ L :=
    (le_sup_right.trans hsup.le).trans (inf_le_right : sec53S T L ≤ L)
  set X := sec53M12 L H with hX
  have hXL : ∀ g ∈ X, g ∈ Subgroup.normalizer (L : Set G) := fun g hg =>
    (Subgroup.mem_inf.mp hg).1
  have hXV : ∀ g ∈ X, g ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) := fun g hg =>
    normalizer_le_normalizer_pCoreOf 2 L (hXL g hg)
  have hTX : T ≤ X := by
    rw [← hN]
    exact le_normalizer_sec53S hyp
  apply le_antisymm
  · intro x hx
    have hxT : x ∈ T :=
      EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_isSylowTwo h.sylow hTX) hx
    have hxX : x ∈ X := pCoreOf_le 2 X hx
    obtain ⟨τ, σ, hτ, hσ⟩ := C.exists_semilinear hLG hV₂L (hXL x hxX) (hXV x hxX)
    have hZx : (τ (0, 1)).1 = 0 := by
      have hxN : x ∈ Subgroup.normalizer (sec53S T L : Set G) := by rw [hN]; exact hxX
      have h1 : C.ι (τ (0, 1)) ∈ sec53ZS T L := by
        rw [hτ]
        exact conj_mem_centerOf hxN ((C.center _).mpr ⟨1, rfl⟩)
      obtain ⟨c, hc⟩ := (C.center _).mp h1
      rw [C.inj hc]
    have hPX : ∀ g ∈ X, ∀ y ∈ pCoreOf 2 X, g * y * g⁻¹ ∈ pCoreOf 2 X := fun g hg y hy =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 X hg) y).mp hy

    have hσid : ∀ t : F, σ t = t := by
      intro t
      by_cases ht : t = 0
      · rw [ht, map_zero]
      obtain ⟨d, hdX, hd⟩ := exists_diag_mem_F4 h527 h531 hyp hty hf C ht
      have hcomm : x * d * x⁻¹ * d⁻¹ ∈ pCoreOf 2 X := by
        have h1 := hPX d hdX x⁻¹ (Subgroup.inv_mem _ hx)
        have h2 := (pCoreOf 2 X).mul_mem hx h1
        simpa [mul_assoc] using h2
      obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 X ⟨_, hcomm⟩
      have hk' : (x * d * x⁻¹ * d⁻¹) ^ 2 ^ k = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      exact C.sigma_fix_of_tri (hXV x hxX) (hXV d hdX) hτ hσ hZx ht (inv_ne_zero ht)
        (fun u v => by rw [hd, zero_mul, zero_add]) hk'
    exact mem_S_of_linear'_F4 h527 h531 hyp hty hf C hxT hτ
      (fun c p => by rw [hσ, hσid]) hZx
  · refine le_pCoreOf_of_le_normalizer 2 ?_ (by rw [← hN]) (h.sylow.1.to_le inf_le_left)
    rw [← hN]
    exact Subgroup.le_normalizer

theorem centerOf_L_eq_bot_F4 (h527 : Stmt5_2_7_F4) (h531 : Stmt5_3_1_F4)
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hty : IsOfLieType52 M L H B D T .PSL 3 f)
    (hf : 2 ≤ f) {z : G} (hz : z ∈ centerOf L) : z = 1 := by
  have hpar : IsSec53Param .PSL 3 f := ⟨hf, Or.inl ⟨rfl, rfl⟩⟩
  obtain ⟨-, ⟨hCT, hO2, -, -⟩, -, -⟩ := h531 G T M L V H B D L₂ n .PSL 3 f hyp hty hpar
  obtain ⟨F, _, _, _, -, ⟨C⟩⟩ := exists_v1Coords_F4 h527 hyp hty hf
  have hsup := sup_sec53_F4 h527 hyp hty hf
  have hV₂L : pCoreOf 2 (oTwoUpper H) ≤ L :=
    (le_sup_right.trans hsup.le).trans (inf_le_right : sec53S T L ≤ L)
  obtain ⟨hzL, hzc⟩ := Subgroup.mem_inf.mp hz
  have hzC : z ∈ Subgroup.centralizer (pCoreOf 2 L : Set G) :=
    Subgroup.centralizer_le (show (pCoreOf 2 L : Set G) ⊆ L from pCoreOf_le 2 L) hzc
  have hzV : z ∈ pCoreOf 2 L := by
    have h1 := hCT (Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer hzL, by rw [hO2]; exact hzC⟩)
    rwa [hO2] at h1
  obtain ⟨⟨u, v⟩, rfl⟩ := C.surj z hzV
  have hcomm : ∀ g ∈ L, g * C.ι (u, v) * g⁻¹ = C.ι (u, v) := fun g hg => by
    rw [Subgroup.mem_centralizer_iff.mp hzc g hg]
    group
  have hv : v = 0 := by
    have h1 := hcomm _ (C.xe_mem 1)
    rw [C.xe_act, tvX_apply] at h1
    have h2 := congrArg Prod.fst (C.inj h1)
    simp only [one_mul] at h2
    linear_combination h2
  have hu : u = 0 := by
    have h1 := hcomm _ (hV₂L (C.ye_mem 1))
    rw [C.ye_act, tvY_apply] at h1
    have h2 := congrArg Prod.snd (C.inj h1)
    simp only [one_mul] at h2
    linear_combination h2
  rw [hu, hv]
  have h0 := C.add 0 0
  rw [add_zero] at h0
  exact mul_eq_left.mp h0.symm

theorem centerOf_K_eq_bot_F4 (h527 : Stmt5_2_7_F4) (h531 : Stmt5_3_1_F4)
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hty : IsOfLieType52 M L H B D T .PSL 3 f)
    (hf : 2 ≤ f) {z : G} (hz : z ∈ centerOf (oTwoUpper H)) : z = 1 := by
  have hpar : IsSec53Param .PSL 3 f := ⟨hf, Or.inl ⟨rfl, rfl⟩⟩
  obtain ⟨-, ⟨-, -, hCT, hO2⟩, -, -⟩ := h531 G T M L V H B D L₂ n .PSL 3 f hyp hty hpar
  obtain ⟨F, _, _, _, -, -, C, -, -, -⟩ := exists_sCoords_F4 h527 hyp hty hf
  have hsup := sup_sec53_F4 h527 hyp hty hf
  have hV₁K : pCoreOf 2 L ≤ oTwoUpper H :=
    (le_sup_left.trans hsup.le).trans (sec53S_le_K_F4 h527 hyp)
  obtain ⟨hzK, hzc⟩ := Subgroup.mem_inf.mp hz
  have hzC : z ∈ Subgroup.centralizer (pCoreOf 2 (oTwoUpper H) : Set G) :=
    Subgroup.centralizer_le
      (show (pCoreOf 2 (oTwoUpper H) : Set G) ⊆ oTwoUpper H from pCoreOf_le 2 _) hzc
  have hzV : z ∈ pCoreOf 2 (oTwoUpper H) := by
    have h1 := hCT (Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer hzK, by rw [hO2]; exact hzC⟩)
    rwa [hO2] at h1
  obtain ⟨⟨u, v⟩, rfl⟩ := C.surj z hzV
  have hcomm : ∀ g ∈ oTwoUpper H, g * C.ι (u, v) * g⁻¹ = C.ι (u, v) := fun g hg => by
    rw [Subgroup.mem_centralizer_iff.mp hzc g hg]
    group
  have hv : v = 0 := by
    have h1 := hcomm _ (C.xe_mem 1)
    rw [C.xe_act, tvX_apply] at h1
    have h2 := congrArg Prod.fst (C.inj h1)
    simp only [one_mul] at h2
    linear_combination h2
  have hu : u = 0 := by
    have h1 := hcomm _ (hV₁K (C.ye_mem 1))
    rw [C.ye_act, tvY_apply] at h1
    have h2 := congrArg Prod.snd (C.inj h1)
    simp only [one_mul] at h2
    linear_combination h2
  rw [hu, hv]
  have h0 := C.add 0 0
  rw [add_zero] at h0
  exact mul_eq_left.mp h0.symm

theorem stmt5_3_3_factsAt_PSL_F4 (h527 : Stmt5_2_7_F4) (h531 : Stmt5_3_1_F4) :
    Stmt5_3_3_factsAt_F4 .PSL 3 := by
  intro G _ _ T M L V H B D L₂ n f hyp hty hpar
  have hf := hpar.1
  refine ⟨⟨perfectCore_M1_F4 h527 h531 hyp hty hf, perfectCore_M2_F4 h527 h531 hyp hty hf,
    pCoreOf_M12_F4 h527 h531 hyp hty hf⟩, fun z hz hz1 => ?_, fun z hz hz1 => ?_, fun h => ?_⟩
  · exact absurd (centerOf_L_eq_bot_F4 h527 h531 hyp hty hf hz) hz1
  · exact absurd (centerOf_K_eq_bot_F4 h527 h531 hyp hty hf hz) hz1
  · exact absurd h (by decide)

end L3

theorem stmt5_3_3_facts_of_F4 (h527 : Stmt5_2_7_F4) (h531 : Stmt5_3_1_F4)
    (hSp : Stmt5_3_3_factsAt_F4 .PSp 2) (hG2 : Stmt5_3_3_factsAt_F4 .G2 0)
    (h3D4 : Stmt5_3_3_factsAt_F4 .trialityD4 0) (h2F4 : Stmt5_3_3_factsAt_F4 .twistedF4 0)
    (hU4 : Stmt5_3_3_factsAt_F4 .PSU 4) (hU5 : Stmt5_3_3_factsAt_F4 .PSU 5) : Stmt5_3_3_facts_F4 :=
  stmt5_3_3_facts_of_at_F4 (stmt5_3_3_factsAt_PSL_F4 h527 h531) hSp hG2 h3D4 h2F4 hU4 hU5

end CFSG.Quasithin.H13.Sec53L3
