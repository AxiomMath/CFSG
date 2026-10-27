module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneLambdaZeroQuot
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUSp6LagrangianStatements
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBISp6ActionParameters

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

theorem symThreeSquare_one_single : symThreeSquare 1 ![1, 0, 0] = symE₁₁ := by
  apply Subtype.ext
  change (1 : ZMod 2) • vecMulVec ![1, 0, 0] ![1, 0, 0] = jMat 1 0 0
  rw [one_smul]
  decide

theorem standard_binary_symplectic_six_lambda_zero_epsilon_one_common_normalization
    {G : Type} [Group G] [Finite G] (hG : CFSG.oddCore G = ⊥) {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L) (hLn : ¬ L.Normal)
    (hZ : center L = ⊥) (hmodel : CFSG.Blueprint.LieModel L .PSp 3 2 1)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G)))) {z : G}
    (hzT : z ∈ (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype)
    (hz : orderOf z = 2) (hH : CFSG.oddCore (centralizer ({z} : Set G)) = ⊥)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {b : BilinForm (ZMod 2) V} (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hV : finrank (ZMod 2) V = 6) (φ : L ≃* bilinIsometryGroup b)
    (e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V) (he : IsSymplecticBasis b e)
    (hfull : conjClass (normalizer ((pullSub φ (pointwiseStabilizer b (lagrangianOf e)) ⊔
        zpowers z : Subgroup G) : Set G)) z =
      z • (pullSub φ (pointwiseStabilizer b (lagrangianOf e)) : Set G)) :
    let u := e (Sum.inl 0)
    let f := e (Sum.inr 0)
    let E := pairOrth b u f
    let n : E → ZMod 2 → bilinIsometryGroup b := fun w c => pointElt hb (mem_pairOrth_left w.2) c
    let τ : ↥(binarySymMatrices 3) → G := fun B => tauHom φ he (Multiplicative.ofAdd B)
    let A₂ := pullSub φ (pointwiseStabilizer b (lagrangianOf e))
    let R₂ := A₂ ⊔ zpowers z
    let N₂ := normalizer (R₂ : Set G)
    let D₂ := CFSG.Assembly.pCoreOf 2 N₂
    let I₂ : Set G := {x | ∃ B : ↥(binarySymMatrices 3), symThreeDiag (B : M₃) = 0 ∧ τ B = x}
    let F₂ : Set G := {d | d ∈ D₂ ∧ z⁻¹ * (d⁻¹ * z * d) ∈ I₂}
    let A₁ := pullSub φ (pointRadical b hb u f)
    let b₁ : G := ((φ.symm (n 0 1) : L) : G)
    let I₁ := zpowers b₁
    let B₁ := A₁ ⊔ zpowers z
    let N₁ := normalizer (B₁ : Set G)
    let D₁ := CFSG.Assembly.pCoreOf 2 N₁
    let F₁ : Set G := {d | d ∈ D₁ ∧ z⁻¹ * (d⁻¹ * z * d) ∈ I₁}
    let J := A₁ ⊓ A₂
    let J₀ : Set G := (A₁ : Set G) ∩ I₂
    let E₂ := sp6E₂ φ he z
    let C₂ := D₂ ⊓ centralizer (E₂ : Set G)
    (∀ a ∈ A₁, ∀ d ∈ D₁, a * d = d * a) →
    (∀ c ∈ C₂, ∀ B : ↥(binarySymMatrices 3), z⁻¹ * (c⁻¹ * z * c) = τ B →
      c ^ 2 = τ (symThreeSquare 1 (symThreeDiag (B : M₃)))) →
    ∃ C₁ : Subgroup G,
      let E₁ : Set G := (C₁ : Set G) ∩ F₁
      let K₀ := C₁ ⊓ C₂
      let M : Set G := (C₁ : Set G) ∩ E₂
      let P₁ := A₁ ⊔ K₀
      let P₂ := A₂ ⊔ K₀
      let A := A₁ ⊔ A₂ ⊔ K₀
      let B := zpowers z ⊔ A
      (C₁ ≤ D₁ ∧ (∀ m ∈ N₁, ∀ c ∈ C₁, m * c * m⁻¹ ∈ C₁) ∧ Nat.card C₁ = 1024 ∧
        zpowers z ⊔ C₁ = D₁ ∧ C₁ ⊓ B₁ = A₁ ∧ ⁅C₁, C₁⁆ = I₁ ∧
        closure {x | ∃ y ∈ C₁, y ^ 2 = x} = I₁ ∧ ((center C₁).map C₁.subtype : Set G) = E₁ ∧
        Nonempty (↥(center C₁) ≃* Multiplicative (ZMod 4 × (Fin 4 → ZMod 2)))) ∧
      ((∀ m ∈ N₂, ∀ x ∈ E₂, m * x * m⁻¹ ∈ E₂) ∧ (E₂ : Set G) ⊆ F₂ ∧
        IsElementaryAbelian 2 E₂ ∧ Nat.card E₂ = 512 ∧
        (∀ E' : Subgroup G, (E' : Set G) ⊆ F₂ → IsMulCommutative E' → Nat.card E' = 512 →
          E' = E₂) ∧
        (center C₂).map C₂.subtype = E₂ ∧ (∀ c ∈ C₂, c ^ 2 = 1 ↔ c ∈ E₂)) ∧
      (K₀ = C₁ ⊓ D₂ ∧ Nat.card K₀ = 64 ∧ Nat.card ↥M = 32 ∧ Nat.card J = 8 ∧
        Nat.card ↥J₀ = 4 ∧ conjClass K₀ z = z • (J : Set G) ∧ ⁅K₀, A₂⁆ = ⊥) ∧
      (∀ x ∈ P₁, ∀ y ∈ P₁, x * y = y * x) ∧ Nat.card P₁ = 2 ^ 8 ∧
      (∀ x ∈ P₂, ∀ y ∈ P₂, x * y = y * x) ∧ Nat.card P₂ = 2 ^ 9 ∧
      Nat.card A = 2 ^ 11 ∧ Nat.card B = 2 ^ 12 ∧
      D₂ ≤ normalizer (B : Set G) ∧ D₂ ≤ normalizer (P₁ : Set G) ∧
      D₂ ≤ normalizer (P₂ : Set G) ∧ D₂ ≤ normalizer (A : Set G) ∧
      D₂ ≤ centralizer ({b₁} : Set G) ∧
      (I₁ ≤ P₂ ∧ P₂ ≤ B ∧ (∀ x ∈ P₂, x ^ 2 ∈ I₁) ∧
        ∀ Y : Subgroup G, I₁ ≤ Y → Y ≤ B → Nat.card Y = 2 ^ 9 → (∀ y ∈ Y, y ^ 2 ∈ I₁) →
          (∀ y ∈ Y, ∀ y' ∈ Y, y⁻¹ * y'⁻¹ * y * y' ∈ I₁) → Y = P₂) ∧
      (I₁ ≤ P₁ ∧ P₁ ≤ B ∧ (∀ x ∈ P₁, x ^ 2 ∈ I₁) ∧ Nat.card (P₁ ⊔ P₂ : Subgroup G) = 2 ^ 11 ∧
        ∀ Y : Subgroup G, I₁ ≤ Y → Y ≤ B → Nat.card Y = 2 ^ 8 → (∀ y ∈ Y, y ^ 2 ∈ I₁) →
          (∀ y ∈ Y, ∀ y' ∈ Y, y⁻¹ * y'⁻¹ * y * y' ∈ I₁) →
          Nat.card (Y ⊔ P₂ : Subgroup G) = 2 ^ 11 → Y = P₁) ∧
      (I₁.subgroupOf B).Normal ∧ ∀ [(I₁.subgroupOf B).Normal],
        (∀ Y : Subgroup (↥B ⧸ I₁.subgroupOf B),
          (IsElementaryAbelian 2 Y ∧ Nat.card Y = 256) ↔
            Y = (P₂.subgroupOf B).map (QuotientGroup.mk' (I₁.subgroupOf B))) ∧
        ∀ Y : Subgroup (↥B ⧸ I₁.subgroupOf B),
          (IsElementaryAbelian 2 Y ∧ Nat.card Y = 128 ∧
            Nat.card ((Y : Set (↥B ⧸ I₁.subgroupOf B)) *
              ((P₂.subgroupOf B).map (QuotientGroup.mk' (I₁.subgroupOf B)) :
                Set (↥B ⧸ I₁.subgroupOf B)) : Set (↥B ⧸ I₁.subgroupOf B)) = 1024) ↔
            Y = (P₁.subgroupOf B).map (QuotientGroup.mk' (I₁.subgroupOf B)) := by
  obtain ⟨-, hzC, hsup, hinf, hrest⟩ :=
    standard_binary_symplectic_six_fusion_orbit_lengths hG hL hLn hZ hmodel T hT hzT hz hH
  obtain ⟨-, hW⟩ := hrest hb hnd hV φ
  obtain ⟨-, -, -, -, -, -, -, -, -, hker, -, -, -, ⟨σ, -, hσker, hσcol, hσ⟩, -⟩ :=
    hW (isTotallyIsotropic_lagrangianOf he) finrank_lagrangianOf e he rfl
  obtain ⟨κ, D₂, F₂', ν₂', hD₂, hFD₂, hD₂N, hRF₂, hD₂n, -, -, -, hν₂z, hν₂eq, hν₂surj, hact₂,
    -, -, hD₂H, -, -, -⟩ :=
    degree64_lagrangian_two_group φ he hzC hz hinf hker σ hσ hfull
  have hRD₂ := hRF₂.trans hFD₂
  obtain ⟨-, hfull₁⟩ := degree64_point_fusion_of_lagrangian he hb hnd φ hzC hsup hinf hz hV hD₂N
    hD₂n hν₂z hν₂eq hν₂surj hact₂
  obtain ⟨lam₀, D₁, F₁, ν₁, hD₁, hFD₁, hD₁N, hBF₁, hD₁n, -, -, -, -, -, -, hν₁z, -, -,
    hact₁, -, hprod₁, hD₁H, -, hb₁c, -, -, -, -, -, -, ⟨hγD₁, -, hF₁mem, -⟩, -, -⟩ :=
    degree64_point_two_group he hb hnd φ hzC hsup hinf hz hfull₁
  have hBD₁ := hBF₁.trans hFD₁
  have h3 :=
    standard_binary_symplectic_six_degree64_central_point_action_excludes_noncentral_lagrangian
      hG hL hLn hZ hmodel T hT hzT hz hH hb hnd hV φ e he hfull
  subst hD₂ hD₁
  obtain ⟨-, -, -, -, htrans⟩ := h3
  set D₁ := CFSG.Assembly.pCoreOf 2 (normalizer ((ptSub φ z hb e : Subgroup G) : Set G))
    with hD₁def
  set D₂ := CFSG.Assembly.pCoreOf 2 (normalizer ((radSub φ z e : Subgroup G) : Set G))
    with hD₂def
  have hpure : ∀ d ∈ D₂, ∀ (B : ↥(binarySymMatrices 3)) (ε : ZMod 2),
      d⁻¹ * radHom φ he hzC hz (Multiplicative.ofAdd (B, ε)) * d =
        radHom φ he hzC hz (Multiplicative.ofAdd (B + ε • ν₂' d, ε)) :=
    fun d hd B ε => htrans d hd (ν₂' d) B ε (hν₂z d hd)
  have hD₂A : ∀ d ∈ D₂, ∀ a ∈ pullSub φ (pointwiseStabilizer b (lagrangianOf e)),
      d * a = a * d := by
    intro d hd a ha
    obtain ⟨B, rfl⟩ := (mem_pullSub_iff φ he).1 ha
    have h := hpure d hd (Multiplicative.toAdd B) 0
    rw [zero_smul, add_zero, radHom_tau, ofAdd_toAdd] at h
    exact comm_of_inv_mul_mul_eq h
  have hKz : ∀ j ∈ pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0))) ⊓
      pullSub φ (pointwiseStabilizer b (lagrangianOf e)), ∃ k ∈ D₁ ⊓ D₂,
        k⁻¹ * z * k = z * j := fun j hj =>
    exists_mem_inf_conj_eq he hb hnd φ hzC hsup hinf hz hD₂N hD₂n hν₂z hν₂eq hν₂surj hact₂ hRD₂
      hD₁n hBD₁ hν₁z hact₁ hprod₁ hj
  have hF₁ : ∀ d : G, d ∈ F₁ ↔ d ∈ D₁ ∧ z⁻¹ * (d⁻¹ * z * d) ∈ zpowers (ptB₁ he hb φ hzC hz) :=
    fun d => ⟨fun h => ⟨hFD₁ h, (hF₁mem d (hFD₁ h)).2 h⟩, fun h => (hF₁mem d h.1).1 h.2⟩
  have hb₁eq := ptB₁_eq he hb φ hzC hz
  intro u f E n τ A₂ R₂ N₂ D₂' I₂ F₂s A₁ b₁ I₁ B₁ N₁ D₁' F₁s J J₀ E₂ C₂ hA₁cen hε
  have hb₁' : ptB₁ he hb φ hzC hz = b₁ := hb₁eq
  obtain ⟨κ₂, lam, hκ₂, hlam⟩ := SteinbergBI.exists_action_parameters hG hL hLn hZ hmodel T hT
    hzT hz hH hb hnd hV φ e he hfull
  obtain ⟨-, C₁, E₂', h4'⟩ := standard_binary_symplectic_six_degree64_lagrangian_subgroup_completion
    hG hL hLn hZ hmodel T hT hzT hz hH hb hnd hV φ e he hfull κ₂ lam hκ₂ hlam
  obtain ⟨hC₁D, hC₁n, hC₁c, hC₁z, hC₁B, hcl, -, hJcard, hJ₀card, -, -, hK₀card, hMcard,
    hK₀c, hKconj, hK₀A, hE₂n, hE₂F, hE₂c, hE₂card, hE₂uniq, hE₂sq, -, -, -, hC₂n, -,
    hDzC, hC₂R, -, -, -, hC₁C₂, hC₁E₂, hPc, hPcard, ν, ε, hνz, hνmul, -, hνk, -, hδs, -, -,
    hsqf, hε0, hε1, hlam0, hlam1⟩ := h4'
  have hspec := Classical.epsilon_spec (p := fun E : Subgroup G =>
    (E : Set G) ⊆ sp6F₂ φ he z ∧ IsMulCommutative E ∧ Nat.card E = 512) ⟨E₂', hE₂F, hE₂c, hE₂card⟩
  have hE : E₂' = sp6E₂ φ he z := (hE₂uniq _ hspec.1 hspec.2.1 hspec.2.2).symm
  subst hE
  have hAC₁ : A₁ ≤ C₁ := ptA_le_of_inf_eq hb φ hC₁B
  have hC₂D : C₂ ≤ D₂ := inf_le_left
  have hb₁ne : ptB₁ he hb φ hzC hz ≠ 1 := fun h => by
    have h2 := orderOf_ptB₁ he hb φ hzC hz
    rw [h, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hlam0' : lam = 0 := by
    rcases zmod_two_eq_zero_or_eq_one lam with h | h
    · exact h
    · exfalso
      obtain ⟨-, -, hZc, -⟩ := hlam1 h
      have hle : Nat.card A₁ ≤ Nat.card (center C₁) := by
        refine Nat.card_le_card_of_injective (fun a => ⟨⟨(a : G), hAC₁ a.2⟩, ?_⟩) ?_
        · rw [mem_center_iff]
          intro g
          apply Subtype.ext
          exact (hA₁cen _ a.2 _ (hC₁D g.2)).symm
        · intro a a' h
          exact Subtype.ext (congrArg (fun x : center C₁ => ((x : C₁) : G)) h)
      rw [(ptA_facts he hb hnd φ).2.2.1, hZc] at hle
      norm_num at hle
  have hε1' : ε = 1 := by
    rcases zmod_two_eq_zero_or_eq_one ε with h | h
    · exfalso
      obtain ⟨hsq1, -, -⟩ := hε0 h
      obtain ⟨c, hc, hcw⟩ := hδs ![1, 0, 0]
      have h1 : c ^ 2 = tauHom φ he (Multiplicative.ofAdd
          (symThreeSquare 1 (symThreeDiag (ν c : M₃)))) := hε c hc (ν c) (hνz c (hC₂D hc))
      rw [hcw, symThreeSquare_one_single, ← ptB₁_eq_tauHom he hb φ hzC hz, hsq1 c hc] at h1
      exact hb₁ne h1.symm
    · exact h
  obtain ⟨-, -, -, hcenC₂, hΩ₁⟩ := hε1 hε1'
  obtain ⟨-, -, -, hlam0e, -⟩ := hlam0 hlam0'
  obtain ⟨hcomm₁, hclos₁, hZ₁, hZiso⟩ := hlam0e hε1'
  have hν₂z'' : ∀ d ∈ D₂, d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (ν d, 1)) := by
    intro d hd
    rw [radHom_one_eq φ he hzC hz]
    have h := hνz d hd
    calc d⁻¹ * z * d = z * (z⁻¹ * (d⁻¹ * z * d)) := by group
      _ = z * tauHom φ he (Multiplicative.ofAdd (ν d)) := by rw [h]
  have hC₁sq' : ∀ c ∈ C₁, c ^ 2 ∈ zpowers (ptB₁ he hb φ hzC hz) := fun c hc => by
    rw [hb₁']
    exact hcl (Subgroup.subset_closure ⟨c, hc, rfl⟩)
  have hC₂comm : ∀ c ∈ C₂, ∀ d ∈ C₂, c⁻¹ * d⁻¹ * c * d ∈ A₂ := fun c hc d hd => by
    rw [(hsqf c hc d hd).2]
    change tauHom φ he _ * z ^ (0 : ZMod 2).val ∈ A₂
    rw [ZMod.val_zero, pow_zero, mul_one]
    exact (mem_pullSub_iff φ he).2 ⟨_, rfl⟩
  have key := epsOne_lambda_zero_block he hb hnd φ hzC hsup hinf hz σ hσ hσcol hσker
    (D₁ := D₁) (C₁ := C₁) (D₂ := D₂) (C₂ := C₂) (F₁ := F₁) (ν₂ := ν) hD₁N hD₁n hD₁H hγD₁ hb₁c
    hC₁D hC₁n hC₁z hC₁B hC₁c hC₁sq' hA₁cen hD₂n hRD₂ hD₂H hν₂z'' hKz hD₂A hC₂D hC₂n hC₂R
    hC₁C₂ hDzC hνmul hνk hC₂comm hK₀c hK₀card hKconj hK₀A hPc hPcard hF₁
  rw [← hC₁C₂, hb₁'] at key
  obtain ⟨hP₁c, hP₁card, hP₂c, hP₂card, hAcard, hBcard, hD₂NB, hD₂NP₁, hD₂NP₂, hD₂NA, hD₂b₁,
    hIP₁, hIP₂, hP₁B, hP₂B, hAeq, hBNP₂, hP₁sq, hP₂sq, hIcen, huniq₂, huniq₁⟩ := key
  have hI2 : Nat.card I₁ = 2 := by
    rw [Nat.card_zpowers, ← hb₁', orderOf_ptB₁ he hb φ hzC hz]
  have hIB := hIP₂.trans hP₂B
  have hInorm : (I₁.subgroupOf (zpowers z ⊔ (A₁ ⊔ A₂ ⊔ C₁ ⊓ C₂))).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [mem_subgroupOf] at hx ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hIcen _ hx _ g.2, mul_inv_cancel_right]
    exact hx
  refine ⟨C₁, ⟨hC₁D, hC₁n, hC₁c, hC₁z, hC₁B, hcomm₁, hclos₁, hZ₁, hZiso⟩,
    ⟨hE₂n, hE₂F, elemAbelian_of_sq_eq_one hE₂sq, hE₂card, hE₂uniq, hcenC₂, hΩ₁⟩,
    ⟨hC₁C₂, by rw [hC₁C₂]; exact hK₀card, by rw [hC₁E₂]; exact hMcard, hJcard, hJ₀card,
      by rw [hC₁C₂]; exact hKconj, by rw [hC₁C₂]; exact hK₀A⟩,
    hP₁c, hP₁card, hP₂c, hP₂card, hAcard, hBcard, hD₂NB, hD₂NP₁, hD₂NP₂, hD₂NA, hD₂b₁,
    ⟨hIP₂, hP₂B, hP₂sq, fun Y _ hYB hYc hYsq _ => huniq₂ Y hYB hYc hYsq⟩,
    ⟨hIP₁, hP₁B, hP₁sq, by rw [hAeq]; exact hAcard,
      fun Y _ hYB hYc hYsq _ hYP => huniq₁ Y hYB hYc hYsq hYP⟩, hInorm, ?_⟩
  intro _
  refine ⟨fun Yb => ?_, fun Yb => ?_⟩
  · have h := quotB_unique_iff hIB hI2 hIP₂ hP₂B (m := 8) hP₂card hP₂sq hP₂c
      (fun Y _ hYB hYc hYsq _ => huniq₂ Y hYB hYc hYsq) Yb
    rwa [show (2 : ℕ) ^ 8 = 256 by norm_num] at h
  · have h := quotB_unique_prod_iff hIB hI2 hIP₁ hP₁B hP₂B hBNP₂ (m := 7) (k := 10) hP₁card hP₁sq
      hP₁c (by rw [hAeq]; exact hAcard)
      (fun Y _ hYB hYc hYsq _ hYP => huniq₁ Y hYB hYc hYsq hYP) Yb
    rwa [show (2 : ℕ) ^ 7 = 128 by norm_num, show (2 : ℕ) ^ 10 = 1024 by norm_num] at h

theorem standard_binary_symplectic_six_lambda_zero_epsilon_one_degree64_exclusion
    {G : Type} [Group G] [Finite G] (hG : CFSG.oddCore G = ⊥) {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L) (hLn : ¬ L.Normal)
    (hZ : center L = ⊥) (hmodel : CFSG.Blueprint.LieModel L .PSp 3 2 1)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G)))) {z : G}
    (hzT : z ∈ (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype)
    (hz : orderOf z = 2) (hH : CFSG.oddCore (centralizer ({z} : Set G)) = ⊥)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {b : BilinForm (ZMod 2) V} (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hV : finrank (ZMod 2) V = 6) (φ : L ≃* bilinIsometryGroup b)
    (e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V) (he : IsSymplecticBasis b e)
    (hfull : conjClass (normalizer ((pullSub φ (pointwiseStabilizer b (lagrangianOf e)) ⊔
        zpowers z : Subgroup G) : Set G)) z =
      z • (pullSub φ (pointwiseStabilizer b (lagrangianOf e)) : Set G)) :
    let u := e (Sum.inl 0)
    let f := e (Sum.inr 0)
    let τ : ↥(binarySymMatrices 3) → G := fun B => tauHom φ he (Multiplicative.ofAdd B)
    let A₂ := pullSub φ (pointwiseStabilizer b (lagrangianOf e))
    let R₂ := A₂ ⊔ zpowers z
    let N₂ := normalizer (R₂ : Set G)
    let D₂ := CFSG.Assembly.pCoreOf 2 N₂
    let A₁ := pullSub φ (pointRadical b hb u f)
    let B₁ := A₁ ⊔ zpowers z
    let N₁ := normalizer (B₁ : Set G)
    let D₁ := CFSG.Assembly.pCoreOf 2 N₁
    let E₂ := sp6E₂ φ he z
    let C₂ := D₂ ⊓ centralizer (E₂ : Set G)
    (∀ a ∈ A₁, ∀ d ∈ D₁, a * d = d * a) →
    (∀ c ∈ C₂, ∀ B : ↥(binarySymMatrices 3), z⁻¹ * (c⁻¹ * z * c) = τ B →
      c ^ 2 = τ (symThreeSquare 1 (symThreeDiag (B : M₃)))) →
    False := by
  intro u f τ A₂ R₂ N₂ D₂' A₁ B₁ N₁ D₁' E₂ C₂ hA₁cen hε
  obtain ⟨C₁, ⟨hC₁D, -, -, -, hC₁B, -⟩, -, ⟨hK₀D, -, -, -, -, hKconj, hK₀A⟩, -, -, -, -, -, -, -,
    hD₂P₁, -⟩ :=
    standard_binary_symplectic_six_lambda_zero_epsilon_one_common_normalization hG hL hLn hZ
      hmodel T hT hzT hz hH hb hnd hV φ e he hfull hA₁cen hε
  obtain ⟨-, hzC, hsup, hinf, hrest⟩ :=
    standard_binary_symplectic_six_fusion_orbit_lengths hG hL hLn hZ hmodel T hT hzT hz hH
  obtain ⟨-, hW⟩ := hrest hb hnd hV φ
  obtain ⟨-, -, -, -, -, -, -, -, -, hker, -, -, -, ⟨σ, -, -, hσcol, hσ⟩, -⟩ :=
    hW (isTotallyIsotropic_lagrangianOf he) finrank_lagrangianOf e he rfl
  obtain ⟨κ, D₂, F₂', ν₂', hD₂, hFD₂, hD₂N, hRF₂, hD₂n, -, -, -, hν₂z, hν₂eq, hν₂surj, hact₂,
    -, -, hD₂H, -, -, -⟩ :=
    degree64_lagrangian_two_group φ he hzC hz hinf hker σ hσ hfull
  have hRD₂ := hRF₂.trans hFD₂
  obtain ⟨-, hfull₁⟩ := degree64_point_fusion_of_lagrangian he hb hnd φ hzC hsup hinf hz hV hD₂N
    hD₂n hν₂z hν₂eq hν₂surj hact₂
  obtain ⟨lam₀, D₁, F₁, ν₁, hD₁, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hD₁H, -⟩ :=
    degree64_point_two_group he hb hnd φ hzC hsup hinf hz hfull₁
  subst hD₂ hD₁
  have hC₁C₂ : C₁ ⊓ C₂ = C₁ ⊓ D₂' := hK₀D
  rw [hC₁C₂] at hKconj hK₀A hD₂P₁
  obtain ⟨hexp, a, ha, p, hp, hcomm, hp2⟩ := epsOne_lambda_zero_kill he hb hnd φ hzC hsup hinf hz
    σ hσ hσcol (D₁ := D₁') (C₁ := C₁) (D₂ := D₂') (C₂ := C₂) (ν₂ := ν₂') hD₁H hC₁D hC₁B hA₁cen
    hD₂H hRD₂ hν₂z hC₁C₂ hν₂surj hKconj hK₀A hD₂P₁ hε
  have h1 := hexp a ha p hp hcomm
  rw [hp2] at h1
  have h2 := orderOf_ptB₁ he hb φ hzC hz
  rw [h1, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem false_of_lambda_zero
    {G : Type} [Group G] [Finite G] (hG : CFSG.oddCore G = ⊥) {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L) (hLn : ¬ L.Normal)
    (hZ : center L = ⊥) (hmodel : CFSG.Blueprint.LieModel L .PSp 3 2 1)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G)))) {z : G}
    (hzT : z ∈ (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype)
    (hz : orderOf z = 2) (hH : CFSG.oddCore (centralizer ({z} : Set G)) = ⊥)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {b : BilinForm (ZMod 2) V} (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hV : finrank (ZMod 2) V = 6) (φ : L ≃* bilinIsometryGroup b)
    (e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V) (he : IsSymplecticBasis b e)
    (hfull : conjClass (normalizer ((pullSub φ (pointwiseStabilizer b (lagrangianOf e)) ⊔
        zpowers z : Subgroup G) : Set G)) z =
      z • (pullSub φ (pointwiseStabilizer b (lagrangianOf e)) : Set G)) :
    let u := e (Sum.inl 0)
    let f := e (Sum.inr 0)
    let E := pairOrth b u f
    let n : E → ZMod 2 → bilinIsometryGroup b := fun w c => pointElt hb (mem_pairOrth_left w.2) c
    let Q : E → ZMod 2 := fun w =>
      e.repr w (Sum.inl 1) * e.repr w (Sum.inr 1) + e.repr w (Sum.inl 2) * e.repr w (Sum.inr 2)
    let r : E × ZMod 2 := (0, 1)
    let τ : ↥(binarySymMatrices 3) → G := fun B => tauHom φ he (Multiplicative.ofAdd B)
    let θ₂ : ↥(binarySymMatrices 3) × ZMod 2 → G := fun x => τ x.1 * z ^ x.2.val
    let θ₁ : (E × ZMod 2) × ZMod 2 → G := fun x =>
      ((φ.symm (n x.1.1 (x.1.2 + Q x.1.1)) : L) : G) * z ^ x.2.val
    let A₂ := pullSub φ (pointwiseStabilizer b (lagrangianOf e))
    let R₂ := A₂ ⊔ zpowers z
    let N₂ := normalizer (R₂ : Set G)
    let D₂ := CFSG.Assembly.pCoreOf 2 N₂
    let A₁ := pullSub φ (pointRadical b hb u f)
    let B₁ := A₁ ⊔ zpowers z
    let N₁ := normalizer (B₁ : Set G)
    let D₁ := CFSG.Assembly.pCoreOf 2 N₁
    ∀ κ₂ lam : ZMod 2,
      (∀ d ∈ D₂, ∀ (C B : ↥(binarySymMatrices 3)) (ε : ZMod 2), d⁻¹ * z * d = θ₂ (C, 1) →
        d⁻¹ * θ₂ (B, ε) * d = θ₂ (B + κ₂ • symThreePolarSym (symThreeDiag (C : M₃))
          (symThreeDiag (B : M₃)) + ε • C, ε)) →
      (∀ d ∈ D₁, ∀ (a v : E × ZMod 2) (ε : ZMod 2), d⁻¹ * z * d = θ₁ (a, 1) →
        d⁻¹ * θ₁ (v, ε) * d = θ₁ (v + (lam * b (a.1 : V) (v.1 : V)) • r + ε • a, ε)) →
      lam = 0 → ¬ IsElementaryAbelian 2 (sp6C₂ φ he z) → False := by
  intro u f E n Q r τ θ₂ θ₁ A₂ R₂ N₂ D₂ A₁ B₁ N₁ D₁ κ₂ lam h₂ h₁ hlam hC₂
  have hzC : z ∈ centralizer (L : Set G) := map_subtype_le _ hzT
  obtain ⟨-, C₁, E₂', h4'⟩ := standard_binary_symplectic_six_degree64_lagrangian_subgroup_completion
    hG hL hLn hZ hmodel T hT hzT hz hH hb hnd hV φ e he hfull κ₂ lam h₂ h₁
  obtain ⟨hC₁D, -, -, hC₁z, hC₁B, -, -, -, -, -, -, -, -, -, -, -, -, hE₂F, hE₂c, hE₂card,
    hE₂uniq, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ν, ε, hνz, -, -, -, -, -, -, -, hsqf,
    hε0, -, hlam0, -⟩ := h4'
  have hspec := Classical.epsilon_spec (p := fun E : Subgroup G =>
    (E : Set G) ⊆ sp6F₂ φ he z ∧ IsMulCommutative E ∧ Nat.card E = 512) ⟨E₂', hE₂F, hE₂c, hE₂card⟩
  have hE : E₂' = sp6E₂ φ he z := (hE₂uniq _ hspec.1 hspec.2.1 hspec.2.2).symm
  subst hE
  have hε1 : ε = 1 := by
    rcases zmod_two_eq_zero_or_eq_one ε with h | h
    · exact absurd (elemAbelian_of_sq_eq_one (hε0 h).1) hC₂
    · exact h
  have hAC₁ : A₁ ≤ C₁ := ptA_le_of_inf_eq hb φ hC₁B
  obtain ⟨hE₁c, -⟩ := hlam0 hlam
  have hD₁eq : D₁ = zpowers z ⊔ C₁ := hC₁z.symm
  have hle : D₁ ≤ centralizer (A₁ : Set G) := by
    rw [hD₁eq]
    refine sup_le ?_ ?_
    · rw [zpowers_le]
      exact mem_centralizer_iff.2 fun a ha => mul_comm_z hzC (pullSub_le φ _ ha)
    · intro c hc
      refine mem_centralizer_iff.2 fun a ha => hE₁c a ⟨hAC₁ ha, hC₁D (hAC₁ ha), ?_⟩ c hc
      have haz : a⁻¹ * z * a = z := by
        rw [mul_assoc, ← mul_comm_z hzC (pullSub_le φ _ ha), inv_mul_cancel_left]
      change z⁻¹ * (a⁻¹ * z * a) ∈ zpowers _
      rw [haz, inv_mul_cancel]
      exact one_mem _
  have hA₁cen : ∀ a ∈ A₁, ∀ d ∈ D₁, a * d = d * a := fun a ha d hd =>
    mem_centralizer_iff.1 (hle hd) a ha
  have hε : ∀ c ∈ sp6C₂ φ he z, ∀ B : ↥(binarySymMatrices 3), z⁻¹ * (c⁻¹ * z * c) = τ B →
      c ^ 2 = τ (symThreeSquare 1 (symThreeDiag (B : M₃))) := by
    intro c hc B hB
    have hcB : ν c = B := Multiplicative.ofAdd.injective
      (tauHom_injective φ he ((hνz c (mem_inf.1 hc).1).symm.trans hB))
    rw [(hsqf c hc c hc).1, hε1, hcB]
    change tauHom φ he _ * z ^ (0 : ZMod 2).val = _
    rw [ZMod.val_zero, pow_zero, mul_one]
  exact standard_binary_symplectic_six_lambda_zero_epsilon_one_degree64_exclusion hG hL hLn hZ
    hmodel T hT hzT hz hH hb hnd hV φ e he hfull hA₁cen hε

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
