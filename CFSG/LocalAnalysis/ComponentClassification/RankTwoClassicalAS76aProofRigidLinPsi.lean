module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofRigidLinAut
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofRigidQuot
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviProj

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin (perfectCore)
open scoped commutatorElement

section StdMidSL

variable {K : Type} [Field K] {k : ℕ}

theorem card_stdMid (hk : 2 ≤ k) : Fintype.card (StdMid hk) = k := by
  rw [Fintype.card_subtype]
  have h : (Finset.univ.filter fun x : Fin (2 + k) => x ≠ idxU hk ∧ x ≠ idxV hk) =
      Finset.univ \ {idxU hk, idxV hk} := by
    ext x
    simp [not_or]
  rw [h, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
    Finset.card_pair (idxU_ne_idxV hk)]
  omega

theorem isQuasisimple_SL_stdMid (hk : 2 ≤ k) (h4 : ∃ s : Finset K, s.card = 4) :
    CFSG.IsQuasisimple (SpecialLinearGroup (StdMid hk) K) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (slIndexEquiv K (Fintype.equivFinOfCardEq (card_stdMid hk))).symm (isQuasisimple_SL hk h4)

theorem odd_card_center_SL_stdMid [Finite K] (hk : 2 ≤ k) {m : ℕ} (hm : 1 ≤ m)
    (hK : Nat.card K = 2 ^ m) : Odd (Nat.card (center (SpecialLinearGroup (StdMid hk) K))) := by
  rw [card_center_congr (slIndexEquiv K (Fintype.equivFinOfCardEq (card_stdMid hk)))]
  exact odd_card_center_SL hm hK

end StdMidSL

theorem eq_one_of_commutator_eq_self {G M : Type*} [Group G] [CommGroup M] {W : Subgroup G}
    (hW : ⁅W, W⁆ = W) (φ : ↥W →* M) (g : ↥W) : φ g = 1 := by
  have hle : ⁅W, W⁆ ≤ φ.ker.map W.subtype := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨⁅(⟨a, ha⟩ : ↥W), ⟨b, hb⟩⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_commute]
    exact Commute.all _ _
  rw [hW] at hle
  obtain ⟨g', hg', he⟩ := hle g.2
  obtain rfl : g' = g := Subtype.ext he
  exact hg'

theorem eq_one_of_pow_four_eq_one_of_mem_center {H : Type*} [Group H] [Finite H]
    (hodd : Odd (Nat.card (center H))) {z : H} (hz : z ∈ center H) (h4 : z ^ 4 = 1) : z = 1 := by
  have h1 : orderOf (⟨z, hz⟩ : center H) ∣ Nat.card (center H) := orderOf_dvd_natCard _
  have h2 : orderOf (⟨z, hz⟩ : center H) ∣ 2 ^ 2 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using h4))
  obtain ⟨i, -, hio⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  rcases i with _ | i
  · rw [pow_zero, orderOf_eq_one_iff] at hio
    exact congrArg Subtype.val hio
  · exfalso
    have h3 : 2 ∣ Nat.card (center H) := (dvd_pow_self 2 (Nat.succ_ne_zero i)).trans (hio ▸ h1)
    exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr h3)

section SLTwoThree

variable (K : Type) [Field K] [CharP K 2]

@[expose] def slTwoThree : SpecialLinearGroup (Fin 2) K :=
  ⟨!![0, 1; 1, 1], by rw [det_fin_two_of]; simp [CharTwo.neg_eq]⟩

theorem slTwoThree_pow_three : slTwoThree K ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  change !![(0 : K), 1; 1, 1] ^ 3 = 1
  rw [pow_succ, pow_two, mul_fin_two, mul_fin_two, one_fin_two]
  simp [CharTwo.add_self_eq_zero]

theorem slTwoThree_apply_zero_zero : (slTwoThree K : Matrix (Fin 2) (Fin 2) K) 0 0 = 0 := rfl

end SLTwoThree

section Lift

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {k : ℕ}

omit [Finite G] in
theorem perfectCore_inf_le (A : Subgroup G) (p : G) :
    perfectCore (A ⊓ centralizer ({p} : Set G)) ≤ A :=
  (CFSG.Quasithin.perfectCore_le _).trans inf_le_left

theorem theta_mem_map_proj_stdX (hk : 2 ≤ k) {θ : ↥A →* projectiveSL (2 + k) K}
    (hθ : Function.Surjective θ) (hker : θ.ker = center ↥A) (hodd : Odd (Nat.card (center ↥A)))
    {p : G} (hpA : p ∈ A) (hp2 : p ^ 2 = 1)
    (hθp : θ ⟨p, hpA⟩ = proj (2 + k) K (trSL (idxU hk) (idxV hk) (idxU_ne_idxV hk) 1))
    {x : G} (hx : x ∈ perfectCore (A ⊓ centralizer ({p} : Set G))) :
    θ ⟨x, perfectCore_inf_le A p hx⟩ ∈ (stdX K hk).map (proj (2 + k) K) := by
  have hp2' : (⟨p, hpA⟩ : ↥A) ^ 2 = 1 := Subtype.ext (by simpa using hp2)
  rw [perfectCore_inf_centralizer_eq_map ⟨p, hpA⟩] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  have h1 : θ a ∈ perfectCore (centralizer ({θ ⟨p, hpA⟩} : Set (projectiveSL (2 + k) K))) := by
    rw [← map_perfectCore_centralizer_eq_of_quot hθ hker hodd hp2']
    exact ⟨a, ha, rfl⟩
  rw [hθp] at h1
  exact perfectCore_centralizer_proj_le hk h1

theorem exists_linPsi (hk : 2 ≤ k) {θ : ↥A →* projectiveSL (2 + k) K}
    (hθ : Function.Surjective θ) (hker : θ.ker = center ↥A) (hodd : Odd (Nat.card (center ↥A)))
    {p : G} (hpA : p ∈ A) (hp2 : p ^ 2 = 1)
    (hθp : θ ⟨p, hpA⟩ = proj (2 + k) K (trSL (idxU hk) (idxV hk) (idxU_ne_idxV hk) 1)) :
    ∃ (lam : ↥(perfectCore (A ⊓ centralizer ({p} : Set G))) →*
        SpecialLinearGroup (Fin (2 + k)) K)
      (ψ : ↥(perfectCore (A ⊓ centralizer ({p} : Set G))) →* SpecialLinearGroup (StdMid hk) K),
      (∀ x, lam x ∈ stdX K hk) ∧
      (∀ x, proj (2 + k) K (lam x) = θ (Subgroup.inclusion (perfectCore_inf_le A p) x)) ∧
      ∀ x, (ψ x : Matrix (StdMid hk) (StdMid hk) K) =
        stdRhoMat hk (lam x : Matrix (Fin (2 + k)) (Fin (2 + k)) K) := by
  set X := perfectCore (A ⊓ centralizer ({p} : Set G))
  set πX : ↥(stdX K hk) →* projectiveSL (2 + k) K := (proj (2 + k) K).comp (stdX K hk).subtype
  have hinj : Function.Injective πX := fun g h he => Subtype.ext (proj_injOn_stdX hk g.2 h.2 he)
  set θX : ↥X →* projectiveSL (2 + k) K := θ.comp (Subgroup.inclusion (perfectCore_inf_le A p))
  have hmem : ∀ x, θX x ∈ πX.range := by
    intro x
    obtain ⟨g, hg, hgx⟩ := theta_mem_map_proj_stdX hk hθ hker hodd hpA hp2 hθp x.2
    exact ⟨⟨g, hg⟩, hgx⟩
  set e₁ := MonoidHom.ofInjective hinj
  set lam' : ↥X →* ↥(stdX K hk) := e₁.symm.toMonoidHom.comp (θX.codRestrict πX.range hmem)
  have hlam' : ∀ x, πX (lam' x) = θX x := by
    intro x
    rw [← MonoidHom.ofInjective_apply hinj]
    change ((e₁ (e₁.symm ⟨θX x, hmem x⟩) : ↥πX.range) : projectiveSL (2 + k) K) = θX x
    rw [MulEquiv.apply_symm_apply]
  set ρ' : ↥X →* GL (StdMid hk) K := (stdRho K hk).comp lam'
  have hdet : ∀ x, ((ρ' x : GL (StdMid hk) K) : Matrix (StdMid hk) (StdMid hk) K).det = 1 := by
    intro x
    have h := congrArg Units.val (eq_one_of_commutator_eq_self
      (CFSG.Quasithin.perfectCore_perfect _) (Matrix.GeneralLinearGroup.det.comp ρ') x)
    rw [Units.val_one] at h
    exact h
  let ψ : ↥X →* SpecialLinearGroup (StdMid hk) K :=
    { toFun := fun x => ⟨(ρ' x : Matrix (StdMid hk) (StdMid hk) K), hdet x⟩
      map_one' := Subtype.ext (by
        change ((ρ' 1 : GL (StdMid hk) K) : Matrix (StdMid hk) (StdMid hk) K) = 1
        rw [map_one]
        rfl)
      map_mul' := fun x y => Subtype.ext (by
        change ((ρ' (x * y) : GL (StdMid hk) K) : Matrix (StdMid hk) (StdMid hk) K) =
          (ρ' x : Matrix (StdMid hk) (StdMid hk) K) * (ρ' y : Matrix (StdMid hk) (StdMid hk) K)
        rw [map_mul]
        rfl) }
  exact ⟨(stdX K hk).subtype.comp lam', ψ, fun x => (lam' x).2, hlam', fun x => rfl⟩

theorem exists_lam_eq_of_mem_perfectCore (hk : 2 ≤ k) {θ : ↥A →* projectiveSL (2 + k) K}
    (hθ : Function.Surjective θ) (hker : θ.ker = center ↥A) (hodd : Odd (Nat.card (center ↥A)))
    {p : G} (hpA : p ∈ A) (hp2 : p ^ 2 = 1)
    (hθp : θ ⟨p, hpA⟩ = proj (2 + k) K (trSL (idxU hk) (idxV hk) (idxU_ne_idxV hk) 1))
    {lam : ↥(perfectCore (A ⊓ centralizer ({p} : Set G))) →* SpecialLinearGroup (Fin (2 + k)) K}
    (hlamX : ∀ x, lam x ∈ stdX K hk)
    (hlam : ∀ x, proj (2 + k) K (lam x) = θ (Subgroup.inclusion (perfectCore_inf_le A p) x))
    {g : SpecialLinearGroup (Fin (2 + k)) K} (hg : g ∈ perfectCore (stdCen K hk)) :
    ∃ x, lam x = g := by
  have hp2' : (⟨p, hpA⟩ : ↥A) ^ 2 = 1 := Subtype.ext (by simpa using hp2)
  have h1 : proj (2 + k) K g ∈ perfectCore (centralizer ({θ ⟨p, hpA⟩} :
      Set (projectiveSL (2 + k) K))) := by
    rw [hθp, centralizer_proj_stdT_eq hk, ← CFSG.Quasithin.map_perfectCore]
    exact ⟨g, hg, rfl⟩
  rw [← map_perfectCore_centralizer_eq_of_quot hθ hker hodd hp2'] at h1
  obtain ⟨a, ha, hag⟩ := h1
  have hx : (a : G) ∈ perfectCore (A ⊓ centralizer ({p} : Set G)) := by
    rw [perfectCore_inf_centralizer_eq_map ⟨p, hpA⟩]
    exact ⟨a, ha, rfl⟩
  refine ⟨⟨a, hx⟩, proj_injOn_stdX hk (hlamX _) (perfectCore_stdCen_le_stdX hk hg) ?_⟩
  rw [hlam, ← hag]
  rfl

theorem linPsi_surjective (hk : 2 ≤ k) (h4 : 4 ≤ Nat.card K) {θ : ↥A →* projectiveSL (2 + k) K}
    (hθ : Function.Surjective θ) (hker : θ.ker = center ↥A) (hodd : Odd (Nat.card (center ↥A)))
    {p : G} (hpA : p ∈ A) (hp2 : p ^ 2 = 1)
    (hθp : θ ⟨p, hpA⟩ = proj (2 + k) K (trSL (idxU hk) (idxV hk) (idxU_ne_idxV hk) 1))
    {lam : ↥(perfectCore (A ⊓ centralizer ({p} : Set G))) →* SpecialLinearGroup (Fin (2 + k)) K}
    {ψ : ↥(perfectCore (A ⊓ centralizer ({p} : Set G))) →* SpecialLinearGroup (StdMid hk) K}
    (hlamX : ∀ x, lam x ∈ stdX K hk)
    (hlam : ∀ x, proj (2 + k) K (lam x) = θ (Subgroup.inclusion (perfectCore_inf_le A p) x))
    (hψ : ∀ x, (ψ x : Matrix (StdMid hk) (StdMid hk) K) =
      stdRhoMat hk (lam x : Matrix (Fin (2 + k)) (Fin (2 + k)) K)) :
    Function.Surjective ψ := by
  rw [← MonoidHom.range_eq_top, eq_top_iff,
    ← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field,
    Subgroup.closure_le]
  rintro _ ⟨⟨a, b, hab, c⟩, rfl⟩
  have hT := trSL_mem_perfectCore_stdCen hk h4 (fun h => hab (Subtype.ext h)) a.2.2 b.2.1 c
  obtain ⟨x, hx⟩ := exists_lam_eq_of_mem_perfectCore hk hθ hker hodd hpA hp2 hθp hlamX hlam hT
  refine ⟨x, Subtype.ext ?_⟩
  rw [hψ, hx, stdRhoMat_trSL hk hab c]
  rfl

omit [Finite G] [Finite K] in
theorem theta_pow_four_eq_one_of_linPsi (hk : 2 ≤ k) {θ : ↥A →* projectiveSL (2 + k) K}
    {p : G}
    {lam : ↥(perfectCore (A ⊓ centralizer ({p} : Set G))) →* SpecialLinearGroup (Fin (2 + k)) K}
    {ψ : ↥(perfectCore (A ⊓ centralizer ({p} : Set G))) →* SpecialLinearGroup (StdMid hk) K}
    (hlamX : ∀ x, lam x ∈ stdX K hk)
    (hlam : ∀ x, proj (2 + k) K (lam x) = θ (Subgroup.inclusion (perfectCore_inf_le A p) x))
    (hψ : ∀ x, (ψ x : Matrix (StdMid hk) (StdMid hk) K) =
      stdRhoMat hk (lam x : Matrix (Fin (2 + k)) (Fin (2 + k)) K))
    {x : ↥(perfectCore (A ⊓ centralizer ({p} : Set G)))} (hx : ψ x = 1) :
    θ (Subgroup.inclusion (perfectCore_inf_le A p) (x ^ 4)) = 1 := by
  have hρ : stdRhoMat hk (lam x : Matrix (Fin (2 + k)) (Fin (2 + k)) K) = 1 := by
    rw [← hψ, hx]
    rfl
  rw [← hlam, map_pow, stdX_pow_four_eq_one hk (hlamX x) hρ, map_one]

theorem linPsi_eq_one_of_mem_center (hk : 2 ≤ k) (h4 : 4 ≤ Nat.card K)
    {θ : ↥A →* projectiveSL (2 + k) K}
    (hθ : Function.Surjective θ) (hker : θ.ker = center ↥A) (hodd : Odd (Nat.card (center ↥A)))
    {p : G} (hpA : p ∈ A) (hp2 : p ^ 2 = 1)
    (hθp : θ ⟨p, hpA⟩ = proj (2 + k) K (trSL (idxU hk) (idxV hk) (idxU_ne_idxV hk) 1))
    {lam : ↥(perfectCore (A ⊓ centralizer ({p} : Set G))) →* SpecialLinearGroup (Fin (2 + k)) K}
    {ψ : ↥(perfectCore (A ⊓ centralizer ({p} : Set G))) →* SpecialLinearGroup (StdMid hk) K}
    (hlamX : ∀ x, lam x ∈ stdX K hk)
    (hlam : ∀ x, proj (2 + k) K (lam x) = θ (Subgroup.inclusion (perfectCore_inf_le A p) x))
    (hψ : ∀ x, (ψ x : Matrix (StdMid hk) (StdMid hk) K) =
      stdRhoMat hk (lam x : Matrix (Fin (2 + k)) (Fin (2 + k)) K))
    {x : ↥(perfectCore (A ⊓ centralizer ({p} : Set G)))}
    (hx : x ∈ center ↥(perfectCore (A ⊓ centralizer ({p} : Set G)))) : ψ x = 1 := by
  apply Subtype.ext
  rw [hψ]
  refine stdRhoMat_eq_one_of_commute hk (hlamX x) fun a => ?_
  obtain ⟨y, hy⟩ := exists_lam_eq_of_mem_perfectCore hk hθ hker hodd hpA hp2 hθp hlamX hlam
    (trSL_mem_perfectCore_stdCen hk h4 (Ne.symm a.2.1) (idxU_ne_idxV hk) a.2.1 1)
  have hc : x * y = y * x := (mem_center_iff.mp hx y).symm
  rw [← hy, ← map_mul (proj (2 + k) K), ← map_mul (proj (2 + k) K), ← map_mul lam,
    ← map_mul lam, hc]

theorem linPsi_map_eq_one (hk : 2 ≤ k) (h4 : 4 ≤ Nat.card K) (hq4 : ∃ s : Finset K, s.card = 4)
    {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m) {θ : ↥A →* projectiveSL (2 + k) K}
    (hθ : Function.Surjective θ) (hker : θ.ker = center ↥A) (hodd : Odd (Nat.card (center ↥A)))
    {p : G} (hpA : p ∈ A) (hp2 : p ^ 2 = 1)
    (hθp : θ ⟨p, hpA⟩ = proj (2 + k) K (trSL (idxU hk) (idxV hk) (idxU_ne_idxV hk) 1))
    {lam : ↥(perfectCore (A ⊓ centralizer ({p} : Set G))) →* SpecialLinearGroup (Fin (2 + k)) K}
    {ψ : ↥(perfectCore (A ⊓ centralizer ({p} : Set G))) →* SpecialLinearGroup (StdMid hk) K}
    (hlamX : ∀ x, lam x ∈ stdX K hk)
    (hlam : ∀ x, proj (2 + k) K (lam x) = θ (Subgroup.inclusion (perfectCore_inf_le A p) x))
    (hψ : ∀ x, (ψ x : Matrix (StdMid hk) (StdMid hk) K) =
      stdRhoMat hk (lam x : Matrix (Fin (2 + k)) (Fin (2 + k)) K))
    (γ : MulAut ↥(perfectCore (A ⊓ centralizer ({p} : Set G))))
    {x : ↥(perfectCore (A ⊓ centralizer ({p} : Set G)))} (hx : ψ x = 1) : ψ (γ x) = 1 := by
  have hsurj := linPsi_surjective hk h4 hθ hker hodd hpA hp2 hθp hlamX hlam hψ
  set M := (ψ.ker.map (γ : ↥(perfectCore (A ⊓ centralizer ({p} : Set G))) →*
    ↥(perfectCore (A ⊓ centralizer ({p} : Set G))))).map ψ with hM
  have hMn : M.Normal := ((ψ.normal_ker).map _ γ.surjective).map _ hsurj
  have hM4 : ∀ y ∈ M, y ^ 4 = 1 := by
    rintro _ ⟨_, ⟨n, hn, rfl⟩, rfl⟩
    have h1 := theta_pow_four_eq_one_of_linPsi hk hlamX hlam hψ hn
    have hz : Subgroup.inclusion (perfectCore_inf_le A p) (n ^ 4) ∈ center ↥A := by
      rw [← hker]
      exact h1
    have h2 : n ^ 4 ∈ center ↥(perfectCore (A ⊓ centralizer ({p} : Set G))) := by
      rw [mem_center_iff]
      intro y
      have e := mem_center_iff.mp hz (Subgroup.inclusion (perfectCore_inf_le A p) y)
      exact Subtype.ext (congrArg (Subtype.val : ↥A → G) e)
    have h3 : γ (n ^ 4) ∈ center ↥(perfectCore (A ⊓ centralizer ({p} : Set G))) := by
      rw [← Subgroup.map_center_eq γ]
      exact ⟨_, h2, rfl⟩
    rw [← map_pow, ← map_pow]
    exact linPsi_eq_one_of_mem_center hk h4 hθ hker hodd hpA hp2 hθp hlamX hlam hψ h3
  have hmem : ψ (γ x) ∈ M := ⟨γ x, ⟨x, hx, rfl⟩, rfl⟩
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple
    (isQuasisimple_SL_stdMid hk hq4) M with hc | htop
  · exact eq_one_of_pow_four_eq_one_of_mem_center (odd_card_center_SL_stdMid hk hm hK) (hc hmem)
      (hM4 _ hmem)
  · exfalso
    obtain ⟨x₃, hx₃⟩ := exists_lam_eq_of_mem_perfectCore hk hθ hker hodd hpA hp2 hθp hlamX hlam
      (blkSL₁_range_le_perfectCore hk h4 ⟨slTwoThree K, rfl⟩)
    have h1 : ψ x₃ ^ 4 = 1 := hM4 _ (htop ▸ Subgroup.mem_top _)
    have h2 : ψ x₃ ^ 4 = ψ x₃ := by
      apply Subtype.ext
      rw [← map_pow, hψ, hψ, map_pow, hx₃, ← map_pow, pow_succ, slTwoThree_pow_three, one_mul]
    rw [h2] at h1
    set w : StdMid hk := ⟨idxW k, idxW_ne_idxU hk, idxW_ne_idxV hk⟩
    have h3 := congrFun (congrFun (congrArg Subtype.val h1) w) w
    rw [hψ, hx₃, stdRhoMat, submatrix_apply, coe_blkSL₁, Matrix.SpecialLinearGroup.coe_one,
      one_apply_eq] at h3
    have h5 : blk (slTwoThree K : Matrix (Fin 2) (Fin 2) K) (1 : Matrix (Fin k) (Fin k) K)
        (idxW k) (idxW k) = 0 := by
      rw [blk, coe_reindexAlgEquiv, reindex_apply, submatrix_apply, idxW,
        Equiv.symm_apply_apply, fromBlocks_apply₁₁, slTwoThree_apply_zero_zero]
    exact zero_ne_one (h5.symm.trans h3)

theorem exists_mulAut_linPsi (hk : 2 ≤ k) (h4 : 4 ≤ Nat.card K)
    (hq4 : ∃ s : Finset K, s.card = 4) {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m)
    {θ : ↥A →* projectiveSL (2 + k) K}
    (hθ : Function.Surjective θ) (hker : θ.ker = center ↥A) (hodd : Odd (Nat.card (center ↥A)))
    {p : G} (hpA : p ∈ A) (hp2 : p ^ 2 = 1)
    (hθp : θ ⟨p, hpA⟩ = proj (2 + k) K (trSL (idxU hk) (idxV hk) (idxU_ne_idxV hk) 1))
    {lam : ↥(perfectCore (A ⊓ centralizer ({p} : Set G))) →* SpecialLinearGroup (Fin (2 + k)) K}
    {ψ : ↥(perfectCore (A ⊓ centralizer ({p} : Set G))) →* SpecialLinearGroup (StdMid hk) K}
    (hlamX : ∀ x, lam x ∈ stdX K hk)
    (hlam : ∀ x, proj (2 + k) K (lam x) = θ (Subgroup.inclusion (perfectCore_inf_le A p) x))
    (hψ : ∀ x, (ψ x : Matrix (StdMid hk) (StdMid hk) K) =
      stdRhoMat hk (lam x : Matrix (Fin (2 + k)) (Fin (2 + k)) K))
    (γ : MulAut ↥(perfectCore (A ⊓ centralizer ({p} : Set G)))) :
    ∃ β : MulAut (SpecialLinearGroup (StdMid hk) K), ∀ x, β (ψ x) = ψ (γ x) :=
  exists_mulAut_comp_eq_of_ker ψ (linPsi_surjective hk h4 hθ hker hodd hpA hp2 hθp hlamX hlam hψ)
    γ fun _ hx => linPsi_map_eq_one hk h4 hq4 hm hK hθ hker hodd hpA hp2 hθp hlamX hlam hψ γ hx

end Lift

end CFSG.ComponentClassification.RankTwoClassical
