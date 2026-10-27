module

public import CFSG.LieType.SeitzGeneration.UnitaryONExt
public import CFSG.LieType.SeitzGeneration.UnitaryRankThreeBlocks
public import CFSG.LieType.SeitzGeneration.UnitaryHyperPSU
public import CFSG.LieType.SeitzGeneration.HyperAveraging
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeCore
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary
public import CFSG.LieType.SeitzGeneration.UnitaryBlocks
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.URankThree

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary HyperBlocks Centers
  CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.BorelTits Nonsplit CFSG.ClassicalGroups.UnitaryFlag

section Centers

variable {K : Type*} [Field K] {σ : K ≃+* K} {n p : ℕ}

theorem isCenter_of_mem_fixSub (hσ : ∀ c, σ (σ c) = c) {A F : Subgroup (SUid σ n)} (hFA : F ≤ A)
    (hF : F.relIndex A = p) {v : Fin n → K} (hv : v ∈ HyperBlocks.fixSub (act σ n) F)
    (hvi : herm σ v v = 0) : IsCenter (hyperClosure p ⊤ A) v := by
  refine ⟨hvi, fun c hc => ⟨tv hσ hvi hc, Subgroup.subset_closure
    ⟨Subgroup.mem_top _, F, hFA, hF, fun g hg => ?_⟩, tv_smul hσ hvi hc⟩⟩
  have hgv : g • v = v := hv g hg
  refine ext_smul σ fun u => ?_
  have h1 : herm σ v (g • u) = herm σ v u := by
    have := herm_smul_smul σ g v u
    rwa [hgv] at this
  rw [mul_smul, mul_smul, tv_smul, tv_smul, smul_add, smul_comm g (c * herm σ v u) v, hgv, h1]

end Centers

section Core

variable {ℓ f n : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

local notation "σ₀" => unitaryInvolution K ℓ f

omit [Fact ℓ.Prime] [CharP K ℓ] in
theorem eq_one_of_pow_prime_eq_one (hU : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime)
    (hpq1 : ¬ p ∣ ℓ ^ f + 1) (hpq : ¬ p ∣ ℓ ^ f - 1) {c : K} (hc : c ^ p = 1) : c = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hc
    exact zero_ne_one hc
  have hq := FiniteField.pow_card_sub_one_eq_one c hc0
  have hcardK : Fintype.card K = (ℓ ^ f) ^ 2 := by
    rw [Fintype.card_eq_nat_card]
    exact hU.card_eq_sq
  obtain ⟨t, ht⟩ : ∃ t, ℓ ^ f = t + 1 := ⟨ℓ ^ f - 1, by
    have := Nat.one_le_pow f ℓ hU.prime.pos
    omega⟩
  have hsplit : Fintype.card K - 1 = (ℓ ^ f - 1) * (ℓ ^ f + 1) := by
    rw [hcardK, ht]
    have : (t + 1) ^ 2 = t * (t + 2) + 1 := by ring
    rw [this, Nat.add_sub_cancel, Nat.add_sub_cancel]
  have hcop : Nat.gcd p (Fintype.card K - 1) = 1 := by
    rw [hsplit]
    exact Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd hp).2 hpq)
      ((Nat.Prime.coprime_iff_not_dvd hp).2 hpq1)
  have := pow_gcd_eq_one.mpr ⟨hc, hq⟩
  rwa [hcop, pow_one] at this

theorem ext_mem_hyperClosure (hU : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpℓ : p ≠ ℓ) (hpq1 : ¬ p ∣ ℓ ^ f + 1) (hpq : ¬ p ∣ ℓ ^ f - 1)
    {A : Subgroup (SUid σ₀ n)} (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hexp : ∀ a ∈ A, a ^ p = 1) (hcard : Nat.card A = p ^ 3) {m : ℕ}
    {x : Fin m → Fin n → K} (hx : ONExt.IsON σ₀ x)
    (hAU : ∀ a ∈ A, ∀ c, ∃ d, a • orthoEmb x c = orthoEmb x d)
    {y₀ : SUid σ₀ n} (hy₀A : y₀ ∈ A) (hy₀ : y₀ ≠ 1)
    (hy₀U : ∀ c, y₀ • orthoEmb x c = orthoEmb x c) (g : SUid σ₀ m) :
    ONExt.ext (isUnitaryInvolution hU).invol hx g ∈ hyperClosure p ⊤ A := by
  classical
  have hσ := isUnitaryInvolution hU
  have hfp : Fact p.Prime := ⟨hp⟩
  have hAfin : Finite A :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 3 hp.ne_zero)
  have hdet : ∀ s ∈ A,
      (ONExt.resMat σ₀ x ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).det = 1 := by
    intro s hs
    refine eq_one_of_pow_prime_eq_one hU hp hpq1 hpq ?_
    rw [← Matrix.det_pow, ← ONExt.resMat_pow hx (hAU s hs), hexp s hs, ONExt.resMat_one hx,
      Matrix.det_one]
  set r := ONExt.res hx hAU hdet with hr
  have hcommA : ∀ a b : A, a * b = b * a := fun a b => Subtype.ext (hcomm a a.2 b b.2)
  have hexpA : ∀ a : A, a ^ p = 1 := fun a => Subtype.ext (by
    rw [Subgroup.coe_pow]
    exact hexp a a.2)
  have hgen : ∀ (g₀ : SUid σ₀ m) (F : Subgroup A), F.index = p →
      (∀ f ∈ F, r f * g₀ = g₀ * r f) → ONExt.ext hσ.invol hx g₀ ∈ hyperClosure p ⊤ A := by
    intro g₀ F hF hFg
    refine Subgroup.subset_closure ⟨Subgroup.mem_top _, F.map A.subtype,
      Subgroup.map_subtype_le _, ?_, ?_⟩
    · have hsub : (F.map A.subtype).subgroupOf A = F :=
        Subgroup.comap_map_eq_self_of_injective A.subtype_injective F
      rw [Subgroup.relIndex, hsub]
      exact hF
    · rintro _ ⟨f₀, hf₀, rfl⟩
      exact ONExt.commute_ext hσ.invol hx hAU hdet f₀ (hFg f₀ hf₀)
  have hy₀ker : (⟨y₀, hy₀A⟩ : A) ∈ r.ker := by
    rw [MonoidHom.mem_ker]
    exact ONExt.res_eq_one hx hAU hdet ⟨y₀, hy₀A⟩ hy₀U
  have hkdvd : Nat.card r.ker ∣ p ^ 3 := hcard ▸ Subgroup.card_subgroup_dvd_card r.ker
  obtain ⟨k, hk3, hkc⟩ := (Nat.dvd_prime_pow hp).1 hkdvd
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hkc
    have hbot := Subgroup.eq_bot_of_card_eq _ hkc
    rw [hbot] at hy₀ker
    exact hy₀ (congrArg Subtype.val (Subgroup.mem_bot.1 hy₀ker))
  by_cases hk : k = 1
  ·
    subst hk
    have hkerIdx : r.ker.index = p ^ 2 := by
      have h1 := r.ker.card_mul_index
      rw [hkc, pow_one, hcard] at h1
      exact Nat.eq_of_mul_eq_mul_left hp.pos (by rw [h1]; ring)
    have hrc : Nat.card r.range = p ^ 2 := by rw [← Subgroup.index_ker, hkerIdx]
    let ε : SUid σ₀ m ≃* unitarySU ℓ f K m :=
      MulEquiv.subgroupCongr (suid_unitaryInvolution_eq hU m)
    let E' : Subgroup (unitarySU ℓ f K m) := r.range.map ε.toMonoidHom
    have hE'comm : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := by
      rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩ _ ⟨_, ⟨b, rfl⟩, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hcommA a b]
    have hE'exp : ∀ a ∈ E', a ^ p = 1 := by
      rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_pow, ← map_pow, hexpA a, map_one, map_one]
    have hE'card : Nat.card E' = p ^ 2 := by
      rw [Subgroup.card_map_of_injective ε.injective, hrc]
    have h2e := CFSG.RankThree.PartOne.CTP.two_mul_ordNegQ_le hU hp hpℓ E' hE'exp hE'card
    have he3 := three_le_ordNegQ hp hp5 hU.prime hpℓ hU.one_le hpq1 hpq
    have hcl := unitarySUNonsplit ℓ f p m K hU hp hp5 hpℓ hpq1 hpq (by omega) E' hE'comm hE'exp
      hE'card
    have hle : Subgroup.closure {g' : unitarySU ℓ f K m | ∃ x' ∈ E', x' ≠ 1 ∧ g' * x' = x' * g'} ≤
        (hyperClosure p ⊤ A).comap ((ONExt.ext hσ.invol hx).comp ε.symm.toMonoidHom) := by
      rw [Subgroup.closure_le]
      rintro g' ⟨_, ⟨_, ⟨a, rfl⟩, rfl⟩, hx'1, hg'x'⟩
      simp only [MulEquiv.coe_toMonoidHom] at hx'1 hg'x'
      have hcomm' : r a * ε.symm g' = ε.symm g' * r a := by
        apply ε.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hg'x']
      have ha1 : a ∉ r.ker := fun h => hx'1 (by rw [MonoidHom.mem_ker.1 h, map_one])
      have hidx : (r.ker ⊔ Subgroup.zpowers a).index = p := by
        have h1 := hyper_index_sup_zpowers (p := p) hcommA r.ker ha1 (hexpA a)
        rw [hkerIdx] at h1
        exact Nat.eq_of_mul_eq_mul_right hp.pos (by rw [h1]; ring)
      have hsub : r.ker ⊔ Subgroup.zpowers a ≤ (Subgroup.centralizer {ε.symm g'}).comap r := by
        refine sup_le (fun k hk => ?_) ?_
        · rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hk]
          exact Subgroup.one_mem _
        · rw [Subgroup.zpowers_le, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
          exact hcomm'
      change ONExt.ext hσ.invol hx (ε.symm g') ∈ hyperClosure p ⊤ A
      refine hgen (ε.symm g') _ hidx fun f₀ hf₀ => ?_
      have := hsub hf₀
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at this
      exact this
    have hmem : ε g ∈ Subgroup.closure
        {g' : unitarySU ℓ f K m | ∃ x' ∈ E', x' ≠ 1 ∧ g' * x' = x' * g'} := by
      rw [hcl]
      exact Subgroup.mem_top _
    have := hle hmem
    rw [Subgroup.mem_comap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply] at this
    exact this
  ·
    have hp2 : p ^ 2 ∣ Nat.card r.ker := by
      rw [hkc]
      exact pow_dvd_pow p (by omega)
    obtain ⟨F₀, hF₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := r.ker) p hp2
    have hFc : Nat.card (F₀.map r.ker.subtype) = p ^ 2 := by
      rw [Subgroup.card_map_of_injective r.ker.subtype_injective, hF₀]
    have hFi : (F₀.map r.ker.subtype).index = p := by
      have h := (F₀.map r.ker.subtype).card_mul_index
      rw [hFc, hcard] at h
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) (by rw [h]; ring)
    refine hgen g _ hFi fun f₀ hf₀ => ?_
    obtain ⟨k₀, -, rfl⟩ := hf₀
    rw [show r (r.ker.subtype k₀) = 1 from k₀.2, one_mul, mul_one]

theorem allCenters_of_fix (hU : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpℓ : p ≠ ℓ) (hpq1 : ¬ p ∣ ℓ ^ f + 1) (hpq : ¬ p ∣ ℓ ^ f - 1)
    {A : Subgroup (SUid σ₀ n)} (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hexp : ∀ a ∈ A, a ^ p = 1) (hcard : Nat.card A = p ^ 3) {m : ℕ}
    {x : Fin m → Fin n → K} (hx : ONExt.IsON σ₀ x)
    (hAU : ∀ a ∈ A, ∀ c, ∃ d, a • orthoEmb x c = orthoEmb x d)
    {y₀ : SUid σ₀ n} (hy₀A : y₀ ∈ A) (hy₀ : y₀ ≠ 1)
    (hy₀U : ∀ c, y₀ • orthoEmb x c = orthoEmb x c) :
    AllCenters (hyperClosure p ⊤ A) (Submodule.span K (Set.range x)) :=
  ONExt.allCenters_of_forall_ext_mem (isUnitaryInvolution hU).invol hx fun g =>
    ext_mem_hyperClosure hU hp hp5 hpℓ hpq1 hpq hcomm hexp hcard hx hAU hy₀A hy₀ hy₀U g

end Core

end CFSG.LieType.SeitzGeneration.URankThree
