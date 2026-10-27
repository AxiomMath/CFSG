module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SymplecticRigid
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SymplecticPlane

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Polynomial Module CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCSpFull
  CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.RankThree.Classical (spForm spLin spEnd altPrimaryData_spLin SpPrimaryBlocks
  symplectic_cross_prime_primary_centralizer_blocks)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.Open (IsElemAbelian)

variable {r : ℕ} {K : Type} [Field K]

local notation "PSp" => StatedProj (StatedSp r K)

theorem spListedFacts_q {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hq : 4 ≤ ℓ ^ f) (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hr : 2 ≤ r)
    (B : Subgroup (MulAut PSp)) (hB : (MulAut.conj : PSp →* MulAut PSp).range ≤ B)
    (x : StatedSp r K) (hxp : orderOf x = p) :
    (∀ h : primaryFactors (spEnd x), (h : K[X]) ≠ X - 1 →
      2 ≤ primaryMultiplicity (spEnd x) (h : K[X]) →
        SpListedFacts p B (proj r K x) (spBlockImage x (h : K[X]))) ∧
    (SpFixedListed x → SpListedFacts p B (proj r K x) (spFixedLayerImage x)) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero f hℓ.ne_zero)
  have hrq : ¬ (r = 2 ∧ ℓ ^ f = 2) := fun h => by omega
  obtain ⟨-, -, hinj⟩ := spProj_facts hℓ hf hK hr hrq
  have hx : x ^ p = 1 := by rw [← hxp]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := fun h => hp.one_lt.ne' (by rw [← hxp, h, orderOf_one])
  have ha1 : proj r K x ≠ 1 := fun h =>
    hx1 (KCSymplectic.eq_one_of_proj_eq_one_of_pow_eq_one (by omega) hp2 hp h hx)
  have ha : orderOf (proj r K x) = p := orderOf_eq_prime (by rw [← map_pow, hx, map_one]) ha1
  have blocks := (symplectic_cross_prime_primary_centralizer_blocks hℓ hf hK hp hp2 hpℓ
    (by omega) (proj r K x) ha).2 x rfl hxp
  have hcent := blocks.centralizer_eq
  refine ⟨fun h hh hm => spListed_facts hp hB hinj hcent (spPull_le_centralizer x _)
    (spPull_normalized x _)
    (spPull_isQuasisimple (spBlockFacts_of_ne_X_sub_one_q hq blocks h hh) hm), fun hl => ?_⟩
  have h42 : ¬ (spFixedDim x = 4 ∧ Nat.card K = 2) := fun h => by omega
  have himg : spFixedLayerImage x = (spFixedFactor x).map (proj r K) := by
    unfold spFixedLayerImage
    simp only [hl, h42, ↓reduceIte]
  rw [himg]
  exact spListed_facts hp hB hinj hcent (spFixedFactor_le_centralizer x)
    (spFixedFactor_normalized x) (spFixedFactor_isQuasisimple hK hℓ hf blocks hl h42)

theorem localDeltaIn_eq_bot_psp_q {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hq : 4 ≤ ℓ ^ f) (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    (hr : 2 ≤ r) (E : Subgroup (MulAut PSp)) (hEin : E ≤ innerAut PSp)
    (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2) {H : Subgroup (MulAut PSp)}
    (hH : innerAut PSp ≤ H) : localDeltaIn p H E = ⊥ := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero f hℓ.ne_zero)
  have hr1 : 1 ≤ r := by omega
  have hrq : ¬ (r = 2 ∧ ℓ ^ f = 2) := fun h => by omega
  have hinj := spConj_injective hℓ hf hK hr hrq
  have hEel : CFSG.IsElementaryAbelian p E :=
    { toIsMulCommutative := hE.1
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x =>
        Subtype.ext (hE.2 x x.2) }
  obtain ⟨Ahat, hlift, -⟩ := exists_unique_spPlaneLift hr1 hp hp2 hinj E hEin hEel hEc
  have S : SpPlaneSetupQ ℓ f p r K Ahat := ⟨hℓ, hf, hK, hp, hp2, hpℓ, hr, hq, hlift.1, hlift.2.1⟩
  have D := S.decomp
  refine eq_bot_iff.2 fun g hg => ?_
  rw [Subgroup.mem_bot]
  have hE1 : ∀ x ∈ Ahat, x ≠ 1 → MulAut.conj (proj r K x) ∈ E ∧ proj r K x ≠ 1 := by
    intro x hxA hx1
    have ha : spInnerLift r K x ∈ E := hlift.2.2.1 ▸ Subgroup.mem_map_of_mem _ hxA
    have ha1 : spInnerLift r K x ≠ 1 := fun h =>
      hx1 (hlift.2.2.2 hxA (one_mem _) (h.trans (map_one _).symm))
    exact ⟨ha, fun h => ha1 (by rw [spInnerLift_apply, h, map_one])⟩
  have hkey : ∀ x ∈ Ahat, x ≠ 1 → ∀ J : Subgroup PSp, SpListedFacts p H (proj r K x) J →
      p ∣ Nat.card J → ∀ t ∈ J, g * MulAut.conj t = MulAut.conj t * g :=
    fun x hxA hx1 J hJ hpJ =>
      commute_of_spListedFacts hp hinj hH hg (hE1 x hxA hx1).1 (hE1 x hxA hx1).2 hJ hpJ
  have hF : ∀ x ∈ Ahat, x ≠ 1 → _ := fun x hxA hx1 =>
    spListedFacts_q hℓ hf hK hq hp hp2 hpℓ hr H hH x (S.orderOf_eq hxA hx1)
  have hblk : ∀ x ∈ Ahat, x ≠ 1 → ∀ h ∈ primaryFactors (spEnd x), h ≠ X - 1 →
      2 ≤ primaryMultiplicity (spEnd x) h →
        ∀ t ∈ spBlockImage x h, g * MulAut.conj t = MulAut.conj t * g :=
    fun x hxA hx1 h hmem hh1 hm2 => hkey x hxA hx1 _ ((hF x hxA hx1).1 ⟨h, hmem⟩ hh1 hm2)
      (dvd_card_spBlockImage hr1 hp hp2 (S.blocks hxA hx1) ⟨h, hmem⟩ hh1 hm2)
  have hact : ∀ M : Subgroup ↥Ahat, Nat.card M = p → spLineSpace M ≠ ⊥ →
      ∀ x (hxA : x ∈ Ahat), (⟨x, hxA⟩ : ↥Ahat) ∈ M → x ≠ 1 →
        ∀ t ∈ spFixedLayerImage x, g * MulAut.conj t = MulAut.conj t * g := by
    intro M hM hVM x hxA hxM hx1
    obtain ⟨hlisted, -⟩ := S.spFixedListed D hM hVM hxA hxM hx1
    obtain ⟨u, huM, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVM
    have hmove : ∃ y ∈ Ahat, spEnd y u ≠ u := by
      by_contra hcon
      push Not at hcon
      have hu₀ : u ∈ spPlaneFix Ahat :=
        CFSG.RankThree.Classical.mem_fixSub.mpr fun a _ => hcon a a.2
      have huo := (Submodule.mem_inf.mp huM).2
      rw [LinearMap.BilinForm.mem_orthogonal_iff] at huo
      have := (D.nondeg none).2 ⟨u, hu₀⟩ fun z => huo z z.2
      exact hu0 (congrArg Subtype.val this)
    obtain ⟨y, hyA, hyu⟩ := hmove
    have hu : u ∈ LinearMap.ker (spEnd x - 1) := by
      rw [D.ker_eq_sup hM hxA hxM hx1]
      exact Submodule.mem_sup_right huM
    have hxy : y * x = x * y := congrArg Subtype.val (S.mul_comm_elem ⟨y, hyA⟩ ⟨x, hxA⟩)
    exact hkey x hxA hx1 _ ((hF x hxA hx1).2 hlisted) (dvd_card_spFixedLayerImage hr1 hp hp2
      (S.blocks hxA hx1) hlisted hxy (S.pow_eq_one hyA) hu hyu)
  have hlist : ∀ x ∈ Ahat, x ≠ 1 → CentralizesListed g x := by
    intro x hxA hx1
    refine ⟨fun hlisted t ht => ?_, hblk x hxA hx1⟩
    set M : Subgroup ↥Ahat := Subgroup.zpowers ⟨x, hxA⟩ with hMdef
    have hM : Nat.card M = p := by
      rw [hMdef, Nat.card_zpowers, Subgroup.orderOf_mk, S.orderOf_eq hxA hx1]
    have hxM : (⟨x, hxA⟩ : ↥Ahat) ∈ M := Subgroup.mem_zpowers _
    by_cases hVM : spLineSpace M = ⊥
    ·
      obtain ⟨M₁, -, hM₁, -, -, hV₁, -⟩ := D.two_active
      obtain ⟨t₁, ht₁, ht₁1⟩ := S.exists_ne_one_mem hM₁
      have ht₁1' : (t₁ : StatedSp r K) ≠ 1 := fun h => ht₁1 (Subtype.ext h)
      have hkerx : LinearMap.ker (spEnd x - 1) = spPlaneFix Ahat := by
        rw [D.ker_eq_sup hM hxA hxM hx1, hVM, sup_bot_eq]
      have hker₁ : LinearMap.ker (spEnd (t₁ : StatedSp r K) - 1) =
          spPlaneFix Ahat ⊔ spLineSpace M₁ := D.ker_eq_sup hM₁ t₁.2 ht₁ ht₁1'
      have hle : spFixedFactor x ≤ spFixedFactor (t₁ : StatedSp r K) :=
        spFixedFactor_le_of_ker_le (altPrimaryData_spLin S.p_cast_ne_zero (S.pow_eq_one hxA))
          (altPrimaryData_spLin S.p_cast_ne_zero (S.pow_eq_one t₁.2))
          (D.nondegenerate_ker hM hxA hxM hx1) (by rw [hkerx, hker₁]; exact le_sup_left)
      obtain ⟨hlisted₁, -⟩ := S.spFixedListed D hM₁ hV₁ t₁.2 ht₁ ht₁1'
      have hq4 := S.four_le_card
      have h42 : ¬ (spFixedDim (t₁ : StatedSp r K) = 4 ∧ Nat.card K = 2) := fun h => by omega
      have himg₁ : spFixedLayerImage (t₁ : StatedSp r K) =
          (spFixedFactor (t₁ : StatedSp r K)).map (proj r K) := by
        simp [spFixedLayerImage, hlisted₁, h42]
      have hlayer : spFixedLayerImage x ≤ (spFixedFactor x).map (proj r K) := by
        rw [spFixedLayerImage_eq]
        refine Subgroup.map_mono ?_
        unfold spFixedLayerS
        split_ifs <;> first | exact commutator_le_self _ | exact le_rfl
      have htmem : t ∈ spFixedLayerImage (t₁ : StatedSp r K) := by
        rw [himg₁]
        exact Subgroup.map_mono hle (hlayer ht)
      exact hact M₁ hM₁ hV₁ _ t₁.2 ht₁ ht₁1' t htmem
    · exact hact M hM hVM x hxA hxM hx1 t ht
  exact S.eq_one_of_centralizes hlist

end CFSG.HardMathSupport.Timmesfeld.CrossChar
