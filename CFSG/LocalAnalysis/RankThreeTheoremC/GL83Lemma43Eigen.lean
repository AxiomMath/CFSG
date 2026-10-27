module

import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.Maschke
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ElementaryAbelianAction
public import CFSG.Open.LocalVocabulary
public import TauCeti.Algebra.GroupAction.TypeTags

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup
open scoped Pointwise IsMulCommutative

variable {G : Type} [Group G]

private theorem exists_isCompl_invariant_subgroup {p : ℕ} [Fact p.Prime] {A V : Type*} [Group A]
    [Fintype A] [Group V] [IsElementaryAbelian p V] [MulDistribMulAction A V]
    (hA : ¬ p ∣ Fintype.card A) (U : Subgroup V) (hU : ∀ a : A, ∀ g : V, g ∈ U → a • g ∈ U) :
    ∃ W : Subgroup V, IsCompl U W ∧ ∀ a : A, ∀ g : V, g ∈ W → a • g ∈ W := by
  classical
  let e : Subgroup V ≃o Submodule (ZMod p) (Additive V) :=
    Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := p))
  let rho := Theory.Representation.ofElementaryAbelianAction (A := A) (G := V) (p := p)
  have hUmod : ∀ a : A, ∀ v ∈ e U, rho a v ∈ e U := by
    intro a v hv
    change Additive.toMul v ∈ U at hv
    change Additive.toMul (rho a v) ∈ U
    simpa [rho] using hU a (Additive.toMul v) hv
  have hUinv : e U ∈ rho.invtSubmodule := by
    rw [Representation.mem_invtSubmodule]
    intro a
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    exact hUmod a
  let Upack : rho.invtSubmodule := ⟨e U, hUinv⟩
  let instAdd : AddCommGroup rho.asModule := Representation.instAddCommGroupAsModule rho
  let : AddCommGroup rho.asModule := instAdd
  let instMod : Module (MonoidAlgebra (ZMod p) A) rho.asModule :=
    Representation.instModuleMonoidAlgebraAsModule rho
  let : Module (MonoidAlgebra (ZMod p) A) rho.asModule := instMod
  have : NeZero (Fintype.card A : ZMod p) := by
    constructor
    intro hzero
    exact hA ((ZMod.natCast_eq_zero_iff (Fintype.card A) p).1 hzero)
  let Umod : @Submodule (MonoidAlgebra (ZMod p) A) rho.asModule _
      instAdd.toAddCommMonoid instMod :=
    rho.mapSubmodule Upack
  obtain ⟨Wmod, hUWmod⟩ := @MonoidAlgebra.Submodule.exists_isCompl'
    (ZMod p) inferInstance A inferInstance inferInstance rho.asModule
      instAdd instMod inferInstance Umod
  let Wpack : rho.invtSubmodule := rho.mapSubmodule.symm Wmod
  have hcompl_pack : IsCompl Upack Wpack :=
    (rho.mapSubmodule.isCompl_iff).2 (by simpa [Umod, Wpack] using hUWmod)
  have hcompl : IsCompl (e U) (Wpack : Submodule (ZMod p) (Additive V)) := by
    rw [isCompl_iff, disjoint_iff, codisjoint_iff] at hcompl_pack ⊢
    constructor
    · simpa [Upack] using congrArg Subtype.val hcompl_pack.1
    · simpa [Upack] using congrArg Subtype.val hcompl_pack.2
  refine ⟨e.symm Wpack, ?_, ?_⟩
  · apply e.isCompl_iff.mpr
    simpa using hcompl
  · intro a g hg
    have hgmod : Additive.ofMul g ∈ (Wpack : Submodule (ZMod p) (Additive V)) := by
      simpa [e] using hg
    have hmem := (Representation.mem_invtSubmodule (ρ := rho)).1 Wpack.2 a
    have hsmul := (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (rho a)).1 hmem _ hgmod
    simpa [e, rho] using hsmul

private theorem unique_component {O K : Subgroup G} (hKO : K ⊓ O = ⊥) {x : G} {k₁ k₂ : K}
    (h₁ : (k₁ : G)⁻¹ * x ∈ O) (h₂ : (k₂ : G)⁻¹ * x ∈ O) : k₁ = k₂ := by
  have h3 : (k₁ : G)⁻¹ * k₂ ∈ K ⊓ O := by
    refine ⟨K.mul_mem (K.inv_mem k₁.2) k₂.2, ?_⟩
    have h4 := O.mul_mem h₁ (O.inv_mem h₂)
    have e : (k₁ : G)⁻¹ * x * ((k₂ : G)⁻¹ * x)⁻¹ = (k₁ : G)⁻¹ * k₂ := by group
    rwa [e] at h4
  rw [hKO, Subgroup.mem_bot] at h3
  exact Subtype.ext (inv_mul_eq_one.mp h3)

private theorem inv_mul_mem_iff {O : Subgroup G} {k : G} (hk : k ∈ normalizer (O : Set G))
    (z : G) : k⁻¹ * z ∈ O ↔ z * k⁻¹ ∈ O := by
  have e : z * k⁻¹ = k * (k⁻¹ * z) * k⁻¹ := by group
  rw [e]
  exact mem_normalizer_iff.mp hk (k⁻¹ * z)

private theorem exists_action {O K Y : Subgroup G} (hKO : K ≤ normalizer (O : Set G))
    (hYO : Y ≤ normalizer (O : Set G)) (hKO' : K ⊓ O = ⊥)
    (hYB : Y ≤ normalizer ((K ⊔ O : Subgroup G) : Set G)) :
    ∃ ρ : Y →* MulAut K, ∀ (y : Y) (k : K),
      ((ρ y k : K) : G)⁻¹ * ((y : G) * k * (y : G)⁻¹) ∈ O := by
  classical
  have hex : ∀ (y : Y) (k : K), ∃ k' : K, (k' : G)⁻¹ * ((y : G) * k * (y : G)⁻¹) ∈ O := by
    intro y k
    have hmem : (y : G) * k * (y : G)⁻¹ ∈ K ⊔ O :=
      (mem_normalizer_iff.mp (hYB y.2) k).mp (Subgroup.mem_sup_left k.2)
    have hset : ((K ⊔ O : Subgroup G) : Set G) = (K : Set G) * (O : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right K O hKO
    have hmem' : (y : G) * k * (y : G)⁻¹ ∈ (K : Set G) * (O : Set G) := by
      rw [← hset]
      exact hmem
    obtain ⟨a, ha, o, ho, hao⟩ := hmem'
    refine ⟨⟨a, ha⟩, ?_⟩
    show a⁻¹ * ((y : G) * k * (y : G)⁻¹) ∈ O
    rw [← hao]
    simpa using ho
  choose f hf using hex
  have f_mul : ∀ (y : Y) (k k' : K), f y (k * k') = f y k * f y k' := by
    intro y k k'
    refine unique_component hKO' (hf y (k * k')) ?_
    have h₁ := hf y k
    have h₂ := hf y k'
    have hn : (f y k' : G) ∈ normalizer (O : Set G) := hKO (f y k').2
    have h₃ := (mem_normalizer_iff''.mp hn _).mp h₁
    have e : ((f y k * f y k' : K) : G)⁻¹ * ((y : G) * ((k * k' : K) : G) * (y : G)⁻¹) =
        ((f y k' : G)⁻¹ * ((f y k : G)⁻¹ * ((y : G) * k * (y : G)⁻¹)) * (f y k' : G)) *
          ((f y k' : G)⁻¹ * ((y : G) * k' * (y : G)⁻¹)) := by
      simp only [Subgroup.coe_mul]
      group
    have hmem := O.mul_mem h₃ h₂
    rw [← e] at hmem
    exact hmem
  have f_one : ∀ k : K, f 1 k = k := by
    intro k
    refine unique_component hKO' (x := (k : G)) ?_ ?_
    · simpa using hf 1 k
    · simp
  have f_comp : ∀ (y y' : Y) (k : K), f (y * y') k = f y (f y' k) := by
    intro y y' k
    refine unique_component hKO' (hf (y * y') k) ?_
    have h₁ := hf y' k
    have h₂ := hf y (f y' k)
    have h₃ : (y : G) * ((f y' k : G)⁻¹ * ((y' : G) * k * (y' : G)⁻¹)) * (y : G)⁻¹ ∈ O :=
      (mem_normalizer_iff.mp (hYO y.2) _).mp h₁
    have e : (f y (f y' k) : G)⁻¹ * (((y * y' : Y) : G) * k * ((y * y' : Y) : G)⁻¹) =
        ((f y (f y' k) : G)⁻¹ * ((y : G) * (f y' k : G) * (y : G)⁻¹)) *
          ((y : G) * ((f y' k : G)⁻¹ * ((y' : G) * k * (y' : G)⁻¹)) * (y : G)⁻¹) := by
      simp only [Subgroup.coe_mul]
      group
    have hmem := O.mul_mem h₂ h₃
    rw [← e] at hmem
    exact hmem
  let φ : Y → (K ≃* K) := fun y =>
    { toFun := f y
      invFun := f y⁻¹
      left_inv := fun k => by rw [← f_comp, inv_mul_cancel, f_one]
      right_inv := fun k => by rw [← f_comp, mul_inv_cancel, f_one]
      map_mul' := f_mul y }
  refine ⟨{ toFun := φ, map_one' := ?_, map_mul' := ?_ }, hf⟩
  · exact MulEquiv.ext fun k => f_one k
  · intro y y'
    exact MulEquiv.ext fun k => f_comp y y' k

theorem l43_exists_eigenline [Finite G] {O K Y : Subgroup G} {ℓ : G}
    (hKO : K ≤ normalizer (O : Set G)) (hYO : Y ≤ normalizer (O : Set G))
    (hO3 : ¬ 3 ∣ Nat.card O) (hY2 : IsPGroup 2 Y)
    (hK : IsElemAbelian 3 K) (hK9 : Nat.card K = 9)
    (hYB : Y ≤ normalizer ((K ⊔ O : Subgroup G) : Set G))
    (hℓ : ℓ ∈ K) (hℓ1 : ℓ ≠ 1) (hYℓ : ∀ y ∈ Y, y * ℓ * y⁻¹ * ℓ⁻¹ ∈ O)
    (hnt : ∃ y ∈ Y, ∃ k ∈ K, y * k * y⁻¹ * k⁻¹ ∉ O) :
    ∃ U₂ : Subgroup G, U₂ ≤ K ∧ Nat.card U₂ = 3 ∧ zpowers ℓ ⊓ U₂ = ⊥ ∧
      Y ≤ normalizer ((U₂ ⊔ O : Subgroup G) : Set G) ∧
      ∃ y ∈ Y, ∃ b ∈ U₂ ⊔ O, y * b * y⁻¹ * b⁻¹ ∉ O := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKO' : K ⊓ O = ⊥ := by
    have hd : Nat.card (K ⊓ O : Subgroup G) ∣ 3 ^ 2 := by
      have h := Subgroup.card_dvd_of_le (inf_le_left : K ⊓ O ≤ K)
      rw [hK9] at h
      simpa using h
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · exact Subgroup.eq_bot_of_card_eq _ (by simpa using hi)
    · exfalso
      apply hO3
      have h3 : 3 ∣ Nat.card (K ⊓ O : Subgroup G) := by
        rw [hi]
        exact dvd_pow_self 3 hipos.ne'
      exact h3.trans (Subgroup.card_dvd_of_le inf_le_right)
  obtain ⟨ρ, hρ⟩ := exists_action hKO hYO hKO' hYB
  obtain ⟨ℓ', hℓ'⟩ : ∃ ℓ' : K, (ℓ' : G) = ℓ := ⟨⟨ℓ, hℓ⟩, rfl⟩
  have hρ_eq : ∀ (y : Y) (k : K),
      ρ y k = k ↔ (y : G) * k * (y : G)⁻¹ * (k : G)⁻¹ ∈ O := by
    intro y k
    rw [← inv_mul_mem_iff (hKO k.2) ((y : G) * k * (y : G)⁻¹)]
    constructor
    · intro h
      have h' := hρ y k
      rw [h] at h'
      exact h'
    · intro h
      exact unique_component hKO' (hρ y k) h
  have hρℓ : ∀ y : Y, ρ y ℓ' = ℓ' := fun y =>
    (hρ_eq y ℓ').mpr (by rw [hℓ']; exact hYℓ y y.2)
  have : IsElementaryAbelian 3 K :=
    { toIsMulCommutative := hK.1
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x =>
        Subtype.ext (by simpa using hK.2 x x.2) }
  have : Fintype Y := Fintype.ofFinite Y
  have hA : ¬ 3 ∣ Fintype.card Y := by
    obtain ⟨n, hn⟩ := hY2.exists_card_eq
    rw [← Nat.card_eq_fintype_card, hn]
    intro h
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by norm_num)
  let _ : MulDistribMulAction Y K := MulDistribMulAction.compHom K ρ
  have hinvU : ∀ (a : Y) (g : K), g ∈ zpowers ℓ' → a • g ∈ zpowers ℓ' := by
    intro a g hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    show ρ a (ℓ' ^ n) ∈ zpowers ℓ'
    rw [map_zpow, hρℓ a]
    exact Subgroup.zpow_mem_zpowers ℓ' n
  obtain ⟨W, hW, hWinv⟩ :=
    exists_isCompl_invariant_subgroup (p := 3) (A := Y) (V := K) hA (zpowers ℓ') hinvU
  have hℓ3 : ℓ' ^ 3 = 1 := by
    apply Subtype.ext
    simpa [hℓ'] using hK.2 ℓ hℓ
  have hℓ'1 : ℓ' ≠ 1 := fun h => hℓ1 (by simpa [hℓ'] using congrArg Subtype.val h)
  have hLcard : Nat.card (zpowers ℓ') = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hℓ3 hℓ'1
  have hWcard : Nat.card W = 3 := by
    have hW9 : Nat.card W ∣ 3 ^ 2 := by
      have h := Subgroup.card_subgroup_dvd_card W
      rw [hK9] at h
      simpa using h
    obtain ⟨j, hj2, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hW9
    interval_cases j
    · exfalso
      have hbot : W = ⊥ := Subgroup.eq_bot_of_card_eq _ (by simpa using hj)
      have htop : zpowers ℓ' = ⊤ := by
        have h := hW.sup_eq_top
        rwa [hbot, sup_bot_eq] at h
      have hcard : Nat.card (zpowers ℓ') = Nat.card K := by
        rw [htop, Subgroup.card_top]
      omega
    · simpa using hj
    · exfalso
      have htop : W = ⊤ := by
        apply Subgroup.eq_top_of_card_eq
        rw [hK9]
        simpa using hj
      have hbot : zpowers ℓ' = ⊥ := by
        have h := hW.inf_eq_bot
        rwa [htop, inf_top_eq] at h
      have hcard : Nat.card (zpowers ℓ') = 1 := by
        rw [hbot, Subgroup.card_bot]
      omega
  obtain ⟨y₀, hy₀, k₀, hk₀, hnot₀⟩ := hnt
  have hmove : ∃ (y : Y) (b : K), b ∈ W ∧ ρ y b ≠ b := by
    by_contra hcon
    push Not at hcon
    apply hnot₀
    have hfix : ∀ k : K, ρ ⟨y₀, hy₀⟩ k = k := by
      intro k
      let F : Subgroup K :=
        { carrier := {k | ρ ⟨y₀, hy₀⟩ k = k}
          mul_mem' := fun {a b} (ha : ρ ⟨y₀, hy₀⟩ a = a) (hb : ρ ⟨y₀, hy₀⟩ b = b) => by
            show ρ ⟨y₀, hy₀⟩ (a * b) = a * b
            rw [map_mul, ha, hb]
          one_mem' := map_one (ρ ⟨y₀, hy₀⟩)
          inv_mem' := fun {a} (ha : ρ ⟨y₀, hy₀⟩ a = a) => by
            show ρ ⟨y₀, hy₀⟩ a⁻¹ = a⁻¹
            rw [map_inv, ha] }
      have hF : zpowers ℓ' ⊔ W ≤ F :=
        sup_le (Subgroup.zpowers_le.mpr (hρℓ ⟨y₀, hy₀⟩)) fun b hb => hcon _ b hb
      have hk : k ∈ zpowers ℓ' ⊔ W := by
        rw [hW.sup_eq_top]
        exact Subgroup.mem_top k
      exact hF hk
    exact (hρ_eq ⟨y₀, hy₀⟩ ⟨k₀, hk₀⟩).mp (hfix _)
  obtain ⟨y₁, b₁, hb₁W, hb₁⟩ := hmove
  obtain ⟨U₂, hU₂⟩ : ∃ U₂ : Subgroup G, U₂ = W.map K.subtype := ⟨_, rfl⟩
  have hmem₂ : ∀ g : G, g ∈ U₂ ↔ ∃ w : K, w ∈ W ∧ (w : G) = g := fun g => by
    rw [hU₂]
    exact Subgroup.mem_map
  have hU₂K : U₂ ≤ K := by
    rw [hU₂]
    exact Subgroup.map_subtype_le W
  refine ⟨U₂, hU₂K, ?_, ?_, ?_, ?_⟩
  · rw [hU₂, Subgroup.card_map_of_injective K.subtype_injective]
    exact hWcard
  · have hz : zpowers ℓ = (zpowers ℓ').map K.subtype := by
      rw [MonoidHom.map_zpowers]
      simp [hℓ']
    rw [hU₂, hz, ← Subgroup.map_inf_eq _ _ _ K.subtype_injective, hW.inf_eq_bot,
      Subgroup.map_bot]
  · have key : ∀ y : Y, ∀ x ∈ U₂ ⊔ O, (y : G) * x * (y : G)⁻¹ ∈ U₂ ⊔ O := by
      intro y x hx
      have hset : ((U₂ ⊔ O : Subgroup G) : Set G) = (U₂ : Set G) * (O : Set G) :=
        Subgroup.coe_mul_of_left_le_normalizer_right U₂ O (hU₂K.trans hKO)
      have hx' : x ∈ (U₂ : Set G) * (O : Set G) := by
        rw [← hset]
        exact hx
      obtain ⟨u, hu, o, ho, rfl⟩ := hx'
      obtain ⟨w, hwW, rfl⟩ := (hmem₂ u).mp hu
      have h1 := hρ y w
      have h2 : (y : G) * o * (y : G)⁻¹ ∈ O := (mem_normalizer_iff.mp (hYO y.2) o).mp ho
      have hmemU : ((ρ y w : K) : G) ∈ U₂ := (hmem₂ _).mpr ⟨ρ y w, hWinv y w hwW, rfl⟩
      have e : (y : G) * ((w : G) * o) * (y : G)⁻¹ =
          ((ρ y w : K) : G) * (((ρ y w : K) : G)⁻¹ * ((y : G) * w * (y : G)⁻¹) *
            ((y : G) * o * (y : G)⁻¹)) := by group
      rw [e]
      exact Subgroup.mul_mem_sup hmemU (O.mul_mem h1 h2)
    intro y hy
    rw [mem_normalizer_iff]
    intro x
    constructor
    · exact key ⟨y, hy⟩ x
    · intro hx
      have h := key ⟨y⁻¹, Y.inv_mem hy⟩ _ hx
      simpa [mul_assoc] using h
  · refine ⟨y₁, y₁.2, (b₁ : G), Subgroup.mem_sup_left ((hmem₂ _).mpr ⟨b₁, hb₁W, rfl⟩), ?_⟩
    intro hmem
    exact hb₁ ((hρ_eq y₁ b₁).mpr hmem)

end CFSG.LocalAnalysis.RankThreeTheoremC
