module

public import CFSG.ClassicalInvolution.Q3.Q3T7P25H01
import CFSG.ClassicalInvolution.Asc77.AscT7U11Eng
public import CFSG.ClassicalInvolution.Q3.Q3T7P25A04

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7U
open CFSG.ClassicalInvolution.Asc77.T7U
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ : G}

private theorem hyp25F_q3 (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) :
    Hyp25F K S R R' z where
  hz2 := hyp.std.setting.hz.sq
  hz1 := hyp.std.setting.hz.ne_one
  hzS := hyp.hzS
  hRS := hyp.hR.2.2
  zA := T7T.z_mem_centralizer_of_hyp hyp
  swap_nf := T7G2.exists_swap_nonfused hyp
  hRne := T7ER.ne_of_hyp25 hyp
  cA := fun hs => T7T.conjSub_centralizer_of_hyp hyp hs
  twin_sq := fun hx =>
      T7T.twin_sq (show Hyp23Setting Ω K K' z from hyp.std.setting) hx
  not_norm := fun hg hzt hnf => T7G2.not_normalizes_of_nonfused hyp hg hzt hnf
  c25_5 := fun A hzA hAS hAn hall =>
      T7T.c25_5_proved G Ω K K' W S R R' z t u₁ u₂ hyp A hzA hAS hAn hall

theorem exists_normal_four_bad (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂)
    (hne : (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) ≠
      Subgroup.zpowers z) :
    ∃ a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
      a * a = 1 ∧ a ≠ 1 ∧ a ≠ z ∧
        (∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z) ∧
        z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)) := by
  exact CFSG.ClassicalInvolution.Asc77.T7U.exists_normal_four_badE (hyp25F_q3 hyp) hne

theorem comm_swap_of_normal_four (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {t' g : G}
    (ht'S : t' ∈ (S : Subgroup G)) (ht'2 : t' * t' = 1) (hg : g * z * g⁻¹ = t')
    (hnf : ¬ ∃ y : G, y * z * y⁻¹ = t' * z) {a : G} (haS : a ∈ (S : Subgroup G))
    (hconj : ∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z) :
    t' * a = a * t' := by
  exact CFSG.ClassicalInvolution.Asc77.T7U.comm_swap_of_normal_fourE (hyp25F_q3 hyp) ht'S ht'2 hg
    hnf haS hconj
section Residual

@[expose] def C25_11E4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ →
      ∀ a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
        a * a = 1 → a ≠ 1 → a ≠ z →
          (∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z) →
            z ∈ zStarOf (Subgroup.centralizer ({a} : Set G))
end Residual

theorem c25_11_of_E4 (h : C25_11E4) : C25_11 := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp
  by_contra hne
  obtain ⟨a, haA, ha2, ha1, haz, hconj, hbad⟩ := exists_normal_four_bad hyp hne
  exact hbad (h G Ω K K' W S R R' z t u₁ u₂ hyp a haA ha2 ha1 haz hconj)
end T7U
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
    CFSG.ClassicalInvolution.Disconnected
namespace C25X
open CFSG.ClassicalInvolution.Asc77.C25X
variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem twinSection_cases0 {n : ℕ}
    (hBelow : Generic.CITBelowU n) (hlt : Nat.card X < n) (hS : GenSection Φ)
    {A A' : Subgroup X} {z a₀ b₀ : X} (T : TwinSect0 Φ A A' z a₀ b₀) :
    (∀ L ∈ Φ, L = A ∨ L = A') ∨
      ∃ (D : OmegaLie 3 1 Φ) (_ : D.card = 1) (i : Fin D.card),
        (D.tag i = .PSp ∧ D.rank i = 2) ∨ (D.tag i = .PSL ∧ D.rank i = 4) ∨
          (D.tag i = .PSU ∧ D.rank i = 4) ∨ (D.tag i = .POmegaOdd ∧ D.rank i = 3) ∨
          (D.tag i = .POmegaPlus ∧ D.rank i = 4) ∨ (D.tag i = .POmegaMinus ∧ D.rank i = 4) := by
  classical
  have hΦ : HypOmegaModT Φ := hS.hyp
  by_cases hconn : DConnected Φ
  · left
    have hpath : ∀ N, Relation.ReflTransGen (fun M N : Subgroup X => N ∈ Φ ∧ dAdj Φ M N) A N →
        N = A ∨ N = A' := by
      intro N hN
      induction hN with
      | refl => exact Or.inl rfl
      | tail hpre hstep ih =>
        rename_i M N'
        obtain ⟨hN'Φ, hadj⟩ := hstep
        have hMΦ : M ∈ Φ := by
          rcases ih with rfl | rfl
          · exact T.hA
          · exact T.hA'
        rcases ih with rfl | rfl
        · refine Or.inr (T.nbA N' hN'Φ ?_)
          rcases hadj with h | h
          · exact h
          · exact Q3CL.T3.omegaNbr_symm (l6_2) hΦ hN'Φ hMΦ h
        · refine Or.inl (T.nbA' N' hN'Φ ?_)
          rcases hadj with h | h
          · exact h
          · exact Q3CL.T3.omegaNbr_symm (l6_2) hΦ hN'Φ hMΦ h
    intro L hL
    exact hpath L (hconn _ T.hA L hL)
  · right
    have hNE : ¬ DEdgeless Φ := by
      intro h
      rcases mem_kPerp_of_twin hΦ T.hA T.hA' T.hzA T.hzA' with h' | h'
      · exact T.ne h'
      · exact h _ T.hA' _ T.hA (Or.inl h')
    obtain ⟨d, ε, hd5, hd8, t', n', hortag, D, hcard, i, htag, hrank⟩ :=
      thm8SectBelow'_of_citBelow hBelow X hlt Φ hS
        ⟨_, T.hA⟩ hNE hconn
    refine ⟨D, hcard, i, ?_⟩
    rw [htag, hrank]
    rcases hortag with ⟨-, ht, hn⟩ | ⟨-, -, ht, hn⟩ | ⟨-, -, ht, hn⟩ | ⟨hd7, hodd, ht, hn⟩ |
      ⟨hd8', hev, -, ht, hn⟩ | ⟨hd8', hev, -, ht, hn⟩
    · exact Or.inl ⟨ht, hn⟩
    · exact Or.inr (Or.inl ⟨ht, hn⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨ht, hn⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, by omega⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, by omega⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ht, by omega⟩))))
end C25X
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
open scoped commutatorElement
namespace C25X
open CFSG.ClassicalInvolution.Asc77.C25X
section NC4
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {z : G}

theorem toBar_conj_odd {a x n : G} (hx : x ∈ ExactLayer.exactLayer Ω a)
    (hn : n ∈ oddCoreOf (ExactLayer.exactLayer Ω a)) (hxn : n * x * n⁻¹ ∈ ExactLayer.exactLayer Ω
        a) :
    T7H.toBar Ω a (n * x * n⁻¹) hxn = T7H.toBar Ω a x hx := by
  obtain ⟨n', hn', hnn⟩ := Subgroup.mem_map.mp hn
  have hnn' : (n' : G) = n := hnn
  subst hnn'
  unfold T7H.toBar
  have h1 : (⟨(n' : G) * x * (n' : G)⁻¹, hxn⟩ : ↥(ExactLayer.exactLayer Ω a)) = n' * ⟨x, hx⟩ * n'⁻¹
      :=
    rfl
  have h3 : QuotientGroup.mk' (classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω a)) n' = 1 :=
    (QuotientGroup.eq_one_iff n').mpr hn'
  rw [h1, map_mul, map_mul, map_inv, h3]
  simp

theorem nc4_layer_excl {S : Sylow 2 G} {R R' : Subgroup G} {t u₁ u₂ : G}
    (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a : G} (ha2 : a * a = 1) :
    ∀ {J₁ J₂ : Subgroup (↥(ExactLayer.exactLayer Ω a) ⧸ classicalInvolutionOddCore
        ↥(ExactLayer.exactLayer Ω a))},
      J₁ ∈ oddQuotientFamily (ExactLayer.exactPair Ω a) → J₂ ∈ oddQuotientFamily
          (ExactLayer.exactPair Ω a) →
      ∀ {y z₂ : ↥(ExactLayer.exactLayer Ω a) ⧸ classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω
          a)},
        y ∈ J₁ → y * y * y * y = 1 → y * y ≠ 1 → z₂ ∈ J₂ → z₂ * z₂ = 1 → z₂ ≠ 1 →
        z₂ ≠ y * y → z₂ * y = y * z₂ → False := by
  classical
  have hs : Hyp23Setting Ω K K' z := hyp.std.setting
  have hst := hs.stand
  have hΩ : HypOmegaModT Ω := hst.modU
  have hzK : IsUniqueInvolution K z := hs.hz
  have hcpg : IsPGroup 2 (Subgroup.zpowers a) := isPGroup_zpowers_of_sq_eq_one ha2
  set Y := ExactLayer.exactLayer Ω a with hY
  set N₀ := classicalInvolutionOddCore ↥Y with hN₀
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  intro J₁ J₂ hJ₁ hJ₂ y z₂ hy hy4 hy2 hz₂ hz₂2 hz₂1 hne hcomm
  
  obtain ⟨M₁, hM₁tq, rfl⟩ := T7H.exists_exactImg_of_mem hJ₁
  obtain ⟨M₂, hM₂tq, rfl⟩ := T7H.exists_exactImg_of_mem hJ₂
  obtain ⟨g₁, hg₁⟩ := hst.trans M₁ hM₁tq.1
  obtain ⟨g₂, hg₂⟩ := hst.trans M₂ hM₂tq.1
  have hzM₁ : IsUniqueInvolution M₁ (g₁ * z * g₁⁻¹) := by
    rw [← hg₁]
    exact hzK.conj g₁
  have hzM₂ : IsUniqueInvolution M₂ (g₂ * z * g₂⁻¹) := by
    rw [← hg₂]
    exact hzK.conj g₂
  have hzMY₁ : g₁ * z * g₁⁻¹ ∈ Y :=
    ExactLayer.exactCore_le_exactLayer hM₁tq
      (T7H.isUniqueInvolution_exactCore hΩ hcpg hM₁tq hzM₁).mem
  have hzMY₂ : g₂ * z * g₂⁻¹ ∈ Y :=
    ExactLayer.exactCore_le_exactLayer hM₂tq
      (T7H.isUniqueInvolution_exactCore hΩ hcpg hM₂tq hzM₂).mem
  have hbar₁ := T7H.exactImg_isUnique hΩ hcpg hM₁tq hzM₁ hzMY₁
  have hbar₂ := T7H.exactImg_isUnique hΩ hcpg hM₂tq hzM₂ hzMY₂
  have hz₂eq : z₂ = T7H.toBar Ω a (g₂ * z * g₂⁻¹) hzMY₂ :=
    (hbar₂.unique z₂ hz₂ hz₂2).resolve_left hz₂1
  have hyy : y * y = T7H.toBar Ω a (g₁ * z * g₁⁻¹) hzMY₁ := by
    refine (hbar₁.unique (y * y) ((T7H.exactImg Ω a M₁).mul_mem hy hy) ?_).resolve_left hy2
    calc y * y * (y * y) = y * y * y * y := by simp only [mul_assoc]
      _ = 1 := hy4
  
  obtain ⟨c, hcmem, hcy⟩ := Subgroup.mem_map.mp hy
  have hcM : (c : G) ∈ ExactLayer.exactCore a M₁ := Subgroup.mem_subgroupOf.mp hcmem
  have hy_ord : orderOf y = 4 := by
    have h4 : y ^ 2 ^ (1 + 1) = 1 := by
      have : y ^ 2 ^ (1 + 1) = y * y * y * y := by simp [pow_succ, mul_assoc]
      rw [this]
      exact hy4
    have h2 : ¬ y ^ 2 ^ 1 = 1 := by simpa [pow_two] using hy2
    have := orderOf_eq_prime_pow (p := 2) (n := 1) h2 h4
    simpa using this
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  set c' : ↥Y := c ^ m with hc'
  have hc'k : c' ^ (2 ^ k) = 1 := by
    rw [hc', ← pow_mul, mul_comm, ← hkm]
    exact pow_orderOf_eq_one c
  have hπc' : QuotientGroup.mk' N₀ c' = y ^ m := by
    rw [hc', map_pow, hcy]
  have hcop : Nat.Coprime (orderOf y) m := by
    rw [hy_ord]
    exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hm)
  have hym_ord : orderOf (y ^ m) = 4 := by
    rw [Nat.Coprime.orderOf_pow hcop, hy_ord]
  have hy44 : y ^ 4 = 1 := by
    rw [← hy_ord]
    exact pow_orderOf_eq_one y
  have hc'4 : c' ^ 4 = 1 := by
    have h1 : c' ^ 4 ∈ N₀ := by
      have h0 : QuotientGroup.mk' N₀ (c' ^ 4) = 1 := by
        rw [map_pow, hπc', ← pow_mul, mul_comm, pow_mul, hy44, one_pow]
      exact (QuotientGroup.eq_one_iff _).mp h0
    have h2 : orderOf (⟨c' ^ 4, h1⟩ : N₀) ∣ Nat.card N₀ := orderOf_dvd_natCard _
    have h3 : orderOf (⟨c' ^ 4, h1⟩ : N₀) ∣ 2 ^ k := by
      rw [← Subgroup.orderOf_coe]
      refine orderOf_dvd_of_pow_eq_one ?_
      show (c' ^ 4) ^ (2 ^ k) = 1
      rw [← pow_mul, mul_comm, pow_mul, hc'k, one_pow]
    have h4 : Nat.Coprime (2 ^ k) (Nat.card N₀) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hN₀odd)
    have h5 : orderOf (⟨c' ^ 4, h1⟩ : N₀) = 1 := Nat.eq_one_of_dvd_coprimes h4 h3 h2
    exact congrArg Subtype.val (orderOf_eq_one_iff.mp h5)
  have hc'2 : ¬ c' ^ 2 ^ 1 = 1 := by
    intro h'
    have h'' : c' ^ 2 = 1 := by simpa using h'
    have h3 : (y ^ m) ^ 2 = 1 := by
      rw [← hπc', ← map_pow, h'', map_one]
    have h4 : orderOf (y ^ m) ∣ 2 := orderOf_dvd_of_pow_eq_one h3
    rw [hym_ord] at h4
    omega
  have hc'_ord : orderOf c' = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) hc'2 (by simpa using hc'4)
    simpa using this
  set y₁ : G := (c' : G) with hy₁
  have hy₁M : y₁ ∈ M₁ :=
    ExactLayer.exactCore_le_left a M₁ ((ExactLayer.exactCore a M₁).pow_mem hcM m)
  have hy₁Y : y₁ ∈ Y := c'.2
  have hy₁4 : orderOf y₁ = 4 := by rw [hy₁, Subgroup.orderOf_coe]; exact hc'_ord
  
  have hcom : ⁅g₂ * z * g₂⁻¹, y₁⁆ ∈ oddCoreOf Y := by
    have h1 : (⟨g₂ * z * g₂⁻¹, hzMY₂⟩ : ↥Y) * c' * (c' * ⟨g₂ * z * g₂⁻¹, hzMY₂⟩)⁻¹ ∈ N₀ := by
      have h2 : QuotientGroup.mk' N₀ ((⟨g₂ * z * g₂⁻¹, hzMY₂⟩ : ↥Y) * c' *
          (c' * ⟨g₂ * z * g₂⁻¹, hzMY₂⟩)⁻¹) = 1 := by
        rw [map_mul, map_inv, map_mul, map_mul, hπc']
        have h3 : QuotientGroup.mk' N₀ (⟨g₂ * z * g₂⁻¹, hzMY₂⟩ : ↥Y) = z₂ := hz₂eq.symm
        rw [h3]
        exact mul_inv_eq_one.mpr ((Commute.pow_right (show Commute z₂ y from hcomm) m).eq)
      exact (QuotientGroup.eq_one_iff _).mp h2
    exact Subgroup.mem_map.mpr ⟨_, h1, by simp [commutatorElement_def, mul_assoc, hy₁]⟩
  
  have hR2 : IsPGroup 2 (Subgroup.zpowers y₁) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hy₁4]; norm_num)
  have hcN : g₂ * z * g₂⁻¹ ∈ Subgroup.normalizer (oddCoreOf Y : Set G) :=
    T7L.mem_normalizer_oddCoreOf (Subgroup.le_normalizer hzMY₂)
  have huN : y₁ ∈ Subgroup.normalizer (oddCoreOf Y : Set G) :=
    T7L.mem_normalizer_oddCoreOf (Subgroup.le_normalizer hy₁Y)
  obtain ⟨n, hn, hncent⟩ := T7L.exists_conj_centralizes hzM₂.sq (oddCoreOf_odd_natCard Y) hR2
    (Subgroup.zpowers_le.mpr huN) hcN (fun r hr => comm_mem_of_mem_zpowers huN hcom hr)
  have hyc : (n * y₁ * n⁻¹) * (g₂ * z * g₂⁻¹) = (g₂ * z * g₂⁻¹) * (n * y₁ * n⁻¹) :=
    Subgroup.mem_centralizer_singleton_iff.mp
      (hncent (conj_mem_conjSub (Subgroup.mem_zpowers y₁)))
  
  have hJ₀Ω : conjSub n M₁ ∈ Ω := hΩ.conjInvariant n M₁ hM₁tq.1
  have hJ₀z : IsUniqueInvolution (conjSub n M₁) (n * (g₁ * z * g₁⁻¹) * n⁻¹) := hzM₁.conj n
  have hyJ : n * y₁ * n⁻¹ ∈ conjSub n M₁ := conj_mem_conjSub hy₁M
  have hy4' : orderOf (n * y₁ * n⁻¹) = 4 := by
    have := MulEquiv.orderOf_eq (MulAut.conj n) y₁
    simpa [MulAut.conj_apply, hy₁4] using this
  have hya : g₂ * z * g₂⁻¹ ≠ n * (g₁ * z * g₁⁻¹) * n⁻¹ := by
    intro heq
    have hxn : n * (g₁ * z * g₁⁻¹) * n⁻¹ ∈ Y := heq ▸ hzMY₂
    have h1 : (⟨g₂ * z * g₂⁻¹, hzMY₂⟩ : ↥Y) = ⟨n * (g₁ * z * g₁⁻¹) * n⁻¹, hxn⟩ :=
      Subtype.ext heq
    have h2 : T7H.toBar Ω a (g₂ * z * g₂⁻¹) hzMY₂ =
        T7H.toBar Ω a (n * (g₁ * z * g₁⁻¹) * n⁻¹) hxn := by
      unfold T7H.toBar
      rw [h1]
    rw [toBar_conj_odd hzMY₁ hn hxn, ← hyy, ← hz₂eq] at h2
    exact hne h2
  exact T7ER.not_commute_of_conj hs hyp.hW hyp.hE4 hJ₀Ω hJ₀z hya hyJ hy4' hyc.symm
end NC4
end C25X
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
namespace C25X
open CFSG.ClassicalInvolution.Asc77.C25X
section Section
variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem s4_excl (hmf : NC4Fact) {tg : StatedLieTag} {k ee : ℕ}
    (M : Ih8Model 3 1 Φ tg k ee) (hne' : Φ.Nonempty)
    (hS4 : (tg = .PSU ∧ k = 4) ∨ (tg = .POmegaOdd ∧ k = 3) ∨
      (tg = .POmegaPlus ∧ k = 4) ∨ (tg = .POmegaMinus ∧ k = 4)) :
    ∃ J₁ ∈ Φ, ∃ J₂ ∈ Φ, ∃ y ∈ J₁, ∃ z₂ ∈ J₂, y * y * y * y = 1 ∧ y * y ≠ 1 ∧
      z₂ * z₂ = 1 ∧ z₂ ≠ 1 ∧ z₂ ≠ y * y ∧ z₂ * y = y * z₂ := by
  classical
  have hG2 : tg ≠ .G2 := by
    rintro rfl
    rcases hS4 with h | h | h | h <;> simp at h
  have hD4 : tg ≠ .trialityD4 := by
    rintro rfl
    rcases hS4 with h | h | h | h <;> simp at h
  have hnpsl : ¬ (tg = .PSL ∧ k = 2) := by
    rintro ⟨rfl, rfl⟩
    rcases hS4 with h | h | h | h <;> simp at h
  have hee : ee = 1 := M.exp_eq_f hD4
  subst hee
  obtain ⟨R₁, hR₁, R₂, hR₂, y, hy, x₂, hx₂, hy4, hy2, hx₂2, hx₂1, hcomm, hnc⟩ :=
    hmf tg k M.admissible hS4
  have hR₁cls : R₁ ∈ M.cls := M.fund_subset_cls hne' hG2 hD4 hR₁
  have hR₂cls : R₂ ∈ M.cls := M.fund_subset_cls hne' hG2 hD4 hR₂
  have hinj₁ := M.injOn_fund hnpsl hR₁
  have hinj₂ := M.injOn_fund hnpsl hR₂
  have hyy : y * y ∈ R₁ := R₁.mul_mem hy hy
  refine ⟨R₁.map M.ψ, M.map_mem hR₁cls, R₂.map M.ψ, M.map_mem hR₂cls, M.ψ y,
    Subgroup.mem_map_of_mem _ hy, M.ψ x₂, Subgroup.mem_map_of_mem _ hx₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul, ← map_mul, hy4, map_one]
  · intro h
    rw [← map_mul] at h
    exact hy2 (hinj₁ (y * y) hyy h)
  · rw [← map_mul, hx₂2, map_one]
  · intro h
    exact hx₂1 (hinj₂ x₂ hx₂ h)
  · intro h
    apply hnc
    rw [← map_mul] at h
    have hker : x₂ * (y * y)⁻¹ ∈ Subgroup.center (modelUniv tg k 3 1 Fact.out).K := by
      apply M.ker_le_center
      rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
    have hxinv : (y * y)⁻¹ = y * y := by
      apply inv_eq_of_mul_eq_one_right
      calc y * y * (y * y) = y * y * y * y := by simp only [mul_assoc]
        _ = 1 := hy4
    rw [hxinv] at hker
    have hc : (y * y) * x₂ = x₂ * (y * y) := by
      calc y * y * x₂ = y * (y * x₂) := by simp only [mul_assoc]
        _ = y * (x₂ * y) := by rw [hcomm]
        _ = (y * x₂) * y := by simp only [mul_assoc]
        _ = (x₂ * y) * y := by rw [hcomm]
        _ = x₂ * (y * y) := by simp only [mul_assoc]
    rw [hc]
    exact hker
  · rw [← map_mul, ← map_mul, hcomm]
end Section
section Layer
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {z : G}

theorem layer_a_tag (hmf : NC4Fact) {S : Sylow 2 G} {R R' : Subgroup G} {t u₁ u₂ : G}
    (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a : G} (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (haR : ∀ x ∈ R, a * x = x * a) (haR' : ∀ x ∈ R', a * x = x * a) :
    (∀ L ∈ oddQuotientFamily (ExactLayer.exactPair Ω a),
        L = T7H.exactImg Ω a K ∨ L = T7H.exactImg Ω a K') ∨
      LayerOrthType Ω a 5 true ∨ LayerOrthType Ω a 6 (!piSign 3 1) := by
  classical
  obtain ⟨_hzY, _hu₁Y, _hu₂Y, -, -, hS, hlt, T⟩ := layer_a_frame hyp ha2 ha1 haR haR'
  have hs : Hyp23Setting Ω K K' z := hyp.std.setting
  have hst := hs.stand
  have hBelow : Generic.CITBelowU (Nat.card G) := hst.below
  rcases twinSection_cases0 hBelow hlt hS T with hconn | ⟨D, hcard, i, hsix⟩
  · left
    exact hconn
  · right
    let M := T7L.toModelOfGen hS.hyp D hcard hS.gen i
    have key : ((D.tag i = .PSU ∧ D.rank i = 4) ∨ (D.tag i = .POmegaOdd ∧ D.rank i = 3) ∨
        (D.tag i = .POmegaPlus ∧ D.rank i = 4) ∨ (D.tag i = .POmegaMinus ∧ D.rank i = 4)) →
        False := by
      intro hS4
      obtain ⟨J₁, hJ₁, J₂, hJ₂, y, hy, z₂, hz₂, hy4, hy2, hz₂2, hz₂1, hne, hcomm⟩ :=
        s4_excl hmf M ⟨_, T.hA⟩ hS4
      exact nc4_layer_excl hyp ha2 hJ₁ hJ₂ hy hy4 hy2 hz₂ hz₂2 hz₂1 hne hcomm
    have hπ : piSign 3 1 = false := by decide
    rcases hsix with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      exact sectionOrthType_of_hasOrthType hS.gen
        ⟨_, _, Or.inl ⟨rfl, h1, h2⟩, D, hcard, i, rfl, rfl⟩
    · right
      rw [hπ]
      exact sectionOrthType_of_hasOrthType hS.gen
        ⟨_, _, Or.inr (Or.inl ⟨rfl, rfl, h1, h2⟩), D, hcard, i, rfl, rfl⟩
    · exact (key (Or.inl ⟨h1, h2⟩)).elim
    · exact (key (Or.inr (Or.inl ⟨h1, h2⟩))).elim
    · exact (key (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))).elim
    · exact (key (Or.inr (Or.inr (Or.inr ⟨h1, h2⟩)))).elim
end Layer
end C25X
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
namespace C25X
open CFSG.ClassicalInvolution.Asc77.C25X
section Layer
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {z : G}

theorem zStar_of_connected {S : Sylow 2 G} {R R' : Subgroup G} {t u₁ u₂ : G}
    (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a : G} (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (haR : ∀ x ∈ R, a * x = x * a) (haR' : ∀ x ∈ R', a * x = x * a)
    (hconn : ∀ L ∈ oddQuotientFamily (ExactLayer.exactPair Ω a),
      L = T7H.exactImg Ω a K ∨ L = T7H.exactImg Ω a K') :
    z ∈ zStarOf (Subgroup.centralizer ({a} : Set G)) := by
  classical
  obtain ⟨hzY, -, -, hK₂, hK₂', -⟩ := layer_a_frame hyp ha2 ha1 haR haR'
  have hs : Hyp23Setting Ω K K' z := hyp.std.setting
  have hst := hs.stand
  have hΩ : HypOmegaModT Ω := hst.modU
  have hzK : IsUniqueInvolution K z := hs.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  have hcpg : IsPGroup 2 (Subgroup.zpowers a) := isPGroup_zpowers_of_sq_eq_one ha2
  have hz2 : z * z = 1 := hzK.sq
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  set H := Subgroup.centralizer ({a} : Set G) with hH
  set Y := ExactLayer.exactLayer Ω a with hY
  have hzH : z ∈ H := ExactLayer.exactLayer_le_centralizer Ω a hzY
  have hBN : ∀ b ∈ H, b ∈ Subgroup.normalizer (oddCoreOf Y : Set G) := fun b hb =>
    T7L.mem_normalizer_oddCoreOf
      (mem_normalizer_iff_conjSub_eq.mpr (ExactLayer.conjSub_exactLayer hΩ.conjInvariant hb))
  have hOY : oddCoreOf Y ≤ oddCoreOf H :=
    Balance.le_oddCoreIn_of_normalizes
      ((oddCoreOf_le_self Y).trans (ExactLayer.exactLayer_le_centralizer Ω a)) hBN
          (oddCoreOf_odd_natCard _)
  
  have key : ∀ c ∈ H, z * (c * z * c⁻¹) ∈ oddCoreOf Y := by
    intro c hc
    have hKc : conjSub c K ∈ ExactLayer.tqMembers Ω a :=
      ExactLayer.conjSub_mem_tqMembers hΩ.conjInvariant hc hK₂
    have hzc : IsUniqueInvolution (conjSub c K) (c * z * c⁻¹) := hzK.conj c
    have hz'c : c * z * c⁻¹ ∈ ExactLayer.exactCore a (conjSub c K) :=
      (T7H.isUniqueInvolution_exactCore hΩ hcpg hKc hzc).mem
    have hz'Y : c * z * c⁻¹ ∈ Y := ExactLayer.exactCore_le_exactLayer hKc hz'c
    have hbar := T7H.exactImg_isUnique hΩ hcpg hKc hzc hz'Y
    have hmem := T7H.exactImg_mem hKc
    have hbarK := T7H.exactImg_isUnique hΩ hcpg hK₂ hzK hzY
    have hbarK' := T7H.exactImg_isUnique hΩ hcpg hK₂' hzK' hzY
    have heq : T7H.toBar Ω a (c * z * c⁻¹) hz'Y = T7H.toBar Ω a z hzY := by
      rcases hconn _ hmem with h | h
      · rw [h] at hbar
        exact hbar.eq hbarK
      · rw [h] at hbar
        exact hbar.eq hbarK'
    have h1 : (⟨c * z * c⁻¹, hz'Y⟩ : ↥Y)⁻¹ * ⟨z, hzY⟩ ∈ classicalInvolutionOddCore ↥Y :=
      QuotientGroup.eq.mp heq
    have h2 : (c * z * c⁻¹)⁻¹ * z ∈ oddCoreOf Y := Subgroup.mem_map.mpr ⟨_, h1, rfl⟩
    have h3 := (oddCoreOf Y).inv_mem h2
    have e : ((c * z * c⁻¹)⁻¹ * z)⁻¹ = z * (c * z * c⁻¹) := by
      rw [mul_inv_rev, inv_inv, hzinv]
    rwa [e] at h3
  unfold zStarOf
  refine Subgroup.mem_map.mpr ⟨⟨z, hzH⟩, ?_, rfl⟩
  rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
  intro c
  obtain ⟨c0, rfl⟩ := QuotientGroup.mk_surjective c
  rw [← QuotientGroup.mk'_apply (classicalInvolutionOddCore ↥H) c0, ← map_mul, ← map_mul,
    QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  have hk := hOY (key (c0 : G)⁻¹ (H.inv_mem c0.2))
  obtain ⟨y, hy, hyval⟩ := Subgroup.mem_map.mp hk
  have hyval' : (y : G) = z * ((c0 : G)⁻¹ * z * ((c0 : G)⁻¹)⁻¹) := hyval
  have e : (c0 * (⟨z, hzH⟩ : ↥H))⁻¹ * (⟨z, hzH⟩ * c0) = y := by
    apply Subtype.ext
    rw [hyval']
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, mul_inv_rev, hzinv, mul_assoc]
  rw [e]
  exact hy

theorem layer_a_typed (hmf : NC4Fact) {S : Sylow 2 G} {R R' : Subgroup G} {t u₁ u₂ : G}
    (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a : G} (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (haR : ∀ x ∈ R, a * x = x * a) (haR' : ∀ x ∈ R', a * x = x * a) :
    z ∈ zStarOf (Subgroup.centralizer ({a} : Set G)) ∨ LayerOrthType Ω a 5 true ∨
      LayerOrthType Ω a 6 (!piSign 3 1) := by
  rcases layer_a_tag hmf hyp ha2 ha1 haR haR' with h | h
  · exact Or.inl (zStar_of_connected hyp ha2 ha1 haR haR' h)
  · exact Or.inr h
end Layer
end C25X
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
namespace C25X
open CFSG.ClassicalInvolution.Asc77.C25X
section Final
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {z : G}

theorem layer_a_typed_proved (hnc4 : NC4Fact) {S : Sylow 2 G} {R R' : Subgroup G} {t u₁ u₂ : G}
    (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a : G} (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (haR : ∀ x ∈ R, a * x = x * a) (haR' : ∀ x ∈ R', a * x = x * a) :
    z ∈ zStarOf (Subgroup.centralizer ({a} : Set G)) ∨ LayerOrthType Ω a 5 true ∨
      LayerOrthType Ω a 6 (!piSign 3 1) :=
  layer_a_typed hnc4 hyp ha2 ha1 haR haR'
end Final
end C25X
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
namespace C25X
open CFSG.ClassicalInvolution.Asc77.C25X
section Residual

@[expose] def C25_11Typed : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ →
      ∀ a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
        a * a = 1 → a ≠ 1 → a ≠ z →
          (∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z) →
            ¬ (LayerOrthType Ω a 5 true ∨ LayerOrthType Ω a 6 (!piSign 3 1))
end Residual
section Reduction

theorem c25_11E4_of_typed (hnc4 : NC4Fact) (h : C25_11Typed) : T7U.C25_11E4 := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haA ha2 ha1 haz hconj
  by_contra hz
  have hcent := Subgroup.mem_centralizer_iff.mp haA.2
  have haR : ∀ x ∈ R, a * x = x * a := fun x hx =>
    (hcent x (Subgroup.mem_sup_left hx)).symm
  have haR' : ∀ x ∈ R', a * x = x * a := fun x hx =>
    (hcent x (Subgroup.mem_sup_right hx)).symm
  have hty := layer_a_typed_proved hnc4 hyp ha2 ha1 haR haR'
  exact h G Ω K K' W S R R' z t u₁ u₂ hyp a haA ha2 ha1 haz hconj (hty.resolve_left hz)

theorem c25_11_of_typed (hnc4 : NC4Fact) (h : C25_11Typed) : C25_11 :=
  T7U.c25_11_of_E4 (c25_11E4_of_typed hnc4 h)
end Reduction
end C25X
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
