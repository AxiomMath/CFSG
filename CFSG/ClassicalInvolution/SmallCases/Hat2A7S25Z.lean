module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8Lift
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8LayerCol
public import CFSG.ClassicalInvolution.Asc77.AscC25W1
public import CFSG.ClassicalInvolution.Asc77.AscT7ABasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Balance (oddCoreIn)

section Wrap

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}


theorem mem_zStarOf_of_section (h : Hyp25A7 Ω K K' W S R R' z t u₁ u₂) {a : G} {X : Subgroup G}
    (hRX : R ≤ X) (hXC : X ≤ Subgroup.centralizer ({a} : Set G))
    (hXn : ∀ c ∈ Subgroup.centralizer ({a} : Set G), ∀ x ∈ X, c * x * c⁻¹ ∈ X)
    (hZ : ∀ c ∈ Subgroup.centralizer ({a} : Set G), ∀ y ∈ X,
      (c * z * c⁻¹) * y * (c * z * c⁻¹)⁻¹ * y⁻¹ ∈ oddCoreIn X) :
    z ∈ zStarOf (Subgroup.centralizer ({a} : Set G)) := by
  classical
  set C : Subgroup G := Subgroup.centralizer ({a} : Set G) with hC
  set N : Subgroup G := oddCoreIn X with hN
  have hΩ : AschTight.HypOmegaGen Ω := h.hΩ
  have hK : K ∈ Ω := h.hK
  have hzK : IsUniqueInvolution K z := h.std.1.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hzK h.std.1.hK'
  have hperp : KPerp Ω K = {K, K'} := h.std.2
  have hzX : z ∈ X := hRX h.hzR
  have hNodd : Odd (Nat.card N) := Balance.odd_card_oddCoreIn X
  have hNX : N ≤ X := Balance.oddCoreIn_le X
  have hcn : ∀ c ∈ C, c ∈ Subgroup.normalizer (X : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hXn c hc x hx, fun hx => ?_⟩
    have := hXn c⁻¹ (C.inv_mem hc) _ hx
    simpa [mul_assoc] using this
  have hNnorm : C ≤ Subgroup.normalizer (N : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => Balance.Bootstrap.conj_mem_oddCoreIn_of_mem_normalizer (hcn c hc) hy,
      fun hy => ?_⟩
    have := Balance.Bootstrap.conj_mem_oddCoreIn_of_mem_normalizer (hcn c⁻¹ (C.inv_mem hc)) hy
    simpa [mul_assoc] using this
  have hNC : N ≤ oddCoreIn C :=
    Balance.le_oddCoreIn_of_normalizes (hNX.trans hXC) hNnorm hNodd
  have key : ∀ d ∈ C, ∃ o ∈ N, o * (d * z * d⁻¹) * o⁻¹ = z := by
    intro d hd
    have hM : conjSub d K ∈ Ω := hΩ.conjInvariant d K hK
    have hzM : IsUniqueInvolution (conjSub d K) (d * z * d⁻¹) := hzK.conj d
    have hzMinv : (d * z * d⁻¹)⁻¹ = d * z * d⁻¹ := inv_eq_of_mul_eq_one_right hzM.sq
    by_cases hcase : ∃ o ∈ N, conjSub o (conjSub d K) = K
    · obtain ⟨o, hoN, hoK⟩ := hcase
      refine ⟨o, hoN, ?_⟩
      have h1 : IsUniqueInvolution (conjSub o (conjSub d K)) (o * (d * z * d⁻¹) * o⁻¹) :=
        hzM.conj o
      rw [hoK] at h1
      exact (hzK.eq h1).symm
    · push Not at hcase
      have hRn : ∀ e ∈ R, ∀ o ∈ N, e * o * e⁻¹ ∈ N := fun e he o ho =>
        Balance.conj_mem_oddCoreIn (hRX he) ho
      have hca : ∀ r ∈ R, (d * z * d⁻¹)⁻¹ * (r * (d * z * d⁻¹) * r⁻¹) ∈ N := by
        intro r hr
        have h1 := hZ d hd r (hRX hr)
        rw [hzMinv] at h1 ⊢
        simpa [mul_assoc] using h1
      obtain ⟨o, hoN, hnbr⟩ := Hat2A7S8.exists_nbr_conj hΩ hK hM hzM h.hR.1 h.hR.2.1 hNodd hRn
        hca hcase
      have hmem : conjSub o (conjSub d K) ∈ KPerp Ω K := Set.mem_insert_of_mem K hnbr
      rw [hperp] at hmem
      have hK'eq : conjSub o (conjSub d K) = K' := by
        rcases hmem with h1 | h1
        · exact absurd h1 (hcase o hoN)
        · exact h1
      refine ⟨o, hoN, ?_⟩
      have h1 : IsUniqueInvolution (conjSub o (conjSub d K)) (o * (d * z * d⁻¹) * o⁻¹) :=
        hzM.conj o
      rw [hK'eq] at h1
      exact (hzK'.eq h1).symm
  rw [C25W.mem_zStarOf_iff]
  refine ⟨hXC hzX, fun c hc => ?_⟩
  obtain ⟨o, hoN, ho⟩ := key c⁻¹ (C.inv_mem hc)
  have hz1 : c⁻¹ * z * c⁻¹⁻¹ = o⁻¹ * z * o := by
    calc c⁻¹ * z * c⁻¹⁻¹ = o⁻¹ * (o * (c⁻¹ * z * c⁻¹⁻¹) * o⁻¹) * o := by group
      _ = o⁻¹ * z * o := by rw [ho]
  have e : z⁻¹ * c⁻¹ * z * c = z⁻¹ * (c⁻¹ * z * c⁻¹⁻¹) := by group
  rw [e, hz1]
  have h2 : z⁻¹ * o⁻¹ * z⁻¹⁻¹ ∈ N := Balance.conj_mem_oddCoreIn (X.inv_mem hzX) (N.inv_mem hoN)
  have e2 : z⁻¹ * (o⁻¹ * z * o) = (z⁻¹ * o⁻¹ * z⁻¹⁻¹) * o := by group
  rw [e2]
  exact hNC (N.mul_mem h2 hoN)

theorem mem_zStarOf_of_classical_layer [IsSimpleGroup G]
    (h : Hyp25A7 Ω K K' W S R R' z t u₁ u₂) {a : G} (ha1 : a ≠ 1) {L : Subgroup G}
    (hRL : R ≤ L) (hL : Hat2A7.IsClassical2A7 (Subgroup.centralizer ({a} : Set G)) L z) :
    z ∈ zStarOf (Subgroup.centralizer ({a} : Set G)) := by
  classical
  set C : Subgroup G := Subgroup.centralizer ({a} : Set G) with hC
  have hB : Hat2A7.CITBelow2A7 (Nat.card G) := h.std.1.stand.below
  have hCne : C ≠ ⊤ := by
    intro htop
    apply ha1
    refine Hat2A7.center_trivial_of_simple h.std.1.stand.nonabelian a fun y => ?_
    have hy : y ∈ C := htop ▸ Subgroup.mem_top y
    exact (Subgroup.mem_centralizer_singleton_iff.mp hy).symm
  set X : Subgroup G := Hat2A7.normalClosureIn2A7 C L with hX
  have hLC : L ≤ C := hL.le
  have hXC : X ≤ C := Hat2A7.normalClosureIn2A7_le hLC
  have hLX : L ≤ X := Hat2A7.le_normalClosureIn2A7
  have hXne : X ≠ ⊤ := fun h' => hCne (top_le_iff.mp (h' ▸ hXC))
  have hlt : Nat.card X < Nat.card G := Hat2A7.card_lt_of_ne_top' hXne
  let Λ : Set (Subgroup G) := (fun c => L.map (MulAut.conj c).toMonoidHom) '' (C : Set G)
  have hY : ⨆ M ∈ Λ, M = X := by
    simp only [Λ, iSup_image]
    rfl
  have hLΛ : L ∈ Λ := ⟨1, C.one_mem, Hat2A7.map_conj_one L⟩
  have hinv : ∀ y ∈ X, ∀ M ∈ Λ, M.map (MulAut.conj y).toMonoidHom ∈ Λ := by
    rintro y hy _ ⟨c, hc, rfl⟩
    refine ⟨y * c, C.mul_mem (hXC hy) hc, ?_⟩
    exact (Balance.map_map_conj L c y).symm
  have hcls : ∀ M ∈ Λ, ∃ u : G, Hat2A7.IsClassical2A7 C M u := by
    rintro _ ⟨c, hc, rfl⟩
    have h1 := hL.conj c
    rw [Hat2A7.map_conj_eq_of_mem hc] at h1
    exact ⟨_, h1⟩
  have hS : Hat2A7.A7SystemMod (Hat2A7.restrictTo Λ X) :=
    Hat2A7.a7SystemMod_of_lt hB hXC hlt ⟨L, hLΛ⟩ hY hinv hcls
  refine mem_zStarOf_of_section h (hRL.trans hLX) hXC ?_ ?_
  · intro c hc x hx
    have hmap : ∀ d ∈ C, X.map (MulAut.conj d).toMonoidHom ≤ X := by
      intro d hd
      refine Subgroup.map_le_iff_le_comap.mpr (Hat2A7.normalClosureIn2A7_le_of fun e he => ?_)
      refine Subgroup.map_le_iff_le_comap.mp ?_
      rw [Balance.map_map_conj]
      exact Hat2A7.map_conj_le_normalClosureIn2A7 (C.mul_mem hd he)
    exact hmap c hc ⟨x, hx, rfl⟩
  · intro c hc y hy
    have hcl : Hat2A7.IsClassical2A7 C (L.map (MulAut.conj c).toMonoidHom) (c * z * c⁻¹) := by
      have h1 := hL.conj c
      rw [Hat2A7.map_conj_eq_of_mem hc] at h1
      exact h1
    exact Hat2A7.commutator_mem_oddCoreIn_of_system hS hY (L := L.map (MulAut.conj c).toMonoidHom)
      ⟨c, hc, rfl⟩ hcl.mem (fun e he => hcl.mul_comm_of_mem he) hy

end Wrap

end CFSG.ClassicalInvolution.Hat2A7S
