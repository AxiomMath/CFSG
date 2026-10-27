module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII203ZGlauber
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII203ZKey

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameCore)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

open Out


section Frame203ZTwo

variable {G : Type} [Group G] [Finite G] [FrameCore G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

abbrev N203X (K K' : Subgroup G) (z : G) : Subgroup ↥(X203 K K' z) :=
  (N203 K K' z).subgroupOf (X203 K K' z)

abbrev P203X (S : Sylow 2 G) (K K' : Subgroup G) (z : G) : Subgroup ↥(X203 K K' z) :=
  ((S : Subgroup G) ⊓ X203 K K' z).subgroupOf (X203 K K' z)

theorem padicValNat_index_N203_le_one (d : Std20Frame K K' J S R R' W V z t) :
    padicValNat 2 (N203X K K' z).index ≤ 1 := by
  obtain ⟨v₀, hv₀V, hgen, hv₀v₀, hvt⟩ := exists_gen_V d
  have hv₀X : v₀ ∈ X203 K K' z := V_le_X203 d hv₀V
  have hv₀P : v₀ ∈ (S : Subgroup G) ⊓ X203 K K' z := ⟨d.hVS hv₀V, hv₀X⟩
  have hv₀N : v₀ ∉ N203 K K' z := not_mem_N203_of_outer d hv₀V hv₀v₀
  have htN : t ∈ N203 K K' z := Subgroup.mem_sup_right d.htKK
  haveI hN : (N203X K K' z).Normal :=
    ⟨fun n hn g => Subgroup.mem_subgroupOf.mpr (by
      have hn' : (n : G) ∈ N203 K K' z := Subgroup.mem_subgroupOf.mp hn
      simpa using conj_mem_N203 d g.2 hn')⟩
  obtain ⟨vX, hvX⟩ : ∃ vX : ↥(X203 K K' z), (vX : G) = v₀ := ⟨⟨v₀, hv₀X⟩, rfl⟩
  have hXeq : X203 K K' z =
      (⨆ c ∈ Subgroup.centralizer ({z} : Set G), conjSub c V) ⊔ (K ⊔ K') :=
    Std20Frame.sec20X_eq d
  have hcoe : ∀ x : ↥(X203 K K' z),
      ((x⁻¹ * vX * x : ↥(X203 K K' z)) : G) = (x : G)⁻¹ * v₀ * (x : G) :=
    fun x => by simp [hvX]
  have hPsyl : IsSylow2In ((P203X S K K' z).map (QuotientGroup.mk' (N203X K K' z))) ⊤ := by
    have h := Hall196.isSylow2In_map_hom (QuotientGroup.mk' (N203X K K' z))
      (isSylow2In_top_subgroupOf d)
    rwa [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h
  have hzP : (QuotientGroup.mk vX : ↥(X203 K K' z) ⧸ N203X K K' z) ∈
      (P203X S K K' z).map (QuotientGroup.mk' (N203X K K' z)) :=
    Subgroup.mem_map.mpr ⟨vX, Subgroup.mem_subgroupOf.mpr (by rw [hvX]; exact hv₀P), rfl⟩
  have hz2 : (QuotientGroup.mk vX : ↥(X203 K K' z) ⧸ N203X K K' z) * QuotientGroup.mk vX = 1 := by
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr (by rw [Subgroup.coe_mul, hvX, hvt]; exact htN)
  have hz1 : (QuotientGroup.mk vX : ↥(X203 K K' z) ⧸ N203X K K' z) ≠ 1 := by
    intro h
    rw [QuotientGroup.eq_one_iff] at h
    apply hv₀N
    rw [← hvX]
    exact Subgroup.mem_subgroupOf.mp h
  have Qmem : ∀ u : ↥(X203 K K' z), (u : G) ∈ N203 K K' z ⊔ V →
      QuotientGroup.mk (s := N203X K K' z) u = 1 ∨
        QuotientGroup.mk (s := N203X K K' z) u = QuotientGroup.mk (s := N203X K K' z) vX := by
    intro u hu
    obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_decomp_of_normalizes
      (fun b' hb' a' ha' => conj_mem_N203 d (V_le_X203 d hb') ha') hu
    obtain ⟨k, rfl⟩ := hgen b hb
    have haX : a ∈ X203 K K' z := N203_le_X203 K K' z ha
    have hvkX : v₀ ^ k ∈ X203 K K' z := zpow_mem hv₀X k
    have hu' : u = (⟨a, haX⟩ : ↥(X203 K K' z)) * ⟨v₀ ^ k, hvkX⟩ := Subtype.ext hab
    have hvk' : (⟨v₀ ^ k, hvkX⟩ : ↥(X203 K K' z)) = vX ^ k :=
      Subtype.ext (by rw [Subgroup.coe_zpow, hvX])
    have ha1 : QuotientGroup.mk (⟨a, haX⟩ : ↥(X203 K K' z)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr ha)
    rw [hu', QuotientGroup.mk_mul, ha1, one_mul, hvk', QuotientGroup.mk_zpow]
    exact zpow_eq_one_or_self_203Z hz2 k
  have Qlem : ∀ x : ↥(X203 K K' z),
      ((x⁻¹ * vX * x : ↥(X203 K K' z)) : G) ∈ N203 K K' z ⊔ ((S : Subgroup G) ⊓ X203 K K' z) →
      QuotientGroup.mk (s := N203X K K' z) (x⁻¹ * vX * x : ↥(X203 K K' z)) =
        QuotientGroup.mk (s := N203X K K' z) vX := by
    intro x hx
    have hu : ((x⁻¹ * vX * x : ↥(X203 K K' z)) : G) ∈ N203 K K' z ⊔ V := by
      rw [hcoe]
      rw [hcoe] at hx
      exact conj_mem_N203_sup_V_of_mem d hv₀V hgen hx
    rcases Qmem _ hu with h1 | h1
    · exfalso
      rw [QuotientGroup.eq_one_iff] at h1
      have hh : (x : G)⁻¹ * v₀ * (x : G) ∈ N203 K K' z := by
        rw [← hcoe]
        exact Subgroup.mem_subgroupOf.mp h1
      have h2 := conj_mem_N203 d x.2 hh
      have e2 : (x : G) * ((x : G)⁻¹ * v₀ * (x : G)) * (x : G)⁻¹ = v₀ := by group
      rw [e2] at h2
      exact hv₀N h2
    · exact h1
  have hcent : ∀ p ∈ (P203X S K K' z).map (QuotientGroup.mk' (N203X K K' z)),
      p * QuotientGroup.mk vX = QuotientGroup.mk vX * p := by
    intro p hp
    obtain ⟨p', hp', rfl⟩ := Subgroup.mem_map.mp hp
    have hp'P : (p' : G) ∈ (S : Subgroup G) ⊓ X203 K K' z := Subgroup.mem_subgroupOf.mp hp'
    have hm : (((p'⁻¹)⁻¹ * vX * p'⁻¹ : ↥(X203 K K' z)) : G) ∈
        (S : Subgroup G) ⊓ X203 K K' z := by
      rw [hcoe]
      simp only [Subgroup.coe_inv, inv_inv]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hp'P hv₀P) (Subgroup.inv_mem _ hp'P)
    have hc : QuotientGroup.mk (s := N203X K K' z) (p' * vX * p'⁻¹ : ↥(X203 K K' z)) =
        QuotientGroup.mk (s := N203X K K' z) vX := by
      have h := Qlem p'⁻¹ (Subgroup.mem_sup_right hm)
      simpa using h
    have h1 : QuotientGroup.mk (s := N203X K K' z) p' * QuotientGroup.mk vX *
        (QuotientGroup.mk (s := N203X K K' z) p')⁻¹ = QuotientGroup.mk vX := by
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      exact hc
    show QuotientGroup.mk p' * QuotientGroup.mk vX = QuotientGroup.mk vX * QuotientGroup.mk p'
    exact mul_inv_eq_iff_eq_mul.mp h1
  have hweak : ∀ g : ↥(X203 K K' z) ⧸ N203X K K' z,
      g⁻¹ * QuotientGroup.mk vX * g ∈ (P203X S K K' z).map (QuotientGroup.mk' (N203X K K' z)) →
      g⁻¹ * QuotientGroup.mk vX * g = QuotientGroup.mk vX := by
    intro g hg
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    have hxe : (QuotientGroup.mk x : ↥(X203 K K' z) ⧸ N203X K K' z)⁻¹ * QuotientGroup.mk vX *
        QuotientGroup.mk x = QuotientGroup.mk (x⁻¹ * vX * x : ↥(X203 K K' z)) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hxe] at hg ⊢
    obtain ⟨p, hp, hpe⟩ := Subgroup.mem_map.mp hg
    have hpe' : QuotientGroup.mk p = QuotientGroup.mk (x⁻¹ * vX * x : ↥(X203 K K' z)) := hpe
    have hrel : p⁻¹ * (x⁻¹ * vX * x) ∈ N203X K K' z := QuotientGroup.eq.mp hpe'
    have hrelG : ((p⁻¹ * (x⁻¹ * vX * x) : ↥(X203 K K' z)) : G) ∈ N203 K K' z :=
      Subgroup.mem_subgroupOf.mp hrel
    have hpP : (p : G) ∈ (S : Subgroup G) ⊓ X203 K K' z := Subgroup.mem_subgroupOf.mp hp
    apply Qlem x
    have e : ((x⁻¹ * vX * x : ↥(X203 K K' z)) : G) =
        (p : G) * ((p⁻¹ * (x⁻¹ * vX * x) : ↥(X203 K K' z)) : G) := by
      simp
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hpP) (Subgroup.mem_sup_left hrelG)
  have hgen' : ∀ q : ↥(X203 K K' z) ⧸ N203X K K' z,
      q ∈ Subgroup.closure {x | ∃ g : ↥(X203 K K' z) ⧸ N203X K K' z,
        x = g * QuotientGroup.mk vX * g⁻¹} := by
    set T := Subgroup.closure {x : ↥(X203 K K' z) ⧸ N203X K K' z |
      ∃ g : ↥(X203 K K' z) ⧸ N203X K K' z, x = g * QuotientGroup.mk vX * g⁻¹} with hT
    have hzT : (QuotientGroup.mk vX : ↥(X203 K K' z) ⧸ N203X K K' z) ∈ T :=
      Subgroup.subset_closure ⟨1, by simp⟩
    let Ψ : Subgroup G := (T.comap (QuotientGroup.mk' (N203X K K' z))).map (X203 K K' z).subtype
    have hmemT : ∀ w (hw : w ∈ X203 K K' z), w ∈ Ψ →
        (QuotientGroup.mk (⟨w, hw⟩ : ↥(X203 K K' z)) : ↥(X203 K K' z) ⧸ N203X K K' z) ∈ T := by
      intro w hw hwΨ
      obtain ⟨y, hy, hyw⟩ := Subgroup.mem_map.mp hwΨ
      have hyeq : y = ⟨w, hw⟩ := Subtype.ext hyw
      rw [← hyeq]
      exact hy
    have hmkΨ : ∀ y : ↥(X203 K K' z),
        (QuotientGroup.mk y : ↥(X203 K K' z) ⧸ N203X K K' z) ∈ T → (y : G) ∈ Ψ :=
      fun y hy => Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    have hNΨ : ∀ w ∈ N203 K K' z, w ∈ Ψ := by
      intro w hwN
      have hwX : w ∈ X203 K K' z := N203_le_X203 K K' z hwN
      apply hmkΨ ⟨w, hwX⟩
      have h1 : (QuotientGroup.mk (⟨w, hwX⟩ : ↥(X203 K K' z)) :
          ↥(X203 K K' z) ⧸ N203X K K' z) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hwN)
      rw [h1]
      exact T.one_mem
    have hXΨ : X203 K K' z ≤ Ψ := by
      rw [hXeq]
      refine sup_le (iSup₂_le fun c hc => ?_) (sup_le (fun w hw => hNΨ w (K_le_N203 K K' z hw))
        (fun w hw => hNΨ w (K'_le_N203 K K' z hw)))
      intro w hw
      have hUX : conjSub c V ≤ X203 K K' z := by
        rw [hXeq]
        exact le_trans (le_iSup₂ (f := fun c (_ : c ∈ Subgroup.centralizer ({z} : Set G)) =>
          conjSub c V) c hc) le_sup_left
      have hU : conjSub c V ∈ USet (CoreAssembly.conjClass K) :=
        USet.conj d.hyp.conjInvariant d.hV c
      obtain ⟨y, hyX, hyU⟩ := exists_conj_mem_N203_sup_V d hU hUX
      have hwX : w ∈ X203 K K' z := hUX hw
      have hw' : y⁻¹ * w * y ∈ N203 K K' z ⊔ V := hyU w hw
      have hw'X : y⁻¹ * w * y ∈ X203 K K' z :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hyX) hwX) hyX
      apply hmkΨ ⟨w, hwX⟩
      have e : (QuotientGroup.mk (⟨w, hwX⟩ : ↥(X203 K K' z)) :
          ↥(X203 K K' z) ⧸ N203X K K' z) =
          QuotientGroup.mk (⟨y, hyX⟩ : ↥(X203 K K' z)) *
            QuotientGroup.mk (⟨y⁻¹ * w * y, hw'X⟩ : ↥(X203 K K' z)) *
            (QuotientGroup.mk (⟨y, hyX⟩ : ↥(X203 K K' z)))⁻¹ := by
        rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e]
      rcases Qmem ⟨y⁻¹ * w * y, hw'X⟩ hw' with h | h
      · rw [h, mul_one, mul_inv_cancel]
        exact T.one_mem
      · rw [h]
        exact Subgroup.subset_closure ⟨QuotientGroup.mk (⟨y, hyX⟩ : ↥(X203 K K' z)), rfl⟩
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact hmemT x x.2 (hXΨ x.2)
  rw [Subgroup.index_eq_card]
  exact padicValNat_card_le_one_of_zStar hPsyl hzP hz1 hz2 hcent hweak hgen'

end Frame203ZTwo

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

end
