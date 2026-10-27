module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf7A03
public import CFSG.ClassicalInvolution.Asc77.AscT7C2RFive
public import CFSG.ClassicalInvolution.Asc77.AscS24BDefs
public import CFSG.ClassicalInvolution.Asc77.AscT7XGen

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7C2
open CFSG.ClassicalInvolution.Asc77.T7C2
variable {G : Type} [Group G]
section Frame
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem fixed_of_frame (c : Q3.Q3CL.Thompson.Ctx Ω W)
    {e : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4)}
    (he : ∀ x, x ∈ Thompson.muDelta Ω W ↔ (e x).IsSwap) (F : T7E.Frame4 Ω W)
    (hab : T7D.imgQ F.ρ ≠ T7D.imgQ F.ρ')
    (hcomm : T7D.imgQ F.ρ * T7D.imgQ F.ρ' = T7D.imgQ F.ρ' * T7D.imgQ F.ρ)
    (hac : T7D.imgQ F.ρ * T7D.imgQ F.ρ₃ ≠ T7D.imgQ F.ρ₃ * T7D.imgQ F.ρ) {ε : G} (hε : ε ∈ W)
    (h₁ : F.ρ.r * ε * F.ρ.r⁻¹ = ε) (h₂ : F.ρ'.r * ε * F.ρ'.r⁻¹ = ε)
    (h₃ : F.ρ₃.r * ε * F.ρ₃.r⁻¹ = ε) {R : Subgroup G} (hR : R ∈ DSet Ω W) {r : G} (hr : r ∈ R) :
    r * ε * r⁻¹ = ε := by
  have ha := T7D.imgQ_mem F.ρ
  have ha' := T7D.imgQ_mem F.ρ'
  have ha₃ := T7D.imgQ_mem F.ρ₃
  have hmem : ∀ σ : Thompson.Rep Ω W, σ.r * ε * σ.r⁻¹ = ε →
      T7D.imgQ σ ∈ Thompson.muStab Ω W ε := fun σ h =>
    (c.mem_muStab_iff hε σ.hR σ.hr (q := T7D.imgQ σ) rfl).mpr h
  have hΔ : ∀ x ∈ Thompson.muDelta Ω W, x ∈ Thompson.muStab Ω W ε := fun x hx => by
    have hx' := S4.mem_closure_frame he ha ha' ha₃ hab hcomm hac hx
    refine (Subgroup.closure_le (Thompson.muStab Ω W ε)).mpr ?_ hx'
    rintro y (rfl | rfl | rfl)
    · exact hmem F.ρ h₁
    · exact hmem F.ρ' h₂
    · exact hmem F.ρ₃ h₃
  by_cases hrW : r ∈ W
  · have hWab := Q3.Q3CL.Thompson.commutes_of_mem_WSet c.hΩ c.hW
    rw [mul_inv_eq_iff_eq_mul]
    exact hWab r hrW ε hε
  · have hrq : Thompson.piG W r ∈ muGroup Ω W :=
      Thompson.piG_mem_muGroup (Subgroup.mem_sup_left (Thompson.le_MGrp_of_mem_D hR hr))
    have hx : (⟨Thompson.piG W r, hrq⟩ : ↥(muGroup Ω W)) ∈ Thompson.muDelta Ω W :=
      ⟨R, hR, r, hr, hrW, rfl⟩
    exact (c.mem_muStab_iff hε hR hr (q := ⟨Thompson.piG W r, hrq⟩) rfl).mp (hΔ _ hx)

theorem exists_two_gen_W [CoreLike G] {K K' W : Subgroup G} {S : Sylow 2 G}
    {R R' : Subgroup G} {z u : G} (hs : Hyp23Setting Ω K K' z)
    (hd : Hyp24Data Ω K K' W S R R' z u) (h8 : Nat.card ↥R = 8) :
    ∃ a b : G, a ∈ W ∧ b ∈ W ∧ Subgroup.closure ({a, b} : Set G) = W := by
  have hst : AscStand Ω K := hs.stand
  have hΩ : HypOmegaMod Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hW : W ∈ WSet Ω := hd.hW
  have : Fact (Q3.Q3CL.ClassicalClause Ω) := ⟨hst.cls⟩
  have c : Q3.Q3CL.Thompson.Ctx Ω W := T7D.ctx_of_stand hst hW
  have hWab := Q3.Q3CL.Thompson.commutes_of_mem_WSet hΩ hW
  have hRsyl : IsSylow2In R K := T7C.isSylow2In_of_mem_RSet_of_le hΩ hK hd.hR.1 hd.hR.2.1
  have hR'syl : IsSylow2In R' K' :=
    T7C.isSylow2In_of_mem_RSet_of_le hΩ hK' hd.hR'.1 hd.hR'.2.1
  have hRD : R ∈ DSet Ω W :=
    Q3.Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hW hd.hWS hd.hR.1 hd.hR.2.2
  have hR'D : R' ∈ DSet Ω W :=
    Q3.Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hW hd.hWS hd.hR'.1 hd.hR'.2.2
  obtain ⟨e, F, he, -, -, hFR, -, -, hab, hcomm, hac, -⟩ :=
    T7E.exists_frame4_of_sylow hs hW hd.hS4 hRsyl hR'syl hRD hR'D
  obtain ⟨x₁, x₂, x₃, h₁, h₂, h₃, r₁, r₂, r₃, t₁, t₂, t₃, s₁, s₂, s₃⟩ := F.exists_gens c
  obtain ⟨m, hm, o₁, o₂, o₃, z₁, z₂, z₃⟩ := F.orders c h₁ h₂ h₃
  have hgen : W ≤ Subgroup.closure ({x₁, x₂, x₃} : Set G) :=
    F.W_le_closure c he hab hcomm hac h₁ h₂ h₃ r₂ r₃ t₃
  have m₁ : x₁ ∈ W := (h₁ ▸ Subgroup.mem_zpowers x₁ : x₁ ∈ F.ρ.R ⊓ W).2
  have m₂ : x₂ ∈ W := (h₂ ▸ Subgroup.mem_zpowers x₂ : x₂ ∈ F.ρ'.R ⊓ W).2
  have m₃ : x₃ ∈ W := (h₃ ▸ Subgroup.mem_zpowers x₃ : x₃ ∈ F.ρ₃.R ⊓ W).2
  have hm1 : m = 1 := by
    have h1 := Q3.Q3CL.Thompson.D_card hΩ hW F.ρ.hR
    have h2 : Nat.card ↥(F.ρ.R ⊓ W) = 4 * m := by rw [← h₁, Nat.card_zpowers, o₁]
    rw [h2, hFR, h8] at h1
    omega
  subst hm1
  have c12 : Commute x₁ x₂ := hWab x₁ m₁ x₂ m₂
  have c13 : Commute x₁ x₃ := hWab x₁ m₁ x₃ m₃
  have c23 : Commute x₂ x₃ := hWab x₂ m₂ x₃ m₃
  have o₂' : x₂ ^ 4 = 1 := by simpa [o₂] using pow_orderOf_eq_one x₂
  have o₃' : x₃ ^ 4 = 1 := by simpa [o₃] using pow_orderOf_eq_one x₃
  obtain ⟨hfr, hft, hfs⟩ := e_fixed c12 c13 c23 o₂' o₃' r₁ r₂ r₃ t₁ t₂ t₃ s₁ s₂ s₃
  have hεW : x₁ * x₂⁻¹ * x₃ ^ 2 ∈ W := W.mul_mem (W.mul_mem m₁ (W.inv_mem m₂)) (W.pow_mem m₃ 2)
  have hfix : ∀ R₀ : Subgroup G, R₀ ∈ DSet Ω W → ∀ r : G, r ∈ R₀ →
      r * (x₁ * x₂⁻¹ * x₃ ^ 2) * r⁻¹ = x₁ * x₂⁻¹ * x₃ ^ 2 := fun R₀ hR₀ r hr =>
    fixed_of_frame c he F hab hcomm hac hεW hfr hft hfs hR₀ hr
  have hcent : ∀ n ∈ Subgroup.normalizer (W : Set G),
      n * (x₁ * x₂⁻¹ * x₃ ^ 2) * n⁻¹ = x₁ * x₂⁻¹ * x₃ ^ 2 := by
    intro n hn
    have hn' : n⁻¹ ∈ Subgroup.normalizer (W : Set G) := Subgroup.inv_mem _ hn
    have hfW : n * (x₁ * x₂⁻¹ * x₃ ^ 2) * n⁻¹ ∈ W :=
      (Thompson.mem_normalizer_iff_of_mem hn _).mpr hεW
    have hfixc : ∀ σ : Thompson.Rep Ω W,
        σ.r * (n * (x₁ * x₂⁻¹ * x₃ ^ 2) * n⁻¹) * σ.r⁻¹ = n * (x₁ * x₂⁻¹ * x₃ ^ 2) * n⁻¹ := by
      intro σ
      have hmemD : n⁻¹ * σ.r * n ∈ conjSub n⁻¹ σ.R := by
        rw [mem_conjSub_iff]
        have h1 : (n⁻¹)⁻¹ * (n⁻¹ * σ.r * n) * n⁻¹ = σ.r := by group
        rw [h1]
        exact σ.hr
      have := hfix _ (Q3.Q3CL.Thompson.conjSub_mem_D hΩ σ.hR hn') _ hmemD
      calc σ.r * (n * (x₁ * x₂⁻¹ * x₃ ^ 2) * n⁻¹) * σ.r⁻¹
          = n * ((n⁻¹ * σ.r * n) * (x₁ * x₂⁻¹ * x₃ ^ 2) * (n⁻¹ * σ.r * n)⁻¹) * n⁻¹ := by group
        _ = n * (x₁ * x₂⁻¹ * x₃ ^ 2) * n⁻¹ := by rw [this]
    rcases A3Mod.fixed_eq_one_or c12 c13 c23 o₁ o₂ o₃ (z₁.trans z₂.symm) r₁ r₂ r₃ t₁ t₂ t₃ s₁ s₂
        s₃ (hgen hfW) (hfixc F.ρ) (hfixc F.ρ') (hfixc F.ρ₃) with h | h
    · have h0 : x₁ * x₂⁻¹ * x₃ ^ 2 = 1 := conj_eq_one_iff.mp h
      rw [h0]
      group
    · rw [h, pow_one]
  have hmemC : x₁ * x₂⁻¹ * x₃ ^ 2 ∈ Asc77.centerIn (Subgroup.normalizer (W : Set G)) :=
    mem_centerIn_of_forall (Subgroup.le_normalizer hεW) hcent
  have hmem : x₁ * x₂⁻¹ * x₃ ^ 2 ∈ W ⊓ Asc77.centerIn (Subgroup.normalizer (W : Set G)) :=
    ⟨hεW, hmemC⟩
  rw [hd.hZ] at hmem
  have hε1 : x₁ * x₂⁻¹ * x₃ ^ 2 = 1 := Subgroup.mem_bot.mp hmem
  have hx₂ : x₂ = x₃ ^ 2 * x₁ := by
    calc x₂ = x₃ ^ 2 * (x₁ * x₂⁻¹ * x₃ ^ 2)⁻¹ * x₁ := by group
      _ = x₃ ^ 2 * x₁ := by rw [hε1, inv_one, mul_one]
  refine ⟨x₁, x₃, m₁, m₃, le_antisymm ?_ ?_⟩
  · rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact m₁
    · exact m₃
  · refine hgen.trans ?_
    rw [Subgroup.closure_le]
    have hx₁ : x₁ ∈ Subgroup.closure ({x₁, x₃} : Set G) := Subgroup.subset_closure (by simp)
    have hx₃ : x₃ ∈ Subgroup.closure ({x₁, x₃} : Set G) := Subgroup.subset_closure (by simp)
    rintro y (rfl | rfl | rfl)
    · exact hx₁
    · rw [hx₂]
      exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hx₃ 2) hx₁
    · exact hx₃
end Frame
end T7C2
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7C2
open CFSG.ClassicalInvolution.Asc77.T7C2
section Main
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem genLE_four_of_le_MGrp [CoreLike G] {K K' W : Subgroup G} {S : Sylow 2 G}
    {R R' : Subgroup G} {z u : G} (hs : Hyp23Setting Ω K K' z)
    (hd : Hyp24Data Ω K K' W S R R' z u) (h8 : Nat.card ↥R = 8)
    (hSM : (S : Subgroup G) ≤ MGrp Ω W) {H : Subgroup G} (hH : H ≤ (S : Subgroup G)) :
    GenLE H 4 := by
  have hst : AscStand Ω K := hs.stand
  have hΩ : HypOmegaMod Ω := hst.hyp
  have hW : W ∈ WSet Ω := hd.hW
  have hWab := Q3.Q3CL.Thompson.commutes_of_mem_WSet hΩ hW
  obtain ⟨a, b, ha, hb, hgen⟩ := exists_two_gen_W hs hd h8
  obtain ⟨e⟩ := hd.hS4
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer (W : Set G) :=
    hSM.trans (Thompson.MGrp_le_normalizer Ω W)
  let ι : ↥(S : Subgroup G) →* ↥(Subgroup.normalizer (W : Set G)) := Subgroup.inclusion hSN
  have hψ : ∀ x : ↥(S : Subgroup G), (Thompson.piN W).comp ι x ∈ muGroup Ω W := by
    intro x
    have h1 : (Thompson.piN W).comp ι x = Thompson.piG W (x : G) :=
      (Thompson.piG_of_mem (hSN x.2)).symm
    rw [h1]
    exact Thompson.piG_mem_muGroup (Subgroup.mem_sup_left (hSM x.2))
  let ψ : ↥(S : Subgroup G) →* ↥(muGroup Ω W) :=
    ((Thompson.piN W).comp ι).codRestrict (muGroup Ω W) hψ
  let φ : ↥(S : Subgroup G) →* Equiv.Perm (Fin 4) := e.toMonoidHom.comp ψ
  have hker : φ.ker ≤ W.subgroupOf (S : Subgroup G) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : ψ x = 1 := e.injective (hx.trans (map_one e).symm)
    have h2 : Thompson.piN W (ι x) = 1 := congrArg Subtype.val h1
    have h3 : ((ι x : ↥(Subgroup.normalizer (W : Set G))) : G) ∈ W ⊔ OCW W :=
      (Thompson.piN_eq_one_iff W (ι x)).mp h2
    rw [Subgroup.mem_subgroupOf]
    exact Thompson.inf_sup_OCW_le (Thompson.isPGroup_of_mem_WSet hW) S.isPGroup' ⟨x.2, h3⟩
  have hA : ∀ B : Subgroup ↥(S : Subgroup G), B ≤ W.subgroupOf (S : Subgroup G) →
      GenLE B 2 := by
    intro B hB
    apply GenLE.of_map_injective (Subgroup.subtype_injective (S : Subgroup G))
    refine genLE_two_of_closure_pair ha hb (hWab a ha b hb) hgen ?_
    rintro y ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hB hx)
  have h4 := genLE_four_of_ker S.isPGroup' φ (W.subgroupOf (S : Subgroup G)) hA hker
    (H.subgroupOf (S : Subgroup G))
  exact GenLE.of_subgroupOf hH h4

theorem twoSubgroupsFourGenerated_of_le_MGrp [CoreLike G] {K K' W : Subgroup G}
    {S : Sylow 2 G} {R R' : Subgroup G} {z u : G} (hs : Hyp23Setting Ω K K' z)
    (hd : Hyp24Data Ω K K' W S R R' z u) (h8 : Nat.card ↥R = 8)
    (hSM : (S : Subgroup G) ≤ MGrp Ω W) : TwoSubgroupsFourGenerated G := by
  intro P hP
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := exists_conjSub_eq_of_sylow Q S
  have hle : conjSub g P ≤ (S : Subgroup G) := hg ▸ conjSub_mono hPQ
  have h4 := GenLE.conj (genLE_four_of_le_MGrp hs hd h8 hSM hle) g⁻¹
  have hP' : (conjSub g P).map (MulAut.conj g⁻¹).toMonoidHom = P := conjSub_inv_conjSub g P
  rw [hP'] at h4
  exact h4
end Main
end T7C2
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7X
open CFSG.ClassicalInvolution.Asc77.T7X
section Frame
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

structure Frame24 (Ω : Set (Subgroup G)) (W : Subgroup G) : Type where
  c : Q3.Q3CL.Thompson.Ctx Ω W
  F : T7E.Frame4 Ω W
  φ : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4)
  hφ : ∀ x, x ∈ Thompson.muDelta Ω W ↔ (φ x).IsSwap
  hab : T7D.imgQ F.ρ ≠ T7D.imgQ F.ρ'
  hcomm : T7D.imgQ F.ρ * T7D.imgQ F.ρ' = T7D.imgQ F.ρ' * T7D.imgQ F.ρ
  hac : T7D.imgQ F.ρ * T7D.imgQ F.ρ₃ ≠ T7D.imgQ F.ρ₃ * T7D.imgQ F.ρ
  x₁ : G
  x₂ : G
  x₃ : G
  m : ℕ
  hm : 0 < m
  h₁ : Subgroup.zpowers x₁ = F.ρ.R ⊓ W
  h₂ : Subgroup.zpowers x₂ = F.ρ'.R ⊓ W
  h₃ : Subgroup.zpowers x₃ = F.ρ₃.R ⊓ W
  r₁ : F.ρ.r * x₁ * F.ρ.r⁻¹ = x₁⁻¹
  r₂ : F.ρ.r * x₂ * F.ρ.r⁻¹ = x₂
  r₃ : F.ρ.r * x₃ * F.ρ.r⁻¹ = x₃ * x₁
  t₁ : F.ρ'.r * x₁ * F.ρ'.r⁻¹ = x₁
  t₂ : F.ρ'.r * x₂ * F.ρ'.r⁻¹ = x₂⁻¹
  t₃ : F.ρ'.r * x₃ * F.ρ'.r⁻¹ = x₃ * x₂
  s₁ : F.ρ₃.r * x₁ * F.ρ₃.r⁻¹ = x₁ * x₃
  s₂ : F.ρ₃.r * x₂ * F.ρ₃.r⁻¹ = x₂ * x₃
  s₃ : F.ρ₃.r * x₃ * F.ρ₃.r⁻¹ = x₃⁻¹
  o₁ : orderOf x₁ = 4 * m
  o₂ : orderOf x₂ = 4 * m
  o₃ : orderOf x₃ = 4 * m
  z₁ : x₁ ^ (2 * m) = F.z
  z₂ : x₂ ^ (2 * m) = F.z
  z₃ : x₃ ^ (2 * m) = F.j
  hgen : W ≤ Subgroup.closure ({x₁, x₂, x₃} : Set G)

theorem exists_frame24 [CoreLike G] {K K' : Subgroup G} {S : Sylow 2 G}
    {R R' : Subgroup G} {z u : G} (hs : Hyp23Setting Ω K K' z)
    (hd : Hyp24Data Ω K K' W S R R' z u) :
    ∃ D : Frame24 Ω W, D.F.ρ.K = K ∧ D.F.ρ'.K = K' ∧ D.F.ρ.R = R ∧ D.F.ρ'.R = R' ∧
      D.F.z = z := by
  have hst : AscStand Ω K := hs.stand
  have hΩ : HypOmegaMod Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hW : W ∈ WSet Ω := hd.hW
  have : Fact (Q3.Q3CL.ClassicalClause Ω) := ⟨hst.cls⟩
  have c : Q3.Q3CL.Thompson.Ctx Ω W := T7D.ctx_of_stand hst hW
  have hRsyl : IsSylow2In R K := T7C.isSylow2In_of_mem_RSet_of_le hΩ hK hd.hR.1 hd.hR.2.1
  have hR'syl : IsSylow2In R' K' :=
    T7C.isSylow2In_of_mem_RSet_of_le hΩ hK' hd.hR'.1 hd.hR'.2.1
  have hRD : R ∈ DSet Ω W :=
    Q3.Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hW hd.hWS hd.hR.1 hd.hR.2.2
  have hR'D : R' ∈ DSet Ω W :=
    Q3.Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hW hd.hWS hd.hR'.1 hd.hR'.2.2
  obtain ⟨e, F, he, hFK, hFK', hFR, hFR', hFz, hab, hcomm, hac, -⟩ :=
    T7E.exists_frame4_of_sylow hs hW hd.hS4 hRsyl hR'syl hRD hR'D
  obtain ⟨x₁, x₂, x₃, h₁, h₂, h₃, r₁, r₂, r₃, t₁, t₂, t₃, s₁, s₂, s₃⟩ := F.exists_gens c
  obtain ⟨m, hm, o₁, o₂, o₃, z₁, z₂, z₃⟩ := F.orders c h₁ h₂ h₃
  refine ⟨{
    c := c, F := F, φ := e, hφ := he, hab := hab, hcomm := hcomm, hac := hac,
    x₁ := x₁, x₂ := x₂, x₃ := x₃, m := m, hm := hm, h₁ := h₁, h₂ := h₂, h₃ := h₃,
    r₁ := r₁, r₂ := r₂, r₃ := r₃, t₁ := t₁, t₂ := t₂, t₃ := t₃, s₁ := s₁, s₂ := s₂, s₃ := s₃,
    o₁ := o₁, o₂ := o₂, o₃ := o₃, z₁ := z₁, z₂ := z₂, z₃ := z₃,
    hgen := F.W_le_closure c he hab hcomm hac h₁ h₂ h₃ r₂ r₃ t₃ },
    ?_, ?_, ?_, ?_, ?_⟩
  all_goals assumption
end Frame
end T7X
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace S24B
open CFSG.ClassicalInvolution.Asc77.S24B
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

structure Ctx8 (Ω : Set (Subgroup G)) (K K' W : Subgroup G)
    (S : Sylow 2 G) (R R' : Subgroup G) (z u : G) : Type where
  hs : Hyp23Setting Ω K K' z
  hd : Hyp24Data Ω K K' W S R R' z u
  h8 : Nat.card ↥R = 8
  D : T7X.Frame24 Ω W
  hK : D.F.ρ.K = K
  hK' : D.F.ρ'.K = K'
  hR : D.F.ρ.R = R
  hR' : D.F.ρ'.R = R'
  hz : D.F.z = z

theorem Ctx8.nonempty [CoreLike G] {K K' W : Subgroup G} {S : Sylow 2 G}
    {R R' : Subgroup G} {z u : G} (hs : Hyp23Setting Ω K K' z)
    (hd : Hyp24Data Ω K K' W S R R' z u) (h8 : Nat.card ↥R = 8) :
    Nonempty (Ctx8 Ω K K' W S R R' z u) := by
  obtain ⟨D, hK, hK', hR, hR', hz⟩ := T7X.exists_frame24 hs hd
  exact ⟨⟨hs, hd, h8, D, hK, hK', hR, hR', hz⟩⟩
end S24B
end Asc77

end

end CFSG.ClassicalInvolution.Q8P
