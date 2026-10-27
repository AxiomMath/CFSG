module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFTorus
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFStmts
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFTorusTrA
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFTorusTrQ

public section

namespace CFSG.LocalAnalysis.RankThreeUC

attribute [local instance] f2Module

open CFSG.Open CFSG.Quasithin Subgroup

variable {V : Type} [CommGroup V] [Finite V]

section Glue

variable [IsF2Space V]

theorem torusStep_of_secData
    {L D Θ : Subgroup (MulAut V)} {M₀ M₁ : Subgroup V} {c : ℕ}
    {Θi : Fin c → Subgroup (MulAut V)} {w θ₀ : MulAut V} {π : Equiv.Perm (Fin c)}
    (hS : TorusSetting L D M₀ M₁) (hT : IsTorusData L c Θ Θi w θ₀ π) (hc : 3 ≤ c)
    (i₀ : Fin c) {m : Polynomial (ZMod 2)} (hm : Irreducible m) (hd : 2 ≤ m.natDegree)
    (W : Fin c → Subgroup (Sec M₁ M₀)) (hWind : iSupIndep W) (hWtop : ⨆ i, W i = ⊤)
    (hWstab : ∀ i, ∀ g (hg : g ∈ L), g ∈ Θ → ∀ s ∈ W i,
      secAct L hS.inv hS.stab₀ ⟨g, hg⟩ s ∈ W i)
    (hWfix : ∀ j, ∀ s : Sec M₁ M₀, (∀ g (hg : g ∈ L), g ∈ Θi j →
      secAct L hS.inv hS.stab₀ ⟨g, hg⟩ s = s) → s ∈ W j)
    (hWtriv : ∀ j, ∀ g (hg : g ∈ L), g ∈ Θi j → ∀ s ∈ W j,
      secAct L hS.inv hS.stab₀ ⟨g, hg⟩ s = s)
    (hWkill : ∀ s ∈ W i₀,
      polyAct (secAct L hS.inv hS.stab₀ ⟨θ₀, hT.le_L hT.θ₀_mem⟩) m s = 1)
    (hWcard : Nat.card ↥(W i₀) ≤ 2 ^ m.natDegree)
    {e : ℕ} (he : e ≤ 2)
    (hcount : Nat.card (commV L) ≤
      e * Nat.card (autSub D (commV L)) * Nat.card ↥(commV L ⊓ fixV D)) :
    commV L ≤ fixV D := by
  classical
  have hΘL := hT.le_L
  have hΘ : IsThetaFamily Θ Θi := hT.isThetaFamily
  have hM₁L : ∀ g ∈ L, ∀ x ∈ M₁, g x ∈ M₁ := fun g hg x hx => (hS.inv hg x).2 hx
  have hM₀L : ∀ g ∈ L, ∀ x ∈ M₀, g x ∈ M₀ := fun g hg x hx => (hS.stab₀ hg x).2 hx
  have hM₁Θ : ∀ g ∈ Θ, ∀ x ∈ M₁, g x ∈ M₁ := fun g hg => hM₁L g (hΘL hg)
  have hM₀Θ : ∀ g ∈ Θ, ∀ x ∈ M₀, g x ∈ M₀ := fun g hg => hM₀L g (hΘL hg)
  have hUL : ∀ g ∈ L, ∀ u ∈ commV L, g u ∈ commV L := fun g hg u hu =>
    (commV_stab (le_normalizer_self L hg) u).2 hu
  have hgd : ∀ d ∈ D, ∀ g ∈ L, ∀ y : V, d (g y) = g (d y) := by
    intro d hd' g hg y
    have := congrArg (fun φ : MulAut V => φ y) (hS.DL d hd' g hg)
    simpa using this
  have hYL : ∀ g ∈ L, ∀ y ∈ commV L ⊓ fixV D, g y ∈ commV L ⊓ fixV D := by
    intro g hg y hy
    refine ⟨hUL g hg y hy.1, fun d hd' => ?_⟩
    rw [hgd d hd' g hg y, hy.2 d hd']
  have hYΘ : ∀ g ∈ Θ, ∀ y ∈ commV L ⊓ fixV D, g y ∈ commV L ⊓ fixV D :=
    fun g hg => hYL g (hΘL hg)
  have hYM : commSub (commV L ⊓ fixV D) Θ ≤ M₁ := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨θ, hθ, y, hy, rfl⟩
    exact hS.triv_top θ (hΘL hθ) y hy
  have hM₀fix : ∀ z ∈ M₀, ∀ g ∈ L, g z = z := by
    intro z hz g hg
    have := hS.triv₀ g hg z hz
    rwa [Subgroup.mem_bot, mul_inv_eq_one] at this
  have hbot : commSub M₁ Θ ⊓ M₀ = ⊥ := by
    rw [commSub_inf_of_le hT.odd hM₁Θ hM₀Θ hS.le, commSub_eq_bot_iff]
    exact fun z hz g hg => hM₀fix z hz g (hΘL hg)
  have hYM' : commSub (commV L ⊓ fixV D) Θ ≤ commSub M₁ Θ :=
    commSub_le_commSub_of_le hT.odd hYΘ hM₁Θ hYM
  have hmemW : ∀ x ∈ Rsub Θ (Θi i₀) (commV L ⊓ fixV D), qv M₀ M₁ x ∈ W i₀ := by
    intro x hx
    refine hWfix i₀ _ fun g hg hgΘ => ?_
    rw [qv_act hS.inv hS.stab₀ hg (hYM hx.1), hx.2 g hgΘ]
  refine torus_main hT hc i₀ hS.simple hS.nonab hS.Dcomm hS.Dsq hS.DL hm hd ?_ ?_ ?_ he hcount
  ·
    intro x hx
    have hxM : x ∈ M₁ := hYM hx.1
    have hθ₀L : θ₀ ∈ L := hΘL hT.θ₀_mem
    have hcomm : ∀ θ ∈ Θ, ∀ z : V, θ (polyAct θ₀ m z) = polyAct θ₀ m (θ z) := by
      intro θ hθ z
      exact polyAct_comm (by
        have := hT.comm θ hθ θ₀ hT.θ₀_mem
        exact this) m z
    have hyY : polyAct θ₀ m x ∈ commSub (commV L ⊓ fixV D) Θ :=
      map_commSub_le (polyActHom θ₀ m) (fun θ hθ z => (hcomm θ hθ z).symm)
        (fun z hz => polyAct_mem (θ := θ₀) (fun u hu => hYL θ₀ hθ₀L u hu) m hz) x hx.1
    have hyM : polyAct θ₀ m x ∈ M₁ := hYM hyY
    have hq : qv M₀ M₁ (polyAct θ₀ m x) = 1 := by
      let θA : MulAut ↥M₁ := resHom M₁ ⟨θ₀, hS.inv hθ₀L⟩
      let qm : ↥M₁ →* Sec M₁ M₀ := QuotientGroup.mk' (M₀.subgroupOf M₁)
      have h1 := polyAct_map M₁.subtype (θA := θA) (θB := θ₀) (fun z => rfl) m ⟨x, hxM⟩
      have h2 := polyAct_map qm (θA := θA)
        (θB := secAct L hS.inv hS.stab₀ ⟨θ₀, hθ₀L⟩)
        (fun z => (secAct_mk L hS.inv hS.stab₀ ⟨θ₀, hθ₀L⟩ z).symm) m ⟨x, hxM⟩
      have h3 : qv M₀ M₁ (polyAct θ₀ m x) = qm (polyAct θA m ⟨x, hxM⟩) := by
        have h4 : polyAct θ₀ m x = ((polyAct θA m ⟨x, hxM⟩ : ↥M₁) : V) := h1.symm
        rw [h4, qv_of_mem (polyAct θA m ⟨x, hxM⟩).2]
        rfl
      rw [h3, h2]
      have hxW : qm ⟨x, hxM⟩ ∈ W i₀ := by
        have := hmemW x hx
        rwa [qv_of_mem hxM] at this
      exact hWkill _ hxW
    have hyM₀ : polyAct θ₀ m x ∈ M₀ := (qv_eq_one_iff hyM).mp hq
    have : polyAct θ₀ m x ∈ commSub M₁ Θ ⊓ M₀ := ⟨hYM' hyY, hyM₀⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  ·
    intro x hx
    have hxM₁ : x ∈ M₁ := hYM hx
    have hxS : x ∈ commSub M₁ Θ := hYM' hx
    obtain ⟨f, hfW, hfprod⟩ :=
      exists_prod_of_mem_iSup W (hWtop ▸ Subgroup.mem_top (qv M₀ M₁ x))
    have havg : ∀ j, avgMap (Θi j) x ∈ M₁ ∧ qv M₀ M₁ (avgMap (Θi j) x) = f j := by
      intro j
      haveI : Fintype ↥(Θi j) := Fintype.ofFinite _
      have hmem : avgMap (Θi j) x ∈ M₁ :=
        avgMap_mem (fun g hg w hw => hM₁Θ g (hΘ.Θi_le j hg) w hw) hxM₁
      refine ⟨hmem, ?_⟩
      rw [avgMap_apply, qv_prod Finset.univ _ (fun g _ => hM₁Θ g.1 (hΘ.Θi_le j g.2) x hxM₁)]
      let ρ' : ↥(Θi j) →* MulAut (Sec M₁ M₀) :=
        (secAct L hS.inv hS.stab₀).comp (Subgroup.inclusion ((hΘ.Θi_le j).trans hΘL))
      have hGodd : Odd (Fintype.card ↥(Θi j)) := by
        rw [← Nat.card_eq_fintype_card]
        exact Odd.of_dvd_nat hΘ.odd (Subgroup.card_dvd_of_le (hΘ.Θi_le j))
      have key := prod_act_eq_component W hWind hGodd ρ' j IsF2Space.sq_eq_one
        (fun i g s hs => hWstab i g.1 (hΘL (hΘ.Θi_le j g.2)) (hΘ.Θi_le j g.2) s hs)
        (fun g s hs => hWtriv j g.1 (hΘL (hΘ.Θi_le j g.2)) g.2 s hs)
        (fun s hs => hWfix j s fun g hg hgΘ => hs ⟨g, hgΘ⟩) f hfW
      rw [hfprod] at key
      rw [← key]
      refine Finset.prod_congr rfl fun g _ => ?_
      exact (qv_act hS.inv hS.stab₀ (hΘL (hΘ.Θi_le j g.2)) hxM₁).symm
    have hEE : EE Θi x = ∏ j, avgMap (Θi j) x := by
      unfold EE
      rw [MonoidHom.finset_prod_apply]
    have hEEM : EE Θi x ∈ M₁ := by
      rw [hEE]
      exact Subgroup.prod_mem _ fun j _ => (havg j).1
    have hqEE : qv M₀ M₁ (EE Θi x) = qv M₀ M₁ x := by
      rw [hEE, qv_prod Finset.univ _ (fun j _ => (havg j).1)]
      simp only [fun j => (havg j).2]
      exact hfprod
    have hz1 : EE Θi x * x⁻¹ ∈ commSub M₁ Θ :=
      (commSub M₁ Θ).mul_mem (EE_mem hΘ hM₁Θ hxS) ((commSub M₁ Θ).inv_mem hxS)
    have hxinv : x⁻¹ ∈ M₁ := M₁.inv_mem hxM₁
    have hz0 : EE Θi x * x⁻¹ ∈ M₀ := by
      have h1 : qv M₀ M₁ (EE Θi x * x⁻¹) = 1 := by
        rw [qv_mul hEEM hxinv, qv_inv hxM₁, hqEE, mul_inv_cancel]
      exact (qv_eq_one_iff (M₁.mul_mem hEEM hxinv)).mp h1
    have hz : EE Θi x * x⁻¹ ∈ commSub M₁ Θ ⊓ M₀ := ⟨hz1, hz0⟩
    rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at hz
    exact hz
  ·
    let φ : ↥(Rsub Θ (Θi i₀) (commV L ⊓ fixV D)) → ↥(W i₀) :=
      fun x => ⟨qv M₀ M₁ x.1, hmemW x.1 x.2⟩
    have hφ : Function.Injective φ := by
      intro x x' hxx
      have h1 : qv M₀ M₁ x.1 = qv M₀ M₁ x'.1 := congrArg Subtype.val hxx
      have hx1 : x.1 ∈ M₁ := hYM x.2.1
      have hx2 : x'.1 ∈ M₁ := hYM x'.2.1
      have h2 : x.1⁻¹ * x'.1 ∈ M₀ := (qv_eq_iff hx1 hx2).mp h1
      have h3 : x.1⁻¹ * x'.1 ∈ commSub M₁ Θ :=
        (commSub M₁ Θ).mul_mem ((commSub M₁ Θ).inv_mem (hYM' x.2.1)) (hYM' x'.2.1)
      have h4 : x.1⁻¹ * x'.1 ∈ commSub M₁ Θ ⊓ M₀ := ⟨h3, h2⟩
      rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at h4
      exact Subtype.ext h4
    exact (Nat.card_le_card_of_injective φ hφ).trans hWcard

end Glue

end CFSG.LocalAnalysis.RankThreeUC
