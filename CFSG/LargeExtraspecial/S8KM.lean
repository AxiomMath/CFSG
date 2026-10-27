module

public import CFSG.LargeExtraspecial.S8KL
public import CFSG.LargeExtraspecial.S8KK

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent
attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem exists_range_lift {N : Type*} [AddCommGroup N] [Module (ZMod 2) N]
    (f g : N →ₗ[ZMod 2] N) (h : LinearMap.ker f ≤ LinearMap.ker g) :
    ∃ θ : LinearMap.range f →ₗ[ZMod 2] N,
      ∀ x (hx : f x ∈ LinearMap.range f), θ ⟨f x, hx⟩ = g x :=
  ⟨(LinearMap.ker f).liftQ g h ∘ₗ (LinearMap.quotKerEquivRange f).symm.toLinearMap,
    fun x hx => by
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        LinearMap.quotKerEquivRange_symm_apply_image]
      rfl⟩

theorem eq_of_ker_le_of_actsTv {N : Type*} [AddCommGroup N] [Module (ZMod 2) N]
    [FiniteDimensional (ZMod 2) N] {f g : N →ₗ[ZMod 2] N}
    (hk : LinearMap.ker f ≤ LinearMap.ker g) {A B F : Submodule (ZMod 2) N}
    (hfA : A.map f = F) (hgA : A.map g = F) (h2 : 2 ≤ finrank (ZMod 2) F)
    (htv : ∀ (c : F) (μ : Dual (ZMod 2) F), μ c = 0 → ∃ ρ : N →ₗ[ZMod 2] N,
      (∀ x, f (ρ x) = ρ (f x)) ∧ (∀ x, g (ρ x) = ρ (g x)) ∧
        ∀ w : F, ρ w = (w : N) + μ w • (c : N))
    {ρB : N →ₗ[ZMod 2] N} (hfB : ∀ x, f (ρB x) = ρB (f x)) (hgB : ∀ x, g (ρB x) = ρB (g x))
    (hB : B ≤ A.map ρB) (hAB : A ⊔ B = ⊤) : g = f := by
  obtain ⟨θ, hθ⟩ := exists_range_lift f g hk
  have hθ' : ∀ (v : N) (hv : v ∈ LinearMap.range f) (α : N), f α = v → θ ⟨v, hv⟩ = g α := by
    rintro v hv α rfl
    exact hθ α hv
  have hFr : F ≤ LinearMap.range f := hfA ▸ LinearMap.map_le_range
  have hθF : ∀ w : F, θ ⟨w, hFr w.2⟩ ∈ F := by
    intro w
    obtain ⟨α, hα, hαw⟩ : (w : N) ∈ A.map f := hfA.symm ▸ w.2
    rw [hθ' _ _ α hαw, ← hgA]
    exact Submodule.mem_map_of_mem hα
  let θF : F →ₗ[ZMod 2] F := LinearMap.codRestrict F (θ ∘ₗ Submodule.inclusion hFr) hθF
  have hθFv : ∀ w : F, ((θF w : F) : N) = θ ⟨w, hFr w.2⟩ := fun _ => rfl
  have hcomm : ∀ (c : F) (μ : Dual (ZMod 2) F), μ c = 0 →
      ∀ w, θF (w + μ w • c) = θF w + μ (θF w) • c := by
    intro c μ hμ w
    obtain ⟨ρ, hρf, hρg, hρF⟩ := htv c μ hμ
    obtain ⟨y, hy⟩ := hFr w.2
    apply Subtype.ext
    calc ((θF (w + μ w • c) : F) : N)
        = θ ⟨((w + μ w • c : F) : N), hFr (w + μ w • c).2⟩ := rfl
      _ = g (ρ y) := hθ' _ _ (ρ y) (by rw [hρf, hy, hρF w]; rfl)
      _ = ρ (g y) := hρg y
      _ = ρ ((θF w : F) : N) := by rw [hθFv, hθ' _ (hFr w.2) y hy]
      _ = ((θF w : F) : N) + μ (θF w) • (c : N) := hρF (θF w)
      _ = ((θF w + μ (θF w) • c : F) : N) := rfl
  obtain ⟨a, ha⟩ := eq_smul_of_commute_actsTv h2 θF hcomm
  have hgf : ∀ α ∈ A, g α = a • f α := by
    intro α hα
    have hw : f α ∈ F := hfA ▸ Submodule.mem_map_of_mem hα
    have h1 := congrArg (fun φ : F →ₗ[ZMod 2] F => ((φ ⟨f α, hw⟩ : F) : N)) ha
    exact ((hθFv ⟨f α, hw⟩).trans (hθ' _ _ α rfl)).symm.trans h1
  have hA1 : ∀ α ∈ A, g α = f α := by
    refine (zmod2_eq_zero_or_eq_one a).elim (fun h0 => ?_) (fun h1 => ?_)
    · exfalso
      have hF0 : F = ⊥ := by
        rw [← hgA, eq_bot_iff]
        rintro _ ⟨α, hα, rfl⟩
        rw [Submodule.mem_bot, hgf α hα, h0, zero_smul]
      rw [hF0, finrank_bot] at h2
      omega
    · intro α hα
      rw [hgf α hα, h1, one_smul]
  have hB1 : ∀ β ∈ B, g β = f β := by
    intro β hβ
    obtain ⟨α, hα, rfl⟩ := hB hβ
    rw [hgB, hfB, hA1 α hα]
  refine LinearMap.ext fun y => ?_
  have hy : y ∈ A ⊔ B := hAB ▸ Submodule.mem_top
  obtain ⟨α, hα, β, hβ, rfl⟩ := Submodule.mem_sup.mp hy
  rw [map_add, map_add, hA1 α hα, hB1 β hβ]

theorem nqLinC_nqHom_comm [NQHyp S g t] (σ : CMt S t)
    (hσR : ∀ r ∈ Rbar S g t, (σ : S.O) * r * (σ : S.O)⁻¹ * r⁻¹ ∈ Nbar S g t)
    (r : Rbar S g t) (m : NQ S g t) :
    nqHom S g t r (S9.nqLinC σ m) = S9.nqLinC σ (nqHom S g t r m) := by
  refine (nqMk_surjective (S := S) (g := g) (t := t) m).elim fun n hn => ?_
  subst hn
  change nqMk (nConj r (S9.nConjC σ n)) = nqMk (S9.nConjC σ (nConj r n))
  rw [nqMk_eq_iff]
  simp only [S9.coe_nConjC, coe_nConj]
  have hc := hσR r r.2
  have hy := (nConj r (S9.nConjC σ n)).2
  simp only [coe_nConj, S9.coe_nConjC] at hy
  convert NQHyp.comm _ (inv_mem hy) _ hc using 1
  group

theorem nqComm_nqHom (H : Hyp4 S g) [NQHyp S g t] {σ : S.O} (hσK : σ ∈ CMt S t)
    (hσV : ∀ v ∈ Vt S g t, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) (r : Rbar S g t) (v : NQ S g t) :
    nqComm S g t ⟨σ, hσK⟩ (nqHom S g t r v) = nqHom S g t r (nqComm S g t ⟨σ, hσK⟩ v) := by
  have h := nqLinC_nqHom_comm ⟨σ, hσK⟩ (comm_mem_Nbar_of_fix' H hσK hσV) r v
  calc nqComm S g t ⟨σ, hσK⟩ (nqHom S g t r v) =
      S9.nqLinC ⟨σ, hσK⟩ (nqHom S g t r v) + nqHom S g t r v := nqComm_apply _ _
    _ = nqHom S g t r (S9.nqLinC ⟨σ, hσK⟩ v) + nqHom S g t r v :=
        congrArg (· + nqHom S g t r v) h.symm
    _ = nqHom S g t r (S9.nqLinC ⟨σ, hσK⟩ v + v) := (map_add (nqHom S g t r) _ _).symm
    _ = nqHom S g t r (nqComm S g t ⟨σ, hσK⟩ v) := rfl

theorem nqHom_eq_fqHom [NQHyp S g t] (δ : S9.GamF S g t) (hδR : (δ : S.O) ∈ Rbar S g t)
    (w : nqSub S g t (S9.Fbar S g t)) :
    nqHom S g t ⟨δ, hδR⟩ (w : NQ S g t) =
      ((S9.fqHom S g t δ w : nqSub S g t (S9.Fbar S g t)) : NQ S g t) := by
  refine w.2.elim fun n hn => ?_
  have hnF : (n : S.O) ∈ S9.Fbar S g t := hn.1
  have e : w = ⟨nqMk n, ⟨n, hnF, rfl⟩⟩ := Subtype.ext hn.2.symm
  subst e
  rfl

theorem exists_nqHom_eq_of_mem_nqSub_Lbar_mul (H : Hyp4 S g) [NQHyp S g t] {h : S.M}
    (hh : S.ρ h ∈ Rbar S g t) {v : NQ S g t} (hv : v ∈ nqSub S g t (S.Lbar ((h : G) * g))) :
    ∃ w ∈ nqSub S g t (S.Lbar g), nqHom S g t ⟨S.ρ h, hh⟩ w = v := by
  obtain ⟨m, hmL, rfl⟩ := hv
  rw [Lbar_mul S h g] at hmL
  obtain ⟨m₀, hm₀L, hm₀⟩ := hmL
  have hm₀N : m₀ ∈ Nbar S g t := by
    have h1 := inv_conj_mem_Nbar H.conj_mem hh m.2
    have e : (S.ρ h)⁻¹ * (m : S.O) * S.ρ h = m₀ := by
      rw [← hm₀]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rwa [e] at h1
  refine ⟨nqMk ⟨m₀, hm₀N⟩, ⟨⟨m₀, hm₀N⟩, hm₀L, rfl⟩, ?_⟩
  rw [nqHom_mk]
  congr 1
  apply Subtype.ext
  rw [coe_nConj, ← hm₀]
  rfl

theorem nqSub_Lbar_sup_nqSub_Lbar_mul_eq_top (hNo : NoA2 S g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (D : Std H C ht ht1 hVQ) [NQHyp S g t] :
    nqSub S g t (S.Lbar g) ⊔ nqSub S g t (S.Lbar ((D.h : G) * g)) = ⊤ := by
  have hD := timmesfeld_6_5_omega H hNo C ht ht1 hVQ hΩ D.hN0 D.hh D.hb D.hX D.hE
  have hT : ((S2.radFix D.Q ⊥ (bV (mem_Lbar_of_pair H ht D.hh)) : Subgroup _) :
      Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)) = LhmodN S g t D.h := by
    rw [S2.radFix_bot, LhmodN_eq_pointRadical H ht D.hh (mem_Lbar_of_pair H ht D.hh) D.hX D.hE]
  have hB := fixOf_nqRep_eq H hNo C ht ht1 hVQ D.hgen D.hN0 D.hh D.hb D.hX D.hh hT
  have h1 := hD.1
  rw [top_inf_eq, top_inf_eq, fixOf_nqRep_radFix_eq hNo D, hB] at h1
  exact h1

namespace Bad4

variable {D : Std H C ht ht1 hVQ} {τ : S.O} (B : Bad4 D τ)
include B

theorem center_le :
    ∀ x ∈ Nbar S g t, (∀ y ∈ Nbar S g t, y * x = x * y) → x ∈ zpowers t := fun _ hx h =>
  Zbar_le_zpowers B.red.hNo B.red.hΩ D (mem_Zbar.mpr ⟨hx, h⟩)

theorem range_nqComm_eq [NQHyp S g t] {σ : S.O} (hσ : σ ∈ conjCentM S t)
    (hσN : σ ∉ Nbar S g t) :
    LinearMap.range (nqComm S g t ⟨σ, mem_CMt_of_mem_conjCentM hσ⟩) =
      LinearMap.range (nqComm S g t ⟨τ, mem_CMt_of_mem_conjCentM B.mem⟩) := by
  rw [← nqSub_N1bar H _ (B.red.N1bar_spec hσ hσN).1,
    ← nqSub_N1bar H _ (B.red.N1bar_spec B.mem B.not_mem).1, B.N1bar_eq hσ hσN]

theorem ker_nqComm_eq' [NQHyp S g t] {σ : S.O} (hσ : σ ∈ conjCentM S t)
    (hσN : σ ∉ Nbar S g t) :
    LinearMap.ker (nqComm S g t ⟨σ, mem_CMt_of_mem_conjCentM hσ⟩) =
      LinearMap.ker (nqComm S g t ⟨τ, mem_CMt_of_mem_conjCentM B.mem⟩) := by
  have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  rw [ker_nqComm_eq htt B.center_le _ (mul_self_of_mem_conjCentM H ht hσ),
    ker_nqComm_eq htt B.center_le _ (mul_self_of_mem_conjCentM H ht B.mem),
    B.range_nqComm_eq hσ hσN]

theorem nqComm_eq [NQHyp S g t] {σ : S.O} (hσ : σ ∈ conjCentM S t) (hσN : σ ∉ Nbar S g t) :
    nqComm S g t ⟨σ, mem_CMt_of_mem_conjCentM hσ⟩ =
      nqComm S g t ⟨τ, mem_CMt_of_mem_conjCentM B.mem⟩ := by
  have R := B.red
  have hσK := mem_CMt_of_mem_conjCentM hσ
  have hτK := mem_CMt_of_mem_conjCentM B.mem
  have hσV := R.fix_Vt hσ
  have hτV := R.fix_Vt B.mem
  have hk := B.ker_nqComm_eq' hσ hσN
  have hτt : τ * t = t * τ := B.mem.2.1
  have hσt : σ * t = t * σ := hσ.2.1
  refine B.mem.2.2.elim fun x hx => hσ.2.2.elim fun y hy => ?_
  have hF4 := finrank_nqSub_Fbar_of_four R.hCE R.hNo R.hΩ D R.hm4 R.hsub hx.1 hx.2 hτt hτV
    B.not_mem (t := t)
  have hFτ := (nqSub_Fbar_eq_of_four R.hCE R.hNo R.hΩ D R.hm4 R.hsub hx.1 hx.2 hτt hτV B.not_mem
    hτK).symm
  have hFσ := (nqSub_Fbar_eq_of_four R.hCE R.hNo R.hΩ D R.hm4 R.hsub hy.1 hy.2 hσt hσV hσN
    hσK).symm
  have h2 : 2 ≤ finrank (ZMod 2) (nqSub S g t (S9.Fbar S g t)) := by rw [hF4]; norm_num
  have htv : ∀ (c : nqSub S g t (S9.Fbar S g t)) (μ : Dual (ZMod 2) (nqSub S g t (S9.Fbar S g t))),
      μ c = 0 → ∃ ρ : NQ S g t →ₗ[ZMod 2] NQ S g t,
        (∀ v, nqComm S g t ⟨τ, hτK⟩ (ρ v) = ρ (nqComm S g t ⟨τ, hτK⟩ v)) ∧
        (∀ v, nqComm S g t ⟨σ, hσK⟩ (ρ v) = ρ (nqComm S g t ⟨σ, hσK⟩ v)) ∧
          ∀ w : nqSub S g t (S9.Fbar S g t), ρ w = (w : NQ S g t) + μ w • (c : NQ S g t) := by
    intro c μ hμ
    refine (forall_actsTv_Fbar_of_four R.hCE R.hNo R.hΩ D R.hm4 R.hsub hx.1 hx.2 hτt hτV
      B.not_mem c μ hμ).elim fun δ hδ => ?_
    have hδR : ((δ : S9.GamF S g t) : S.O) ∈ Rbar S g t := (mem_subgroupOf.mp hδ.1).1
    refine ⟨(nqHom S g t ⟨δ, hδR⟩ : NQ S g t →ₗ[ZMod 2] NQ S g t),
      fun v => nqComm_nqHom H hτK hτV _ v, fun v => nqComm_nqHom H hσK hσV _ v, fun w => ?_⟩
    exact (nqHom_eq_fqHom δ hδR w).trans (congrArg Subtype.val (hδ.2 w))
  have hτB : ∀ v, nqComm S g t ⟨τ, hτK⟩
      ((nqHom S g t ⟨S.ρ D.h, D.hh⟩ : NQ S g t →ₗ[ZMod 2] NQ S g t) v) =
        (nqHom S g t ⟨S.ρ D.h, D.hh⟩ : NQ S g t →ₗ[ZMod 2] NQ S g t)
          (nqComm S g t ⟨τ, hτK⟩ v) := fun v => nqComm_nqHom H hτK hτV _ v
  have hσB : ∀ v, nqComm S g t ⟨σ, hσK⟩
      ((nqHom S g t ⟨S.ρ D.h, D.hh⟩ : NQ S g t →ₗ[ZMod 2] NQ S g t) v) =
        (nqHom S g t ⟨S.ρ D.h, D.hh⟩ : NQ S g t →ₗ[ZMod 2] NQ S g t)
          (nqComm S g t ⟨σ, hσK⟩ v) := fun v => nqComm_nqHom H hσK hσV _ v
  have hB : nqSub S g t (S.Lbar ((D.h : G) * g)) ≤ (nqSub S g t (S.Lbar g)).map
      (nqHom S g t ⟨S.ρ D.h, D.hh⟩ : NQ S g t →ₗ[ZMod 2] NQ S g t) :=
    fun β hβ => exists_nqHom_eq_of_mem_nqSub_Lbar_mul H D.hh hβ
  exact eq_of_ker_le_of_actsTv hk.ge hFτ hFσ h2 htv hτB hσB hB
    (nqSub_Lbar_sup_nqSub_Lbar_mul_eq_top R.hNo R.hΩ D)

end Bad4

end CFSG.LargeExtraspecial.S8
