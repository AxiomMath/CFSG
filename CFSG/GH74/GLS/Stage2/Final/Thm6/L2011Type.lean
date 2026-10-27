module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011Aut
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011Z
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011CentS
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011CFTypeStmt

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm6 CFSG.GH74.GLS.Stage2.Final.Thm6.L20 CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage2.Local.P34
open CFSG.GH74.GLS.Stage2.Final.Thm6.SL2Bound (bar_mem_barOf_iff bar_mem_conjugate_iff)
open CFSG.GH74.GLS.Stage2.Final.Thm6.L2012 (F20_conj_mem F20_le_OddCore)


section Tp

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem H0_ne_top {z : G} {S : Subgroup G} (hM : IsCoatom (Cen z)) (hGs : IsSimpleGroup G) {g : G}
    (hg : Case20A z S g) : H0 z g ≠ ⊤ := by
  intro htop
  have hnormal : (F0 z g).Normal := Subgroup.normalizer_eq_top_iff.1 htop
  rcases hGs.eq_bot_or_eq_top_of_normal (F0 z g) with h0 | h1
  · exact hg.inter h0
  · apply hM.1
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ F0 z g := by rw [h1]; trivial
    exact (Subgroup.map_subtype_le _ : OddCore z ≤ Cen z) (F20_le_OddCore z hx.1)

theorem not_central_of_simple {K : Type} [Group K] (hs : IsSimpleGroup K) (hnab : ∃ a b : K, a * b ≠ b * a)
    {x : K} (hx1 : x ≠ 1) : ∃ a : K, a * x ≠ x * a := by
  by_contra hcon
  push Not at hcon
  have hx : x ∈ Subgroup.center K := Subgroup.mem_center_iff.2 fun a => hcon a
  have hcen : (Subgroup.center K) = ⊥ ∨ Subgroup.center K = ⊤ := hs.eq_bot_or_eq_top_of_normal _
  rcases hcen with h | h
  · rw [h] at hx; exact hx1 ((Subgroup.mem_bot).1 hx)
  · obtain ⟨a, b, hab⟩ := hnab
    have : b ∈ Subgroup.center K := by rw [h]; trivial
    exact hab (Subgroup.mem_center_iff.1 this a)

end Tp

section Tp2

variable {G : Type} [Group G] [Finite G]

theorem actB_Z_ne_bot (hcore : CentCoreProp) {z : G} {S : Subgroup G} {g : G} (hJ : JSetup20 z S g)
    {r : ℕ} (hr : r.Prime) {Z : Subgroup G} (hZp : IsPGroup r ↥Z)
    (hcopr : ¬ r ∣ Nat.card ↥⁅pPrimeCoreOf 2 (J0 z g), J0 z g⁆) (hZH : Z ≤ H0 z g)
    (hZN : ∀ g' ∈ normalizer (Z : Set G), g' ∈ Cen z) (hz2 : orderOf z = 2) :
    Yimg (J0_le_H0 z g) (fun _ hh _ hj => J0_conj_mem z g hh hj) Z ≠ ⊥ := by
  intro hbot
  set H := H0 z g with hH
  set J := J0 z g with hJdef
  have hJle : J ≤ H := J0_le_H0 z g
  have hJH : ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J := fun h hh j hj => J0_conj_mem z g hh hj
  have hperf : ⁅J, J⁆ = J := perfect_of_pCompIn hJle hJ.comp
  have hZtriv : ∀ (w : G) (hw : w ∈ Z), actB hJle hJH ⟨w, hZH hw⟩ = 1 := by
    intro w hw
    have : actB hJle hJH ⟨w, hZH hw⟩ ∈ Yimg hJle hJH Z :=
      ⟨⟨w, hZH hw⟩, Subgroup.mem_subgroupOf.2 hw, rfl⟩
    rw [hbot] at this
    exact (Subgroup.mem_bot).1 this
  have hF₁N : ∀ f ∈ Z, ∀ j ∈ J, f * j * f⁻¹ * j⁻¹ ∈ pPrimeCoreOf 2 J := by
    intro f hf j hj
    have h1 := hZtriv f hf
    have h2 := actB_mk hJle hJH ⟨f, hZH hf⟩ ⟨j, hj⟩
    rw [h1] at h2
    have h3 : mkH J ⟨f * j * f⁻¹, hJH f (hZH hf) j hj⟩ = mkH J ⟨j, hj⟩ := h2.symm
    have h4 : mkH J ((⟨f * j * f⁻¹, hJH f (hZH hf) j hj⟩ : ↥J) * (⟨j, hj⟩ : ↥J)⁻¹) = 1 := by
      rw [map_mul, map_inv, h3]; simp
    have h5 := (mkH_eq_one_iff J).1 h4
    exact ⟨_, h5, rfl⟩
  have hcop : Nat.Coprime (Nat.card ↥Z) (Nat.card ↥⁅pPrimeCoreOf 2 J, J⁆) := by
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨n, hn⟩ := hZp.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hr).2 hcopr)
  obtain ⟨-, hcov⟩ := hcore G H J Z hJH hJle hperf hZH hF₁N hcop ⊥ bot_le
    (fun s hs f hf => by rw [(Subgroup.mem_bot).1 hs]; simpa using hf)
  have hzJ' : orderOf (⟨z, hJ.z_mem⟩ : ↥J) = 2 := by
    rw [← hz2]; exact (Subgroup.orderOf_coe (⟨z, hJ.z_mem⟩ : ↥J)).symm
  have hx2 : orderOf (mkH J ⟨z, hJ.z_mem⟩) = 2 := orderOf_mk_eq_two J hzJ'
  have hx1 : mkH J ⟨z, hJ.z_mem⟩ ≠ 1 := by
    intro h; rw [h, orderOf_one] at hx2; omega
  obtain ⟨a, ha⟩ := not_central_of_simple hJ.simple hJ.nonab hx1
  obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥J) a
  obtain ⟨d, hdJ, hdZ, hjd⟩ := hcov (j : G) j.2
  have hdN : d ∈ normalizer (Z : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      have : d * w * d⁻¹ = w := by rw [hdZ w hw]; group
      rw [this]; exact hw
    · intro hw
      have h1 := hdZ _ hw
      have hw' : d * w * d⁻¹ = w := by
        have e : d * (d * w * d⁻¹) = d * w := by
          calc d * (d * w * d⁻¹) = (d * w * d⁻¹) * d := h1
            _ = d * w := by group
        calc d * w * d⁻¹ = d⁻¹ * (d * (d * w * d⁻¹)) := by group
          _ = d⁻¹ * (d * w) := by rw [e]
          _ = w := by group
      rw [← hw']; exact hw
  have hdC : d ∈ Cen z := hZN d hdN
  have hdz : d * z = z * d := Subgroup.mem_centralizer_singleton_iff.1 hdC
  apply ha
  have hjd' : mkH J j = mkH J ⟨d, hdJ⟩ := by
    have h1 : mkH J (j * (⟨d, hdJ⟩ : ↥J)⁻¹) = 1 := by
      refine (mkH_eq_one_iff J).2 ?_
      obtain ⟨x', hx', hx'e⟩ := hjd
      have : x' = j * (⟨d, hdJ⟩ : ↥J)⁻¹ := Subtype.ext hx'e
      rwa [← this]
    rw [map_mul, map_inv] at h1
    exact mul_inv_eq_one.1 h1
  rw [hjd']
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hdz

end Tp2

section Tp3

variable {G : Type} [Group G] [Finite G]

theorem typeData20 (hCF : CFTypeAut) (h20b : Coprime20b) (hcore : CentCoreProp)
    {z : G} {k : Kind} {S : Subgroup G} (hC : Ctx2011 G z k S) {g : G} (hg : Case20A z S g)
    (hJ : JSetup20 z S g) {q : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)} {K₁ K₂ : Subgroup G}
    (hP : Stage1Pair G z S q L₁ L₂) (hK : CompData z K₁ K₂ L₁ L₂) :
    CFConcl (HBar (J0 z g)) (mkH (J0 z g) ⟨z, hJ.z_mem⟩) q (barIn (J0 z g) K₁) (barIn (J0 z g) K₂)
      (actB (J0_le_H0 z g) (fun _ hh _ hj => J0_conj_mem z g hh hj)).range := by
  have hctx : Stage2Ctx G z k S := hC.1.ctx.ctx17.ctx
  have hM : IsCoatom (Cen z) := hC.1.ctx.ctx17.mem.1
  have hGs : IsSimpleGroup G := hctx.std.kps.1
  have hz2 : orderOf z = 2 := hctx.orderOf_z
  have hHne : H0 z g ≠ ⊤ := H0_ne_top hM hGs hg
  have hJle : J0 z g ≤ H0 z g := J0_le_H0 z g
  have hJH : ∀ h ∈ H0 z g, ∀ j ∈ J0 z g, h * j * h⁻¹ ∈ J0 z g := fun _ hh _ hj => J0_conj_mem z g hh hj
  have hJne : J0 z g ≠ ⊤ := fun h => hHne (top_le_iff.1 (h ▸ hJle))
  have hGH : GHList (HBar (J0 z g)) :=
    hctx.std.kgh (J0 z g) hJne (pPrimeCore 2 ↥(J0 z g)) inferInstance hJ.simple hJ.nonab
  have hcfg := hJ.cfg q L₁ L₂ K₁ K₂ hP hK
  have hFne : F20 z ≠ ⊥ := fun h => hg.inter (le_bot_iff.1 (by rw [← h]; exact inf_le_left))
  have hcard : Nat.card ↥(F20 z) ≠ 1 := fun h => hFne (Subgroup.card_eq_one.1 h)
  obtain ⟨r, hr, hrF⟩ := Nat.exists_prime_and_dvd hcard
  obtain ⟨Z, hZp, hZne, hZF, hZcen, hZnorm, hZN⟩ := exists_Z20 z hr hrF hz2 hM hGs
  have hZH : Z ≤ H0 z g := by
    intro w hw
    unfold H0
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hc : ∀ f ∈ F0 z g, w * f * w⁻¹ = f := fun f hf => by
      have := hZcen f hf.1 w hw
      rw [← this]; group
    constructor
    · intro hx; rw [hc x hx]; exact hx
    · intro hx
      have h := hc _ hx
      have e : w * x * w⁻¹ = x := by
        calc w * x * w⁻¹ = w⁻¹ * (w * (w * x * w⁻¹) * w⁻¹) * w := by group
          _ = w⁻¹ * (w * x * w⁻¹) * w := by rw [h]
          _ = x := by group
      rw [e] at hx; exact hx
  have hFodd : Odd (Nat.card ↥(F20 z)) := odd_card_F20 z
  have hrodd : Odd r := Odd.of_dvd_nat hFodd hrF
  have hZodd : Odd (Nat.card ↥Z) := by
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨n, hn⟩ := hZp.exists_card_eq
    rw [hn]
    exact hrodd.pow
  have hcopr : ¬ r ∣ Nat.card ↥⁅pPrimeCoreOf 2 (J0 z g), J0 z g⁆ := h20b G z k S hC g hg hJ r hr hrF
  have hZne' := actB_Z_ne_bot hcore hJ hr hZp hcopr hZH hZN hz2
  have hZz : ∀ f ∈ Z, f * z = z * f := fun f hf =>
    Subgroup.mem_centralizer_singleton_iff.1
      ((Subgroup.map_subtype_le _ : OddCore z ≤ Cen z) (F20_le_OddCore z (hZF hf)))
  exact hCF _ hJ.simple hJ.nonab hGH _ hJ.central q _ _ hcfg _ (conj_mem_range_actB hJle hJH)
    ⟨Yimg hJle hJH Z, Yimg_le_range hJle hJH Z, Yimg_fix hJle hJH hJ.z_mem hZz,
      Yimg_norm hJle hJH hJ.z_mem hz2 (fun c hcC _ f hf => hZnorm c hcC f hf),
      Yimg_odd hJle hJH hZH hZodd, hZne'⟩

end Tp3

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011
