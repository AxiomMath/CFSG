module

public import CFSG.ClassicalInvolution.Q3.TL4OddMu4G
public import CFSG.ClassicalInvolution.Q3.TL4OddMu4SecG
public import CFSG.ClassicalInvolution.Q3.TL4OddMu4Z

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance.Bootstrap (rankTwoSpan le_rankTwoSpan_of_le_centralizer)
open CFSG.ClassicalInvolution.Disconnected (DConnected)

section Group

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mk_eq_mk_iff_mem_oddCoreOf {Λ : Subgroup G} {a b : ↥Λ} :
    QuotientGroup.mk' (classicalInvolutionOddCore ↥Λ) a =
        QuotientGroup.mk' (classicalInvolutionOddCore ↥Λ) b ↔
      (a : G)⁻¹ * b ∈ oddCoreOf Λ := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Asc77.mem_oddCoreOf_iff]
  exact ⟨fun h => ⟨(a⁻¹ * b).2, h⟩, fun ⟨_, h⟩ => h⟩

theorem mem_of_conj_mem_oddCoreOf {Λ H : Subgroup G} {b : G} (hb2 : b * b = 1)
    (hbN : b ∈ Subgroup.normalizer (Λ : Set G)) (hO : oddCoreOf Λ ≤ H)
    (hC : Λ ⊓ Subgroup.centralizer ({b} : Set G) ≤ H) {ℓ : G} (hℓ : ℓ ∈ Λ)
    (hℓb : ℓ⁻¹ * (b * ℓ * b⁻¹) ∈ oddCoreOf Λ) : ℓ ∈ H := by
  obtain ⟨o, ho, h⟩ := Q3AM.exists_mul_centralizes_of_odd hb2 (Asc77.oddCoreOf_odd_natCard Λ)
    (fun o ho => Asc77.mem_normalizer_oddCoreOf_of_mem_normalizer hbN ho) hℓb
  have h1 : ℓ * o ∈ H := by
    refine hC (Subgroup.mem_inf.mpr ⟨Λ.mul_mem hℓ (Asc77.oddCoreOf_le_self Λ ho), ?_⟩)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc ℓ * o * b = b * (ℓ * o) * b⁻¹ * b := by rw [h]
      _ = b * (ℓ * o) := by group
  have h2 := H.mul_mem h1 (H.inv_mem (hO ho))
  rwa [mul_inv_cancel_right] at h2

theorem centralizer_le_map_of_conj {Λ H : Subgroup G} {b : G} (hb2 : b * b = 1)
    (hbN : b ∈ Subgroup.normalizer (Λ : Set G)) (hO : oddCoreOf Λ ≤ H)
    (hC : Λ ⊓ Subgroup.centralizer ({b} : Set G) ≤ H) {c : ↥Λ ⧸ classicalInvolutionOddCore ↥Λ}
    (hact : ∀ (ℓ : ↥Λ) (h : b * ℓ * b⁻¹ ∈ Λ),
      QuotientGroup.mk' (classicalInvolutionOddCore ↥Λ) ⟨b * ℓ * b⁻¹, h⟩ =
        c * QuotientGroup.mk' (classicalInvolutionOddCore ↥Λ) ℓ * c⁻¹) :
    Subgroup.centralizer ({c} : Set (↥Λ ⧸ classicalInvolutionOddCore ↥Λ)) ≤
      (H.subgroupOf Λ).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Λ)) := by
  intro q hq
  obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥Λ) q
  rw [Subgroup.mem_centralizer_singleton_iff] at hq
  have h1 := hact ℓ ((Subgroup.mem_normalizer_iff.mp hbN ℓ).mp ℓ.2)
  rw [← hq, mul_inv_cancel_right] at h1
  exact ⟨ℓ, Subgroup.mem_subgroupOf.mpr (mem_of_conj_mem_oddCoreOf hb2 hbN hO hC ℓ.2
    (mk_eq_mk_iff_mem_oddCoreOf.mp h1.symm)), rfl⟩

omit [Finite G] in
theorem le_of_map_mk_eq_top {Λ H : Subgroup G} (hO : oddCoreOf Λ ≤ H)
    (htop : ⊤ ≤ (H.subgroupOf Λ).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Λ))) :
    Λ ≤ H := by
  intro ℓ hℓ
  obtain ⟨m, hm, hmℓ⟩ := htop (Subgroup.mem_top
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥Λ) ⟨ℓ, hℓ⟩))
  have h2 := H.mul_mem (Subgroup.mem_subgroupOf.mp hm) (hO (mk_eq_mk_iff_mem_oddCoreOf.mp hmℓ))
  rwa [mul_inv_cancel_left] at h2

end Group

section Frame

variable {Y : Type} [Group Y] {R : Subgroup Y} {t : Y} {J K' : Subgroup Y} {u x y x' : Y}

theorem E4FrameAt.closure_le_centralizer (hF : E4FrameAt R t J K' u x y x') :
    Subgroup.closure ({t, u, x * y * x'} : Set Y) ≤ Subgroup.centralizer ({t} : Set Y) := by
  rw [Subgroup.closure_le]
  rintro w (rfl | rfl | rfl)
  · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  · exact Subgroup.mem_centralizer_singleton_iff.mpr hF.comm_tu.symm
  · exact Subgroup.mem_centralizer_singleton_iff.mpr hF.comm_ts.symm

end Frame

section Cit3

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J K' : Subgroup Y} {u x y x' : Y}

theorem mem_normalizer_linkLayer (hL : TightLargeHypR r n Y R S t) {c : Y}
    (hc : c ∈ Subgroup.centralizer ({t} : Set Y)) :
    c ∈ Subgroup.normalizer ((linkLayer R t : Subgroup Y) : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨conj_mem_linkLayer hL hc, fun hh => ?_⟩
  have h1 := conj_mem_linkLayer hL ((Subgroup.centralizer ({t} : Set Y)).inv_mem hc) hh
  rwa [show c⁻¹ * (c * h * c⁻¹) * c⁻¹⁻¹ = h by group] at h1

theorem oddCoreOf_linkLayer_le_rankTwoSpan_e4 (hL : TightLargeHypR r n Y R S t)
    (hF : E4FrameAt R t J K' u x y x') :
    oddCoreOf (linkLayer R t) ≤ rankTwoSpan (Subgroup.closure ({t, u, x * y * x'} : Set Y)) := by
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 2
    Nat.prime_two _ _ (hF.isElemAbelian hL) (by rw [hF.natCard hL]; norm_num)
    (fun a ha => Asc77.T7L.mem_normalizer_oddCoreOf
      (mem_normalizer_linkLayer hL (hF.closure_le_centralizer ha)))
    (Nat.coprime_two_left.mpr (Asc77.oddCoreOf_odd_natCard _))
  conv_lhs => rw [← hgen]
  exact iSup₂_le fun F hF => le_rankTwoSpan_of_le_centralizer hF inf_le_right

theorem linkLayer_le_rankTwoSpan_e4 (hodd : E4CoverOddFree) (hgen : E4CoverGen)
    (hL : TightLargeHypR r n Y R S t) (hcase : LinkE4 R t) (hF : E4FrameAt R t J K' u x y x') :
    linkLayer R t ≤ rankTwoSpan (Subgroup.closure ({t, u, x * y * x'} : Set Y)) := by
  have ht := hL.datum.isUniqueInvolution_core
  have hu := hF.invJ
  have htu := hF.invK
  obtain ⟨ctx, cty, ctx'⟩ := hF.commute_t
  obtain ⟨-, cuy, cux'⟩ := hF.commute_u
  have ctu : t * u = u * t := hF.comm_tu
  have hm := mem_closure_three_left t u (x * y * x')
  have hBt := hF.closure_le_centralizer
  have hO := oddCoreOf_linkLayer_le_rankTwoSpan_e4 hL hF
  have cttu : t * (t * u) = t * u * t := by rw [mul_assoc, ctu, ← mul_assoc]
  have hutu : u * (t * u) = t := by rw [← mul_assoc, ← ctu, mul_assoc, hu.sq, mul_one]
  have huΛ : u ∈ linkLayer R t := coreAt_le_linkLayerAt hF.memJ
    (mem_coreAt_of_sq_sq hu.mem (by rw [hu.sq, one_mul]) ctu.symm)
  have htΛ : t ∈ linkLayer R t := by
    have h1 := (linkLayer R t).mul_mem huΛ (coreAt_le_linkLayerAt hF.memK
      (mem_coreAt_of_sq_sq htu.mem (by rw [htu.sq, one_mul]) cttu.symm))
    rwa [hutu] at h1
  have hwΛ : y * x' ∈ linkLayer R t := (linkLayer R t).mul_mem
    (coreAt_le_linkLayerAt hF.memJ
      (mem_coreAt_of_sq_sq hF.memy (by rw [hF.sqy, hu.sq]) cty.eq.symm))
    (coreAt_le_linkLayerAt hF.memK
      (mem_coreAt_of_sq_sq hF.memx' (by rw [hF.sqx', htu.sq]) ctx'.eq.symm))
  have hxK : x ∈ coreAt t (tightCore R) :=
    mem_coreAt_of_sq_sq hF.memx (by rw [hF.sqx, ht.sq]) ctx.eq.symm
  have hxC := coreAt_le_centralizer t (tightCore R) hxK
  have hfour : ∀ b ∈ Subgroup.closure ({t, u, x * y * x'} : Set Y), b * b = 1 → b ≠ 1 →
      b ≠ t → t * b = b * t → linkLayer R t ⊓ Subgroup.centralizer ({b} : Set Y) ≤
        rankTwoSpan (Subgroup.closure ({t, u, x * y * x'} : Set Y)) :=
    fun b hbB hb2 hb1 hbt hcb => le_rankTwoSpan_of_le_centralizer
      (RouteD.TwinY.closure_pair_mem_signalizer hm.1 hbB ht.sq hb2 ht.ne_one hb1 (Ne.symm hbt)
        hcb)
      (RouteD.TwinY.le_centralizer_pair (inf_le_left.trans linkLayerAt_le_centralizer)
        inf_le_right)
  have hs2 := hF.sq_s ht.sq hu.sq
  have htc : t ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
  have huc : u ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
  have htu' : t ≠ u := fun h =>
    hF.memJ.2.1 (eq_core_of_isUniqueInvolution hL hF.memJ.1 (h ▸ hF.invJ))
  have hs1 : x * y * x' ≠ 1 := fun h => hF.notMem (h ▸ Subgroup.one_mem _)
  have hst : x * y * x' ≠ t := fun h => hF.notMem (h ▸ htc)
  have hus := Subgroup.mul_mem _ hm.2.1 hm.2.2
  have hus2 : u * (x * y * x') * (u * (x * y * x')) = 1 := by
    rw [mul_mul_self_of_comm hF.comm_us, hu.sq, hs2, one_mul]
  have hus1 : u * (x * y * x') ≠ 1 := fun h => hF.notMem (by
    rw [show x * y * x' = u⁻¹ * (u * (x * y * x')) by group, h, mul_one]
    exact Subgroup.inv_mem _ huc)
  have hust : u * (x * y * x') ≠ t := fun h => hF.notMem (by
    rw [show x * y * x' = u⁻¹ * (u * (x * y * x')) by group, h]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ huc) htc)
  have c1 : Commute t u := ctu
  have c2 : Commute t (x * y * x') := hF.comm_ts
  have htr := vertexTriv_core hL (isPGroup_secImg_of_linkE4 hodd hL hcase)
  have hcov : CoverSp4 (↥(linkLayer R t) ⧸ classicalInvolutionOddCore ↥(linkLayer R t)) ∨
      CoverSL4 (↥(linkLayer R t) ⧸ classicalInvolutionOddCore ↥(linkLayer R t)) :=
    hcase.2.2.imp (coverSp4_core hL) (coverSL4_core hL)
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥(linkLayer R t)) with hπ
  have hxπ : ∀ (g : ↥(linkLayer R t)) (hg : x * g * x⁻¹ ∈ linkLayer R t),
      π ⟨x * g * x⁻¹, hg⟩ = π g := by
    intro g hg
    refine mk_eq_mk_iff_mem_oddCoreOf.mpr ?_
    have h1 := htr x hxK _ ((linkLayer R t).inv_mem g.2)
    rwa [show x * (g : Y)⁻¹ * x⁻¹ * (g : Y)⁻¹⁻¹ = (x * g * x⁻¹)⁻¹ * g by group] at h1
  have hactu : ∀ (ℓ : ↥(linkLayer R t)) (h : u * ℓ * u⁻¹ ∈ linkLayer R t),
      π ⟨u * ℓ * u⁻¹, h⟩ = π ⟨u, huΛ⟩ * π ℓ * (π ⟨u, huΛ⟩)⁻¹ := by
    intro ℓ h
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hacts : ∀ (ℓ : ↥(linkLayer R t)) (h : x * y * x' * ℓ * (x * y * x')⁻¹ ∈ linkLayer R t),
      π ⟨x * y * x' * ℓ * (x * y * x')⁻¹, h⟩ =
        π ⟨y * x', hwΛ⟩ * π ℓ * (π ⟨y * x', hwΛ⟩)⁻¹ := by
    intro ℓ h
    have hm' := (linkLayer R t).mul_mem ((linkLayer R t).mul_mem hwΛ ℓ.2)
      ((linkLayer R t).inv_mem hwΛ)
    have hxm := conj_mem_linkLayer hL hxC hm'
    calc π ⟨x * y * x' * ℓ * (x * y * x')⁻¹, h⟩
        = π ⟨x * (y * x' * ℓ * (y * x')⁻¹) * x⁻¹, hxm⟩ := congrArg π (Subtype.ext
          (show x * y * x' * ℓ * (x * y * x')⁻¹ = x * (y * x' * ℓ * (y * x')⁻¹) * x⁻¹ by group))
      _ = π ⟨y * x' * ℓ * (y * x')⁻¹, hm'⟩ := hxπ ⟨_, hm'⟩ hxm
      _ = π (⟨y * x', hwΛ⟩ * ℓ * ⟨y * x', hwΛ⟩⁻¹) := rfl
      _ = π ⟨y * x', hwΛ⟩ * π ℓ * (π ⟨y * x', hwΛ⟩)⁻¹ := by rw [map_mul, map_mul, map_inv]
  have hactus : ∀ (ℓ : ↥(linkLayer R t))
      (h : u * (x * y * x') * ℓ * (u * (x * y * x'))⁻¹ ∈ linkLayer R t),
      π ⟨u * (x * y * x') * ℓ * (u * (x * y * x'))⁻¹, h⟩ =
        π ⟨u, huΛ⟩ * π ⟨y * x', hwΛ⟩ * π ℓ * (π ⟨u, huΛ⟩ * π ⟨y * x', hwΛ⟩)⁻¹ := by
    intro ℓ h
    have hs' := conj_mem_linkLayer hL (hBt hm.2.2) ℓ.2
    calc π ⟨u * (x * y * x') * ℓ * (u * (x * y * x'))⁻¹, h⟩
        = π (⟨u, huΛ⟩ * ⟨x * y * x' * ℓ * (x * y * x')⁻¹, hs'⟩ * ⟨u, huΛ⟩⁻¹) :=
          congrArg π (Subtype.ext (show u * (x * y * x') * ℓ * (u * (x * y * x'))⁻¹ =
            u * (x * y * x' * ℓ * (x * y * x')⁻¹) * u⁻¹ by group))
      _ = π ⟨u, huΛ⟩ * π ⟨y * x', hwΛ⟩ * π ℓ * (π ⟨u, huΛ⟩ * π ⟨y * x', hwΛ⟩)⁻¹ := by
          rw [map_mul, map_mul, map_inv, hacts ℓ hs']
          group
  have htZ : π ⟨t, htΛ⟩ ∈ Subgroup.center _ := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk'_surjective
      (classicalInvolutionOddCore ↥(linkLayer R t)) q
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (linkLayerAt_le_centralizer ℓ.2))
  have hww : π ⟨y * x', hwΛ⟩ * π ⟨y * x', hwΛ⟩ = π ⟨t, htΛ⟩ := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext (show y * x' * (y * x') = t by
      rw [mul_mul_self_of_comm hF.cyx', hF.sqy, hF.sqx', hutu])
  have huu : π ⟨u, huΛ⟩ * π ⟨u, huΛ⟩ = 1 := by
    rw [← map_mul, show (⟨u, huΛ⟩ : ↥(linkLayer R t)) * ⟨u, huΛ⟩ = 1 from Subtype.ext hu.sq,
      map_one]
  have ht1 : π ⟨t, htΛ⟩ ≠ 1 := mk_ne_one_of_sq (x := (⟨t, htΛ⟩ : ↥(linkLayer R t)))
    (Subtype.ext ht.sq) (fun h => ht.ne_one (congrArg Subtype.val h))
  have huw : π ⟨u, huΛ⟩ * π ⟨y * x', hwΛ⟩ = π ⟨y * x', hwΛ⟩ * π ⟨u, huΛ⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg π (Subtype.ext (cuy.mul_right cux').eq)
  have hgen' := hgen _ hcov (π ⟨u, huΛ⟩) (π ⟨y * x', hwΛ⟩) huu (by rw [hww]; exact htZ)
    (by rw [hww]; exact ht1) huw
  refine le_of_map_mk_eq_top hO ?_
  rw [← hgen']
  refine sup_le (sup_le ?_ ?_) ?_
  · exact centralizer_le_map_of_conj hu.sq (mem_normalizer_linkLayer hL (hBt hm.2.1)) hO
      (hfour u hm.2.1 hu.sq hu.ne_one htu'.symm ctu) hactu
  · exact centralizer_le_map_of_conj hs2 (mem_normalizer_linkLayer hL (hBt hm.2.2)) hO
      (hfour _ hm.2.2 hs2 hs1 hst hF.comm_ts) hacts
  · exact centralizer_le_map_of_conj hus2 (mem_normalizer_linkLayer hL (hBt hus)) hO
      (hfour _ hus hus2 hus1 hust (c1.mul_right c2).eq) hactus

theorem tightE4LinkGenR_of (hodd : E4CoverOddFree) (hgen : E4CoverGen) : TightE4LinkGenR r n := by
  intro Y _ _ R S t hL _ hcase _ J K' u x y x' hF
  exact linkLayer_le_rankTwoSpan_e4 hodd hgen hL hcase hF

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
