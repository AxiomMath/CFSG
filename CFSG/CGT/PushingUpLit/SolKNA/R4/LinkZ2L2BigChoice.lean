module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big27
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big36
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big37

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W
open CFSG.Blueprint

section Aut

theorem mulAut_congr_mem_innGrp_iff {A B : Type} [Group A] [Group B] (φ : A ≃* B)
    (β : MulAut A) : MulAut.congr φ β ∈ innGrp B ↔ β ∈ innGrp A := by
  constructor
  · intro h
    obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp h
    refine MonoidHom.mem_range.mpr ⟨φ.symm m, (MulAut.congr φ).injective ?_⟩
    rw [mulAut_congr_conj, MulEquiv.apply_symm_apply]
    exact hm
  · intro h
    obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp h
    exact MonoidHom.mem_range.mpr ⟨φ m, (mulAut_congr_conj φ m).symm⟩

theorem exists_pow_two_pow_of_lt_orderOf {G : Type} [Group G] {H : Subgroup G}
    (hH : IsPGroup 2 ↥H) {β : G} (hβ : β ∈ H) {e : ℕ} (he : 2 ^ e < orderOf β) :
    ∃ K : ℕ, e < K ∧ β ^ 2 ^ K = 1 ∧ β ^ 2 ^ (K - 1) ≠ 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hK⟩ := IsPGroup.iff_orderOf.mp hH ⟨β, hβ⟩
  have hK' : orderOf β = 2 ^ K := by simpa using hK
  have hlt : e < K := by
    rw [hK'] at he
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp he
  exact ⟨K, hlt, by rw [← hK']; exact pow_orderOf_eq_one β,
    (pow_half_mul_self_eq_one (by omega) hK').2⟩

end Aut

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y} {R₀ T₀ : Subgroup Y} {P : Sylow 2 Y}

theorem Z2SetR.edgeCent_le_normalizer_linkLayer (hs : Z2SetR r n R S t J u R₀ T₀ P) :
    edgeCent (P : Subgroup Y) t u ≤ Subgroup.normalizer ((linkLayer R t : Subgroup Y) : Set Y) :=
  fun _ hx => hs.mem_normalizer_linkLayer hx.1.2

@[expose] noncomputable def Z2SetR.rhoT (hs : Z2SetR r n R S t J u R₀ T₀ P) :
    ↥(edgeCent (P : Subgroup Y) t u) →* MulAut ↥(linkGrp R t) :=
  ((MulAut.congr (linkLayerEquiv hs.large)).toMonoidHom.comp (actAut (linkLayer R t))).comp
    (Subgroup.inclusion hs.edgeCent_le_normalizer_linkLayer)

theorem Z2SetR.rhoT_apply (hs : Z2SetR r n R S t J u R₀ T₀ P) {x : Y}
    (hx : x ∈ edgeCent (P : Subgroup Y) t u) :
    hs.rhoT ⟨x, hx⟩ = MulAut.congr (linkLayerEquiv hs.large)
      (actAut (linkLayer R t) ⟨x, hs.mem_normalizer_linkLayer hx.1.2⟩) := rfl

theorem Z2SetR.rhoT_eq_one_iff (hs : Z2SetR r n R S t J u R₀ T₀ P) {x : Y}
    (hx : x ∈ edgeCent (P : Subgroup Y) t u) :
    hs.rhoT ⟨x, hx⟩ = 1 ↔ ActsTriv (linkLayer R t) x := by
  rw [hs.rhoT_apply hx, ← actAut_eq_one_iff (hs.mem_normalizer_linkLayer hx.1.2)]
  constructor
  · intro h
    apply (MulAut.congr (linkLayerEquiv hs.large)).injective
    rw [h, map_one]
  · intro h
    rw [h, map_one]

theorem Z2SetR.rhoT_mem_innGrp_iff (hs : Z2SetR r n R S t J u R₀ T₀ P) {x : Y}
    (hx : x ∈ edgeCent (P : Subgroup Y) t u) :
    hs.rhoT ⟨x, hx⟩ ∈ innGrp ↥(linkGrp R t) ↔ InnerModOdd (linkLayer R t) x := by
  rw [hs.rhoT_apply hx, mulAut_congr_mem_innGrp_iff, actAut_mem_innGrp_iff]

theorem Z2SetR.rhoT_eq_of_actsLike (hs : Z2SetR r n R S t J u R₀ T₀ P) {x w : Y}
    (hx : x ∈ edgeCent (P : Subgroup Y) t u) (hw : w ∈ edgeCent (P : Subgroup Y) t u)
    (h : ActsLike (linkLayer R t) x w) : hs.rhoT ⟨x, hx⟩ = hs.rhoT ⟨w, hw⟩ := by
  have hwi : w⁻¹ ∈ edgeCent (P : Subgroup Y) t u := Subgroup.inv_mem _ hw
  have h1 := actsLike_mul (actsLike_refl (linkLayer R t) w⁻¹) h
    (hs.conjSub_Λt_of_mem hw) (hs.conjSub_Λt_of_mem hwi)
  rw [inv_mul_cancel] at h1
  have h2 := (hs.rhoT_eq_one_iff (Subgroup.mul_mem _ hwi hx)).mpr (actsTriv_iff.mpr h1)
  have e : (⟨w⁻¹ * x, Subgroup.mul_mem _ hwi hx⟩ : ↥(edgeCent (P : Subgroup Y) t u)) =
      (⟨w, hw⟩ : ↥(edgeCent (P : Subgroup Y) t u))⁻¹ * ⟨x, hx⟩ := rfl
  rw [e, map_mul, map_inv] at h2
  exact (inv_mul_eq_one.mp h2).symm

theorem Z2SetR.rhoT_range_eq (hs : Z2SetR r n R S t J u R₀ T₀ P) :
    hs.rhoT.range =
      (((edgeCent (P : Subgroup Y) t u).subgroupOf
        (Subgroup.normalizer ((linkLayer R t : Subgroup Y) : Set Y))).map
          (actAut (linkLayer R t))).map (MulAut.congr (linkLayerEquiv hs.large)).toMonoidHom := by
  rw [Subgroup.map_map, Z2SetR.rhoT, MonoidHom.range_comp, Subgroup.inclusion_range]

theorem Z2SetR.rhoT_isPGroup (hs : Z2SetR r n R S t J u R₀ T₀ P) :
    IsPGroup 2 ↥hs.rhoT.range :=
  IsPGroup.of_surjective (edgeCent_isPGroup P t u) hs.rhoT.rangeRestrict
    hs.rhoT.rangeRestrict_surjective

theorem Z2SetR.exists_quat_linkGrp (hs : Z2SetR r n R S t J u R₀ T₀ P) (hr : 4 ≤ r) :
    ∃ Q : Subgroup ↥(linkGrp R t), Nonempty (↥Q ≃* QuaternionGroup (2 ^ (r - 2))) := by
  obtain ⟨e, he⟩ := hs.exists_quat_T₀ hr
  obtain ⟨Qb, eb, -⟩ := exists_piData (A' := edgeCent (P : Subgroup Y) t u)
    hs.T₀_le_linkLayer (hs.T₀_le_linkLayer hs.u_mem_T₀) hs.hT₀.2.1 e he
    (fun y hy => hs.mem_normalizer_linkLayer hy.1.2) (edgeCent_isPGroup P t u)
    (fun y hy z hz => hs.conj_mem_T₀ hy.1.1 hy.2 hz)
  exact ⟨Qb.map (linkLayerEquiv hs.large).toMonoidHom,
    ⟨(Qb.equivMapOfInjective (linkLayerEquiv hs.large).toMonoidHom
      (linkLayerEquiv hs.large).injective).symm.trans eb⟩⟩

theorem Z2SetR.exists_choiceB (hs : Z2SetR r n R S t J u R₀ T₀ P) (hr : 4 ≤ r)
    (hSplit : Z2BigSplit r n) (hall : NoA1All R t J u)
    (hno : ¬ InvOutsideA (P : Subgroup Y) t u)
    (hInn : ∃ S₁ : Subgroup ↥(linkGrp R t), IsSylow2In S₁ ⊤ ∧
      S₁.map (MulAut.conj : ↥(linkGrp R t) →* MulAut ↥(linkGrp R t)) ≤
        (((edgeCent (P : Subgroup Y) t u).subgroupOf
          (Subgroup.normalizer ((linkLayer R t : Subgroup Y) : Set Y))).map
            (actAut (linkLayer R t))).map (MulAut.congr (linkLayerEquiv hs.large)).toMonoidHom) :
    ∃ b ∈ (P : Subgroup Y), b ∉ edgeCent (P : Subgroup Y) t u ∧
      t * u ∈ Subgroup.zpowers b := by
  obtain ⟨p, f, hm⟩ := hs.exists_linkModel hr (z2BigModelArith_holds r)
  obtain ⟨b₀, hb₀P, hb₀t⟩ := hs.exists_swap
  have hb₀u : b₀ * u * b₀⁻¹ = t := hs.swap_u hb₀P hb₀t
  have hb₀A : b₀ ∉ edgeCent (P : Subgroup Y) t u := fun h =>
    hs.t_ne_u ((hs.mem_edgeCent_iff.mp h).2.symm.trans hb₀t)
  have hb₀bb : b₀ * b₀ ∈ edgeCent (P : Subgroup Y) t u := hs.mul_self_mem_edgeCent hb₀P
  have hout := (hs.sq_outer_of_not_invOutsideA hSplit hr hall hno hb₀P hb₀A).1
  have hyH : hs.rhoT ⟨b₀ * b₀, hb₀bb⟩ ∈ hs.rhoT.range := ⟨_, rfl⟩
  have hyInn : hs.rhoT ⟨b₀ * b₀, hb₀bb⟩ ∉ innGrp ↥(linkGrp R t) := fun h =>
    hout ((hs.rhoT_mem_innGrp_iff hb₀bb).mp h)
  obtain ⟨Q, ⟨eQ⟩⟩ := hs.exists_quat_linkGrp hr
  rw [← hs.rhoT_range_eq] at hInn
  obtain ⟨s, hsmem, hord⟩ := z2BigModelL1_holds r hr ↥(linkGrp R t) p f hm Q eQ _
    hs.rhoT_isPGroup hInn _ hyH hyInn
  obtain ⟨hsH, hsInn⟩ := Subgroup.mem_inf.mp hsmem
  obtain ⟨⟨x₁, hx₁⟩, hsx⟩ := MonoidHom.mem_range.mp hsH
  have hin : InnerModOdd (linkLayer R t) x₁ :=
    (hs.rhoT_mem_innGrp_iff hx₁).mp (hsx ▸ hsInn)
  obtain ⟨g, hgA, hg1, hg2⟩ := hSplit hr Y R S t J u R₀ T₀ P hs hall x₁ hx₁ hin
  have hgs : hs.rhoT ⟨g, hgA⟩ = s := (hs.rhoT_eq_of_actsLike hgA hx₁ hg1).trans hsx
  have hgP : g ∈ (P : Subgroup Y) := hgA.1.1
  have hbP : b₀ * g ∈ (P : Subgroup Y) := (P : Subgroup Y).mul_mem hb₀P hgP
  have hbA : b₀ * g ∉ edgeCent (P : Subgroup Y) t u := by
    intro h
    apply hb₀A
    have e : b₀ = b₀ * g * g⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ h (Subgroup.inv_mem _ hgA)
  have hbt : b₀ * g * t * (b₀ * g)⁻¹ = u := hs.swap_of_not_mem hbP hbA
  have hbu : b₀ * g * u * (b₀ * g)⁻¹ = t := hs.swap_u hbP hbt
  have hmA : b₀⁻¹ * g * b₀⁻¹⁻¹ ∈ edgeCent (P : Subgroup Y) t u :=
    hs.conj_mem_edgeCent ((P : Subgroup Y).inv_mem hb₀P) hgA
  have hb₀u' : b₀⁻¹ * u * b₀⁻¹⁻¹ = t := inv_conj_of_conj hb₀t
  have hmtriv : ActsTriv (linkLayer R t) (b₀⁻¹ * g * b₀⁻¹⁻¹) := by
    have h := actsTriv_conj hg2 b₀⁻¹
    rwa [hs.conjSub_Λu_swap hb₀u'] at h
  have hbb : b₀ * g * (b₀ * g) ∈ edgeCent (P : Subgroup Y) t u :=
    hs.mul_self_mem_edgeCent hbP
  have hrho : hs.rhoT ⟨b₀ * g * (b₀ * g), hbb⟩ = hs.rhoT ⟨b₀ * b₀, hb₀bb⟩ * s := by
    have e : (⟨b₀ * g * (b₀ * g), hbb⟩ : ↥(edgeCent (P : Subgroup Y) t u)) =
        ⟨b₀ * b₀, hb₀bb⟩ * ⟨b₀⁻¹ * g * b₀⁻¹⁻¹, hmA⟩ * ⟨g, hgA⟩ := by
      apply Subtype.ext
      show b₀ * g * (b₀ * g) = b₀ * b₀ * (b₀⁻¹ * g * b₀⁻¹⁻¹) * g
      group
    rw [e, map_mul, map_mul, (hs.rhoT_eq_one_iff hmA).mpr hmtriv, mul_one, hgs]
  have hβH : hs.rhoT ⟨b₀ * g * (b₀ * g), hbb⟩ ∈ hs.rhoT.range := ⟨_, rfl⟩
  obtain ⟨K, hK, hK1, hK2⟩ := exists_pow_two_pow_of_lt_orderOf hs.rhoT_isPGroup hβH
    (by rw [hrho]; exact hord)
  have hpow : ∀ k : ℕ, hs.rhoT ⟨(b₀ * g * (b₀ * g)) ^ k, Subgroup.pow_mem _ hbb k⟩ =
      hs.rhoT ⟨b₀ * g * (b₀ * g), hbb⟩ ^ k := fun k => by
    rw [← map_pow]
    rfl
  have h1 : ActsTriv (linkLayer R t) ((b₀ * g * (b₀ * g)) ^ 2 ^ K) :=
    (hs.rhoT_eq_one_iff (Subgroup.pow_mem _ hbb _)).mp (by rw [hpow]; exact hK1)
  have h2 : ¬ ActsTriv (linkLayer R t) ((b₀ * g * (b₀ * g)) ^ 2 ^ (K - 1)) := fun h =>
    hK2 (by rw [← hpow]; exact (hs.rhoT_eq_one_iff (Subgroup.pow_mem _ hbb _)).mpr h)
  have hlike := hs.pi_t_cyc hr (z2BigModelPiCyc_holds r) hm hbb (K := K) hK h1 h2
  have hcA : (b₀ * g * (b₀ * g)) ^ 2 ^ (K - 1) ∈ edgeCent (P : Subgroup Y) t u :=
    Subgroup.pow_mem _ hbb _
  have hcomm : b₀ * g * (b₀ * g * (b₀ * g)) ^ 2 ^ (K - 1) =
      (b₀ * g * (b₀ * g)) ^ 2 ^ (K - 1) * (b₀ * g) :=
    (((Commute.refl (b₀ * g)).mul_right (Commute.refl (b₀ * g))).pow_right _).eq
  have hct : ActsLike (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u)
      ((b₀ * g * (b₀ * g)) ^ 2 ^ (K - 1)) t := by
    have h := actsLike_conj hlike (b₀ * g)
    rwa [hs.conjSub_Λt_swap hbt, conj_eq_of_comm hcomm, hbu] at h
  have hΛt : ∀ y ∈ linkLayer R t, t * y = y * t := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.mp (linkLayerAt_le_centralizer hy)).symm
  have hΛu : ∀ y ∈ linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u, u * y = y * u :=
    fun y hy => (Subgroup.mem_centralizer_singleton_iff.mp (linkLayerAt_le_centralizer hy)).symm
  have huΛ : u ∈ linkLayer R t := hs.T₀_le_linkLayer hs.u_mem_T₀
  have htΛ : t ∈ linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u :=
    hs.R₀_le_linkLayerAt hs.t_mem_R₀
  have htE : t ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
  have huE : u ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
  have hutA : u * t ∈ edgeCent (P : Subgroup Y) t u :=
    hs.aux_E_le (Subgroup.mul_mem _ huE htE)
  have key := hs.eq_one_of_actsTriv ((edgeCent (P : Subgroup Y) t u).mul_mem hcA hutA) ?_ ?_
  · have hc : (b₀ * g * (b₀ * g)) ^ 2 ^ (K - 1) = t * u := by
      rw [eq_inv_of_mul_eq_one_left key, mul_inv_rev, inv_eq_of_mul_eq_one_right hs.t2,
        inv_eq_of_mul_eq_one_right hs.u2]
    refine ⟨b₀ * g, hbP, hbA, ?_⟩
    rw [← hc]
    exact Subgroup.pow_mem _ (Subgroup.mul_mem _ (Subgroup.mem_zpowers _)
      (Subgroup.mem_zpowers _)) _
  · rw [← mul_assoc]
    exact actsTriv_mul_of_comm hΛt (actsTriv_mul_of_actsLike huΛ hs.u2 hlike)
  · rw [← hs.comm_t_u, ← mul_assoc]
    exact actsTriv_mul_of_comm hΛu (actsTriv_mul_of_actsLike htΛ hs.t2 hct)

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
