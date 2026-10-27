module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3CentXZ
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3SHatZ

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent CFSG.Sporadic.Schreier.Tits.titsZMod2CharP

namespace CFSG.ComponentClassification.AS81

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.Open
open CFSG.ABGLocalTools Sec3
open CFSG.LargeExtraspecial.S2 (perp mem_perp)
open CFSG.LargeExtraspecial.OrthoF2 (isRefl_polarBilin zmod2_eq_zero_or_eq_one)
open scoped Pointwise

namespace Sec3U

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V}

theorem eq_one_of_forall_polar_eq_zero (hq : q.polarBilin.Nondegenerate) {a : V} (ha : q a = 0)
    {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup q)
    (hfix : ∀ v, polar q a v = 0 → g v = v) : g = 1 := by
  refine LinearEquiv.ext fun v => ?_
  change g v = v
  by_cases hv : polar q a v = 0
  · exact hfix v hv
  have hv1 : polar q a v = 1 := by
    rcases zmod2_eq_zero_or_eq_one (polar q a v) with h | h
    · exact absurd h hv
    · exact h
  have hd : g v - v ∈ perp q (perp q ((ZMod 2) ∙ a)) := by
    refine mem_perp.mpr fun w hw => ?_
    have hwa : polar q a w = 0 := mem_perp.mp hw a (Submodule.mem_span_singleton_self a)
    rw [polar_sub_right, ← hfix w hwa,
      TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg, hfix w hwa, sub_self]
  have hd' : g v - v ∈ LinearMap.BilinForm.orthogonal (polarBilin q)
      (LinearMap.BilinForm.orthogonal (polarBilin q) ((ZMod 2) ∙ a)) := hd
  rw [LinearMap.BilinForm.orthogonal_orthogonal hq (isRefl_polarBilin q)] at hd'
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hd'
  have hgv : g v = v + c • a := by rw [hc]; abel
  have hq' : q (g v) = q v := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg v
  have hpol : q (v + c • a) = q v + q (c • a) + polar q v (c • a) := by
    rw [polar]
    abel
  rw [hgv, hpol, QuadraticMap.map_smul, ha, smul_zero, add_zero, polar_smul_right, polar_comm,
    hv1, smul_eq_mul, mul_one] at hq'
  have hc0 : c = 0 := by simpa using hq'
  rw [hgv, hc0, zero_smul, add_zero]

omit [FiniteDimensional (ZMod 2) V] in
theorem lt_inf_normalizer {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {M S : Subgroup G} (hS : IsPGroup p S) (hMS : M < S) : M < S ⊓ normalizer (M : Set G) := by
  have : Group.IsNilpotent S := hS.isNilpotent
  have hproper : M.subgroupOf S < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro heq
    exact (not_le_of_gt hMS) (Subgroup.subgroupOf_eq_top.mp heq)
  have hgrowth := Group.normalizerCondition_of_isNilpotent (G := S) (M.subgroupOf S) hproper
  have hmapgrowth := Subgroup.map_subtype_lt_map_subtype.mpr hgrowth
  rw [Subgroup.map_subgroupOf_eq_of_le hMS.le] at hmapgrowth
  have hnormalizer : (Subgroup.normalizer (M.subgroupOf S : Set S)).map S.subtype =
      S ⊓ Subgroup.normalizer (M : Set G) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hMS.le, Subgroup.subgroupOf_map_subtype, inf_comm]
  rwa [hnormalizer] at hmapgrowth

end Sec3U

namespace Sec38Hyp

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G}
  {x : G} {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U V₀ V Q₀ : Subgroup G}
  (H : Sec38Hyp G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀)
include H

theorem Zs_le_U (hZQ : Zs ≤ Q) : Zs ≤ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) := fun _ hs =>
  mem_inf.mpr ⟨H.Q_le (hZQ hs), mem_centralizer_iff.mpr fun _ ht => H.comm_of_mem_Zs ht hs⟩

theorem mem_Zs_of_mem_Q₁ (hZQ : Zs ≤ Q) {c : G} (hcQ : c ∈ Q₀ ⊔ Q)
    (hcU : c ∈ centralizer (((Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) : Subgroup G) : Set G)) :
    c ∈ Zs := by
  obtain ⟨z₂, hz₂, hz₂z⟩ := H.exists_z₂
  rw [H.Zs_eq_clPre hZQ hz₂ hz₂z]
  refine ⟨hcQ, ?_⟩
  have h1 : H.xsub.cl c ∈ perp H.xsub.q (perp H.xsub.q ((ZMod 2) ∙ H.xsub.cl z₂)) := by
    refine mem_perp.mpr fun w hw => ?_
    obtain ⟨b, hb, rfl⟩ := H.xsub.exists_cl w
    have hbU : b ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) := by
      rw [H.centralizer_Zs_eq_clPre hZQ hz₂ hz₂z]
      exact ⟨hb, hw⟩
    exact (H.xsub.polar_cl_eq_zero_iff hb hcQ).mpr (mem_centralizer_iff.mp hcU b hbU)
  have h2 : H.xsub.cl c ∈ LinearMap.BilinForm.orthogonal (polarBilin H.xsub.q)
      (LinearMap.BilinForm.orthogonal (polarBilin H.xsub.q) ((ZMod 2) ∙ H.xsub.cl z₂)) := h1
  rwa [LinearMap.BilinForm.orthogonal_orthogonal H.xsub.q_nondegenerate
    (isRefl_polarBilin H.xsub.q)] at h2

theorem mem_Zs_of_two_elt (hZQ : Zs ≤ Q) {c : G} (hcN : c ∈ H.xsub.N)
    (hcU : c ∈ centralizer (((Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) : Subgroup G) : Set G))
    {n : ℕ} (hc2 : c ^ 2 ^ n = 1) : c ∈ Zs := by
  obtain ⟨z₂, hz₂, hz₂z⟩ := H.exists_z₂
  have hρ : H.ρG ⟨c, hcN⟩ = 1 := by
    refine Sec3U.eq_one_of_forall_polar_eq_zero H.xsub.q_nondegenerate (H.q_cl_eq_zero hZQ hz₂)
      (H.xsub.ρ _).2 fun v hv => ?_
    obtain ⟨u, hu, rfl⟩ := H.xsub.exists_cl v
    have huU : u ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) := by
      rw [H.centralizer_Zs_eq_clPre hZQ hz₂ hz₂z]
      refine ⟨hu, mem_perp.mpr fun w hw => ?_⟩
      obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [polar_smul_left, hv, smul_zero]
    rw [H.ρG_cl _ hu]
    change H.xsub.cl (c * u * c⁻¹) = H.xsub.cl u
    rw [← mem_centralizer_iff.mp hcU u huU, mul_inv_cancel_right]
  obtain ⟨c₀, hc₀, hd⟩ := H.xsub.exists_mem_of_ρ_eq_one ((H.ρG_eq_one_iff _).mp hρ)
  have hUQ : ((Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) : Subgroup G) ≤ H.xsub.Q₁ := inf_le_left
  have hdU : c₀⁻¹ * c ∈
      centralizer (((Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) : Subgroup G) : Set G) :=
    Subgroup.centralizer_le hUQ hd
  have hc₀U : c₀ ∈
      centralizer (((Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) : Subgroup G) : Set G) := by
    have e : c₀ = c * (c₀⁻¹ * c)⁻¹ := by group
    rw [e]
    exact mul_mem hcU (inv_mem hdU)
  have hc₀Z : c₀ ∈ Zs := H.mem_Zs_of_mem_Q₁ hZQ hc₀ hc₀U
  have hcom : Commute c₀⁻¹ c :=
    (show Commute c₀ c from mem_centralizer_iff.mp hcU c₀ (H.Zs_le_U hZQ hc₀Z)).inv_left
  have hc₀2 : c₀ ^ 2 = 1 := H.sq_eq_one_of_mem_Zs hc₀Z
  have h1 : c₀⁻¹ ^ 2 ^ (n + 1) = 1 := by rw [pow_succ', pow_mul, inv_pow, hc₀2, inv_one, one_pow]
  have h2 : c ^ 2 ^ (n + 1) = 1 := by rw [pow_succ, pow_mul, hc2, one_pow]
  have hd2 : (c₀⁻¹ * c) ^ 2 ^ (n + 1) = 1 := by rw [hcom.mul_pow, h1, h2, one_mul]
  have hdz : zpowers (c₀⁻¹ * c) ≤ zpowers z :=
    H.le_zpowers_of_le_centralizer (AS76b.isPGroup_zpowers_of_pow_eq_one hd2)
      (zpowers_le.mpr hd)
  have hzZ : zpowers z ≤ Zs := zpowers_le.mpr H.z_mem_Zs
  have e : c = c₀ * (c₀⁻¹ * c) := by group
  rw [e]
  exact mul_mem hc₀Z (hzZ (hdz (mem_zpowers _)))

theorem commutator_mem_zpowers {a b : G} (ha : a ∈ Q₀ ⊔ Q) (hb : b ∈ Q₀ ⊔ Q) :
    a * b * a⁻¹ * b⁻¹ ∈ zpowers z := by
  have ha' : a ∈ H.xsub.Q₁ := ha
  have hb' : b ∈ H.xsub.Q₁ := hb
  have hm : a * b * a⁻¹ * b⁻¹ ∈ H.xsub.Q₁ :=
    mul_mem (mul_mem (mul_mem ha' hb') (inv_mem ha')) (inv_mem hb')
  change a * b * a⁻¹ * b⁻¹ ∈ zpowers H.xsub.z
  rw [← H.xsub.cl_eq_zero_iff hm, H.xsub.cl_mul (mul_mem (mul_mem ha' hb') (inv_mem ha'))
    (inv_mem hb'), H.xsub.cl_mul (mul_mem ha' hb') (inv_mem ha'), H.xsub.cl_mul ha' hb',
    H.xsub.cl_inv ha', H.xsub.cl_inv hb']
  have e : H.xsub.cl a + H.xsub.cl b + H.xsub.cl a + H.xsub.cl b =
      (H.xsub.cl a + H.xsub.cl a) + (H.xsub.cl b + H.xsub.cl b) := by abel
  rw [e, ZModModule.add_self, ZModModule.add_self, add_zero]

theorem zpowers_z_le_centralizer : zpowers z ≤ centralizer (Zs : Set G) :=
  zpowers_le.mpr (mem_centralizer_iff.mpr fun _ hs => H.comm_of_mem_Zs hs H.z_mem_Zs)

theorem mem_normalizer_U_of_mem_Q₁ {q : G} (hq : q ∈ Q₀ ⊔ Q) :
    q ∈ normalizer (((Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) : Subgroup G) : Set G) := by
  refine AS76b.mem_normalizer_of_map_conj_le ?_
  rintro _ ⟨u, hu, rfl⟩
  change q * u * q⁻¹ ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G)
  refine mem_inf.mpr ⟨H.xsub.conj_mem (H.xsub.le_N hq) hu.1, ?_⟩
  have e : q * u * q⁻¹ = (q * u * q⁻¹ * u⁻¹) * u := by group
  rw [e]
  exact mul_mem (H.zpowers_z_le_centralizer (H.commutator_mem_zpowers hq hu.1)) hu.2

theorem mem_normalizer_U {g : G} (hgN : g ∈ H.xsub.N) (hgZ : g ∈ centralizer (Zs : Set G)) :
    g ∈ normalizer (((Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) : Subgroup G) : Set G) := by
  refine AS76b.mem_normalizer_of_map_conj_le ?_
  rintro _ ⟨u, hu, rfl⟩
  change g * u * g⁻¹ ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G)
  refine mem_inf.mpr ⟨H.xsub.conj_mem hgN hu.1, mem_centralizer_iff.mpr fun s hs => ?_⟩
  have hgs : g * s * g⁻¹ = s := by rw [← mem_centralizer_iff.mp hgZ s hs, mul_inv_cancel_right]
  have hus : s * u = u * s := mem_centralizer_iff.mp hu.2 s hs
  calc s * (g * u * g⁻¹) = (g * s * g⁻¹) * (g * u * g⁻¹) := by rw [hgs]
    _ = g * (s * u) * g⁻¹ := by group
    _ = g * (u * s) * g⁻¹ := by rw [hus]
    _ = (g * u * g⁻¹) * (g * s * g⁻¹) := by group
    _ = (g * u * g⁻¹) * s := by rw [hgs]

theorem Q₁_le_normalizer_C :
    Q₀ ⊔ Q ≤ normalizer ((centralizer (((Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) : Subgroup G) :
      Set G) : Subgroup G) : Set G) :=
  fun _ hq => AS81.mem_normalizer_centralizer (H.mem_normalizer_U_of_mem_Q₁ hq)

omit [Finite G] H in
theorem Zs_le_C :
    Zs ≤ centralizer (((Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) : Subgroup G) : Set G) :=
  fun s hs => mem_centralizer_iff.mpr fun _ hu => (mem_centralizer_iff.mp hu.2 s hs).symm

theorem isSylowOf_Q₁_sup (hZQ : Zs ≤ Q) :
    IsSylowOf 2 (Q₀ ⊔ Q) ((Q₀ ⊔ Q) ⊔
      centralizer (((Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) : Subgroup G) : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer (((Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) : Subgroup G) : Set G) with hC
  set Y := (Q₀ ⊔ Q) ⊔ C with hY
  have hQ2 : IsPGroup 2 ↥(Q₀ ⊔ Q) := IsPGroup.of_card (n := 9) H.card
  obtain ⟨S, hS⟩ := (hQ2.comap_subtype (K := Y)).exists_le_sylow
  set S' := (S : Subgroup ↥Y).map Y.subtype with hS'
  have hQY : Q₀ ⊔ Q ≤ Y := le_sup_left
  have hQS' : Q₀ ⊔ Q ≤ S' := fun q hq =>
    ⟨⟨q, hQY hq⟩, hS (show (⟨q, hQY hq⟩ : ↥Y) ∈ (Q₀ ⊔ Q).subgroupOf Y from hq), rfl⟩
  have hS'2 : IsPGroup 2 S' := S.isPGroup'.map _
  have hYmul : ((Y : Subgroup G) : Set G) = ((Q₀ ⊔ Q : Subgroup G) : Set G) * (C : Set G) :=
    coe_mul_of_left_le_normalizer_right _ _ H.Q₁_le_normalizer_C
  have hS'Q : S' ≤ Q₀ ⊔ Q := by
    by_contra hne
    have hlt : Q₀ ⊔ Q < S' := lt_of_le_of_ne hQS' fun e => hne (e ▸ le_rfl)
    obtain ⟨g, hg, hgQ⟩ := IsConcreteLE.exists_of_lt (Sec3U.lt_inf_normalizer hS'2 hlt)
    have hgY : g ∈ ((Y : Subgroup G) : Set G) := map_subtype_le _ hg.1
    rw [hYmul] at hgY
    obtain ⟨q, hq, c, hc, rfl⟩ := hgY
    have hcS : c ∈ S' := by
      have e : c = q⁻¹ * (q * c) := by group
      rw [e]
      exact mul_mem (inv_mem (hQS' hq)) hg.1
    have hcN : c ∈ H.xsub.N := by
      have e : c = q⁻¹ * (q * c) := by group
      rw [e]
      exact mul_mem (inv_mem (H.xsub.le_N hq)) hg.2
    obtain ⟨n, hn⟩ := hS'2 ⟨c, hcS⟩
    have hcn : c ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hcZ := H.mem_Zs_of_two_elt hZQ hcN hc hcn
    exact hgQ (mul_mem hq (H.Q_le (hZQ hcZ)))
  exact ⟨S, le_antisymm hS'Q hQS'⟩

theorem isSylowOf_Zs (hZQ : Zs ≤ Q) :
    IsSylowOf 2 Zs (centralizer (((Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) : Subgroup G) : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := (H.isSylowOf_Q₁_sup hZQ).inf_of_le_normalizer le_sup_right
    (sup_le H.Q₁_le_normalizer_C le_normalizer)
  have e : (Q₀ ⊔ Q) ⊓ centralizer (((Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) : Subgroup G) :
      Set G) = Zs :=
    le_antisymm (fun c hc => H.mem_Zs_of_mem_Q₁ hZQ hc.1 hc.2)
      (le_inf (fun s hs => H.Q_le (hZQ hs)) Zs_le_C)
  rwa [e] at h

theorem centralizer_U_le_sup (hZQ : Zs ≤ Q) :
    centralizer (((Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) : Subgroup G) : Set G) ≤
      Zs ⊔ AS76b.oddCoreIn
        (centralizer (((Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) : Subgroup G) : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C₁ := centralizer (((Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) : Subgroup G) : Set G) with hC₁
  have hZ2 : IsPGroup 2 Zs := IsPGroup.of_card (n := 2) (by rw [H.q0.dData.suz.Zs_card]; norm_num)
  have hZc : ∀ s ∈ Zs, ∀ c ∈ C₁, c * s = s * c := fun s hs c hc =>
    (mem_centralizer_iff.mp hc s (H.Zs_le_U hZQ hs)).symm
  let P : Sylow 2 ↥C₁ := default
  have hPz : (P : Subgroup ↥C₁).map C₁.subtype ≤ Zs := by
    have hP2 : IsPGroup 2 ((P : Subgroup ↥C₁).map C₁.subtype) := P.isPGroup'.map _
    have hPN : (P : Subgroup ↥C₁).map C₁.subtype ≤ normalizer (Zs : Set G) := fun c hc =>
      centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun s hs =>
        (hZc s hs c (map_subtype_le _ hc)).symm)
    have hsup := hP2.to_sup_of_normal_right' hZ2 hPN
    have heq := (H.isSylowOf_Zs hZQ).eq_of_le le_sup_right
      (sup_le (map_subtype_le _) Zs_le_C) hsup
    exact heq ▸ le_sup_left
  have hPc : ∀ p ∈ (P : Subgroup ↥C₁), ∀ c : ↥C₁, c * p = p * c := by
    intro p hp c
    exact Subtype.ext (hZc p (hPz ⟨p, hp, rfl⟩) c c.2)
  have hP : normalizer ((P : Subgroup ↥C₁) : Set ↥C₁) ≤
      centralizer ((P : Subgroup ↥C₁) : Set ↥C₁) :=
    fun c _ => mem_centralizer_iff.mpr fun p hp => (hPc p hp c).symm
  have hcomp := MonoidHom.ker_transferSylow_isComplement' P hP
  have hodd : Odd (Nat.card (MonoidHom.transferSylow P hP).ker) :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (MonoidHom.not_dvd_card_ker_transferSylow P hP))
  have hKO : (MonoidHom.transferSylow P hP).ker ≤ CFSG.Assembly.oddCore ↥C₁ :=
    le_sSup ⟨inferInstance, hodd⟩
  intro c hc
  have hctop : (⟨c, hc⟩ : ↥C₁) ∈ (MonoidHom.transferSylow P hP).ker ⊔ (P : Subgroup ↥C₁) := by
    rw [hcomp.sup_eq_top]
    exact mem_top _
  have hmap := Subgroup.mem_map_of_mem C₁.subtype hctop
  rw [Subgroup.map_sup] at hmap
  exact (sup_le ((map_mono hKO).trans le_sup_right) (hPz.trans le_sup_left)) hmap

section Trivial

variable {g : G}

theorem comm_z_of_trivial
    (hg : ∀ u ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G), g * u * g⁻¹ * u⁻¹ ∈ zpowers z)
    (hZQ : Zs ≤ Q) : g * z * g⁻¹ * z⁻¹ = 1 := by
  rcases H.xsub.mem_zpowers_z_iff.mp (hg z (H.Zs_le_U hZQ H.z_mem_Zs)) with h | h
  · exact h
  · exfalso
    have h' : g * z * g⁻¹ * z⁻¹ = z := h
    have h3 : g * z * g⁻¹ = 1 := by
      calc g * z * g⁻¹ = (g * z * g⁻¹ * z⁻¹) * z := by group
        _ = z * z := by rw [h']
        _ = 1 := H.xsub.z_mul_z
    apply H.z_ne_one
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [h3]; group

theorem comm_mul_of_trivial
    (hg : ∀ u ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G), g * u * g⁻¹ * u⁻¹ ∈ zpowers z)
    {u v : G} (hu : u ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G))
    (hv : v ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G)) :
    g * (u * v) * g⁻¹ * (u * v)⁻¹ = (g * u * g⁻¹ * u⁻¹) * (g * v * g⁻¹ * v⁻¹) := by
  have hcom : g * v * g⁻¹ * v⁻¹ * u = u * (g * v * g⁻¹ * v⁻¹) := by
    rcases H.xsub.mem_zpowers_z_iff.mp (hg v hv) with h | h
    · rw [h, one_mul, mul_one]
    · rw [h]
      exact (H.xsub.z_comm hu.1).symm
  calc g * (u * v) * g⁻¹ * (u * v)⁻¹ =
      (g * u * g⁻¹ * u⁻¹) * (u * (g * v * g⁻¹ * v⁻¹)) * u⁻¹ := by group
    _ = (g * u * g⁻¹ * u⁻¹) * ((g * v * g⁻¹ * v⁻¹) * u) * u⁻¹ := by rw [hcom]
    _ = (g * u * g⁻¹ * u⁻¹) * (g * v * g⁻¹ * v⁻¹) := by group

theorem comm_eq_of_cl_eq
    (hg : ∀ u ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G), g * u * g⁻¹ * u⁻¹ ∈ zpowers z)
    (hZQ : Zs ≤ Q) {u v : G} (hu : u ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G))
    (hv : v ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G)) (h : H.xsub.cl u = H.xsub.cl v) :
    g * v * g⁻¹ * v⁻¹ = g * u * g⁻¹ * u⁻¹ := by
  have hw : u⁻¹ * v ∈ zpowers z := (H.xsub.cl_eq_cl_iff hu.1 hv.1).mp h
  have hwU : u⁻¹ * v ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) := mul_mem (inv_mem hu) hv
  have hcw : g * (u⁻¹ * v) * g⁻¹ * (u⁻¹ * v)⁻¹ = 1 := by
    rcases H.xsub.mem_zpowers_z_iff.mp hw with h1 | h1
    · have h1' : u⁻¹ * v = 1 := h1
      rw [h1']
      group
    · have h1' : u⁻¹ * v = z := h1
      rw [h1']
      exact H.comm_z_of_trivial hg hZQ
  have e : v = u * (u⁻¹ * v) := by group
  rw [e, H.comm_mul_of_trivial hg hu hwU, hcw, mul_one]

omit H [Finite G] in
theorem comm_eq_one_iff {a b : G} : a * b * a⁻¹ * b⁻¹ = 1 ↔ a * b = b * a := by
  constructor
  · intro h
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [h, one_mul]
  · intro h
    rw [h]
    group

theorem exists_mem_Q₁_of_trivial
    (hg : ∀ u ∈ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G), g * u * g⁻¹ * u⁻¹ ∈ zpowers z)
    (hZQ : Zs ≤ Q) : ∃ q ∈ Q₀ ⊔ Q, q⁻¹ * g ∈
      centralizer (((Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) : Subgroup G) : Set G) := by
  classical
  obtain ⟨z₂, hz₂, hz₂z⟩ := H.exists_z₂
  set U' := (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) with hU'
  set A' := perp H.xsub.q ((ZMod 2) ∙ H.xsub.cl z₂) with hA'
  have hUeq : U' = H.xsub.clPre A' := H.centralizer_Zs_eq_clPre hZQ hz₂ hz₂z
  have hz1 : z ≠ 1 := H.z_ne_one
  have hzz : z * z = 1 := H.xsub.z_mul_z
  let r : H.xsub.Qt → G := fun v => Classical.choose (H.xsub.exists_cl v)
  have hr : ∀ v, r v ∈ H.xsub.Q₁ ∧ H.xsub.cl (r v) = v := fun v =>
    Classical.choose_spec (H.xsub.exists_cl v)
  have hrU : ∀ v ∈ A', r v ∈ U' := fun v hv => by
    rw [hUeq]
    exact ⟨(hr v).1, (hr v).2.symm ▸ hv⟩
  let c : H.xsub.Qt → G := fun v => g * r v * g⁻¹ * (r v)⁻¹
  have hc : ∀ v ∈ A', c v = 1 ∨ c v = z := fun v hv => H.xsub.mem_zpowers_z_iff.mp (hg _ (hrU v hv))
  have hcu : ∀ u ∈ U', c (H.xsub.cl u) = g * u * g⁻¹ * u⁻¹ := fun u hu => by
    have hA : H.xsub.cl u ∈ A' := by
      have hu' := hu
      rw [hUeq] at hu'
      exact hu'.2
    exact H.comm_eq_of_cl_eq hg hZQ hu (hrU _ hA) (hr _).2.symm
  let δ : H.xsub.Qt → ZMod 2 := fun v => if c v = 1 then 0 else 1
  have hadd : ∀ v ∈ A', ∀ w ∈ A', δ (v + w) = δ v + δ w := by
    intro v hv w hw
    have hvw : v + w ∈ A' := A'.add_mem hv hw
    have hmulU : r v * r w ∈ U' := mul_mem (hrU v hv) (hrU w hw)
    have hcl : H.xsub.cl (r v * r w) = v + w := by
      rw [H.xsub.cl_mul (hr v).1 (hr w).1, (hr v).2, (hr w).2]
    have e : c (v + w) = c v * c w := by
      rw [← hcl, hcu _ hmulU]
      exact H.comm_mul_of_trivial hg (hrU v hv) (hrU w hw)
    have hδ : ∀ t, c t = 1 ∨ c t = z → (δ t = 0 ↔ c t = 1) := by
      intro t ht
      simp only [δ]
      split_ifs with h
      · exact ⟨fun _ => h, fun _ => rfl⟩
      · exact ⟨fun h' => absurd h' (by decide), fun h' => absurd h' h⟩
    rcases hc v hv with h1 | h1 <;> rcases hc w hw with h2 | h2
    · have h3 : c (v + w) = 1 := by rw [e, h1, h2, one_mul]
      rw [(hδ _ (Or.inl h1)).mpr h1, (hδ _ (Or.inl h2)).mpr h2, (hδ _ (Or.inl h3)).mpr h3,
        add_zero]
    · have h3 : c (v + w) = z := by rw [e, h1, h2, one_mul]
      have hv0 := (hδ _ (Or.inl h1)).mpr h1
      have hw1 : δ w = 1 := by simp [δ, h2, hz1]
      have h31 : δ (v + w) = 1 := by simp [δ, h3, hz1]
      rw [hv0, hw1, h31, zero_add]
    · have h3 : c (v + w) = z := by rw [e, h1, h2, mul_one]
      have hw0 := (hδ _ (Or.inl h2)).mpr h2
      have hv1 : δ v = 1 := by simp [δ, h1, hz1]
      have h31 : δ (v + w) = 1 := by simp [δ, h3, hz1]
      rw [hw0, hv1, h31, add_zero]
    · have h3 : c (v + w) = 1 := by rw [e, h1, h2, hzz]
      have hv1 : δ v = 1 := by simp [δ, h1, hz1]
      have hw1 : δ w = 1 := by simp [δ, h2, hz1]
      rw [(hδ _ (Or.inl h3)).mpr h3, hv1, hw1]
      decide
  let lam₀ : ↥A' →+ ZMod 2 := AddMonoidHom.mk' (fun v => δ v) fun v w => hadd v v.2 w w.2
  obtain ⟨Λ, hΛ⟩ := LinearMap.exists_extend (lam₀.toZModLinearMap 2)
  have : Module.Finite (ZMod 2) H.xsub.Qt := Module.Finite.of_finite
  obtain ⟨w, hw⟩ := (LinearMap.BilinForm.toDual (polarBilin H.xsub.q)
    H.xsub.q_nondegenerate).surjective Λ
  have hpol : ∀ v ∈ A', polar H.xsub.q w v = δ v := by
    intro v hv
    have h1 := LinearMap.congr_fun hw v
    rw [LinearMap.BilinForm.toDual_def, polarBilin_apply_apply] at h1
    rw [h1]
    exact LinearMap.congr_fun hΛ ⟨v, hv⟩
  set q₀ := r w with hq₀
  have hq₀Q : q₀ ∈ H.xsub.Q₁ := (hr w).1
  refine ⟨q₀, hq₀Q, mem_centralizer_iff.mpr fun u hu => ?_⟩
  have hA : H.xsub.cl u ∈ A' := by
    have hu' := hu
    rw [hUeq] at hu'
    exact hu'.2
  have key : q₀ * u * q₀⁻¹ * u⁻¹ = g * u * g⁻¹ * u⁻¹ := by
    have hp := hpol _ hA
    rw [← (hr w).2] at hp
    have hcq := H.xsub.mem_zpowers_z_iff.mp (H.commutator_mem_zpowers hq₀Q hu.1)
    rcases hc _ hA with h | h
    · have hδ0 : δ (H.xsub.cl u) = 0 := by simp [δ, h]
      rw [hδ0, H.xsub.polar_cl_eq_zero_iff hq₀Q hu.1] at hp
      rw [← hcu u hu, h]
      exact comm_eq_one_iff.mpr hp
    · have hδ1 : δ (H.xsub.cl u) = 1 := by simp [δ, h, hz1]
      have hne : ¬ q₀ * u = u * q₀ := by
        rw [← H.xsub.polar_cl_eq_zero_iff hq₀Q hu.1, hp, hδ1]
        decide
      rw [← hcu u hu, h]
      rcases hcq with h' | h'
      · exact absurd (comm_eq_one_iff.mp h') hne
      · exact h'
  have h2 : q₀ * u * q₀⁻¹ = g * u * g⁻¹ := by
    have := congrArg (· * u) key
    simpa using this
  calc u * (q₀⁻¹ * g) = q₀⁻¹ * (q₀ * u * q₀⁻¹) * g := by group
    _ = q₀⁻¹ * (g * u * g⁻¹) * g := by rw [h2]
    _ = q₀⁻¹ * g * u := by group

end Trivial

theorem E_le_centralizer_Zs : E ≤ centralizer (Zs : Set G) := by
  have hSz := H.q0.dData.suz
  intro e he
  refine mem_centralizer_iff.mpr fun s hs => ?_
  have hs' : s ∈ sec2Z A₁ E F := by rw [← hSz.Zs_eq]; exact hs
  exact (mem_centralizer_iff.mp (mem_inf.mp hs').2.2 e (mem_sup_left he)).symm

theorem E_le_N
    (hCBz : ∀ k ∈ sec3B A₁ x ⊓ centralizer ({z} : Set G), ∃ b₀ ∈ B₀, ∃ i : ℤ, k = b₀ * x ^ i) :
    E ≤ H.xsub.N := by
  have hS := H.q0.dData.suz
  have hEB : E ≤ sec3B A₁ x :=
    hS.setting.frame.E_le.trans (sup_le (le_sec3B (A₁_le_centralizer hS.setting.toSec3Pre))
      hS.R_le)
  intro e he
  have hez : e ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.mpr
    (mem_centralizer_iff.mp (H.E_le_centralizer_Zs he) z H.z_mem_Zs).symm
  obtain ⟨b₀, hb₀, i, rfl⟩ := hCBz e (mem_inf.mpr ⟨hEB he, hez⟩)
  exact mul_mem (H.B₀_le_N hb₀) (zpow_mem H.x_mem_N i)

theorem le_N_of_odd
    (h17 : Step17G24Odd)
    (hinner : ∀ w : G, w * x = x * w →
      ∃ b ∈ sec3B A₁ x, b⁻¹ * w ∈ centralizer (sec3B A₁ x : Set G))
    (hCBz : ∀ k ∈ sec3B A₁ x ⊓ centralizer ({z} : Set G), ∃ b₀ ∈ B₀, ∃ i : ℤ, k = b₀ * x ^ i)
    {W : Subgroup G} (hWo : Odd (Nat.card W)) (hEW : E ≤ normalizer (W : Set G))
    (hxW : x ∈ normalizer (W : Set G)) (hWz : W ≤ centralizer ({z} : Set G)) :
    W ≤ H.xsub.N := by
  have hS := H.q0.dData.suz.setting
  have hWX := H.le_zpowers_sup_of_odd h17 hWo hEW hxW
  have hxZ : x ∈ centerIn A₁ := by rw [hS.center_A₁]; exact mem_zpowers x
  have hxA : x ∈ A := hS.le hxZ.1
  have hOK : AS76b.oddCoreIn (centralizer (A : Set G)) ≤ centralizer (A : Set G) :=
    AS76b.oddCoreIn_le _
  have hWx : W ≤ centralizer ({x} : Set G) := hWX.trans (sup_le
    (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
    (fun k hk => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hOK hk) x hxA).symm))
  intro w hw
  exact H.mem_normalizer_of_comm h17 hinner hCBz (mem_centralizer_singleton_iff.mp (hWx hw))
    (mem_centralizer_singleton_iff.mp (hWz hw))

theorem centralizer_U_le_N
    (h17 : Step17G24Odd)
    (hinner : ∀ w : G, w * x = x * w →
      ∃ b ∈ sec3B A₁ x, b⁻¹ * w ∈ centralizer (sec3B A₁ x : Set G))
    (hCBz : ∀ k ∈ sec3B A₁ x ⊓ centralizer ({z} : Set G), ∃ b₀ ∈ B₀, ∃ i : ℤ, k = b₀ * x ^ i)
    (hZQ : Zs ≤ Q) :
    centralizer (((Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) : Subgroup G) : Set G) ≤ H.xsub.N := by
  set U' := (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) with hU'
  set C₁ := centralizer (U' : Set G) with hC₁
  have hEU : E ≤ normalizer (U' : Set G) := fun e he =>
    H.mem_normalizer_U (H.E_le_N hCBz he) (H.E_le_centralizer_Zs he)
  have hxU : x ∈ normalizer (U' : Set G) :=
    H.mem_normalizer_U H.x_mem_N (mem_centralizer_iff.mpr fun s hs => (H.x_comm_Zs hs).symm)
  have hNC : normalizer (U' : Set G) ≤ normalizer (C₁ : Set G) := fun g hg =>
    AS81.mem_normalizer_centralizer hg
  have hCO := AS76b.normalizer_le_normalizer_oddCoreIn C₁
  have hOz : AS76b.oddCoreIn C₁ ≤ centralizer ({z} : Set G) := fun w hw =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (AS76b.oddCoreIn_le C₁ hw) z
      (H.Zs_le_U hZQ H.z_mem_Zs)).symm
  have hON := H.le_N_of_odd h17 hinner hCBz (AS76b.odd_card_oddCoreIn C₁)
    (fun e he => hCO (hNC (hEU he))) (hCO (hNC hxU)) hOz
  exact (H.centralizer_U_le_sup hZQ).trans
    (sup_le (fun s hs => H.xsub.le_N (H.Q_le (hZQ hs))) hON)

theorem mem_N_of_mem_normalizer_U
    (h17 : Step17G24Odd)
    (hinner : ∀ w : G, w * x = x * w →
      ∃ b ∈ sec3B A₁ x, b⁻¹ * w ∈ centralizer (sec3B A₁ x : Set G))
    (hCBz : ∀ k ∈ sec3B A₁ x ⊓ centralizer ({z} : Set G), ∃ b₀ ∈ B₀, ∃ i : ℤ, k = b₀ * x ^ i)
    (hZQ : Zs ≤ Q) {n : G}
    (hnU : n ∈ normalizer (((Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) : Subgroup G) : Set G))
    (hnz : n * z = z * n) : n ∈ H.xsub.N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U' := (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) with hU'
  set C₁ := centralizer (U' : Set G) with hC₁
  set Y := (Q₀ ⊔ Q) ⊔ C₁ with hY
  have hCN := H.centralizer_U_le_N h17 hinner hCBz hZQ
  have hYN : Y ≤ H.xsub.N := sup_le H.xsub.le_N hCN
  have hYmul : ((Y : Subgroup G) : Set G) = ((Q₀ ⊔ Q : Subgroup G) : Set G) * (C₁ : Set G) :=
    coe_mul_of_left_le_normalizer_right _ _ H.Q₁_le_normalizer_C
  have hconj : (Q₀ ⊔ Q).map (MulAut.conj n).toMonoidHom ≤ Y := by
    rintro _ ⟨q, hq, rfl⟩
    change n * q * n⁻¹ ∈ Y
    have htriv : ∀ u ∈ U', n * q * n⁻¹ * u * (n * q * n⁻¹)⁻¹ * u⁻¹ ∈ zpowers z := by
      intro u hu
      have hu' : n⁻¹ * u * n ∈ U' := by
        have h := (mem_normalizer_iff.mp (inv_mem hnU) u).mp hu
        rwa [inv_inv] at h
      have hc := H.commutator_mem_zpowers hq hu'.1
      have hnz' : n * z * n⁻¹ = z := by rw [hnz, mul_inv_cancel_right]
      have e : n * q * n⁻¹ * u * (n * q * n⁻¹)⁻¹ * u⁻¹ =
          n * (q * (n⁻¹ * u * n) * q⁻¹ * (n⁻¹ * u * n)⁻¹) * n⁻¹ := by group
      rw [e]
      rcases H.xsub.mem_zpowers_z_iff.mp hc with h | h
      · rw [h, mul_one, mul_inv_cancel]
        exact one_mem _
      · have h' : q * (n⁻¹ * u * n) * q⁻¹ * (n⁻¹ * u * n)⁻¹ = z := h
        rw [h', hnz']
        exact mem_zpowers z
    obtain ⟨q', hq', hq'c⟩ := H.exists_mem_Q₁_of_trivial htriv hZQ
    have hmem : n * q * n⁻¹ ∈ ((Y : Subgroup G) : Set G) := by
      rw [hYmul]
      exact ⟨q', hq', q'⁻¹ * (n * q * n⁻¹), hq'c, by group⟩
    exact hmem
  have hQ2 : IsPGroup 2 ↥(Q₀ ⊔ Q) := IsPGroup.of_card (n := 9) H.card
  have hP2 : IsPGroup 2 ((Q₀ ⊔ Q).map (MulAut.conj n).toMonoidHom) := hQ2.map _
  have hPN : (Q₀ ⊔ Q).map (MulAut.conj n).toMonoidHom ≤ normalizer ((Q₀ ⊔ Q : Subgroup G) :
      Set G) := hconj.trans hYN
  have hsup := hP2.to_sup_of_normal_right' hQ2 hPN
  have heq := (H.isSylowOf_Q₁_sup hZQ).eq_of_le le_sup_right (sup_le hconj le_sup_left) hsup
  exact AS76b.mem_normalizer_of_map_conj_le (le_sup_left.trans heq.le)

end Sec38Hyp

end CFSG.ComponentClassification.AS81
