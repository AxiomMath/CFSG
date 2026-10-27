module

public import CFSG.LocalAnalysis.ComponentInitial.SelfCentralizingCoreAutomorphisms
public import CFSG.LocalAnalysis.ComponentInitial.RootPairRestriction
public import CFSG.LieType.Chevalley.SylowOpposition

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

variable {G : Type*} [Group G]

theorem map_centralizer_eq_of_fixes {Z : Subgroup G} {α : MulAut G}
    (hα : α ∈ pointwiseFixingAut Z) :
    (Subgroup.centralizer (Z : Set G)).map α.toMonoidHom = Subgroup.centralizer (Z : Set G) := by
  have key : ∀ β : MulAut G, β ∈ pointwiseFixingAut Z → ∀ h ∈ Subgroup.centralizer (Z : Set G),
      β h ∈ Subgroup.centralizer (Z : Set G) := fun β hβ h hh => by
    rw [Subgroup.mem_centralizer_iff] at hh ⊢
    intro z hz
    rw [← hβ z hz, ← map_mul, ← map_mul, hh z hz]
  refine le_antisymm (Subgroup.map_le_iff_le_comap.2 fun h hh => key α hα h hh) fun h hh => ?_
  exact ⟨α⁻¹ h, key α⁻¹ (inv_mem hα) h hh, α.apply_symm_apply h⟩

theorem map_eq_of_fixes {K : Subgroup G} {α : MulAut G} (hα : α ∈ pointwiseFixingAut K) :
    K.map α.toMonoidHom = K := by
  ext x
  rw [Subgroup.mem_map_equiv]
  constructor
  · intro hx
    rw [← α.apply_symm_apply x, hα _ hx]
    exact hx
  · intro hx
    have h := (inv_mem hα : α⁻¹ ∈ pointwiseFixingAut K) x hx
    rw [MulAut.inv_apply] at h
    rw [h]
    exact hx

theorem map_normalizer_eq_of_fixes {K : Subgroup G} {α : MulAut G}
    (hα : α ∈ pointwiseFixingAut K) :
    (Subgroup.normalizer (K : Set G)).map α.toMonoidHom = Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.map_equiv_normalizer_eq, map_eq_of_fixes hα]

theorem pointwiseFixingAut_abelian_pGroup {L : Type*} [Group L] [Finite L] {p : ℕ}
    [Fact p.Prime] {Q : Subgroup L} [Q.Normal] (hQ : Subgroup.centralizer (Q : Set L) ≤ Q)
    (hp : IsPGroup p Q) :
    IsPGroup p (pointwiseFixingAut Q) ∧ ∀ α β : pointwiseFixingAut Q, α * β = β * α := by
  obtain ⟨-, -, h1, h2⟩ := Tits_self_centralizing_core_automorphism_kernel hQ p hp
  exact ⟨h1, h2⟩

theorem centralizer_subgroupOf_le {H J : Subgroup G} (hJH : J ≤ H)
    (h : H ⊓ Subgroup.centralizer (J : Set G) ≤ J) :
    Subgroup.centralizer ((J.subgroupOf H : Subgroup H) : Set H) ≤ J.subgroupOf H := by
  intro x hx
  rw [Subgroup.mem_subgroupOf]
  refine h (Subgroup.mem_inf.2 ⟨x.2, Subgroup.mem_centralizer_iff.2 fun j hj => ?_⟩)
  have := Subgroup.mem_centralizer_iff.1 hx ⟨j, hJH hj⟩ (Subgroup.mem_subgroupOf.2 hj)
  exact congrArg Subtype.val this

theorem isPGroup_subgroupOf {p : ℕ} {H J : Subgroup G} (hJH : J ≤ H) (hJ : IsPGroup p J) :
    IsPGroup p (J.subgroupOf H) :=
  hJ.of_equiv (Subgroup.subgroupOfEquivOfLe hJH).symm

theorem exists_conj_mul_mem_pairAutSubgroup [Finite G] {p : ℕ} [Fact p.Prime] (S : Sylow p G)
    (α : MulAut G) : ∃ (c : G) (β : MulAut G),
      β ∈ pairAutSubgroup (S : Subgroup G) (S : Subgroup G) ∧ α = MulAut.conj c * β := by
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G S (α • S)
  refine ⟨c, (MulAut.conj c)⁻¹ * α, ?_, by rw [mul_inv_cancel_left]⟩
  have e : ((MulAut.conj c)⁻¹).toMonoidHom.comp (MulAut.conj c).toMonoidHom =
      MonoidHom.id G := MonoidHom.ext fun x => (MulAut.conj c).symm_apply_apply x
  have h : (S : Subgroup G).map ((MulAut.conj c)⁻¹ * α).toMonoidHom = S := by
    rw [← coe_mulAut_smul_sylow, mul_smul, ← hc, coe_mulAut_smul_sylow, coe_smul_sylow_eq_map,
      Subgroup.map_map, e, Subgroup.map_id]
  exact ⟨h, h⟩

theorem tits_Sylow_local_Schreier_criterion [Finite G] {p : ℕ} [Fact p.Prime] (S : Sylow p G)
    (H : Subgroup G)
    (hH : H = Subgroup.centralizer
      (((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype : Subgroup G) : Set G))
    (K : Subgroup G) (hKS : K ≤ S) (N : Subgroup G) (hN : N = Subgroup.normalizer (K : Set G))
    (J : Subgroup G) (hJp : IsPGroup p J) (hJS : J ≤ S) (hJH : J ≤ H)
    (hJn : (J.subgroupOf H).Normal) (hCJ : H ⊓ Subgroup.centralizer (J : Set G) ≤ J)
    (hCK : N ⊓ Subgroup.centralizer (K : Set G) ≤ K) (hgen : H ⊔ N = ⊤) :
    IsPGroup p (pointwiseFixingAut (S : Subgroup G)) ∧
    (∀ α β : pointwiseFixingAut (S : Subgroup G), α * β = β * α) ∧
    (Group.IsSolvable (MulAut (S : Subgroup G)) → Group.IsSolvable (Outer G)) ∧
    (IsPGroup p (MulAut (S : Subgroup G)) → IsPGroup p (Outer G)) := by
  classical
  set C := pointwiseFixingAut (S : Subgroup G)
  have hZS : ((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype : Subgroup G) ≤ S :=
    Subgroup.map_subtype_le _
  have hCH : ∀ α ∈ C, H.map α.toMonoidHom = H := fun α hα => by
    rw [hH]
    exact map_centralizer_eq_of_fixes fun z hz => hα z (hZS hz)
  have hCN : ∀ α ∈ C, N.map α.toMonoidHom = N := fun α hα => by
    rw [hN]
    exact map_normalizer_eq_of_fixes fun k hk => hα k (hKS hk)
  have hKN : K ≤ N := hN ▸ Subgroup.le_normalizer
  have hJ' : Subgroup.centralizer ((J.subgroupOf H : Subgroup H) : Set H) ≤ J.subgroupOf H :=
    centralizer_subgroupOf_le hJH hCJ
  have hKn : (K.subgroupOf N).Normal := by
    subst hN
    exact Subgroup.normal_in_normalizer
  have hK' : Subgroup.centralizer ((K.subgroupOf N : Subgroup N) : Set N) ≤ K.subgroupOf N :=
    centralizer_subgroupOf_le hKN hCK
  have hKp : IsPGroup p K := S.isPGroup'.to_le hKS
  obtain ⟨hPJ, hcommJ⟩ := pointwiseFixingAut_abelian_pGroup hJ'
    (isPGroup_subgroupOf hJH hJp)
  obtain ⟨hPK, hcommK⟩ := pointwiseFixingAut_abelian_pGroup hK' (isPGroup_subgroupOf hKN hKp)
  have hC1 : C ≤ pairAutSubgroup H N := fun α hα => ⟨hCH α hα, hCN α hα⟩
  have hC2 : C ≤ pairAutSubgroup N H := fun α hα => ⟨hCN α hα, hCH α hα⟩
  let ρH : C →* MulAut H := (pairAutRestrict H N).comp (Subgroup.inclusion hC1)
  let ρN : C →* MulAut N := (pairAutRestrict N H).comp (Subgroup.inclusion hC2)
  have hmemH : ∀ α : C, ρH α ∈ pointwiseFixingAut (J.subgroupOf H) := fun α j hj =>
    Subtype.ext (α.2 _ (hJS (Subgroup.mem_subgroupOf.1 hj)))
  have hmemN : ∀ α : C, ρN α ∈ pointwiseFixingAut (K.subgroupOf N) := fun α k hk =>
    Subtype.ext (α.2 _ (hKS (Subgroup.mem_subgroupOf.1 hk)))
  let ρ := (ρH.codRestrict _ hmemH).prod (ρN.codRestrict _ hmemN)
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro α hα1
    have h0 : ρH α = 1 := congrArg Subtype.val (congrArg Prod.fst hα1)
    have h1 : ρN α = 1 := congrArg Subtype.val (congrArg Prod.snd hα1)
    have hle : H ⊔ N ≤ MonoidHom.eqLocus (α : MulAut G).toMonoidHom (MonoidHom.id G) := by
      refine sup_le (fun x hx => ?_) fun x hx => ?_
      · exact congrArg Subtype.val (DFunLike.congr_fun h0 ⟨x, hx⟩)
      · exact congrArg Subtype.val (DFunLike.congr_fun h1 ⟨x, hx⟩)
    rw [hgen] at hle
    exact Subtype.ext (MulEquiv.ext fun g => hle (Subgroup.mem_top g))
  have hPC : IsPGroup p C := by
    refine IsPGroup.of_injective ?_ ρ hρinj
    intro x
    obtain ⟨n, hn⟩ := hPJ x.1
    obtain ⟨m, hm⟩ := hPK x.2
    refine ⟨n + m, Prod.ext ?_ ?_⟩
    · rw [Prod.pow_fst, pow_add, pow_mul, hn, one_pow, Prod.fst_one]
    · rw [Prod.pow_snd, pow_add, mul_comm, pow_mul, hm, one_pow, Prod.snd_one]
  have hcommC : ∀ α β : C, α * β = β * α := fun α β => hρinj (by
    rw [map_mul, map_mul]
    exact Prod.ext (hcommJ _ _) (hcommK _ _))
  refine ⟨hPC, hcommC, ?_, ?_⟩
  all_goals
    set R := pairAutSubgroup (S : Subgroup G) (S : Subgroup G)
    have hCR : C ≤ R := fun α hα => ⟨map_eq_of_fixes hα, map_eq_of_fixes hα⟩
    let r := pairAutRestrict (S : Subgroup G) (S : Subgroup G)
    have hker : ∀ α : R, r α = 1 → (α : MulAut G) ∈ C := fun α hα s hs => by
      have h := DFunLike.congr_fun hα (⟨s, hs⟩ : (S : Subgroup G))
      exact congrArg Subtype.val h
    let π : R →* Outer G := (QuotientGroup.mk' (inner G)).comp R.subtype
    have hπ : Function.Surjective π := by
      intro q
      obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective (inner G) q
      obtain ⟨c, β, hβ, rfl⟩ := exists_conj_mul_mem_pairAutSubgroup S α
      refine ⟨⟨β, hβ⟩, ?_⟩
      change ((β : MulAut G) : Outer G) = ((MulAut.conj c * β : MulAut G) : Outer G)
      rw [QuotientGroup.mk_mul,
        (QuotientGroup.eq_one_iff (N := inner G) (MulAut.conj c)).2 ⟨c, rfl⟩, one_mul]
  · intro hsolv
    have : Group.IsSolvable C := Group.isSolvable_of_comm hcommC
    have hRsolv : Group.IsSolvable R := Group.isSolvable_of_ker_le_range
      (Subgroup.inclusion hCR) r fun α hα => ⟨⟨α, hker α hα⟩, rfl⟩
    exact Group.isSolvable_of_surjective hπ
  · intro hpS
    have hPR : IsPGroup p R := by
      intro α
      obtain ⟨n, hn⟩ := hpS (r α)
      rw [← map_pow] at hn
      obtain ⟨m, hm⟩ := hPC ⟨_, hker _ hn⟩
      refine ⟨n + m, Subtype.ext ?_⟩
      have hm' := congrArg Subtype.val hm
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at hm'
      rw [SubmonoidClass.coe_pow, pow_add, pow_mul, OneMemClass.coe_one]
      exact hm'
    exact hPR.of_surjective π hπ

end CFSG.LieType.Ree
