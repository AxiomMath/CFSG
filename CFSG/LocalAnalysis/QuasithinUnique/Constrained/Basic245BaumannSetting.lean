module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245BaumannRho
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBaumann
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatSetting
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin Subgroup CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell CFSG.Quasithin.BlueprintB2
open scoped commutatorElement MatrixGroups

namespace C56

variable {G : Type} [Group G] [Finite G]

section Transfer

variable {R H : Subgroup G}

theorem elemThompsonIn_subgroupOf_map' (hRH : R ≤ H) :
    (elemThompsonIn 2 (R.subgroupOf H)).map H.subtype = elemThompsonIn 2 R := by
  rw [← elemThompsonIn_map_of_injective 2 H.subtype H.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le hRH]

theorem elemThompsonIn_subgroupOf_map (hRH : R ≤ H) :
    (elemThompsonIn 2 (R.subgroupOf H)).map H.subtype = thompsonJ R := by
  rw [elemThompsonIn_subgroupOf_map' hRH]
  exact elemThompson_map_subtype_eq_thompsonJ R

theorem elemCenterIn_subgroupOf_map (hRH : R ≤ H) :
    (elemCenterIn 2 (R.subgroupOf H)).map H.subtype = elemCenterIn 2 R := by
  have hJ' := elemThompsonIn_subgroupOf_map' hRH
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hxR, hx2, hxj⟩ := mem_elemCenterIn_iff_centralizer.mp hx
    refine mem_elemCenterIn_iff_centralizer.mpr ⟨Subgroup.mem_subgroupOf.mp hxR, ?_, ?_⟩
    · simpa using congrArg Subtype.val hx2
    · intro j hj
      rw [← hJ'] at hj
      obtain ⟨j', hj', rfl⟩ := hj
      exact congrArg Subtype.val (hxj j' hj')
  · intro hy
    obtain ⟨hyR, hy2, hyj⟩ := mem_elemCenterIn_iff_centralizer.mp hy
    refine ⟨⟨y, hRH hyR⟩, mem_elemCenterIn_iff_centralizer.mpr
      ⟨Subgroup.mem_subgroupOf.mpr hyR, Subtype.ext (by simpa using hy2), ?_⟩, rfl⟩
    intro j' hj'
    have : (j' : G) ∈ elemThompsonIn 2 R := by
      rw [← hJ']; exact ⟨j', hj', rfl⟩
    exact Subtype.ext (hyj _ this)

theorem elemBaumannIn_subgroupOf_map (hRH : R ≤ H) :
    (elemBaumannIn 2 (R.subgroupOf H)).map H.subtype = baum R := by
  rw [← elemBaumann_map_subtype_eq_baum]
  show _ = elemBaumannIn 2 R
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hxR, hxe⟩ := mem_elemBaumannIn_iff.mp hx
    refine mem_elemBaumannIn_iff.mpr ⟨Subgroup.mem_subgroupOf.mp hxR, fun e he => ?_⟩
    rw [← elemCenterIn_subgroupOf_map hRH] at he
    obtain ⟨e', he', rfl⟩ := he
    exact congrArg Subtype.val (hxe e' he')
  · intro hy
    obtain ⟨hyR, hye⟩ := mem_elemBaumannIn_iff.mp hy
    refine ⟨⟨y, hRH hyR⟩, mem_elemBaumannIn_iff.mpr
      ⟨Subgroup.mem_subgroupOf.mpr hyR, fun e he => ?_⟩, rfl⟩
    have he' : (e : G) ∈ elemCenterIn 2 R := by
      rw [← elemCenterIn_subgroupOf_map hRH]; exact ⟨e, he, rfl⟩
    exact Subtype.ext (hye _ he')

end Transfer

section OddOrder

variable {R H L : Subgroup G}

theorem oddOrderSubgroup_top_eq (hLs : IsShort2 L) (hHLR : H = L ⊔ R) (hR2 : IsPGroup 2 R)
    (hRN : R ≤ normalizer (L : Set G)) (hLH : L ≤ H) :
    oddOrderSubgroup (⊤ : Subgroup ↥H) = L.subgroupOf H := by
  apply le_antisymm
  · refine oddOrderSubgroup_le_of_pow_mem fun h _ => ?_
    have hh : (h : G) ∈ L ⊔ R := hHLR ▸ h.2
    obtain ⟨k, hk⟩ := C1.exists_pow_mem_of_mem_sup hR2 hRN hh
    exact ⟨k, Subgroup.mem_subgroupOf.mpr (by simpa using hk)⟩
  · intro l hl
    set N₀ := oddOrderSubgroup (⊤ : Subgroup ↥H) with hN₀
    have hN₀n : N₀.Normal := by
      apply Subgroup.normalizer_eq_top_iff.mp
      refine top_le_iff.mp fun g _ => normalizer_le_normalizer_oddOrderSubgroup (⊤ : Subgroup ↥H)
        (?_ : g ∈ Subgroup.normalizer ((⊤ : Subgroup ↥H) : Set ↥H))
      rw [Subgroup.mem_normalizer_iff]
      intro x
      simp
    let N : Subgroup ↥L := N₀.comap (Subgroup.inclusion hLH)
    have hNn : N.Normal := hN₀n.comap _
    have hN2 : IsPGroup 2 (↥L ⧸ N) := by
      intro x
      induction x using QuotientGroup.induction_on with | _ g => ?_
      obtain ⟨k, hk⟩ := exists_pow_mem_oddOrderSubgroup (G := ↥H) (H := ⊤)
        (h := Subgroup.inclusion hLH g) (Subgroup.mem_top _)
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      show Subgroup.inclusion hLH (g ^ 2 ^ k) ∈ N₀
      rw [map_pow]
      exact hk
    have hNtop : N = ⊤ := hLs.1 N hN2
    have : (⟨(l : G), Subgroup.mem_subgroupOf.mp hl⟩ : ↥L) ∈ N := by rw [hNtop]; trivial
    exact this

end OddOrder

section Setting

variable {R H L : Subgroup G} {F : Type} [Field F]

theorem exists_natQuotSetting [Fintype F] [CharP F 2] (hF : 2 < Fintype.card F) (D : Lin2Data L F)
    (hLs : IsShort2 L) (hmin : IsMinimalParabolic R H) (hLH : L ≤ H) (hHLR : H = L ⊔ R)
    (hRN : R ≤ normalizer (L : Set G)) :
    ∃ (M : Subgroup ↥H) (ρ : ↥H →* Gamma F)
      (φ : ↥((blockU L).subgroupOf H) →* Multiplicative (Fin 2 → F)),
      IsNatQuotSetting (R.subgroupOf H) M ((blockU L).subgroupOf H) ρ φ ∧
      (∀ l : ↥L, ((ρ ⟨l, hLH l.2⟩ : Gamma F) : Equiv.Perm (Fin 2 → F)) = slPerm F (D.α l)) := by
  classical
  have hR2 : IsPGroup 2 R := hmin.1.isPGroup
  have hRH : R ≤ H := hmin.1.le
  have hHN : H ≤ normalizer (L : Set G) := by
    rw [hHLR]; exact sup_le Subgroup.le_normalizer hRN
  have hUL : blockU L ≤ L := (C1.blockU_le_blockQ hLs).trans (C1.blockQ_le L)
  have hUH : blockU L ≤ H := hUL.trans hLH
  have hH2 : ∀ g ∈ H, ∃ k : ℕ, g ^ 2 ^ k ∈ L := fun g hg =>
    C1.exists_pow_mem_of_mem_sup hR2 hRN (hHLR ▸ hg)
  have hCent : H ⊓ centralizer (blockU L : Set G) = pCoreOf 2 H :=
    C1.inf_centralizer_blockU_eq hLs hLH hHN hH2
  obtain ⟨ρ, φ, hφs, hφk, hφe, hρL⟩ := exists_rho_phi hF D hHN hHLR hR2 hRH hLH
  obtain ⟨K, hRK, hKH, hK⟩ := hmin.2.2
  have hcentV : ∀ y : ↥H, y ∈ centralizer (((blockU L).subgroupOf H : Subgroup ↥H) : Set ↥H) ↔
      (y : G) ∈ pCoreOf 2 H := by
    intro y
    rw [mem_centralizer_subgroupOf_iff hUH, ← hCent]
    exact ⟨fun hy => ⟨y.2, hy⟩, fun hy => hy.2⟩
  refine ⟨K.subgroupOf H, ρ, φ.comp (Subgroup.subgroupOfEquivOfLe hUH).toMonoidHom, ?_, hρL⟩
  refine
    { sylow := ?_, nonnormal := ?_, le_M := ?_, M_lt := ?_, M_max := ?_, reduced := ?_,
      sl_le := ?_, two_quot := ?_, φ_surj := ?_, φ_equiv := ?_, φ_ker := ?_ }
  · refine ⟨le_top, hR2.of_equiv (Subgroup.subgroupOfEquivOfLe hRH).symm, ?_⟩
    show ¬ 2 ∣ (R.subgroupOf H).relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact hmin.1.2.2
  · exact fun hn => hmin.2.1 ((Subgroup.normal_subgroupOf_iff_le_normalizer hRH).mp hn)
  · exact fun x hx => Subgroup.mem_subgroupOf.mpr (hRK (Subgroup.mem_subgroupOf.mp hx))
  · refine lt_top_iff_ne_top.mpr fun h => ?_
    have hHK : H ≤ K := fun x hx =>
      Subgroup.mem_subgroupOf.mp (show (⟨x, hx⟩ : ↥H) ∈ K.subgroupOf H by rw [h]; trivial)
    exact absurd hHK (not_le_of_gt hKH)
  · intro Y hRY hY
    have hRY' : R ≤ Y.map H.subtype := by
      have := Subgroup.map_mono (f := H.subtype) hRY
      rwa [Subgroup.map_subgroupOf_eq_of_le hRH] at this
    have hYH : Y.map H.subtype < H := by
      refine lt_of_le_of_ne (map_subtype_le_self Y) fun h => ?_
      apply (lt_top_iff_ne_top.mp hY)
      refine top_unique fun x _ => ?_
      have hx : (x : G) ∈ Y.map H.subtype := by rw [h]; exact x.2
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := Subtype.ext hyx
      rwa [this] at hy
    intro y hy
    exact Subgroup.mem_subgroupOf.mpr (hK _ hRY' hYH ⟨y, hy, rfl⟩)
  · have hVn : ((blockU L).subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hUH).mpr fun g hg => C1.mem_normalizer_blockU (hHN hg)
    refine ⟨le_top, top_le_iff.mpr (Subgroup.normalizer_eq_top_iff.mpr hVn), ?_, ?_⟩
    · refine ⟨GammaExtra.isMulCommutative_iff_forall.mpr fun a ha b hb => ?_, fun x hx => ?_⟩
      · exact Subtype.ext ((C1.elemAb2_blockU hLs).1 _ (Subgroup.mem_subgroupOf.mp ha) _
          (Subgroup.mem_subgroupOf.mp hb))
      · exact Subtype.ext (by
          have := C1.blockU_sq hLs _ (Subgroup.mem_subgroupOf.mp hx)
          simpa using this)
    · intro D' _ hDn hDpow
      have hDnormal : D'.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hDn)
      have hD2 : IsPGroup 2 D' := by
        intro d
        obtain ⟨k, hk⟩ := hDpow d d.2
        have hkQ : (((d : ↥H) ^ 2 ^ k : ↥H) : G) ∈ pCoreOf 2 H := (hcentV _).mp hk
        rw [Subgroup.coe_pow] at hkQ
        obtain ⟨j, hj⟩ := C1.exists_pow_eq_one_of_isPGroup
          (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H) hkQ
        refine ⟨k + j, Subtype.ext (Subtype.ext ?_)⟩
        rw [Subgroup.coe_pow, Subgroup.coe_pow]
        show (((d : ↥H) : G)) ^ 2 ^ (k + j) = 1
        rw [pow_add, pow_mul]
        exact hj
      have hD₀H : D'.map H.subtype ≤ H := map_subtype_le_self D'
      have hD₀N : H ≤ normalizer ((D'.map H.subtype : Subgroup G) : Set G) := by
        rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hD₀H, subgroupOf_map_subtype_self]
        exact hDnormal
      have hD₀2 : IsPGroup 2 (D'.map H.subtype) :=
        hD2.of_equiv (D'.equivMapOfInjective H.subtype H.subtype_injective)
      have hle := le_pCoreOf_of_normalizes hD₀H hD₀N hD₀2
      intro d hd
      exact (hcentV d).mpr (hle ⟨d, hd, rfl⟩)
  · intro A
    obtain ⟨l, rfl⟩ := D.surj_α A
    exact ⟨⟨l, hLH l.2⟩, hρL l⟩
  · intro h
    obtain ⟨k, hk⟩ := hH2 (h : G) h.2
    refine ⟨k, ?_⟩
    rw [← map_pow]
    have hl : ((h ^ 2 ^ k : ↥H) : G) ∈ L := by simpa using hk
    exact mem_slGamma_iff.mpr ⟨D.α ⟨_, hl⟩, hρL ⟨_, hl⟩⟩
  · exact hφs.comp (Subgroup.subgroupOfEquivOfLe hUH).surjective
  · intro h v v' hv'
    exact hφe h (Subgroup.subgroupOfEquivOfLe hUH v) (Subgroup.subgroupOfEquivOfLe hUH v')
      (by simpa using congrArg Subtype.val hv')
  · rw [oddOrderSubgroup_top_eq hLs hHLR hR2 hRN hLH]
    ext v
    constructor
    · intro hv
      have h1 : (Subgroup.subgroupOfEquivOfLe hUH v) ∈ φ.ker := hv
      rw [hφk, D.ker_β, Subgroup.mem_subgroupOf] at h1
      rw [Subgroup.mem_subgroupOf, mem_centralizer_subgroupOf_iff hLH]
      exact h1.2
    · intro hv
      rw [Subgroup.mem_subgroupOf, mem_centralizer_subgroupOf_iff hLH] at hv
      show (Subgroup.subgroupOfEquivOfLe hUH v) ∈ φ.ker
      rw [hφk, D.ker_β, Subgroup.mem_subgroupOf]
      exact ⟨(Subgroup.subgroupOfEquivOfLe hUH v).2, hv⟩

end Setting

end C56

end CFSG.QuasithinUnique
