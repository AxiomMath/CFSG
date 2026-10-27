module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S4a
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7Sp4b

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace Seven

variable {X : Type} [Group X] [Finite X]

theorem exists_D1_of_cf (hComp : CFSp4Comp) (hD : CFSp4D) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) {J L J₀ Y S : Subgroup X}
    (hLie : Blueprint.LieModel (L ⧸ pPrimeCore 2 L) .PSp 2 p f)
    (hZJ : center (J ⧸ pPrimeCore 2 J) = ⊥) {t : X} (htL : t ∈ L)
    (ht : t * t = 1) (ht1 : t ≠ 1) (hJ0J : J₀ ≤ J) (hJ0L : J₀ ≤ L)
    (hJ0t : J₀ ≤ centralizer ({t} : Set X)) (hYt : L ⊓ centralizer ({t} : Set X) ≤ Y)
    (hJ0pc : IsPComponent 2 (J₀.subgroupOf Y))
    (hsup : J₀ ⊔ (pPrimeCore 2 J).map J.subtype = J)
    (hcore : (pPrimeCore 2 J₀).map J₀.subtype = J₀ ⊓ (pPrimeCore 2 J).map J.subtype)
    (hSL : IsSylowIn (S ⊓ L) (L ⊓ centralizer ({t} : Set X)))
    (hSN : S ⊓ L ≤ normalizer (J : Set X) ⊓ normalizer (J₀ : Set X)) :
    ∃ D₁ : Subgroup X, D₁ ≤ S ⊓ L ∧ D₁ ≤ coreActionKernel J ∧
      ∃ T : Sylow 2 (J ⧸ pPrimeCore 2 J),
        Nonempty (↥D₁ ≃* ↥(T : Subgroup (J ⧸ pPrimeCore 2 J))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set t' : ↥L := ⟨t, htL⟩ with ht'
  have ht'2 : t' * t' = 1 := Subtype.ext ht
  have ht'1 : t' ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  have hJ0Lt : J₀ ≤ L ⊓ centralizer ({t} : Set X) := le_inf hJ0L hJ0t
  have hpc1 : IsPComponent 2 (J₀.subgroupOf (L ⊓ centralizer ({t} : Set X))) :=
    UnbalancedCorr.isPComponent_subgroupOf_of_le hJ0Lt hYt hJ0pc
  have hpc2 : IsPComponent 2 ((J₀.subgroupOf L).subgroupOf (centralizer ({t'} : Set ↥L))) := by
    rw [← inf_centralizer_subgroupOf htL]
    exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_left 2
      Nat.prime_two).mpr hpc1
  have hMt : J₀.subgroupOf L ≤ centralizer ({t'} : Set ↥L) := by
    rw [← inf_centralizer_subgroupOf htL]
    intro v hv
    exact mem_subgroupOf.mpr (hJ0Lt (mem_subgroupOf.mp hv))
  obtain ⟨hMbt, hMbpc⟩ := isPComponent_centralizer_map ht'2 hMt hpc2
  rw [← range_toLbar hJ0L] at hMbt hMbpc
  have hO : pPrimeCore 2 ↥(toLbar hJ0L).range = ⊥ :=
    hComp _ p f hp hp2 hf hLie _ (orderOf_mk_eq_two ht'2 ht'1) _ hMbt hMbpc
  set ι := iota hJ0J hJ0L hsup hcore hO with hι
  have hZM : center ↥(toLbar hJ0L).range = ⊥ := by
    rw [eq_bot_iff]
    intro m hm
    have h1 : ι.symm m ∈ center (J ⧸ pPrimeCore 2 J) := by
      rw [mem_center_iff]
      intro u
      apply ι.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact (mem_center_iff.mp hm (ι u))
    rw [hZJ, mem_bot] at h1
    rw [mem_bot, ← ι.apply_symm_apply m, h1, map_one]
  have hSylL := hSL.subgroupOf (inf_le_left : L ⊓ centralizer ({t} : Set X) ≤ L)
  rw [inf_centralizer_subgroupOf htL] at hSylL
  obtain ⟨hRY, hR⟩ := hSylL
  obtain ⟨R', hR'⟩ := OddQuot.exists_sylow_map (QuotientGroup.mk' (pPrimeCore 2 ↥L)) hRY hR
  have hSylb : IsSylowIn (((S ⊓ L).subgroupOf L).map (QuotientGroup.mk' (pPrimeCore 2 ↥L)))
      (centralizer ({QuotientGroup.mk' (pPrimeCore 2 ↥L) t'} : Set (L ⧸ pPrimeCore 2 L))) := by
    rw [OddQuot.centralizer_singleton_map_eq ht'2]
    exact ⟨map_mono hRY, R', hR'⟩
  obtain ⟨Db, hDbR, hDbC, T, ⟨eT⟩⟩ := hD _ p f hp hp2 hf hLie _ (orderOf_mk_eq_two ht'2 ht'1) _
    hMbt hMbpc hZM _ hSylb
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥L) with hπ
  set R₀ : Subgroup ↥L := (S ⊓ L).subgroupOf L with hR₀
  have hR₀2 : IsPGroup 2 R₀ := by
    obtain ⟨hSLle, R₁, hR₁⟩ := hSL
    have h1 : IsPGroup 2 ((S ⊓ L).subgroupOf (L ⊓ centralizer ({t} : Set X))) :=
      hR₁ ▸ R₁.isPGroup'
    have h2 := h1.of_equiv (subgroupOfEquivOfLe hSLle)
    exact h2.of_equiv (subgroupOfEquivOfLe (inf_le_right : S ⊓ L ≤ L)).symm
  set D₁' : Subgroup ↥L := R₀ ⊓ Db.comap π with hD₁'
  have hinj : Set.InjOn π (D₁' : Set ↥L) := fun u hu v hv huv =>
    OddQuot.injOn_of_isPGroup hR₀2 (mem_inf.mp hu).1 (mem_inf.mp hv).1 huv
  have hDmap : D₁'.map π = Db := by
    apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩
      exact (mem_inf.mp hu).2
    · intro w hw
      obtain ⟨u, huR, rfl⟩ := mem_map.mp (hDbR hw)
      exact mem_map_of_mem _ (mem_inf.mpr ⟨huR, hw⟩)
  refine ⟨D₁'.map L.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact mem_subgroupOf.mp (mem_inf.mp hu).1
  ·
    rintro _ ⟨u, hu, rfl⟩
    have huSL : (u : X) ∈ S ⊓ L := mem_subgroupOf.mp (mem_inf.mp hu).1
    obtain ⟨huJ, huJ0⟩ := mem_inf.mp (hSN huSL)
    have hρ := oddBarAction_eq_conj hJ0J hJ0L hsup hcore hO huJ u.2 huJ0
    have htriv : (toLbar hJ0L).range.normalizerMonoidHom
        ⟨_, mk_mem_normalizer_range hJ0L huJ0 u.2⟩ = 1 := by
      ext m
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      have hc := (mem_centralizer_iff.mp (hDbC (mem_inf.mp hu).2)) m m.2
      change π u * (m : L ⧸ pPrimeCore 2 L) * (π u)⁻¹ = m
      rw [← hc, mul_inv_cancel_right]
    rw [htriv] at hρ
    have h1 : Eight.oddBarAction J ⟨u, huJ⟩ = 1 := by
      rw [hρ]
      ext x
      simp
    exact Eight.mem_ker_oddBarAction.mp h1
  ·
    have hsurj : Function.Surjective (ι.symm.toMonoidHom : ↥(toLbar hJ0L).range →* _) := by
      rw [MulEquiv.coe_toMonoidHom]; exact ι.symm.surjective
    refine ⟨T.mapSurjective hsurj, ⟨?_⟩⟩
    have e1 : ↥(D₁'.map L.subtype) ≃* ↥D₁' := (D₁'.equivMapOfInjective _ L.subtype_injective).symm
    have e2 : ↥D₁' ≃* ↥(D₁'.map π) := by
      refine MulEquiv.ofBijective (π.subgroupMap D₁') ⟨fun u v huv => ?_,
        π.subgroupMap_surjective D₁'⟩
      exact Subtype.ext (hinj u.2 v.2 (congrArg Subtype.val huv))
    have e3 : ↥(D₁'.map π) ≃* ↥Db := MulEquiv.subgroupCongr hDmap
    have e4 : ↥(T : Subgroup ↥(toLbar hJ0L).range) ≃*
        ↥((T.mapSurjective hsurj : Sylow 2 (J ⧸ pPrimeCore 2 J)) :
          Subgroup (J ⧸ pPrimeCore 2 J)) := by
      rw [Sylow.coe_mapSurjective]
      exact (T : Subgroup ↥(toLbar hJ0L).range).equivMapOfInjective _ ι.symm.injective
    exact ((e1.trans e2).trans e3).trans (eT.trans e4)

namespace Setting

variable (s : Setting X)

theorem exists_D1 (hConj : CFSp4Conj) (hComp : CFSp4Comp) (hOut : CFSp4Outer)
    (hCent : CFL2Cent) (hD : CFSp4D) :
    ∃ D₁ : Subgroup X, D₁ ≤ s.h.P ∧ D₁ ≤ Lay s.h s.y ∧
      ∃ T : Sylow 2 (s.h.J ⧸ pPrimeCore 2 s.h.J),
        Nonempty (↥D₁ ≃* ↥(T : Subgroup (s.h.J ⧸ pPrimeCore 2 s.h.J))) := by
  obtain ⟨c, hc, hcc, hacL⟩ := s.exists_c hConj hComp hOut hCent
  have hSL : IsSylowIn (s.h.S ⊓ Lay s.h s.y)
      (Lay s.h s.y ⊓ centralizer ({s.h.a * c} : Set X)) := by
    rw [s.L_inf_centralizer_eq hc]
    exact s.sylow_S_inf_L
  have hSN : s.h.S ⊓ Lay s.h s.y ≤
      normalizer (s.h.J : Set X) ⊓ normalizer (J0 s.h s.y : Set X) := by
    intro g hg
    obtain ⟨hgS, hgL⟩ := mem_inf.mp hg
    have hgJ := s.h.S_le_normalizer hgS
    exact mem_inf.mpr ⟨hgJ, Hyp52.mem_normalizer_secJ0 (h := s.h) (y := s.y)
      (centralizer_le_normalizer _ (s.L_le_centralizer hgL)) hgJ⟩
  obtain ⟨D₁, hD₁SL, hD₁K, T, eT⟩ := exists_D1_of_cf hComp hD s.hp' s.hp2' s.hf' s.hLLie s.hZJ
    hacL (ac_mul_ac hc hcc) (ac_ne_one hc) s.J0_le_J s.J0_le_L (J0_le_centralizer_ac hc)
    (s.L_inf_centralizer_le hc) s.isPComponent_J0 s.J0_sup_core.1 s.J0_sup_core.2 hSL hSN
  exact ⟨D₁, le_inf (hD₁SL.trans inf_le_left) hD₁K, hD₁SL.trans inf_le_right, T, eT⟩

end Setting

end Seven

end CFSG.ComponentClassification.GSThmB
