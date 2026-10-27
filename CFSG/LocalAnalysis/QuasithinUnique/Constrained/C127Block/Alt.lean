module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.C127Block.Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127MAut
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenModule
public import CFSG.Quasithin.Background.B69Alt
public import CFSG.Quasithin.Background.G64Realize

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.AGLEmbeddingD2
open scoped commutatorElement

namespace L246C127

namespace C127Block

open MAut

variable {G : Type} [Group G] [Finite G]

private def coreModEquivEven (m : ℕ) : ↥(G6.coreMod m) ≃* Multiplicative (evenWeight m) where
  toFun x := Multiplicative.ofAdd ⟨Multiplicative.toAdd (x : G6.PermMod m), x.2⟩
  invFun y := ⟨Multiplicative.ofAdd
    ((Multiplicative.toAdd y : evenWeight m) : Fin m → ZMod 2), (Multiplicative.toAdd y).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private theorem symCoreWith_of_coreAct {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {N : ℕ}
    (θ : ↥L ≃* Equiv.Perm (Fin N)) (β : ↥(commV L) ≃* ↥(G6.coreMod N))
    (hequiv : ∀ (x : ↥L) (p : ↥(commV L)) (hp : (x : MulAut W) p ∈ commV L),
      β ⟨(x : MulAut W) p, hp⟩ = G6.coreAct N (θ x) (β p)) :
    GN.SymCoreWith L N θ (β.trans (coreModEquivEven N)) := by
  intro h u hu i
  show Multiplicative.toAdd ((β ⟨(h : MulAut W) u, hu⟩ : ↥(G6.coreMod N)) : G6.PermMod N) i =
    Multiplicative.toAdd ((β u : ↥(G6.coreMod N)) : G6.PermMod N) ((θ h)⁻¹ i)
  rw [hequiv h u hu]
  exact G6.permAct_apply N (θ h) (β u) i

theorem isAltType_of_symCore {V K : Subgroup G} (hV : IsElemAbelian 2 V) {N : ℕ} (h5 : 5 ≤ N) (hodd : Odd N)
    (hKN : K ≤ Subgroup.normalizer (V : Set G)) (hshort : IsShort2 K) (hUV : blockU K ≤ V)
    (hVK : ⁅V, K⁆ ≤ blockU K)
    (hker : (toAutI hV K hKN).ker = CFSG.pCore 2 ↥K)
    {L : Subgroup (MulAut (IntMod V hV))} (hKL : autI hV K ≤ L)
    (θ : ↥L ≃* Equiv.Perm (Fin N)) (β : ↥(commV L) ≃* Multiplicative (evenWeight N))
    (hβ : ∀ (h : ↥L) (u : ↥(commV L)) (hu : (h : MulAut (IntMod V hV)) (u : IntMod V hV) ∈ commV L)
      (i : Fin N),
      ((Multiplicative.toAdd (β ⟨(h : MulAut (IntMod V hV)) u, hu⟩) : evenWeight N) :
          Fin N → ZMod 2) i =
        ((Multiplicative.toAdd (β u) : evenWeight N) : Fin N → ZMod 2) ((θ h)⁻¹ i))
    (hsub : ∀ x : ↥L, (x : MulAut (IntMod V hV)) ∈ autI hV K → θ x ∈ alternatingGroup (Fin N))
    (hcov : ∀ g ∈ alternatingGroup (Fin N), ∃ x : ↥L, (x : MulAut (IntMod V hV)) ∈ autI hV K ∧ θ x = g) :
    IsAltType K N := by
  have hF : GN.CoversAlt θ (autI hV K) := by
    intro g hg
    obtain ⟨x, hx, hθx⟩ := hcov g hg
    exact ⟨x, hx, hθx⟩
  have hcommL : ∀ u : ↥(blockU K), iotaU hV hUV u ∈ commV L := fun u =>
    commV_le_of_le hKL (iotaU_mem_commV hV hKN hshort hUV u)
  let ι : ↥(blockU K) →* ↥(commV L) := (iotaU hV hUV).codRestrict (commV L) hcommL
  have hU : (iotaU hV hUV).range ≤ commV L := by
    rintro _ ⟨u, rfl⟩
    exact hcommL u
  have hinv : ∀ h ∈ autI hV K, ∀ x ∈ (iotaU hV hUV).range, h x ∈ (iotaU hV hUV).range := by
    intro h hh x hx
    obtain ⟨⟨k, hkN⟩, hk, rfl⟩ := (mem_autI hV).1 hh
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.1 hx
    have hmem : k * (u : G) * k⁻¹ ∈ blockU K :=
      (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU K hk) (u : G)).mp u.2
    refine MonoidHom.mem_range.2 ⟨⟨k * (u : G) * k⁻¹, hmem⟩, IntMod.val_injective ?_⟩
    simp only [iotaU_val, convI_apply_val]
  have hne₀ : (iotaU hV hUV).range ≠ ⊥ := by
    have hUne : blockU K ≠ ⊥ := by
      intro h
      have hZU : blockZ K < blockU K := hshort.2.2.2.2.1
      rw [h] at hZU
      exact not_lt_bot hZU
    obtain ⟨u, hu⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hUne
    intro hbot
    have hmem : iotaU hV hUV u ∈ (iotaU hV hUV).range := MonoidHom.mem_range.2 ⟨u, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    apply hu
    apply iotaU_injective hV hUV
    rw [hmem, map_one]
  have hUeq : (iotaU hV hUV).range = commV L :=
    (GN.irred_commV θ β hβ h5 hodd hF hU hinv).resolve_left hne₀
  let α₀ : K →* Equiv.Perm (Fin N) :=
    θ.toMonoidHom.comp ((Subgroup.inclusion hKL).comp (toAutI hV K hKN))
  have hα₀ : ∀ k : K, α₀ k ∈ alternatingGroup (Fin N) := fun k =>
    hsub (Subgroup.inclusion hKL (toAutI hV K hKN k)) (toAutI hV K hKN k).2
  let α : K →* alternatingGroup (Fin N) := α₀.codRestrict (alternatingGroup (Fin N)) hα₀
  have hαsurj : Function.Surjective α := by
    intro g
    obtain ⟨x, hx, hθx⟩ := hcov (g : Equiv.Perm (Fin N)) g.2
    obtain ⟨k, hk⟩ := toAutI_surjective hV K hKN ⟨(x : MulAut (IntMod V hV)), hx⟩
    refine ⟨k, Subtype.ext ?_⟩
    show θ (Subgroup.inclusion hKL (toAutI hV K hKN k)) = (g : Equiv.Perm (Fin N))
    rw [hk]
    exact hθx
  have hαker : α.ker = CFSG.pCore 2 ↥K := by
    ext k
    rw [← hker, MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : θ (Subgroup.inclusion hKL (toAutI hV K hKN k)) = 1 := congrArg Subtype.val h
      have h2 : Subgroup.inclusion hKL (toAutI hV K hKN k) = 1 :=
        θ.injective (h1.trans (map_one θ).symm)
      have h3 := congrArg Subtype.val h2
      exact Subtype.ext h3
    · intro h
      have h0 := congrArg Subtype.val h
      have h1 : Subgroup.inclusion hKL (toAutI hV K hKN k) = 1 := Subtype.ext h0
      apply Subtype.ext
      show θ (Subgroup.inclusion hKL (toAutI hV K hKN k)) = 1
      rw [h1, map_one]
  have hβsurj : Function.Surjective (β.toMonoidHom.comp ι) := by
    intro y
    have hc : ((β.symm y : ↥(commV L)) : IntMod V hV) ∈ (iotaU hV hUV).range := by
      rw [hUeq]
      exact (β.symm y).2
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.1 hc
    refine ⟨u, ?_⟩
    have hιu : ι u = β.symm y := Subtype.ext hu
    show β (ι u) = y
    rw [hιu, MulEquiv.apply_symm_apply]
  have hβker : (β.toMonoidHom.comp ι).ker = (blockZ K).subgroupOf (blockU K) := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 : β (ι u) = 1 := h
      have h2 : ι u = 1 := by
        apply β.injective
        rw [h1, map_one]
      have h3 : iotaU hV hUV u = 1 := congrArg Subtype.val h2
      have h4 : u = 1 := iotaU_injective hV hUV (h3.trans (map_one (iotaU hV hUV)).symm)
      rw [h4, Subgroup.coe_one]
      exact (blockZ K).one_mem
    · intro h
      have h' : (u : G) ∈ blockU K ⊓ Subgroup.centralizer (K : Set G) := h
      have hzc : (u : G) ∈ Subgroup.centralizer (K : Set G) := (Subgroup.mem_inf.mp h').2
      have hcomm : ∀ k ∈ K, k * (u : G) = (u : G) * k := fun k hk =>
        Subgroup.mem_centralizer_iff.mp hzc k hk
      have hfix : ∀ g ∈ autI hV K, g (iotaU hV hUV u) = iotaU hV hUV u := by
        intro g hg
        obtain ⟨⟨k, hkN⟩, hk, rfl⟩ := (mem_autI hV).1 hg
        apply IntMod.val_injective
        rw [convI_apply_val, iotaU_val]
        show k * (u : G) * k⁻¹ = (u : G)
        rw [hcomm k hk, mul_inv_cancel_right]
      have h1 : iotaU hV hUV u = 1 := GN.fix_commV θ β hβ h5 hodd hF (hcommL u) hfix
      have h2 : u = 1 := iotaU_injective hV hUV (h1.trans (map_one (iotaU hV hUV)).symm)
      rw [h2, map_one]
  have hequiv : ∀ ℓ : ↥K, ∀ u v : ↥(blockU K), (v : G) = ℓ * u * ℓ⁻¹ → ∀ i : Fin N,
      ((Multiplicative.toAdd ((β.toMonoidHom.comp ι) v) : evenWeight N) : Fin N → ZMod 2) i =
        ((Multiplicative.toAdd ((β.toMonoidHom.comp ι) u) : evenWeight N) : Fin N → ZMod 2)
          ((α ℓ : Equiv.Perm (Fin N))⁻¹ i) := by
    intro ℓ u v huv i
    have hcoe : ((Subgroup.inclusion hKL (toAutI hV K hKN ℓ) : ↥L) : MulAut (IntMod V hV)) =
        convI hV ⟨(ℓ : G), hKN ℓ.2⟩ := rfl
    have hu' : ((Subgroup.inclusion hKL (toAutI hV K hKN ℓ) : ↥L) : MulAut (IntMod V hV))
        (iotaU hV hUV u) ∈ commV L :=
      GN.act_mem_commV' (Subgroup.inclusion hKL (toAutI hV K hKN ℓ) : ↥L).2 (hcommL u)
    have hact : ((Subgroup.inclusion hKL (toAutI hV K hKN ℓ) : ↥L) : MulAut (IntMod V hV))
        (iotaU hV hUV u) = iotaU hV hUV v := by
      apply IntMod.val_injective
      rw [hcoe, convI_apply_val, iotaU_val, iotaU_val, huv]
      rfl
    have key := hβ (Subgroup.inclusion hKL (toAutI hV K hKN ℓ)) (ι u) hu' i
    have e : β ⟨((Subgroup.inclusion hKL (toAutI hV K hKN ℓ) : ↥L) : MulAut (IntMod V hV))
        ((ι u : ↥(commV L)) : IntMod V hV), hu'⟩ = β (ι v) :=
      congrArg β (Subtype.ext hact)
    show ((Multiplicative.toAdd (β (ι v)) : evenWeight N) : Fin N → ZMod 2) i =
        ((Multiplicative.toAdd (β (ι u)) : evenWeight N) : Fin N → ZMod 2)
          ((θ (Subgroup.inclusion hKL (toAutI hV K hKN ℓ)))⁻¹ i)
    rw [← e]
    exact key
  unfold IsAltType
  exact ⟨α, hαsurj, hαker, β.toMonoidHom.comp ι, hβsurj, hβker, hequiv⟩



theorem isAltType_of_altShapeK {V K : Subgroup G} (hV : IsElemAbelian 2 V)
    (hKN : K ≤ Subgroup.normalizer (V : Set G)) (hshort : IsShort2 K) (hUV : blockU K ≤ V)
    (hVK : ⁅V, K⁆ ≤ blockU K) (hker : (toAutI hV K hKN).ker = CFSG.pCore 2 ↥K)
    {M A : Subgroup (MulAut (IntMod V hV))} {k : ℕ} (hk : 2 ≤ k)
    (hcomm : commV (autI hV K ⊔ A) = commV (autI hV K))
    (hshape : B69.AltShapeK k M A (autI hV K) (commV (autI hV K))) :
    IsAltType K (2 * k + 1) := by
  obtain ⟨π, hsurj, hreal, hLeq, -, -⟩ := hshape
  have hn : Odd (2 * k + 1) := odd_two_mul_add_one k
  have h5 : 5 ≤ 2 * k + 1 := by omega
  have hreal' : (FFModel.symDn (2 * k + 1)).RealizesVia (autI hV K ⊔ A)
      (commV (autI hV K ⊔ A)) ⊥ π := by
    rw [hcomm]
    exact hreal
  obtain ⟨e', he'⟩ := B69.exists_core_equiv hn hreal'
  have hinj : Function.Injective π :=
    FFModel.RealizesVia.injective_of_faithful_on (G64.symDn_faithful h5) hreal'
  let θ : ↥(autI hV K ⊔ A) ≃* Equiv.Perm (Fin (2 * k + 1)) :=
    (MulEquiv.ofBijective π ⟨hinj, hsurj⟩).symm
  have hθπ : ∀ σ, θ (π σ) = σ := fun σ => (MulEquiv.ofBijective π ⟨hinj, hsurj⟩).symm_apply_apply σ
  have hequiv : ∀ (x : ↥(autI hV K ⊔ A)) (p : ↥(commV (autI hV K ⊔ A)))
      (hp : (x : MulAut (IntMod V hV)) (p : IntMod V hV) ∈ commV (autI hV K ⊔ A)),
      e' ⟨(x : MulAut (IntMod V hV)) p, hp⟩ = G6.coreAct (2 * k + 1) (θ x) (e' p) := by
    intro x p hp
    obtain ⟨σ, rfl⟩ := hsurj x
    rw [hθπ]
    exact he' σ p hp
  have hβ := symCoreWith_of_coreAct θ e' hequiv
  refine isAltType_of_symCore (L := autI hV K ⊔ A) hV h5 hn hKN hshort hUV hVK hker le_sup_left θ
    (e'.trans (coreModEquivEven (2 * k + 1))) hβ ?_ ?_
  · intro x hx
    have hx' : (x : MulAut (IntMod V hV)) ∈
        (alternatingGroup (Fin (2 * k + 1))).map ((autI hV K ⊔ A).subtype.comp π) := by
      rw [← hLeq]
      exact hx
    obtain ⟨g, hg, hgx⟩ := Subgroup.mem_map.1 hx'
    have hgx' : π g = x := Subtype.ext hgx
    rw [← hgx', hθπ]
    exact hg
  · intro g hg
    refine ⟨π g, ?_, hθπ g⟩
    exact hLeq.ge (Subgroup.mem_map.2 ⟨g, hg, rfl⟩)

end C127Block

end L246C127

end CFSG.QuasithinUnique
