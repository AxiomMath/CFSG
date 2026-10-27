module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Quot
public import CFSG.Quasithin.Background.E2Three
import CFSG.Quasithin.Background.C126A5PermBasic
import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement

namespace L246C127

namespace MAut

variable {G : Type} [Group G] [Finite G]

section Aut

variable {V K : Subgroup G} (hV : IsElemAbelian 2 V)

@[expose] def valHom : IntMod V hV →* G where
  toFun := IntMod.val
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] noncomputable def iotaU (hUV : blockU K ≤ V) : ↥(blockU K) →* IntMod V hV where
  toFun u := IntMod.mk hV ⟨u, hUV u.2⟩
  map_one' := IntMod.val_injective rfl
  map_mul' _ _ := IntMod.val_injective rfl

theorem iotaU_val (hUV : blockU K ≤ V) (u : ↥(blockU K)) : (iotaU hV hUV u).val = (u : G) := rfl

theorem iotaU_injective (hUV : blockU K ≤ V) : Function.Injective (iotaU hV hUV) := by
  intro a b h
  exact Subtype.ext (by simpa [iotaU_val] using congrArg IntMod.val h)

theorem iotaU_mem_commV (hKN : K ≤ Subgroup.normalizer (V : Set G)) (hshort : IsShort2 K)
    (hUV : blockU K ≤ V) (u : ↥(blockU K)) : iotaU hV hUV u ∈ commV (autI hV K) := by
  have hmem : (u : G) ∈ ⁅blockU K, K⁆ := by rw [C1.commutator_blockU hshort]; exact u.2
  have hle : ⁅blockU K, K⁆ ≤ (commV (autI hV K)).map (valHom hV) := by
    rw [Subgroup.commutator_le]
    intro a ha k hk
    have haV := hUV ha
    set a' : IntMod V hV := IntMod.mk hV ⟨a, haV⟩ with ha'
    set x : MulAut (IntMod V hV) := convI hV ⟨k, hKN hk⟩ with hxdef
    have hx : x ∈ autI hV K := convI_mem_autI hV hk (hKN hk)
    have hgen : x a' * a'⁻¹ ∈ commV (autI hV K) := Subgroup.subset_closure ⟨x, hx, a', rfl⟩
    refine ⟨(x a' * a'⁻¹)⁻¹, (commV (autI hV K)).inv_mem hgen, ?_⟩
    show ((x a' * a'⁻¹)⁻¹).val = ⁅a, k⁆
    have e : (x a').val = k * a * k⁻¹ := convI_apply_val hV ⟨k, hKN hk⟩ a'
    rw [IntMod.val_inv, IntMod.val_mul, IntMod.val_inv, e]
    show _ = a * k * a⁻¹ * k⁻¹
    have : a'.val = a := rfl
    rw [this]
    group
  obtain ⟨c, hc, hcu⟩ := hle hmem
  have : c = iotaU hV hUV u := IntMod.val_injective hcu
  rwa [← this]

theorem commV_le_range (hKN : K ≤ Subgroup.normalizer (V : Set G)) (hVK : ⁅V, K⁆ ≤ blockU K)
    (hUV : blockU K ≤ V) :
    ∀ c ∈ commV (autI hV K), ∃ u : ↥(blockU K), iotaU hV hUV u = c := by
  have hle : (commV (autI hV K)).map (valHom hV) ≤ blockU K := by
    rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).2 ?_
    rintro w ⟨x, hx, v, rfl⟩
    obtain ⟨⟨k, hkN⟩, hk, rfl⟩ := (mem_autI hV).1 hx
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    show (convI hV ⟨k, hkN⟩ v * v⁻¹).val ∈ blockU K
    rw [IntMod.val_mul, IntMod.val_inv, convI_apply_val]
    have hcomm : k * v.val * k⁻¹ * (v.val)⁻¹ = (⁅v.val, k⁆)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [hcomm]
    exact (blockU K).inv_mem (hVK (Subgroup.commutator_mem_commutator v.val_mem hk))
  intro c hc
  have hcu : c.val ∈ blockU K := hle ⟨c, hc, rfl⟩
  exact ⟨⟨c.val, hcu⟩, IntMod.val_injective rfl⟩

end Aut

theorem ker_toAutI_eq_pCore {V K : Subgroup G} (hV : IsElemAbelian 2 V) (hshort : IsShort2 K)
    (hKN : K ≤ Subgroup.normalizer (V : Set G)) (hUV : blockU K ≤ V)
    (hQ : blockQ K ≤ Subgroup.centralizer (V : Set G)) :
    (toAutI hV K hKN).ker = CFSG.pCore 2 ↥K := by
  rw [toAutI_ker]
  ext k
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · rintro ⟨-, hc⟩
    exact (L246.mem_blockQ_iff k).1
      (C1.inf_centralizer_blockU_le hshort ⟨k.2, Subgroup.centralizer_le hUV hc⟩)
  · intro h
    exact ⟨k.2, hQ ((L246.mem_blockQ_iff k).2 h)⟩

theorem isQuasisimple_autI_of_ker {V K : Subgroup G} (hV : IsElemAbelian 2 V)
    (hKN : K ≤ Subgroup.normalizer (V : Set G))
    (hker : (toAutI hV K hKN).ker = CFSG.pCore 2 ↥K)
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) : CFSG.IsQuasisimple ↥(autI hV K) := by
  let e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* ↥(autI hV K) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (toAutI_surjective hV K hKN))
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq

theorem isLin2Type_of_natural {V K : Subgroup G} (hV : IsElemAbelian 2 V)
    (hKN : K ≤ Subgroup.normalizer (V : Set G)) (hshort : IsShort2 K) (hUV : blockU K ≤ V)
    (hVK : ⁅V, K⁆ ≤ blockU K)
    (hker : (toAutI hV K hKN).ker = CFSG.pCore 2 ↥K)
    {C : Subgroup (IntMod V hV)}
    (hC : ∀ u : ↥(blockU K), iotaU hV hUV u ∈ C ↔ (u : G) ∈ blockZ K)
    {n : ℕ} (hnat : E2.IsL2Natural (autI hV K) C n) : IsLin2Type K n := by
  obtain ⟨_, F, iF, iFin, hF, e, β, hβs, hβk, hβe⟩ := hnat
  let ι : ↥(blockU K) →* ↥(commV (autI hV K)) :=
    (iotaU hV hUV).codRestrict (commV (autI hV K)) (iotaU_mem_commV hV hKN hshort hUV)
  have hιsurj : Function.Surjective ι := by
    intro y
    obtain ⟨u, hu⟩ := commV_le_range hV hKN hVK hUV y.1 y.2
    exact ⟨u, Subtype.ext hu⟩
  have hk : ∀ y : ↥(commV (autI hV K)), β y = 1 ↔ (y : IntMod V hV) ∈ C := by
    intro y
    rw [← MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨y.2, h⟩⟩
  unfold IsLin2Type
  refine ⟨F, iF, iFin, hF, e.toMonoidHom.comp (toAutI hV K hKN), ?_, ?_, β.comp ι, ?_, ?_, ?_⟩
  ·
    intro y
    obtain ⟨x, hx⟩ := e.surjective y
    obtain ⟨k, hk'⟩ := toAutI_surjective hV K hKN x
    refine ⟨k, ?_⟩
    show e (toAutI hV K hKN k) = y
    rw [hk', hx]
  ·
    rw [← hker]
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    show e (toAutI hV K hKN k) = 1 ↔ toAutI hV K hKN k = 1
    exact MulEquiv.map_eq_one_iff e
  ·
    exact hβs.comp hιsurj
  ·
    ext u
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf]
    exact (hk (ι u)).trans (hC u)
  ·
    intro ℓ u v hvℓ
    have hEq : ((toAutI hV K hKN ℓ : ↥(autI hV K)) : MulAut (IntMod V hV)) (iotaU hV hUV u)
        = iotaU hV hUV v := by
      apply IntMod.val_injective
      show ((convI hV ⟨(ℓ : G), hKN ℓ.2⟩) (iotaU hV hUV u)).val = (v : G)
      rw [convI_apply_val, iotaU_val]
      exact hvℓ.symm
    have hu' : ((toAutI hV K hKN ℓ : ↥(autI hV K)) : MulAut (IntMod V hV))
        ((ι u : ↥(commV (autI hV K))) : IntMod V hV) ∈ commV (autI hV K) := by
      show ((toAutI hV K hKN ℓ : ↥(autI hV K)) : MulAut (IntMod V hV)) (iotaU hV hUV u)
        ∈ commV (autI hV K)
      rw [hEq]
      exact iotaU_mem_commV hV hKN hshort hUV v
    have hmem : (⟨((toAutI hV K hKN ℓ : ↥(autI hV K)) : MulAut (IntMod V hV))
        ((ι u : ↥(commV (autI hV K))) : IntMod V hV), hu'⟩ : ↥(commV (autI hV K))) = ι v :=
      Subtype.ext hEq
    have hβv : β (ι v) = β ⟨((toAutI hV K hKN ℓ : ↥(autI hV K)) : MulAut (IntMod V hV))
        ((ι u : ↥(commV (autI hV K))) : IntMod V hV), hu'⟩ := congrArg β hmem.symm
    show Multiplicative.toAdd (β (ι v)) =
      (e (toAutI hV K hKN ℓ) : Matrix (Fin 2) (Fin 2) F).mulVec
        (Multiplicative.toAdd (β (ι u)))
    rw [hβv]
    exact hβe (toAutI hV K hKN ℓ) (ι u) hu'

section A5

open CFSG.Quasithin.C126.A5

theorem commV_le_of_le {W : Type} [CommGroup W] {A B : Subgroup (MulAut W)} (h : A ≤ B) :
    commV A ≤ commV B :=
  Subgroup.closure_mono fun _ ⟨x, hx, v, hxv⟩ => ⟨x, h hx, v, hxv⟩

end A5

end MAut

end L246C127

end CFSG.QuasithinUnique
