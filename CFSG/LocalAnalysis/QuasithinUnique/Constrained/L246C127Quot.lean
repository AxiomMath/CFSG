module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Lift
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Quasi
public import CFSG.Quasithin.Background.B2FactorizationSolvable

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement

namespace L246C127

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_autI_eq_bot {X V : Subgroup G} (hV : IsElemAbelian 2 V) (hred : IsTwoReducedIn X V) :
    pCoreOf 2 (autI hV X) = ⊥ := by
  have hMN : X ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hPX : pCoreOf 2 (autI hV X) ≤ autI hV X := pCoreOf_le 2 _
  have hP2 : IsPGroup 2 (pCoreOf 2 (autI hV X)) := pCoreOf_isPGroup 2 _
  have hXn : autI hV X ≤ Subgroup.normalizer
      ((pCoreOf 2 (autI hV X) : Subgroup (MulAut (IntMod V hV))) :
        Set (MulAut (IntMod V hV))) := le_normalizer_pCoreOf 2 _
  have hDM : preI hV X hMN (pCoreOf 2 (autI hV X)) ≤ X := preI_le hV
  have key : ∀ m ∈ X, ∀ d ∈ preI hV X hMN (pCoreOf 2 (autI hV X)),
      m * d * m⁻¹ ∈ preI hV X hMN (pCoreOf 2 (autI hV X)) := by
    intro m hm d hd
    obtain ⟨hdM, hdP⟩ := (mem_preI hV).1 hd
    have hmem : m * d * m⁻¹ ∈ X := X.mul_mem (X.mul_mem hm hdM) (X.inv_mem hm)
    refine (mem_preI hV).2 ⟨hmem, ?_⟩
    have e : (⟨m * d * m⁻¹, hmem⟩ : ↥X) = ⟨m, hm⟩ * ⟨d, hdM⟩ * ⟨m, hm⟩⁻¹ := rfl
    have hmX : convHom hV X hMN ⟨m, hm⟩ ∈ autI hV X := by
      rw [convHom_apply]
      exact convI_mem_autI hV hm (hMN hm)
    rw [e, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hXn hmX) _).mp hdP
  have hDn : X ≤ Subgroup.normalizer
      ((preI hV X hMN (pCoreOf 2 (autI hV X)) : Subgroup G) : Set G) := fun m hm =>
    B6.mem_normalizer_of_forall_mem (key m hm)
      (fun x hx => by simpa using key m⁻¹ (X.inv_mem hm) x hx)
  have hD2 : ∀ d ∈ preI hV X hMN (pCoreOf 2 (autI hV X)),
      ∃ k : ℕ, d ^ (2 ^ k) ∈ Subgroup.centralizer (V : Set G) := by
    intro d hd
    obtain ⟨hdM, hdP⟩ := (mem_preI hV).1 hd
    obtain ⟨k, hk⟩ := hP2 ⟨convHom hV X hMN ⟨d, hdM⟩, hdP⟩
    refine ⟨k, ?_⟩
    have h2 : (⟨d, hdM⟩ : ↥X) ^ 2 ^ k ∈ (convHom hV X hMN).ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact congrArg Subtype.val hk
    rw [ker_convHom hV X hMN, Subgroup.mem_subgroupOf] at h2
    simpa using h2.2
  have hDC := hred.2.2.2 _ hDM hDn hD2
  refine eq_bot_iff.mpr fun φ hφ => ?_
  obtain ⟨g, hgM, rfl⟩ := (mem_autI hV).1 (hPX hφ)
  have hgD : (g : G) ∈ preI hV X hMN (pCoreOf 2 (autI hV X)) :=
    (mem_preI hV).2 ⟨hgM, by rw [convHom_apply]; exact hφ⟩
  exact Subgroup.mem_bot.mpr ((convI_eq_one_iff hV g).2 (hDC hgD))

section Hom

variable {V : Subgroup G} (hV : IsElemAbelian 2 V)

@[expose] noncomputable def toAutI (K : Subgroup G) (hK : K ≤ Subgroup.normalizer (V : Set G)) :
    ↥K →* ↥(autI hV K) :=
  (MulEquiv.subgroupCongr (range_convHom hV K hK)).toMonoidHom.comp (convHom hV K hK).rangeRestrict

omit [Finite G] in
theorem toAutI_surjective (K : Subgroup G) (hK : K ≤ Subgroup.normalizer (V : Set G)) :
    Function.Surjective (toAutI hV K hK) := by
  intro y
  obtain ⟨x, hx⟩ := (convHom hV K hK).rangeRestrict_surjective
    ((MulEquiv.subgroupCongr (range_convHom hV K hK)).symm y)
  exact ⟨x, by simp [toAutI, hx]⟩

omit [Finite G] in
theorem toAutI_coe (K : Subgroup G) (hK : K ≤ Subgroup.normalizer (V : Set G)) (k : ↥K) :
    ((toAutI hV K hK k : ↥(autI hV K)) : MulAut (IntMod V hV)) = convHom hV K hK k := rfl

omit [Finite G] in
theorem toAutI_ker (K : Subgroup G) (hK : K ≤ Subgroup.normalizer (V : Set G)) :
    (toAutI hV K hK).ker = (K ⊓ Subgroup.centralizer (V : Set G)).subgroupOf K := by
  rw [← ker_convHom hV K hK]
  ext k
  simp only [MonoidHom.mem_ker]
  constructor
  · intro h
    have h' := congrArg Subtype.val h
    rw [toAutI_coe, Subgroup.coe_one] at h'
    exact h'
  · intro h
    apply Subtype.ext
    rw [toAutI_coe, Subgroup.coe_one]
    exact h

end Hom


omit [Finite G] in
theorem autI_commutator {V : Subgroup G} (hV : IsElemAbelian 2 V) {X A B : Subgroup G}
    (hXV : X ≤ Subgroup.normalizer (V : Set G)) (hA : A ≤ X) (hB : B ≤ X) :
    autI hV ⁅A, B⁆ = ⁅autI hV A, autI hV B⁆ := by
  have hAB : ⁅A, B⁆ ≤ X := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact X.mul_mem (X.mul_mem (X.mul_mem (hA ha) (hB hb)) (X.inv_mem (hA ha))) (X.inv_mem (hB hb))
  rw [autI_eq_map_convHom hV hXV hAB, autI_eq_map_convHom hV hXV hA,
    autI_eq_map_convHom hV hXV hB, ← Subgroup.map_commutator]
  congr 1
  apply Subgroup.map_injective X.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hAB,
    Subgroup.map_subgroupOf_eq_of_le hA, Subgroup.map_subgroupOf_eq_of_le hB]

namespace Setting

variable {X T P K : Subgroup G} (S : Setting X T P K)

include S

theorem hKN : K ≤ Subgroup.normalizer (VZ T X : Set G) := S.KP.trans (S.PX.trans S.hXV)

theorem hTN : T ≤ Subgroup.normalizer (VZ T X : Set G) := S.TP.trans (S.PX.trans S.hXV)

theorem ker_toAutI_le_pCore (hV : IsElemAbelian 2 (VZ T X)) (hUV : blockU K ≤ VZ T X) :
    (toAutI hV K S.hKN).ker ≤ CFSG.pCore 2 ↥K := by
  rw [toAutI_ker]
  intro k hk
  rw [Subgroup.mem_subgroupOf] at hk
  have : (k : G) ∈ blockQ K :=
    C1.inf_centralizer_blockU_le S.short ⟨k.2, Subgroup.centralizer_le hUV hk.2⟩
  exact (L246.mem_blockQ_iff k).1 this

theorem map_pCore_le_center (hV : IsElemAbelian 2 (VZ T X)) (hUV : blockU K ≤ VZ T X) :
    (CFSG.pCore 2 ↥K).map (toAutI hV K S.hKN) ≤ Subgroup.center ↥(autI hV K) := by
  have hsurj := toAutI_surjective hV K S.hKN
  rintro _ ⟨r, hr, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro a
  obtain ⟨k, rfl⟩ := hsurj a
  have hr' : (r : G) ∈ blockQ K := (L246.mem_blockQ_iff r).2 hr
  have hcomm : (⁅(r : G), (k : G)⁆ : G) ∈ blockU K := Subgroup.commutator_mem_commutator hr' k.2
  have hc1 : ⁅r, k⁆ ∈ (toAutI hV K S.hKN).ker := by
    rw [toAutI_ker, Subgroup.mem_subgroupOf]
    refine ⟨(⁅r, k⁆ : ↥K).2, B2F.le_centralizer_self hV (hUV ?_)⟩
    have e : (((⁅r, k⁆ : ↥K)) : G) = ⁅(r : G), (k : G)⁆ := by simp [commutatorElement_def]
    rw [e]
    exact hcomm
  have hc2 : toAutI hV K S.hKN ⁅r, k⁆ = 1 := hc1
  have : ⁅toAutI hV K S.hKN r, toAutI hV K S.hKN k⁆ = 1 := by
    rw [← map_commutatorElement]; exact hc2
  exact (commutatorElement_eq_one_iff_mul_comm.1 this).symm

theorem isQuasisimple_or_card_three_autI (hV : IsElemAbelian 2 (VZ T X)) (hUV : blockU K ≤ VZ T X) :
    CFSG.IsQuasisimple ↥(autI hV K) ∨ Nat.card ↥(autI hV K) = 3 := by
  set π := toAutI hV K S.hKN with hπ
  have hsurj : Function.Surjective π := toAutI_surjective hV K S.hKN
  have hker : π.ker ≤ CFSG.pCore 2 ↥K := S.ker_toAutI_le_pCore hV hUV
  have hRn : (CFSG.pCore 2 ↥K).Normal := CFSG.pCore_normal
  let Z : Subgroup ↥(autI hV K) := (CFSG.pCore 2 ↥K).map π
  have hZn : Z.Normal := Subgroup.Normal.map hRn π hsurj
  refine isQuasisimple_or_card_three_of_central_two (Z := Z) ?_ ?_ ?_ ?_
  ·
    intro N hNn hN
    have hcn : (N.comap π).Normal := Subgroup.Normal.comap hNn π
    have hq : IsPGroup 2 (↥K ⧸ N.comap π) := by
      refine hN.of_injective (QuotientGroup.map (N.comap π) N π le_rfl) ?_
      rw [injective_iff_map_eq_one]
      intro q hq1
      induction q using QuotientGroup.induction_on with
      | H x =>
        rw [QuotientGroup.map_mk, QuotientGroup.eq_one_iff] at hq1
        exact (QuotientGroup.eq_one_iff x).2 hq1
    have htop := S.short.1 (N.comap π) hq
    refine eq_top_iff.2 fun a _ => ?_
    obtain ⟨k, rfl⟩ := hsurj a
    have : k ∈ N.comap π := htop ▸ Subgroup.mem_top k
    exact this
  ·
    exact S.map_pCore_le_center hV hUV
  · exact (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).map π
  ·
    let ψ : ↥K →* ↥(autI hV K) ⧸ Z := (QuotientGroup.mk' Z).comp π
    have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective Z).comp hsurj
    have hψker : ψ.ker = CFSG.pCore 2 ↥K := by
      have h1 : ψ.ker = Z.comap π := by
        ext k
        simp [ψ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
      rw [h1]
      show ((CFSG.pCore 2 ↥K).map π).comap π = _
      rw [Subgroup.comap_map_eq, sup_eq_left.2 hker]
    let e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* ↥(autI hV K) ⧸ Z :=
      (QuotientGroup.quotientMulEquivOfEq hψker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
    exact S.short.2.2.2.1.imp (fun h => CFSG.LocalCores.isQuasisimple_of_mulEquiv e h)
      (fun h => by rw [← Nat.card_congr e.toEquiv]; exact h)

theorem isSubnormal_autI_sup (hV : IsElemAbelian 2 (VZ T X)) :
    IsSubnormal (autI hV K) (autI hV K ⊔ autI hV T) := by
  have hKT : K ⊔ T ≤ Subgroup.normalizer (VZ T X : Set G) := sup_le S.hKN S.hTN
  have h1 : IsSubnormal K (K ⊔ T) :=
    A3.subnormal_of_le_of_le S.subnormal le_sup_left (sup_le S.KP S.TP)
  have h2 : IsSubnormal (K.subgroupOf (K ⊔ T)) ⊤ := by
    have := A3.subnormal_comap (K ⊔ T).subtype h1
    have e : (K ⊔ T).comap (K ⊔ T).subtype = ⊤ := by ext x; simp
    rwa [e] at this
  have h3 := A3.subnormal_map (convHom hV (K ⊔ T) hKT) h2
  rw [← autI_eq_map_convHom hV hKT le_sup_left, Subgroup.map_top, range_convHom hV (K ⊔ T) hKT,
    autI_sup hV S.hKN S.hTN] at h3
  exact h3

theorem ffJP_offenderImages_eq (hV : IsElemAbelian 2 (VZ T X)) :
    ffJP (offenderImages hV X) (autI hV T) = autI hV (thompsonJ T) := by
  apply le_antisymm
  · refine iSup_le fun B => iSup_le fun hB => iSup_le fun hBT => ?_
    exact B2F.offenderImages_le_autI_thompsonJ hV S.hXV S.sylow hB hBT
  · rw [autI_thompsonJ hV S.hTN]
    refine iSup_le fun B => iSup_le fun hB => iSup_le fun hBT => ?_
    refine le_iSup₂_of_le B ?_ (le_iSup_of_le hBT le_rfl)
    obtain ⟨A, hA, rfl⟩ := hB
    exact ⟨A, ⟨isMaxElemAbelian_of_isSylowTwoOf S.sylow hA.1, hA.2⟩, rfl⟩

theorem commutator_ffJP_eq (hV : IsElemAbelian 2 (VZ T X)) (hKJ : ⁅K, thompsonJ T⁆ = K) :
    ⁅autI hV K, ffJP (offenderImages hV X) (autI hV T)⁆ = autI hV K := by
  have hJX : thompsonJ T ≤ X := (thompsonJ_le_self T).trans S.sylow.1
  have hKX : K ≤ X := S.KP.trans S.PX
  rw [ffJP_offenderImages_eq S hV, ← autI_commutator hV S.hXV hKX hJX, hKJ]

theorem not_thompsonJ_le_centralizer (hKJ : ⁅K, thompsonJ T⁆ = K) (hne : ⁅VZ T X, K⁆ ≠ ⊥) :
    ¬ thompsonJ T ≤ Subgroup.centralizer (VZ T X : Set G) := by
  intro hJC
  apply hne
  have hVJ : ⁅thompsonJ T, VZ T X⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hJC
  have h1 : ⁅⁅thompsonJ T, VZ T X⁆, K⁆ = ⊥ := by rw [hVJ]; exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 bot_le
  have hVK : ⁅VZ T X, K⁆ ≤ VZ T X :=
    CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing (VZ T X) K S.hKN
  have h2 : ⁅⁅VZ T X, K⁆, thompsonJ T⁆ = ⊥ := by
    refine le_bot_iff.1 ?_
    calc ⁅⁅VZ T X, K⁆, thompsonJ T⁆ ≤ ⁅VZ T X, thompsonJ T⁆ := Subgroup.commutator_mono hVK le_rfl
      _ = ⊥ := by rw [Subgroup.commutator_comm]; exact hVJ
      _ ≤ ⊥ := le_rfl
  have h3 : ⁅⁅K, thompsonJ T⁆, VZ T X⁆ = ⊥ := three_subgroup_lemma h1 h2
  rw [hKJ] at h3
  rw [Subgroup.commutator_comm]
  exact h3

theorem isStableFF_offenderImages (hV : IsElemAbelian 2 (VZ T X)) (hKJ : ⁅K, thompsonJ T⁆ = K)
    (hne : ⁅VZ T X, K⁆ ≠ ⊥) : IsStableFF (autI hV X) (offenderImages hV X) := by
  have hJ : ¬ thompsonJ X ≤ Subgroup.centralizer (VZ T X : Set G) := fun h =>
    S.not_thompsonJ_le_centralizer hKJ hne ((thompsonJ_le_thompsonJ_of_isSylowTwoOf S.sylow).trans h)
  exact B2_5 hV (le_pCoreOf_of_isTwoReducedIn S.hred |>.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 X))
    S.hXV ((offenderImages_nonempty_iff_not_le hV).2 hJ)

end Setting

end L246C127

end CFSG.QuasithinUnique
