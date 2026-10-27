module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelBlockData
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelDecomp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourSylow
public import CFSG.LocalAnalysis.QuasithinUnique.EscapingComponents

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Setup.Layer
open scoped Multiplicative commutatorElement

section Hom

variable {G : Type} [Group G] {V : Subgroup G} [V.Normal]

@[expose] noncomputable def rhoBlock (B : Subgroup G) (A : Subgroup (MulAut V))
    (h : ∀ b ∈ B, MulAut.conjNormal (H := V) b ∈ A) : ↥B →* ↥A :=
  ((MulAut.conjNormal (H := V)).comp B.subtype).codRestrict A fun b => h b b.2

theorem rhoBlock_surjective (B : Subgroup G) (A : Subgroup (MulAut V))
    (h : ∀ b ∈ B, MulAut.conjNormal (H := V) b ∈ A)
    (hs : ∀ x ∈ A, ∃ b ∈ B, MulAut.conjNormal (H := V) b = x) :
    Function.Surjective (rhoBlock B A h) := by
  intro x
  obtain ⟨b, hb, hbx⟩ := hs x.1 x.2
  exact ⟨⟨b, hb⟩, Subtype.ext hbx⟩

theorem rhoBlock_ker [Finite G] (B LS : Subgroup G) (A : Subgroup (MulAut V))
    (h : ∀ b ∈ B, MulAut.conjNormal (H := V) b ∈ A) (hBLS : B ≤ LS)
    (hker : LS ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 LS)
    (hcore : pCoreOf 2 B = B ⊓ pCoreOf 2 LS) :
    (rhoBlock B A h).ker = CFSG.pCore 2 ↥B := by
  ext b
  rw [MonoidHom.mem_ker]
  have h1 : rhoBlock B A h b = 1 ↔ MulAut.conjNormal (H := V) (b : G) = 1 := by
    constructor
    · intro hb
      exact congrArg Subtype.val hb
    · intro hb
      exact Subtype.ext hb
  have h2 : b ∈ CFSG.pCore 2 ↥B ↔ (b : G) ∈ pCoreOf 2 B := by
    unfold pCoreOf
    exact (Subgroup.mem_map_iff_mem B.subtype_injective).symm
  rw [h1, conjNormal_eq_one_iff, h2, hcore]
  constructor
  · intro hC
    refine ⟨b.2, ?_⟩
    rw [← hker]
    exact ⟨hBLS b.2, hC⟩
  · rintro ⟨-, hQ⟩
    rw [← hker] at hQ
    exact hQ.2

end Hom

section Main

theorem delBlockTypeProp
    : DelBlockTypeProp := by
  intro G _ _ R M V n F _ r Lc ctx hcore hall hImage hCore
  have hS := ctx.setting
  have hX := ctx.hX
  have hVn : V.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hX)
  have hbridge := even_SL2_original_bridge hS ctx.comps
  have hfam := del_family_data hS ctx.comps ctx.deleted
  have hr : 0 < r := hbridge.r_pos
  obtain ⟨Fs0, P0, hP0⟩ := hall ⟨0, hr⟩
  set L := oddOrderSubgroup (⊤ : Subgroup G) with hL
  set LS := L ⊔ baum R with hLS
  have hLSn : LS.Normal := hcore.normal
  have hker : LS ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 LS := hP0.ker.kernel.2
  have hVe : IsElemAbelian 2 V := hS.reduced.2.2.1
  have hBLS : ∀ j, blockOf (⊤ : Subgroup G) R V hX (Lc j) ≤ LS := fun j =>
    (oddOrderSubgroup_le _).trans inf_le_left
  have hρmem : ∀ j, ∀ b ∈ blockOf (⊤ : Subgroup G) R V hX (Lc j),
      MulAut.conjNormal (H := V) b ∈ Lc j := by
    intro j b hb
    have : MulAut.conjNormal (H := V) b ∈ autOn (blockOf (⊤ : Subgroup G) R V hX (Lc j)) V := by
      rw [autOn_eq_map_conjNormal]
      exact Subgroup.mem_map_of_mem _ hb
    rwa [hImage.image j] at this
  have hlift : ∀ j, ∀ x ∈ Lc j, ∃ b ∈ blockOf (⊤ : Subgroup G) R V hX (Lc j),
      MulAut.conjNormal (H := V) b = x := by
    intro j x hx
    have hx' : x ∈ (blockOf (⊤ : Subgroup G) R V hX (Lc j)).map (MulAut.conjNormal (H := V)) := by
      rw [← autOn_eq_map_conjNormal, hImage.image j]
      exact hx
    obtain ⟨b, hb, hbx⟩ := hx'
    exact ⟨b, hb, hbx⟩
  have hsub : ∀ i, ((blockOf (⊤ : Subgroup G) R V hX (Lc i)).subgroupOf (⊤ : Subgroup G)).IsSubnormal := by
    intro i
    have h1 : (blockOf (⊤ : Subgroup G) R V hX (Lc i)).IsSubnormal :=
      Subgroup.IsSubnormal.trans (hBLS i) (Subgroup.Normal.isSubnormal (hImage.normal_B i))
        (Subgroup.Normal.isSubnormal hLSn)
    exact Subgroup.IsSubnormal.subgroupOf h1
  have hAlt : ∀ i, IsAltType (blockOf (⊤ : Subgroup G) R V hX (Lc i)) 5 := by
    intro i
    obtain ⟨e, β₀, hequi⟩ := hfam.alt i
    have hU : blockU (blockOf (⊤ : Subgroup G) R V hX (Lc i)) = modComm V (Lc i) :=
      (hCore.coreComm i).1
    have hZ : blockZ (blockOf (⊤ : Subgroup G) R V hX (Lc i)) = ⊥ := by
      have h1 : blockZ (blockOf (⊤ : Subgroup G) R V hX (Lc i)) =
          modComm V (Lc i) ⊓ Subgroup.centralizer
            ((blockOf (⊤ : Subgroup G) R V hX (Lc i) : Subgroup G) : Set G) := by
        unfold blockZ
        rw [hU]
      rw [h1]
      exact hCore.fixed i
    have hρBs := rhoBlock_surjective (blockOf (⊤ : Subgroup G) R V hX (Lc i)) (Lc i) (hρmem i)
      (hlift i)
    have hρBk := rhoBlock_ker (blockOf (⊤ : Subgroup G) R V hX (Lc i)) LS (Lc i) (hρmem i)
      (hBLS i) hker (hImage.core i)
    refine ⟨e.toMonoidHom.comp (rhoBlock (blockOf (⊤ : Subgroup G) R V hX (Lc i)) (Lc i) (hρmem i)),
      e.surjective.comp hρBs, ?_,
      β₀.toMonoidHom.comp (MulEquiv.subgroupCongr hU).toMonoidHom,
      β₀.surjective.comp (MulEquiv.subgroupCongr hU).surjective, ?_, ?_⟩
    · rw [← hρBk]
      ext b
      simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      exact map_eq_one_iff _ e.injective
    · rw [hZ, Subgroup.bot_subgroupOf, MonoidHom.ker_eq_bot_iff]
      exact β₀.injective.comp (MulEquiv.subgroupCongr hU).injective
    · intro ℓ u v hv k
      have hu' : (u : G) ∈ modComm V (Lc i) := hU ▸ u.2
      have hv' : (v : G) ∈ modComm V (Lc i) := hU ▸ v.2
      have hmove : ((rhoBlock (blockOf (⊤ : Subgroup G) R V hX (Lc i)) (Lc i) (hρmem i) ℓ :
          ↥(Lc i)) : MulAut V) ⟨u, modComm_le V (Lc i) hu'⟩ = ⟨v, modComm_le V (Lc i) hv'⟩ := by
        apply Subtype.ext
        show (ℓ : G) * u * (ℓ : G)⁻¹ = v
        rw [hv]
        rfl
      exact hequi (rhoBlock (blockOf (⊤ : Subgroup G) R V hX (Lc i)) (Lc i) (hρmem i) ℓ)
        ⟨u, hu'⟩ ⟨v, hv'⟩ (modComm_le V (Lc i) hu') (modComm_le V (Lc i) hv') hmove k
  have hShort : ∀ i, IsShort2 (blockOf (⊤ : Subgroup G) R V hX (Lc i)) := by
    intro i
    have hU : blockU (blockOf (⊤ : Subgroup G) R V hX (Lc i)) = modComm V (Lc i) :=
      (hCore.coreComm i).1
    have hZ : blockZ (blockOf (⊤ : Subgroup G) R V hX (Lc i)) = ⊥ := by
      have h1 : blockZ (blockOf (⊤ : Subgroup G) R V hX (Lc i)) =
          modComm V (Lc i) ⊓ Subgroup.centralizer
            ((blockOf (⊤ : Subgroup G) R V hX (Lc i) : Subgroup G) : Set G) := by
        unfold blockZ
        rw [hU]
      rw [h1]
      exact hCore.fixed i
    have hLSnB : LS ≤ Subgroup.normalizer
        ((blockOf (⊤ : Subgroup G) R V hX (Lc i) : Subgroup G) : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (hBLS i)).1 (hImage.normal_B i)
    refine ⟨hasNoTwoQuotient_oddOrderSubgroup _,
      EscapingComponents.charTwo_of_isSubnormal ctx.charTwo le_top (hsub i), ⟨?_, ?_⟩, ?_, ?_⟩
    ·
      have hIQ : modComm V (Lc i) ≤ pCoreOf 2 (blockOf (⊤ : Subgroup G) R V hX (Lc i)) := by
        rw [← (hCore.coreComm i).1]
        exact commutator_le_of_le_normalizer (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
      have hIC : modComm V (Lc i) ≤ Subgroup.centralizer
          ((pCoreOf 2 (blockOf (⊤ : Subgroup G) R V hX (Lc i)) : Subgroup G) : Set G) := by
        have h1 : modComm V (Lc i) ≤ omegaOneCenterOf (pCoreOf 2 LS) :=
          (le_iSup (fun j => modComm V (Lc j)) i).trans hP0.sum.commutator.2.2
        have h2 : omegaOneCenterOf (pCoreOf 2 LS) ≤
            Subgroup.centralizer ((pCoreOf 2 LS : Subgroup G) : Set G) :=
          (Subgroup.closure_le _).2 fun x hx => hx.1.2
        have h3 : (pCoreOf 2 (blockOf (⊤ : Subgroup G) R V hX (Lc i)) : Set G) ⊆
            (pCoreOf 2 LS : Set G) := by
          rw [hImage.core i]
          exact fun x hx => hx.2
        exact (h1.trans h2).trans (Subgroup.centralizer_le h3)
      rw [hU]
      exact le_inf hIQ hIC
    · intro x hx
      rw [hU] at hx
      exact hVe.2 x (modComm_le V (Lc i) hx)
    · left
      have hρBs := rhoBlock_surjective (blockOf (⊤ : Subgroup G) R V hX (Lc i)) (Lc i) (hρmem i)
        (hlift i)
      have hρBk := rhoBlock_ker (blockOf (⊤ : Subgroup G) R V hX (Lc i)) LS (Lc i) (hρmem i)
        (hBLS i) hker (hImage.core i)
      let eq1 : (↥(blockOf (⊤ : Subgroup G) R V hX (Lc i)) ⧸
          CFSG.pCore 2 ↥(blockOf (⊤ : Subgroup G) R V hX (Lc i))) ≃* ↥(Lc i) :=
        (QuotientGroup.quotientMulEquivOfEq hρBk.symm).trans
          (QuotientGroup.quotientKerEquivOfSurjective _ hρBs)
      exact CFSG.LocalCores.isQuasisimple_of_mulEquiv eq1.symm
        (isQuasisimple_of_isComp (ctx.comps.isComp i))
    · rw [hZ, hU]
      refine ⟨bot_lt_iff_ne_bot.2 (hfam.nonzero i), fun W' hZW hWU hBW => ?_⟩
      have hinvW : ∀ x ∈ Lc i, ∀ w : V, (w : G) ∈ W' → ((x w : V) : G) ∈ W' := by
        intro x hx w hw
        obtain ⟨b, hb, rfl⟩ := hlift i x hx
        show b * (w : G) * b⁻¹ ∈ W'
        exact (Subgroup.mem_normalizer_iff.1 (hBW hb) w).1 hw
      exact hfam.irr i W' hWU hinvW
  have hBlock : ∀ i, IsBlock2 (⊤ : Subgroup G) (blockOf (⊤ : Subgroup G) R V hX (Lc i)) :=
    fun i => ⟨hShort i, le_top, hsub i⟩
  refine ⟨fun i => ⟨hBlock i, Or.inr (Or.inr (hAlt i))⟩, hAlt, fun i => ?_⟩
  exact CFSG.Quasithin.mem_cComp_iff.1
    (CFSG.QuasithinUnique.L238.mem_cComp_of_isChi0Block_nonsolvable (hBlock i)
      (Or.inr (hAlt i)))

end Main

end CFSG.QuasithinUnique.Setup.Lift
