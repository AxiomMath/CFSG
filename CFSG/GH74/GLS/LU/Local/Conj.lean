module

public import CFSG.GH74.GLS.LU.Local.Lemma62
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.LU.Compat
public import CFSG.GH74.Statements
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.GH74.GLS.LU.Local

open Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G]

theorem isCompIn_map_conj {X L : Subgroup G} (h : IsCompIn X L) (c : G) :
    IsCompIn (X.map (MulAut.conj c).toMonoidHom) (L.map (MulAut.conj c).toMonoidHom) := by
  obtain ⟨hLX, hcomp⟩ := h
  refine ⟨Subgroup.map_mono hLX, ?_⟩
  let e : ↥X ≃* ↥(X.map (MulAut.conj c).toMonoidHom) := (MulAut.conj c).subgroupMap X
  have hmap : (L.subgroupOf X).map e.toMonoidHom =
      (L.map (MulAut.conj c).toMonoidHom).subgroupOf (X.map (MulAut.conj c).toMonoidHom) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, Subgroup.mem_subgroupOf.mp hw, rfl⟩
    · intro hz
      obtain ⟨k, hk, hkz⟩ := Subgroup.mem_subgroupOf.mp hz
      have hkX : k ∈ X := hLX hk
      exact ⟨⟨k, hkX⟩, Subgroup.mem_subgroupOf.mpr hk, Subtype.ext hkz⟩
  have := CFSG.LocalCores.isComponent_map_mulEquiv e hcomp
  rwa [hmap] at this

theorem center_map_conj (K : Subgroup G) (c : G) :
    (center ↥(K.map (MulAut.conj c).toMonoidHom)).map
        (K.map (MulAut.conj c).toMonoidHom).subtype =
      ((center ↥K).map K.subtype).map (MulAut.conj c).toMonoidHom := by
  let e : ↥K ≃* ↥(K.map (MulAut.conj c).toMonoidHom) := (MulAut.conj c).subgroupMap K
  have h1 : (center ↥K).map (e : ↥K →* ↥(K.map (MulAut.conj c).toMonoidHom)) =
      center ↥(K.map (MulAut.conj c).toMonoidHom) := Subgroup.map_center_eq e
  rw [← h1, Subgroup.map_map, Subgroup.map_map]
  congr 1

namespace LUComps

variable {q : ℕ} {z : G} {K₁ K₂ : Subgroup G}

theorem conj [Finite G] (h : LUComps G q z K₁ K₂) (c : G) :
    LUComps G q (c * z * c⁻¹) (K₁.map (MulAut.conj c).toMonoidHom)
      (K₂.map (MulAut.conj c).toMonoidHom) := by
  have hC : (Cz z).map (MulAut.conj c).toMonoidHom = Cz (c * z * c⁻¹) :=
    CFSG.GH74.GLS.Stage1.Thm2.Recip.map_centralizer_singleton_conj z c
  have hCinv : ((Cz (c * z * c⁻¹)).map (MulAut.conj c⁻¹).toMonoidHom) = Cz z := by
    rw [← hC]
    exact CFSG.GH74.GLS.Stage1.Thm3.Sec4.cmap_inv_cancel c (Cz z)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := isCompIn_map_conj h.comp₁ c
    rwa [hC] at this
  · have := isCompIn_map_conj h.comp₂ c
    rwa [hC] at this
  · exact fun he => h.ne (Subgroup.map_injective (MulAut.conj c).injective he)
  · intro L hL
    have hL' := CFSG.GH74.GLS.Stage1.Thm2.Recip.isPCompIn_map_conj hL c⁻¹
    rw [hCinv] at hL'
    have hcancel : (L.map (MulAut.conj c⁻¹).toMonoidHom).map (MulAut.conj c).toMonoidHom = L :=
      CFSG.GH74.GLS.Stage1.Thm3.Sec4.cmap_cancel c L
    rcases h.only _ hL' with e | e
    · left; rw [← hcancel, e]
    · right; rw [← hcancel, e]
  · obtain ⟨F, hF, hFin, hq, ⟨e⟩⟩ := h.sl₁
    exact ⟨F, hF, hFin, hq, ⟨((MulAut.conj c).subgroupMap K₁).symm.trans e⟩⟩
  · obtain ⟨F, hF, hFin, hq, ⟨e⟩⟩ := h.sl₂
    exact ⟨F, hF, hFin, hq, ⟨((MulAut.conj c).subgroupMap K₂).symm.trans e⟩⟩
  · rw [center_map_conj, h.cen₁, MonoidHom.map_zpowers]
    rfl
  · rw [center_map_conj, h.cen₂, MonoidHom.map_zpowers]
    rfl

theorem cj [Finite G] (h : LUComps G q z K₁ K₂) (g : G) :
    LUComps G q (g⁻¹ * z * g) (CFSG.GH74.GLS.LU.Local.cj K₁ g) (CFSG.GH74.GLS.LU.Local.cj K₂ g) := by
  have := h.conj g⁻¹
  rwa [inv_inv] at this

end LUComps

namespace LUSyl

variable {z : G} {S : Sylow 2 G} {K₁ K₂ : Subgroup G} {t u : G}

theorem mul_z {q : ℕ} (hc : LUComps G q z K₁ K₂) (h : LUSyl G z S K₁ K₂ t u) :
    LUSyl G z S K₁ K₂ t (u * z) where
  z_inv := h.z_inv
  z_cen := h.z_cen
  t_mem := h.t_mem
  t_conj := h.t_conj
  t_swap := h.t_swap
  u_mem := mul_mem h.u_mem h.z_mem
  u_ord := by
    have hz2 := h.z_sq
    have hu2 : u * u = 1 := by
      have : u ^ 2 = 1 := by rw [← h.u_ord]; exact pow_orderOf_eq_one u
      rwa [pow_two] at this
    have hcomm : u * z = z * u := h.comm_z h.u_mem
    have hsq : (u * z) ^ 2 = 1 := by
      calc (u * z) ^ 2 = u * z * (u * z) := pow_two _
        _ = u * u * (z * z) := by
          calc u * z * (u * z) = u * (z * u) * z := by group
            _ = u * (u * z) * z := by rw [hcomm]
            _ = u * u * (z * z) := by group
        _ = 1 := by rw [hu2, hz2]; group
    have hne : u * z ≠ 1 := by
      intro h1
      apply h.u_ne
      have : u = z⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this, inv_eq_of_mul_eq_one_right hz2]
    exact orderOf_eq_prime hsq hne
  u_ne := by
    intro h1
    have : u = 1 := by
      calc u = u * z * z⁻¹ := by group
        _ = 1 := by rw [h1]; group
    have := h.u_ord
    rw [‹u = 1›, orderOf_one] at this
    omega
  u_conj := h.uz_conj
  uz_conj := by
    have : u * z * z = u := by rw [mul_assoc, h.z_sq, mul_one]
    rw [this]; exact h.u_conj
  u_norm := by
    exact mul_mem h.u_norm hc.z_mem_normalizer₁
  ut := by
    have hz : z * t = t * z := (h.comm_z h.t_mem).symm
    calc u * z * t = u * (z * t) := by group
      _ = u * (t * z) := by rw [hz]
      _ = (u * t) * z := by group
      _ = (t * u) * z := by rw [h.ut]
      _ = t * (u * z) := by group
  coset := h.coset
  cs := h.cs
  card_S := h.card_S
  cen_ab := h.cen_ab

theorem t_sq (h : LUSyl G z S K₁ K₂ t u) : t * t = 1 := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h.t_conj
  rw [← hc]
  calc c * z * c⁻¹ * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
    _ = 1 := by rw [h.z_sq]; group

theorem u_sq (h : LUSyl G z S K₁ K₂ t u) : u * u = 1 := by
  have : u ^ 2 = 1 := by rw [← h.u_ord]; exact pow_orderOf_eq_one u
  rwa [pow_two] at this

theorem zt_comm (h : LUSyl G z S K₁ K₂ t u) : z * t = t * z := (h.comm_z h.t_mem).symm

theorem zu_comm (h : LUSyl G z S K₁ K₂ t u) : z * u = u * z := (h.comm_z h.u_mem).symm

theorem t_not_normalizer {q : ℕ} (hc : LUComps G q z K₁ K₂) (h : LUSyl G z S K₁ K₂ t u) :
    t ∉ normalizer (K₁ : Set G) := by
  intro hn
  apply hc.ne
  rw [← h.t_swap]
  exact (Subgroup.mem_normalizer_iff_map_conj_eq.mp hn).symm

theorem t_ne_z {q : ℕ} (hc : LUComps G q z K₁ K₂) (h : LUSyl G z S K₁ K₂ t u) : t ≠ z := by
  intro htz
  exact h.t_not_normalizer hc (by rw [htz]; exact hc.z_mem_normalizer₁)

theorem t_mem_Cz (h : LUSyl G z S K₁ K₂ t u) : t ∈ Cz z := h.S_le_Cz h.t_mem

theorem u_mem_Cz (h : LUSyl G z S K₁ K₂ t u) : u ∈ Cz z := h.S_le_Cz h.u_mem

theorem t_swap₂ (h : LUSyl G z S K₁ K₂ t u) : K₂.map (MulAut.conj t).toMonoidHom = K₁ := by
  rw [← h.t_swap, Subgroup.map_map]
  have : ((MulAut.conj t).toMonoidHom.comp (MulAut.conj t).toMonoidHom) = MonoidHom.id G := by
    ext x
    show t * (t * x * t⁻¹) * t⁻¹ = x
    calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
      _ = x := by rw [h.t_sq]; group
  rw [this]
  exact Subgroup.map_id K₁

theorem card_eq (h : LUSyl G z S K₁ K₂ t u) : Nat.card K₁ = Nat.card K₂ := by
  rw [← h.t_swap]
  exact (card_map_conj K₁ t).symm

end LUSyl

section ZSwaps

variable {q : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ : Subgroup G} {t u : G}

theorem LUComps.card_sup [Finite G] (hc : LUComps G q z K₁ K₂) (hz : orderOf z = 2) :
    Nat.card ↥(K₁ ⊔ K₂) * 2 = Nat.card K₁ * Nat.card K₂ := by
  have h1 := card_sup_mul_card_inf_of_commute hc.comm
  rw [hc.inf_eq, Nat.card_zpowers, hz] at h1
  exact h1

theorem z_not_fix_J [Finite G] (hc : LUComps G q z K₁ K₂) (hs : LUSyl G z S K₁ K₂ t u) {g : G}
    (hg : g⁻¹ * z * g = t) :
    ¬ ((∀ a ∈ cj K₁ g, z * a * z⁻¹ ∈ cj K₁ g) ∧ (∀ a ∈ cj K₂ g, z * a * z⁻¹ ∈ cj K₂ g)) := by
  rintro ⟨hf₁, hf₂⟩
  have hts₁ : ∀ k ∈ K₁, t * k * t⁻¹ ∈ K₂ := fun k hk => LUComps.mem_of_map hs.t_swap hk
  have hts₂ : ∀ k ∈ K₂, t * k * t⁻¹ ∈ K₁ := fun k hk => LUComps.mem_of_map hs.t_swap₂ hk
  obtain ⟨hdiag, hJC⟩ := diag_setup hs.z_sq hs.z_ne_one (hs.t_ne_z hc) hs.zt_comm hg
    hc.perfect₁ hc.perfect₂ hc.comm hc.inf_eq hs.card_eq (hc.card_sup hs.z_inv) hts₁ hc.cen₁
    hc.quasi₁.2.1 (diag_le_cj hc hs.z_inv hs.t_sq hs.zt_comm hg hts₁ hts₂) (hCK_of_syl hc hs)
  have hzD : ∀ i ∈ (diagHom K₁ K₂ t hc.comm hts₁).range, z * i * z⁻¹ = i := by
    rintro i ⟨k, rfl⟩
    show z * ((k : G) * (t * (k : G) * t⁻¹)) * z⁻¹ = (k : G) * (t * (k : G) * t⁻¹)
    have e1 := hc.cz₁ k.2
    have e2 := hc.cz₂ (hts₁ k k.2)
    calc z * ((k : G) * (t * (k : G) * t⁻¹)) * z⁻¹
        = (z * (k : G) * z⁻¹) * (z * (t * (k : G) * t⁻¹) * z⁻¹) := by group
      _ = (k : G) * (t * (k : G) * t⁻¹) := by
          have a1 : z * (k : G) * z⁻¹ = k := by
            calc z * (k : G) * z⁻¹ = (k * z) * z⁻¹ := by rw [← e1]
              _ = k := by group
          have a2 : z * (t * (k : G) * t⁻¹) * z⁻¹ = t * (k : G) * t⁻¹ := by
            calc z * (t * (k : G) * t⁻¹) * z⁻¹ = ((t * (k : G) * t⁻¹) * z) * z⁻¹ := by rw [← e2]
              _ = t * (k : G) * t⁻¹ := by group
          rw [a1, a2]
  obtain ⟨h1, h2⟩ := hdiag z hzD hf₁ hf₂
  apply hJC
  refine sup_le (fun j hj => ?_) (fun j hj => ?_)
  · have := h1 j hj
    rw [mem_centralizer_singleton_iff]
    calc j * z = (z * j * z⁻¹) * z := by rw [this]
      _ = z * j := by group
  · have := h2 j hj
    rw [mem_centralizer_singleton_iff]
    calc j * z = (z * j * z⁻¹) * z := by rw [this]
      _ = z * j := by group

theorem z_swaps_J [Finite G] (hc : LUComps G q z K₁ K₂) (hs : LUSyl G z S K₁ K₂ t u) {g : G}
    (hg : g⁻¹ * z * g = t) :
    (∀ a ∈ cj K₁ g, z * a * z⁻¹ ∈ cj K₂ g) ∧ (∀ a ∈ cj K₂ g, z * a * z⁻¹ ∈ cj K₁ g) := by
  have hJ : LUComps G q t (cj K₁ g) (cj K₂ g) := by
    have := hc.cj g
    rwa [hg] at this
  have hzC : z ∈ Cz t := mem_centralizer_singleton_iff.mpr hs.zt_comm
  rcases hJ.perm' z hzC with hfix | hswap
  · exact absurd hfix (z_not_fix_J hc hs hg)
  · exact hswap

theorem prop61a [Finite G] (hc : LUComps G q z K₁ K₂) (hs : LUSyl G z S K₁ K₂ t u) {g : G}
    (hg : g⁻¹ * z * g = t) :
    ((∀ a ∈ cj K₁ g, u * a * u⁻¹ ∈ cj K₁ g) ∧ (∀ a ∈ cj K₂ g, u * a * u⁻¹ ∈ cj K₂ g)) ∨
    ((∀ a ∈ cj K₁ g, (u * z) * a * (u * z)⁻¹ ∈ cj K₁ g) ∧
      (∀ a ∈ cj K₂ g, (u * z) * a * (u * z)⁻¹ ∈ cj K₂ g)) := by
  have hJ : LUComps G q t (cj K₁ g) (cj K₂ g) := by
    have := hc.cj g
    rwa [hg] at this
  have huC : u ∈ Cz t := mem_centralizer_singleton_iff.mpr hs.ut
  have hzC : z ∈ Cz t := mem_centralizer_singleton_iff.mpr hs.zt_comm
  have huzC : u * z ∈ Cz t := mul_mem huC hzC
  rcases hJ.perm' u huC with hu | hu
  · exact Or.inl hu
  · right
    rcases hJ.perm' (u * z) huzC with huz | huz
    · exact huz
    · exfalso
      apply z_not_fix_J hc hs hg
      refine ⟨fun a ha => ?_, fun a ha => ?_⟩
      · have h1 := huz.1 a ha
        have h2 := hu.2 _ h1
        have e : u * ((u * z) * a * (u * z)⁻¹) * u⁻¹ = (u * u) * (z * a * z⁻¹) * (u * u)⁻¹ := by
          group
        rw [e, hs.u_sq] at h2
        simpa using h2
      · have h1 := huz.2 a ha
        have h2 := hu.1 _ h1
        have e : u * ((u * z) * a * (u * z)⁻¹) * u⁻¹ = (u * u) * (z * a * z⁻¹) * (u * u)⁻¹ := by
          group
        rw [e, hs.u_sq] at h2
        simpa using h2

end ZSwaps

end CFSG.GH74.GLS.LU.Local
