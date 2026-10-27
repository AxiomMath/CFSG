module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.TransvectionIrreducible
import CFSG.HardMathSupport.Cooperstein.Coordinator.StarAux
import CFSG.GroupTheory.PCore.OpenTransport

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG.AGLEmbedding (blockV barM)
open CFSG.Open (pCoreOf)
open CFSG.Quasithin (omegaOneCenterOf centerOf)
open Subgroup
open scoped commutatorElement

section PCoreOf

variable {G : Type} [Group G]

theorem pCoreOf_le_self (H : Subgroup G) : pCoreOf 2 H ≤ H := CFSG.openPCoreOf_le 2 H

theorem isPGroup_pCoreOf (H : Subgroup G) : IsPGroup 2 (pCoreOf 2 H) := by
  change IsPGroup 2 ((CFSG.Open.pCore 2 ↥H).map H.subtype)
  exact CFSG.pCore_isPGroup.map _

theorem mem_pCoreOf_of_mem_pCore {H : Subgroup G} {x : ↥H} (hx : x ∈ CFSG.pCore 2 ↥H) :
    (x : G) ∈ pCoreOf 2 H := (CFSG.mem_openPCoreOf_iff x).mpr hx

theorem exists_mem_pCore_of_mem_pCoreOf {H : Subgroup G} {x : G} (hx : x ∈ pCoreOf 2 H) :
    ∃ y : ↥H, y ∈ CFSG.pCore 2 ↥H ∧ (y : G) = x := by
  change x ∈ (CFSG.Open.pCore 2 ↥H).map H.subtype at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, hy, rfl⟩

theorem le_pCoreOf_of_le_normalizer {H N : Subgroup G} (hNH : N ≤ H)
    (hN : H ≤ normalizer (N : Set G)) (hp : IsPGroup 2 N) : N ≤ pCoreOf 2 H := by
  have hnorm : (N.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hN
  have hp' : IsPGroup 2 (N.subgroupOf H) :=
    hp.of_equiv (Subgroup.subgroupOfEquivOfLe hNH).symm
  have hle : N.subgroupOf H ≤ CFSG.pCore 2 ↥H := le_sSup ⟨hnorm, hp'⟩
  intro x hx
  exact mem_pCoreOf_of_mem_pCore (hle (show (⟨x, hNH hx⟩ : ↥H) ∈ N.subgroupOf H from hx))

theorem conj_mem_pCoreOf {H : Subgroup G} {g : G} (hg : g ∈ normalizer (H : Set G)) {x : G}
    (hx : x ∈ pCoreOf 2 H) : g * x * g⁻¹ ∈ pCoreOf 2 H := by
  obtain ⟨y, hy, rfl⟩ := exists_mem_pCore_of_mem_pCoreOf hx
  let e : MulAut ↥H := H.normalizerMonoidHom ⟨g, hg⟩
  have h1 : e y ∈ CFSG.pCore 2 ↥H := by
    have := CFSG.pCore_map_iso 2 (e : ↥H ≃* ↥H)
    rw [← this]
    exact ⟨y, hy, rfl⟩
  have h2 : ((e y : ↥H) : G) = g * (y : G) * g⁻¹ :=
    Subgroup.normalizerMonoidHom_apply_apply_coe H ⟨g, hg⟩ y
  rw [← h2]
  exact mem_pCoreOf_of_mem_pCore h1

end PCoreOf

section Blocks

variable {G : Type} [Group G] {S L : Subgroup G}

theorem pCoreOf_le_pCoreOf_sup (hSL : S ≤ normalizer (L : Set G)) :
    pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ S) := by
  refine le_pCoreOf_of_le_normalizer ((pCoreOf_le_self L).trans le_sup_left) ?_
    (isPGroup_pCoreOf L)
  refine sup_le ?_ ?_
  · exact TransvIrr.le_normalizer_of_conj_mem fun g hg x hx =>
      conj_mem_pCoreOf (Subgroup.le_normalizer hg) hx
  · exact TransvIrr.le_normalizer_of_conj_mem fun g hg x hx =>
      conj_mem_pCoreOf (hSL hg) hx

theorem blockV_le_centerOf (S L : Subgroup G) :
    blockV S L ≤ centerOf (pCoreOf 2 (L ⊔ S)) :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1

theorem blockV_le_pCoreOf (S L : Subgroup G) : blockV S L ≤ pCoreOf 2 (L ⊔ S) :=
  (blockV_le_centerOf S L).trans inf_le_left

theorem commute_of_mem_pCoreOf_blockV {q v : G} (hq : q ∈ pCoreOf 2 (L ⊔ S))
    (hv : v ∈ blockV S L) : q * v = v * q := by
  have := (blockV_le_centerOf S L hv).2
  exact Subgroup.mem_centralizer_iff.mp this q hq

theorem commutator_le_commutator_commutator_of_perfect {B L : Subgroup G} (hperf : ⁅L, L⁆ = L)
    (hLB : L ≤ normalizer (B : Set G))
    (hBN : B ≤ normalizer ((⁅⁅B, L⁆, L⁆ : Subgroup G) : Set G)) : ⁅B, L⁆ ≤ ⁅⁅B, L⁆, L⁆ := by
  have hLL : L ≤ normalizer (L : Set G) := Subgroup.le_normalizer
  have hLN : L ≤ normalizer ((⁅⁅B, L⁆, L⁆ : Subgroup G) : Set G) := fun g hg =>
    TransvIrr.mem_normalizer_commutator
      (TransvIrr.mem_normalizer_commutator (hLB hg) (hLL hg)) (hLL hg)
  have h3 := TransvIrr.commutator_commutator_le_of_rotate (A := L) (B := B) (C := L) hLN hBN hLN
    (by rw [Subgroup.commutator_comm L B]) le_rfl
  rw [hperf] at h3
  exact (Subgroup.commutator_comm B L).le.trans h3

theorem blockU_eq_commutator_blockV {s : G} (hSL : S ≤ normalizer (L : Set G))
    (hperf : ⁅L, L⁆ = L) (hset : TransvIrr.Setting (L ⊔ S) L (blockV S L) s)
    (hQV : ⁅pCoreOf 2 (L ⊔ S), L⁆ ≤ blockV S L) :
    CFSG.QuasithinUnique.blockU L = ⁅blockV S L, L⁆ := by
  have hQ'Q : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ S) := pCoreOf_le_pCoreOf_sup hSL
  have hVM : blockV S L ≤ L ⊔ S := (blockV_le_pCoreOf S L).trans (pCoreOf_le_self _)
  have hVLL : (⁅blockV S L, L⁆ : Subgroup G) ≤ L := by
    refine Subgroup.commutator_le.mpr fun v hv l hl => ?_
    have h1 : v * l * v⁻¹ ∈ L := TransvIrr.conj_mem_of_le_normalizer hset.normL (hVM hv) hl
    have : (⁅v, l⁆ : G) = (v * l * v⁻¹) * l⁻¹ := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact L.mul_mem h1 (L.inv_mem hl)
  have hVLle : (⁅blockV S L, L⁆ : Subgroup G) ≤ pCoreOf 2 L := by
    refine le_pCoreOf_of_le_normalizer hVLL (fun g hg => hset.normU (hset.le hg)) ?_
    exact (isPGroup_pCoreOf (L ⊔ S)).to_le (hset.U_le_V.trans (blockV_le_pCoreOf S L))
  have hge : (⁅blockV S L, L⁆ : Subgroup G) ≤ ⁅pCoreOf 2 L, L⁆ :=
    hset.comm_comm_ge.trans (Subgroup.commutator_mono hVLle le_rfl)
  have hQ'V : (⁅pCoreOf 2 L, L⁆ : Subgroup G) ≤ blockV S L :=
    (Subgroup.commutator_mono hQ'Q le_rfl).trans hQV
  have hLQ' : L ≤ normalizer ((pCoreOf 2 L : Subgroup G) : Set G) :=
    TransvIrr.le_normalizer_of_conj_mem fun g hg x hx =>
      conj_mem_pCoreOf (Subgroup.le_normalizer hg) hx
  have hLN : L ≤ normalizer ((⁅⁅pCoreOf 2 L, L⁆, L⁆ : Subgroup G) : Set G) := fun g hg =>
    TransvIrr.mem_normalizer_commutator
      (TransvIrr.mem_normalizer_commutator (hLQ' hg) (Subgroup.le_normalizer hg))
      (Subgroup.le_normalizer hg)
  have hle : (⁅pCoreOf 2 L, L⁆ : Subgroup G) ≤ ⁅⁅pCoreOf 2 L, L⁆, L⁆ :=
    commutator_le_commutator_commutator_of_perfect hperf hLQ'
      ((pCoreOf_le_self L).trans (fun g hg => hLN hg))
  exact le_antisymm (hle.trans (Subgroup.commutator_mono hQ'V le_rfl)) hge

theorem blockZ_eq_of_blockU_eq (h : CFSG.QuasithinUnique.blockU L = ⁅blockV S L, L⁆) :
    CFSG.QuasithinUnique.blockZ L = ⁅blockV S L, L⁆ ⊓ centralizer (L : Set G) := by
  rw [CFSG.QuasithinUnique.blockZ, h]

end Blocks

section Kernel

variable {G : Type} [Group G]

theorem ker_eq_pCore_of_quasisimple {X L : Subgroup G} (hLX : L ≤ X)
    (hqs : CFSG.Open.IsQuasisimple ↥(barM X L)) (hZ : Subgroup.center ↥(barM X L) = ⊥)
    {Γ : Type*} [Group Γ] (ρ : ↥L →* Γ) (hpk : CFSG.pCore 2 ↥L ≤ ρ.ker)
    (hne : ρ.ker ≠ ⊤) : ρ.ker = CFSG.pCore 2 ↥L := by
  refine le_antisymm ?_ hpk
  let φ0 : ↥L →* (↥X ⧸ CFSG.pCore 2 ↥X) :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥X)).comp (Subgroup.inclusion hLX)
  have hmem : ∀ l : ↥L, φ0 l ∈ barM X L := fun l =>
    ⟨⟨(l : G), hLX l.2⟩, l.2, rfl⟩
  let π : ↥L →* ↥(barM X L) := φ0.codRestrict _ hmem
  have hπ : Function.Surjective π := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨(x : G), hx⟩, Subtype.ext rfl⟩
  have hπ1 : ∀ l : ↥L, π l = 1 ↔ (⟨(l : G), hLX l.2⟩ : ↥X) ∈ CFSG.pCore 2 ↥X := fun l => by
    rw [← Subtype.coe_inj, ← QuotientGroup.eq_one_iff]
    rfl
  have hkerπ : π.ker ≤ CFSG.pCore 2 ↥L := by
    let f : ↥π.ker →* ↥(CFSG.pCore 2 ↥X) :=
      (((Subgroup.inclusion hLX).comp π.ker.subtype)).codRestrict _ fun r =>
        (hπ1 r).mp (MonoidHom.mem_ker.mp r.2)
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      have := congrArg (fun z : ↥(CFSG.pCore 2 ↥X) => ((z : ↥X) : G)) hab
      exact this
    have hp : IsPGroup 2 ↥π.ker := CFSG.pCore_isPGroup.of_injective f hf
    have hn : π.ker.Normal := MonoidHom.normal_ker π
    exact le_sSup ⟨hn, hp⟩
  have hnormal : (ρ.ker.map π).Normal := Subgroup.Normal.map (MonoidHom.normal_ker ρ) π hπ
  rcases CFSG.HardMathSupport.Cooperstein.Coordinator.StarAux.normal_le_center_or_eq_top
    hqs.1 hqs.2 _ hnormal with hc | htop
  · rw [hZ, le_bot_iff, Subgroup.map_eq_bot_iff] at hc
    exact hc.trans hkerπ
  · exfalso
    apply hne
    rw [eq_top_iff]
    intro l _
    have hl : π l ∈ ρ.ker.map π := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨k, hk, hπk⟩ := hl
    have h1 : k⁻¹ * l ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hπk, inv_mul_cancel]
    have h2 : k⁻¹ * l ∈ ρ.ker := hpk (hkerπ h1)
    have := ρ.ker.mul_mem hk h2
    rwa [mul_inv_cancel_left] at this

end Kernel

end CFSG.HardMathSupport.Cooperstein.StructureLie
