module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenSolvDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeSolvDirectCount
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SUThreeTwoShape
import CFSG.LocalAnalysis.AGLEmbedding.CZeroBasic
import CFSG.LocalAnalysis.AGLEmbedding.SUPairModel

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.ComponentClassification.AS76b (oUpperTwo)
open scoped commutatorElement

namespace SolvDirectCfg

section Involution

variable {X : Type*} [Group X]

private def fixMod (O : Subgroup X) (t : X) : Subgroup X where
  carrier := {b | b ∈ normalizer (O : Set X) ∧ t * b * t⁻¹ * b⁻¹ ∈ O}
  mul_mem' {b c} hb hc := by
    refine ⟨mul_mem hb.1 hc.1, ?_⟩
    have h1 : b * (t * c * t⁻¹ * c⁻¹) * b⁻¹ ∈ O := (mem_normalizer_iff.mp hb.1 _).mp hc.2
    have e : t * (b * c) * t⁻¹ * (b * c)⁻¹ =
        (t * b * t⁻¹ * b⁻¹) * (b * (t * c * t⁻¹ * c⁻¹) * b⁻¹) := by group
    rw [e]
    exact mul_mem hb.2 h1
  one_mem' := ⟨one_mem _, by simp⟩
  inv_mem' {b} hb := by
    refine ⟨inv_mem hb.1, ?_⟩
    have h1 : b⁻¹ * (t * b * t⁻¹ * b⁻¹)⁻¹ * b⁻¹⁻¹ ∈ O :=
      (mem_normalizer_iff.mp (inv_mem hb.1) _).mp (inv_mem hb.2)
    have e : t * b⁻¹ * t⁻¹ * b⁻¹⁻¹ = b⁻¹ * (t * b * t⁻¹ * b⁻¹)⁻¹ * b⁻¹⁻¹ := by group
    rw [e]
    exact h1

private theorem mem_fixMod {O : Subgroup X} {t b : X} :
    b ∈ fixMod O t ↔ b ∈ normalizer (O : Set X) ∧ t * b * t⁻¹ * b⁻¹ ∈ O :=
  Iff.rfl

private theorem sup_inf_sup_le {A B O : Subgroup X} {t : X}
    (hA : A ≤ normalizer (O : Set X)) (hB : B ≤ normalizer (O : Set X))
    (ht : t ∈ normalizer (O : Set X))
    (hinv : ∀ a ∈ A, t * a * t⁻¹ * a ∈ O) (hcube : ∀ a ∈ A, a ^ 3 ∈ O)
    (hfix : ∀ b ∈ B, t * b * t⁻¹ * b⁻¹ ∈ O) :
    (A ⊔ O) ⊓ (B ⊔ O) ≤ O := by
  intro x hx
  obtain ⟨hxA, hxB⟩ := mem_inf.mp hx
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right A O hA] at hxA
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right B O hB] at hxB
  obtain ⟨a, ha, o₁, ho₁, rfl⟩ := hxA
  obtain ⟨b, hb, o₂, ho₂, hab⟩ := hxB
  have hab' : b * o₂ = a * o₁ := hab
  obtain ⟨u, hu, rfl⟩ : ∃ u ∈ O, a * u = b :=
    ⟨o₁ * o₂⁻¹, mul_mem ho₁ (inv_mem ho₂), by rw [← mul_assoc, ← hab', mul_inv_cancel_right]⟩
  have hc := hfix _ hb
  have hu' : t * u * t⁻¹ ∈ O := (mem_normalizer_iff.mp ht u).mp hu
  have hw : a * (u * (t * u * t⁻¹)⁻¹) * a⁻¹ ∈ O :=
    (mem_normalizer_iff.mp (hA ha) _).mp (mul_mem hu (inv_mem hu'))
  have h2 : a * a ∈ O := by
    have e : a * a = (a * (u * (t * u * t⁻¹)⁻¹) * a⁻¹)⁻¹ *
        ((t * (a * u) * t⁻¹ * (a * u)⁻¹)⁻¹ * (t * a * t⁻¹ * a)) := by group
    rw [e]
    exact mul_mem (inv_mem hw) (mul_mem (inv_mem hc) (hinv a ha))
  have haO : a ∈ O := by
    have h := mul_mem (hcube a ha) (inv_mem h2)
    rwa [pow_succ, sq, show a * a * a * (a * a)⁻¹ = a by group] at h
  exact mul_mem haO ho₁

end Involution

section Quotient

variable {G : Type} [Group G] {H : Subgroup G} (N : Subgroup ↥H) [N.Normal]

private theorem map_conj_map_mk (h : ↥H) (A : Subgroup G) :
    ((A.subgroupOf H).map (QuotientGroup.mk' N)).map
        (MulAut.conj (QuotientGroup.mk' N h)).toMonoidHom =
      ((A.map (MulAut.conj (h : G)).toMonoidHom).subgroupOf H).map (QuotientGroup.mk' N) := by
  rw [subgroupOf_map_conj h.2 A, Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem map_mk_le_normalizer {A B : Subgroup G} (hAB : A ≤ normalizer (B : Set G)) :
    (A.subgroupOf H).map (QuotientGroup.mk' N) ≤
      normalizer (((B.subgroupOf H).map (QuotientGroup.mk' N) : Subgroup (↥H ⧸ N)) :
        Set (↥H ⧸ N)) := by
  refine le_trans (Subgroup.map_mono ?_) (Subgroup.le_normalizer_map _)
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  exact Subgroup.mem_normalizer_iff.mp (hAB (Subgroup.mem_subgroupOf.mp hx)) y

private theorem commutator_map_mk_le {A B C : Subgroup G} (hABC : ⁅A, B⁆ ≤ C) :
    ⁅(A.subgroupOf H).map (QuotientGroup.mk' N), (B.subgroupOf H).map (QuotientGroup.mk' N)⁆ ≤
      (C.subgroupOf H).map (QuotientGroup.mk' N) := by
  rw [← Subgroup.map_commutator]
  refine Subgroup.map_mono ?_
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [Subgroup.mem_subgroupOf] at ha hb ⊢
  have e : ((⁅a, b⁆ : ↥H) : G) = ⁅(a : G), (b : G)⁆ := by
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [e]
  exact hABC (Subgroup.commutator_mem_commutator ha hb)

end Quotient

section Conjugates

variable {G : Type} [Group G] [Finite G]

private theorem perm3_inv (σ : Equiv.Perm (Fin 3)) (h : σ ^ 3 = 1) :
    Equiv.swap 0 1 * σ * (Equiv.swap 0 1)⁻¹ * σ = 1 := by
  revert σ
  decide

private theorem exists_inv_mod {I : Subgroup G}
    (hS3 : Nonempty (↥I ⧸ CFSG.pCore 2 ↥I ≃* Equiv.Perm (Fin 3))) :
    ∃ s ∈ I, ∀ a ∈ oUpperTwo I, s * a * s⁻¹ * a ∈ pCoreOf 2 I := by
  obtain ⟨e⟩ := hS3
  obtain ⟨s, hs⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥I) (e.symm (Equiv.swap 0 1))
  refine ⟨s, s.2, fun a ha => ?_⟩
  have haI : a ∈ I := oUpperTwo_le_self I ha
  have h3 : (⟨a, haI⟩ : ↥I) ^ 3 ∈ CFSG.pCore 2 ↥I := by
    obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp
      (IsCZeroMember.cube_mem kFactSUThreeTwoShape_holds (Or.inl ⟨e⟩) a ha)
    have hb' : b = (⟨a, haI⟩ : ↥I) ^ 3 := Subtype.ext (by simpa using hba)
    rwa [← hb']
  have hσ : e (QuotientGroup.mk' (CFSG.pCore 2 ↥I) ⟨a, haI⟩) ^ 3 = 1 := by
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥I) ((⟨a, haI⟩ : ↥I) ^ 3) = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact h3
    rw [← map_pow, ← map_pow, h1, map_one]
  have hs' : e (QuotientGroup.mk' (CFSG.pCore 2 ↥I) s) = Equiv.swap 0 1 := by
    rw [hs, MulEquiv.apply_symm_apply]
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥I) (s * ⟨a, haI⟩ * s⁻¹ * ⟨a, haI⟩) = 1 := by
    apply e.injective
    rw [map_one, map_mul, map_mul, map_mul, map_inv, map_mul, map_mul, map_mul, map_inv, hs']
    exact perm3_inv _ hσ
  have h2 : s * ⟨a, haI⟩ * s⁻¹ * ⟨a, haI⟩ ∈ CFSG.pCore 2 ↥I := by
    rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥I)]
    exact h1
  exact Subgroup.mem_map_of_mem I.subtype h2

private theorem commutator_map_conj_le {M H L I₀ : Subgroup G} (hL : IsTwoPrimeComponent M L)
    (hI₀ : IsCZeroMember (H ⊓ L) I₀)
    (hS3 : Nonempty (↥I₀ ⧸ CFSG.pCore 2 ↥I₀ ≃* Equiv.Perm (Fin 3)))
    (hblk : ∀ I₂ ∈ cZero (H ⊓ L), Nonempty (↥I₂ ⧸ CFSG.pCore 2 ↥I₂ ≃* Equiv.Perm (Fin 3)) →
      oUpperTwo I₀ ≠ oUpperTwo I₂ → ⁅I₀, I₂⁆ ≤ pCoreOf 2 (H ⊓ L))
    {g : G} (hg : g ∈ H ⊓ M)
    (hne : oUpperTwo I₀ ≠ (oUpperTwo I₀).map (MulAut.conj g).toMonoidHom) :
    ⁅I₀, I₀.map (MulAut.conj g).toMonoidHom⁆ ≤ pCoreOf 2 (H ⊓ M) := by
  have hHLM : CFSG.Open.IsSubnormal (H ⊓ L) (H ⊓ M) := by
    have h := hL.subnormal.inf H
    rwa [inf_comm L H, inf_comm M H] at h
  by_cases hgL : g ∈ normalizer (L : Set G)
  · have hgHL : g ∈ normalizer ((H ⊓ L : Subgroup G) : Set G) := by
      rw [mem_normalizer_iff]
      intro x
      exact (mem_inf.trans (and_congr (mem_normalizer_iff.mp (le_normalizer hg.1) x)
        (mem_normalizer_iff.mp hgL x))).trans mem_inf.symm
    have hS3g : Nonempty (↥(I₀.map (MulAut.conj g).toMonoidHom) ⧸
        CFSG.pCore 2 ↥(I₀.map (MulAut.conj g).toMonoidHom) ≃* Equiv.Perm (Fin 3)) := by
      obtain ⟨e⟩ := hS3
      exact ⟨(QuotientGroup.congr _ _ ((MulAut.conj g).subgroupMap I₀)
        (CFSG.pCore_map_iso 2 _)).symm.trans e⟩
    have hne' : oUpperTwo I₀ ≠ oUpperTwo (I₀.map (MulAut.conj g).toMonoidHom) := by
      rwa [← SUPair.map_oUpperTwo]
    exact (hblk _ (hI₀.map_conj hgHL) hS3g hne').trans (cfsg_subnormal_pCoreOf_le 2 hHLM)
  · have hLg : L ≠ L.map (MulAut.conj g).toMonoidHom := fun h =>
      hgL (mem_normalizer_iff_map_conj_eq.mpr h.symm)
    have hIL : I₀ ≤ L := hI₀.le.trans inf_le_right
    have h1 : ⁅I₀, I₀.map (MulAut.conj g).toMonoidHom⁆ ≤ pCoreOf 2 M :=
      (commutator_mono hIL (map_mono hIL)).trans (hL.commutator_le (hL.map_conj hg.2) hLg)
    have hIHM : I₀ ≤ H ⊓ M := hI₀.le.trans (inf_le_inf_left H hL.le)
    have hIgHM : I₀.map (MulAut.conj g).toMonoidHom ≤ H ⊓ M := by
      have hHM : (H ⊓ M).map (MulAut.conj g).toMonoidHom = H ⊓ M :=
        mem_normalizer_iff_map_conj_eq.mp (le_normalizer hg)
      exact (map_mono hIHM).trans hHM.le
    have h2 : ⁅I₀, I₀.map (MulAut.conj g).toMonoidHom⁆ ≤ H ⊓ M :=
      (commutator_mono hIHM hIgHM).trans (commutator_le_self _)
    have h3 : pCoreOf 2 M ⊓ (H ⊓ M) ≤ pCoreOf 2 (H ⊓ M) := by
      refine normal_pGroup_le_pCoreOf 2 _ _ inf_le_right ?_
        ((pCoreOf_isPGroup 2 M).to_le inf_le_left)
      rw [normal_subgroupOf_iff_le_normalizer inf_le_right]
      exact common_normalizer_le_normalizer_inf _ _ _
        (fun x hx => localGroup_le_normalizer_pCoreOf 2 M hx.2) le_normalizer
    exact (le_inf h1 h2).trans h3

private theorem commutator_map_conj_conj_le {H M I₀ : Subgroup G}
    (hA : ∀ g ∈ H ⊓ M, oUpperTwo I₀ ≠ (oUpperTwo I₀).map (MulAut.conj g).toMonoidHom →
      ⁅I₀, I₀.map (MulAut.conj g).toMonoidHom⁆ ≤ pCoreOf 2 (H ⊓ M)) :
    ∀ h₁ ∈ H ⊓ M, ∀ h₂ ∈ H ⊓ M, (oUpperTwo I₀).map (MulAut.conj h₁).toMonoidHom ≠
        (oUpperTwo I₀).map (MulAut.conj h₂).toMonoidHom →
      ⁅I₀.map (MulAut.conj h₁).toMonoidHom, I₀.map (MulAut.conj h₂).toMonoidHom⁆ ≤
        pCoreOf 2 (H ⊓ M) := by
  intro h₁ hh₁ h₂ hh₂ hne
  have hg : h₁⁻¹ * h₂ ∈ H ⊓ M := mul_mem (inv_mem hh₁) hh₂
  have e : ∀ Y : Subgroup G, Y.map (MulAut.conj h₂).toMonoidHom =
      (Y.map (MulAut.conj (h₁⁻¹ * h₂)).toMonoidHom).map (MulAut.conj h₁).toMonoidHom := by
    intro Y
    rw [← map_conj_mul_eq, mul_inv_cancel_left]
  have hne' : oUpperTwo I₀ ≠ (oUpperTwo I₀).map (MulAut.conj (h₁⁻¹ * h₂)).toMonoidHom := by
    intro heq
    apply hne
    rw [e, ← heq]
  rw [e I₀, ← Subgroup.map_commutator]
  calc (⁅I₀, I₀.map (MulAut.conj (h₁⁻¹ * h₂)).toMonoidHom⁆).map (MulAut.conj h₁).toMonoidHom
      ≤ (pCoreOf 2 (H ⊓ M)).map (MulAut.conj h₁).toMonoidHom := Subgroup.map_mono (hA _ hg hne')
    _ = pCoreOf 2 (H ⊓ M) :=
      mem_normalizer_iff_map_conj_eq.mp (localGroup_le_normalizer_pCoreOf 2 (H ⊓ M) hh₁)

private theorem solvThreeDirectCond_of {H M I₀ : Subgroup G} (N : Subgroup ↥H) [N.Normal]
    (hIHM : I₀ ≤ H ⊓ M) (hcore : pCoreOf 2 I₀ ≤ pCoreOf 2 (H ⊓ M))
    (hs : ∃ s ∈ I₀, ∀ a ∈ oUpperTwo I₀, s * a * s⁻¹ * a ∈ pCoreOf 2 I₀)
    (hcube : ∀ a ∈ oUpperTwo I₀, a ^ 3 ∈ pCoreOf 2 I₀)
    (hB : ∀ h₁ ∈ H ⊓ M, ∀ h₂ ∈ H ⊓ M, (oUpperTwo I₀).map (MulAut.conj h₁).toMonoidHom ≠
        (oUpperTwo I₀).map (MulAut.conj h₂).toMonoidHom →
      ⁅I₀.map (MulAut.conj h₁).toMonoidHom, I₀.map (MulAut.conj h₂).toMonoidHom⁆ ≤
        pCoreOf 2 (H ⊓ M)) :
    SolvThreeDirectCond (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' N))
      (((oUpperTwo I₀).subgroupOf H).map (QuotientGroup.mk' N)) := by
  obtain ⟨s, hsI, hsinv⟩ := hs
  set π := QuotientGroup.mk' N
  set X₀ := ((H ⊓ M).subgroupOf H).map π
  set J := ((oUpperTwo I₀).subgroupOf H).map π
  set D := ⨆ y ∈ X₀, J.map (MulAut.conj y).toMonoidHom with hD
  set O := (CFSG.pCore 2 ↥D).map D.subtype
  set N₂ := ((pCoreOf 2 (H ⊓ M)).subgroupOf H).map π
  have hconj : ∀ h : ↥H, J.map (MulAut.conj (π h)).toMonoidHom =
      (((oUpperTwo I₀).map (MulAut.conj (h : G)).toMonoidHom).subgroupOf H).map π :=
    fun h => map_conj_map_mk N h _
  have hX₀mem : ∀ y ∈ X₀, ∃ h : ↥H, (h : G) ∈ H ⊓ M ∧ π h = y := by
    intro y hy
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨h, Subgroup.mem_subgroupOf.mp hh, rfl⟩
  have hπX₀ : ∀ h : ↥H, (h : G) ∈ H ⊓ M → π h ∈ X₀ := fun h hh =>
    Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hh)
  have hJX : J ≤ X₀ :=
    Subgroup.map_mono (Subgroup.comap_mono ((oUpperTwo_le_self I₀).trans hIHM))
  have hJyD : ∀ y ∈ X₀, J.map (MulAut.conj y).toMonoidHom ≤ D := fun y hy =>
    le_iSup₂_of_le y hy le_rfl
  have hDX : D ≤ X₀ := iSup₂_le fun y hy =>
    (Subgroup.map_mono hJX).trans (mem_normalizer_iff_map_conj_eq.mp (le_normalizer hy)).le
  have hXD : X₀ ≤ normalizer (D : Set (↥H ⧸ N)) := by
    refine le_normalizer_of_forall_map_conj_le fun t ht => ?_
    rw [hD, Subgroup.map_iSup]
    refine iSup_le fun y => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hy => ?_
    rw [← map_conj_mul_eq]
    exact hJyD _ (mul_mem ht hy)
  have hDO : D ≤ normalizer (O : Set (↥H ⧸ N)) := localGroup_le_normalizer_pCoreOf 2 D
  have hXO : X₀ ≤ normalizer (O : Set (↥H ⧸ N)) :=
    hXD.trans (normalizer_localGroup_le_normalizer_pCoreOf 2 D)
  have hN₂O : ∀ x ∈ N₂, x ∈ D → x ∈ O := by
    have hXN : X₀ ≤ normalizer (N₂ : Set (↥H ⧸ N)) :=
      map_mk_le_normalizer N (localGroup_le_normalizer_pCoreOf 2 (H ⊓ M))
    have hN2 : IsPGroup 2 N₂ := ((pCoreOf_isPGroup 2 (H ⊓ M)).comap_subtype (K := H)).map π
    have h : N₂ ⊓ D ≤ O := by
      refine normal_pGroup_le_pCoreOf 2 _ D inf_le_right ?_ (hN2.to_le inf_le_left)
      rw [normal_subgroupOf_iff_le_normalizer inf_le_right]
      exact common_normalizer_le_normalizer_inf D N₂ D (hDX.trans hXN) le_normalizer
    exact fun x hx hxD => h (mem_inf.mpr ⟨hx, hxD⟩)
  have hmemN₂ : ∀ x : ↥H, (x : G) ∈ pCoreOf 2 (H ⊓ M) → π x ∈ N₂ := fun x hx =>
    Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hx)
  have hconjcore : ∀ g ∈ H ⊓ M, ∀ x ∈ pCoreOf 2 (H ⊓ M), g * x * g⁻¹ ∈ pCoreOf 2 (H ⊓ M) :=
    fun g hg x hx =>
      (mem_normalizer_iff.mp (localGroup_le_normalizer_pCoreOf 2 (H ⊓ M) hg) x).mp hx
  have hcomm : ∀ y₁ ∈ X₀, ∀ y₂ ∈ X₀,
      J.map (MulAut.conj y₁).toMonoidHom ≠ J.map (MulAut.conj y₂).toMonoidHom →
        ⁅J.map (MulAut.conj y₁).toMonoidHom, J.map (MulAut.conj y₂).toMonoidHom⁆ ≤ O := by
    intro y₁ hy₁ y₂ hy₂ hne
    have hD₁ := hJyD y₁ hy₁
    have hD₂ := hJyD y₂ hy₂
    obtain ⟨h₁, hh₁, rfl⟩ := hX₀mem y₁ hy₁
    obtain ⟨h₂, hh₂, rfl⟩ := hX₀mem y₂ hy₂
    have hDD := (commutator_mono hD₁ hD₂).trans (commutator_le_self D)
    rw [hconj h₁, hconj h₂] at hne hDD ⊢
    have hne' : (oUpperTwo I₀).map (MulAut.conj (h₁ : G)).toMonoidHom ≠
        (oUpperTwo I₀).map (MulAut.conj (h₂ : G)).toMonoidHom := fun he => hne (by rw [he])
    have h1 : ⁅(oUpperTwo I₀).map (MulAut.conj (h₁ : G)).toMonoidHom,
        (oUpperTwo I₀).map (MulAut.conj (h₂ : G)).toMonoidHom⁆ ≤ pCoreOf 2 (H ⊓ M) :=
      (commutator_mono (map_mono (oUpperTwo_le_self I₀)) (map_mono (oUpperTwo_le_self I₀))).trans
        (hB _ hh₁ _ hh₂ hne')
    have h2 := commutator_map_mk_le N h1
    exact fun x hx => hN₂O x (h2 hx) (hDD hx)
  have hind : ∀ y ∈ X₀, (J.map (MulAut.conj y).toMonoidHom ⊔ O) ⊓
      ((⨆ y' ∈ X₀, ⨆ (_ : J.map (MulAut.conj y').toMonoidHom ≠ J.map (MulAut.conj y).toMonoidHom),
        J.map (MulAut.conj y').toMonoidHom) ⊔ O) ≤ O := by
    intro y hy
    have hyD := hJyD y hy
    obtain ⟨h, hh, rfl⟩ := hX₀mem y hy
    have hsH : s ∈ H := (hIHM hsI).1
    obtain ⟨t₀, ht₀v⟩ : ∃ t₀ : ↥H, (t₀ : G) = (h : G) * s * (h : G)⁻¹ :=
      ⟨h * ⟨s, hsH⟩ * h⁻¹, rfl⟩
    have ht₀I : (t₀ : G) ∈ I₀.map (MulAut.conj (h : G)).toMonoidHom := by
      rw [ht₀v]
      exact Subgroup.mem_map.mpr ⟨s, hsI, by simp [MulAut.conj_apply]⟩
    have ht₀HM : (t₀ : G) ∈ H ⊓ M := by
      rw [ht₀v]
      exact mul_mem (mul_mem hh (hIHM hsI)) (inv_mem hh)
    have htD : π t₀ ∈ normalizer (D : Set (↥H ⧸ N)) := hXD (hπX₀ t₀ ht₀HM)
    have htO : π t₀ ∈ normalizer (O : Set (↥H ⧸ N)) := hXO (hπX₀ t₀ ht₀HM)
    have hJy : ∀ a ∈ J.map (MulAut.conj (π h)).toMonoidHom, ∃ a' : ↥H, ∃ a₀ ∈ oUpperTwo I₀,
        (a' : G) = (h : G) * a₀ * (h : G)⁻¹ ∧ π a' = a := by
      intro a ha
      rw [hconj h] at ha
      obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨a₀, ha₀, he⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp ha')
      exact ⟨a', a₀, ha₀, by simpa [MulAut.conj_apply] using he.symm, rfl⟩
    refine sup_inf_sup_le (hyD.trans hDO)
      ((iSup₂_le fun y' hy' => iSup_le fun _ => hJyD y' hy').trans hDO) htO ?_ ?_ ?_
    ·
      intro a ha
      obtain ⟨a', a₀, ha₀, hav, rfl⟩ := hJy a ha
      have hD' : π t₀ * π a' * (π t₀)⁻¹ * π a' ∈ D :=
        mul_mem ((mem_normalizer_iff.mp htD _).mp (hyD ha)) (hyD ha)
      have e2 : π (t₀ * a' * t₀⁻¹ * a') = π t₀ * π a' * (π t₀)⁻¹ * π a' := by
        simp only [map_mul, map_inv]
      rw [← e2] at hD' ⊢
      refine hN₂O _ (hmemN₂ _ ?_) hD'
      have e : ((t₀ * a' * t₀⁻¹ * a' : ↥H) : G) =
          (h : G) * (s * a₀ * s⁻¹ * a₀) * (h : G)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, ht₀v, hav]
        group
      rw [e]
      exact hconjcore _ hh _ (hcore (hsinv a₀ ha₀))
    ·
      intro a ha
      obtain ⟨a', a₀, ha₀, hav, rfl⟩ := hJy a ha
      have hD' : π a' ^ 3 ∈ D := pow_mem (hyD ha) 3
      rw [← map_pow] at hD' ⊢
      refine hN₂O _ (hmemN₂ _ ?_) hD'
      have e : ((a' ^ 3 : ↥H) : G) = (h : G) * a₀ ^ 3 * (h : G)⁻¹ := by
        rw [Subgroup.coe_pow, hav, conj_pow]
      rw [e]
      exact hconjcore _ hh _ (hcore (hcube a₀ ha₀))
    ·
      have hle : (⨆ y' ∈ X₀, ⨆ (_ : J.map (MulAut.conj y').toMonoidHom ≠
          J.map (MulAut.conj (π h)).toMonoidHom), J.map (MulAut.conj y').toMonoidHom) ≤
          fixMod O (π t₀) := by
        refine iSup₂_le fun y' hy' => iSup_le fun hne => ?_
        intro b hb
        have hbD := hJyD y' hy' hb
        refine mem_fixMod.mpr ⟨hDO hbD, ?_⟩
        obtain ⟨h', hh', rfl⟩ := hX₀mem y' hy'
        have hD' : π t₀ * b * (π t₀)⁻¹ * b⁻¹ ∈ D :=
          mul_mem ((mem_normalizer_iff.mp htD _).mp hbD) (inv_mem hbD)
        rw [hconj h'] at hb
        rw [hconj h', hconj h] at hne
        have hne' : (oUpperTwo I₀).map (MulAut.conj (h : G)).toMonoidHom ≠
            (oUpperTwo I₀).map (MulAut.conj (h' : G)).toMonoidHom := fun he => hne (by rw [he])
        obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
        have hb'I : (b' : G) ∈ I₀.map (MulAut.conj (h' : G)).toMonoidHom :=
          map_mono (oUpperTwo_le_self I₀) (Subgroup.mem_subgroupOf.mp hb')
        have e2 : π (t₀ * b' * t₀⁻¹ * b'⁻¹) = π t₀ * π b' * (π t₀)⁻¹ * (π b')⁻¹ := by
          simp only [map_mul, map_inv]
        rw [← e2] at hD' ⊢
        refine hN₂O _ (hmemN₂ _ ?_) hD'
        have e : ((t₀ * b' * t₀⁻¹ * b'⁻¹ : ↥H) : G) = ⁅(t₀ : G), (b' : G)⁆ := by
          simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
        rw [e]
        exact hB _ hh _ hh' hne' (commutator_mem_commutator ht₀I hb'I)
      exact fun b hb => (mem_fixMod.mp (hle hb)).2
  exact SolvThreeDirectCond.of_indep X₀ J D O rfl rfl hcomm hind

end Conjugates

end SolvDirectCfg

variable (G : Type) [Group G] [Finite G]

open SolvDirectCfg in
theorem agl81TenThreeSolvDirect_cfg
    (hNoSU : Setting G → ∀ (P : Sylow 3 G) (M H Q : Subgroup G)
      (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
      AGL81CfgData 3 P M H Q K → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      ∀ I₀ ∈ cZero (H ⊓ L), IsSymThreeOrSUThreeTwo (↥I₀ ⧸ CFSG.pCore 2 ↥I₀) →
        Nonempty (↥I₀ ⧸ CFSG.pCore 2 ↥I₀ ≃* Equiv.Perm (Fin 3)))
    (hBlock : Setting G → ∀ (P : Sylow 3 G) (M H Q : Subgroup G)
      (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
      AGL81CfgData 3 P M H Q K → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      ∀ I₁ ∈ cZero (H ⊓ L), ∀ I₂ ∈ cZero (H ⊓ L),
        Nonempty (↥I₁ ⧸ CFSG.pCore 2 ↥I₁ ≃* Equiv.Perm (Fin 3)) →
        Nonempty (↥I₂ ⧸ CFSG.pCore 2 ↥I₂ ≃* Equiv.Perm (Fin 3)) →
        CFSG.ComponentClassification.AS76b.oUpperTwo I₁ ≠
          CFSG.ComponentClassification.AS76b.oUpperTwo I₂ →
        ⁅I₁, I₂⁆ ≤ pCoreOf 2 (H ⊓ L)) :
    Setting G → ∀ (P : Sylow 3 G) (M H Q : Subgroup G)
      (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
      AGL81CfgData 3 P M H Q K → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      ∀ I₀ ∈ cZero (H ⊓ L), IsSymThreeOrSUThreeTwo (↥I₀ ⧸ CFSG.pCore 2 ↥I₀) →
        SolvThreeDirectCond (d1X0 3 M H)
          (((CFSG.ComponentClassification.AS76b.oUpperTwo I₀).subgroupOf H).map
            (QuotientGroup.mk' (primeComplementCore (G := H) 3))) := by
  intro hS P M H Q K hcfg L hL I₀ hI₀ hshape
  have hI₀' : IsCZeroMember (H ⊓ L) I₀ := hI₀
  have hS3 := hNoSU hS P M H Q K hcfg L hL I₀ hI₀ hshape
  have hHLM : CFSG.Open.IsSubnormal (H ⊓ L) (H ⊓ M) := by
    have h := hL.subnormal.inf H
    rwa [inf_comm L H, inf_comm M H] at h
  have hA : ∀ g ∈ H ⊓ M, oUpperTwo I₀ ≠ (oUpperTwo I₀).map (MulAut.conj g).toMonoidHom →
      ⁅I₀, I₀.map (MulAut.conj g).toMonoidHom⁆ ≤ pCoreOf 2 (H ⊓ M) :=
    fun g hg hne => commutator_map_conj_le hL.toIsTwoPrimeComponent hI₀' hS3
      (fun I₂ hI₂ hS3₂ hne₂ => hBlock hS P M H Q K hcfg L hL I₀ hI₀ I₂ hI₂ hS3 hS3₂ hne₂) hg hne
  exact solvThreeDirectCond_of (primeComplementCore (G := H) 3)
    (hI₀'.le.trans (inf_le_inf_left H hL.le))
    (cfsg_subnormal_pCoreOf_le 2 (hI₀'.subnormal.trans hHLM)) (exists_inv_mod hS3)
    (IsCZeroMember.cube_mem kFactSUThreeTwoShape_holds hshape) (commutator_map_conj_conj_le hA)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
