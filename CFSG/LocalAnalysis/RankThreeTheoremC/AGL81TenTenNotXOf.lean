module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightBridge
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.BlockLift
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3InnerNotQJZeroInV
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenSevenFourL34NoRem
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCGammaTools
public import CFSG.LocalAnalysis.ComponentInitial.EmptyLayerCharTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CfgData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers
open Subgroup

namespace TenTenNotX

variable {G : Type} [Group G]

theorem mul_mem_of_odd {I V : Subgroup G} (hVI : V ≤ normalizer (I : Set G))
    {v x : G} (hv : v ∈ V) (h2 : ∃ a : ℕ, v ^ 2 ^ a = 1) (hx : x ∈ I) {m : ℕ} (hm : Odd m)
    (hvx : (v * x) ^ m = 1) : v * x ∈ I := by
  have key : ∀ n : ℕ, ∃ i ∈ I, (v * x) ^ n = v ^ n * i := by
    intro n
    induction n with
    | zero => exact ⟨1, I.one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨i, hi, he⟩ := ih
      refine ⟨v⁻¹ * i * v * x, I.mul_mem ?_ hx, ?_⟩
      · have hvinv : v⁻¹ ∈ normalizer (I : Set G) := (normalizer (I : Set G)).inv_mem (hVI hv)
        have := (Subgroup.mem_normalizer_iff.mp hvinv i).mp hi
        simpa [inv_inv] using this
      · rw [pow_succ, he, pow_succ]
        group
  obtain ⟨i, hi, he⟩ := key m
  rw [hvx] at he
  have hvm : v ^ m ∈ I := by
    have : v ^ m = i⁻¹ := by
      calc v ^ m = v ^ m * i * i⁻¹ := by group
        _ = i⁻¹ := by rw [← he, one_mul]
    rw [this]
    exact I.inv_mem hi
  obtain ⟨a, ha⟩ := h2
  have hcop : Nat.Coprime m (2 ^ a) :=
    Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hm)
  have hcop' : Nat.Coprime m (orderOf v) :=
    hcop.coprime_dvd_right (orderOf_dvd_of_pow_eq_one ha)
  obtain ⟨c, hc⟩ := exists_pow_eq_self_of_coprime hcop'
  have hvI : v ∈ I := by
    rw [← hc]
    exact I.pow_mem hvm c
  exact I.mul_mem hvI hx

variable [Finite G]

theorem mem_normalizer_of_commutator_mem {I V : Subgroup G}
    (hI : I ≤ closure {x : G | x ∈ I ∧ Odd (orderOf x)}) (hVI : V ≤ normalizer (I : Set G))
    (hV : IsPGroup 2 V) {k : G} (hk : ∀ x ∈ I, k * x * k⁻¹ * x⁻¹ ∈ V) :
    k ∈ normalizer (I : Set G) := by
  have hmap : I.map (MulAut.conj k).toMonoidHom ≤ I := by
    refine (Subgroup.map_mono hI).trans ?_
    rw [MonoidHom.map_closure, closure_le]
    rintro _ ⟨x, ⟨hxI, hxo⟩, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    set v := k * x * k⁻¹ * x⁻¹ with hvdef
    have hvV : v ∈ V := hk x hxI
    obtain ⟨a, ha⟩ := hV ⟨v, hvV⟩
    have h2 : v ^ 2 ^ a = 1 := by
      have := congrArg Subtype.val ha
      simpa using this
    have he : k * x * k⁻¹ = v * x := by rw [hvdef]; group
    rw [he]
    refine mul_mem_of_odd hVI hvV ⟨a, h2⟩ hxI (m := orderOf (k * x * k⁻¹)) ?_ ?_
    · have h := orderOf_injective (MulAut.conj k).toMonoidHom (MulAut.conj k).injective x
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
      rw [h]
      exact hxo
    · rw [← he]
      exact pow_orderOf_eq_one _
  apply TenNineOneThree.mem_normalizer_of_conj_mem
  intro r hr
  exact hmap ⟨r, hr, by simp [MulAut.conj_apply]⟩

end TenTenNotX

variable (G : Type) [Group G] [Finite G]

@[expose] def AGL81TenTenNormICfg : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    AGL81CfgData p P M H Q K → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    ¬ (L.subgroupOf M).Normal → ∀ I₀ ∈ cZero (H ⊓ L),
      normalizer (CFSG.ComponentClassification.AS76b.oUpperTwo I₀ : Set G) ≤ M

@[expose] def AGL81TenFiveXCfg : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    AGL81CfgData p P M H Q K → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    ∀ I₀ ∈ cZero (H ⊓ L),
      CFSG.ComponentClassification.AS76b.oUpperTwo I₀ ≤ d1PlusCore p H K →
      ∀ Y : Subgroup G, RankThreeUC.AGL81C.IsPComponentIn p Y H → ¬ Y ≤ M →
        ∀ y ∈ Y, ∀ x ∈ CFSG.ComponentClassification.AS76b.oUpperTwo I₀,
          y * x * y⁻¹ * x⁻¹ ∈ pCoreOf 2 H

variable {G}

theorem exists_pComponent_not_le_of_cfg {p : ℕ} {P : Sylow p G} {M H Q : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hd : AGL81CfgData p P M H Q K) :
    ∃ Y : Subgroup G, RankThreeUC.AGL81C.IsPComponentIn p Y H ∧ ¬ Y ≤ M := by
  have hK : ¬ d1KBar p M H ≤ d1X0 p M H := hd.kbar ▸ hd.not_le_X0
  have hL : ∃ L, IsComponentOf L ⊤ ∧ ¬ L ≤ d1X0 p M H := by
    by_contra hno
    push Not at hno
    exact hK (iSup₂_le fun L hL => absurd (hno L hL.1) hL.2)
  obtain ⟨L, hLc, hLX⟩ := hL
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p)
  obtain ⟨Y', hY', hYL⟩ := CFSG.LocalAnalysis.ComponentInitial.exists_isPComponent_of_isComponent
    p (isComponent_of_isComponentOf_top'' hLc)
  have hYL' : Y'.map π = L := hYL
  have hYY : (Y'.map H.subtype).subgroupOf H = Y' :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  refine ⟨Y'.map H.subtype, ⟨Subgroup.map_subtype_le _, by rw [hYY]; exact hY'⟩, ?_⟩
  intro hle
  refine hLX ?_
  rw [← hYL']
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y, ⟨y.2, hle ⟨y, hy, rfl⟩⟩, rfl⟩

theorem pCoreOf_le_normalizer_oUpperTwo {M H L I₀ : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hI₀ : I₀ ∈ cZero (H ⊓ L)) (hHM : pCoreOf 2 H ≤ M)
    (hNH : normalizer (pCoreOf 2 H : Set G) = H) :
    pCoreOf 2 H ≤ normalizer (CFSG.ComponentClassification.AS76b.oUpperTwo I₀ : Set G) := by
  set I := CFSG.ComponentClassification.AS76b.oUpperTwo I₀ with hIdef
  have hII₀ : I ≤ I₀ := oUpperTwo_le_self I₀
  have hsub1 : IsSubnormal I I₀ :=
    .step hII₀ ((Subgroup.normal_subgroupOf_iff_le_normalizer hII₀).mpr
      fun n hn => mem_normalizer_oUpperTwo hn) (.refl I₀)
  have hsub2 : IsSubnormal (H ⊓ L) (H ⊓ M) := by
    have h := hL.subnormal.inf H
    rwa [inf_comm L H, inf_comm M H] at h
  have hsub : IsSubnormal I (H ⊓ M) := (hsub1.trans hI₀.subnormal).trans hsub2
  have hIle : I ≤ H ⊓ M := hII₀.trans (hI₀.le.trans (inf_le_inf_left H hL.le))
  have hgen : I ≤ closure {x : G | x ∈ I ∧ Odd (orderOf x)} := by
    have h := NoRem.oUpperTwo_idem I₀
    rw [← hIdef] at h
    calc I = CFSG.ComponentClassification.AS76b.oUpperTwo I := h.symm
      _ ≤ closure {x : G | x ∈ I ∧ Odd (orderOf x)} := le_rfl
  refine CFSG.AGLEmbeddingD2.GN.le_normalizer_of_isSubnormal_of_odd hIle hsub.subgroupOf hgen
    (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 H) hHM) ?_
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
  rw [hNH]
  exact inf_le_left

end CFSG.LocalAnalysis.RankThreeTheoremC
