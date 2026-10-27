module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTLink
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTO2s
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTOFCfg

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

namespace L2V

variable {A : Type} [Group A] [Finite A]

theorem layer_le_normalizer {J : Subgroup A} (hJ : IsComponent J) :
    layer A ≤ normalizer (J : Set A) := by
  refine sSup_le fun J' hJ' => ?_
  rcases LocalCores.distinct_components_commute hJ hJ' with h | h
  · rw [← h]
    exact le_normalizer
  · rw [commutator_comm, commutator_eq_bot_iff_le_centralizer] at h
    exact h.trans (centralizer_le_normalizer _)

theorem actJ_mem_range_conj {J : Subgroup A} (hJ : IsComponent J) {x : A} (hx : x ∈ layer A) :
    actJ J ⟨x, layer_le_normalizer hJ hx⟩ ∈
      (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).range := by
  set R : Subgroup ↥(normalizer (J : Set A)) :=
    (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).range.comap (actJ J) with hR
  have hle : layer A ≤ R.map (normalizer (J : Set A)).subtype := by
    refine sSup_le fun J' hJ' => ?_
    intro y hy
    rcases LocalCores.distinct_components_commute hJ hJ' with h | h
    · subst h
      refine Subgroup.mem_map.mpr ⟨⟨y, le_normalizer hy⟩, ?_, rfl⟩
      rw [hR, mem_comap]
      exact ⟨_, (actJ_of_mem J hy).symm⟩
    · have hJ'C : J' ≤ centralizer (J : Set A) := by
        rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm]
        exact h
      have hyC := hJ'C hy
      refine Subgroup.mem_map.mpr ⟨⟨y, mem_normalizer_of_mem_centralizer hyC⟩, ?_, rfl⟩
      rw [hR, mem_comap, actJ_eq_one_of_mem_centralizer hyC]
      exact one_mem _
  obtain ⟨n, hn, hnx⟩ := Subgroup.mem_map.mp (hle hx)
  have : n = ⟨x, layer_le_normalizer hJ hx⟩ := Subtype.ext hnx
  rw [← this]
  rw [hR, mem_comap] at hn
  exact hn

end L2V

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S T Tstar : Subgroup G} {p : ℕ}
  {H P : Subgroup G} {g : G} {X Y : Subgroup G} {t : G} {q : ℕ} {I Q₁ : Subgroup G}

theorem exists_perfect_image (hd : Data5A2 z k S T Tstar p H P t q I Q₁) {Γ : Type} [Group Γ]
    {K : Subgroup Γ} [K.Normal] {a : Γ} {P' : Subgroup Γ} {J : Subgroup (HBar H)}
    (hq : IsQuasisimple ↥K) (hL : LinkB H P g K a P' J)
    (hI : ¬ barIn H I ≤ centralizer (J : Set (HBar H))) :
    ∃ Xi : Subgroup (↥K ⧸ center ↥K), ⁅Xi, Xi⁆ = Xi ∧ Xi ≠ ⊥ ∧
      Xi ≤ normalizer ((innerPart (K := K) P' : Subgroup (↥K ⧸ center ↥K)) :
        Set (↥K ⧸ center ↥K)) := by
  have hJ : IsComponent J := by
    obtain ⟨Γ₀, _, _, π, ι, hg, -, -, -, -, -, -, -, hJ, -, -⟩ := hL
    exact hJ
  obtain ⟨e, he⟩ := LinkB.exists_equiv hq hL
  set N := normalizer (J : Set (HBar H)) with hN
  set Ib := barIn H I with hIb
  have hIbL : Ib ≤ layer (HBar H) := hd.i.good.layer
  have hIbN : Ib ≤ N := hIbL.trans (L2V.layer_le_normalizer hJ)
  set c := (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)) with hc
  have hZJ : center (↥J ⧸ center ↥J) = ⊥ := center_quot_eq_bot hJ.1
  have hcinj : Function.Injective c := by
    rw [injective_iff_map_eq_one]
    intro y hy
    exact eq_one_of_conj_eq_one hZJ hy
  set A' : Subgroup (MulAut (↥J ⧸ center ↥J)) := (Ib.subgroupOf N).map (actJ J) with hA'
  have hA'le : A' ≤ c.range := by
    rintro _ ⟨n, hn, rfl⟩
    exact L2V.actJ_mem_range_conj hJ (hIbL (mem_subgroupOf.mp hn))
  set Xj : Subgroup (↥J ⧸ center ↥J) := A'.comap c with hXj
  have hXjmap : Xj.map c = A' := map_comap_eq_self hA'le
  have hIbperf : ⁅Ib, Ib⁆ = Ib :=
    OFC.perfect_map (OFC.perfect_subgroupOf hd.i.good.le_H hd.i.perf) _
  have hA'perf : ⁅A', A'⁆ = A' := OFC.perfect_map (OFC.perfect_subgroupOf hIbN hIbperf) _
  have hXjperf : ⁅Xj, Xj⁆ = Xj := by
    apply Subgroup.map_injective hcinj
    rw [Subgroup.map_commutator, hXjmap, hA'perf]
  have hXjne : Xj ≠ ⊥ := by
    intro hbot
    apply hI
    intro x hx
    have hxN := hIbN hx
    have h1 : actJ J ⟨x, hxN⟩ = 1 := by
      have hmem : actJ J ⟨x, hxN⟩ ∈ A' := ⟨⟨x, hxN⟩, mem_subgroupOf.mpr hx, rfl⟩
      rw [← hXjmap, hbot, Subgroup.map_bot] at hmem
      exact hmem
    exact mem_centralizer_of_actJ_eq_one J hJ.1.1 h1
  have key : ∀ y ∈ Xj, ∀ w ∈ innerPart (K := K) P',
      e y * w * (e y)⁻¹ ∈ innerPart (K := K) P' := by
    intro y hy w hw
    obtain ⟨n, hn, hny⟩ := hy
    obtain ⟨h0, hh0, hh0n⟩ := mem_subgroupOf.mp hn
    have hh : QuotientGroup.mk' (pPrimeCore 2 ↥H) h0 ∈ N := hh0n ▸ n.2
    obtain ⟨γ, hγP, -, hγ⟩ := he h0 hh
    have hγN := hγP (hd.i.norm_P (mem_subgroupOf.mp hh0))
    have hconj : e y * w * (e y)⁻¹ = actYHom (K := K) γ w := by
      have h1 := hγ (e.symm w)
      rw [MulEquiv.apply_symm_apply] at h1
      rw [← h1]
      have hn' : (⟨QuotientGroup.mk' (pPrimeCore 2 ↥H) h0, hh⟩ : ↥N) = n := Subtype.ext hh0n
      rw [hn', hny, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    rw [hconj]
    obtain ⟨x, hx, hxw⟩ := mem_innerPart.mp hw
    refine mem_innerPart.mpr ⟨γ * x * γ⁻¹, (mem_normalizer_iff.mp hγN x).mp hx, ?_⟩
    rw [map_mul, map_mul, map_inv, hxw, OFC.mul_conj_inv]
  refine ⟨Xj.map e.toMonoidHom, OFC.perfect_map hXjperf _, ?_, ?_⟩
  · intro hbot
    exact hXjne ((Subgroup.map_eq_bot_iff_of_injective Xj e.injective).mp hbot)
  · rintro _ ⟨y, hy, rfl⟩
    rw [mem_normalizer_iff]
    intro w
    refine ⟨key y hy w, fun hw => ?_⟩
    have h1 := key y⁻¹ (inv_mem hy) _ hw
    simpa [map_inv, mul_assoc] using h1

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
