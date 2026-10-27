module

public import CFSG.LocalAnalysis.ComponentClassification.Components

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup

section Perfect

variable {H : Type*} [Group H]

@[expose] def perfCore (N : Subgroup H) : Subgroup H :=
  sSup {K : Subgroup H | K ≤ N ∧ ⁅K, K⁆ = K}

theorem perfCore_le (N : Subgroup H) : perfCore N ≤ N := sSup_le fun _ hK => hK.1

theorem le_perfCore {N K : Subgroup H} (hKN : K ≤ N) (hK : ⁅K, K⁆ = K) : K ≤ perfCore N :=
  le_sSup ⟨hKN, hK⟩

theorem commutator_perfCore (N : Subgroup H) : ⁅perfCore N, perfCore N⁆ = perfCore N := by
  refine le_antisymm ?_ (sSup_le fun K hK => ?_)
  · simpa only [sup_idem] using Subgroup.commutator_le_sup (perfCore N) (perfCore N)
  · rw [← hK.2]
    exact Subgroup.commutator_mono (le_sSup hK) (le_sSup hK)

theorem map_perfCore_comap_of_subnormal {Q : Type*} [Finite H] [Group Q] (f : H →* Q)
    (hf : Function.Surjective f) (Lb : Subgroup Q) (hsub : Lb.IsSubnormal)
    (hLb : ⁅Lb, Lb⁆ = Lb) : (perfCore (Lb.comap f)).map f = Lb := by
  have : Group.IsPerfect Lb := Subgroup.isPerfect_iff.mpr hLb
  obtain ⟨lift, -, hmap, hperf, -⟩ :=
    CFSG.ComponentClassification.Components.perfect_subnormal_lift f hf Lb hsub
  have hl : ⁅lift, lift⁆ = lift := Subgroup.isPerfect_iff.mp ⟨hperf⟩
  have hle : lift ≤ Lb.comap f := by rw [← Subgroup.map_le_iff_le_comap, hmap]
  refine le_antisymm ((Subgroup.map_mono (perfCore_le _)).trans (Subgroup.map_comap_le f Lb)) ?_
  calc Lb = lift.map f := hmap.symm
    _ ≤ (perfCore (Lb.comap f)).map f := Subgroup.map_mono (le_perfCore hle hl)

theorem conj_mem_perfCore {N : Subgroup H} {h : H} (hh : h ∈ normalizer (N : Set H)) {x : H}
    (hx : x ∈ perfCore N) : h * x * h⁻¹ ∈ perfCore N := by
  have hle : (perfCore N).map (MulAut.conj h).toMonoidHom ≤ N := by
    rintro _ ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff.mp hh y).mp (perfCore_le N hy)
  have hperf : ⁅(perfCore N).map (MulAut.conj h).toMonoidHom,
      (perfCore N).map (MulAut.conj h).toMonoidHom⁆ =
        (perfCore N).map (MulAut.conj h).toMonoidHom := by
    rw [← Subgroup.map_commutator, commutator_perfCore]
  exact le_perfCore hle hperf ⟨x, hx, rfl⟩

theorem mem_normalizer_perfCore {N : Subgroup H} {h : H} (hh : h ∈ normalizer (N : Set H)) :
    h ∈ normalizer ((perfCore N : Subgroup H) : Set H) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · exact conj_mem_perfCore hh
  · intro hx
    have hh' : h⁻¹ ∈ normalizer (N : Set H) := (normalizer (N : Set H)).inv_mem hh
    have := conj_mem_perfCore hh' hx
    simpa [mul_assoc] using this

theorem perfCore_isSubnormal {N : Subgroup H} (hN : N.IsSubnormal) :
    (perfCore N).IsSubnormal := by
  refine Subgroup.IsSubnormal.step (perfCore N) N (perfCore_le N) hN ?_
  refine ⟨fun x hx n => ?_⟩
  have hxP : (x : H) ∈ perfCore N := hx
  have hnN : (n : H) ∈ normalizer (N : Set H) := Subgroup.le_normalizer n.2
  exact conj_mem_perfCore hnN hxP

theorem le_of_isPerfect_of_le_sup {K D X : Subgroup H} [D.Normal] (hD : Group.IsSolvable ↥D)
    (hKD : D ≤ normalizer (K : Set H)) (hX : ⁅X, X⁆ = X) (hXle : X ≤ D ⊔ K) : X ≤ K := by
  set N := D ⊔ K with hN
  have hKn : (K.subgroupOf N).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hKD
  let χ : ↥N →* ↥N ⧸ K.subgroupOf N := QuotientGroup.mk' (K.subgroupOf N)
  let ψ : ↥D →* ↥N ⧸ K.subgroupOf N := χ.comp (Subgroup.inclusion le_sup_left)
  have hψ : Function.Surjective ψ := by
    intro q
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨y, hy, z, hz, hyz⟩ := (Subgroup.mem_sup_of_normal_left (s := D) (t := K)).mp n.2
    refine ⟨⟨y, hy⟩, ?_⟩
    show (QuotientGroup.mk (Subgroup.inclusion le_sup_left ⟨y, hy⟩) : ↥N ⧸ K.subgroupOf N) =
      QuotientGroup.mk n
    apply QuotientGroup.eq.mpr
    show (y⁻¹ * n.1 : H) ∈ K
    rw [← hyz]
    simpa using hz
  have hsolQ : Group.IsSolvable (↥N ⧸ K.subgroupOf N) := by
    have := hD
    exact Group.isSolvable_of_surjective hψ
  have hXperf : Group.IsPerfect ↥X := Subgroup.isPerfect_iff.mpr hX
  let φ : ↥X →* ↥N ⧸ K.subgroupOf N := χ.comp (Subgroup.inclusion hXle)
  intro x hx
  have hφ : φ ⟨x, hx⟩ = 1 := by
    by_contra hne
    have hnt : Nontrivial ↥φ.range := ⟨⟨⟨φ ⟨x, hx⟩, ⟨_, rfl⟩⟩, 1, fun h => hne
      (congrArg Subtype.val h)⟩⟩
    have hperf : Group.IsPerfect ↥φ.range := Group.IsPerfect.range φ
    have hsolR : Group.IsSolvable ↥φ.range := by
      have := hsolQ
      infer_instance
    exact Group.IsPerfect.not_isSolvable ↥φ.range hsolR
  have : (⟨x, hXle hx⟩ : ↥N) ∈ K.subgroupOf N := (QuotientGroup.eq_one_iff _).mp hφ
  exact this

end Perfect

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
