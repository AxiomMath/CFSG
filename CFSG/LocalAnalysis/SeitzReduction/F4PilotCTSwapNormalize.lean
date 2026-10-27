module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCTSwap

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Quasithin (perfectCore)

local instance f4PilotCTSwapNormalizeNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section Abstract

variable {G : Type*} [Group G] {A : Subgroup G} {t : G}

theorem commute_of_map_conj_le_centralizer
    (hcomm : A.map (MulAut.conj t).toMonoidHom ≤ centralizer (A : Set G)) :
    ∀ a ∈ A, ∀ b ∈ A.map (MulAut.conj t).toMonoidHom, Commute a b :=
  fun a ha _ hb => mem_centralizer_iff.1 (hcomm hb) a ha

@[expose] def swapDiagHom (hcomm : A.map (MulAut.conj t).toMonoidHom ≤ centralizer (A : Set G)) :
    A →* G where
  toFun a := a * (t * a * t⁻¹)
  map_one' := by simp
  map_mul' a b := by
    have hc : (b : G) * (t * a * t⁻¹) = t * a * t⁻¹ * b :=
      commute_of_map_conj_le_centralizer hcomm b b.2 _ ⟨a, a.2, rfl⟩
    simp only [Subgroup.coe_mul]
    calc (a : G) * b * (t * (a * b) * t⁻¹) = a * (b * (t * a * t⁻¹)) * (t * b * t⁻¹) := by group
      _ = a * (t * a * t⁻¹ * b) * (t * b * t⁻¹) := by rw [hc]
      _ = a * (t * a * t⁻¹) * (b * (t * b * t⁻¹)) := by group

theorem swapDiagHom_apply (hcomm : A.map (MulAut.conj t).toMonoidHom ≤ centralizer (A : Set G))
    (a : A) : swapDiagHom hcomm a = a * (t * a * t⁻¹) :=
  rfl

theorem swapDiagHom_injective
    (hcomm : A.map (MulAut.conj t).toMonoidHom ≤ centralizer (A : Set G))
    (hdisj : A ⊓ A.map (MulAut.conj t).toMonoidHom = ⊥) :
    Function.Injective (swapDiagHom hcomm) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  rw [swapDiagHom_apply] at ha
  have h1 : (a : G) = t * (a : G)⁻¹ * t⁻¹ :=
    calc (a : G) = (t * a * t⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left ha
      _ = t * (a : G)⁻¹ * t⁻¹ := by group
  have h2 : (a : G) ∈ A ⊓ A.map (MulAut.conj t).toMonoidHom :=
    ⟨a.2, ⟨(a : G)⁻¹, inv_mem a.2, h1.symm⟩⟩
  rw [hdisj] at h2
  exact Subtype.ext (Subgroup.mem_bot.1 h2)

theorem eq_of_mul_eq_mul_of_swap
    (hcomm : A.map (MulAut.conj t).toMonoidHom ≤ centralizer (A : Set G))
    (hdisj : A ⊓ A.map (MulAut.conj t).toMonoidHom = ⊥) {a a₁ b b₁ : G} (ha : a ∈ A)
    (ha₁ : a₁ ∈ A) (hb : b ∈ A.map (MulAut.conj t).toMonoidHom)
    (hb₁ : b₁ ∈ A.map (MulAut.conj t).toMonoidHom) (h : a * b = a₁ * b₁) : a = a₁ := by
  have hinj := injective_noncommCoprod_subtype (commute_of_map_conj_le_centralizer hcomm) hdisj
  have h' := @hinj (⟨a, ha⟩, ⟨b, hb⟩) (⟨a₁, ha₁⟩, ⟨b₁, hb₁⟩) h
  exact congrArg (fun p : A × A.map (MulAut.conj t).toMonoidHom => (p.1 : G)) h'

theorem range_swapDiagHom (hcomm : A.map (MulAut.conj t).toMonoidHom ≤ centralizer (A : Set G))
    (htt : t * t = 1) (hdisj : A ⊓ A.map (MulAut.conj t).toMonoidHom = ⊥) :
    (swapDiagHom hcomm).range =
      (A ⊔ A.map (MulAut.conj t).toMonoidHom) ⊓ centralizer ({t} : Set G) := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have htt' : ∀ x : G, t * (t * x * t⁻¹) * t⁻¹ = x := fun x => by
    calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
      _ = x := by rw [htt]; group
  ext g
  constructor
  · rintro ⟨a, rfl⟩
    refine mem_inf.2 ⟨mul_mem (mem_sup_left a.2) (mem_sup_right ⟨a, a.2, rfl⟩), ?_⟩
    rw [mem_centralizer_singleton_iff, swapDiagHom_apply]
    have hc : (a : G) * (t * a * t⁻¹) = t * a * t⁻¹ * a :=
      commute_of_map_conj_le_centralizer hcomm a a.2 _ ⟨a, a.2, rfl⟩
    have h1 : t * ((a : G) * (t * a * t⁻¹)) * t⁻¹ = (a : G) * (t * a * t⁻¹) := by
      calc t * ((a : G) * (t * a * t⁻¹)) * t⁻¹ = (t * a * t⁻¹) * (t * (t * a * t⁻¹) * t⁻¹) := by
            group
        _ = (a : G) * (t * a * t⁻¹) := by rw [htt', hc]
    calc (a : G) * (t * a * t⁻¹) * t = t * ((a : G) * (t * a * t⁻¹)) * t⁻¹ * t := by rw [h1]
      _ = t * ((a : G) * (t * a * t⁻¹)) := by group
  · intro hgm
    obtain ⟨hg, hgt⟩ := mem_inf.1 hgm
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      exists_mul_eq_of_mem_sup_of_commute (commute_of_map_conj_le_centralizer hcomm) hg
    obtain ⟨a', ha', rfl⟩ := hb
    rw [mem_centralizer_singleton_iff] at hgt
    have hgt' : a * (t * a' * t⁻¹) * t = t * (a * (t * a' * t⁻¹)) := hgt
    have h1 : t * (a * (t * a' * t⁻¹)) * t⁻¹ = a * (t * a' * t⁻¹) := by
      rw [← hgt']
      group
    have hc : a' * (t * a * t⁻¹) = t * a * t⁻¹ * a' :=
      commute_of_map_conj_le_centralizer hcomm a' ha' _ ⟨a, ha, rfl⟩
    have h2 : t * (a * (t * a' * t⁻¹)) * t⁻¹ = a' * (t * a * t⁻¹) := by
      calc t * (a * (t * a' * t⁻¹)) * t⁻¹ = (t * a * t⁻¹) * (t * (t * a' * t⁻¹) * t⁻¹) := by group
        _ = a' * (t * a * t⁻¹) := by rw [htt', hc]
    have h3 : a * (t * a' * t⁻¹) = a' * (t * a * t⁻¹) := h1.symm.trans h2
    have h4 : a = a' := eq_of_mul_eq_mul_of_swap hcomm hdisj ha ha' ⟨a', ha', rfl⟩
      ⟨a, ha, rfl⟩ h3
    subst h4
    exact ⟨⟨a, ha⟩, rfl⟩

end Abstract

section Normalize


variable {K : Type} [Field K] {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .F4 K} {t : G}

theorem nonempty_swapNeighbourIso (N : AmalgamNeighbour) {Kc : Subgroup G} (htt : t * t = 1)
    (hcomm : Kc.map (MulAut.conj t).toMonoidHom ≤ centralizer (Kc : Set G))
    (hdisj : Kc ⊓ Kc.map (MulAut.conj t).toMonoidHom = ⊥)
    (hE : Kc ⊔ Kc.map (MulAut.conj t).toMonoidHom = neighbourCore e N)
    (hfix : neighbourCore e N ⊓ centralizer ({t} : Set G) =
      modelToG e ((N.levi K).map (adjointGroup .F4 K).subtype)) :
    Nonempty (SwapNeighbourIso e t N) := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  obtain ⟨ε, hε⟩ : ∃ ε : N.levi K →* G, ∀ x, ε x = ((e.symm (x : adjointGroup .F4 K) : L) : G) :=
    ⟨L.subtype.comp (e.symm.toMonoidHom.comp (N.levi K).subtype), fun x => rfl⟩
  have hεinj : Function.Injective ε := by
    intro x y hxy
    rw [hε, hε] at hxy
    exact Subtype.ext (e.symm.injective (Subtype.ext hxy))
  have hεrange : ε.range = modelToG e ((N.levi K).map (adjointGroup .F4 K).subtype) := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      rw [hε]
      exact symm_mem_modelToG e ⟨x, x.2, rfl⟩
    · intro hg
      obtain ⟨x, ⟨y, hy, hyx⟩, rfl⟩ := (mem_modelToG e).1 hg
      have hxy : x = y := Subtype.ext hyx.symm
      subst hxy
      exact ⟨⟨x, hy⟩, hε _⟩
  have hδrange : (swapDiagHom hcomm).range = ε.range := by
    rw [range_swapDiagHom hcomm htt hdisj, hE, hfix, hεrange]
  have hδinj := swapDiagHom_injective hcomm hdisj
  obtain ⟨lam, hlam⟩ : ∃ lam : N.levi K ≃* Kc, ∀ x, swapDiagHom hcomm (lam x) = ε x := by
    refine ⟨(MonoidHom.ofInjective hεinj).trans ((MulEquiv.subgroupCongr hδrange.symm).trans
      (MonoidHom.ofInjective hδinj).symm), fun x => ?_⟩
    have h1 := congrArg Subtype.val ((MonoidHom.ofInjective hδinj).apply_symm_apply
      ((MulEquiv.subgroupCongr hδrange.symm) (MonoidHom.ofInjective hεinj x)))
    rw [MonoidHom.ofInjective_apply, MulEquiv.subgroupCongr_apply,
      MonoidHom.ofInjective_apply] at h1
    exact h1
  have hc : ∀ x y : N.levi K, Commute ((Kc.subtype.comp lam.toMonoidHom) x)
      (((MulAut.conj t).toMonoidHom.comp (Kc.subtype.comp lam.toMonoidHom)) y) := fun x y =>
    commute_of_map_conj_le_centralizer hcomm _ (lam x).2 _ ⟨_, (lam y).2, rfl⟩
  set Φ₀ := (Kc.subtype.comp lam.toMonoidHom).noncommCoprod
    ((MulAut.conj t).toMonoidHom.comp (Kc.subtype.comp lam.toMonoidHom)) hc with hΦ₀
  have hΦ₀apply : ∀ x y, Φ₀ (x, y) = (lam x : G) * (t * (lam y : G) * t⁻¹) := fun x y => rfl
  have hrange1 : (Kc.subtype.comp lam.toMonoidHom).range = Kc := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 lam.surjective, ← MonoidHom.range_eq_map,
      range_subtype]
  have hrange2 : ((MulAut.conj t).toMonoidHom.comp (Kc.subtype.comp lam.toMonoidHom)).range =
      Kc.map (MulAut.conj t).toMonoidHom := by
    rw [MonoidHom.range_comp, hrange1]
  have hinj : Function.Injective Φ₀ := by
    rw [hΦ₀, MonoidHom.noncommCoprod_injective]
    refine ⟨Subtype.val_injective.comp lam.injective,
      (MulAut.conj t).injective.comp (Subtype.val_injective.comp lam.injective), ?_⟩
    rw [hrange1, hrange2]
    exact disjoint_iff.2 hdisj
  have hrange : Φ₀.range = neighbourCore e N := by
    rw [hΦ₀, MonoidHom.noncommCoprod_range, hrange1, hrange2, hE]
  refine ⟨⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange), fun x => ?_,
    fun x y => ?_⟩⟩
  · rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply,
      hΦ₀apply, ← hε, ← hlam, swapDiagHom_apply]
  · rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
      MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply, MonoidHom.ofInjective_apply,
      hΦ₀apply, hΦ₀apply]
    have hcy : (lam y : G) * (t * (lam x : G) * t⁻¹) = t * (lam x : G) * t⁻¹ * (lam y : G) :=
      commute_of_map_conj_le_centralizer hcomm _ (lam y).2 _ ⟨_, (lam x).2, rfl⟩
    calc t * ((lam x : G) * (t * (lam y : G) * t⁻¹)) * t⁻¹ =
        (t * (lam x : G) * t⁻¹) * ((t * t) * (lam y : G) * (t * t)⁻¹) := by group
      _ = (lam y : G) * (t * (lam x : G) * t⁻¹) := by rw [htt, hcy]; group

theorem nonempty_swapNeighbourIso_of_perfectCore (N : AmalgamNeighbour)
    {Kc : Subgroup G} (htt : t * t = 1) (hKperf : ⁅Kc, Kc⁆ = Kc)
    (hcomm : Kc.map (MulAut.conj t).toMonoidHom ≤ centralizer (Kc : Set G))
    (hdisj : Kc ⊓ Kc.map (MulAut.conj t).toMonoidHom = ⊥)
    (hE : Kc ⊔ Kc.map (MulAut.conj t).toMonoidHom = neighbourCore e N)
    (hfix : perfectCore (neighbourCore e N ⊓ centralizer ({t} : Set G)) =
      modelToG e ((N.levi K).map (adjointGroup .F4 K).subtype)) :
    Nonempty (SwapNeighbourIso e t N) := by
  refine nonempty_swapNeighbourIso N htt hcomm hdisj hE ?_
  have htop : ⁅(⊤ : Subgroup Kc), (⊤ : Subgroup Kc)⁆ = ⊤ := by
    apply map_injective Kc.subtype_injective
    rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype, hKperf]
  have hperf : ⁅(swapDiagHom hcomm).range, (swapDiagHom hcomm).range⁆ =
      (swapDiagHom hcomm).range := by
    rw [MonoidHom.range_eq_map, ← map_commutator, htop]
  rw [← hfix, ← hE, ← range_swapDiagHom hcomm htt hdisj]
  exact (CFSG.Quasithin.perfectCore_eq_self_of_perfect hperf).symm

end Normalize

section Endgame


variable {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type} [Group G] [Finite G]
  {L : Subgroup G} {e : L ≃* adjointGroup .F4 K} {t : G}

theorem exists_swapFactors_of_decomposition (htL : t ∈ centralizer (L : Set G)) (htt : t * t = 1)
    (hq : 4 ≤ Nat.card K) {KX KY : Subgroup G}
    (hcX : KX.map (MulAut.conj t).toMonoidHom ≤ centralizer (KX : Set G))
    (hdX : KX ⊓ KX.map (MulAut.conj t).toMonoidHom = ⊥)
    (hEX : KX ⊔ KX.map (MulAut.conj t).toMonoidHom = neighbourCore e .X)
    (hfX : neighbourCore e .X ⊓ centralizer ({t} : Set G) =
      modelToG e ((AmalgamNeighbour.X.levi K).map (adjointGroup .F4 K).subtype))
    (hcY : KY.map (MulAut.conj t).toMonoidHom ≤ centralizer (KY : Set G))
    (hdY : KY ⊓ KY.map (MulAut.conj t).toMonoidHom = ⊥)
    (hEY : KY ⊔ KY.map (MulAut.conj t).toMonoidHom = neighbourCore e .Y)
    (hfY : neighbourCore e .Y ⊓ centralizer ({t} : Set G) =
      modelToG e ((AmalgamNeighbour.Y.levi K).map (adjointGroup .F4 K).subtype)) :
    ∃ (G₁ G₂ : Subgroup G) (ε : G₁ ≃* adjointGroup .F4 K),
      G₂ ≤ centralizer (G₁ : Set G) ∧ G₁.map (MulAut.conj t).toMonoidHom = G₂ ∧
      G₁ ⊔ G₂ = ⨆ J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2}, pieceCore e J.1 ∧
      ∀ g : G₁, (g : G) * (t * g * t⁻¹) = ((e.symm (ε g) : L) : G) := by
  obtain ⟨hX⟩ := nonempty_swapNeighbourIso .X htt hcX hdX hEX hfX
  obtain ⟨hY⟩ := nonempty_swapNeighbourIso .Y htt hcY hdY hEY hfY
  exact exists_swapFactors hX hY (hX.toX' (commute_symm_n1242_of_mem_centralizer htL)) hq

theorem false_of_simple_of_swapDecomposition [IsSimpleGroup G] (htL : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    {KX KY : Subgroup G}
    (hcX : KX.map (MulAut.conj t).toMonoidHom ≤ centralizer (KX : Set G))
    (hdX : KX ⊓ KX.map (MulAut.conj t).toMonoidHom = ⊥)
    (hEX : KX ⊔ KX.map (MulAut.conj t).toMonoidHom = neighbourCore e .X)
    (hfX : neighbourCore e .X ⊓ centralizer ({t} : Set G) =
      modelToG e ((AmalgamNeighbour.X.levi K).map (adjointGroup .F4 K).subtype))
    (hcY : KY.map (MulAut.conj t).toMonoidHom ≤ centralizer (KY : Set G))
    (hdY : KY ⊓ KY.map (MulAut.conj t).toMonoidHom = ⊥)
    (hEY : KY ⊔ KY.map (MulAut.conj t).toMonoidHom = neighbourCore e .Y)
    (hfY : neighbourCore e .Y ⊓ centralizer ({t} : Set G) =
      modelToG e ((AmalgamNeighbour.Y.levi K).map (adjointGroup .F4 K).subtype))
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer ((⨆ J : {J : Finset (Fin (Tag.rank .F4)) //
        J.card ≤ 2}, pieceCore e J.1 : Subgroup G) : Set G) →
      g ∈ normalizer ((⨆ J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2},
        pieceCore e J.1 : Subgroup G) : Set G)) : False := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨hX⟩ := nonempty_swapNeighbourIso .X htt hcX hdX hEX hfX
  obtain ⟨hY⟩ := nonempty_swapNeighbourIso .Y htt hcY hdY hEY hfY
  exact false_of_simple_of_swapRow hX hY (hX.toX' (commute_symm_n1242_of_mem_centralizer htL)) hq
    ht hf hK huniq

end Endgame

end CFSG.SeitzReduction.F4Pilot
