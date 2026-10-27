module

public import CFSG.GH74.GLS.C3.Layer1.Th2P61L2

public section

namespace CFSG.GH74.Generic.BProg.B3.S3KG

open Subgroup CFSG CFSG.GorensteinWalter CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Proofs2
  CFSG.GH74.GLS.Th2.Bal CFSG.Assembly.Dichotomy CFSG.GH74.GLS.Th2.Obs
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] {K : Type} [Group K]
  [Finite K]

omit [Finite G] [Finite F] [Finite K] in
theorem comp_barAct_eq_one_iff {J : Subgroup G} {ψ : MulAut (kBar J) →* MulAut K}
    (hψ : Function.Injective ψ) (m : ↥(normalizer (J : Set G))) :
    ψ.comp (barAct J) m = 1 ↔ (m : G) ∈ centralizerSection J (pPrimeCoreOf 2 J) := by
  rw [MonoidHom.comp_apply, map_eq_one_iff ψ hψ, barAct_eq_one_iff]

theorem obs_innDiag_comp
    {B : Subgroup G} {a : G} {J D : Subgroup G} (h : ObsData B a J D)
    (hB : CFSG.IsElementaryAbelian 2 ↥B) (hF : L2Field F) (e : K ≃* L2 F)
    {ψ : MulAut (kBar J) →* MulAut K} (hψ : Function.Injective ψ)
    (hInn : innAut K ≤ (ψ.comp (barAct J)).range) {d : G} (hd : d ∈ D) :
    ψ.comp (barAct J) ⟨d, h.D_norm d hd⟩ ∈ innDiagSub e := by
  classical
  obtain ⟨-, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hB
  by_contra hnot
  set M : Subgroup G := normalizer (J : Set G) with hM
  set ρ : ↥M →* MulAut K := ψ.comp (barAct J) with hρ
  have hd1 : d ≠ 1 := by
    rintro rfl
    apply hnot
    have : (⟨1, h.D_norm 1 hd⟩ : ↥M) = 1 := rfl
    rw [this, map_one]
    exact (innDiagSub e).one_mem
  set Z : Subgroup (MulAut K) := ρ.range with hZ
  let φ : ↥M →* ↥Z := ρ.rangeRestrict
  have hφ : Function.Surjective φ := MonoidHom.rangeRestrict_surjective ρ
  obtain ⟨x, hxX, hxmove⟩ := h.X_move
  have hxN : x ∈ M := h.X_norm x hxX
  have hdM : d ∈ M := h.D_norm d hd
  have hd2 : d * d = 1 := hBsq d (h.D_le hd)
  have hmem := map_mem_involutionOddCore φ hφ hdM hd2 hxN (h.mem_core hB hxX hd hd1)
  have hy2 : ρ ⟨d, hdM⟩ * ρ ⟨d, hdM⟩ = 1 := by
    rw [← map_mul]
    have : (⟨d, hdM⟩ : ↥M) * ⟨d, hdM⟩ = 1 := Subtype.ext hd2
    rw [this, map_one]
  have hbot : involutionOddCore (φ ⟨d, hdM⟩) = ⊥ := by
    refine involutionOddCore_eq_bot_of_pPrimeCoreOf Z (φ ⟨d, hdM⟩) ?_
    exact pPrimeCoreOf_outer_involution_eq_bot hF e Z hInn (y := ρ ⟨d, hdM⟩) hy2 hnot
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hxmove ((comp_barAct_eq_one_iff hψ _).1 (congrArg Subtype.val hmem))

omit [Finite G] [Finite F] [Finite K] in
theorem card_map_comp {B : Subgroup G} {a : G} {J D : Subgroup G} (h : ObsData B a J D)
    {ψ : MulAut (kBar J) →* MulAut K} (hψ : Function.Injective ψ) :
    Nat.card ((D.subgroupOf (normalizer (J : Set G))).map (ψ.comp (barAct J))) = Nat.card D := by
  set M : Subgroup G := normalizer (J : Set G) with hM
  have hDM : D ≤ M := fun d hd => h.D_norm d hd
  have hbij : Function.Bijective ((ψ.comp (barAct J)).subgroupMap (D.subgroupOf M)) := by
    refine ⟨?_, (ψ.comp (barAct J)).subgroupMap_surjective _⟩
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro m hm
    have h1 : ψ.comp (barAct J) (m : ↥M) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hm)
    have hmD : ((m : ↥M) : G) ∈ D := Subgroup.mem_subgroupOf.mp m.2
    by_contra hne
    have hm1 : ((m : ↥M) : G) ≠ 1 := by
      intro h1'
      apply hne
      apply Subtype.ext
      apply Subtype.ext
      exact h1'
    exact h.D_faith _ hmD hm1 ((comp_barAct_eq_one_iff hψ _).1 h1)
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij)]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDM).toEquiv

theorem obs_four_comp
    {B : Subgroup G} {a : G} {J D : Subgroup G} (h : ObsData B a J D)
    (hB : CFSG.IsElementaryAbelian 2 ↥B) (hF : L2Field F) (e : K ≃* L2 F)
    {ψ : MulAut (kBar J) →* MulAut K} (hψ : Function.Injective ψ)
    (hInn : innAut K ≤ (ψ.comp (barAct J)).range) :
    IsFourSubgroup ((D.subgroupOf (normalizer (J : Set G))).map (ψ.comp (barAct J))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hB
  set M : Subgroup G := normalizer (J : Set G) with hM
  set U : Subgroup (MulAut K) := (D.subgroupOf M).map (ψ.comp (barAct J)) with hU
  have hUD : U ≤ innDiagSub e := by
    rintro _ ⟨m, hm, rfl⟩
    exact obs_innDiag_comp h hB hF e hψ hInn (Subgroup.mem_subgroupOf.mp hm)
  have hUsq : ∀ x ∈ U, x * x = 1 := by
    rintro _ ⟨m, hm, rfl⟩
    rw [← map_mul]
    have : m * m = 1 := Subtype.ext (hBsq m (h.D_le (Subgroup.mem_subgroupOf.mp hm)))
    rw [this, map_one]
  have hUc : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := by
    rintro _ ⟨m, hm, rfl⟩ _ ⟨n, hn, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hBc _ (h.D_le (Subgroup.mem_subgroupOf.mp hm)) _ (h.D_le (Subgroup.mem_subgroupOf.mp hn))
  have hUel : CFSG.IsElementaryAbelian 2 ↥U := isElementaryAbelian_two_of_sq U hUsq
  have hU2 : IsPGroup 2 ↥U := CFSG.IsElementaryAbelian.isPGroup 2 _
  obtain ⟨T', hT'⟩ := hU2.exists_le_sylow
  have hle : Nat.card ↥U ≤ 4 := card_le_four_of_le_inf e hF T' U hT' hUD hUc hUsq
  have hge : 4 ≤ Nat.card ↥U := by
    rw [hU, card_map_comp h hψ]
    exact h.D_card
  exact ⟨hUel, le_antisymm hle hge⟩

theorem obs_not_B_comp
    {B : Subgroup G} {a : G} {J D : Subgroup G} (h : ObsData B a J D)
    (hB : CFSG.IsElementaryAbelian 2 ↥B) (hBN : ∀ g ∈ B, g ∈ normalizer (J : Set G))
    (hF : L2Field F) (e : K ≃* L2 F) {ψ : MulAut (kBar J) →* MulAut K}
    (hψ : Function.Injective ψ) (hInn : innAut K ≤ (ψ.comp (barAct J)).range) : False := by
  classical
  obtain ⟨hBc, -⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hB
  set M : Subgroup G := normalizer (J : Set G) with hM
  obtain ⟨y, β, hy, hβ, hx, -, hnc⟩ := h.exists_noncomm hB hBN
  have hxX : ⁅y, β⁆ ∈ ⁅AG D ⊓ centralizer ({a} : Set G), B⁆ :=
    Subgroup.commutator_mem_commutator hy hβ
  have hU := obs_four_comp h hB hF e hψ hInn
  have hUD : (D.subgroupOf M).map (ψ.comp (barAct J)) ≤ innDiagSub e := by
    rintro _ ⟨m, hm, rfl⟩
    exact obs_innDiag_comp h hB hF e hψ hInn (Subgroup.mem_subgroupOf.mp hm)
  apply hnc
  apply hψ
  rw [map_mul, map_mul]
  refine centralizer_four_comm hF e hUD hU ?_ ?_
  · rintro _ ⟨m, hm, rfl⟩
    have hmD : (m : G) ∈ D := Subgroup.mem_subgroupOf.mp hm
    rw [← MonoidHom.comp_apply, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hBc _ hβ _ (h.D_le hmD)
  · rintro _ ⟨m, hm, rfl⟩
    have hmD : (m : G) ∈ D := Subgroup.mem_subgroupOf.mp hm
    rw [← MonoidHom.comp_apply, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact h.comm_D hB hxX hmD

end CFSG.GH74.Generic.BProg.B3.S3KG
