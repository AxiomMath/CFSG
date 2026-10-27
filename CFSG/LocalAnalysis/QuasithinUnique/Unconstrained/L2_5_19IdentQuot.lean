module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentOrd
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdGen
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabBasic

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
open scoped commutatorElement

section Generic

variable {H Q : Type*} [Group H] [Group Q]

theorem commutator_mul_central {k y z : H} (hz : z ∈ Subgroup.center H) :
    ⁅k * z, y⁆ = ⁅k, y⁆ := by
  have h1 : z * y * z⁻¹ = y := by
    have := Subgroup.mem_center_iff.mp hz y
    rw [← this]
    group
  rw [commutatorElement_def, commutatorElement_def]
  calc k * z * y * (k * z)⁻¹ * y⁻¹ = k * (z * y * z⁻¹) * k⁻¹ * y⁻¹ := by group
    _ = k * y * k⁻¹ * y⁻¹ := by rw [h1]

theorem commutator_mul_central' {k y z : H} (hz : z ∈ Subgroup.center H) :
    ⁅k, y * z⁆ = ⁅k, y⁆ := by
  have h1 : ⁅k, y * z⁆ = (⁅y * z, k⁆)⁻¹ := (commutatorElement_inv (y * z) k).symm
  have h2 : ⁅k, y⁆ = (⁅y, k⁆)⁻¹ := (commutatorElement_inv y k).symm
  rw [h1, h2, commutator_mul_central hz]

theorem le_of_perfect_of_comm_map (π : H →* Q) (hker : π.ker ≤ Subgroup.center H)
    {C K R : Subgroup H} (hRC : R ≤ C) (hR : ⁅R, R⁆ = R) (h : ⁅C.map π, C.map π⁆ ≤ K.map π) :
    R ≤ K := by
  have hRK : ∀ r ∈ R, ∃ k ∈ K, ∃ z ∈ Subgroup.center H, r = k * z := by
    intro r hr
    have h2 : R.map π ≤ K.map π := by
      calc R.map π = (⁅R, R⁆).map π := by rw [hR]
        _ = ⁅R.map π, R.map π⁆ := Subgroup.map_commutator _ _ _
        _ ≤ ⁅C.map π, C.map π⁆ :=
          Subgroup.commutator_mono (Subgroup.map_mono hRC) (Subgroup.map_mono hRC)
        _ ≤ K.map π := h
    obtain ⟨k, hk, hkr⟩ := h2 (Subgroup.mem_map_of_mem π hr)
    refine ⟨k, hk, k⁻¹ * r, hker ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hkr, inv_mul_cancel]
  have hcomm : ⁅R, R⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨k, hk, z, hz, rfl⟩ := hRK a ha
    obtain ⟨k', hk', z', hz', rfl⟩ := hRK b hb
    rw [commutator_mul_central hz, commutator_mul_central' hz']
    rw [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem hk hk') (K.inv_mem hk)) (K.inv_mem hk')
  rw [hR] at hcomm
  exact hcomm

end Generic

section Setting

variable {G : Type} [Group G] {X K : Subgroup G} {t : G}

theorem IdentSetting.eq_perfectResidual_of_map (hs : IdentSetting X K t) {Q : Type*} [Group Q]
    [Finite G] (π : ↥X →* Q) (hker : π.ker ≤ Subgroup.center ↥X)
    (h : ⁅((X ⊓ Subgroup.centralizer ({t} : Set G)).subgroupOf X).map π,
        ((X ⊓ Subgroup.centralizer ({t} : Set G)).subgroupOf X).map π⁆ ≤
        (K.subgroupOf X).map π) :
    K = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
      (X ⊓ Subgroup.centralizer ({t} : Set G)) := by
  set C := X ⊓ Subgroup.centralizer ({t} : Set G) with hC
  set R := CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf C with hRdef
  have hKR : K ≤ R := le_perfectResidualOf hs.perfect_K hs.comp.1
  have hRC : R ≤ C := perfectResidualOf_le C
  have hRperf : ⁅R, R⁆ = R := perfectResidualOf_perfect C
  have hRX : R ≤ X := hRC.trans inf_le_left
  have hRx : ⁅R.subgroupOf X, R.subgroupOf X⁆ = R.subgroupOf X := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hRX, hRperf]
  have hle := le_of_perfect_of_comm_map π hker (C := C.subgroupOf X) (K := K.subgroupOf X)
    (R := R.subgroupOf X) (fun r hr => hRC hr) hRx h
  refine le_antisymm hKR fun r hr => ?_
  exact hle (show (⟨r, hRX hr⟩ : ↥X) ∈ R.subgroupOf X from hr)

end Setting

section Quotient

variable {G : Type} [Group G] [Finite G] {X K : Subgroup G} {t : G}

theorem IdentSetting.center_eq_pCore (hs : IdentSetting X K t) {Q : Type*} [Group Q]
    (e0 : (↥X ⧸ CFSG.pCore 2 ↥X) ≃* Q) (hQ : Subgroup.center Q = ⊥) :
    Subgroup.center ↥X = CFSG.pCore 2 ↥X := by
  have hNn : (CFSG.pCore 2 ↥X).Normal := CFSG.pCore_normal
  have hNp : IsPGroup 2 (CFSG.pCore 2 ↥X) := CFSG.pCore_isPGroup
  apply le_antisymm
  · intro z hz
    have h1 : QuotientGroup.mk z ∈ Subgroup.center (↥X ⧸ CFSG.pCore 2 ↥X) :=
      Subgroup.map_center_le_center (f := QuotientGroup.mk' (CFSG.pCore 2 ↥X))
        (QuotientGroup.mk'_surjective _) (Subgroup.mem_map_of_mem _ hz)
    have h2 : e0 (QuotientGroup.mk z) ∈ Subgroup.center Q := by
      rw [← Subgroup.map_center_eq e0]
      exact Subgroup.mem_map_of_mem _ h1
    rw [hQ, Subgroup.mem_bot] at h2
    have h3 : (QuotientGroup.mk z : ↥X ⧸ CFSG.pCore 2 ↥X) = 1 := e0.injective (by rw [h2, map_one])
    exact (QuotientGroup.eq_one_iff z).mp h3
  · intro n hn
    set Nbar := (CFSG.pCore 2 ↥X).map (QuotientGroup.mk' (Subgroup.center ↥X)) with hNbar
    have hNbn : Nbar.Normal := Subgroup.Normal.map hNn _ (QuotientGroup.mk'_surjective _)
    have hsimple : IsSimpleGroup (↥X ⧸ Subgroup.center ↥X) := hs.quasi.2.1
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Nbar with h | h
    · have hmem : (QuotientGroup.mk' (Subgroup.center ↥X)) n ∈ Nbar := Subgroup.mem_map_of_mem _ hn
      rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply] at hmem
      exact (QuotientGroup.eq_one_iff n).mp hmem
    · exfalso
      have hp2 : IsPGroup 2 (↥X ⧸ Subgroup.center ↥X) := by
        intro a
        have : a ∈ Nbar := by rw [h]; exact Subgroup.mem_top a
        obtain ⟨m, hm, hma⟩ := Subgroup.mem_map.mp this
        obtain ⟨k, hk⟩ := hNp ⟨m, hm⟩
        refine ⟨k, ?_⟩
        rw [← hma, QuotientGroup.mk'_apply, ← QuotientGroup.mk_pow]
        have := congrArg Subtype.val hk
        simp only [Subgroup.coe_pow, OneMemClass.coe_one] at this
        rw [this]
        rfl
      have hnil := hp2.isNilpotent
      have hsolv : Group.IsSolvable (↥X ⧸ Subgroup.center ↥X) := inferInstance
      obtain ⟨-, -, a, b, hab⟩ := hs.quasi
      exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv a b)

theorem IdentSetting.injective_proj
    (hs : IdentSetting X K t) (hK : IsKType K) {Q : Type*} [Group Q]
    (π : ↥X →* Q) (hker : π.ker = Subgroup.center ↥X) :
    Function.Injective (π.comp (Subgroup.inclusion hs.K_le)) := by
  rw [injective_iff_map_eq_one]
  intro k hk
  have hz : Subgroup.inclusion hs.K_le k ∈ Subgroup.center ↥X := by
    rw [← hker]
    exact hk
  have hmem : Subgroup.inclusion hs.K_le k ∈ K.subgroupOf X ⊓ Subgroup.center ↥X := ⟨k.2, hz⟩
  rw [hs.inf_center hK, Subgroup.mem_bot] at hmem
  exact Subgroup.inclusion_injective hs.K_le (by rw [hmem, map_one])

omit [Finite G] in
theorem IdentSetting.map_subgroupOf_eq_range (hs : IdentSetting X K t) {Q : Type*} [Group Q]
    (π : ↥X →* Q) : (K.subgroupOf X).map π = (π.comp (Subgroup.inclusion hs.K_le)).range := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨Subgroup.inclusion hs.K_le k, k.2, rfl⟩

end Quotient

namespace Tab

open CFSG.ComponentClassification.OuterAutomorphisms

theorem quotAct_mem_inner_of_inducesInner {G : Type} [Group G] {X : Subgroup G} {Q : Type*}
    [Group Q] {t : G} (π : ↥X →* Q) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.center ↥X) (ht : t ∈ Subgroup.normalizer (X : Set G))
    (ht2 : t * t = 1) (h : CFSG.QuasithinUnique.Ch1.InducesInner t X) :
    quotAct π hπ hker ht ∈ inner Q := by
  obtain ⟨l, hl, hx⟩ := h
  have hinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hconj : conjAut X t ht = MulAut.conj (⟨l⁻¹, X.inv_mem hl⟩ : ↥X) := by
    ext x
    rw [coe_conjAut, MulAut.conj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    calc t * (x : G) * t⁻¹ = t⁻¹ * (x : G) * t := by rw [hinv]
      _ = (l : G)⁻¹ * x * l := hx x x.2
  rw [quotAct, hconj, quotActHom_conj]
  exact ⟨π _, rfl⟩

end Tab

end CFSG.QuasithinUnique.Id2519
