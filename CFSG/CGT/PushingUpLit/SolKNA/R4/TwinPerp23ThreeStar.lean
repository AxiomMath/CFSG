module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp23ThreeHyp

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

namespace Perp23

namespace Three

section Generic

variable {Y : Type} [Group Y] [Finite Y]

theorem comm_of_mem_zpowers {x a b : Y} (ha : a ∈ Subgroup.zpowers x)
    (hb : b ∈ Subgroup.zpowers x) : a * b = b * a := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  exact ((Commute.refl x).zpow_zpow i j).eq

theorem eq_or_mul_of_sq {L : Subgroup Y} {t b y : Y} (hz : IsUniqueInvolution L t) (hb : b ∈ L)
    (hy : y ∈ L) (hbb : b * b = t) (hyy : y * y = t) (hcomm : y * b = b * y) :
    y = b ∨ y = t * b := by
  have hbi : Commute y b⁻¹ := (Commute.inv_right (show Commute y b from hcomm))
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right hz.sq
  have h1 : (y * b⁻¹) * (y * b⁻¹) = 1 := by
    calc (y * b⁻¹) * (y * b⁻¹) = y * (b⁻¹ * y) * b⁻¹ := by group
      _ = y * (y * b⁻¹) * b⁻¹ := by rw [← hbi.eq]
      _ = (y * y) * (b⁻¹ * b⁻¹) := by group
      _ = t * (b * b)⁻¹ := by rw [hyy]; group
      _ = 1 := by rw [hbb, hti]; exact hz.sq
  rcases hz.unique (y * b⁻¹) (L.mul_mem hy (L.inv_mem hb)) h1 with h | h
  · left
    calc y = (y * b⁻¹) * b := by group
      _ = b := by rw [h, one_mul]
  · right
    calc y = (y * b⁻¹) * b := by group
      _ = t * b := by rw [h]

theorem prod_cases {t b b' u y y' : Y} (ht2 : t * t = 1) (hu : u = b * b'⁻¹) (hut : t * u = u * t)
    (hu2 : u * u = 1) (hy : y = b ∨ y = t * b) (hy' : y' = b' ∨ y' = t * b') :
    y * y'⁻¹ = u ∨ y * y'⁻¹ = t * u := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  rcases hy with rfl | rfl <;> rcases hy' with rfl | rfl
  · left; rw [hu]
  · right
    calc y * (t * b')⁻¹ = (y * b'⁻¹) * t⁻¹ := by group
      _ = u * t := by rw [← hu, hti]
      _ = t * u := hut.symm
  · right
    calc (t * b) * y'⁻¹ = t * (b * y'⁻¹) := by group
      _ = t * u := by rw [← hu]
  · left
    calc (t * b) * (t * b')⁻¹ = (t * (b * b'⁻¹)) * t⁻¹ := by group
      _ = (t * u) * t := by rw [← hu, hti]
      _ = (u * t) * t := by rw [hut]
      _ = u := by rw [mul_assoc, ht2, mul_one]

theorem prod_cases_swap {t b b' u y y' : Y} (ht2 : t * t = 1) (hu : u = b * b'⁻¹)
    (hut : t * u = u * t) (hu2 : u * u = 1) (hy : y = b' ∨ y = t * b') (hy' : y' = b ∨ y' = t * b) :
    y * y'⁻¹ = u ∨ y * y'⁻¹ = t * u := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hub : b' * b⁻¹ = u := by
    rw [← hui, hu]; group
  rcases hy with rfl | rfl <;> rcases hy' with rfl | rfl
  · left; exact hub
  · right
    calc y * (t * b)⁻¹ = (y * b⁻¹) * t⁻¹ := by group
      _ = u * t := by rw [hub, hti]
      _ = t * u := hut.symm
  · right
    calc (t * b') * y'⁻¹ = t * (b' * y'⁻¹) := by group
      _ = t * u := by rw [hub]
  · left
    calc (t * b') * (t * b)⁻¹ = (t * (b' * b⁻¹)) * t⁻¹ := by group
      _ = (t * u) * t := by rw [hub, hti]
      _ = (u * t) * t := by rw [hut]
      _ = u := by rw [mul_assoc, ht2, mul_one]

end Generic

section Star


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  (d : Data r n Y R S t)

namespace Data

include d

@[expose] def T : Subgroup Y := d.D.F.ρ.R ⊔ d.D.F.ρ'.R

theorem hRcomm : Commutes d.D.F.ρ.R d.D.F.ρ'.R :=
  Sec6Gen.commutes_of_twin_of_isPGroup d.hΩ d.hKΩ d.hK'Ω d.hne.symm d.hz d.hz' d.hRK.1 d.hRK'.1
    (d.D.S₀.isPGroup'.to_le (sup_le d.D.hρS d.D.hρ'S))

theorem T_isPGroup : IsPGroup 2 d.T :=
  d.D.S₀.isPGroup'.to_le (sup_le d.D.hρS d.D.hρ'S)

theorem T_sylow : IsSylow2In d.T (tightCore R ⊔ d.K') :=
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T7A.isSylow2In_sup_of_twin d.hΩ d.hKΩ d.hK'Ω d.hne
    d.hz d.hz' d.hRK d.hRK' d.hRcomm

theorem R_le_T : d.D.F.ρ.R ≤ d.T := le_sup_left

theorem R'_le_T : d.D.F.ρ'.R ≤ d.T := le_sup_right

theorem hquat : ∀ L ∈ CoreAssembly.conjClass (tightCore R), ∃ P : Subgroup Y, IsSylow2In P L ∧
    Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))) := by
  rintro _ ⟨g', rfl⟩
  refine ⟨conjSub g' ((S : Subgroup R).map R.subtype), d.h.core.datum.sylow_core.conj g', ⟨?_⟩⟩
  exact (Subgroup.equivMapOfInjective _ (MulAut.conj g').toMonoidHom
    (MulAut.conj g').injective).symm.trans
    ((Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype R.subtype_injective).symm.trans
      d.h.core.quat.some)

theorem h16 (hr : 4 ≤ r) : ∀ J ∈ CoreAssembly.conjClass (tightCore R), ∀ P : Subgroup Y,
    IsSylow2In P J → 16 ≤ Nat.card P := WTool.sylow16_of_quat hr d.hΩ d.hquat

theorem U1_eq : Subgroup.zpowers d.D.x₁ = tightCore R ⊓ d.W := by
  have hKS : tightCore R ⊓ (d.D.S₀ : Subgroup Y) = d.D.F.ρ.R :=
    d.hRK.2.2 _ inf_le_left (d.D.S₀.isPGroup'.to_le inf_le_right)
      (le_inf d.hRK.1 d.D.hρS)
  refine d.D.h₁.trans (le_antisymm (inf_le_inf_right _ d.hRK.1) ?_)
  intro x hx
  have : x ∈ tightCore R ⊓ (d.D.S₀ : Subgroup Y) := ⟨hx.1, d.D.hWS hx.2⟩
  rw [hKS] at this
  exact ⟨this, hx.2⟩

theorem U2_eq : Subgroup.zpowers d.D.x₂ = d.K' ⊓ d.W := by
  have hKS : d.K' ⊓ (d.D.S₀ : Subgroup Y) = d.D.F.ρ'.R :=
    d.hRK'.2.2 _ inf_le_left (d.D.S₀.isPGroup'.to_le inf_le_right)
      (le_inf d.hRK'.1 d.D.hρ'S)
  refine d.D.h₂.trans (le_antisymm (inf_le_inf_right _ d.hRK'.1) ?_)
  intro x hx
  have : x ∈ d.K' ⊓ (d.D.S₀ : Subgroup Y) := ⟨hx.1, d.D.hWS hx.2⟩
  rw [hKS] at this
  exact ⟨this, hx.2⟩

theorem U1_mem (hr : 4 ≤ r) : Subgroup.zpowers d.D.x₁ ∈ USet (CoreAssembly.conjClass (tightCore R)) := by
  rw [d.U1_eq]
  refine WTool.inf_mem_USet_of_card d.hΩ d.hW (S := d.D.S₀) d.D.hWS d.hKΩ ?_
  have h1 := Subgroup.card_le_of_le (le_inf d.hRK.1 d.D.hρS)
  have h2 := d.h16 hr _ d.hKΩ _ d.hRK
  omega

theorem U2_mem (hr : 4 ≤ r) : Subgroup.zpowers d.D.x₂ ∈ USet (CoreAssembly.conjClass (tightCore R)) := by
  rw [d.U2_eq]
  refine WTool.inf_mem_USet_of_card d.hΩ d.hW (S := d.D.S₀) d.D.hWS d.hK'Ω ?_
  have h1 := Subgroup.card_le_of_le (le_inf d.hRK'.1 d.D.hρ'S)
  have h2 := d.h16 hr _ d.hK'Ω _ d.hRK'
  omega

theorem hKtw : tightCore R ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) :=
  mem_twinSet_self d.hKΩ d.hz

theorem conj_u_mem (hr : 4 ≤ r) {n : Y} (hn : n ∈ Subgroup.centralizer ({t} : Set Y))
    (hnT : conjSub n d.T = d.T) :
    n * d.D.u * n⁻¹ = d.D.u ∨ n * d.D.u * n⁻¹ = t * d.D.u := by
  classical
  have hc := d.hc
  have hnt : n * t * n⁻¹ = t := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hn
    rw [this]; group
  have hu : d.D.u = d.D.b * d.D.b'⁻¹ := rfl
  have hut : t * d.D.u = d.D.u * t := hc _ d.D.t_mem_W _ d.D.u_mem_W
  have hu2 := u_mul_self d.D hc
  have ht2 := d.hz.sq
  have hU₁ := d.U1_mem hr
  have hU₂ := d.U2_mem hr
  have hU₁T : Subgroup.zpowers d.D.x₁ ≤ d.T :=
    (Subgroup.zpowers_le.mpr d.D.x₁_mem_R).trans d.R_le_T
  have hU₂T : Subgroup.zpowers d.D.x₂ ≤ d.T :=
    (Subgroup.zpowers_le.mpr d.D.x₂_mem_R).trans d.R'_le_T
  have hU₁K : Subgroup.zpowers d.D.x₁ ≤ tightCore R := d.U1_eq ▸ inf_le_left
  have hU₂K : Subgroup.zpowers d.D.x₂ ≤ d.K' := d.U2_eq ▸ inf_le_left
  have hbU : d.D.b ∈ Subgroup.zpowers d.D.x₁ := Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  have hb'U : d.D.b' ∈ Subgroup.zpowers d.D.x₂ := Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  have himg : ∀ U : Subgroup Y, U ∈ USet (CoreAssembly.conjClass (tightCore R)) → U ≤ d.T →
      conjSub n U ∈ USet (CoreAssembly.conjClass (tightCore R)) ∧ conjSub n U ≤ d.T := fun U hU hUT =>
    ⟨USet.conj d.hΩ.conjInvariant hU n, by
      have := conjSub_mono (n := n) hUT
      rwa [hnT] at this⟩
  have hKn : conjSub n (tightCore R) ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) :=
    d.h.conj_mem_twinSet d.hKtw hn
  have hK'n : conjSub n d.K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) :=
    d.h.conj_mem_twinSet d.hK' hn
  rw [d.hpair] at hKn hK'n
  have hinj : conjSub n (tightCore R) ≠ conjSub n d.K' := fun heq => d.hne (by
    have h1 := congrArg (conjSub n⁻¹) heq
    rw [conjSub_inv_conjSub, conjSub_inv_conjSub] at h1
    exact h1.symm)
  have hconj : n * d.D.u * n⁻¹ = (n * d.D.b * n⁻¹) * (n * d.D.b' * n⁻¹)⁻¹ := by rw [hu]; group
  have hbb : (n * d.D.b * n⁻¹) * (n * d.D.b * n⁻¹) = t := by
    calc (n * d.D.b * n⁻¹) * (n * d.D.b * n⁻¹) = n * (d.D.b * d.D.b) * n⁻¹ := by group
      _ = t := by rw [d.D.b_sq, hnt]
  have hb'b' : (n * d.D.b' * n⁻¹) * (n * d.D.b' * n⁻¹) = t := by
    calc (n * d.D.b' * n⁻¹) * (n * d.D.b' * n⁻¹) = n * (d.D.b' * d.D.b') * n⁻¹ := by group
      _ = t := by rw [d.D.b'_sq, hnt]
  rw [hconj]
  rcases Set.mem_insert_iff.mp hKn with h1 | h1
  ·
    have h1' : conjSub n d.K' = d.K' := by
      rcases Set.mem_insert_iff.mp hK'n with h2 | h2
      · exact absurd (h1.trans h2.symm) hinj
      · exact Set.mem_singleton_iff.mp h2
    obtain ⟨hV₁, hV₁T⟩ := himg _ hU₁ hU₁T
    obtain ⟨hV₂, hV₂T⟩ := himg _ hU₂ hU₂T
    have hV₁K : conjSub n (Subgroup.zpowers d.D.x₁) ≤ tightCore R := by
      have := conjSub_mono (n := n) hU₁K
      rwa [h1] at this
    have hV₂K : conjSub n (Subgroup.zpowers d.D.x₂) ≤ d.K' := by
      have := conjSub_mono (n := n) hU₂K
      rwa [h1'] at this
    have e₁ := WTool.eq_of_mem_USet_of_isPGroup d.hΩ (d.h16 hr) d.hKΩ d.T_isPGroup hV₁ hU₁ hV₁K
      hU₁K hV₁T hU₁T
    have e₂ := WTool.eq_of_mem_USet_of_isPGroup d.hΩ (d.h16 hr) d.hK'Ω d.T_isPGroup hV₂ hU₂ hV₂K
      hU₂K hV₂T hU₂T
    have hy : n * d.D.b * n⁻¹ ∈ Subgroup.zpowers d.D.x₁ := by
      rw [← e₁]; exact conj_mem_conjSub hbU
    have hy' : n * d.D.b' * n⁻¹ ∈ Subgroup.zpowers d.D.x₂ := by
      rw [← e₂]; exact conj_mem_conjSub hb'U
    have c1 := eq_or_mul_of_sq d.hz (hU₁K hbU) (hU₁K hy) d.D.b_sq hbb
      (comm_of_mem_zpowers hy hbU)
    have c2 := eq_or_mul_of_sq d.hz' (hU₂K hb'U) (hU₂K hy') d.D.b'_sq hb'b'
      (comm_of_mem_zpowers hy' hb'U)
    exact prod_cases ht2 hu hut hu2 c1 c2
  ·
    have h1 : conjSub n (tightCore R) = d.K' := Set.mem_singleton_iff.mp h1
    have h1' : conjSub n d.K' = tightCore R := by
      rcases Set.mem_insert_iff.mp hK'n with h2 | h2
      · exact h2
      · exact absurd (h1.trans (Set.mem_singleton_iff.mp h2).symm) hinj
    obtain ⟨hV₁, hV₁T⟩ := himg _ hU₁ hU₁T
    obtain ⟨hV₂, hV₂T⟩ := himg _ hU₂ hU₂T
    have hV₁K : conjSub n (Subgroup.zpowers d.D.x₁) ≤ d.K' := by
      have := conjSub_mono (n := n) hU₁K
      rwa [h1] at this
    have hV₂K : conjSub n (Subgroup.zpowers d.D.x₂) ≤ tightCore R := by
      have := conjSub_mono (n := n) hU₂K
      rwa [h1'] at this
    have e₁ := WTool.eq_of_mem_USet_of_isPGroup d.hΩ (d.h16 hr) d.hK'Ω d.T_isPGroup hV₁ hU₂ hV₁K
      hU₂K hV₁T hU₂T
    have e₂ := WTool.eq_of_mem_USet_of_isPGroup d.hΩ (d.h16 hr) d.hKΩ d.T_isPGroup hV₂ hU₁ hV₂K
      hU₁K hV₂T hU₁T
    have hy : n * d.D.b * n⁻¹ ∈ Subgroup.zpowers d.D.x₂ := by
      rw [← e₁]; exact conj_mem_conjSub hbU
    have hy' : n * d.D.b' * n⁻¹ ∈ Subgroup.zpowers d.D.x₁ := by
      rw [← e₂]; exact conj_mem_conjSub hb'U
    have c1 := eq_or_mul_of_sq d.hz' (hU₂K hb'U) (hU₂K hy) d.D.b'_sq hbb
      (comm_of_mem_zpowers hy hb'U)
    have c2 := eq_or_mul_of_sq d.hz (hU₁K hbU) (hU₁K hy') d.D.b_sq hb'b'
      (comm_of_mem_zpowers hy' hbU)
    exact prod_cases_swap ht2 hu hut hu2 c1 c2

theorem exists_odd_mul {ℓ : Y} (hℓ : ℓ ∈ Subgroup.centralizer ({t} : Set Y)) :
    ∃ o ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)), ∃ n ∈ Subgroup.centralizer ({t} : Set Y),
      conjSub n d.T = d.T ∧ ℓ = o * n := by
  classical
  set C := Subgroup.centralizer ({t} : Set Y) with hCdef
  set K := tightCore R with hKdef
  have hKC := d.K_le_centralizer
  have hK'C := d.K'_le_centralizer
  have hMle : conjSub ℓ (K ⊔ d.K') ≤ K ⊔ d.K' := by
    rintro _ ⟨y, hy, rfl⟩
    exact d.conj_mem_sup ℓ hℓ y hy
  have hMeq : conjSub ℓ (K ⊔ d.K') = K ⊔ d.K' :=
    mem_normalizer_iff_conjSub_eq.mp (mem_normalizer_of_conjSub_le hMle)
  have hsyl : IsSylow2In (conjSub ℓ d.T) (K ⊔ d.K') := by
    have := d.T_sylow.conj ℓ
    rwa [hMeq] at this
  obtain ⟨m, hmM, hm⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In d.T_sylow hsyl
  have hKN : K ≤ Subgroup.normalizer (d.K' : Set Y) :=
    Sec6Gen.le_normalizer_of_twin d.hΩ d.hKΩ d.hK'Ω d.hne.symm d.hz d.hz'
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right K d.K' hKN] at hmM
  obtain ⟨k, hk, k', hk', rfl⟩ := hmM
  obtain ⟨r₁, hr₁, o₁, ho₁, rfl⟩ :=
    TwinExact.mem_mul_oddCore_of_sylow (d.h2all K d.hKΩ) d.hRK k hk
  obtain ⟨r₁', hr₁', o₁', ho₁', rfl⟩ :=
    TwinExact.mem_mul_oddCore_of_sylow (d.h2all _ d.hK'Ω) d.hRK' k' hk'
  have hr₁C : r₁ ∈ C := hKC (d.hRK.1 hr₁)
  have hr₁'C : r₁' ∈ C := hK'C (d.hRK'.1 hr₁')
  have hτT : r₁ * r₁' ∈ d.T := d.T.mul_mem (d.R_le_T hr₁) (d.R'_le_T hr₁')
  have hτC : r₁ * r₁' ∈ C := C.mul_mem hr₁C hr₁'C
  have ho₁C : o₁ ∈ oddCoreIn C := d.oddCoreIn_K_le ho₁
  have ho₁'C : o₁' ∈ oddCoreIn C := d.oddCoreIn_K'_le ho₁'
  set o₃ : Y := (r₁ * o₁ * r₁⁻¹) * ((r₁ * r₁') * o₁' * (r₁ * r₁')⁻¹) with ho₃
  have ho₃O : o₃ ∈ oddCoreOf C :=
    (oddCoreOf C).mul_mem (conj_mem_oddCoreIn hr₁C ho₁C) (conj_mem_oddCoreIn hτC ho₁'C)
  have hm' : (r₁ * o₁) * (r₁' * o₁') = o₃ * (r₁ * r₁') := by rw [ho₃]; group
  have hn : conjSub (o₃⁻¹ * ℓ) d.T = d.T := by
    have hm0 : conjSub ((r₁ * o₁) * (r₁' * o₁')) d.T = conjSub ℓ d.T := hm
    have hτ : conjSub (r₁ * r₁') d.T = d.T := conjSub_eq_self_of_mem hτT
    rw [conjSub_mul, ← hm0, hm', conjSub_mul, hτ, conjSub_inv_conjSub]
  refine ⟨o₃, ho₃O, o₃⁻¹ * ℓ, C.mul_mem (C.inv_mem (oddCoreIn_le C ho₃O)) hℓ, hn, ?_⟩
  group

theorem starT_key (hr : 4 ≤ r) {ℓ : Y} (hℓ : ℓ ∈ Subgroup.centralizer ({t} : Set Y)) :
    ∃ o ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)),
      ℓ * d.D.u * ℓ⁻¹ = d.D.u * o ∨ ℓ * d.D.u * ℓ⁻¹ = (t * d.D.u) * o := by
  set C := Subgroup.centralizer ({t} : Set Y) with hCdef
  obtain ⟨o, ho, n, hn, hnT, rfl⟩ := d.exists_odd_mul hℓ
  have huC : d.D.u ∈ C :=
    Subgroup.mem_centralizer_singleton_iff.mpr (d.hc _ d.D.u_mem_W _ d.D.t_mem_W)
  have htC : t ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hoC : o ∈ C := oddCoreIn_le C ho
  have key : ∀ u'' : Y, u'' ∈ C → n * d.D.u * n⁻¹ = u'' →
      ∃ o' ∈ oddCoreOf C, (o * n) * d.D.u * (o * n)⁻¹ = u'' * o' := by
    intro u'' hu''C hnu
    refine ⟨u''⁻¹ * o * u'' * o⁻¹, ?_, ?_⟩
    · have h1 : u''⁻¹ * o * u''⁻¹⁻¹ ∈ oddCoreOf C := conj_mem_oddCoreIn (C.inv_mem hu''C) ho
      rw [inv_inv] at h1
      exact (oddCoreOf C).mul_mem h1 ((oddCoreOf C).inv_mem ho)
    · calc (o * n) * d.D.u * (o * n)⁻¹ = o * (n * d.D.u * n⁻¹) * o⁻¹ := by group
        _ = u'' * (u''⁻¹ * o * u'' * o⁻¹) := by rw [hnu]; group
  rcases d.conj_u_mem hr hn hnT with h | h
  · obtain ⟨o', ho', h'⟩ := key _ huC h
    exact ⟨o', ho', Or.inl h'⟩
  · obtain ⟨o', ho', h'⟩ := key _ (C.mul_mem htC huC) h
    exact ⟨o', ho', Or.inr h'⟩

theorem starT (hr : 4 ≤ r) : ∀ ℓ ∈ Subgroup.centralizer ({t} : Set Y),
    d.D.u * ℓ * d.D.u⁻¹ * ℓ⁻¹ ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)) ∨
    d.D.u * (d.D.F.ρ.r⁻¹ * ℓ) * d.D.u⁻¹ * (d.D.F.ρ.r⁻¹ * ℓ)⁻¹ ∈
      oddCoreOf (Subgroup.centralizer ({t} : Set Y)) := by
  set C := Subgroup.centralizer ({t} : Set Y) with hCdef
  have huC : d.D.u ∈ C :=
    Subgroup.mem_centralizer_singleton_iff.mpr (d.hc _ d.D.u_mem_W _ d.D.t_mem_W)
  have hrC : d.D.F.ρ.r ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr d.D.r_t
  have hP : ∀ (ℓ' : Y) (o' : Y), o' ∈ oddCoreOf C → ℓ' * d.D.u * ℓ'⁻¹ = d.D.u * o' →
      d.D.u * ℓ' * d.D.u⁻¹ * ℓ'⁻¹ ∈ oddCoreOf C := by
    intro ℓ' o' ho' h
    have e : d.D.u * ℓ' * d.D.u⁻¹ * ℓ'⁻¹ = d.D.u * o'⁻¹ * d.D.u⁻¹ := by
      calc d.D.u * ℓ' * d.D.u⁻¹ * ℓ'⁻¹ = d.D.u * (ℓ' * d.D.u⁻¹ * ℓ'⁻¹) := by group
        _ = d.D.u * (ℓ' * d.D.u * ℓ'⁻¹)⁻¹ := by group
        _ = d.D.u * o'⁻¹ * d.D.u⁻¹ := by rw [h]; group
    rw [e]
    exact conj_mem_oddCoreIn huC ((oddCoreOf C).inv_mem ho')
  intro ℓ hℓ
  obtain ⟨o, ho, h | h⟩ := d.starT_key hr hℓ
  · exact Or.inl (hP ℓ o ho h)
  · right
    have hℓ' : d.D.F.ρ.r⁻¹ * ℓ ∈ C := C.mul_mem (C.inv_mem hrC) hℓ
    refine hP _ (d.D.F.ρ.r⁻¹ * o * d.D.F.ρ.r) ?_ ?_
    · have h1 : d.D.F.ρ.r⁻¹ * o * d.D.F.ρ.r⁻¹⁻¹ ∈ oddCoreOf C :=
        conj_mem_oddCoreIn (C.inv_mem hrC) ho
      rwa [inv_inv] at h1
    · have hru := d.D.r_u d.hc
      calc (d.D.F.ρ.r⁻¹ * ℓ) * d.D.u * (d.D.F.ρ.r⁻¹ * ℓ)⁻¹
          = d.D.F.ρ.r⁻¹ * (ℓ * d.D.u * ℓ⁻¹) * d.D.F.ρ.r := by group
        _ = d.D.F.ρ.r⁻¹ * ((t * d.D.u) * o) * d.D.F.ρ.r := by rw [h]
        _ = (d.D.F.ρ.r⁻¹ * (t * d.D.u) * d.D.F.ρ.r) * (d.D.F.ρ.r⁻¹ * o * d.D.F.ρ.r) := by group
        _ = d.D.u * (d.D.F.ρ.r⁻¹ * o * d.D.F.ρ.r) := by
            rw [← hru]; group

end Data

end Star

end Three

end Perp23

end CFSG.CGT.PushingUpLit.SolKNA.R4
