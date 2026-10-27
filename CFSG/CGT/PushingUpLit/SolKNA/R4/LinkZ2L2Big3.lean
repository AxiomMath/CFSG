module

public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2L2B4A
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big1

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W
open CFSG.Blueprint

section Aux

variable {Y : Type} [Group Y]

variable {Y : Type} [Group Y]

theorem aux_conj_comm_iff (x h w : Y) :
    (x * h * x⁻¹) * (x * w * x⁻¹) = (x * w * x⁻¹) * (x * h * x⁻¹) ↔ h * w = w * h := by
  have e1 : (x * h * x⁻¹) * (x * w * x⁻¹) = x * (h * w) * x⁻¹ := by group
  have e2 : (x * w * x⁻¹) * (x * h * x⁻¹) = x * (w * h) * x⁻¹ := by group
  rw [e1, e2]
  constructor
  · intro H
    exact mul_left_cancel (mul_right_cancel H)
  · intro H
    rw [H]

theorem aux_comm_of_mem_closure {x t u : Y} (hxt : x * t = t * x) (hxu : x * u = u * x)
    {e : Y} (he : e ∈ Subgroup.closure ({t, u} : Set Y)) : x * e = e * x := by
  have hle : Subgroup.closure ({t, u} : Set Y) ≤ Subgroup.centralizer ({x} : Set Y) := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hxt.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hxu.symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle he)).symm

theorem aux_eq_one_of_mem_odd {P : Sylow 2 Y} {O : Subgroup Y} (hO : Odd (Nat.card O))
    {k : Y} (hkO : k ∈ O) (hkP : k ∈ (P : Subgroup Y)) : k = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : orderOf k ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hkO
  obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.mp P.isPGroup' ⟨k, hkP⟩
  rw [Subgroup.orderOf_mk] at hm
  rw [hm] at h1
  rcases m with _ | m
  · rwa [pow_zero, orderOf_eq_one_iff] at hm
  · exfalso
    have h2 : 2 ∣ Nat.card O := (dvd_pow_self 2 (Nat.succ_ne_zero m)).trans h1
    exact Nat.not_even_iff_odd.mpr hO (even_iff_two_dvd.mpr h2)


@[expose] def aux_diag (R₀ T₀ : Subgroup Y) (w : Y) (hT : ∀ x ∈ R₀, w * x * w⁻¹ ∈ T₀)
    (hc : Commutes R₀ T₀) : ↥R₀ →* Y where
  toFun x := (x : Y) * (w * x * w⁻¹)
  map_one' := by simp
  map_mul' x y := by
    have h := hc (y : Y) y.2 (w * x * w⁻¹) (hT x x.2)
    simp only [Subgroup.coe_mul]
    calc (x : Y) * y * (w * (x * y) * w⁻¹) = x * (y * (w * x * w⁻¹)) * (w * y * w⁻¹) := by group
      _ = x * ((w * x * w⁻¹) * y) * (w * y * w⁻¹) := by rw [h]
      _ = x * (w * x * w⁻¹) * (y * (w * y * w⁻¹)) := by group

theorem aux_diag_apply {R₀ T₀ : Subgroup Y} {w : Y} (hT : ∀ x ∈ R₀, w * x * w⁻¹ ∈ T₀)
    (hc : Commutes R₀ T₀) (x : ↥R₀) : aux_diag R₀ T₀ w hT hc x = (x : Y) * (w * x * w⁻¹) :=
  rfl

theorem aux_diag_comm {R₀ T₀ : Subgroup Y} {w : Y} (hT : ∀ x ∈ R₀, w * x * w⁻¹ ∈ T₀)
    (hc : Commutes R₀ T₀) (hw2 : w * w = 1) (x : ↥R₀) :
    w * aux_diag R₀ T₀ w hT hc x = aux_diag R₀ T₀ w hT hc x * w := by
  rw [aux_diag_apply]
  have hcx := hc (x : Y) x.2 (w * x * w⁻¹) (hT x x.2)
  have h2 : w * (w * x * w⁻¹) * w⁻¹ = x := by
    calc w * (w * x * w⁻¹) * w⁻¹ = (w * w) * x * (w * w)⁻¹ := by group
      _ = x := by rw [hw2, one_mul, inv_one, mul_one]
  have h3 : w * ((x : Y) * (w * x * w⁻¹)) * w⁻¹ = (x : Y) * (w * x * w⁻¹) := by
    calc w * ((x : Y) * (w * x * w⁻¹)) * w⁻¹
        = (w * x * w⁻¹) * (w * (w * x * w⁻¹) * w⁻¹) := by group
      _ = (w * x * w⁻¹) * x := by rw [h2]
      _ = x * (w * x * w⁻¹) := hcx.symm
  calc w * ((x : Y) * (w * x * w⁻¹)) = (w * ((x : Y) * (w * x * w⁻¹)) * w⁻¹) * w := by group
    _ = (x : Y) * (w * x * w⁻¹) * w := by rw [h3]

end Aux

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y} {R₀ T₀ : Subgroup Y} {P : Sylow 2 Y}

theorem Z2SetR.aux_t_mem (hs : Z2SetR r n R S t J u R₀ T₀ P) : t ∈ R₀ :=
  T3.mem_of_isPGroup hs.large.datum.isUniqueInvolution_core hs.hR₀.1 hs.hR₀.2.1
    (le_trans (by norm_num) (Sec6Gen.eight_le_of_mem_RSet hs.large.datum.hypOmegaGen
      (mem_RSet_of_isSylow2In (CoreAssembly.mem_conjClass_self _) hs.hR₀)))

theorem Z2SetR.aux_u_mem (hs : Z2SetR r n R S t J u R₀ T₀ P) : u ∈ T₀ :=
  T3.mem_of_isPGroup hs.hu hs.hT₀.1 hs.hT₀.2.1
    (le_trans (by norm_num) (Sec6Gen.eight_le_of_mem_RSet hs.large.datum.hypOmegaGen
      (mem_RSet_of_isSylow2In hs.hJ.1 hs.hT₀)))

theorem Z2SetR.aux_tu (hs : Z2SetR r n R S t J u R₀ T₀ P) : t * u = u * t :=
  Subgroup.mem_centralizer_singleton_iff.mp (hs.hR₀u hs.aux_t_mem)

theorem Z2SetR.aux_t_ne_u (hs : Z2SetR r n R S t J u R₀ T₀ P) : t ≠ u :=
  T8.ne_of_mem_omegaNbr (fun K' hK' => by rwa [hs.large.datum.twinSet_eq] at hK') hs.hJ
    hs.large.datum.isUniqueInvolution_core hs.hu

theorem Z2SetR.aux_t_P (hs : Z2SetR r n R S t J u R₀ T₀ P) : t ∈ (P : Subgroup Y) :=
  hs.hR₀P hs.aux_t_mem

theorem Z2SetR.aux_u_P (hs : Z2SetR r n R S t J u R₀ T₀ P) : u ∈ (P : Subgroup Y) :=
  hs.hT₀P hs.aux_u_mem

theorem Z2SetR.aux_E_le (hs : Z2SetR r n R S t J u R₀ T₀ P) :
    Subgroup.closure ({t, u} : Set Y) ≤ edgeCent (P : Subgroup Y) t u := by
  rw [Subgroup.closure_le]
  have htu := hs.aux_tu
  rintro x (rfl | rfl)
  · exact ⟨⟨hs.aux_t_P, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr htu⟩
  · exact ⟨⟨hs.aux_u_P, Subgroup.mem_centralizer_singleton_iff.mpr htu.symm⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

theorem Z2SetR.aux_swap (hs : Z2SetR r n R S t J u R₀ T₀ P) {x : Y}
    (hx : x ∈ (P : Subgroup Y)) (hxA : x ∉ edgeCent (P : Subgroup Y) t u) :
    x * t * x⁻¹ = u ∧ x * u * x⁻¹ = t := by
  rcases hs.perm hx with ⟨h, -⟩ | h
  · exact absurd (hs.mem_edgeCent_iff.mpr ⟨hx, h⟩) hxA
  · exact h

theorem Z2SetR.exists_conj_le_edgeCent (hs : Z2SetR r n R S t J u R₀ T₀ P) {Q : Subgroup Y}
    (hQ : IsPGroup 2 ↥Q) (hQt : Q ≤ Subgroup.centralizer ({t} : Set Y))
    (hQu : Q ≤ Subgroup.centralizer ({u} : Set Y)) :
    ∃ c ∈ Subgroup.centralizer ({t} : Set Y) ⊓ Subgroup.centralizer ({u} : Set Y),
      conjSub c Q ≤ edgeCent (P : Subgroup Y) t u := by
  have hcent : ∀ x h w : Y, h ∈ Subgroup.centralizer ({w} : Set Y) ↔
      x * h * x⁻¹ ∈ Subgroup.centralizer ({x * w * x⁻¹} : Set Y) := by
    intro x h w
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff,
      aux_conj_comm_iff]
  have hPN : (P : Subgroup Y) ≤ Subgroup.normalizer
      ((Subgroup.centralizer ({t} : Set Y) ⊓ Subgroup.centralizer ({u} : Set Y) : Subgroup Y) :
        Set Y) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rcases hs.perm hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [Subgroup.mem_inf, Subgroup.mem_inf, hcent x h t, hcent x h u, h1, h2]
    · rw [Subgroup.mem_inf, Subgroup.mem_inf, hcent x h t, hcent x h u, h1, h2, and_comm]
  have hPsyl : IsSylow2In (P : Subgroup Y) (Subgroup.normalizer
      ((Subgroup.centralizer ({t} : Set Y) ⊓ Subgroup.centralizer ({u} : Set Y) : Subgroup Y) :
        Set Y)) :=
    ⟨hPN, P.isPGroup', fun V _ hV hPV => P.is_maximal' hV hPV⟩
  have hAsyl := AscP1Nine3.isSylow2In_inf_of_le_normalizer' hPsyl Subgroup.le_normalizer le_rfl
  obtain ⟨V, hV, hQV⟩ := IsSylow2In.exists_ge hQ (le_inf hQt hQu)
  obtain ⟨c, hc, hcV⟩ := exists_conjSub_eq_of_isSylow2In hV hAsyl
  refine ⟨c, hc, fun x hx => ?_⟩
  have h := conjSub_mono (n := c) hQV hx
  rw [hcV] at h
  obtain ⟨hxP, hxt, hxu⟩ := h
  exact ⟨⟨hxP, hxt⟩, hxu⟩

theorem Z2SetR.exists_conj_le (hs : Z2SetR r n R S t J u R₀ T₀ P) {Q : Subgroup Y}
    (hQ : IsPGroup 2 ↥Q) (hQa : Q ≤ Subgroup.centralizer ({t * u} : Set Y)) :
    ∃ c ∈ Subgroup.centralizer ({t * u} : Set Y), conjSub c Q ≤ (P : Subgroup Y) := by
  have hPa : (P : Subgroup Y) ≤ Subgroup.centralizer ({t * u} : Set Y) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hs.comm_tu hy)
  obtain ⟨h, hh, hle⟩ := exists_conj_sylow_ge hPa hQ hQa
  refine ⟨h⁻¹, inv_mem hh, ?_⟩
  have := conjSub_mono (n := h⁻¹) hle
  rwa [conjSub_inv_conjSub] at this

theorem Z2SetR.mul_self_mem_edgeCent (hs : Z2SetR r n R S t J u R₀ T₀ P) {x : Y}
    (hx : x ∈ (P : Subgroup Y)) : x * x ∈ edgeCent (P : Subgroup Y) t u := by
  rw [hs.mem_edgeCent_iff]
  refine ⟨(P : Subgroup Y).mul_mem hx hx, ?_⟩
  have e : x * x * t * (x * x)⁻¹ = x * (x * t * x⁻¹) * x⁻¹ := by group
  rcases hs.perm hx with ⟨h1, -⟩ | ⟨h1, h2⟩
  · rw [e, h1, h1]
  · rw [e, h1, h2]

theorem Z2SetR.aux_mem_norm_O (hs : Z2SetR r n R S t J u R₀ T₀ P) {c : Y}
    (hc : c ∈ Subgroup.centralizer ({t * u} : Set Y)) :
    c ∈ Subgroup.normalizer
      ((oddCoreOf (layerY (CoreAssembly.conjClass (tightCore R)) (t * u)) : Subgroup Y) :
        Set Y) :=
  mem_normalizer_of_conjSub_eq (by
    rw [← Thompson.oddCoreOf_conjSub_eq,
      layerY_conjSub_eq hs.large.datum.hypOmegaGen.conjInvariant hc])

theorem Z2SetR.aux_mem_cent_a (hs : Z2SetR r n R S t J u R₀ T₀ P) {y : Y}
    (hy : y ∈ (P : Subgroup Y)) : y ∈ Subgroup.centralizer ({t * u} : Set Y) :=
  Subgroup.mem_centralizer_singleton_iff.mpr (hs.comm_tu hy)

theorem Z2SetR.aux_closure_eq (hs : Z2SetR r n R S t J u R₀ T₀ P) :
    Subgroup.closure ({t * u, t} : Set Y) = Subgroup.closure ({t, u} : Set Y) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
    · exact Subgroup.subset_closure (by simp)
  · rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨Subgroup.subset_closure (by simp), ?_⟩
    have h := mul_mem (inv_mem (Subgroup.subset_closure (by simp : t ∈ ({t * u, t} : Set Y))))
      (Subgroup.subset_closure (by simp : t * u ∈ ({t * u, t} : Set Y)))
    rwa [inv_mul_cancel_left] at h

theorem Z2SetR.aux_E_le_cent (hs : Z2SetR r n R S t J u R₀ T₀ P) :
    Subgroup.closure ({t, u} : Set Y) ≤ Subgroup.centralizer ({t * u} : Set Y) :=
  fun _ he => hs.aux_mem_cent_a (hs.aux_E_le he).1.1

theorem Z2SetR.aux_mem_sup (hs : Z2SetR r n R S t J u R₀ T₀ P) {m : Y}
    (hm : m ∈ Subgroup.closure ({t * u, t} : Set Y) ⊔
      oddCoreOf (layerY (CoreAssembly.conjClass (tightCore R)) (t * u))) :
    ∃ e ∈ Subgroup.closure ({t, u} : Set Y),
      ∃ o ∈ oddCoreOf (layerY (CoreAssembly.conjClass (tightCore R)) (t * u)), e * o = m := by
  have hle : Subgroup.closure ({t * u, t} : Set Y) ≤ Subgroup.normalizer
      ((oddCoreOf (layerY (CoreAssembly.conjClass (tightCore R)) (t * u)) : Subgroup Y) :
        Set Y) := by
    intro e he
    rw [hs.aux_closure_eq] at he
    exact hs.aux_mem_norm_O (hs.aux_E_le_cent he)
  have h : m ∈ ((Subgroup.closure ({t * u, t} : Set Y) ⊔
      oddCoreOf (layerY (CoreAssembly.conjClass (tightCore R)) (t * u)) : Subgroup Y) :
        Set Y) := hm
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle] at h
  obtain ⟨e, he, o, ho, rfl⟩ := Set.mem_mul.mp h
  have he' : e ∈ Subgroup.closure ({t * u, t} : Set Y) := he
  rw [hs.aux_closure_eq] at he'
  exact ⟨e, he', o, ho, rfl⟩

theorem Z2SetR.aux_comm_mem_O (hs : Z2SetR r n R S t J u R₀ T₀ P) {h : Y}
    (hh : h ∈ edgeCent (P : Subgroup Y) t u) {m : Y}
    (hm : m ∈ Subgroup.closure ({t * u, t} : Set Y) ⊔
      oddCoreOf (layerY (CoreAssembly.conjClass (tightCore R)) (t * u))) :
    h * m * h⁻¹ * m⁻¹ ∈ oddCoreOf (layerY (CoreAssembly.conjClass (tightCore R)) (t * u)) := by
  obtain ⟨e, he, o, ho, rfl⟩ := hs.aux_mem_sup hm
  obtain ⟨⟨hhP, hht⟩, hhu⟩ := hh
  have hhe : h * e = e * h := aux_comm_of_mem_closure
    (Subgroup.mem_centralizer_singleton_iff.mp hht) (Subgroup.mem_centralizer_singleton_iff.mp hhu)
    he
  have hho := (Subgroup.mem_normalizer_iff.mp (hs.aux_mem_norm_O (hs.aux_mem_cent_a hhP)) o).mp ho
  have heN := hs.aux_mem_norm_O (hs.aux_E_le_cent he)
  have e1 : h * (e * o) * h⁻¹ * (e * o)⁻¹ = e * ((h * o * h⁻¹) * o⁻¹) * e⁻¹ := by
    calc h * (e * o) * h⁻¹ * (e * o)⁻¹ = (h * e) * o * h⁻¹ * o⁻¹ * e⁻¹ := by group
      _ = (e * h) * o * h⁻¹ * o⁻¹ * e⁻¹ := by rw [hhe]
      _ = e * ((h * o * h⁻¹) * o⁻¹) * e⁻¹ := by group
  rw [e1]
  exact (Subgroup.mem_normalizer_iff.mp heN _).mp (mul_mem hho (inv_mem ho))

theorem Z2SetR.aux_mem_of_conj (hs : Z2SetR r n R S t J u R₀ T₀ P)
    (h1 : C264One (CoreAssembly.conjClass (tightCore R)) t u) {g c : Y}
    (hg : g ∈ (P : Subgroup Y)) (hc : c ∈ Subgroup.centralizer ({t * u} : Set Y))
    (hcg : c * g * c⁻¹ ∈ edgeCent (P : Subgroup Y) t u) : g ∈ edgeCent (P : Subgroup Y) t u := by
  rw [hs.mem_edgeCent_iff]
  refine ⟨hg, ?_⟩
  have htM : t ∈ Subgroup.closure ({t * u, t} : Set Y) ⊔
      oddCoreOf (layerY (CoreAssembly.conjClass (tightCore R)) (t * u)) :=
    Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
  have hm := (Subgroup.mem_normalizer_iff.mp (h1 hc) t).mp htM
  have hk := hs.aux_comm_mem_O hcg hm
  have hk' : g * t * g⁻¹ * t⁻¹ ∈
      oddCoreOf (layerY (CoreAssembly.conjClass (tightCore R)) (t * u)) := by
    have e : g * t * g⁻¹ * t⁻¹ = c⁻¹ * ((c * g * c⁻¹) * (c * t * c⁻¹) * (c * g * c⁻¹)⁻¹ *
        (c * t * c⁻¹)⁻¹) * c⁻¹⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hs.aux_mem_norm_O (inv_mem hc)) _).mp hk
  rcases hs.perm hg with ⟨h, -⟩ | ⟨h, -⟩
  · exact h
  · exfalso
    rw [h] at hk'
    have hut : u * t⁻¹ = 1 := aux_eq_one_of_mem_odd (P := P) (odd_natCard_oddCoreOf _) hk'
      (mul_mem hs.aux_u_P (inv_mem hs.aux_t_P))
    exact hs.aux_t_ne_u (mul_inv_eq_one.mp hut).symm

theorem Z2SetR.mem_edgeCent_iff_conj (hs : Z2SetR r n R S t J u R₀ T₀ P)
    (h1 : C264One (CoreAssembly.conjClass (tightCore R)) t u) {g c : Y}
    (hg : g ∈ (P : Subgroup Y)) (hc : c ∈ Subgroup.centralizer ({t * u} : Set Y))
    (hcg : c * g * c⁻¹ ∈ (P : Subgroup Y)) :
    g ∈ edgeCent (P : Subgroup Y) t u ↔ c * g * c⁻¹ ∈ edgeCent (P : Subgroup Y) t u := by
  constructor
  · intro hgA
    refine hs.aux_mem_of_conj h1 hcg (inv_mem hc) ?_
    have e : c⁻¹ * (c * g * c⁻¹) * c⁻¹⁻¹ = g := by group
    rwa [e]
  · exact hs.aux_mem_of_conj h1 hg hc

theorem Z2SetR.mem_E_of_sylow_le (hs : Z2SetR r n R S t J u R₀ T₀ P)
    (h1 : C264One (CoreAssembly.conjClass (tightCore R)) t u) {L : Subgroup Y}
    (hL : L ∈ CoreAssembly.conjClass (tightCore R)) {y : Y} (hy : IsUniqueInvolution L y)
    {Ry : Subgroup Y} (hRy : IsSylow2In Ry L) (hRa : Ry ≤ Subgroup.centralizer ({t * u} : Set Y))
    (hyP : y ∈ (P : Subgroup Y)) : y ∈ Subgroup.closure ({t, u} : Set Y) := by
  have hΩ := hs.large.datum.hypOmegaGen
  obtain ⟨c, hc, hcR⟩ := hs.exists_conj_le hRy.2.1 hRa
  have hRc : conjSub c Ry ∈ RSet (CoreAssembly.conjClass (tightCore R)) :=
    mem_RSet_of_isSylow2In (hΩ.conjInvariant c L hL) (hRy.conj c)
  have hyR : y ∈ Ry := T3.mem_of_isPGroup hy hRy.1 hRy.2.1
    (le_trans (by norm_num) (Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hL hRy)))
  have hcy : c * y * c⁻¹ ∈ conjSub c Ry := conj_mem_conjSub hyR c
  have hcy2 : (c * y * c⁻¹) * (c * y * c⁻¹) = 1 := by
    calc (c * y * c⁻¹) * (c * y * c⁻¹) = c * (y * y) * c⁻¹ := by group
      _ = 1 := by rw [hy.sq, mul_one, mul_inv_cancel]
  have hcy1 : c * y * c⁻¹ ≠ 1 := by
    intro h
    apply hy.ne_one
    calc y = c⁻¹ * (c * y * c⁻¹) * c := by group
      _ = 1 := by rw [h, mul_one, inv_mul_cancel]
  have hw : c * y * c⁻¹ = t ∨ c * y * c⁻¹ = u := by
    rcases hs.rSet_le hRc hcR with he | he
    · rw [he] at hcy
      exact Or.inl ((hs.large.datum.isUniqueInvolution_core.unique _ (hs.hR₀.1 hcy)
        hcy2).resolve_left hcy1)
    · rw [he] at hcy
      exact Or.inr ((hs.hu.unique _ (hs.hT₀.1 hcy) hcy2).resolve_left hcy1)
  have hwM : c * y * c⁻¹ ∈ Subgroup.closure ({t * u, t} : Set Y) ⊔
      oddCoreOf (layerY (CoreAssembly.conjClass (tightCore R)) (t * u)) := by
    refine Subgroup.mem_sup_left ?_
    rw [hs.aux_closure_eq]
    rcases hw with h | h <;> rw [h] <;> exact Subgroup.subset_closure (by simp)
  have hyM := (Subgroup.mem_normalizer_iff.mp (h1 (inv_mem hc)) _).mp hwM
  have e : c⁻¹ * (c * y * c⁻¹) * c⁻¹⁻¹ = y := by group
  rw [e] at hyM
  obtain ⟨e', he', o, ho, rfl⟩ := hs.aux_mem_sup hyM
  have heP : e' ∈ (P : Subgroup Y) := (hs.aux_E_le he').1.1
  have hoP : o ∈ (P : Subgroup Y) := by
    have h := mul_mem (inv_mem heP) hyP
    rwa [inv_mul_cancel_left] at h
  rw [aux_eq_one_of_mem_odd (P := P) (odd_natCard_oddCoreOf _) ho hoP, mul_one]
  exact he'

theorem Z2SetR.aux_commutes (hs : Z2SetR r n R S t J u R₀ T₀ P) : Commutes R₀ T₀ := by
  refine Q3CP.l67Gen Y _ hs.large.datum.hypOmegaGen P R₀
    (mem_RSet_of_isSylow2In (CoreAssembly.mem_conjClass_self _) hs.hR₀) T₀
    (mem_RSet_of_isSylow2In hs.hJ.1 hs.hT₀) hs.hR₀P hs.hT₀P ?_
  intro h
  have htT : t ∈ T₀ := h ▸ hs.aux_t_mem
  exact hs.aux_t_ne_u ((hs.hu.unique t (hs.hT₀.1 htT)
    hs.large.datum.isUniqueInvolution_core.sq).resolve_left
      hs.large.datum.isUniqueInvolution_core.ne_one)

theorem Z2SetR.aux_conj_R₀ (hs : Z2SetR r n R S t J u R₀ T₀ P) {w : Y}
    (hw : w ∈ (P : Subgroup Y)) (hwt : w * t * w⁻¹ = u) : conjSub w R₀ = T₀ := by
  have hΩ := hs.large.datum.hypOmegaGen
  have hR : conjSub w R₀ ∈ RSet (CoreAssembly.conjClass (tightCore R)) :=
    mem_RSet_of_isSylow2In (hΩ.conjInvariant w _ (CoreAssembly.mem_conjClass_self _))
      (hs.hR₀.conj w)
  have hle : conjSub w R₀ ≤ (P : Subgroup Y) := by
    intro x hx
    rw [mem_conjSub_iff] at hx
    have h := mul_mem (mul_mem hw (hs.hR₀P hx)) (inv_mem hw)
    simpa [mul_assoc] using h
  rcases hs.rSet_le hR hle with h | h
  · exfalso
    have hu : w * t * w⁻¹ ∈ conjSub w R₀ := conj_mem_conjSub hs.aux_t_mem w
    rw [h, hwt] at hu
    exact hs.aux_t_ne_u ((hs.large.datum.isUniqueInvolution_core.unique u (hs.hR₀.1 hu)
      hs.hu.sq).resolve_left hs.hu.ne_one).symm
  · exact h


theorem Z2SetR.aux_conj_u_b (hs : Z2SetR r n R S t J u R₀ T₀ P) {b : Y} (hb2 : b * b = 1)
    (hsw : b * t * b⁻¹ = u) : u * b * u⁻¹ = t * u * b := by
  have htu := hs.aux_tu
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hs.hu.sq
  have hub1 : u * b = b * t := by
    rw [← hsw]
    group
  have hbu : b * u * b⁻¹ = t := by
    rw [← hsw]
    calc b * (b * t * b⁻¹) * b⁻¹ = (b * b) * t * (b * b)⁻¹ := by group
      _ = t := by rw [hb2, one_mul, inv_one, mul_one]
  have hbu1 : b * u = t * b := by
    calc b * u = (b * u * b⁻¹) * b := by group
      _ = t * b := by rw [hbu]
  calc u * b * u⁻¹ = b * t * u⁻¹ := by rw [hub1]
    _ = b * t * u := by rw [hui]
    _ = b * (u * t) := by rw [mul_assoc, htu]
    _ = (b * u) * t := by group
    _ = t * b * t := by rw [hbu1]
    _ = t * (b * t) := by group
    _ = t * (u * b) := by rw [hub1]
    _ = t * u * b := by group

theorem Z2SetR.hfus_of_max (hs : Z2SetR r n R S t J u R₀ T₀ P)
    (h1 : C264One (CoreAssembly.conjClass (tightCore R)) t u)
    (hnc : ∀ b ∈ (P : Subgroup Y), b ∉ edgeCent (P : Subgroup Y) t u → b * b = 1 →
      ∀ g : Y, g * b * g⁻¹ ≠ t * u) {b : Y}
    (hbP : b ∈ (P : Subgroup Y)) (hbA : b ∉ edgeCent (P : Subgroup Y) t u) (hb2 : b * b = 1)
    (hmax : ∀ c ∈ (P : Subgroup Y), c ∉ edgeCent (P : Subgroup Y) t u → c * c = 1 →
      Nat.card ↥((P : Subgroup Y) ⊓ Subgroup.centralizer ({c} : Set Y)) ≤
        Nat.card ↥((P : Subgroup Y) ⊓ Subgroup.centralizer ({b} : Set Y))) :
    ∀ g : Y, (∀ y ∈ (P : Subgroup Y) ⊓ Subgroup.centralizer {b}, g⁻¹ * y * g ∈ (P : Subgroup Y)) →
      b⁻¹ * (g⁻¹ * b * g) ∈ edgeCent (P : Subgroup Y) t u := by
  intro g hg
  have hbD : b ∈ (P : Subgroup Y) ⊓ Subgroup.centralizer ({b} : Set Y) :=
    Subgroup.mem_inf.mpr ⟨hbP, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have heP : g⁻¹ * b * g ∈ (P : Subgroup Y) := hg b hbD
  obtain ⟨hsw, -⟩ := hs.aux_swap hbP hbA
  rcases hs.mem_or_mem_of_swap hbP hsw heP with heA | h
  swap
  · exact h
  exfalso
  have htu := hs.aux_tu
  have haP : t * u ∈ (P : Subgroup Y) := mul_mem hs.aux_t_P hs.aux_u_P
  have haZ : ∀ y ∈ (P : Subgroup Y), y * (t * u) = t * u * y := fun y hy => hs.comm_tu hy
  have hy'D : ∀ w ∈ (P : Subgroup Y) ⊓ Subgroup.centralizer ({b} : Set Y),
      g * (t * u) * g⁻¹ * w = w * (g * (t * u) * g⁻¹) := by
    intro w hw
    have h := haZ _ (hg w hw)
    calc g * (t * u) * g⁻¹ * w = g * ((t * u) * (g⁻¹ * w * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * w * g) * (t * u)) * g⁻¹ := by rw [← h]
      _ = w * (g * (t * u) * g⁻¹) := by group
  have haD : t * u ∈ (P : Subgroup Y) ⊓ Subgroup.centralizer ({b} : Set Y) :=
    Subgroup.mem_inf.mpr ⟨haP, Subgroup.mem_centralizer_singleton_iff.mpr (haZ b hbP).symm⟩
  have ha2 : (t * u) * (t * u) = 1 := by
    calc (t * u) * (t * u) = t * (u * t) * u := by group
      _ = t * (t * u) * u := by rw [htu]
      _ = (t * t) * (u * u) := by group
      _ = 1 := by rw [hs.large.datum.isUniqueInvolution_core.sq, hs.hu.sq, one_mul]
  have ha1 : t * u ≠ 1 := by
    intro h
    have h' := mul_eq_one_iff_eq_inv.mp h
    rw [inv_eq_of_mul_eq_one_right hs.hu.sq] at h'
    exact hs.aux_t_ne_u h'
  have hy'2 : (g * (t * u) * g⁻¹) * (g * (t * u) * g⁻¹) = 1 := by
    calc (g * (t * u) * g⁻¹) * (g * (t * u) * g⁻¹) = g * ((t * u) * (t * u)) * g⁻¹ := by group
      _ = 1 := by rw [ha2, mul_one, mul_inv_cancel]
  have hy'1 : g * (t * u) * g⁻¹ ≠ 1 := by
    intro h
    apply ha1
    calc t * u = g⁻¹ * (g * (t * u) * g⁻¹) * g := by group
      _ = 1 := by rw [h, mul_one, inv_mul_cancel]
  have hy'b : g * (t * u) * g⁻¹ * b = b * (g * (t * u) * g⁻¹) := hy'D b hbD
  by_cases hy' : g * (t * u) * g⁻¹ ∈ (P : Subgroup Y) ⊓ Subgroup.centralizer ({b} : Set Y)
  ·
    obtain ⟨hy'P, -⟩ := Subgroup.mem_inf.mp hy'
    rcases hs.eq_of_center_centralizer hbP hbA hb2 hy'P hy'b
      (fun y hy hyb => hy'D y
        (Subgroup.mem_inf.mpr ⟨hy, Subgroup.mem_centralizer_singleton_iff.mpr hyb⟩))
      hy'2 hy'1 with hz | hz | hz
    · have hga : g⁻¹ ∈ Subgroup.centralizer ({t * u} : Set Y) := by
        refine inv_mem (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
        calc g * (t * u) = (g * (t * u) * g⁻¹) * g := by group
          _ = t * u * g := by rw [hz]
      have hcg : g⁻¹ * b * g⁻¹⁻¹ ∈ (P : Subgroup Y) := by rwa [inv_inv]
      exact hbA ((hs.mem_edgeCent_iff_conj h1 hbP hga hcg).mpr (by rwa [inv_inv]))
    · refine hnc b hbP hbA hb2 g⁻¹ ?_
      calc g⁻¹ * b * g⁻¹⁻¹ = g⁻¹ * (g * (t * u) * g⁻¹) * g := by rw [hz, inv_inv]
        _ = t * u := by group
    · refine hnc b hbP hbA hb2 (g⁻¹ * u) ?_
      calc g⁻¹ * u * b * (g⁻¹ * u)⁻¹ = g⁻¹ * (u * b * u⁻¹) * g := by group
        _ = g⁻¹ * (g * (t * u) * g⁻¹) * g := by rw [hs.aux_conj_u_b hb2 hsw, hz]
        _ = t * u := by group
  ·
    have hD2 : IsPGroup 2 ↥((P : Subgroup Y) ⊓ Subgroup.centralizer ({b} : Set Y)) :=
      P.isPGroup'.to_le inf_le_left
    have hZ2 : IsPGroup 2 ↥(Subgroup.zpowers (g * (t * u) * g⁻¹)) := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact IsPGroup.of_card (n := 1) (by
        rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hy'2) hy'1, pow_one])
    have hZN : Subgroup.zpowers (g * (t * u) * g⁻¹) ≤ Subgroup.normalizer
        (((P : Subgroup Y) ⊓ Subgroup.centralizer ({b} : Set Y) : Subgroup Y) : Set Y) :=
      Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _
        (Subgroup.mem_centralizer_iff.mpr fun w hw => (hy'D w hw).symm))
    have hH2 := IsPGroup.to_sup_of_normal_right' hZ2 hD2 hZN
    have hy'a : g * (t * u) * g⁻¹ * (t * u) = t * u * (g * (t * u) * g⁻¹) := hy'D _ haD
    have hHa : Subgroup.zpowers (g * (t * u) * g⁻¹) ⊔
        ((P : Subgroup Y) ⊓ Subgroup.centralizer ({b} : Set Y)) ≤
          Subgroup.centralizer ({t * u} : Set Y) :=
      sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hy'a))
        (fun w hw => hs.aux_mem_cent_a (Subgroup.mem_inf.mp hw).1)
    have hHb : Subgroup.zpowers (g * (t * u) * g⁻¹) ⊔
        ((P : Subgroup Y) ⊓ Subgroup.centralizer ({b} : Set Y)) ≤
          Subgroup.centralizer ({b} : Set Y) :=
      sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hy'b))
        inf_le_right
    obtain ⟨c, hc, hcH⟩ := hs.exists_conj_le hH2 hHa
    have hcbP : c * b * c⁻¹ ∈ (P : Subgroup Y) :=
      hcH (conj_mem_conjSub (Subgroup.mem_sup_right hbD) c)
    have hcbA : c * b * c⁻¹ ∉ edgeCent (P : Subgroup Y) t u := fun h =>
      hbA ((hs.mem_edgeCent_iff_conj h1 hbP hc hcbP).mpr h)
    have hcb2 : (c * b * c⁻¹) * (c * b * c⁻¹) = 1 := by
      calc (c * b * c⁻¹) * (c * b * c⁻¹) = c * (b * b) * c⁻¹ := by group
        _ = 1 := by rw [hb2, mul_one, mul_inv_cancel]
    have hle := hmax _ hcbP hcbA hcb2
    have hsub : conjSub c (Subgroup.zpowers (g * (t * u) * g⁻¹) ⊔
        ((P : Subgroup Y) ⊓ Subgroup.centralizer ({b} : Set Y))) ≤
          (P : Subgroup Y) ⊓ Subgroup.centralizer ({c * b * c⁻¹} : Set Y) := by
      intro z hz
      refine Subgroup.mem_inf.mpr ⟨hcH hz, ?_⟩
      have hz' := hz
      rw [mem_conjSub_iff] at hz'
      have hzb := Subgroup.mem_centralizer_singleton_iff.mp (hHb hz')
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc z * (c * b * c⁻¹) = c * ((c⁻¹ * z * c) * b) * c⁻¹ := by group
        _ = c * (b * (c⁻¹ * z * c)) * c⁻¹ := by rw [hzb]
        _ = c * b * c⁻¹ * z := by group
    have hlt : (P : Subgroup Y) ⊓ Subgroup.centralizer ({b} : Set Y) <
        Subgroup.zpowers (g * (t * u) * g⁻¹) ⊔
          ((P : Subgroup Y) ⊓ Subgroup.centralizer ({b} : Set Y)) :=
      SetLike.lt_iff_le_and_exists.mpr
        ⟨le_sup_right, _, Subgroup.mem_sup_left (Subgroup.mem_zpowers _), hy'⟩
    have hc1 := Subgroup.card_lt_of_lt hlt
    have hc2 := Subgroup.card_le_of_le hsub
    have hc3 : Nat.card ↥(conjSub c (Subgroup.zpowers (g * (t * u) * g⁻¹) ⊔
        ((P : Subgroup Y) ⊓ Subgroup.centralizer ({b} : Set Y)))) =
          Nat.card ↥(Subgroup.zpowers (g * (t * u) * g⁻¹) ⊔
            ((P : Subgroup Y) ⊓ Subgroup.centralizer ({b} : Set Y))) :=
      Subgroup.card_map_of_injective (MulAut.conj c).injective
    omega

theorem z2BigProp7a_of_hweak_notConj {r n : ℕ} (hw : Z2BigHweak r n) (hnc : Z2BigNotConjTU r n) :
    Z2BigProp7a r n := by
  intro hr Y _ _ R S t J u R₀ T₀ P hs h1 hinv
  classical
  obtain ⟨b, ⟨hbP, hbA, hb2⟩, hmax⟩ := Set.exists_max_image
    {c : Y | c ∈ (P : Subgroup Y) ∧ c ∉ edgeCent (P : Subgroup Y) t u ∧ c * c = 1}
    (fun c => Nat.card ↥((P : Subgroup Y) ⊓ Subgroup.centralizer ({c} : Set Y)))
    (Set.toFinite _) (by obtain ⟨b, hb, hbA, hb2⟩ := hinv; exact ⟨b, hb, hbA, hb2⟩)
  exact LinkZ2B.false_of_transfer_tight hs.large.cls.2.1 hs.hR₀ P
    (fun y hy z hz => hs.commutator_mem hy hz) hbP hbA (by rw [sq, hb2])
    (hs.hfus_of_max h1 (hnc hr Y R S t J u R₀ T₀ P hs) hbP hbA hb2
      fun c hc hcA hc2 => hmax c ⟨hc, hcA, hc2⟩)
    (hw hr Y R S t J u R₀ T₀ P hs h1)

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
