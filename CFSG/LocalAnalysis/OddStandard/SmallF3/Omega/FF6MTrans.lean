module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MTransAux1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MCover
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CenterRes
public import CFSG.Quasithin.Background.C2Nine
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFInduces
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Struct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped commutatorElement

variable {G : Type} [Group G] {L : Subgroup G}

section Model

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff6m_centralizer_iff_eq_one (hq : CFSG.IsQuasisimple ↥L) (hQ : Q.Nondegenerate)
    (h5 : 5 ≤ Module.finrank (ZMod 3) V) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ)
    {s : G} {x : ProjSim Q} (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x) :
    s ∈ centralizer (L : Set G) ↔ x = 1 := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  constructor
  · intro hc
    apply ffSimOmegaAct_injective hQ h5
    rw [map_one]
    apply MulEquiv.ext
    intro w
    obtain ⟨l, rfl⟩ := ff6mPhi_surjective e w
    have hl' : s * (l : G) * s⁻¹ ∈ L := ff_conj_mem hs.1 l
    let l' : ↥L := ⟨s * (l : G) * s⁻¹, hl'⟩
    have key := ff6m_phi_conj hQ h2 e hs l l' rfl
    rw [key, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    show s * (l : G) * s⁻¹ = l
    rw [← Subgroup.mem_centralizer_iff.mp hc l l.2]
    group
  · intro hx
    set σ : MulAut ↥L := Subgroup.normalizerMonoidHom L ⟨s, hs.1⟩ with hσdef
    have h : ∀ y : ↥L, ff6mPhi e (σ y) = ff6mPhi e ((1 : MulAut ↥L) y) := by
      intro y
      rw [MulAut.one_apply]
      have key := ff6m_phi_conj hQ h2 e hs y (σ y) (by
        show (σ y : G) = s * y * s⁻¹
        rw [hσdef]; rfl)
      rw [hx, map_one, MulAut.one_apply] at key
      exact key.symm
    have hσ1 : σ = 1 :=
      mulAut_eq_of_map_eq_of_perfect (hker := by rw [ff6mPhi_ker])
        (hperf := hq.1.commutator_eq_top) h
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hconj : s * (l : G) * s⁻¹ = (l : G) := by
      have hh := congrArg (fun f : MulAut ↥L => f ⟨l, hl⟩) hσ1
      rw [MulAut.one_apply] at hh
      exact congrArg Subtype.val hh
    exact (mul_inv_eq_iff_eq_mul.mp hconj).symm

theorem ff6m_induces_sq (hQ : Q.Nondegenerate) (h5 : 5 ≤ Module.finrank (ZMod 3) V)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {s : G} {x : ProjSim Q}
    (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x) (hss : s * s = 1) : x * x = 1 := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  apply ffSimOmegaAct_injective hQ h5
  rw [map_mul, map_one]
  apply MulEquiv.ext
  intro w
  obtain ⟨l, rfl⟩ := ff6mPhi_surjective e w
  have hl : s * (l : G) * s⁻¹ ∈ L := ff_conj_mem hs.1 l
  let l' : ↥L := ⟨s * (l : G) * s⁻¹, hl⟩
  have hl2 : s * (l' : G) * s⁻¹ ∈ L := ff_conj_mem hs.1 l'
  have k1 := ff6m_phi_conj hQ h2 e hs l l' rfl
  have k2 := ff6m_phi_conj hQ h2 e hs l' ⟨_, hl2⟩ rfl
  rw [MulAut.mul_apply, k1, k2, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  show s * (s * (l : G) * s⁻¹) * s⁻¹ = l
  calc s * (s * (l : G) * s⁻¹) * s⁻¹ = (s * s) * (l : G) * (s * s)⁻¹ := by group
    _ = l := by rw [hss]; group

theorem ff6m_induces_of_mem (hQ : Q.Nondegenerate)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {u : G} (hu : u ∈ L) :
    InducesViaP L (Subgroup.center ↥L) hQ e u
      (projOrthToProjSim Q ((ff6mPhi e ⟨u, hu⟩ : ↥(omegaProj hQ)) : ProjOrth Q)) := by
  refine ⟨Subgroup.le_normalizer hu, ?_⟩
  intro l l' hl
  rw [projSimAct_projOrthToProjSim]
  have hl' : l' = ⟨u, hu⟩ * l * ⟨u, hu⟩⁻¹ := Subtype.ext hl
  have h1 : e (QuotientGroup.mk l') = ff6mPhi e ⟨u, hu⟩ * e (QuotientGroup.mk l) *
      (ff6mPhi e ⟨u, hu⟩)⁻¹ := by
    rw [hl', ff6mPhi_apply]
    simp
  rw [h1]
  rfl

theorem ff6m_innerOn_iff (hq : CFSG.IsQuasisimple ↥L) (hQ : Q.Nondegenerate)
    (h5 : 5 ≤ Module.finrank (ZMod 3) V) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ)
    {s : G} {x : ProjSim Q} (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x) :
    InnerOn L s ↔ SimInOmegaStar hQ x := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  constructor
  · intro hin
    obtain ⟨l, hl, c, hc, rfl⟩ := ff_innerOn_decompose hin
    have hI := ff6m_induces_of_mem hQ e hl
    have hIs : InducesViaP L (Subgroup.center ↥L) hQ e (l * c)
        (projOrthToProjSim Q (((ff6mPhi e ⟨l, hl⟩ : ↥(omegaProj hQ)) : ProjOrth Q))) := by
      refine ⟨mul_mem (Subgroup.le_normalizer hl)
        (Subgroup.centralizer_le_normalizer (L : Set G) hc), ?_⟩
      intro m m' hm'
      have hmk : (m' : G) = (l : G) * m * (l : G)⁻¹ := by
        rw [hm']
        have hcm : c * (m : G) = (m : G) * c :=
          (Subgroup.mem_centralizer_iff.mp hc m m.2).symm
        calc (l * c) * (m : G) * (l * c)⁻¹
            = (l : G) * (c * (m : G) * c⁻¹) * (l : G)⁻¹ := by group
          _ = (l : G) * (m : G) * (l : G)⁻¹ := by rw [hcm]; group
      exact hI.2 m m' hmk
    have hxeq := ff_induces_unique hQ h5 e hs hIs
    exact ⟨ff6mPhi e ⟨l, hl⟩, (ff6mPhi e ⟨l, hl⟩).2, hxeq.symm⟩
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨l, hl⟩ := ff6mPhi_surjective e ⟨y, hy⟩
    have hx' : x = projOrthToProjSim Q (((ff6mPhi e l : ↥(omegaProj hQ)) : ProjOrth Q)) := by
      rw [← hxy]
      exact congrArg (projOrthToProjSim Q) (congrArg Subtype.val hl).symm
    have hI := ff6m_induces_of_mem hQ e l.2
    have hσ : ∀ z : ↥L, ff6mPhi e (Subgroup.normalizerMonoidHom L ⟨s, hs.1⟩ z) =
        ff6mPhi e (Subgroup.normalizerMonoidHom L ⟨(l : G), Subgroup.le_normalizer l.2⟩ z) := by
      intro z
      have k1 := ff6m_phi_conj hQ h2 e hs z (Subgroup.normalizerMonoidHom L ⟨s, hs.1⟩ z) (by
        show ((Subgroup.normalizerMonoidHom L ⟨s, hs.1⟩) z : G) = s * z * s⁻¹
        rfl)
      have k2 := ff6m_phi_conj hQ h2 e hI z
        (Subgroup.normalizerMonoidHom L ⟨(l : G), Subgroup.le_normalizer l.2⟩ z) (by
        show ((Subgroup.normalizerMonoidHom L ⟨(l : G), Subgroup.le_normalizer l.2⟩) z : G)
            = (l : G) * z * (l : G)⁻¹
        rfl)
      have hx'' : ffSimOmegaAct hQ h2 x (ff6mPhi e z) =
          ffSimOmegaAct hQ h2 (projOrthToProjSim Q (((ff6mPhi e l : ↥(omegaProj hQ)) : ProjOrth Q)))
            (ff6mPhi e z) :=
        congrArg (fun f : MulAut ↥(omegaProj hQ) => f (ff6mPhi e z))
          (congrArg (ffSimOmegaAct hQ h2) hx')
      exact k1.symm.trans (hx''.trans k2)
    have hστ := mulAut_eq_of_map_eq_of_perfect (hker := by rw [ff6mPhi_ker])
      (hperf := hq.1.commutator_eq_top) hσ
    have hcentral : (l : G)⁻¹ * s ∈ centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      have hconjG : s * (m : G) * s⁻¹ = (l : G) * (m : G) * (l : G)⁻¹ := by
        have hh := congrArg (fun f : MulAut ↥L => f ⟨m, hm⟩) hστ
        exact congrArg Subtype.val hh
      have hmul : ((l : G)⁻¹ * s) * (m : G) * ((l : G)⁻¹ * s)⁻¹ = (m : G) := by
        have h1 : ((l : G)⁻¹ * s) * (m : G) * ((l : G)⁻¹ * s)⁻¹
            = (l : G)⁻¹ * (s * (m : G) * s⁻¹) * (l : G) := by group
        rw [h1, hconjG]; group
      exact (mul_inv_eq_iff_eq_mul.mp hmul).symm
    have hs_eq : s = (l : G) * ((l : G)⁻¹ * s) := by group
    show s ∈ L ⊔ centralizer (L : Set G)
    rw [hs_eq]
    exact Subgroup.mul_mem_sup l.2 hcentral

theorem ff6m_mem_conjClass_iff (hQ : Q.Nondegenerate)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ)
    (hodd : Odd (Nat.card (Subgroup.center ↥L))) {u u' : G} (hu : u ∈ L) (hu' : u' ∈ L)
    (hu2 : u * u = 1) (hu2' : u' * u' = 1) :
    u' ∈ conjClassIn L u ↔
      ∃ a : ↥(omegaProj hQ), a * ff6mPhi e ⟨u, hu⟩ * a⁻¹ = ff6mPhi e ⟨u', hu'⟩ := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    refine ⟨ff6mPhi e ⟨h, hh⟩, ?_⟩
    have hmk : (⟨h * u * h⁻¹, hu'⟩ : ↥L) = ⟨h, hh⟩ * ⟨u, hu⟩ * ⟨h, hh⟩⁻¹ := rfl
    rw [hmk, map_mul, map_mul, map_inv]
  · rintro ⟨a, ha⟩
    obtain ⟨h, rfl⟩ := ff6mPhi_surjective e a
    set a' : ↥L := ⟨(h : G) * u * (h : G)⁻¹,
      L.mul_mem (L.mul_mem h.2 hu) (L.inv_mem h.2)⟩ with ha'def
    have hsplit : a' = ⟨h, h.2⟩ * ⟨u, hu⟩ * ⟨h, h.2⟩⁻¹ := Subtype.ext rfl
    have ha'2 : a' * a' = 1 := by
      apply Subtype.ext
      rw [hsplit]
      show (h : G) * u * (h : G)⁻¹ * ((h : G) * u * (h : G)⁻¹) = 1
      rw [show (h : G) * u * (h : G)⁻¹ * ((h : G) * u * (h : G)⁻¹)
          = (h : G) * (u * u) * (h : G)⁻¹ from by group, hu2]
      group
    have hphi : ff6mPhi e a' = ff6mPhi e ⟨u', hu'⟩ := by
      rw [hsplit, map_mul, map_mul, map_inv]
      exact ha
    have hu2'' : (⟨u', hu'⟩ : ↥L) * ⟨u', hu'⟩ = 1 := Subtype.ext hu2'
    have heq : a' = ⟨u', hu'⟩ :=
      (ff6m_phi_cover e hodd).eq_of_mul_self_eq_one ha'2 hu2'' hphi
    exact ⟨h, h.2, (congrArg Subtype.val heq).symm⟩

theorem ff6m_ex_u_of_cover [Finite G] (hQ : Q.Nondegenerate)
    (h5 : 5 ≤ Module.finrank (ZMod 3) V) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ)
    (hodd : Odd (Nat.card (Subgroup.center ↥L))) {s : G} {x : ProjSim Q}
    (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x) (hss : s * s = 1)
    (hcov : ∃ w : ↥(omegaProj hQ), w ∈ twoRes (ffFix hQ (by omega) x) ∧ w * w = 1 ∧ w ≠ 1 ∧
      ∃ a : ↥(omegaProj hQ), ffSimOmegaAct hQ (by omega) x a * a⁻¹ = w) :
    ∃ u ∈ twoRes (L ⊓ centralizer ({s} : Set G)), orderOf u = 2 ∧ s * u ∈ conjClassIn L s := by
  obtain ⟨w, hwmem, hw2, hw1, ⟨a, ha⟩⟩ := hcov
  obtain ⟨ρ, hρ, hρeq⟩ := ff6m_exists_centCover hQ (by omega) e hodd hs hss
  have hwmap : w ∈ (twoRes (⊤ : Subgroup ↥(ffFix hQ (by omega) x))).map
      (ffFix hQ (by omega) x).subtype := by
    rw [← ff_twoRes_eq_map (ffFix hQ (by omega) x)]
    exact hwmem
  obtain ⟨w₀, hw₀, hw₀eq⟩ := Subgroup.mem_map.mp hwmap
  have hw2₀ : w₀ * w₀ = 1 := by
    apply Subtype.ext
    have h : ((w₀ : ↥(ffFix hQ (by omega) x)) : ↥(omegaProj hQ)) = w := hw₀eq
    rw [Subgroup.coe_mul, Subgroup.coe_one, h, hw2]
  obtain ⟨u, hu, hu2res, hu2, hρu⟩ := ff6m_cover_lift_involution_in hρ hw₀ hw2₀
  refine ⟨u, hu2res, ?_, ?_⟩
  · have hu1 : u ≠ 1 := by
      intro h1
      apply hw1
      have hsub : (⟨u, hu⟩ : ↥(L ⊓ centralizer ({s} : Set G))) = 1 := Subtype.ext h1
      calc w = (ffFix hQ (by omega) x).subtype w₀ := hw₀eq.symm
        _ = (ffFix hQ (by omega) x).subtype (ρ ⟨u, hu⟩) := by rw [← hρu]
        _ = (ffFix hQ (by omega) x).subtype (ρ 1) := by rw [hsub]
        _ = (ffFix hQ (by omega) x).subtype 1 := by rw [map_one]
        _ = 1 := rfl
    have hu2' : u ^ 2 = 1 := by rw [pow_two, hu2]
    exact orderOf_eq_prime hu2' hu1
  · refine (ff6m_cover_iff hQ (by omega) e hodd hs hss (Subgroup.mem_inf.mp hu).1
      (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hu).2).symm hu2).mpr ⟨a, ?_⟩
    have hcoh : ((ρ ⟨u, hu⟩ : ↥(ffFix hQ (by omega) x)) : ↥(omegaProj hQ)) =
        ff6mPhi e ⟨u, (Subgroup.mem_inf.mp hu).1⟩ := hρeq ⟨u, hu⟩
    have hw_eq : ((w₀ : ↥(ffFix hQ (by omega) x)) : ↥(omegaProj hQ)) = w := hw₀eq
    rw [← hcoh, congrArg Subtype.val hρu, hw_eq]
    exact ha

theorem ff6m_phi_involution (hQ : Q.Nondegenerate)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ)
    (hodd : Odd (Nat.card (Subgroup.center ↥L))) {u : G} (hu : u ∈ L) (hu2 : orderOf u = 2) :
    ff6mPhi e ⟨u, hu⟩ * ff6mPhi e ⟨u, hu⟩ = 1 ∧ ff6mPhi e ⟨u, hu⟩ ≠ 1 := by
  have huu : (⟨u, hu⟩ : ↥L) * ⟨u, hu⟩ = 1 := by
    apply Subtype.ext
    show u * u = 1
    rw [← pow_two, ← hu2]
    exact pow_orderOf_eq_one u
  refine ⟨?_, ?_⟩
  · rw [← map_mul, huu, map_one]
  · intro h1
    have hker : (⟨u, hu⟩ : ↥L) ∈ (ff6mPhi e).ker := by
      rw [MonoidHom.mem_ker]; exact h1
    have heq : (⟨u, hu⟩ : ↥L) = 1 :=
      (ff6m_phi_cover e hodd).eq_one_of_mul_self_eq_one hker huu
    have hu1 : u = 1 := congrArg Subtype.val heq
    rw [hu1, orderOf_one] at hu2
    norm_num at hu2

end Model

theorem ff6m_central_layer [Finite G] (h : IsOm6M L) {s : G}
    (hs : s ∈ centralizer (L : Set G)) : layerCent L s ≠ ⊥ ∧ XOut L s = layerCent L s := by
  obtain ⟨V, _, _, _, Q, hQ, hdim, hsgn, ⟨e⟩⟩ := ff_isOmegaStar_center_six_minus h
  have hcard : Nat.card (↥L ⧸ Subgroup.center ↥L) = 3265920 := by
    rw [Nat.card_congr e.toEquiv, ff_natCard_omegaProj_six_minus hQ hdim hsgn]
  have h2 : 2 ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := by rw [hcard]; norm_num
  have hC : L ⊓ centralizer ({s} : Set G) = L := by
    rw [inf_eq_left]
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hs x hx
  refine ⟨sec5_layerCent_ne_bot_of_mem_centralizer h.1 hs, ?_⟩
  have hL : layerCent L s = L := sec5_layerCent_of_mem_centralizer h.1 hs
  rw [XOut, hC, hL]
  have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp h.1.1
  have htwo : twoRes L = L := CFSG.Quasithin.C2Nine.oTwoUpper_eq_of_perfect hperf
  have htwo' : twoPrimeRes L = L := sec5_twoPrimeRes_eq_self h.1 h2
  rw [htwo, htwo']

theorem ff6m_odd_center [Finite G] (h : IsOm6M L) : Odd (Nat.card (Subgroup.center ↥L)) := by
  rw [ff_center_eq_oddCore_six_minus h]
  exact ff_odd_card_oddCore ↥L

theorem ff6m_exists_model [Finite G] (h : IsOm6M L) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V) (_ : FiniteDimensional (ZMod 3) V)
      (Q : QuadraticForm (ZMod 3) V) (hQ : Q.Nondegenerate)
      (_ : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ),
      Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1 := by
  obtain ⟨V, _, _, _, Q, hQ, hdim, hsgn, ⟨e⟩⟩ := ff_isOmegaStar_center_six_minus h
  exact ⟨V, inferInstance, inferInstance, inferInstance, Q, hQ, e, hdim, hsgn⟩

end CFSG.OddStandard.SmallF3.Omega
