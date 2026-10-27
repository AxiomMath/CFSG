module

public import Certificates.Certificate442267
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.A6Concl
public import CFSG.Quasithin.Background.SmithB45HatA6Six
public import CFSG.Quasithin.Background.SmithB45HatA6Mono
public import CFSG.Quasithin.Background.E3Transport
public import CFSG.Quasithin.Vol2.Ch3Sec2Prop329
public import CFSG.Quasithin.Background.InternalSecISec

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup Certificates.Asc82NormA6 CFSG.Quasithin CFSG.Quasithin.H13.Ch4.E443
  CFSG.Quasithin.H13.Prop329 CFSG.Blueprint
open Certificates.A5GL42 (Mat4)
open scoped Matrix IsMulCommutative

private def Rm (F : Facts) : Equiv.Perm (Fin 6) →* Mat4 where
  toFun := rho
  map_one' := F.rho_one
  map_mul' := F.rho_mul

private def R (F : Facts) : Equiv.Perm (Fin 6) →* GL (Fin 4) (ZMod 2) := (Rm F).toHomUnits

private theorem R_coe (F : Facts) (p : Equiv.Perm (Fin 6)) :
    ((R F p : GL (Fin 4) (ZMod 2)) : Mat4) = rho p := rfl

private theorem R_injective (F : Facts) : Function.Injective (R F) := by
  rw [injective_iff_map_eq_one]
  intro p hp
  apply F.rho_ker p
  have h : ((R F p : GL (Fin 4) (ZMod 2)) : Mat4) = 1 := by rw [hp]; rfl
  rwa [R_coe] at h

private def rhoA6 (F : Facts) : Subgroup (GL (Fin 4) (ZMod 2)) :=
  (alternatingGroup (Fin 6)).map (R F)

private theorem rel_map {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) {x y : M}
    (h : Rel x y) : Rel (f x) (f y) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨by simpa using congrArg f h1, by simpa using congrArg f h2,
    by simpa using congrArg f h3, by simpa using congrArg f h4,
    by simpa using congrArg f h5, by simpa using congrArg f h6⟩

private def sigmaA (F : Facts) : ↥(alternatingGroup (Fin 6)) :=
  ⟨sigma, Equiv.Perm.mem_alternatingGroup.mpr F.sigma_even⟩

private def tauA (F : Facts) : ↥(alternatingGroup (Fin 6)) :=
  ⟨tau, Equiv.Perm.mem_alternatingGroup.mpr F.tau_even⟩

private theorem rel_sigmaA_tauA (F : Facts) : Rel (sigmaA F) (tauA F) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := F.rel
  refine ⟨Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_,
    Subtype.ext ?_⟩
  · simpa [sigmaA] using h1
  · simpa [tauA] using h2
  · simpa [sigmaA, tauA] using h3
  · simpa [sigmaA, tauA] using h4
  · simpa [sigmaA, tauA] using h5
  · simpa [sigmaA, tauA] using h6

private theorem closure_sigmaA_tauA_eq_top (F : Facts) :
    Subgroup.closure ({sigmaA F, tauA F} : Set ↥(alternatingGroup (Fin 6))) = ⊤ := by
  apply le_antisymm le_top
  intro m _
  have hle : Subgroup.closure ({sigma, tau} : Set (Equiv.Perm (Fin 6))) ≤
      (Subgroup.closure ({sigmaA F, tauA F} : Set ↥(alternatingGroup (Fin 6)))).map
        (alternatingGroup (Fin 6)).subtype := by
    rw [Subgroup.closure_le]
    rintro p (rfl | rfl)
    · exact Subgroup.mem_map.mpr ⟨sigmaA F, Subgroup.subset_closure (by simp), rfl⟩
    · exact Subgroup.mem_map.mpr ⟨tauA F, Subgroup.subset_closure (by simp), rfl⟩
  have hgen := F.gen m.1 (Equiv.Perm.mem_alternatingGroup.mp m.2)
  obtain ⟨n, hn, hnm⟩ := Subgroup.mem_map.mp (hle hgen)
  have hnm' : n = m := Subtype.ext hnm
  rwa [hnm'] at hn

private theorem exists_conj_eq_of_a6 (F : Facts) (H : Subgroup (GL (Fin 4) (ZMod 2)))
    (hH : Nonempty (↥H ≃* alternatingGroup (Fin 6))) :
    ∃ g : GL (Fin 4) (ZMod 2), H = (rhoA6 F).map (MulAut.conj g).toMonoidHom := by
  let ι : ↥(alternatingGroup (Fin 6)) ≃* ↥H := hH.some.symm
  have hcardH : Nat.card ↥H = 360 := by
    rw [(Nat.card_congr ι.toEquiv).symm, card_alt6]
  have hcardR : Nat.card ↥(rhoA6 F) = 360 := by
    rw [rhoA6, Subgroup.card_map_of_injective (R_injective F), card_alt6]
  set X : GL (Fin 4) (ZMod 2) := H.subtype (ι (sigmaA F)) with hX
  set Y : GL (Fin 4) (ZMod 2) := H.subtype (ι (tauA F)) with hY
  have hrelH : Rel (ι (sigmaA F)) (ι (tauA F)) := rel_map ι.toMonoidHom (rel_sigmaA_tauA F)
  have hrelM : Rel ((Units.coeHom Mat4) (H.subtype (ι (sigmaA F))))
      ((Units.coeHom Mat4) (H.subtype (ι (tauA F)))) :=
    rel_map ((Units.coeHom Mat4).comp H.subtype) hrelH
  have hX1 : ((Units.coeHom Mat4) (H.subtype (ι (sigmaA F)))) ≠ 1 := by
    intro h
    have h1 : H.subtype (ι (sigmaA F)) = 1 := Units.ext h
    have h2 : (ι (sigmaA F) : ↥H) = 1 := Subtype.ext h1
    have h3 : sigmaA F = 1 := ι.injective (by rw [h2, map_one])
    have h4 : sigma = 1 := congrArg Subtype.val h3
    exact absurd h4 (by decide +kernel)
  obtain ⟨c, c', hcc', ⟨a, ha, haeq⟩, ⟨b, hb, hbeq⟩⟩ :=
    F.classify _ _ hrelM hX1
  let g : GL (Fin 4) (ZMod 2) := ⟨c, c', hcc', mul_eq_one_comm.mp hcc'⟩
  have hgx : g⁻¹ * X * g = R F a := by
    apply Units.ext
    change c' * (X : Mat4) * c = rho a
    rw [haeq]
    rfl
  have hgy : g⁻¹ * Y * g = R F b := by
    apply Units.ext
    change c' * (Y : Mat4) * c = rho b
    rw [hbeq]
    rfl
  have hgen : Subgroup.closure ({X, Y} : Set (GL (Fin 4) (ZMod 2))) = H := by
    have hmap : Subgroup.closure ({X, Y} : Set (GL (Fin 4) (ZMod 2))) =
        (Subgroup.closure ({sigmaA F, tauA F} : Set ↥(alternatingGroup (Fin 6)))).map
          (H.subtype.comp ι.toMonoidHom) := by
      rw [MonoidHom.map_closure, Set.image_pair]
      rfl
    rw [hmap, closure_sigmaA_tauA_eq_top F, ← MonoidHom.range_eq_map]
    ext z
    constructor
    · rintro ⟨m, rfl⟩
      exact (ι m).2
    · intro hz
      exact ⟨ι.symm ⟨z, hz⟩, by simp⟩
  have hle : H.map (MulAut.conj g⁻¹).toMonoidHom ≤ rhoA6 F := by
    rw [← hgen, MonoidHom.map_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro z ⟨y, hy, rfl⟩
    rcases hy with rfl | rfl
    · have hz : MulAut.conj g⁻¹ X = R F a := by
        rw [MulAut.conj_apply]
        simpa using hgx
      rw [show (MulEquiv.toMonoidHom (MulAut.conj g⁻¹)) X = R F a from hz]
      exact Subgroup.mem_map.mpr ⟨a, by rw [Equiv.Perm.mem_alternatingGroup]; exact ha, rfl⟩
    · have hz : MulAut.conj g⁻¹ Y = R F b := by
        rw [MulAut.conj_apply]
        simpa using hgy
      rw [show (MulEquiv.toMonoidHom (MulAut.conj g⁻¹)) Y = R F b from hz]
      exact Subgroup.mem_map.mpr ⟨b, by rw [Equiv.Perm.mem_alternatingGroup]; exact hb, rfl⟩
  have heq : H.map (MulAut.conj g⁻¹).toMonoidHom = rhoA6 F := by
    have hcard : Nat.card ↥(H.map (MulAut.conj g⁻¹).toMonoidHom) = Nat.card ↥(rhoA6 F) := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hcardH, hcardR]
    exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  have hconj : H = (rhoA6 F).map (MulAut.conj g).toMonoidHom := by
    have h := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) heq
    rw [Subgroup.map_map] at h
    have hid : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
        MonoidHom.id (GL (Fin 4) (ZMod 2)) :=
      MonoidHom.ext fun x => by
        show MulAut.conj g (MulAut.conj g⁻¹ x) = x
        rw [MulAut.conj_apply, MulAut.conj_apply]
        group
    rw [hid, Subgroup.map_id] at h
    exact h
  exact ⟨g, hconj⟩


private noncomputable abbrev Psi : MulAut (Multiplicative (Fin 4 → ZMod 2)) ≃* GL (Fin 4) (ZMod 2) :=
  CFSG.SectionRank.Ccomm.mulAutEquivGL 4

private def k1 : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 2 3

private def k2 : Equiv.Perm (Fin 6) := Equiv.swap 2 3 * Equiv.swap 4 5

private def v1 : Fin 4 → ZMod 2 := ![1, 1, 0, 0]

private def v2 : Fin 4 → ZMod 2 := ![0, 0, 1, 1]

private theorem k1_mem : k1 ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

private theorem k2_mem : k2 ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

private theorem k1_sq : k1 * k1 = 1 := by decide +kernel
private theorem k2_sq : k2 * k2 = 1 := by decide +kernel
private theorem k1_comm_k2 : k1 * k2 = k2 * k1 := by decide +kernel
private theorem k1_ne_one : k1 ≠ 1 := by decide +kernel
private theorem k2_ne_one : k2 ≠ 1 := by decide +kernel
private theorem k1_ne_k2 : k1 ≠ k2 := by decide +kernel

private theorem rho_k1_fix_v1 : rho k1 *ᵥ v1 = v1 := by decide +kernel
private theorem rho_k2_fix_v1 : rho k2 *ᵥ v1 = v1 := by decide +kernel
private theorem rho_k1_fix_v2 : rho k1 *ᵥ v2 = v2 := by decide +kernel
private theorem rho_k2_fix_v2 : rho k2 *ᵥ v2 = v2 := by decide +kernel

private theorem isFFModule_rhoA6 (F : Facts) :
    IsFFModule (V := Multiplicative (Fin 4 → ZMod 2))
      ((rhoA6 F).map Psi.symm.toMonoidHom) := by
  let a : MulAut (Multiplicative (Fin 4 → ZMod 2)) := Psi.symm (R F k1)
  let b : MulAut (Multiplicative (Fin 4 → ZMod 2)) := Psi.symm (R F k2)
  have ha2 : a * a = 1 := by
    have h1 : R F k1 * R F k1 = 1 := by rw [← map_mul, k1_sq, map_one]
    calc a * a = Psi.symm (R F k1 * R F k1) := (map_mul Psi.symm _ _).symm
      _ = 1 := by rw [h1, map_one]
  have hb2 : b * b = 1 := by
    have h1 : R F k2 * R F k2 = 1 := by rw [← map_mul, k2_sq, map_one]
    calc b * b = Psi.symm (R F k2 * R F k2) := (map_mul Psi.symm _ _).symm
      _ = 1 := by rw [h1, map_one]
  have hcommR : R F k1 * R F k2 = R F k2 * R F k1 := by
    rw [← map_mul, ← map_mul, k1_comm_k2]
  have hab : a * b = b * a := by
    calc a * b = Psi.symm (R F k1 * R F k2) := (map_mul Psi.symm _ _).symm
      _ = Psi.symm (R F k2 * R F k1) := by rw [hcommR]
      _ = b * a := map_mul Psi.symm _ _
  have ha1 : a ≠ 1 := by
    intro h
    have h3 : Psi a = Psi 1 := congrArg Psi h
    rw [show Psi a = R F k1 from MulEquiv.apply_symm_apply Psi (R F k1), map_one] at h3
    exact k1_ne_one (R_injective F (by rw [h3, map_one]))
  have hb1 : b ≠ 1 := by
    intro h
    have h3 : Psi b = Psi 1 := congrArg Psi h
    rw [show Psi b = R F k2 from MulEquiv.apply_symm_apply Psi (R F k2), map_one] at h3
    exact k2_ne_one (R_injective F (by rw [h3, map_one]))
  have hne : a ≠ b := by
    intro h
    have h3 : Psi a = Psi b := congrArg Psi h
    rw [show Psi a = R F k1 from MulEquiv.apply_symm_apply Psi (R F k1),
      show Psi b = R F k2 from MulEquiv.apply_symm_apply Psi (R F k2)] at h3
    exact k1_ne_k2 (R_injective F h3)
  have hAle : Subgroup.closure ({a, b} : Set (MulAut (Multiplicative (Fin 4 → ZMod 2)))) ≤
      (rhoA6 F).map Psi.symm.toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.mem_map.mpr ⟨R F k1, Subgroup.mem_map.mpr ⟨k1, k1_mem, rfl⟩, rfl⟩
    · exact Subgroup.mem_map.mpr ⟨R F k2, Subgroup.mem_map.mpr ⟨k2, k2_mem, rfl⟩, rfl⟩
  have hAe : CFSG.Quasithin.IsElemAbelian2
      (Subgroup.closure ({a, b} : Set (MulAut (Multiplicative (Fin 4 → ZMod 2))))) :=
    CFSG.Quasithin.B45HatA6.isElemAbelian2_closure_pair ha2 hb2 hab
  have hA4 : Nat.card (Subgroup.closure ({a, b} : Set (MulAut (Multiplicative (Fin 4 → ZMod 2))))) = 4 :=
    CFSG.Quasithin.B45HatA6.card_closure_pair_eq_four ha2 hb2 hab ha1 hb1 hne
  have hA1 : Subgroup.closure ({a, b} : Set (MulAut (Multiplicative (Fin 4 → ZMod 2)))) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hA4
    norm_num at hA4
  have hPsi_a : ((Psi a : GL (Fin 4) (ZMod 2)) : Mat4) = rho k1 := by
    rw [show Psi a = R F k1 from MulEquiv.apply_symm_apply Psi (R F k1)]
    exact R_coe F k1
  have hPsi_b : ((Psi b : GL (Fin 4) (ZMod 2)) : Mat4) = rho k2 := by
    rw [show Psi b = R F k2 from MulEquiv.apply_symm_apply Psi (R F k2)]
    exact R_coe F k2
  have hfixa1 : a (Multiplicative.ofAdd v1) = Multiplicative.ofAdd v1 := by
    apply Multiplicative.toAdd.injective
    rw [← CFSG.SectionRank.Ccomm.mulAutEquivGL_mulVec 4 a v1, hPsi_a]
    simpa using rho_k1_fix_v1
  have hfixb1 : b (Multiplicative.ofAdd v1) = Multiplicative.ofAdd v1 := by
    apply Multiplicative.toAdd.injective
    rw [← CFSG.SectionRank.Ccomm.mulAutEquivGL_mulVec 4 b v1, hPsi_b]
    simpa using rho_k2_fix_v1
  have hfixa2 : a (Multiplicative.ofAdd v2) = Multiplicative.ofAdd v2 := by
    apply Multiplicative.toAdd.injective
    rw [← CFSG.SectionRank.Ccomm.mulAutEquivGL_mulVec 4 a v2, hPsi_a]
    simpa using rho_k1_fix_v2
  have hfixb2 : b (Multiplicative.ofAdd v2) = Multiplicative.ofAdd v2 := by
    apply Multiplicative.toAdd.injective
    rw [← CFSG.SectionRank.Ccomm.mulAutEquivGL_mulVec 4 b v2, hPsi_b]
    simpa using rho_k2_fix_v2
  have hv1 : Multiplicative.ofAdd v1 ∈
      fixV (Subgroup.closure ({a, b} : Set (MulAut (Multiplicative (Fin 4 → ZMod 2))))) := by
    rw [CFSG.Quasithin.B45HatA6.mem_fixV_closure_pair]
    exact ⟨hfixa1, hfixb1⟩
  have hv2 : Multiplicative.ofAdd v2 ∈
      fixV (Subgroup.closure ({a, b} : Set (MulAut (Multiplicative (Fin 4 → ZMod 2))))) := by
    rw [CFSG.Quasithin.B45HatA6.mem_fixV_closure_pair]
    exact ⟨hfixa2, hfixb2⟩
  have hw1sq : Multiplicative.ofAdd v1 * Multiplicative.ofAdd v1 = 1 := by
    rw [← ofAdd_add, CFSG.Quasithin.KGC31.add_self_zmod2, ofAdd_zero]
  have hw2sq : Multiplicative.ofAdd v2 * Multiplicative.ofAdd v2 = 1 := by
    rw [← ofAdd_add, CFSG.Quasithin.KGC31.add_self_zmod2, ofAdd_zero]
  have hw12 : Multiplicative.ofAdd v1 * Multiplicative.ofAdd v2 =
      Multiplicative.ofAdd v2 * Multiplicative.ofAdd v1 := mul_comm _ _
  have hw1ne : Multiplicative.ofAdd v1 ≠ 1 := by
    intro h
    have h' : v1 = 0 := Multiplicative.ofAdd.injective (by simpa using h)
    revert h'
    decide +kernel
  have hw2ne : Multiplicative.ofAdd v2 ≠ 1 := by
    intro h
    have h' : v2 = 0 := Multiplicative.ofAdd.injective (by simpa using h)
    revert h'
    decide +kernel
  have hwne : Multiplicative.ofAdd v1 ≠ Multiplicative.ofAdd v2 := by
    intro h
    have h' : v1 = v2 := Multiplicative.ofAdd.injective h
    revert h'
    decide +kernel
  have hW4 : Nat.card (Subgroup.closure ({Multiplicative.ofAdd v1, Multiplicative.ofAdd v2} :
      Set (Multiplicative (Fin 4 → ZMod 2)))) = 4 :=
    CFSG.Quasithin.B45HatA6.card_closure_pair_eq_four hw1sq hw2sq hw12 hw1ne hw2ne hwne
  have hleW : Subgroup.closure ({Multiplicative.ofAdd v1, Multiplicative.ofAdd v2} :
      Set (Multiplicative (Fin 4 → ZMod 2))) ≤
      fixV (Subgroup.closure ({a, b} : Set (MulAut (Multiplicative (Fin 4 → ZMod 2))))) := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hv1
    · exact hv2
  have h4fix : 4 ≤ Nat.card (fixV (Subgroup.closure ({a, b} :
      Set (MulAut (Multiplicative (Fin 4 → ZMod 2)))))) := by
    have hcard := Subgroup.card_le_of_le hleW
    rwa [hW4] at hcard
  refine ⟨Subgroup.closure ({a, b} : Set (MulAut (Multiplicative (Fin 4 → ZMod 2)))), hAle,
    hA1, hAe, ?_⟩
  have hcardV : Nat.card (Multiplicative (Fin 4 → ZMod 2)) = 16 := by
    show Nat.card (Fin 4 → ZMod 2) = 16
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin]
    norm_num
  show Nat.card (Multiplicative (Fin 4 → ZMod 2)) ≤ _
  calc Nat.card (Multiplicative (Fin 4 → ZMod 2)) = 16 := hcardV
    _ = 4 * 4 := by norm_num
    _ ≤ 4 * Nat.card (fixV (Subgroup.closure ({a, b} :
        Set (MulAut (Multiplicative (Fin 4 → ZMod 2)))))) := Nat.mul_le_mul_left 4 h4fix
    _ = Nat.card (Subgroup.closure ({a, b} : Set (MulAut (Multiplicative (Fin 4 → ZMod 2))))) *
          Nat.card (fixV (Subgroup.closure ({a, b} :
            Set (MulAut (Multiplicative (Fin 4 → ZMod 2)))))) := by rw [hA4]


theorem KConfig.conclK_of_sixteen_a6
    {G : Type} [Group G] [Finite G] {L V MK : Subgroup G}
    (h : KConfig G L V MK) (hV : Nat.card V = 16) (hO : CFSG.Open.pCoreOf 2 L = V)
    (hC : Subgroup.centralizer (V : Set G) ≤ V)
    (e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* alternatingGroup (Fin 6)) : ConclK G L V MK := by
  classical
  have F : Facts := Certificates.certificate442267
  have hcommV : IsMulCommutative ↥V := h.elemAbelian.1
  letI : IsMulCommutative ↥V := hcommV
  have hcomm : ∀ a b : ↥V, a * b = b * a := fun a b => hcommV.is_comm.comm a b
  have hpow : ∀ a : ↥V, a ^ 2 = 1 := fun a => Subtype.ext (by simpa using h.elemAbelian.2 a a.2)
  obtain ⟨e₀⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary hcomm hpow (n := 4)
    (by rw [hV]; norm_num)
  let Ψ : MulAut (Multiplicative (Fin 4 → ZMod 2)) ≃* GL (Fin 4) (ZMod 2) :=
    CFSG.SectionRank.Ccomm.mulAutEquivGL 4
  let Φ : MulAut ↥V ≃* GL (Fin 4) (ZMod 2) := (MulAut.congr e₀).trans Ψ
  have hVC : V ≤ Subgroup.centralizer (V : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact congrArg Subtype.val (hcommV.is_comm.comm ⟨w, hw⟩ ⟨v, hv⟩)
  have hker : (CFSG.Quasithin.InternalSec.autOnHom h.le_normalizer).ker = CFSG.pCore 2 ↥L := by
    rw [← CFSG.Quasithin.KGC31.Hex.pCoreOf_subgroupOf' L, hO]
    ext l
    rw [CFSG.Quasithin.InternalSec.mem_ker_autOnHom, Subgroup.mem_subgroupOf]
    exact ⟨fun hl => hC hl, fun hl => hVC hl⟩
  let eQ : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥(autOn L V) :=
    (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (CFSG.Quasithin.InternalSec.autOnHom_surjective _))
  let H : Subgroup (GL (Fin 4) (ZMod 2)) := (autOn L V).map Φ.toMonoidHom
  have hH : Nonempty (↥H ≃* alternatingGroup (Fin 6)) :=
    ⟨(MulEquiv.subgroupMap Φ (autOn L V)).symm.trans (eQ.symm.trans e)⟩
  obtain ⟨g, hg⟩ := exists_conj_eq_of_a6 F H hH
  have hFF1 := isFFModule_rhoA6 F
  have hΦsymm : Φ.symm.toMonoidHom =
      (MulAut.congr e₀.symm).toMonoidHom.comp Ψ.symm.toMonoidHom := by
    have hsymm : (MulAut.congr e₀).symm = MulAut.congr e₀.symm :=
      MulEquiv.ext fun y => rfl
    have hΦx : ∀ x, Φ (MulAut.congr e₀.symm (Ψ.symm x)) = x := by
      intro x
      show Ψ (MulAut.congr e₀ (MulAut.congr e₀.symm (Ψ.symm x))) = x
      rw [← hsymm]
      rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    refine MonoidHom.ext fun x => ?_
    show Φ.symm x = MulAut.congr e₀.symm (Ψ.symm x)
    rw [MulEquiv.symm_apply_eq]
    exact (hΦx x).symm
  have hFF2 : IsFFModule ((rhoA6 F).map Φ.symm.toMonoidHom) := by
    have h := CFSG.Quasithin.E3.isFFModule_map_congr (φ := e₀.symm) hFF1
    rw [Subgroup.map_map] at h
    rwa [hΦsymm]
  have hFF3 : IsFFModule (((rhoA6 F).map Φ.symm.toMonoidHom).map
      (MulAut.conj (Φ.symm g)).toMonoidHom) := by
    have h := CFSG.Quasithin.E3.isFFModule_map_congr (φ := Φ.symm g) hFF2
    rwa [show (MulAut.congr (Φ.symm g)).toMonoidHom = (MulAut.conj (Φ.symm g)).toMonoidHom
      from rfl] at h
  have hfinal : autOn L V = ((rhoA6 F).map Φ.symm.toMonoidHom).map
      (MulAut.conj (Φ.symm g)).toMonoidHom := by
    have e1 : autOn L V = H.map Φ.symm.toMonoidHom := by
      rw [show H = (autOn L V).map Φ.toMonoidHom from rfl, Subgroup.map_map,
        show Φ.symm.toMonoidHom.comp Φ.toMonoidHom = MonoidHom.id (MulAut ↥V) from
          MonoidHom.ext fun x => by simp, Subgroup.map_id]
    rw [e1, hg, Subgroup.map_map, Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun x => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_inv]
  have hFF : IsFFModule (autOn L V) := by
    rw [hfinal]
    exact hFF3
  have hFFN : IsFFModule (V := ↥V) (autOn (Subgroup.normalizer (V : Set G)) V) :=
    CFSG.Quasithin.H13.Prop329.isFFModule_of_le (CFSG.Quasithin.A4.autOn_mono h.le_normalizer) hFF
  have hcardX : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 360 := by
    rw [Nat.card_congr e.toEquiv, card_alt6]
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := e.isSimpleGroup
  have hnc : ∃ x y : ↥L ⧸ CFSG.pCore 2 ↥L, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := alt6_nonab
    exact ⟨e.symm x, e.symm y, fun h' => hxy (by simpa using congrArg e h')⟩
  have hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) :=
    isQuasisimple_of_simple_nonab hnc
  have hZ : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := by
    obtain ⟨x, y, hxy⟩ := hnc
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))
      with hb | ht
    · exact hb
    · exact absurd (Subgroup.mem_center_iff.mp (ht ▸ Subgroup.mem_top y) x) hxy
  unfold ConclK
  refine Or.inl ⟨hq, Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩))),
    Or.inl ⟨⟨hcommV, hFFN⟩, ?_, ?_, ?_, ?_⟩⟩
  ·
    intro h3
    have h1 := LieModel.card_psl_three_two h3
    rw [hcardX] at h1
    norm_num at h1
  ·
    intro h4
    have h1 := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_four_two
      (h4.statedClassicalModel (by decide))
    rw [hcardX] at h1
    norm_num at h1
  ·
    rintro ⟨-, hc, -⟩
    rw [hZ, Subgroup.card_bot] at hc
    norm_num at hc
  ·
    intro _ h64
    rw [hV] at h64
    norm_num at h64

end CFSG.SectionRank.QTK.Insp443

end
