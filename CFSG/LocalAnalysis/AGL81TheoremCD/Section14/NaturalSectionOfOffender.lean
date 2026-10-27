module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NaturalSectionOn
import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Final
import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Base8Smith
import CFSG.HardMathSupport.Cooperstein.Coordinator.NaturalBridgeLS
import CFSG.CGT.PushingUpLit.BHS5.AmbientConj
import CFSG.Quasithin.Background.C41PfU
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.PartTwo
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open CFSG.HardMathSupport.Cooperstein.Coordinator

variable {X : Type} [Group X] [Finite X]

private noncomputable abbrev autTop (W : Subgroup X) : Subgroup (MulAut ↥W) :=
  autOn ⊤ W

private noncomputable abbrev autL (W L : Subgroup X) : Subgroup (MulAut ↥W) :=
  autOn L W

private noncomputable abbrev autTopRho (W : Subgroup X) [W.Normal] :
    ↥(⊤ : Subgroup X) →* ↥(autTop W) :=
  (Setup.rho W ⊤ (by rw [Subgroup.normalizer_eq_top W])).codRestrict (autTop W) fun g =>
    (Setup.range_rho (by rw [Subgroup.normalizer_eq_top W])).le ⟨g, rfl⟩

private theorem autTopRho_surjective (W : Subgroup X) [W.Normal] :
    Function.Surjective (autTopRho W) := by
  intro g
  have hg : (g : MulAut ↥W) ∈ (Setup.rho W ⊤ (by rw [Subgroup.normalizer_eq_top W])).range := by
    rw [Setup.range_rho]
    exact g.2
  obtain ⟨x, hx⟩ := hg
  exact ⟨x, Subtype.ext hx⟩

private theorem autTopRho_ker (W : Subgroup X) [W.Normal] :
    (autTopRho W).ker = (Subgroup.centralizer (W : Set X)).subgroupOf ⊤ := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    exact (Setup.rho_eq_one_iff (by rw [Subgroup.normalizer_eq_top W]) g).1
      (congrArg (fun x : ↥(autTop W) => (x : MulAut ↥W)) h)
  · intro h
    apply Subtype.ext
    exact (Setup.rho_eq_one_iff (by rw [Subgroup.normalizer_eq_top W]) g).2 h

private theorem autTopRho_apply (W : Subgroup X) [W.Normal]
    (g : ↥(⊤ : Subgroup X)) (v : ↥W) :
    ((((autTopRho W) g : MulAut ↥W) v : ↥W) : X) = (g : X) * (v : X) * (g : X)⁻¹ :=
  Setup.rho_apply_coe (by rw [Subgroup.normalizer_eq_top W]) g v

private noncomputable abbrev autTopPsi (W : Subgroup X) [W.Normal] {n : ℕ}
    (φ : X →* Equiv.Perm (Fin n))
    (hker : φ.ker = Subgroup.centralizer (W : Set X)) :
    ↥(autTop W) →* Equiv.Perm (Fin n) :=
  (autTopRho W).liftOfSurjective (autTopRho_surjective W)
    ⟨φ.domRestrict ⊤, by
      rw [autTopRho_ker, MonoidHom.ker_domRestrict, hker]⟩

private theorem autTopPsi_comp_autTopRho (W : Subgroup X) [W.Normal] {n : ℕ}
    (φ : X →* Equiv.Perm (Fin n))
    (hker : φ.ker = Subgroup.centralizer (W : Set X))
    (x : ↥(⊤ : Subgroup X)) :
    autTopPsi W φ hker (autTopRho W x) = φ.domRestrict ⊤ x :=
  (autTopRho W).liftOfRightInverse_comp_apply _ _ ⟨φ.domRestrict ⊤, by
    rw [autTopRho_ker, MonoidHom.ker_domRestrict, hker]⟩ x

private theorem autTopPsi_injective (W : Subgroup X) [W.Normal] {n : ℕ}
    (φ : X →* Equiv.Perm (Fin n))
    (hker : φ.ker = Subgroup.centralizer (W : Set X)) :
    Function.Injective (autTopPsi W φ hker) := by
  intro a b hab
  obtain ⟨x, rfl⟩ := autTopRho_surjective W a
  obtain ⟨y, rfl⟩ := autTopRho_surjective W b
  rw [autTopPsi_comp_autTopRho, autTopPsi_comp_autTopRho] at hab
  have hxyφ : φ.domRestrict ⊤ (x * y⁻¹) = 1 := by
    rw [map_mul, map_inv, hab, mul_inv_cancel]
  have hxym : x * y⁻¹ ∈ (autTopRho W).ker := by
    rw [autTopRho_ker, ← hker, ← MonoidHom.ker_domRestrict]
    exact MonoidHom.mem_ker.mpr hxyφ
  have hxy : autTopRho W (x * y⁻¹) = 1 := hxym
  rw [map_mul, map_inv] at hxy
  calc autTopRho W x = autTopRho W x * (autTopRho W y)⁻¹ * autTopRho W y := by group
    _ = autTopRho W y := by rw [hxy, one_mul]

private theorem autTopPsi_range (W : Subgroup X) [W.Normal] {n : ℕ}
    (φ : X →* Equiv.Perm (Fin n))
    (hker : φ.ker = Subgroup.centralizer (W : Set X)) :
    (autTopPsi W φ hker).range = Subgroup.map φ ⊤ := by
  have hcomp : ((autTopPsi W φ hker).comp (autTopRho W)).range =
      (autTopPsi W φ hker).range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (autTopRho_surjective W),
      Subgroup.map_top]
  rw [← hcomp, show (autTopPsi W φ hker).comp (autTopRho W) = φ.domRestrict ⊤ from
    MonoidHom.ext (autTopPsi_comp_autTopRho W φ hker)]
  rw [MonoidHom.domRestrict_range]

private theorem alternatingGroup_le_autTopPsi_range {W L : Subgroup X} [W.Normal] {n : ℕ}
    (φ : X →* Equiv.Perm (Fin n))
    (hker : φ.ker = Subgroup.centralizer (W : Set X))
    (hL : L.map φ = alternatingGroup (Fin n)) :
    alternatingGroup (Fin n) ≤ (autTopPsi W φ hker).range := by
  rw [autTopPsi_range, ← hL]
  exact Subgroup.map_mono le_top

private theorem autTopPsi_normalizes_pCore {W L : Subgroup X} [W.Normal] {n : ℕ}
    (φ : X →* Equiv.Perm (Fin n))
    (hker : φ.ker = Subgroup.centralizer (W : Set X))
    (hL : L.map φ = alternatingGroup (Fin n)) :
    ∀ a ∈ alternatingGroup (Fin n),
      ∀ x ∈ Subgroup.map (autTopPsi W φ hker) (pCore 2 ↥(autTop W)),
        a * x * a⁻¹ ∈ Subgroup.map (autTopPsi W φ hker) (pCore 2 ↥(autTop W)) := by
  intro a ha x hx
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp (alternatingGroup_le_autTopPsi_range φ hker hL ha)
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
  have hNn : (pCore 2 ↥(autTop W)).Normal := CFSG.pCore_normal
  rw [← hy]
  exact Subgroup.mem_map.mpr ⟨y * k * y⁻¹, hNn.conj_mem k hk y, by
    rw [map_mul, map_mul, map_inv]⟩

private theorem nonempty_autL_equiv_alt {W L : Subgroup X} [W.Normal] {n : ℕ}
    (φ : X →* Equiv.Perm (Fin n))
    (hker : φ.ker = Subgroup.centralizer (W : Set X))
    (hL : L.map φ = alternatingGroup (Fin n)) :
    Nonempty (↥(autL W L) ≃* alternatingGroup (Fin n)) := by
  have hLW : L ≤ Subgroup.normalizer (W : Set X) := by
    rw [Subgroup.normalizer_eq_top W]
    exact le_top
  let Φ₀ : ↥L →* Equiv.Perm (Fin n) := φ.domRestrict L
  let Φ : ↥L →* ↥(alternatingGroup (Fin n)) :=
    Φ₀.codRestrict _ fun l => by
      rw [← hL]
      exact Subgroup.mem_map_of_mem φ l.2
  have hΦker : Φ.ker = (Subgroup.centralizer (W : Set X)).subgroupOf L := by
    rw [MonoidHom.ker_codRestrict, MonoidHom.ker_domRestrict, hker]
  have hΦsurj : Function.Surjective Φ := by
    intro σ
    obtain ⟨l, hlL, hlφ⟩ := Subgroup.mem_map.mp (by rw [hL]; exact σ.2)
    exact ⟨⟨l, hlL⟩, Subtype.ext hlφ⟩
  let ρL : ↥L →* ↥(autL W L) :=
    (Setup.rho W L hLW).codRestrict (autL W L) fun l => (Setup.range_rho hLW).le ⟨l, rfl⟩
  have hρLsurj : Function.Surjective ρL := by
    intro l
    have hl : (l : MulAut ↥W) ∈ (Setup.rho W L hLW).range := by
      rw [Setup.range_rho]
      exact l.2
    obtain ⟨x, hx⟩ := hl
    exact ⟨x, Subtype.ext hx⟩
  have hρLker : ρL.ker = (Subgroup.centralizer (W : Set X)).subgroupOf L := by
    ext l
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact (Setup.rho_eq_one_iff hLW l).1
        (congrArg (fun x : ↥(autL W L) => (x : MulAut ↥W)) h)
    · intro h
      apply Subtype.ext
      exact (Setup.rho_eq_one_iff hLW l).2 h
  have hker_eq : ρL.ker = Φ.ker := hρLker.trans hΦker.symm
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective ρL hρLsurj).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker_eq).trans
      (QuotientGroup.quotientKerEquivOfSurjective Φ hΦsurj))⟩

private theorem autL_sq_mem {W L : Subgroup X} [W.Normal] {n : ℕ} (hn : 9 ≤ n)
    (φ : X →* Equiv.Perm (Fin n))
    (hker : φ.ker = Subgroup.centralizer (W : Set X))
    (hL : L.map φ = alternatingGroup (Fin n)) :
    ∀ y ∈ autTop W, y ^ 2 ∈ autL W L := by
  have hLs_le_Gs : autL W L ≤ autTop W := InternalSec.autOn_le_autOn_of_le le_top
  haveI : Nontrivial (Fin n) :=
    ⟨⟨⟨0, by omega⟩, ⟨1, by omega⟩, by
      intro h; exact (by omega : (0 : ℕ) ≠ 1) (congrArg Fin.val h)⟩⟩
  intro y hy
  obtain ⟨x, hx⟩ := autTopRho_surjective W ⟨y, hy⟩
  have hyx : y = autTopRho W x := (congrArg Subtype.val hx).symm
  rw [hyx]
  have hsqA : φ.domRestrict ⊤ (x ^ 2) ∈ alternatingGroup (Fin n) := by
    have h := Subgroup.sq_mem_of_index_two (H := alternatingGroup (Fin n))
      alternatingGroup.index_eq_two (φ.domRestrict ⊤ x)
    simpa [map_pow] using h
  obtain ⟨l, hlL, hlφ₀⟩ := Subgroup.mem_map.mp (by rw [hL]; exact hsqA)
  have hlφ : φ l = φ ((x : X) ^ 2) := by
    rw [hlφ₀, MonoidHom.domRestrict_apply, Subgroup.coe_pow]
  have hmemker : ((x : X) ^ 2) * l⁻¹ ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← hlφ, mul_inv_cancel]
  have hmemLs : (Setup.rho W ⊤ (by rw [Subgroup.normalizer_eq_top W])
      ⟨l, Subgroup.mem_top l⟩ : MulAut ↥W) ∈ autL W L :=
    (Setup.mem_autOn_iff_rho (by rw [Subgroup.normalizer_eq_top W]) (X := L)
      (le_top : L ≤ ⊤)).2 ⟨⟨l, Subgroup.mem_top l⟩, hlL, rfl⟩
  let lstar : ↥(autL W L) :=
    ⟨Setup.rho W ⊤ (by rw [Subgroup.normalizer_eq_top W]) ⟨l, Subgroup.mem_top l⟩, hmemLs⟩
  have hρl : autTopRho W (⟨l, Subgroup.mem_top l⟩ : ↥(⊤ : Subgroup X)) =
      Subgroup.inclusion hLs_le_Gs lstar := by
    apply Subtype.ext
    rfl
  have hz : autTopRho W (x ^ 2 * (⟨l, Subgroup.mem_top l⟩ : ↥(⊤ : Subgroup X))⁻¹) = 1 := by
    rw [← MonoidHom.mem_ker, autTopRho_ker, Subgroup.mem_subgroupOf, ← hker, MonoidHom.mem_ker]
    show φ ((x : X) ^ 2 * l⁻¹) = 1
    rw [MonoidHom.mem_ker] at hmemker
    simpa using hmemker
  have hx2 : autTopRho W (x ^ 2) =
      autTopRho W (⟨l, Subgroup.mem_top l⟩ : ↥(⊤ : Subgroup X)) := by
    have hsplit : x ^ 2 = (x ^ 2 * (⟨l, Subgroup.mem_top l⟩ : ↥(⊤ : Subgroup X))⁻¹) *
        (⟨l, Subgroup.mem_top l⟩ : ↥(⊤ : Subgroup X)) := by group
    rw [hsplit, map_mul, hz, one_mul]
  have hfinal : (autTopRho W x) ^ 2 = Subgroup.inclusion hLs_le_Gs lstar := by
    rw [← map_pow, hx2, hρl]
  rw [← Subgroup.coe_pow, hfinal]
  simpa using lstar.2

private theorem map_autTopPsi_pCore_inf_alt_eq_bot {W : Subgroup X} [W.Normal] {n : ℕ}
    (hn : 9 ≤ n) (ψ : ↥(autTop W) →* Equiv.Perm (Fin n))
    (hAnorm : ∀ a ∈ alternatingGroup (Fin n),
      ∀ x ∈ Subgroup.map ψ (pCore 2 ↥(autTop W)),
        a * x * a⁻¹ ∈ Subgroup.map ψ (pCore 2 ↥(autTop W))) :
    Subgroup.map ψ (pCore 2 ↥(autTop W)) ⊓ alternatingGroup (Fin n) = ⊥ := by
  let K : Subgroup ↥(alternatingGroup (Fin n)) :=
    (Subgroup.map ψ (pCore 2 ↥(autTop W)) ⊓ alternatingGroup (Fin n)).subgroupOf
      (alternatingGroup (Fin n))
  have hN'2 : IsPGroup 2 ↥(Subgroup.map ψ (pCore 2 ↥(autTop W))) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥(autTop W))).map ψ
  have hKn : K.Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨hAnorm (g : Equiv.Perm (Fin n)) g.2 x hx.1,
      (alternatingGroup (Fin n)).mul_mem
        ((alternatingGroup (Fin n)).mul_mem g.2 hx.2)
        ((alternatingGroup (Fin n)).inv_mem g.2)⟩⟩
  have hK2 : IsPGroup 2 ↥K := by
    let f : ↥K →* ↥(Subgroup.map ψ (pCore 2 ↥(autTop W))) :=
      { toFun := fun k => ⟨(k.1 : Equiv.Perm (Fin n)),
          (Subgroup.mem_subgroupOf.mp k.2).1⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact hN'2.of_injective f fun a b hab => Subtype.ext (Subtype.ext
      (congrArg (fun z : ↥(Subgroup.map ψ (pCore 2 ↥(autTop W))) =>
        (z : Equiv.Perm (Fin n))) hab))
  have hsimpleA : IsSimpleGroup ↥(alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  have hnot2A : ¬ IsPGroup 2 ↥(alternatingGroup (Fin n)) :=
    CFSG.Quasithin.C41Pf.AltN.not_isPGroup_two_alt (by omega)
  have hKbot : K = ⊥ := by
    rcases hsimpleA.eq_bot_or_eq_top_of_normal K with h | h
    · exact h
    · exfalso
      apply hnot2A
      have hAleN' : alternatingGroup (Fin n) ≤ Subgroup.map ψ (pCore 2 ↥(autTop W)) := by
        intro a ha
        have hmem : (⟨a, ha⟩ : ↥(alternatingGroup (Fin n))) ∈
            (⊤ : Subgroup ↥(alternatingGroup (Fin n))) := Subgroup.mem_top _
        rw [← h] at hmem
        exact (Subgroup.mem_subgroupOf.mp hmem).1
      exact hN'2.of_injective (Subgroup.inclusion hAleN')
        (Subgroup.inclusion_injective hAleN')
  rw [eq_bot_iff]
  intro x hx
  have hmem : (⟨x, hx.2⟩ : ↥(alternatingGroup (Fin n))) ∈ K := by
    rw [Subgroup.mem_subgroupOf]; exact hx
  rw [hKbot, Subgroup.mem_bot] at hmem
  simpa using congrArg (fun z : ↥(alternatingGroup (Fin n)) =>
    (z : Equiv.Perm (Fin n))) hmem

private theorem map_autTopPsi_pCore_eq_bot {W : Subgroup X} [W.Normal] {n : ℕ} (hn : 9 ≤ n)
    (ψ : ↥(autTop W) →* Equiv.Perm (Fin n))
    (hψinj : Function.Injective ψ)
    (hAnorm : ∀ a ∈ alternatingGroup (Fin n),
      ∀ x ∈ Subgroup.map ψ (pCore 2 ↥(autTop W)),
        a * x * a⁻¹ ∈ Subgroup.map ψ (pCore 2 ↥(autTop W)))
    (hN : Subgroup.map ψ (pCore 2 ↥(autTop W)) ⊓ alternatingGroup (Fin n) = ⊥) :
    Subgroup.map ψ (pCore 2 ↥(autTop W)) = ⊥ := by
  have hcentA : Subgroup.centralizer
      ((alternatingGroup (Fin n) : Subgroup (Equiv.Perm (Fin n))) :
        Set (Equiv.Perm (Fin n))) = ⊥ :=
    CFSG.ComponentClassification.PresentationLocal.centralizer_alternatingGroup_eq_bot
      (α := Fin n) (by rw [Nat.card_fin]; omega)
  rw [eq_bot_iff]
  intro x hx
  rw [eq_bot_iff] at hcentA
  exact hcentA (Subgroup.mem_centralizer_iff.2 fun a ha => by
    have hmemN : x * a * x⁻¹ * a⁻¹ ∈ Subgroup.map ψ (pCore 2 ↥(autTop W)) := by
      have hconj := hAnorm a ha x⁻¹ ((Subgroup.map ψ (pCore 2 ↥(autTop W))).inv_mem hx)
      have hmem := (Subgroup.map ψ (pCore 2 ↥(autTop W))).mul_mem hx hconj
      simpa only [mul_assoc] using hmem
    have hmemA : x * a * x⁻¹ * a⁻¹ ∈ alternatingGroup (Fin n) := by
      have hconj := (alternatingGroup.normal (α := Fin n)).conj_mem a ha x
      have hmem := (alternatingGroup (Fin n)).mul_mem hconj
        ((alternatingGroup (Fin n)).inv_mem ha)
      simpa only [mul_assoc] using hmem
    have hcomm : x * a * x⁻¹ * a⁻¹ ∈
        Subgroup.map ψ (pCore 2 ↥(autTop W)) ⊓ alternatingGroup (Fin n) := ⟨hmemN, hmemA⟩
    rw [hN, Subgroup.mem_bot] at hcomm
    calc a * x = (x * a * x⁻¹ * a⁻¹) * (a * x) := by
          rw [hcomm, one_mul]
      _ = x * a := by group)

private theorem autL_eq_quasithinGenFitting {W L : Subgroup X} [W.Normal]
    (hnorm : ∀ y ∈ autTop W, ∀ l ∈ autL W L, y * l * y⁻¹ ∈ autL W L)
    (hsq : ∀ y ∈ autTop W, y ^ 2 ∈ autL W L)
    (hq : CFSG.Open.IsQuasisimple ↥(autL W L))
    (hO2 : pCoreOf 2 (autTop W) = ⊥) :
    autL W L = quasithinGenFitting (autTop W) :=
  (CFSG.Quasithin.B1Red.quasithinGenFitting_eq_of_two_quot (Y := autTop W) (L := autL W L)
    (InternalSec.autOn_le_autOn_of_le le_top) hnorm hq hsq hO2).symm

private theorem isFFModule_autTop {W A : Subgroup X} [W.Normal]
    (hW : IsElemAbelian 2 W) :
    letI : CommGroup ↥W := commGroupOfElemAbelian hW
    ∀ (hA : IsElemAbelian 2 A) (hAW : ¬ A ≤ Subgroup.centralizer (W : Set X)),
      Nat.card W ≤ (Subgroup.centralizer (W : Set X)).relIndex A *
        Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set X)) →
      IsFFModule (autTop W) := by
  letI : CommGroup ↥W := commGroupOfElemAbelian hW
  intro hA hAW hoff
  have hAn : A ≤ Subgroup.normalizer (W : Set X) := by
    rw [Subgroup.normalizer_eq_top W]
    exact le_top
  refine ⟨autOn A W, InternalSec.autOn_le_autOn_of_le le_top,
    CFSG.Quasithin.AutOn.autOn_ne_bot_of_not_le_centralizer hAn hAW,
    CFSG.Quasithin.isElemAbelian2_autOn hW hA hAn, ?_⟩
  rw [CFSG.Quasithin.AutOn.card_autOn_eq_relIndex_centralizer hAn,
    CFSG.Quasithin.card_fixV_autOn_eq hW hAn]
  exact hoff

private theorem isAltNaturalSection_autL
    {W L : Subgroup X} [W.Normal] {n : ℕ}
    (hW : IsElemAbelian 2 W) :
    letI : CommGroup ↥W := commGroupOfElemAbelian hW
    ∀ (hn : 9 ≤ n) (hLF : autL W L = quasithinGenFitting (autTop W))
      (e : ↥(autL W L) ≃* alternatingGroup (Fin n))
      (Astar : Subgroup (MulAut ↥W)) (hAstar : IsFFStarOffender (autTop W) Astar),
      IsAltNaturalSection (autL W L) (commV (autL W L)) n := by
  letI : CommGroup ↥W := commGroupOfElemAbelian hW
  intro hn hLF e Astar hAstar
  have h85 : GF2EightFive := EightFive.gf2EightFive_of_b42L42Core EightFive.b42L42Core_holds
  have hV2 : ∀ v : ↥W, v ^ 2 = 1 := fun v => Subtype.ext (hW.2 v v.2)
  have hLs_le_Gs : autL W L ≤ autTop W := InternalSec.autOn_le_autOn_of_le le_top
  rcases h85 ↥W hV2 (autTop W) (autL W L) hLF n (Or.inr hn) ⟨e⟩ ⟨Astar, hAstar⟩ with
    hnat | ⟨h7, -, -⟩
  · exact isAltNaturalSection_commV_of_le hLs_le_Gs (by omega) hnat
  · omega

private theorem naturalSectionOn_of_altNaturalSection {W L : Subgroup X} [W.Normal] {n : ℕ}
    (hW : IsElemAbelian 2 W) :
    letI : CommGroup ↥W := commGroupOfElemAbelian hW
    ∀ (hLs_le_Gs : autL W L ≤ autTop W)
      (θs : ↥(autTop W) →* Equiv.Perm (Fin n))
      (πs : ↥(commV (autL W L)) →* Multiplicative (altHeart n))
      (hπs : Function.Surjective πs)
      (hkers : πs.ker = (commV (autL W L) ⊓ fixV (autL W L)).subgroupOf (commV (autL W L)))
      (hrange : alternatingGroup (Fin n) ≤ (θs.comp (Subgroup.inclusion hLs_le_Gs)).range)
      (hequiv : ∀ (h : ↥(autTop W)) (u v : ↥(commV (autL W L))),
        (v : ↥W) = (h : MulAut ↥W) (u : ↥W) → ∀ x : evenWeight n,
          Multiplicative.toAdd (πs u) = (x : altHeart n) →
            Multiplicative.toAdd (πs v) =
              (evenWeightPerm (θs h) x : altHeart n))
      (hinj : Function.Injective θs),
      NaturalSectionOn W L ⊤ n := by
  letI : CommGroup ↥W := commGroupOfElemAbelian hW
  intro hLs_le_Gs θs πs hπs hkers hrange hequiv hinj
  have hLW : L ≤ Subgroup.normalizer (W : Set X) := by
    rw [Subgroup.normalizer_eq_top W]
    exact le_top
  let ι : ↥(commV (autL W L)) ≃* ↥⁅W, L⁆ :=
    ((commV (autL W L)).equivMapOfInjective W.subtype W.subtype_injective).trans
      (MulEquiv.subgroupCongr (CFSG.CGT.PushingUpLit.BHS5.map_commV_autOn hW hLW))
  have hι : ∀ u : ↥(commV (autL W L)),
      ((ι u : ↥⁅W, L⁆) : X) = ((u : ↥W) : X) := fun _ => rfl
  have hιs : ∀ t : ↥⁅W, L⁆,
      (((ι.symm t : ↥(commV (autL W L))) : ↥W) : X) = (t : X) := fun t => by
    rw [← hι, ι.apply_symm_apply]
  refine ⟨πs.comp ι.symm.toMonoidHom, θs.comp (autTopRho W), hπs.comp ι.symm.surjective,
    ?_, ?_, ?_, ?_⟩
  · ext t
    have key : t ∈ (πs.comp ι.symm.toMonoidHom).ker ↔
        ((ι.symm t : ↥(commV (autL W L))) : ↥W) ∈ fixV (autL W L) := by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        ← MonoidHom.mem_ker, hkers, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.2, fun h => ⟨(ι.symm t).2, h⟩⟩
    rw [key, CFSG.CGT.PushingUpLit.BHS5.mem_fixV_autOn_iff hW hLW, hιs,
      Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨t.2, h⟩, fun h => h.2⟩
  · intro σ hσ
    obtain ⟨l, hl⟩ := hrange hσ
    obtain ⟨p, hpL, hpl⟩ :=
      (Setup.mem_autOn_iff_rho (by rw [Subgroup.normalizer_eq_top W]) (X := L)
        (le_top : L ≤ ⊤)).1 l.2
    refine ⟨(p : X), hpL, Subgroup.mem_top _, ?_⟩
    have hρp : autTopRho W p = Subgroup.inclusion hLs_le_Gs l := Subtype.ext hpl
    have heq : (⟨(p : X), Subgroup.mem_top (p : X)⟩ : ↥(⊤ : Subgroup X)) = p := Subtype.ext rfl
    calc (θs.comp (autTopRho W)) ⟨(p : X), Subgroup.mem_top (p : X)⟩ =
          (θs.comp (autTopRho W)) p := by rw [heq]
      _ = θs (autTopRho W p) := rfl
      _ = θs (Subgroup.inclusion hLs_le_Gs l) := by rw [hρp]
      _ = σ := hl
  · intro m u u' hu' x hx
    refine hequiv (autTopRho W m) (ι.symm u) (ι.symm u') ?_ x hx
    apply Subtype.ext
    rw [autTopRho_apply, hιs, hιs]
    exact hu'
  · intro m hm
    have h1 : autTopRho W m = 1 := hinj (hm.trans (map_one θs).symm)
    have hmem : m ∈ (autTopRho W).ker := h1
    rw [autTopRho_ker, Subgroup.mem_subgroupOf] at hmem
    exact hmem

theorem naturalSectionOn_top_of_offender
    {W L A : Subgroup X}
    (hW : IsElemAbelian 2 W) (hWn : W.Normal) (hLn : L.Normal) {n : ℕ} (hn : 9 ≤ n)
    (φ : X →* Equiv.Perm (Fin n)) (hker : φ.ker = Subgroup.centralizer (W : Set X))
    (hL : L.map φ = alternatingGroup (Fin n)) (hA : IsElemAbelian 2 A)
    (hAW : ¬ A ≤ Subgroup.centralizer (W : Set X))
    (hoff : Nat.card W ≤ (Subgroup.centralizer (W : Set X)).relIndex A *
      Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set X))) :
    NaturalSectionOn W L ⊤ n := by
  classical
  haveI : W.Normal := hWn
  haveI : L.Normal := hLn
  haveI : Nontrivial (Fin n) :=
    ⟨⟨⟨0, by omega⟩, ⟨1, by omega⟩, by
      intro h; exact (by omega : (0 : ℕ) ≠ 1) (congrArg Fin.val h)⟩⟩
  letI : CommGroup ↥W := commGroupOfElemAbelian hW
  have hLs_le_Gs : autL W L ≤ autTop W := InternalSec.autOn_le_autOn_of_le le_top
  have hψinj := autTopPsi_injective W φ hker
  have hAnorm := autTopPsi_normalizes_pCore φ hker hL
  obtain ⟨e⟩ := nonempty_autL_equiv_alt φ hker hL
  have hqC : CFSG.IsQuasisimple ↥(autL W L) :=
    CFSG.Quasithin.C41Pf.isQuasisimple_of_mulEquiv_alt (by omega) e
  have hq : CFSG.Open.IsQuasisimple ↥(autL W L) :=
    CFSG.Quasithin.B1Red.isQuasisimple_to_open hqC
  have hnorm : ∀ y ∈ autTop W, ∀ l ∈ autL W L, y * l * y⁻¹ ∈ autL W L :=
    InternalSec.autOn_normal_of (U := W) (Y := ⊤) (L := L)
      (by rw [Subgroup.normalizer_eq_top L])
  have hsq := autL_sq_mem hn φ hker hL
  have hN := map_autTopPsi_pCore_inf_alt_eq_bot hn (autTopPsi W φ hker) hAnorm
  have hN'bot := map_autTopPsi_pCore_eq_bot hn (autTopPsi W φ hker) hψinj hAnorm hN
  have hNbot : pCore 2 ↥(autTop W) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ hψinj).mp hN'bot
  have hO2 : pCoreOf 2 (autTop W) = ⊥ := by
    rw [CFSG.Open.pCoreOf, hNbot, Subgroup.map_bot]
  have hLF := autL_eq_quasithinGenFitting hnorm hsq hq hO2
  have hFF := isFFModule_autTop hW hA hAW hoff
  obtain ⟨Astar, hAstar⟩ := exists_isFFStarOffender_of_isFFModule hFF
  have hnatL := isAltNaturalSection_autL hW hn hLF e Astar hAstar
  obtain ⟨θs, πs, hπs, hkers, hrange, hequiv, hinj⟩ :=
    exists_permRep_of_isAltNaturalSection hLF hLs_le_Gs (by omega) (by omega) ⟨e⟩ hnatL
  exact naturalSectionOn_of_altNaturalSection hW hLs_le_Gs θs πs hπs hkers hrange hequiv hinj

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
