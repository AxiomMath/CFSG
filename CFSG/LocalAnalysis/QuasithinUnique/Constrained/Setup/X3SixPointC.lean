module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3GammaL
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3Schur
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3SixPointB
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3Partition

public section

namespace CFSG.QuasithinUnique.Setup.X3

open Equiv Subgroup CFSG.QuasithinUnique.Setup.Offender
open scoped LinearAlgebra.Projectivization

section Defs

variable (F : Type*) [Field F] (V : Type*) [AddCommGroup V] [Module F V]

@[expose] def toGamma : (V ≃ₗ[F] V) →* gammaL F V :=
  glToPerm.codRestrict (gammaL F V) glToPerm_mem_gammaL

theorem toGamma_apply (g : V ≃ₗ[F] V) (v : V) : (toGamma F V g).1 v = g v := rfl

theorem toGamma_injective : Function.Injective (toGamma F V) := fun _ _ hgh =>
  glToPerm_injective (congrArg Subtype.val hgh)

@[expose] noncomputable def lineAction : (V ≃ₗ[F] V) →* Perm (ℙ F V) :=
  pointActHom.comp (toGamma F V)

variable {F V}

theorem lineAction_scalar (c : Fˣ) (x : ℙ F V) : lineAction F V (scalarHom F V c) x = x :=
  pointAct_scalar c x

end Defs

structure ThreeQuaternaryData (F : Type*) [Field F] (V : Type*) [AddCommGroup V] [Module F V]
    (L : Subgroup (V ≃ₗ[F] V)) : Prop where
  card_field : Nat.card F = 4
  finrank_eq : Module.finrank F V = 3
  perfect : Group.IsPerfect L
  irreducible : ∀ W : Submodule F V, (∀ g ∈ L, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤
  center_eq : (Subgroup.center L).map L.subtype = (scalarHom F V).range
  quotient : Nonempty ((L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin 6))

section Basic

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
  {L : Subgroup (V ≃ₗ[F] V)}

theorem ThreeQuaternaryData.scalar_mem (hD : ThreeQuaternaryData F V L) (c : Fˣ) :
    scalarHom F V c ∈ L := by
  have : scalarHom F V c ∈ (Subgroup.center L).map L.subtype := by
    rw [hD.center_eq]; exact ⟨c, rfl⟩
  obtain ⟨g, -, hg⟩ := this
  rw [← hg]
  exact g.2

theorem ThreeQuaternaryData.center_scalar (hD : ThreeQuaternaryData F V L) {g : L}
    (hg : g ∈ Subgroup.center L) : ∃ c : Fˣ, g.1 = scalarHom F V c := by
  have : g.1 ∈ (Subgroup.center L).map L.subtype := ⟨g, hg, rfl⟩
  rw [hD.center_eq] at this
  obtain ⟨c, hc⟩ := this
  exact ⟨c, hc.symm⟩

theorem ThreeQuaternaryData.nonabelian (hD : ThreeQuaternaryData F V L) :
    ∃ g ∈ L, ∃ h ∈ L, g * h ≠ h * g := by
  by_contra hcon
  push Not at hcon
  obtain ⟨e⟩ := hD.quotient
  have hall : ∀ g : L, g ∈ Subgroup.center L := fun g => by
    rw [Subgroup.mem_center_iff]
    intro h
    exact Subtype.ext (hcon h.1 h.2 g.1 g.2)
  have hsub : Subsingleton (L ⧸ Subgroup.center L) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    have ha : (QuotientGroup.mk a : L ⧸ Subgroup.center L) = 1 := (QuotientGroup.eq_one_iff a).2 (hall a)
    have hb : (QuotientGroup.mk b : L ⧸ Subgroup.center L) = 1 := (QuotientGroup.eq_one_iff b).2 (hall b)
    rw [ha, hb]
  have hcard : Nat.card (L ⧸ Subgroup.center L) = 360 := by
    rw [Nat.card_congr e.toEquiv, card_alt6]
  have := Nat.card_unique (α := L ⧸ Subgroup.center L)
  omega

theorem card_points [Finite F] [Module.Finite F V] (hF : Nat.card F = 4)
    (hV : Module.finrank F V = 3) : Nat.card (ℙ F V) = 21 := by
  have hVfin : Finite V := Module.finite_of_finite F
  have h1 := Projectivization.card' (k := F) (V := V)
  have h2 : Nat.card V = Nat.card F ^ Module.finrank F V := Module.natCard_eq_pow_finrank (K := F)
  rw [hF, hV] at h2
  rw [hF] at h1
  norm_num at h2 h1
  omega

theorem ThreeQuaternaryData.no_fixed_point (hD : ThreeQuaternaryData F V L) (x : ℙ F V)
    (h : ∀ g ∈ L, lineAction F V g x = x) : False := by
  have hinv : ∀ g ∈ L, ∀ w ∈ x.submodule, g w ∈ x.submodule := by
    intro g hg w hw
    have h1 := h g hg
    have h2 : lineAction F V g x = Projectivization.mk F (g x.rep) (by
        intro h0
        exact x.rep_nonzero (g.injective (by rw [h0, map_zero]))) := by
      conv_lhs => rw [← Projectivization.mk_rep x]
      rfl
    rw [h2] at h1
    have h3 := (Projectivization.mk_eq_mk_iff' F (g x.rep) x.rep _ x.rep_nonzero).1
      (h1.trans (Projectivization.mk_rep x).symm)
    obtain ⟨a, ha⟩ := h3
    rw [Projectivization.submodule_eq, Submodule.mem_span_singleton] at hw ⊢
    obtain ⟨c, rfl⟩ := hw
    exact ⟨c * a, by rw [map_smul, ← ha, smul_smul, mul_comm]⟩
  rcases hD.irreducible x.submodule hinv with h0 | h0
  · have : x.rep ∈ x.submodule := by
      rw [Projectivization.submodule_eq]; exact Submodule.mem_span_singleton_self _
    rw [h0] at this
    exact x.rep_nonzero ((Submodule.mem_bot F).1 this)
  · have h1 := Projectivization.finrank_submodule x
    rw [h0, finrank_top, hD.finrank_eq] at h1
    omega

end Basic


section Orbits

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
  {L : Subgroup (V ≃ₗ[F] V)}

@[expose] noncomputable def quotAction (hD : ThreeQuaternaryData F V L) :
    (L ⧸ Subgroup.center L) →* Perm (ℙ F V) :=
  QuotientGroup.lift _ ((lineAction F V).comp L.subtype) (by
    intro g hg
    obtain ⟨c, hc⟩ := hD.center_scalar hg
    rw [MonoidHom.mem_ker]
    refine Equiv.ext fun x => ?_
    show lineAction F V g.1 x = x
    rw [hc]
    exact lineAction_scalar c x)

theorem quotAction_mk (hD : ThreeQuaternaryData F V L) (g : L) (x : ℙ F V) :
    quotAction hD (QuotientGroup.mk g) x = lineAction F V g.1 x := rfl

theorem quotOrbit_eq (hD : ThreeQuaternaryData F V L) (x : ℙ F V) :
    {z | ∃ q, quotAction hD q x = z} = {z | ∃ g ∈ L, lineAction F V g x = z} := by
  ext z
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨g.1, g.2, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨QuotientGroup.mk ⟨g, hg⟩, rfl⟩

theorem ThreeQuaternaryData.orbit_ncard_mem [Finite F] [Module.Finite F V]
    (hD : ThreeQuaternaryData F V L) (x : ℙ F V) :
    {z | ∃ q, quotAction hD q x = z}.ncard = 6 ∨ {z | ∃ q, quotAction hD q x = z}.ncard = 10 ∨
      {z | ∃ q, quotAction hD q x = z}.ncard = 12 ∨
      {z | ∃ q, quotAction hD q x = z}.ncard = 15 ∨
      {z | ∃ q, quotAction hD q x = z}.ncard = 20 := by
  obtain ⟨eQ⟩ := hD.quotient
  have hP : Nat.card (ℙ F V) = 21 := card_points hD.card_field hD.finrank_eq
  have hVfin : Finite V := Module.finite_of_finite F
  have hPfin : Finite (ℙ F V) := Nat.finite_of_card_ne_zero (by omega)
  have hle : {z | ∃ q, quotAction hD q x = z}.ncard ≤ 21 := by
    have := Set.ncard_le_card {z | ∃ q, quotAction hD q x = z}
    rwa [hP] at this
  rcases orbit_card_cases' (quotAction hD) eQ x with h | ⟨h6, hdvd, h8, h9, h18⟩
  · exfalso
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h
    have hxa : x = a := by
      have : x ∈ {z | ∃ q, quotAction hD q x = z} := ⟨1, by simp⟩
      rw [ha] at this
      exact this
    refine hD.no_fixed_point x (fun g hg => ?_)
    have : quotAction hD (QuotientGroup.mk ⟨g, hg⟩) x ∈ {z | ∃ q, quotAction hD q x = z} :=
      ⟨_, rfl⟩
    rw [ha] at this
    rw [← quotAction_mk hD ⟨g, hg⟩ x, (Set.mem_singleton_iff.mp this), hxa]
  · generalize {z | ∃ q, quotAction hD q x = z}.ncard = n at *
    interval_cases n <;> omega

end Orbits


section Main

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

variable (L : Subgroup (V ≃ₗ[F] V))

@[expose] noncomputable def lineOrbit (x : ℙ F V) : Set (ℙ F V) :=
  orb (pointActHom (F := F) (V := V)) (L.map (toGamma F V)) x

@[expose] def semilinearNormalizer : Subgroup (gammaL F V) :=
  normalizer ((L.map (toGamma F V) : Subgroup (gammaL F V)) : Set (gammaL F V))

variable {L}

theorem mem_lineOrbit_iff (x z : ℙ F V) :
    z ∈ lineOrbit L x ↔ ∃ g ∈ L, lineAction F V g x = z := by
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨toGamma F V g, ⟨g, hg, rfl⟩, rfl⟩

theorem lineOrbit_eq (hD : ThreeQuaternaryData F V L) (x : ℙ F V) :
    lineOrbit L x = {z | ∃ q, quotAction hD q x = z} := by
  ext z
  rw [mem_lineOrbit_iff, quotOrbit_eq hD]
  rfl

open scoped Classical in
theorem three_quaternary_normalizer_six_point [Finite F] [Module.Finite F V]
    [Fintype (ℙ F V)] (hD : ThreeQuaternaryData F V L) :
    ∃ x y : ℙ F V, (lineOrbit L x).ncard = 6 ∧ (lineOrbit L y).ncard = 15 ∧
      (∀ z, z ∈ lineOrbit L x ∨ z ∈ lineOrbit L y) ∧
      ∃ θ : semilinearNormalizer L →* Perm (lineOrbit L x),
        (∀ n z, (θ n z : ℙ F V) = pointAct n.1 z) ∧
        (∀ n, θ n = 1 ↔ ∃ c : Fˣ, n.1 = toGamma F V (scalarHom F V c)) ∧
        ((L.map (toGamma F V)).subgroupOf (semilinearNormalizer L)).map θ =
          alternatingGroup (lineOrbit L x) ∧
        ∀ K : Subgroup (semilinearNormalizer L),
          (L.map (toGamma F V)).subgroupOf (semilinearNormalizer L) ≤ K →
            Nonempty ((K ⧸ (θ.comp K.subtype).ker) ≃* alternatingGroup (lineOrbit L x)) ∨
              Nonempty ((K ⧸ (θ.comp K.subtype).ker) ≃* Perm (lineOrbit L x)) := by
  obtain ⟨eQ⟩ := hD.quotient
  have hP : Nat.card (ℙ F V) = 21 := card_points hD.card_field hD.finrank_eq
  have hpart := partition_six_fifteen (classSystem_orbit (quotAction hD)) hP
    (fun x => hD.orbit_ncard_mem x)
  obtain ⟨x, y, hx, hy, hcov⟩ := hpart
  have hLx : ∀ z, lineOrbit L z = {w | ∃ q, quotAction hD q z = w} := fun z => lineOrbit_eq hD z
  refine ⟨x, y, by rw [hLx]; exact hx, by rw [hLx]; exact hy,
    fun z => by rw [hLx, hLx]; exact hcov z, ?_⟩
  have hperf : Group.IsPerfect L := hD.perfect
  have hinj : Function.Injective (toGamma F V) := toGamma_injective F V
  let e : L ≃* L.map (toGamma F V) := Subgroup.equivMapOfInjective L (toGamma F V) hinj
  have : Group.IsPerfect (L.map (toGamma F V)) := Group.IsPerfect.map (f := toGamma F V)
  have hcen : (Subgroup.center L).map e.toMonoidHom = Subgroup.center (L.map (toGamma F V)) :=
    Subgroup.map_center_eq e
  let eQ' : (L.map (toGamma F V) ⧸ Subgroup.center (L.map (toGamma F V))) ≃*
      alternatingGroup (Fin 6) :=
    ((QuotientGroup.congr (Subgroup.center L) (Subgroup.center (L.map (toGamma F V))) e hcen).symm).trans eQ
  have hZ : ∀ g : L.map (toGamma F V), g ∈ Subgroup.center (L.map (toGamma F V)) →
      pointActHom (F := F) (V := V) g.1 = 1 := by
    intro g hg
    rw [← hcen] at hg
    obtain ⟨g₀, hg₀, rfl⟩ := hg
    obtain ⟨c, hc⟩ := hD.center_scalar hg₀
    refine Equiv.ext fun z => ?_
    show pointAct (e g₀).1 z = z
    have : (e g₀).1 = toGamma F V (scalarHom F V c) := by
      show toGamma F V g₀.1 = _
      rw [hc]
    rw [this]
    exact pointAct_scalar c z
  have hxo : (orb (pointActHom (F := F) (V := V)) (L.map (toGamma F V)) x).ncard = 6 := by
    have := hx; rw [← hLx] at this; exact this
  have hxo' : (lineOrbit L x).ncard = 6 := hxo
  have hyo : (orb (pointActHom (F := F) (V := V)) (L.map (toGamma F V)) y).ncard = 15 := by
    have := hy; rw [← hLx] at this; exact this
  have hcovo : ∀ z, z ∈ orb (pointActHom (F := F) (V := V)) (L.map (toGamma F V)) x ∨
      z ∈ orb (pointActHom (F := F) (V := V)) (L.map (toGamma F V)) y := by
    intro z
    have := hcov z
    rw [← hLx, ← hLx] at this
    exact this
  obtain ⟨θ, hθ, hker, himg⟩ := six_point_abstract (pointActHom (F := F) (V := V))
    (L.map (toGamma F V)) eQ' hZ hxo hyo hcovo
  have hcardO : Fintype.card (lineOrbit L x) = 6 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact hxo'
  refine ⟨θ, hθ, fun n => ⟨fun hn => ?_, ?_⟩, himg,
    fun K hK => overgroup_cases hcardO θ _ himg K hK⟩
  · have hcent := hker n hn
    rw [Subgroup.mem_centralizer_iff] at hcent
    have ha : n.1.1 ∈ gammaL F V := n.1.2
    have hcomm : ∀ g ∈ L, ∀ v, n.1.1 (g v) = g (n.1.1 v) := by
      intro g hg v
      have := hcent (toGamma F V g) ⟨g, hg, rfl⟩
      exact (congrArg (fun m : gammaL F V => m.1 v) this).symm
    have hsc : ∀ (c : F) (v : V), n.1.1 (c • v) = c • n.1.1 v := by
      intro c v
      by_cases hc : c = 0
      · subst hc
        simp [gammaL_map_zero ha]
      · have := hcomm (scalarHom F V (Units.mk0 c hc)) (hD.scalar_mem _) v
        simpa [scalarHom_apply] using this
    let aL : V →ₗ[F] V := { toFun := n.1.1, map_add' := ha.1, map_smul' := hsc }
    obtain ⟨c, hc⟩ := eq_smul_of_commute_irreducible hD.finrank_eq L hD.irreducible
      hD.nonabelian aL (fun g hg v => hcomm g hg v)
    have hVnt : Nontrivial V := by
      rw [← Module.finrank_pos_iff (R := F)]
      have := hD.finrank_eq
      omega
    obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
    have hc0 : c ≠ 0 := by
      intro h0
      have h1 : n.1.1 v₀ = 0 := by
        have := hc v₀
        simpa [aL, h0] using this
      exact gammaL_ne_zero ha hv₀ h1
    refine ⟨Units.mk0 c hc0, Subtype.ext (Equiv.ext fun v => ?_)⟩
    show n.1.1 v = (scalarHom F V (Units.mk0 c hc0)) v
    rw [scalarHom_apply]
    exact hc v
  · rintro ⟨c, hc⟩
    refine Equiv.ext fun z => Subtype.ext ((hθ n z).trans ?_)
    show pointAct n.1 z = z
    rw [hc]
    exact pointAct_scalar c z.1

end Main

end CFSG.QuasithinUnique.Setup.X3
