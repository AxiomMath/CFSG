module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFKindDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFSimFaith

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {G : Type} [Group G] {L : Subgroup G}

@[expose] noncomputable def ffPhi {hQ : Q.Nondegenerate} (hz : Subgroup.center ↥L = ⊥)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) : ↥L ≃* omegaProj hQ :=
  (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hz.symm)).trans e

theorem ffPhi_apply {hQ : Q.Nondegenerate} (hz : Subgroup.center ↥L = ⊥)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (l : ↥L) :
    ffPhi hz e l = e (QuotientGroup.mk l) := by
  rfl

theorem ff_phi_conj (hQ : Q.Nondegenerate) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (hz : Subgroup.center ↥L = ⊥) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {s : G}
    {x : ProjSim Q} (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x) (l l' : ↥L)
    (hl : (l' : G) = s * l * s⁻¹) :
    ffSimOmegaAct hQ h2 x (ffPhi hz e l) = ffPhi hz e l' := by
  apply Subtype.ext
  rw [coe_ffSimOmegaAct, ffPhi_apply, ffPhi_apply]
  exact (hs.2 l l' hl).symm

theorem ff_phi_mem_fix_iff (hQ : Q.Nondegenerate) (h5 : 5 ≤ Module.finrank (ZMod 3) V)
    (hz : Subgroup.center ↥L = ⊥) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {s : G}
    {x : ProjSim Q} (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x) (l : ↥L) :
    ffPhi hz e l ∈ ffFix hQ (by omega) x ↔ s * (l : G) = (l : G) * s := by
  have hl' : s * (l : G) * s⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hs.1 (l : G)).mp l.2
  let l' : ↥L := ⟨s * (l : G) * s⁻¹, hl'⟩
  have hconj := ff_phi_conj hQ (by omega) hz e hs l l' rfl
  show ffSimOmegaAct hQ (by omega) x (ffPhi hz e l) = ffPhi hz e l ↔ _
  rw [hconj]
  constructor
  · intro h
    have h2 : s * (l : G) * s⁻¹ = l := congrArg Subtype.val ((ffPhi hz e).injective h)
    calc s * (l : G) = (s * (l : G) * s⁻¹) * s := by group
      _ = (l : G) * s := by rw [h2]
  · intro h
    have : l' = l := Subtype.ext (by
      show s * (l : G) * s⁻¹ = l
      rw [h]; group)
    rw [this]

theorem ff_conj_mem {s : G} (hs : s ∈ Subgroup.normalizer (L : Set G)) (l : ↥L) :
    s * (l : G) * s⁻¹ ∈ L :=
  (Subgroup.mem_normalizer_iff.mp hs (l : G)).mp l.2

theorem ff_innerOn_decompose {s : G} (h : InnerOn L s) :
    ∃ l ∈ L, ∃ c ∈ centralizer (L : Set G), s = l * c := by
  classical
  let C : Subgroup G := centralizer (L : Set G)
  have hmem : s ∈ L ⊔ C := h
  have hmain : ∀ x ∈ (L ⊔ C : Subgroup G), ∃ l ∈ L, ∃ c ∈ C, x = l * c := by
    intro x hx
    rw [Subgroup.sup_eq_closure] at hx
    refine Subgroup.closure_induction (p := fun x _ => ∃ l ∈ L, ∃ c ∈ C, x = l * c)
      ?_ ?_ ?_ ?_ hx
    · rintro y (hy | hy)
      · exact ⟨y, hy, 1, C.one_mem, by simp⟩
      · exact ⟨1, L.one_mem, y, hy, by simp⟩
    · exact ⟨1, L.one_mem, 1, C.one_mem, by simp⟩
    · rintro y z _ _ ⟨l₁, hl₁, c₁, hc₁, rfl⟩ ⟨l₂, hl₂, c₂, hc₂, rfl⟩
      refine ⟨l₁ * l₂, L.mul_mem hl₁ hl₂, c₁ * c₂, C.mul_mem hc₁ hc₂, ?_⟩
      have hcomm : c₁ * l₂ = l₂ * c₁ := (Subgroup.mem_centralizer_iff.mp hc₁ l₂ hl₂).symm
      calc (l₁ * c₁) * (l₂ * c₂) = l₁ * (c₁ * l₂) * c₂ := by group
        _ = l₁ * (l₂ * c₁) * c₂ := by rw [hcomm]
        _ = (l₁ * l₂) * (c₁ * c₂) := by group
    · rintro y _ ⟨l, hl, c, hc, rfl⟩
      refine ⟨l⁻¹, L.inv_mem hl, c⁻¹, C.inv_mem hc, ?_⟩
      have hcomm : c * l = l * c := (Subgroup.mem_centralizer_iff.mp hc l hl).symm
      rw [mul_inv_rev, ← mul_inv_rev c l, hcomm, mul_inv_rev]
  exact hmain s hmem

theorem ff_exists_centEquiv (hQ : Q.Nondegenerate) (h5 : 5 ≤ Module.finrank (ZMod 3) V)
    (hz : Subgroup.center ↥L = ⊥) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {s : G}
    {x : ProjSim Q} (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x) :
    ∃ f : ↥(L ⊓ centralizer ({s} : Set G)) ≃* ↥(ffFix hQ (by omega) x),
      ∀ c : ↥(L ⊓ centralizer ({s} : Set G)),
        ((f c : ↥(ffFix hQ (by omega) x)) : ↥(omegaProj hQ)) =
          ffPhi hz e ⟨(c : G), (Subgroup.mem_inf.mp c.2).1⟩ := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  let g : ↥(L ⊓ centralizer ({s} : Set G)) →* omegaProj hQ :=
    (ffPhi hz e).toMonoidHom.comp (Subgroup.inclusion (inf_le_left : L ⊓ _ ≤ L))
  have hmem : ∀ c : ↥(L ⊓ centralizer ({s} : Set G)), g c ∈ ffFix hQ h2 x := fun c =>
    (ff_phi_mem_fix_iff hQ h5 hz e hs ⟨(c : G), (Subgroup.mem_inf.mp c.2).1⟩).mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp c.2).2).symm
  let f0 : ↥(L ⊓ centralizer ({s} : Set G)) →* ↥(ffFix hQ h2 x) := g.codRestrict _ hmem
  have hinj : Function.Injective f0 := by
    intro c c' h
    have h1 : g c = g c' := congrArg Subtype.val h
    have h2' := (ffPhi hz e).injective h1
    exact Subgroup.inclusion_injective _ h2'
  have hsurj : Function.Surjective f0 := by
    intro w
    obtain ⟨l, hl⟩ := (ffPhi hz e).surjective (w : ↥(omegaProj hQ))
    have hfix : ffPhi hz e l ∈ ffFix hQ h2 x := by rw [hl]; exact w.2
    have hcomm := (ff_phi_mem_fix_iff hQ h5 hz e hs l).mp hfix
    refine ⟨⟨(l : G), Subgroup.mem_inf.mpr ⟨l.2,
      Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm⟩⟩, ?_⟩
    exact Subtype.ext hl
  exact ⟨MulEquiv.ofBijective f0 ⟨hinj, hsurj⟩, fun c => rfl⟩

theorem ff_centralizer_iff_eq_one (hQ : Q.Nondegenerate) (h5 : 5 ≤ Module.finrank (ZMod 3) V)
    (hz : Subgroup.center ↥L = ⊥) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {s : G}
    {x : ProjSim Q} (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x) :
    s ∈ centralizer (L : Set G) ↔ x = 1 := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  constructor
  · intro hc
    apply ffSimOmegaAct_injective hQ h5
    rw [map_one]
    apply MulEquiv.ext
    intro w
    obtain ⟨l, rfl⟩ := (ffPhi hz e).surjective w
    have hl : s * (l : G) * s⁻¹ ∈ L := ff_conj_mem hs.1 l
    have hcomm : (l : G) * s = s * (l : G) := Subgroup.mem_centralizer_iff.mp hc l l.2
    have key := ff_phi_conj hQ h2 hz e hs l ⟨s * (l : G) * s⁻¹, hl⟩ rfl
    rw [key, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    show s * (l : G) * s⁻¹ = l
    rw [← hcomm]; group
  · intro hx1
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hfix : ffPhi hz e ⟨l, hl⟩ ∈ ffFix hQ h2 x := by
      show ffSimOmegaAct hQ h2 x (ffPhi hz e ⟨l, hl⟩) = _
      rw [hx1, map_one]; rfl
    exact ((ff_phi_mem_fix_iff hQ h5 hz e hs ⟨l, hl⟩).mp hfix).symm

theorem ff_innerOn_iff (hQ : Q.Nondegenerate) (h5 : 5 ≤ Module.finrank (ZMod 3) V)
    (hz : Subgroup.center ↥L = ⊥) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {s : G}
    {x : ProjSim Q} (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x) :
    InnerOn L s ↔ SimInOmegaStar hQ x := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  constructor
  · intro hin
    obtain ⟨l, hl, c, hc, rfl⟩ := ff_innerOn_decompose hin
    refine ⟨((ffPhi hz e ⟨l, hl⟩ : ↥(omegaProj hQ)) : ProjOrth Q), (ffPhi hz e ⟨l, hl⟩).2, ?_⟩
    apply ffSimOmegaAct_injective hQ h5
    rw [ffSimOmegaAct_projOrthToProjSim]
    apply MulEquiv.ext
    intro w
    obtain ⟨m, rfl⟩ := (ffPhi hz e).surjective w
    have hm : (l * c) * (m : G) * (l * c)⁻¹ ∈ L := ff_conj_mem hs.1 m
    have key := ff_phi_conj hQ h2 hz e hs m ⟨_, hm⟩ rfl
    rw [key]
    have hceq : (l * c) * (m : G) * (l * c)⁻¹ = l * (m : G) * l⁻¹ := by
      have hcm : c * (m : G) = (m : G) * c := (Subgroup.mem_centralizer_iff.mp hc m m.2).symm
      calc (l * c) * (m : G) * (l * c)⁻¹ = l * (c * (m : G) * c⁻¹) * l⁻¹ := by group
        _ = l * (m : G) * l⁻¹ := by rw [hcm]; group
    have hmk : (⟨(l * c) * (m : G) * (l * c)⁻¹, hm⟩ : ↥L) = ⟨l, hl⟩ * m * ⟨l, hl⟩⁻¹ :=
      Subtype.ext hceq
    rw [hmk, map_mul, map_mul, map_inv]
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    rfl
  · rintro ⟨y, hy, hxy⟩
    set l : ↥L := (ffPhi hz e).symm ⟨y, hy⟩ with hl_def
    have hφl : ffPhi hz e l = ⟨y, hy⟩ := (ffPhi hz e).apply_symm_apply _
    have hc : (l : G)⁻¹ * s ∈ centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      have hm' : s * m * s⁻¹ ∈ L := ff_conj_mem hs.1 ⟨m, hm⟩
      have key := ff_phi_conj hQ h2 hz e hs ⟨m, hm⟩ ⟨_, hm'⟩ rfl
      rw [← hxy, ffSimOmegaAct_projOrthToProjSim] at key
      have hk : ffPhi hz e (l * ⟨m, hm⟩ * l⁻¹) = ffPhi hz e ⟨s * m * s⁻¹, hm'⟩ := by
        rw [map_mul, map_mul, map_inv, hφl, ← key]
        apply Subtype.ext
        rw [MulAut.conjNormal_apply]
        rfl
      have h4 : (l : G) * m * (l : G)⁻¹ = s * m * s⁻¹ :=
        congrArg Subtype.val ((ffPhi hz e).injective hk)
      calc m * ((l : G)⁻¹ * s) = (l : G)⁻¹ * ((l : G) * m * (l : G)⁻¹) * s := by group
        _ = (l : G)⁻¹ * (s * m * s⁻¹) * s := by rw [h4]
        _ = ((l : G)⁻¹ * s) * m := by group
    have hs_eq : s = (l : G) * ((l : G)⁻¹ * s) := by group
    show s ∈ L ⊔ centralizer (L : Set G)
    rw [hs_eq]
    exact Subgroup.mul_mem_sup l.2 hc

theorem ff_induces_sq (hQ : Q.Nondegenerate) (h5 : 5 ≤ Module.finrank (ZMod 3) V)
    (hz : Subgroup.center ↥L = ⊥) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {s : G}
    {x : ProjSim Q} (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x) (hss : s * s = 1) :
    x * x = 1 := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  apply ffSimOmegaAct_injective hQ h5
  rw [map_mul, map_one]
  apply MulEquiv.ext
  intro w
  obtain ⟨l, rfl⟩ := (ffPhi hz e).surjective w
  have hl : s * (l : G) * s⁻¹ ∈ L := ff_conj_mem hs.1 l
  let l' : ↥L := ⟨_, hl⟩
  have hl2 : s * (l' : G) * s⁻¹ ∈ L := ff_conj_mem hs.1 l'
  have k1 := ff_phi_conj hQ h2 hz e hs l l' rfl
  have k2 := ff_phi_conj hQ h2 hz e hs l' ⟨_, hl2⟩ rfl
  rw [MulAut.mul_apply, k1, k2, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  show s * (s * (l : G) * s⁻¹) * s⁻¹ = l
  calc s * (s * (l : G) * s⁻¹) * s⁻¹ = (s * s) * l * (s * s)⁻¹ := by group
    _ = l := by rw [hss]; group

theorem ff_induces_of_mem (hQ : Q.Nondegenerate) (hz : Subgroup.center ↥L = ⊥)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {u : G} (hu : u ∈ L) :
    InducesViaP L (Subgroup.center ↥L) hQ e u
      (projOrthToProjSim Q ((ffPhi hz e ⟨u, hu⟩ : ↥(omegaProj hQ)) : ProjOrth Q)) := by
  have hnorm : u ∈ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact L.mul_mem (L.mul_mem hu hh) (L.inv_mem hu)
    · intro hh
      have h3 := L.mul_mem (L.mul_mem (L.inv_mem hu) hh) hu
      have h4 : u⁻¹ * (u * h * u⁻¹) * u = h := by group
      rwa [h4] at h3
  refine ⟨hnorm, ?_⟩
  intro l l' hl
  rw [projSimAct_projOrthToProjSim]
  have hl' : l' = ⟨u, hu⟩ * l * ⟨u, hu⟩⁻¹ := Subtype.ext hl
  have h1 : e (QuotientGroup.mk l') = ffPhi hz e ⟨u, hu⟩ * e (QuotientGroup.mk l) *
      (ffPhi hz e ⟨u, hu⟩)⁻¹ := by
    rw [hl', ffPhi_apply]
    simp
  rw [h1]
  rfl

theorem ff_mem_conjClass_iff (hQ : Q.Nondegenerate) (hz : Subgroup.center ↥L = ⊥)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {u u' : G} (hu : u ∈ L) (hu' : u' ∈ L) :
    u' ∈ conjClassIn L u ↔
      ∃ a : ↥(omegaProj hQ), a * ffPhi hz e ⟨u, hu⟩ * a⁻¹ = ffPhi hz e ⟨u', hu'⟩ := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    refine ⟨ffPhi hz e ⟨h, hh⟩, ?_⟩
    have hmk : (⟨h * u * h⁻¹, hu'⟩ : ↥L) = ⟨h, hh⟩ * ⟨u, hu⟩ * ⟨h, hh⟩⁻¹ := rfl
    rw [hmk, map_mul, map_mul, map_inv]
  · rintro ⟨a, ha⟩
    obtain ⟨h, rfl⟩ := (ffPhi hz e).surjective a
    have hmk : ffPhi hz e (h * ⟨u, hu⟩ * h⁻¹) = ffPhi hz e ⟨u', hu'⟩ := by
      rw [map_mul, map_mul, map_inv]; exact ha
    have h3 : (h : G) * u * (h : G)⁻¹ = u' := congrArg Subtype.val ((ffPhi hz e).injective hmk)
    exact ⟨h, h.2, h3.symm⟩

theorem ff_cover_iff (hQ : Q.Nondegenerate) (h5 : 5 ≤ Module.finrank (ZMod 3) V)
    (hz : Subgroup.center ↥L = ⊥) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {s : G}
    {x : ProjSim Q} (hs : InducesViaP L (Subgroup.center ↥L) hQ e s x) (hss : s * s = 1)
    {u : G} (hu : u ∈ L) :
    s * u ∈ conjClassIn L s ↔
      ∃ a : ↥(omegaProj hQ), ffSimOmegaAct hQ (by omega) x a * a⁻¹ = ffPhi hz e ⟨u, hu⟩ := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have hs1 : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  constructor
  · rintro ⟨h, hh, hsu⟩
    refine ⟨ffPhi hz e ⟨h, hh⟩, ?_⟩
    have hsh : s * h * s⁻¹ ∈ L := ff_conj_mem hs.1 ⟨h, hh⟩
    rw [ff_phi_conj hQ h2 hz e hs ⟨h, hh⟩ ⟨_, hsh⟩ rfl, ← map_inv, ← map_mul]
    congr 1
    apply Subtype.ext
    show s * h * s⁻¹ * h⁻¹ = u
    calc s * h * s⁻¹ * h⁻¹ = s⁻¹ * (h * s * h⁻¹) := by rw [hs1]; group
      _ = s⁻¹ * (s * u) := by rw [hsu]
      _ = u := by group
  · rintro ⟨a, ha⟩
    obtain ⟨h, rfl⟩ := (ffPhi hz e).surjective a
    have hsh : s * (h : G) * s⁻¹ ∈ L := ff_conj_mem hs.1 h
    rw [ff_phi_conj hQ h2 hz e hs h ⟨_, hsh⟩ rfl, ← map_inv, ← map_mul] at ha
    have h3 : s * (h : G) * s⁻¹ * (h : G)⁻¹ = u :=
      congrArg Subtype.val ((ffPhi hz e).injective ha)
    refine ⟨h, h.2, ?_⟩
    calc s * u = s * (s * (h : G) * s⁻¹ * (h : G)⁻¹) := by rw [h3]
      _ = (s * s) * (h : G) * s⁻¹ * (h : G)⁻¹ := by group
      _ = (h : G) * s * (h : G)⁻¹ := by rw [hss, one_mul, hs1]

theorem ff_exists_model_six_plus [Finite G] (h : IsOm6P L) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V) (_ : FiniteDimensional (ZMod 3) V)
      (Q : QuadraticForm (ZMod 3) V) (hQ : Q.Nondegenerate)
      (_ : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ),
      Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = 1 := by
  obtain ⟨V, _, _, _, Q, hQ, hdim, hsgn, ⟨e⟩⟩ := ff_isOmegaStar_center_six_plus h
  exact ⟨V, inferInstance, inferInstance, inferInstance, Q, hQ, e, hdim, hsgn⟩

end CFSG.OddStandard.SmallF3.Omega
