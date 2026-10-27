module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MFixHom
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MTwistAux1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

section Twist

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] def ff6mTwistSub (ρ : ↥(simGroup Q)) : Subgroup (OGroup Q) where
  carrier := {g | simAct Q ρ g = g ∨ simAct Q ρ g = piOrth Q * g}
  mul_mem' := by
    intro a b ha hb
    have hc : ∀ g : OGroup Q, g * piOrth Q = piOrth Q * g := fun g =>
      (Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q)) g)
    change simAct Q ρ (a * b) = a * b ∨ simAct Q ρ (a * b) = piOrth Q * (a * b)
    have ha' : simAct Q ρ a = a ∨ simAct Q ρ a = piOrth Q * a := ha
    have hb' : simAct Q ρ b = b ∨ simAct Q ρ b = piOrth Q * b := hb
    rw [map_mul]
    rcases ha' with h1 | h1 <;> rcases hb' with h2 | h2 <;> rw [h1, h2]
    · exact Or.inl rfl
    · right
      calc a * (piOrth Q * b) = (a * piOrth Q) * b := by rw [mul_assoc]
        _ = (piOrth Q * a) * b := by rw [hc a]
        _ = piOrth Q * (a * b) := by rw [mul_assoc]
    · right
      rw [mul_assoc]
    · left
      calc piOrth Q * a * (piOrth Q * b) = piOrth Q * (a * piOrth Q) * b := by simp only [mul_assoc]
        _ = piOrth Q * (piOrth Q * a) * b := by rw [hc a]
        _ = (piOrth Q * piOrth Q) * (a * b) := by simp only [mul_assoc]
        _ = a * b := by rw [piOrth_mul_self, one_mul]
  one_mem' := Or.inl (map_one _)
  inv_mem' := by
    intro a ha
    have hc : ∀ g : OGroup Q, g * piOrth Q = piOrth Q * g := fun g =>
      (Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q)) g)
    change simAct Q ρ a⁻¹ = a⁻¹ ∨ simAct Q ρ a⁻¹ = piOrth Q * a⁻¹
    have ha' : simAct Q ρ a = a ∨ simAct Q ρ a = piOrth Q * a := ha
    rw [map_inv]
    rcases ha' with h1 | h1 <;> rw [h1]
    · exact Or.inl rfl
    · right
      have hpi : (piOrth Q)⁻¹ = piOrth Q := inv_eq_of_mul_eq_one_right piOrth_mul_self
      rw [mul_inv_rev, hpi, hc a⁻¹]

theorem mem_ff6mTwistSub_iff {ρ : ↥(simGroup Q)} {g : OGroup Q} :
    g ∈ ff6mTwistSub ρ ↔ simAct Q ρ g = g ∨ simAct Q ρ g = piOrth Q * g := Iff.rfl

private theorem piOrth_cancel_left (x : OGroup Q) : piOrth Q * (piOrth Q * x) = x := by
  rw [← mul_assoc, piOrth_mul_self, one_mul]

private theorem piOrth_mul_mul (a b : OGroup Q) :
    (piOrth Q * a) * (piOrth Q * b) = a * b := by
  rw [show (piOrth Q * a) * (piOrth Q * b) = piOrth Q * (a * (piOrth Q * b)) by
      simp only [mul_assoc]]
  rw [← mul_assoc a (piOrth Q) b, mul_piOrth_comm a, mul_assoc]
  exact piOrth_cancel_left (a * b)

private theorem piOrth_conj_mul (a b : OGroup Q) :
    (piOrth Q * a) * b * (piOrth Q * a)⁻¹ = a * b * a⁻¹ := by
  have hci : (piOrth Q * a)⁻¹ = piOrth Q * a⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right piOrth_mul_self, mul_piOrth_comm a⁻¹]
  rw [hci]
  rw [show (piOrth Q * a) * b * (piOrth Q * a⁻¹) =
      piOrth Q * (a * (b * (piOrth Q * a⁻¹))) by simp only [mul_assoc]]
  rw [(mul_piOrth_comm a⁻¹).symm, ← mul_assoc b a⁻¹ (piOrth Q),
    ← mul_assoc a (b * a⁻¹) (piOrth Q), mul_piOrth_comm (a * (b * a⁻¹))]
  exact piOrth_cancel_left (a * (b * a⁻¹))

theorem fixSub_simAct_orthToSim (t : OGroup Q) :
    fixSub (simAct Q (orthToSim Q t)) = Subgroup.centralizer ({t} : Set (OGroup Q)) := by
  ext g
  rw [mem_fixSub_iff, simAct_orthToSim, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g * t = (t * g * t⁻¹) * t := by rw [h]
      _ = t * g := by group
  · intro h
    calc t * g * t⁻¹ = (g * t) * t⁻¹ := by rw [h]
      _ = g := by group

variable (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = -1)
  (ρ : ↥(simGroup Q))

include hsgn in
@[expose] noncomputable def ff6mTwistHom :
    ↥(omegaGroup hQ ⊓ ff6mTwistSub ρ) →*
      ↥(ffFix hQ (by omega) (QuotientGroup.mk ρ : ProjSim Q)) :=
  ((omegaToProj hQ).comp (Subgroup.inclusion inf_le_left)).codRestrict _ (fun g =>
    (ff6m_mem_ffFix_sim_iff hQ hdim hsgn ρ _).mpr
      ⟨g.1, (Subgroup.mem_inf.mp g.2).1, (Subgroup.mem_inf.mp g.2).2, rfl⟩)

private theorem ff6m_mem_ffFix_sim_iff_aux (w : ↥(omegaProj hQ)) :
    w ∈ ffFix hQ (by omega) (QuotientGroup.mk ρ : ProjSim Q) ↔
      ∃ g ∈ omegaGroup hQ, (simAct Q ρ g = g ∨ simAct Q ρ g = piOrth Q * g) ∧
        toProj Q g = (w : ProjOrth Q) := by
  obtain ⟨w, hw⟩ := w
  obtain ⟨g₀, hg₀, rfl⟩ := (mem_omegaProj_iff hQ).mp hw
  constructor
  · intro hfix
    have h1 : toProj Q (simAct Q ρ g₀) = toProj Q g₀ := by
      have h0 := congrArg Subtype.val (mem_fixSub_iff.mp hfix)
      rwa [coe_ffSimOmegaAct, projSimAct_mk, projActAux_toProj] at h0
    have h3 : (simAct Q ρ g₀)⁻¹ * g₀ ∈ piGroup Q := QuotientGroup.eq.mp h1
    refine ⟨g₀, hg₀, ?_, rfl⟩
    rcases mem_piGroup_iff.mp h3 with h4 | h4
    · exact Or.inl (inv_mul_eq_one.mp h4)
    · right
      have h5 : g₀ = simAct Q ρ g₀ * piOrth Q := inv_mul_eq_iff_eq_mul.mp h4
      have h6 : simAct Q ρ g₀ = g₀ * piOrth Q :=
        calc simAct Q ρ g₀ = simAct Q ρ g₀ * (piOrth Q * piOrth Q) := by
              rw [piOrth_mul_self, mul_one]
          _ = (simAct Q ρ g₀ * piOrth Q) * piOrth Q := by rw [mul_assoc]
          _ = g₀ * piOrth Q := by rw [← h5]
      rw [h6]
      exact Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q)) g₀
  · rintro ⟨g, hg, hgc, hgw⟩
    apply mem_fixSub_iff.mpr
    apply Subtype.ext
    rw [coe_ffSimOmegaAct, projSimAct_mk, ← hgw, projActAux_toProj]
    rcases hgc with h | h
    · rw [h]
    · rw [h, map_mul, toProj_piOrth, one_mul]

private noncomputable def ff6mTwistHomAux :
    ↥(omegaGroup hQ ⊓ ff6mTwistSub ρ) →*
      ↥(ffFix hQ (by omega) (QuotientGroup.mk ρ : ProjSim Q)) :=
  ((omegaToProj hQ).comp (Subgroup.inclusion inf_le_left)).codRestrict _ (fun g =>
    (ff6m_mem_ffFix_sim_iff_aux (Q := Q) (V := V) (hQ := hQ) (hdim := hdim) (ρ := ρ) _).mpr
      ⟨g.1, (Subgroup.mem_inf.mp g.2).1, (Subgroup.mem_inf.mp g.2).2, rfl⟩)

private theorem ff6mTwistHomAux_surjective :
    Function.Surjective (ff6mTwistHomAux (Q := Q) (V := V) (hQ := hQ) (hdim := hdim) (ρ := ρ)) := by
  intro w
  obtain ⟨g, hg, hgc, hgw⟩ :=
    (ff6m_mem_ffFix_sim_iff_aux (Q := Q) (V := V) (hQ := hQ) (hdim := hdim) (ρ := ρ)
      (w : ↥(omegaProj hQ))).mp w.2
  exact ⟨⟨g, Subgroup.mem_inf.mpr ⟨hg, hgc⟩⟩, Subtype.ext (Subtype.ext hgw)⟩

private theorem ff6mTwistHomAux_eq_one_iff (g : ↥(omegaGroup hQ ⊓ ff6mTwistSub ρ)) :
    ff6mTwistHomAux (Q := Q) (V := V) (hQ := hQ) (hdim := hdim) (ρ := ρ) g = 1 ↔
      (g : OGroup Q) = 1 ∨ (g : OGroup Q) = piOrth Q := by
  rw [← omegaToProj_eq_one_iff hQ ⟨g.1, (Subgroup.mem_inf.mp g.2).1⟩]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem ff6mTwistHom_surjective : Function.Surjective (ff6mTwistHom hQ hdim hsgn ρ) := by
  intro w
  obtain ⟨g, hg, hgc, hgw⟩ :=
    (ff6m_mem_ffFix_sim_iff hQ hdim hsgn ρ (w : ↥(omegaProj hQ))).mp w.2
  exact ⟨⟨g, Subgroup.mem_inf.mpr ⟨hg, hgc⟩⟩, Subtype.ext (Subtype.ext hgw)⟩

theorem ff6mTwistHom_eq_one_iff (g : ↥(omegaGroup hQ ⊓ ff6mTwistSub ρ)) :
    ff6mTwistHom hQ hdim hsgn ρ g = 1 ↔
      (g : OGroup Q) = 1 ∨ (g : OGroup Q) = piOrth Q := by
  rw [← omegaToProj_eq_one_iff hQ ⟨g.1, (Subgroup.mem_inf.mp g.2).1⟩]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem ff6mTwist_mul_self_mem {g : OGroup Q} (hg : g ∈ ff6mTwistSub ρ) :
    g * g ∈ fixSub (simAct Q ρ) := by
  rw [mem_fixSub_iff, map_mul]
  rw [mem_ff6mTwistSub_iff] at hg
  rcases hg with h | h
  · rw [h]
  · rw [h]
    exact piOrth_mul_mul g g

theorem ff6mTwist_conj_mem_fixSub {g h : OGroup Q} (hg : g ∈ ff6mTwistSub ρ)
    (hh : h ∈ fixSub (simAct Q ρ)) : g * h * g⁻¹ ∈ fixSub (simAct Q ρ) := by
  rw [mem_fixSub_iff, map_mul, map_mul, map_inv]
  have hfix : simAct Q ρ h = h := mem_fixSub_iff.mp hh
  rw [hfix]
  rw [mem_ff6mTwistSub_iff] at hg
  rcases hg with hz | hz
  · rw [hz]
  · rw [hz]
    exact piOrth_conj_mul g h

theorem ff6mTwist_conj_mem_commutator {g h : OGroup Q} (hg : g ∈ ff6mTwistSub ρ)
    (hh : h ∈ ⁅fixSub (simAct Q ρ), fixSub (simAct Q ρ)⁆) :
    g * h * g⁻¹ ∈ ⁅fixSub (simAct Q ρ), fixSub (simAct Q ρ)⁆ := by
  let C : Subgroup (OGroup Q) := fixSub (simAct Q ρ)
  have hh' : h ∈ ⁅C, C⁆ := hh
  have hmap : C.map (MulAut.conj g).toMonoidHom ≤ C := by
    rintro x ⟨y, hy, rfl⟩
    change g * y * g⁻¹ ∈ C
    exact ff6mTwist_conj_mem_fixSub ρ hg hy
  have hmem : (MulAut.conj g) h ∈ (⁅C, C⁆).map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hh'
  rw [Subgroup.map_commutator] at hmem
  have hle : ⁅C.map (MulAut.conj g).toMonoidHom, C.map (MulAut.conj g).toMonoidHom⁆ ≤
      ⁅C, C⁆ := Subgroup.commutator_mono hmap hmap
  have hthis : (MulAut.conj g) h ∈ ⁅C, C⁆ := hle hmem
  rwa [MulAut.conj_apply] at hthis

theorem ff6m_solvable_of_twist
    (hA : Group.IsSolvable ↥(omegaGroup hQ ⊓ fixSub (simAct Q ρ))) :
    Group.IsSolvable ↥(ffFix hQ (by omega) (QuotientGroup.mk ρ : ProjSim Q)) := by
  haveI : Finite (OGroup Q) := inferInstance
  let A : Subgroup (OGroup Q) := omegaGroup hQ ⊓ fixSub (simAct Q ρ)
  let Nsub : Subgroup (OGroup Q) := omegaGroup hQ ⊓ ff6mTwistSub ρ
  let φ : ↥Nsub →* ↥(ffFix hQ (by omega) (QuotientGroup.mk ρ : ProjSim Q)) :=
    ff6mTwistHomAux (hQ := hQ) (hdim := hdim) (ρ := ρ)
  have hAle : A ≤ Nsub := fun x hx => by
    obtain ⟨hxω, hxf⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr
      ⟨hxω, mem_ff6mTwistSub_iff.mpr (Or.inl (mem_fixSub_iff.mp hxf))⟩
  let A' : Subgroup ↥Nsub := A.subgroupOf Nsub
  haveI hA'norm : A'.Normal := by
    show (A.subgroupOf Nsub).Normal
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hAle, Subgroup.le_normalizer_iff]
    intro x hx y hy
    obtain ⟨hxω, hxtw⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hyω, hyf⟩ := Subgroup.mem_inf.mp hy
    exact Subgroup.mem_inf.mpr ⟨(omegaGroup_normal hQ).conj_mem y hyω x,
      ff6mTwist_conj_mem_fixSub ρ hxtw hyf⟩
  haveI hAsol : Group.IsSolvable ↥A := hA
  haveI hA'sol : Group.IsSolvable ↥A' :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hAle).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hAle).injective
  have hsq' : ∀ g : ↥Nsub, g * g ∈ A' := by
    intro g
    obtain ⟨hgω, hgtw⟩ := Subgroup.mem_inf.mp g.2
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_inf.mpr ⟨mul_mem hgω hgω, ff6mTwist_mul_self_mem ρ hgtw⟩
  haveI : Group.IsSolvable ↥Nsub := ff6m_solvable_of_sq_mem A' hA'sol hsq'
  refine Group.isSolvable_of_surjective (f := φ) ?_
  exact ff6mTwistHomAux_surjective (hQ := hQ) (hdim := hdim) (ρ := ρ)

theorem ff6m_xTwoCore_of_twist
    (hA : XTwoCore ↥(omegaGroup hQ ⊓ fixSub (simAct Q ρ))) :
    XTwoCore ↥(ffFix hQ (by omega) (QuotientGroup.mk ρ : ProjSim Q)) := by
  haveI : Finite (OGroup Q) := inferInstance
  let A : Subgroup (OGroup Q) := omegaGroup hQ ⊓ fixSub (simAct Q ρ)
  let Nsub : Subgroup (OGroup Q) := omegaGroup hQ ⊓ ff6mTwistSub ρ
  let φ : ↥Nsub →* ↥(ffFix hQ (by omega) (QuotientGroup.mk ρ : ProjSim Q)) :=
    ff6mTwistHomAux (hQ := hQ) (hdim := hdim) (ρ := ρ)
  have hAle : A ≤ Nsub := fun x hx => by
    obtain ⟨hxω, hxf⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr
      ⟨hxω, mem_ff6mTwistSub_iff.mpr (Or.inl (mem_fixSub_iff.mp hxf))⟩
  let A' : Subgroup ↥Nsub := A.subgroupOf Nsub
  haveI hA'norm : A'.Normal := by
    show (A.subgroupOf Nsub).Normal
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hAle, Subgroup.le_normalizer_iff]
    intro x hx y hy
    obtain ⟨hxω, hxtw⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hyω, hyf⟩ := Subgroup.mem_inf.mp hy
    exact Subgroup.mem_inf.mpr ⟨(omegaGroup_normal hQ).conj_mem y hyω x,
      ff6mTwist_conj_mem_fixSub ρ hxtw hyf⟩
  have hA'two : XTwoCore ↥A' :=
    (ff_xTwoCore_congr (Subgroup.subgroupOfEquivOfLe hAle)).mpr hA
  have hsq' : ∀ g : ↥Nsub, g * g ∈ A' := by
    intro g
    obtain ⟨hgω, hgtw⟩ := Subgroup.mem_inf.mp g.2
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_inf.mpr ⟨mul_mem hgω hgω, ff6mTwist_mul_self_mem ρ hgtw⟩
  have hNtwo : XTwoCore ↥Nsub := ff6m_xTwoCore_of_sq_mem A' hA'two hsq'
  have hker : IsPGroup 2 φ.ker := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro x
    refine ⟨1, ?_⟩
    change x ^ 2 = 1
    rw [pow_two]
    apply Subtype.ext
    apply Subtype.ext
    have hx1 : φ (x : ↥Nsub) = 1 := x.2
    rcases (ff6mTwistHomAux_eq_one_iff (hQ := hQ) (hdim := hdim) (ρ := ρ)
      (x : ↥Nsub)).mp hx1 with hh1 | hh1
    · show ((x : ↥Nsub) : OGroup Q) * ((x : ↥Nsub) : OGroup Q) = 1
      rw [hh1, one_mul]
    · show ((x : ↥Nsub) : OGroup Q) * ((x : ↥Nsub) : OGroup Q) = 1
      rw [hh1, piOrth_mul_self]
  exact ff6m_xTwoCore_of_surj_two_ker φ
    (ff6mTwistHomAux_surjective (hQ := hQ) (hdim := hdim) (ρ := ρ)) hker hNtwo

theorem ff6m_layerModel_of_twist {tg : CFSG.Open.StatedLieTag} {n k : ℕ}
    (G1 : Subgroup (OGroup Q)) (hG1 : G1 ≤ omegaGroup hQ ⊓ fixSub (simAct Q ρ))
    (hnorm : ∀ g ∈ ff6mTwistSub ρ, ∀ h ∈ G1, g * h * g⁻¹ ∈ G1)
    (hLie : LieModel ↥G1 tg n 3 k)
    (hsq : ∀ g ∈ omegaGroup hQ ⊓ fixSub (simAct Q ρ), g * g ∈ G1)
    (hpi : piOrth Q ∉ G1) :
    LayerModel ↥(ffFix hQ (by omega) (QuotientGroup.mk ρ : ProjSim Q)) tg n k := by
  haveI : Finite (OGroup Q) := inferInstance
  let Nsub : Subgroup (OGroup Q) := omegaGroup hQ ⊓ ff6mTwistSub ρ
  let φ : ↥Nsub →* ↥(ffFix hQ (by omega) (QuotientGroup.mk ρ : ProjSim Q)) :=
    ff6mTwistHomAux (hQ := hQ) (hdim := hdim) (ρ := ρ)
  have hG1N : G1 ≤ Nsub := fun x hx => by
    obtain ⟨hxω, hxf⟩ := Subgroup.mem_inf.mp (hG1 hx)
    exact Subgroup.mem_inf.mpr
      ⟨hxω, mem_ff6mTwistSub_iff.mpr (Or.inl (mem_fixSub_iff.mp hxf))⟩
  let E0 : Subgroup ↥Nsub := G1.subgroupOf Nsub
  haveI hE0n : E0.Normal := by
    show (G1.subgroupOf Nsub).Normal
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hG1N, Subgroup.le_normalizer_iff]
    intro x hx y hy
    exact hnorm x (Subgroup.mem_inf.mp hx).2 y hy
  have hE0Lie : LieModel ↥E0 tg n 3 k :=
    LieModel.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hG1N).symm hLie
  have h2 : IsPGroup 2 (↥Nsub ⧸ E0) := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro x
    refine ⟨2, ?_⟩
    refine QuotientGroup.induction_on x (fun g => ?_)
    change (QuotientGroup.mk' E0 g) ^ 4 = 1
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have hfix : (g : OGroup Q) * (g : OGroup Q) ∈ fixSub (simAct Q ρ) :=
      ff6mTwist_mul_self_mem ρ (Subgroup.mem_inf.mp g.2).2
    have hmem := hsq _ (Subgroup.mem_inf.mpr
      ⟨mul_mem (Subgroup.mem_inf.mp g.2).1 (Subgroup.mem_inf.mp g.2).1, hfix⟩)
    have h4 : ((g : OGroup Q)) ^ 4 =
        ((g : OGroup Q) * (g : OGroup Q)) * ((g : OGroup Q) * (g : OGroup Q)) := by
      rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, pow_two]
    rw [Subgroup.mem_subgroupOf]
    change (Subgroup.subtype Nsub (g ^ 4)) ∈ G1
    rw [map_pow]
    change ((g : OGroup Q)) ^ 4 ∈ G1
    rw [h4]
    exact hmem
  have hinj : ∀ g ∈ E0, φ g = 1 → g = 1 := by
    intro g hg hg1
    have hgG1 : (g : OGroup Q) ∈ G1 := by
      rw [Subgroup.mem_subgroupOf] at hg
      exact hg
    rcases (ff6mTwistHomAux_eq_one_iff (hQ := hQ) (hdim := hdim) (ρ := ρ) g).mp hg1
      with h | h
    · exact Subtype.ext h
    · exact absurd (h ▸ hgG1) hpi
  exact ff6m_layerModel_of_surj φ
    (ff6mTwistHomAux_surjective (hQ := hQ) (hdim := hdim) (ρ := ρ)) E0 hE0Lie h2 hinj

end Twist

end CFSG.OddStandard.SmallF3.Omega
