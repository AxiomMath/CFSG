module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3Cases
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3Field
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8L1L3Rank
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55R3
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87BadSL3
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Simple

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

namespace EL3

open Subgroup CFSG CFSG.Blueprint CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12
  CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Act

variable {A : Type} [Group A] {J : Subgroup A} [J.Normal] {P : Type} [Group P]

@[expose] noncomputable def actP (e : ↥J ≃* P) : A →* MulAut P :=
  (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal

theorem actP_apply (e : ↥J ≃* P) (a : A) (x : ↥J) :
    actP e a (e x) = e (MulAut.conjNormal a x) := by
  simp [actP, MulAut.congr_apply]

theorem actP_injective (e : ↥J ≃* P) (hcent : centralizer (J : Set A) = ⊥) :
    Function.Injective (actP e) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hx : ∀ x : ↥J, MulAut.conjNormal a x = x := by
    intro x
    have := congrArg (fun φ : MulAut P => φ (e x)) ha
    simp only [actP_apply, MulAut.one_apply] at this
    exact e.injective this
  have hac : a ∈ centralizer (J : Set A) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have h1 := congrArg Subtype.val (hx ⟨j, hj⟩)
    rw [MulAut.conjNormal_apply] at h1
    calc j * a = (a * j * a⁻¹) * a := by rw [show a * j * a⁻¹ = j from h1]
      _ = a * j := by group
  rw [hcent] at hac
  exact Subgroup.mem_bot.mp hac

theorem actP_of_mem (e : ↥J ≃* P) (j : ↥J) : actP e (j : A) = MulAut.conj (e j) := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [actP_apply, MulAut.conj_apply]
  have : (MulAut.conjNormal (j : A) : MulAut ↥J) x = j * x * j⁻¹ :=
    Subtype.ext (by rw [MulAut.conjNormal_apply]; rfl)
  rw [this, map_mul, map_mul, map_inv]

end Act

section Field

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

theorem false_of_field (hInv : InvSec) (hctx : Stage2Ctx G z k S) (H : Subgroup G)
    {J : Subgroup (HBar H)} [J.Normal] {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hcard : Nat.card F = p ^ f) (e : ↥J ≃* projectiveSL 3 F)
    {u : HBar H} (hu : u * u = 1) (hu2 : orderOf u = 2) (B : GL (Fin 3) F) (σ : F ≃+* F)
    (hσ : σ ≠ 1) (hαeq : actP e u = conjAut 3 F B * fieldAut 3 F σ) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hα : actP e u * actP e u = 1 := by rw [← map_mul, hu, map_one]
  obtain ⟨F0, _, _, _, hodd0, h30, Q, -, hQfix, c, hc⟩ :=
    fl3_field_section hp hp2 hf hcard (actP e u) hα B σ hσ hαeq
  let ι : ↥Q →* HBar H := J.subtype.comp (e.symm.toMonoidHom.comp Q.subtype)
  have hι : Function.Injective ι := by
    intro a b hab
    apply Subtype.ext
    apply e.symm.injective
    exact Subtype.ext hab
  have hcomm : ∀ q : ↥Q, ι q ∈ centralizer ({u} : Set (HBar H)) := by
    intro q
    have h1 : actP e u (e (e.symm (q : projectiveSL 3 F))) = e (e.symm (q : projectiveSL 3 F)) := by
      rw [e.apply_symm_apply]
      exact hQfix q q.2
    rw [actP_apply] at h1
    have h3 := congrArg Subtype.val (e.injective h1)
    rw [MulAut.conjNormal_apply] at h3
    rw [Subgroup.mem_centralizer_singleton_iff]
    show ((e.symm (q : projectiveSL 3 F) : ↥J) : HBar H) * u =
      u * ((e.symm (q : projectiveSL 3 F) : ↥J) : HBar H)
    calc ((e.symm (q : projectiveSL 3 F) : ↥J) : HBar H) * u
        = (u * ((e.symm (q : projectiveSL 3 F) : ↥J) : HBar H) * u⁻¹) * u := by rw [h3]
      _ = u * ((e.symm (q : projectiveSL 3 F) : ↥J) : HBar H) := by group
  have hsecQ : IsSection (projectiveSL 3 F0) ↥Q :=
    ⟨⊤, c.comp (⊤ : Subgroup ↥Q).subtype, fun v => by
      obtain ⟨w, rfl⟩ := hc v
      exact ⟨⟨w, Subgroup.mem_top w⟩, rfl⟩⟩
  have hsecQ' : IsSection (projectiveSL 3 F0) ↥ι.range :=
    IsSection.of_equiv (MonoidHom.ofInjective hι).symm hsecQ
  have hle : ι.range ≤ centralizer ({u} : Set (HBar H)) := by
    rintro _ ⟨q, rfl⟩
    exact hcomm q
  have hsec : IsSection (projectiveSL 3 F0) ↥(centralizer ({u} : Set (HBar H))) :=
    IsSection.of_le_le hle hsecQ'
  have : IsSimpleGroup (projectiveSL 3 F0) := isSimpleGroup_projectiveSL3_fl3 F0
  have : Group.IsPerfect (projectiveSL 3 F0) := isPerfect_projectiveSL3_fl3 F0
  have : Nontrivial (projectiveSL 3 F0) := IsSimpleGroup.toNontrivial
  have hns : ¬ Group.IsSolvable (projectiveSL 3 F0) := Group.IsPerfect.not_isSolvable _
  have hKF := hbar_invsec hInv hctx H u hu2 (projectiveSL 3 F0) hns hsec
  exact not_kindFactorAll hp2 (involved_qdSL_projectiveSL3 (p := p))
    (not_card_dvd_factorial_projectiveSL3 hodd0 h30) hKF

theorem exists_graph_involution (hInv : InvSec) (hctx : Stage2Ctx G z k S) (H : Subgroup G)
    {J : Subgroup (HBar H)} [J.Normal] (hcent : centralizer (J : Set (HBar H)) = ⊥)
    {Y : Type} [Group Y] [Finite Y] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hp2 : p ≠ 2)
    (hLie : LieModel Y .PSL 3 p f) {F : Type} [Field F] [Finite F] (hcard : Nat.card F = p ^ f)
    (eJ : ↥J ≃* Y) (eY : Y ≃* projectiveSL 3 F) (E : Subgroup (HBar H))
    (hE : IsElementaryAbelian 2 ↥E) (h8 : 8 ≤ Nat.card ↥E) :
    ∃ u ∈ E, u ≠ 1 ∧ ∃ (B : GL (Fin 3) F) (σ : F ≃+* F),
      actP (eJ.trans eY) u = conjAut 3 F B * fieldAut 3 F σ * dualAut 3 F := by
  have : Fact p.Prime := ⟨hp⟩
  have hCharP : CharP F p := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hcard])
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (by rwa [ringChar.eq F p])
  by_contra hno
  push Not at hno
  have hEJ : ∀ u ∈ E, u ∈ J := by
    intro u hu
    by_cases hu1 : u = 1
    · rw [hu1]
      exact J.one_mem
    have hupow : u ^ 2 = 1 := by
      have := hE
      exact elemPow_eq_one_of_isElementaryAbelian (p := 2) u hu
    have hu2' : u * u = 1 := by rwa [pow_two] at hupow
    have hord : orderOf u = 2 := orderOf_eq_prime hupow hu1
    have hα : actP (eJ.trans eY) u * actP (eJ.trans eY) u = 1 := by
      rw [← map_mul, hu2', map_one]
    have hne : actP (eJ.trans eY) u ≠ 1 := fun h =>
      hu1 (actP_injective (eJ.trans eY) hcent (h.trans (map_one _).symm))
    rcases linear3_involution_cases h2 (actP (eJ.trans eY) u) hα hne with
      ⟨y, -, -, hy⟩ | ⟨B, σ, hσ, hB⟩ | ⟨B, -, hB⟩ | ⟨B, σ, hσ, hB⟩
    · have h1 : actP (eJ.trans eY) u =
          actP (eJ.trans eY) (((eJ.trans eY).symm y : ↥J) : HBar H) := by
        rw [actP_of_mem, MulEquiv.apply_symm_apply]
        exact hy
      rw [actP_injective (eJ.trans eY) hcent h1]
      exact ((eJ.trans eY).symm y).2
    · exact (false_of_field hInv hctx H hp hp2 hf hcard (eJ.trans eY) hu2' hord B σ hσ hB).elim
    · exact (hno u hu hu1 B 1 (by rw [map_one, mul_one]; exact hB)).elim
    · exact (hno u hu hu1 B σ hB).elim
  have hEJ' : E ≤ J := hEJ
  have := hE
  have hE0 : IsElementaryAbelian 2 ↥(E.subgroupOf J) := IsElementaryAbelian.subgroupOf hEJ'
  have hE1 : IsElementaryAbelian 2 ↥((E.subgroupOf J).map eJ.toMonoidHom) :=
    IsElementaryAbelian.map eJ.toMonoidHom
  have hcardE : Nat.card ↥((E.subgroupOf J).map eJ.toMonoidHom) = Nat.card ↥E := by
    rw [Subgroup.card_map_of_injective eJ.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEJ').toEquiv
  have h4 := L1.fl3_elemAbelian_le_four hp hf hp2 hLie _ hE1
  omega

end Field

end EL3

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
