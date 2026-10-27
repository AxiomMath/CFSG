module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec4_relIndex_centralizer_eq_card [Finite G] (H : Subgroup G) (x : G) :
    (H ⊓ centralizer ({x} : Set G)).relIndex H = Nat.card (conjClassIn H x) := by
  let ρ : ↥H →* ConjAct G := H.subtype.comp ConjAct.toConjAct.toMonoidHom
  letI : MulAction ↥H G := MulAction.compHom G ρ
  have hstab : MulAction.stabilizer ↥H x = (H ⊓ centralizer ({x} : Set G)).subgroupOf H := by
    ext h
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hh
      refine ⟨h.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have hh' : (h : G) * x * (h : G)⁻¹ = x := by
        have := hh
        change ConjAct.toConjAct (h : G) • x = x at this
        rwa [ConjAct.toConjAct_smul] at this
      rw [mul_inv_eq_iff_eq_mul] at hh'
      exact hh'.symm
    · intro hh
      obtain ⟨-, hcent⟩ := hh
      rw [Subgroup.mem_centralizer_iff] at hcent
      change ConjAct.toConjAct (h : G) • x = x
      rw [ConjAct.toConjAct_smul, ← hcent x (Set.mem_singleton x), mul_inv_cancel_right]
  have horbit : MulAction.orbit ↥H x = conjClassIn H x := by
    ext y
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨h, rfl⟩
      refine ⟨(h : G), h.2, ?_⟩
      change ConjAct.toConjAct (h : G) • x = (h : G) * x * (h : G)⁻¹
      rw [ConjAct.toConjAct_smul]
    · rintro ⟨g, hg, rfl⟩
      refine ⟨⟨g, hg⟩, ?_⟩
      change ConjAct.toConjAct g • x = g * x * g⁻¹
      rw [ConjAct.toConjAct_smul]
  rw [Subgroup.relIndex, ← hstab, MulAction.index_stabilizer, horbit, Nat.card_coe_set_eq]

private lemma conjNormal_congr_apply_coe {G : Type*} [Group G] {M A : Subgroup G}
    [(A.subgroupOf M).Normal] (hAM : A ≤ M) (m : ↥M) (a : ↥A) :
    (((MulAut.congr (Subgroup.subgroupOfEquivOfLe hAM))
        (MulAut.conjNormal (H := A.subgroupOf M) m)) a : G) =
      (m : G) * (a : G) * (m : G)⁻¹ := by
  rw [MulAut.congr_apply]
  change ((Subgroup.subgroupOfEquivOfLe hAM)
    (MulAut.conjNormal (H := A.subgroupOf M) m
      ((Subgroup.subgroupOfEquivOfLe hAM).symm a)) : G) = _
  have hcoe : ∀ x : A.subgroupOf M,
      ((Subgroup.subgroupOfEquivOfLe hAM x : ↥A) : G) = ((x : ↥M) : G) := fun x => rfl
  rw [hcoe]
  rw [MulAut.conjNormal_apply]
  rfl

theorem sec4_relIndex_centralizer_dvd_gl7 [Finite G] {A : Subgroup G}
    (hA : CFSG.Open.IsElemAbelian 2 A) (hcard : Nat.card A = 2 ^ 7) :
    (normalizer (A : Set G) ⊓ centralizer (A : Set G)).relIndex (normalizer (A : Set G)) ∣
      Nat.card (Matrix.GeneralLinearGroup (Fin 7) (ZMod 2)) := by
  classical
  let M : Subgroup G := normalizer (A : Set G)
  change (M ⊓ centralizer (A : Set G)).relIndex M ∣
    Nat.card (Matrix.GeneralLinearGroup (Fin 7) (ZMod 2))
  haveI : Finite ↥A := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hcomm : ∀ a b : ↥A, a * b = b * a := fun a b => hA.1.is_comm.comm a b
  have hpow : ∀ a : ↥A, a ^ 2 = 1 := fun a => Subtype.ext (hA.2 (a : G) a.2)
  obtain ⟨eA⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (W := ↥A) (p := 2)
    hcomm hpow hcard
  have hGL : Nat.card (MulAut ↥A) = Nat.card (Matrix.GeneralLinearGroup (Fin 7) (ZMod 2)) :=
    CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL eA
  haveI hN : (A.subgroupOf M).Normal := Subgroup.normal_in_normalizer
  let φ : ↥M →* MulAut ↥A :=
    (MulAut.congr (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := A)))).toMonoidHom.comp
      MulAut.conjNormal
  have hφapply : ∀ (m : ↥M) (a : ↥A),
      ((φ m a : ↥A) : G) = (m : G) * (a : G) * (m : G)⁻¹ := by
    intro m a
    change (((MulAut.congr (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := A))))
      (MulAut.conjNormal m)) a : G) = _
    exact conjNormal_congr_apply_coe (Subgroup.le_normalizer (H := A)) m a
  have hker : φ.ker = (M ⊓ centralizer (A : Set G)).subgroupOf M := by
    ext m
    rw [MonoidHom.mem_ker]
    constructor
    · intro hm
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      refine ⟨m.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have h1 : φ m ⟨a, ha⟩ = ⟨a, ha⟩ := by rw [hm]; rfl
      have h2 : (m : G) * (a : G) * (m : G)⁻¹ = (a : G) := by
        rw [← hφapply m ⟨a, ha⟩]
        exact congrArg (fun x : ↥A => (x : G)) h1
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
    · intro hm
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hm
      obtain ⟨-, hcent⟩ := hm
      rw [Subgroup.mem_centralizer_iff] at hcent
      apply MulEquiv.ext
      intro a
      apply Subtype.ext
      rw [hφapply m a]
      rw [← hcent (a : G) a.2, mul_inv_cancel_right]
      rfl
  have hrel : (M ⊓ centralizer (A : Set G)).relIndex M = (φ.ker).index := by
    rw [Subgroup.relIndex, hker]
  rw [hrel, Subgroup.index_ker]
  have hdvd : Nat.card φ.range ∣ Nat.card (MulAut ↥A) := Subgroup.card_subgroup_dvd_card φ.range
  rwa [hGL] at hdvd

theorem sec4_orbit_card_dvd_gl7 [Finite G] {A : Subgroup G} (hA : CFSG.Open.IsElemAbelian 2 A)
    (hcard : Nat.card A = 2 ^ 7) {x : G} (hx : x ∈ A) :
    Nat.card (conjClassIn (normalizer (A : Set G)) x) ∣
      Nat.card (Matrix.GeneralLinearGroup (Fin 7) (ZMod 2)) := by
  have hsub : ({x} : Set G) ⊆ (A : Set G) := by
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hx
  have hle : normalizer (A : Set G) ⊓ centralizer (A : Set G) ≤
      normalizer (A : Set G) ⊓ centralizer ({x} : Set G) :=
    inf_le_inf le_rfl (Subgroup.centralizer_le hsub)
  have hdvd : (normalizer (A : Set G) ⊓ centralizer ({x} : Set G)).relIndex
        (normalizer (A : Set G)) ∣
      (normalizer (A : Set G) ⊓ centralizer (A : Set G)).relIndex
        (normalizer (A : Set G)) :=
    Subgroup.relIndex_dvd_of_le_left (L := normalizer (A : Set G)) hle
  rw [← sec4_relIndex_centralizer_eq_card (normalizer (A : Set G)) x]
  exact hdvd.trans (sec4_relIndex_centralizer_dvd_gl7 hA hcard)

theorem sec4_not_dvd_gl7 :
    ¬ 43 ∣ Nat.card (Matrix.GeneralLinearGroup (Fin 7) (ZMod 2)) ∧
      ¬ 57 ∣ Nat.card (Matrix.GeneralLinearGroup (Fin 7) (ZMod 2)) := by
  have hGL : Nat.card (Matrix.GeneralLinearGroup (Fin 7) (ZMod 2)) =
      2 ^ 21 * 3 ^ 4 * 5 * 7 ^ 2 * 31 * 127 := by
    rw [Matrix.card_GL_field, ZMod.card]
    norm_num [Fin.prod_univ_succ]
  rw [hGL]
  constructor <;> norm_num

end CFSG.OddStandard.SmallF3.Omega
