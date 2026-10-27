module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26
public import CFSG.LocalAnalysis.GLTheoremA.Basic
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.Tables112T1Defs
public import CFSG.LocalAnalysis.SignalizerFunctor.ElementaryComplements
public import CFSG.RankThree.PartOne.KA.AlternatingPlaneInner
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

section Complement

variable {G : Type} [Group G]

theorem exists_complement_of_elemAbelian {p : ℕ} (hp : p.Prime) {A F : Subgroup G}
    (hA : IsElemAbelian p A) (hFA : F ≤ A) :
    ∃ C : Subgroup G, C ≤ A ∧ F ⊓ C = ⊥ ∧ F ⊔ C = A := by
  have : IsMulCommutative A := hA.1
  let _ : CommGroup A := { (inferInstance : Group A) with mul_comm := mul_comm' }
  obtain ⟨C', hC'⟩ := CFSG.SignalizerFunctor.Helpers.elementary_abelian_isCompl_exists p hp A
    (fun x => Subtype.ext (by simpa using hA.2 x x.2)) (F.subgroupOf A)
  refine ⟨C'.map A.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxF, c, hc, rfl⟩ := Subgroup.mem_inf.mp hx
    have hcF : c ∈ F.subgroupOf A := hxF
    have : c ∈ F.subgroupOf A ⊓ C' := Subgroup.mem_inf.mpr ⟨hcF, hc⟩
    rw [hC'.disjoint.eq_bot, Subgroup.mem_bot] at this
    simp [this]
  · refine le_antisymm (sup_le hFA (Subgroup.map_subtype_le _)) fun a ha => ?_
    have h1 : (⟨a, ha⟩ : A) ∈ F.subgroupOf A ⊔ C' := by
      rw [hC'.sup_eq_top]
      trivial
    obtain ⟨x, hx, y, hy, hxy⟩ := Subgroup.mem_sup.mp h1
    have : a = (x : G) * (y : G) := by
      have := congrArg Subtype.val hxy
      exact this.symm
    rw [this]
    exact Subgroup.mul_mem_sup hx ⟨y, hy, rfl⟩

end Complement

section Counting

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_commute' {S T : Subgroup G} (hc : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) :
    S ≤ Subgroup.normalizer (T : Set G) := fun s hs => by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have : s * h * s⁻¹ = h := by rw [mul_inv_eq_iff_eq_mul]; exact hc s hs h hh
    rw [this]
    exact hh
  · intro hh
    have h1 : s * (s * h * s⁻¹) * s⁻¹ = s * h * s⁻¹ := by
      rw [mul_inv_eq_iff_eq_mul]; exact hc s hs _ hh
    have h2 : s * h * s⁻¹ = h := by
      have h3 : s * (s * h * s⁻¹ * s⁻¹) = s * (h * s⁻¹) := by
        calc s * (s * h * s⁻¹ * s⁻¹) = s * (s * h * s⁻¹) * s⁻¹ := by group
          _ = s * h * s⁻¹ := h1
          _ = s * (h * s⁻¹) := by group
      exact mul_right_cancel (mul_left_cancel h3)
    rw [← h2]
    exact hh

theorem card_le_of_meets {p : ℕ} (hp : p.Prime) {D N : Subgroup G} (hD : IsElemAbelian p D)
    (h : ∀ E ≤ D, IsElemAbelian p E → Nat.card E = p ^ 3 → ∃ x ∈ E ⊓ N, x ≠ 1) :
    Nat.card D ≤ p ^ 2 * Nat.card ↥(D ⊓ N) := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨C, hCD, hdisj, hsup⟩ := exists_complement_of_elemAbelian hp hD (inf_le_left : D ⊓ N ≤ D)
  have hCel : IsElemAbelian p C := isElemAbelian_mono hD hCD
  have hnorm : C ≤ Subgroup.normalizer ((D ⊓ N : Subgroup G) : Set G) :=
    le_normalizer_of_commute' fun c hc x hx => isElemAbelian_commute hD (hCD hc) hx.1
  have hcard := card_sup_mul_card_inf_of_le_normalizer hnorm
  rw [hsup, hdisj, Subgroup.card_bot, mul_one] at hcard
  have hIpos : 0 < Nat.card ↥(D ⊓ N) := Nat.card_pos
  have hC2 : p ^ 2 < Nat.card C := by
    have h1 : Nat.card ↥(D ⊓ N) * p ^ 2 < Nat.card ↥(D ⊓ N) * Nat.card C := by
      rw [← hcard, mul_comm]
      exact hlt
    exact Nat.lt_of_mul_lt_mul_left h1
  obtain ⟨c, hc⟩ := exists_card_eq_pow_of_isElemAbelian hp hCel
  have hc3 : 3 ≤ c := by
    by_contra hc3
    have : p ^ c ≤ p ^ 2 := Nat.pow_le_pow_right hp.pos (by omega)
    omega
  have hCp : IsPGroup p C := isPGroup_of_isElemAbelian hCel
  obtain ⟨H', -, hH'⟩ := Sylow.exists_subgroup_le_card_pow_prime_of_le_card hp hCp (n := 3)
    (H := (⊤ : Subgroup ↥C)) (by rw [Subgroup.card_top, hc]; exact Nat.pow_le_pow_right hp.pos hc3)
  set E : Subgroup G := H'.map C.subtype with hE
  have hEC : E ≤ C := Subgroup.map_subtype_le H'
  obtain ⟨x, hx, hx1⟩ := h E (hEC.trans hCD) (isElemAbelian_mono hCel hEC)
    (by rw [hE, Subgroup.card_map_of_injective C.subtype_injective, hH'])
  have hxx : x ∈ (D ⊓ N) ⊓ C := ⟨⟨hCD (hEC hx.1), hx.2⟩, hEC hx.1⟩
  rw [hdisj, Subgroup.mem_bot] at hxx
  exact hx1 hxx

end Counting

section Tables

open CFSG.HardMathSupport.Timmesfeld.Coordinator (LieOuterRank)

private theorem card_eq_card_inf_ker_mul_card_map' {A Q : Type*} [Group A] [Group Q] (ψ : A →* Q)
    (S : Subgroup A) : Nat.card S = Nat.card ↥(S ⊓ ψ.ker) * Nat.card ↥(S.map ψ) := by
  have h := Subgroup.card_ker_mul_card_range (ψ.comp S.subtype)
  have hr : (ψ.comp S.subtype).range = S.map ψ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let e : ↥(ψ.comp S.subtype).ker ≃ ↥(S ⊓ ψ.ker) :=
    { toFun := fun x => ⟨(x.1 : A), x.1.2, x.2⟩
      invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  rw [hr] at h
  rw [← h, Nat.card_congr e]

theorem card_le_of_card_outer_le {S : Type} [Group S] [Finite S] {p : ℕ} (hp : 3 ≤ p)
    (hOut : Nat.card (Outer S) ≤ 4) (D : Subgroup (MulAut S)) :
    Nat.card D ≤ p ^ 2 * Nat.card ↥(D ⊓ inner S) := by
  haveI : Finite (MulAut S) := MulEquiv.finite_left
  set q : MulAut S →* Outer S := QuotientGroup.mk' (inner S) with hq
  have hker : q.ker = inner S := QuotientGroup.ker_mk' (inner S)
  have h1 := card_eq_card_inf_ker_mul_card_map' q D
  rw [hker] at h1
  have h2 : Nat.card ↥(D.map q) ≤ 4 := (Subgroup.card_le_card_group _).trans hOut
  calc Nat.card D = Nat.card ↥(D ⊓ inner S) * Nat.card ↥(D.map q) := h1
    _ ≤ Nat.card ↥(D ⊓ inner S) * 4 := Nat.mul_le_mul_left _ h2
    _ ≤ Nat.card ↥(D ⊓ inner S) * p ^ 2 := Nat.mul_le_mul_left _ (by nlinarith)
    _ = p ^ 2 * Nat.card ↥(D ⊓ inner S) := mul_comm _ _

theorem card_le_of_not_dvd_outer {S : Type} [Group S] [Finite S] {p : ℕ} (hp : p.Prime)
    (hOut : ¬ p ∣ Nat.card (Outer S)) {D : Subgroup (MulAut S)} (hD : IsElemAbelian p D) :
    Nat.card D ≤ p ^ 2 * Nat.card ↥(D ⊓ inner S) := by
  haveI : Finite (MulAut S) := MulEquiv.finite_left
  set q : MulAut S →* Outer S := QuotientGroup.mk' (inner S) with hq
  have hker : q.ker = inner S := QuotientGroup.ker_mk' (inner S)
  have h1 := card_eq_card_inf_ker_mul_card_map' q D
  rw [hker] at h1
  obtain ⟨c, hc⟩ := exists_card_eq_pow_of_isElemAbelian hp hD
  have hdvd : Nat.card ↥(D.map q) ∣ p ^ c :=
    hc ▸ ⟨Nat.card ↥(D ⊓ inner S), by rw [h1, mul_comm]⟩
  obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hj0 : j = 0 := by
    by_contra hne
    apply hOut
    have h2 : Nat.card ↥(D.map q) ∣ Nat.card (Outer S) := Subgroup.card_subgroup_dvd_card _
    rw [hjeq] at h2
    exact (dvd_pow_self p hne).trans h2
  rw [hj0, pow_zero] at hjeq
  rw [h1, hjeq, mul_one]
  exact Nat.le_mul_of_pos_left _ (pow_pos hp.pos 2)

theorem kd26a_lie (hLie : LieOuterRank) {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnonab : ∃ a b : S, a * b ≠ b * a) (idx : TauCeti.ValidLieTypeIndex)
    (e : Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (D : Subgroup (MulAut S)) (hD : IsElemAbelian p D) :
    Nat.card D ≤ p ^ 2 * Nat.card ↥(D ⊓ inner S) := by
  refine card_le_of_meets hp hD fun E hED hEel hEcard => ?_
  obtain ⟨x, hx, hx1⟩ := hLie S hS hnonab idx e p hp hp2 E hEel hEcard
  exact ⟨x, ⟨hx.1, hx.2⟩, hx1⟩

@[expose] def isSporadicIndex : TauCeti.CFSGIndex → Prop
  | .sporadic _ => True
  | _ => False

@[expose] def SporadicOutOdd : Prop :=
  ∀ (S : Type) [Group S] [Finite S], catalogIs S isSporadicIndex →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ Nat.card (Outer S)

theorem kd26a_of_tables (hLie : LieOuterRank) (hSp : SporadicOutOdd) : KD26a := by
  intro K _ _ hK p hp hp2 D hD
  haveI : Group.IsPerfect K := ⟨hK.1.1⟩
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  set φ := CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom K with hφ
  have hinj : Function.Injective φ :=
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective K
  have hSsimple : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.1.2
  have hnonab : ∃ a b : K ⧸ Subgroup.center K, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK.1
  have hD'el : IsElemAbelian p (D.map φ) := CFSG.SectionRank.isElemAbelian_map hD φ
  have key : Nat.card ↥(D.map φ) ≤ p ^ 2 * Nat.card ↥(D.map φ ⊓ inner (K ⧸ Subgroup.center K)) := by
    obtain ⟨i, ⟨e⟩⟩ := hK.2
    cases i with
    | cyclic p' hp' =>
      exfalso
      obtain ⟨a, b, hab⟩ := hnonab
      apply hab
      apply e.injective
      rw [map_mul, map_mul]
      exact mul_comm _ _
    | alternating n hn =>
      refine card_le_of_card_outer_le hp3 ?_ _
      have h1 : Nat.card (Outer (K ⧸ Subgroup.center K)) =
          Nat.card (Outer (alternatingGroup (Fin n))) :=
        Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv
      rw [h1]
      exact CFSG.RankThree.PartOne.card_outer_alternating_le_four hn
    | lie idx => exact kd26a_lie hLie hSsimple hnonab idx ⟨e⟩ hp hp2 _ hD'el
    | sporadic s => exact card_le_of_not_dvd_outer hp (hSp _ ⟨.sporadic s, trivial, ⟨e⟩⟩ p hp hp2) hD'el
  have h1 : Nat.card ↥(D.map φ) = Nat.card D := Subgroup.card_map_of_injective hinj
  have h2 : (D ⊓ inner K).map φ = D.map φ ⊓ inner (K ⧸ Subgroup.center K) := by
    apply le_antisymm
    · rintro _ ⟨α, hα, rfl⟩
      exact ⟨⟨α, hα.1, rfl⟩, CFSG.ComponentClassification.OuterAutomorphisms.centerQuotient_inner_le hα.2⟩
    · rintro _ ⟨⟨α, hα, rfl⟩, hα'⟩
      exact ⟨α, ⟨hα, mem_inner_of_centerQuotientHom_mem hα'⟩, rfl⟩
  have h3 : Nat.card ↥(D.map φ ⊓ inner (K ⧸ Subgroup.center K)) = Nat.card ↥(D ⊓ inner K) := by
    rw [← h2]
    exact Subgroup.card_map_of_injective hinj
  rw [h1, h3] at key
  exact key

end Tables

end CFSG.LocalAnalysis.GLTheoremA
