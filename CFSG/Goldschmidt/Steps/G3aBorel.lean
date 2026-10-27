module

public import CFSG.Goldschmidt.StatementsG
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutOmega
public import CFSG.GroupTheory.SuzukiTwoGroups
import CFSG.Goldschmidt.Steps.GoldTypeBender
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.Walter.J1.BenderLemma
import CFSG.Walter.ReeOrder.WardLocal.Group

public section

namespace CFSG.Goldschmidt

open CFSG.Open
open scoped MatrixGroups Pointwise commutatorElement

namespace G3a

open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter
  sylowCenter_le)

section Borel

variable {X : Type} [Group X]

theorem exists_mul_of_mem_sup {T D : Subgroup X} (hD : D ≤ Subgroup.normalizer (T : Set X))
    {g : X} (hg : g ∈ T ⊔ D) : ∃ t ∈ T, ∃ d ∈ D, g = t * d := by
  have hg' : g ∈ (T : Set X) * (D : Set X) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hD]
    exact hg
  obtain ⟨t, ht, d, hd, rfl⟩ := Set.mem_mul.mp hg'
  exact ⟨t, ht, d, hd, rfl⟩

structure BorelSetup (T : Sylow 2 X) (D : Subgroup X) : Prop where
  se : fusionStronglyEmbedded (Subgroup.normalizer ((T : Subgroup X) : Set X))
  card : Nat.card (Sylow 2 X) = Nat.card (T : Subgroup X) + 1
  le : D ≤ Subgroup.normalizer ((T : Subgroup X) : Set X)
  cyc : IsCyclic D
  odd : Odd (Nat.card D)
  inf : (T : Subgroup X) ⊓ D = ⊥
  sup : (T : Subgroup X) ⊔ D = Subgroup.normalizer ((T : Subgroup X) : Set X)
  sq : ∀ z ∈ sylowCenter (T : Subgroup X), z ^ 2 = 1
  inv : ∀ t ∈ (T : Subgroup X), t ^ 2 = 1 → t ∈ sylowCenter (T : Subgroup X)
  four : 4 ≤ Nat.card (sylowCenter (T : Subgroup X))
  cent : Subgroup.centralizer ((T : Subgroup X) : Set X) ≤ T

namespace BorelSetup

variable {T : Sylow 2 X} {D : Subgroup X} (h : BorelSetup T D)
include h

theorem exists_mul {g : X} (hg : g ∈ Subgroup.normalizer ((T : Subgroup X) : Set X)) :
    ∃ t ∈ (T : Subgroup X), ∃ d ∈ D, g = t * d := by
  rw [← h.sup] at hg
  exact exists_mul_of_mem_sup h.le hg

theorem trans [Finite X] {x y : X} (hx : x ∈ sylowCenter (T : Subgroup X))
    (hy : y ∈ sylowCenter (T : Subgroup X)) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    ∃ d ∈ D, d⁻¹ * x * d = y := by
  obtain ⟨n, hn, hxy⟩ :=
    CFSG.ComponentClassification.AschbacherToolkit.Bender.normalizer_transitive_center h.se
      h.sq hx hy hx1 hy1
  obtain ⟨t, ht, d, hd, rfl⟩ := h.exists_mul hn
  refine ⟨d, hd, ?_⟩
  have htx : t * x = x * t := (mem_sylowCenter.mp hx).2 t ht
  rw [← hxy]
  calc d⁻¹ * x * d = d⁻¹ * (t⁻¹ * (t * x)) * d := by group
    _ = d⁻¹ * (t⁻¹ * (x * t)) * d := by rw [htx]
    _ = (t * d)⁻¹ * x * (t * d) := by group

theorem exists_ne [Finite X] (z : X) :
    ∃ w ∈ sylowCenter (T : Subgroup X), w ≠ 1 ∧ w ≠ z := by
  obtain ⟨a, ha, b, hb, ha1, hb1, hab⟩ :=
    GoldType.exists_ne_one_of_two_lt (S := sylowCenter (T : Subgroup X)) (by
      have := h.four
      omega)
  by_cases haz : a = z
  · exact ⟨b, hb, hb1, fun hbz => hab (haz.trans hbz.symm)⟩
  · exact ⟨a, ha, ha1, haz⟩

omit h in
theorem exists_involution_pow [Finite X] {c : X} (hc : c ∈ (T : Subgroup X)) (hc1 : c ≠ 1) :
    ∃ k : ℕ, (c ^ k) ^ 2 = 1 ∧ c ^ k ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp T.isPGroup') ⟨c, hc⟩
  have hn' : orderOf c = 2 ^ n := by
    rw [← hn, Subgroup.orderOf_mk]
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hn'
    exact hc1 hn'
  refine ⟨2 ^ (n - 1), ?_, ?_⟩
  · rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0), ← hn',
      pow_orderOf_eq_one]
  · intro h1
    have hdvd := orderOf_dvd_of_pow_eq_one h1
    rw [hn'] at hdvd
    have := Nat.le_of_dvd (by positivity) hdvd
    have := Nat.pow_lt_pow_right (a := 2) (by norm_num) (Nat.sub_lt
      (Nat.pos_of_ne_zero hn0) Nat.one_pos)
    omega

theorem eq_one_of_commute [Finite X] {c : X} (hc : c ∈ (T : Subgroup X))
    (hcD : ∀ d ∈ D, d * c = c * d) : c = 1 := by
  by_contra hc1
  obtain ⟨k, hk2, hk1⟩ := exists_involution_pow hc hc1
  have hzT : c ^ k ∈ (T : Subgroup X) := (T : Subgroup X).pow_mem hc k
  have hzZ := h.inv _ hzT hk2
  obtain ⟨w, hw, hw1, hwz⟩ := h.exists_ne (c ^ k)
  obtain ⟨d, hd, hdz⟩ := h.trans hzZ hw hk1 hw1
  apply hwz
  rw [← hdz]
  have hcomm : d * c ^ k = c ^ k * d := ((Commute.pow_right (hcD d hd) k)).eq
  calc d⁻¹ * c ^ k * d = d⁻¹ * (d * c ^ k) := by rw [hcomm]; group
    _ = c ^ k := by group

omit h in
theorem exists_eq_commutator [Finite X] {d : X}
    (hd : d ∈ Subgroup.normalizer ((T : Subgroup X) : Set X))
    (hC : ∀ c ∈ (T : Subgroup X), d * c = c * d → c = 1) {t : X} (ht : t ∈ (T : Subgroup X)) :
    ∃ s ∈ (T : Subgroup X), s⁻¹ * d * s * d⁻¹ = t := by
  let S := (T : Subgroup X)
  have hconj : ∀ s ∈ S, d * s * d⁻¹ ∈ S := fun s hs => (Subgroup.mem_normalizer_iff.mp hd s).mp hs
  let f : S → S := fun s => ⟨(s : X)⁻¹ * (d * s * d⁻¹), S.mul_mem (S.inv_mem s.2) (hconj _ s.2)⟩
  have hinj : Function.Injective f := by
    intro s s' hss
    have h' : (s : X)⁻¹ * (d * s * d⁻¹) = (s' : X)⁻¹ * (d * s' * d⁻¹) := congrArg Subtype.val hss
    have hc : d * ((s' : X) * (s : X)⁻¹) = ((s' : X) * (s : X)⁻¹) * d := by
      calc d * ((s' : X) * (s : X)⁻¹)
          = s' * ((s' : X)⁻¹ * (d * s' * d⁻¹)) * d * (s : X)⁻¹ := by group
        _ = s' * ((s : X)⁻¹ * (d * s * d⁻¹)) * d * (s : X)⁻¹ := by rw [h']
        _ = ((s' : X) * (s : X)⁻¹) * d := by group
    have h1 := hC _ (S.mul_mem s'.2 (S.inv_mem s.2)) hc
    rw [mul_inv_eq_one] at h1
    exact Subtype.ext h1.symm
  obtain ⟨s, hs⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨t, ht⟩
  refine ⟨s, s.2, ?_⟩
  have := congrArg Subtype.val hs
  simp only [f] at this
  rw [← this]
  group

theorem eq_one_of_commute_gen [Finite X] {d : X} (hgen : ∀ x ∈ D, x ∈ Subgroup.zpowers d)
    {c : X} (hc : c ∈ (T : Subgroup X)) (hdc : d * c = c * d) : c = 1 := by
  refine h.eq_one_of_commute hc fun x hx => ?_
  obtain ⟨k, rfl⟩ := hgen x hx
  exact (Commute.zpow_left hdc k).eq

theorem exists_gen : ∃ d ∈ D, ∀ x ∈ D, x ∈ Subgroup.zpowers d := by
  obtain ⟨⟨d, hd⟩, hgen⟩ := h.cyc.exists_generator
  refine ⟨d, hd, fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := hgen ⟨x, hx⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem comm {d e : X} (hd : d ∈ D) (he : e ∈ D) : d * e = e * d := by
  obtain ⟨g, -, hgen⟩ := h.exists_gen
  obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hgen d hd)
  obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hgen e he)
  exact (Commute.zpow_zpow_self g a b).eq

theorem commutator_eq [Finite X] : ⁅(T : Subgroup X), D⁆ = T := by
  obtain ⟨d, hd, hgen'⟩ := h.exists_gen
  refine le_antisymm ?_ fun t ht => ?_
  · rw [Subgroup.commutator_le]
    intro t ht e he
    have hconj := (Subgroup.mem_normalizer_iff.mp (h.le he) t⁻¹).mp ((T : Subgroup X).inv_mem ht)
    have he' : ⁅t, e⁆ = t * (e * t⁻¹ * e⁻¹) := by rw [commutatorElement_def]; group
    rw [he']
    exact (T : Subgroup X).mul_mem ht hconj
  · obtain ⟨s, hs, rfl⟩ := exists_eq_commutator (h.le hd)
      (fun c hc hdc => h.eq_one_of_commute_gen hgen' hc hdc) ht
    have := Subgroup.commutator_mem_commutator ((T : Subgroup X).inv_mem hs) hd
    rwa [commutatorElement_def, inv_inv] at this

theorem inf_centralizer : D ⊓ Subgroup.centralizer ((T : Subgroup X) : Set X) = ⊥ := by
  rw [eq_bot_iff, ← h.inf]
  exact fun x hx => ⟨h.cent hx.2, hx.1⟩

theorem ti [Finite X] (g : X) (hne : (T : Subgroup X) ⊓ conjSub g T ≠ ⊥) : conjSub g T = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : ((g⁻¹ • T : Sylow 2 X) : Subgroup X) = conjSub g T := by
    ext x
    rw [CFSG.ComponentClassification.AschbacherToolkit.Bender.Omega.mem_conj_smul_iff,
      mem_conjSub, inv_inv]
  by_contra hgT
  apply hne
  have hne' : g⁻¹ • T ≠ T := fun h' => hgT (by rw [← hS, h'])
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  exact CFSG.ComponentClassification.AschbacherToolkit.Bender.Omega.eq_one_of_mem_of_mem h.se
    hne' hx.1 (by rw [hS]; exact hx.2)

theorem exists_smul [Finite X] {P Q : Sylow 2 X} (hP : P ≠ T) (hQ : Q ≠ T) :
    ∃ t ∈ (T : Subgroup X), t • P = Q :=
  CFSG.ComponentClassification.AschbacherToolkit.Bender.Omega.exists_smul_eq h.se h.card hP hQ

theorem exists_ne_sylow [Finite X] : ∃ S : Sylow 2 X, S ≠ T := by
  have hcard2 : 1 < Nat.card (Sylow 2 X) := by
    rw [h.card]
    have := Nat.card_pos (α := (T : Subgroup X))
    omega
  have : Nontrivial (Sylow 2 X) := Finite.one_lt_card_iff_nontrivial.mp hcard2
  exact _root_.exists_ne T

theorem exists_fixed [Finite X] :
    ∃ T' : Sylow 2 X, T' ≠ T ∧ D ≤ Subgroup.normalizer ((T' : Subgroup X) : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨d, hd, hgen⟩ := h.exists_gen
  have hC : ∀ c ∈ (T : Subgroup X), d * c = c * d → c = 1 := fun c hc hdc =>
    h.eq_one_of_commute_gen hgen hc hdc
  obtain ⟨S₀, h₀⟩ := h.exists_ne_sylow
  have hdT : d • T = T := Sylow.smul_eq_iff_mem_normalizer.mpr (h.le hd)
  have hdS₀ : d • S₀ ≠ T := by
    intro hS
    apply h₀
    calc S₀ = d⁻¹ • (d • S₀) := (inv_smul_smul d S₀).symm
      _ = d⁻¹ • (d • T) := by rw [hS, hdT]
      _ = T := inv_smul_smul d T
  obtain ⟨r, hr, hrS⟩ :=
    CFSG.ComponentClassification.AschbacherToolkit.Bender.Omega.exists_smul_eq h.se h.card h₀ hdS₀
  obtain ⟨s, hs, hsr⟩ := exists_eq_commutator (h.le hd) hC ((T : Subgroup X).inv_mem hr)
  refine ⟨s • S₀, ?_, ?_⟩
  · intro hsT
    apply h₀
    have hsT' : s • T = T := Sylow.smul_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hs)
    calc S₀ = s⁻¹ • (s • S₀) := (inv_smul_smul s S₀).symm
      _ = s⁻¹ • (s • T) := by rw [hsT, hsT']
      _ = T := inv_smul_smul s T
  · have e1 : d * s = s * r⁻¹ * d := by
      rw [← hsr]
      group
    have hfix : d • (s • S₀) = s • S₀ := by
      rw [← mul_smul, e1, mul_smul, ← hrS, ← mul_smul, inv_mul_cancel_right]
    have hdN := Sylow.smul_eq_iff_mem_normalizer.mp hfix
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hgen x hx)
    exact Subgroup.zpow_mem _ hdN k

open CFSG.ComponentClassification.AschbacherToolkit.Bender in
theorem normalizer_inf_eq [Finite X] {T' : Sylow 2 X} (hne : T' ≠ T)
    (hDT' : D ≤ Subgroup.normalizer ((T' : Subgroup X) : Set X)) :
    Subgroup.normalizer ((T : Subgroup X) : Set X) ⊓
      Subgroup.normalizer ((T' : Subgroup X) : Set X) = D :=
  le_antisymm (fun _ hg =>
    Omega.mem_of_mem_normalizer_of_mem_normalizer h.se hne (fun _ hg => h.exists_mul hg) hDT'
      hg.1 hg.2) (le_inf h.le hDT')

theorem eq_of_le_normalizer [Finite X] {T' : Sylow 2 X} (hne : T' ≠ T)
    (hDT' : D ≤ Subgroup.normalizer ((T' : Subgroup X) : Set X)) {P : Sylow 2 X}
    (hP : D ≤ Subgroup.normalizer ((P : Subgroup X) : Set X)) : P = T ∨ P = T' := by
  by_cases hPT : P = T
  · exact Or.inl hPT
  right
  obtain ⟨s, hs, rfl⟩ := h.exists_smul hne hPT
  obtain ⟨d, hd, hgen⟩ := h.exists_gen
  have h1 : s⁻¹ * d * s ∈ Subgroup.normalizer ((T' : Subgroup X) : Set X) :=
    CFSG.ComponentClassification.AschbacherToolkit.Bender.Omega.mem_normalizer_conj_smul_iff.mp
      (hP hd)
  have hsN := Subgroup.le_normalizer (H := (T : Subgroup X)) hs
  have h2 : s⁻¹ * d * s ∈ Subgroup.normalizer ((T : Subgroup X) : Set X) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hsN) (h.le hd)) hsN
  have h3 : s⁻¹ * d * s ∈ D := (h.normalizer_inf_eq hne hDT').le ⟨h2, h1⟩
  have h4 : d⁻¹ * (s⁻¹ * d * s) ∈ D := D.mul_mem (D.inv_mem hd) h3
  have h5 : d⁻¹ * (s⁻¹ * d * s) ∈ (T : Subgroup X) := by
    have e : d⁻¹ * (s⁻¹ * d * s) = (d⁻¹ * s⁻¹ * d⁻¹⁻¹) * s := by group
    rw [e]
    exact (T : Subgroup X).mul_mem ((Subgroup.mem_normalizer_iff.mp
      (Subgroup.inv_mem _ (h.le hd)) s⁻¹).mp ((T : Subgroup X).inv_mem hs)) hs
  have h6 : d⁻¹ * (s⁻¹ * d * s) = 1 := by
    have hmem : d⁻¹ * (s⁻¹ * d * s) ∈ (T : Subgroup X) ⊓ D := ⟨h5, h4⟩
    rw [h.inf] at hmem
    exact hmem
  have hsd : d * s = s * d := by
    calc d * s = s * d * (d⁻¹ * (s⁻¹ * d * s)) := by group
      _ = s * d := by rw [h6, mul_one]
  rw [h.eq_one_of_commute_gen hgen hs hsd, one_smul]

theorem ne_bot : (T : Subgroup X) ≠ ⊥ := by
  intro hT
  have hle : sylowCenter (T : Subgroup X) = ⊥ := by
    rw [eq_bot_iff, ← hT]
    exact sylowCenter_le _
  have := h.four
  rw [hle, Subgroup.card_bot] at this
  omega

theorem le_normalizer_of_le [Finite X] [IsSimpleGroup X] {M : Subgroup X}
    (hTM : (T : Subgroup X) ≤ M) (hM : M ≠ ⊤) :
    M ≤ Subgroup.normalizer ((T : Subgroup X) : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro g hgM
  by_contra hg
  apply hM
  have hgT : g • T ≠ T := fun h' => hg (Sylow.smul_eq_iff_mem_normalizer.mp h')
  have hall : ∀ S : Sylow 2 X, (S : Subgroup X) ≤ M := by
    intro S
    by_cases hST : S = T
    · rw [hST]
      exact hTM
    obtain ⟨t, ht, rfl⟩ := h.exists_smul hgT hST
    intro x hx
    rw [CFSG.ComponentClassification.AschbacherToolkit.Bender.Omega.mem_conj_smul_iff,
      CFSG.ComponentClassification.AschbacherToolkit.Bender.Omega.mem_conj_smul_iff] at hx
    have e : x = (t * g) * (g⁻¹ * (t⁻¹ * x * t) * g) * (t * g)⁻¹ := by group
    rw [e]
    exact M.mul_mem (M.mul_mem (M.mul_mem (hTM ht) hgM) (hTM hx))
      (M.inv_mem (M.mul_mem (hTM ht) hgM))
  have hN : Subgroup.normalClosure ((T : Subgroup X) : Set X) ≤ M := by
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    obtain ⟨t, ht, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨c, rfl⟩ := isConj_iff.mp hconj
    refine hall (c • T) ?_
    rw [CFSG.ComponentClassification.AschbacherToolkit.Bender.Omega.mem_conj_smul_iff]
    simpa [mul_assoc] using (show t ∈ (T : Subgroup X) from ht)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.normalClosure ((T : Subgroup X) : Set X)) with hb | ht
  · exfalso
    apply h.ne_bot
    rw [eq_bot_iff, ← hb]
    exact Subgroup.le_normalClosure
  · rw [eq_top_iff, ← ht]
    exact hN

theorem isCoatom [Finite X] [IsSimpleGroup X] :
    IsCoatom (Subgroup.normalizer ((T : Subgroup X) : Set X)) := by
  refine ⟨h.se.1, fun M hM => ?_⟩
  by_contra hMt
  exact (not_le_of_gt hM) (h.le_normalizer_of_le (Subgroup.le_normalizer.trans hM.le) hMt)

theorem isSuzukiTwoGroup [Finite X] (hab : ¬ IsMulCommutative (T : Subgroup X)) :
    CFSG.GroupTheory.IsSuzukiTwoGroup (T : Subgroup X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinv : ∀ x : (T : Subgroup X), orderOf x = 2 →
      (x : X) ∈ sylowCenter (T : Subgroup X) ∧ (x : X) ≠ 1 := by
    intro x hx
    have hx2 : x ^ 2 = 1 := by
      have h' := pow_orderOf_eq_one x
      rwa [hx] at h'
    refine ⟨h.inv _ x.2 (by simpa using congrArg Subtype.val hx2), fun h' => ?_⟩
    have h1 : x = 1 := Subtype.ext h'
    rw [h1, orderOf_one] at hx
    omega
  have hord : ∀ z (hz : z ∈ sylowCenter (T : Subgroup X)), z ≠ 1 →
      orderOf (⟨z, sylowCenter_le _ hz⟩ : (T : Subgroup X)) = 2 := by
    intro z hz hz1
    refine orderOf_eq_prime (Subtype.ext (by simpa using h.sq z hz)) fun h' => hz1 ?_
    exact congrArg Subtype.val h'
  refine ⟨inferInstance, T.isPGroup', hab, ?_,
    (CFSG.ComponentClassification.AschbacherToolkit.Goldschmidt.conjAct h.le).range, ?_, ?_⟩
  · obtain ⟨a, ha, b, hb, ha1, hb1, hab'⟩ :=
      GoldType.exists_ne_one_of_two_lt (S := sylowCenter (T : Subgroup X)) (by
        have := h.four
        omega)
    exact ⟨_, _, hord a ha ha1, hord b hb hb1, fun h' => hab' (congrArg Subtype.val h')⟩
  · have : IsCyclic D := h.cyc
    exact isCyclic_of_surjective _
      (CFSG.ComponentClassification.AschbacherToolkit.Goldschmidt.conjAct
        h.le).rangeRestrict_surjective
  · intro x y hx hy
    obtain ⟨hxZ, hx1⟩ := hinv x hx
    obtain ⟨hyZ, hy1⟩ := hinv y hy
    obtain ⟨d, hd, hdy⟩ := h.trans hxZ hyZ hx1 hy1
    refine ⟨CFSG.ComponentClassification.AschbacherToolkit.Goldschmidt.conjAct h.le
      ⟨d⁻¹, D.inv_mem hd⟩, ⟨_, rfl⟩, Subtype.ext ?_⟩
    rw [CFSG.ComponentClassification.AschbacherToolkit.Goldschmidt.conjAct_apply]
    change d⁻¹ * (x : X) * d⁻¹⁻¹ = y
    rw [inv_inv, hdy]

theorem commutator_eq_center [Finite X] (hab : ¬ IsMulCommutative (T : Subgroup X)) :
    ⁅(T : Subgroup X), (T : Subgroup X)⁆ = sylowCenter (T : Subgroup X) := by
  obtain ⟨-, hZΦ, hΦC, -⟩ := (h.isSuzukiTwoGroup hab).higman
  rw [← Subgroup.map_subtype_commutator, ← hΦC, ← hZΦ,
    CFSG.ComponentClassification.AschbacherToolkit.Bender.map_center_eq_sylowCenter]

theorem sq_mem_center [Finite X] (hab : ¬ IsMulCommutative (T : Subgroup X)) {x : X}
    (hx : x ∈ (T : Subgroup X)) : x ^ 2 ∈ sylowCenter (T : Subgroup X) := by
  obtain ⟨-, -, -, -, n, -, -, hexp, -⟩ := (h.isSuzukiTwoGroup hab).higman
  have h4 : (⟨x, hx⟩ : (T : Subgroup X)) ^ 4 = 1 := by
    rw [← hexp]
    exact Monoid.pow_exponent_eq_one _
  refine h.inv _ ((T : Subgroup X).pow_mem hx 2) ?_
  rw [← pow_mul]
  simpa using congrArg Subtype.val h4

theorem conj_mem_center {d z : X} (hd : d ∈ D) (hz : z ∈ sylowCenter (T : Subgroup X)) :
    d * z * d⁻¹ ∈ sylowCenter (T : Subgroup X) := by
  rw [mem_sylowCenter] at hz ⊢
  have hdN := h.le hd
  refine ⟨(Subgroup.mem_normalizer_iff.mp hdN z).mp hz.1, fun t ht => ?_⟩
  have ht' : d⁻¹ * t * d ∈ (T : Subgroup X) := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hdN) t).mp ht
    simpa using this
  have hc := hz.2 _ ht'
  calc t * (d * z * d⁻¹) = d * ((d⁻¹ * t * d) * z) * d⁻¹ := by group
    _ = d * (z * (d⁻¹ * t * d)) * d⁻¹ := by rw [hc]
    _ = d * z * d⁻¹ * t := by group

theorem mem_centralizer_center [Finite X] {d z₀ : X} (hd : d ∈ D)
    (hz₀ : z₀ ∈ sylowCenter (T : Subgroup X)) (hz₀1 : z₀ ≠ 1) (hfix : d * z₀ = z₀ * d) :
    d ∈ Subgroup.centralizer (sylowCenter (T : Subgroup X) : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  by_cases hz1 : z = 1
  · rw [hz1, one_mul, mul_one]
  obtain ⟨e, he, rfl⟩ := h.trans hz₀ hz hz₀1 hz1
  have hde : d * e = e * d := h.comm hd he
  have hed : e⁻¹ * d = d * e⁻¹ := by
    calc e⁻¹ * d = e⁻¹ * (d * e) * e⁻¹ := by group
      _ = e⁻¹ * (e * d) * e⁻¹ := by rw [hde]
      _ = d * e⁻¹ := by group
  calc e⁻¹ * z₀ * e * d = e⁻¹ * z₀ * (d * e) := by rw [hde]; group
    _ = e⁻¹ * (z₀ * d) * e := by group
    _ = e⁻¹ * (d * z₀) * e := by rw [hfix]
    _ = (e⁻¹ * d) * z₀ * e := by group
    _ = (d * e⁻¹) * z₀ * e := by rw [hed]
    _ = d * (e⁻¹ * z₀ * e) := by group

theorem card_eq_mul [Finite X] : Nat.card D = (Nat.card (sylowCenter (T : Subgroup X)) - 1) *
    Nat.card (D ⊓ Subgroup.centralizer (sylowCenter (T : Subgroup X) : Set X) : Subgroup X) := by
  classical
  have : Fintype X := Fintype.ofFinite X
  set Z := sylowCenter (T : Subgroup X) with hZ
  let F : Finset X := Finset.univ.filter (fun x => x ∈ Z ∧ x ≠ 1)
  have hmemF : ∀ x, x ∈ F ↔ x ∈ Z ∧ x ≠ 1 := fun x => by simp [F]
  obtain ⟨z₀, hz₀, hz₀1, -⟩ := h.exists_ne 1
  have hz₀F : z₀ ∈ F := (hmemF z₀).mpr ⟨hz₀, hz₀1⟩
  have hF : ∀ a ∈ D, ∀ x ∈ F, a * x * a⁻¹ ∈ F := by
    intro a ha x hx
    rw [hmemF] at hx ⊢
    refine ⟨h.conj_mem_center ha hx.1, fun h1 => hx.2 ?_⟩
    have : x = a⁻¹ * (a * x * a⁻¹) * a := by group
    rw [this, h1]
    group
  have htr : ∀ x ∈ F, ∀ y ∈ F, ∃ a ∈ D, a * x * a⁻¹ = y := by
    intro x hx y hy
    rw [hmemF] at hx hy
    obtain ⟨d, hd, hdy⟩ := h.trans hx.1 hy.1 hx.2 hy.2
    exact ⟨d⁻¹, D.inv_mem hd, by rw [inv_inv]; exact hdy⟩
  have hcard := CFSG.Walter.WardLocal.card_eq_card_mul_centralizer D F hF htr hz₀F
  have hFcard : F.card = Nat.card Z - 1 := by
    have hF' : F = (Finset.univ.filter (· ∈ Z)).erase 1 := by
      ext x
      simp [F, and_comm]
    rw [hF', Finset.card_erase_of_mem (by simp [Z.one_mem]), Nat.card_eq_fintype_card,
      Fintype.card_subtype]
  have hcent : D ⊓ Subgroup.centralizer ({z₀} : Set X) =
      D ⊓ Subgroup.centralizer (Z : Set X) := by
    refine le_antisymm (fun d hd => ⟨hd.1, ?_⟩) (inf_le_inf_left _
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hz₀)))
    have hc := Subgroup.mem_centralizer_singleton_iff.mp hd.2
    exact h.mem_centralizer_center hd.1 hz₀ hz₀1 hc
  rw [hcard, hFcard, hcent]

omit h in
theorem eq_one_of_pow_odd [Finite X] {w : X} (hw : w ∈ (T : Subgroup X)) {r : ℕ} (hr : Odd r)
    (hwr : w ^ r = 1) : w = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp T.isPGroup') ⟨w, hw⟩
  have hn' : orderOf w = 2 ^ n := by rw [← hn, Subgroup.orderOf_mk]
  have hdvd : 2 ^ n ∣ r := hn' ▸ orderOf_dvd_of_pow_eq_one hwr
  have hn0 : n = 0 := by
    by_contra hn0
    exact (Nat.not_even_iff_odd.mpr hr) (even_iff_two_dvd.mpr
      ((dvd_pow_self 2 hn0).trans hdvd))
  rw [hn0, pow_zero, orderOf_eq_one_iff] at hn'
  exact hn'

theorem commute_of_coset [Finite X] {W : Subgroup X} (hWT : W ≤ T) {d y : X} (hd : d ∈ D)
    (hdW : ∀ w ∈ W, d * w = w * d) (hdy : y⁻¹ * (d * y * d⁻¹) ∈ W) : d * y = y * d := by
  set w := y⁻¹ * (d * y * d⁻¹) with hw
  have hdyw : d * y * d⁻¹ = y * w := by rw [hw]; group
  have hpow : ∀ k : ℕ, d ^ k * y * (d ^ k)⁻¹ = y * w ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hdwk : d * w ^ k * d⁻¹ = w ^ k := by
        rw [(Commute.pow_right (hdW w hdy) k).eq]
        group
      calc d ^ (k + 1) * y * (d ^ (k + 1))⁻¹ = d * (d ^ k * y * (d ^ k)⁻¹) * d⁻¹ := by
            rw [pow_succ']; group
        _ = (d * y * d⁻¹) * (d * w ^ k * d⁻¹) := by rw [ih]; group
        _ = y * w ^ (k + 1) := by rw [hdyw, hdwk, pow_succ']; group
  have hodd : Odd (orderOf d) := h.odd.of_dvd_nat (Subgroup.orderOf_dvd_natCard D hd)
  have hwr : w ^ orderOf d = 1 := by
    have := hpow (orderOf d)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at this
    exact (mul_eq_left.mp this.symm)
  have hw1 := eq_one_of_pow_odd (hWT hdy) hodd hwr
  have : d * y * d⁻¹ = y := by rw [hdyw, hw1, mul_one]
  calc d * y = d * y * d⁻¹ * d := by group
    _ = y * d := by rw [this]

omit h in
theorem coset_pow {W : Subgroup X} {f y : X} (hf : f ∈ Subgroup.normalizer (W : Set X))
    (hfy : y⁻¹ * (f * y * f⁻¹) ∈ W) (k : ℕ) : y⁻¹ * (f ^ k * y * (f ^ k)⁻¹) ∈ W := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : y⁻¹ * (f ^ (k + 1) * y * (f ^ (k + 1))⁻¹) =
        (y⁻¹ * (f * y * f⁻¹)) * (f * (y⁻¹ * (f ^ k * y * (f ^ k)⁻¹)) * f⁻¹) := by
      rw [pow_succ']
      group
    rw [e]
    exact W.mul_mem hfy ((Subgroup.mem_normalizer_iff.mp hf _).mp ih)

abbrev kerD (D : Subgroup X) (T : Sylow 2 X) : Subgroup X :=
  D ⊓ Subgroup.centralizer (sylowCenter (T : Subgroup X) : Set X)

theorem exists_D₀ [Finite X]
    (hcop : Nat.Coprime (Nat.card (sylowCenter (T : Subgroup X)) - 1) (Nat.card (kerD D T))) :
    ∃ e₀ ∈ D, orderOf e₀ = Nat.card (sylowCenter (T : Subgroup X)) - 1 ∧
      ∀ e ∈ Subgroup.zpowers e₀,
        e ∈ Subgroup.centralizer (sylowCenter (T : Subgroup X) : Set X) → e = 1 := by
  obtain ⟨g, hg, hgen⟩ := h.exists_gen
  have hDg : Nat.card D = orderOf g := by
    have hDz : D = Subgroup.zpowers g :=
      le_antisymm (fun x hx => hgen x hx) ((Subgroup.zpowers_le).mpr hg)
    rw [hDz, Nat.card_zpowers]
  set m₁ := Nat.card (kerD D T) with hm₁def
  have hcard : Nat.card D = (Nat.card (sylowCenter (T : Subgroup X)) - 1) * m₁ := h.card_eq_mul
  have hm₁ : m₁ ≠ 0 := Nat.card_pos.ne'
  have hord : orderOf (g ^ m₁) = Nat.card (sylowCenter (T : Subgroup X)) - 1 := by
    rw [orderOf_pow_of_dvd hm₁ (by rw [← hDg, hcard]; exact dvd_mul_left _ _), ← hDg, hcard,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm₁)]
  refine ⟨g ^ m₁, D.pow_mem hg _, hord, fun e he heC => ?_⟩
  have heD : e ∈ kerD D T := ⟨(Subgroup.zpowers_le.mpr (D.pow_mem hg _)) he, heC⟩
  have h1 : e ^ m₁ = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard (kerD D T) heD)
  have h2 : e ^ (Nat.card (sylowCenter (T : Subgroup X)) - 1) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (hord ▸ orderOf_dvd_of_mem_zpowers he)
  have := pow_gcd_eq_one.mpr ⟨h2, h1⟩
  rwa [hcop.gcd_eq_one, pow_one] at this

theorem eq_one_of_commute_D₀ [Finite X] {e₀ : X} (he₀ : e₀ ∈ D)
    (hfree : ∀ e ∈ Subgroup.zpowers e₀,
      e ∈ Subgroup.centralizer (sylowCenter (T : Subgroup X) : Set X) → e = 1)
    {e : X} (he : e ∈ Subgroup.zpowers e₀) (he1 : e ≠ 1) {c : X} (hc : c ∈ (T : Subgroup X))
    (hec : e * c = c * e) : c = 1 := by
  by_contra hc1
  obtain ⟨k, hk2, hk1⟩ := exists_involution_pow hc hc1
  have hzZ := h.inv _ ((T : Subgroup X).pow_mem hc k) hk2
  have heD : e ∈ D := Subgroup.zpowers_le.mpr he₀ he
  have hcomm : e * c ^ k = c ^ k * e := (Commute.pow_right hec k).eq
  exact he1 (hfree e he (h.mem_centralizer_center heD hzZ hk1 hcomm))

theorem dvd_card_sub [Finite X] {e₀ : X} (he₀ : e₀ ∈ D)
    (hfree : ∀ e ∈ Subgroup.zpowers e₀,
      e ∈ Subgroup.centralizer (sylowCenter (T : Subgroup X) : Set X) → e = 1)
    {Y : Subgroup X} (hZY : sylowCenter (T : Subgroup X) ≤ Y) (hYT : Y ≤ T)
    (hDY : D ≤ Subgroup.normalizer (Y : Set X)) :
    orderOf e₀ ∣ Nat.card Y - Nat.card (sylowCenter (T : Subgroup X)) := by
  have hE := CFSG.Walter.J1.card_dvd_ncard_of_free (H := Subgroup.zpowers e₀)
    (X := (Y : Set X) \ (sylowCenter (T : Subgroup X) : Set X)) ?_ ?_
  · rw [Nat.card_zpowers, Set.ncard_sdiff (by exact_mod_cast hZY), ← Nat.card_coe_set_eq,
      ← Nat.card_coe_set_eq] at hE
    exact hE
  · rintro u ⟨huY, huZ⟩ k hk
    have hkD : k ∈ D := Subgroup.zpowers_le.mpr he₀ hk
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hDY hkD) u).mp huY, fun hZ => huZ ?_⟩
    have e : u = k⁻¹ * (k * u * k⁻¹) * k⁻¹⁻¹ := by group
    rw [SetLike.mem_coe, e]
    exact h.conj_mem_center (D.inv_mem hkD) hZ
  · rintro u ⟨huY, huZ⟩ k hk hku
    by_contra hk1
    have hu1 := h.eq_one_of_commute_D₀ he₀ hfree hk hk1 (hYT huY) hku
    exact huZ (by rw [hu1]; exact (sylowCenter _).one_mem)

theorem eq_one_of_fix_coset [Finite X] {e₀ : X} (he₀ : e₀ ∈ D)
    (hfree : ∀ e ∈ Subgroup.zpowers e₀,
      e ∈ Subgroup.centralizer (sylowCenter (T : Subgroup X) : Set X) → e = 1)
    {W : Subgroup X} (hWT : W ≤ T) (hDW : D ≤ Subgroup.normalizer (W : Set X)) {f y : X}
    (hf : f ∈ Subgroup.zpowers e₀) (hy : y ∈ (T : Subgroup X)) (hyW : y ∉ W)
    (hfy : y⁻¹ * (f * y * f⁻¹) ∈ W) : f = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfD : f ∈ D := Subgroup.zpowers_le.mpr he₀ hf
  let S : Set X := (fun w => y * w) '' (W : Set X)
  have hmemS : ∀ x, x ∈ S ↔ y⁻¹ * x ∈ W := by
    intro x
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
    · intro hx
      exact ⟨y⁻¹ * x, hx, by group⟩
  have hE := CFSG.Walter.J1.card_dvd_ncard_of_free (H := Subgroup.zpowers f) (X := S) ?_ ?_
  · have hS : S.ncard = Nat.card W := by
      rw [Set.ncard_image_of_injective _ (mul_right_injective y), ← Nat.card_coe_set_eq]
      rfl
    rw [hS, Nat.card_zpowers] at hE
    obtain ⟨c, hc⟩ := (IsPGroup.iff_card.mp (T.isPGroup'.to_le hWT))
    rw [hc] at hE
    have hodd : Odd (orderOf f) := h.odd.of_dvd_nat (Subgroup.orderOf_dvd_natCard D hfD)
    have hcop : Nat.Coprime (orderOf f) (2 ^ c) :=
      Nat.Coprime.pow_right c (Nat.coprime_two_right.mpr hodd)
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hE)
  · intro u hu k hk
    rw [hmemS] at hu ⊢
    have hfin : IsOfFinOrder f := isOfFinOrder_of_finite f
    obtain ⟨j, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (hfin.mem_powers_iff_mem_zpowers.mpr hk)
    have hfjD : f ^ j ∈ D := D.pow_mem hfD j
    have e : y⁻¹ * (f ^ j * u * (f ^ j)⁻¹) =
        (y⁻¹ * (f ^ j * y * (f ^ j)⁻¹)) * (f ^ j * (y⁻¹ * u) * (f ^ j)⁻¹) := by group
    rw [e]
    exact W.mul_mem (coset_pow (hDW hfD) hfy j)
      ((Subgroup.mem_normalizer_iff.mp (hDW hfjD) _).mp hu)
  · intro u hu k hk hku
    by_contra hk1
    have hkE : k ∈ Subgroup.zpowers e₀ := (Subgroup.zpowers_le.mpr hf) hk
    have huT : u ∈ (T : Subgroup X) := by
      rw [hmemS] at hu
      have e : u = y * (y⁻¹ * u) := by group
      rw [e]
      exact (T : Subgroup X).mul_mem hy (hWT hu)
    have hu1 := h.eq_one_of_commute_D₀ he₀ hfree hkE hk1 huT hku
    rw [hmemS, hu1, mul_one] at hu
    exact hyW (by simpa using W.inv_mem hu)

theorem mem_of_mem_kerD [Finite X] {e₀ : X} (he₀ : e₀ ∈ D)
    (hord : orderOf e₀ = Nat.card (sylowCenter (T : Subgroup X)) - 1)
    (hfree : ∀ e ∈ Subgroup.zpowers e₀,
      e ∈ Subgroup.centralizer (sylowCenter (T : Subgroup X) : Set X) → e = 1)
    (hcop : Nat.Coprime (Nat.card (sylowCenter (T : Subgroup X)) - 1) (Nat.card (kerD D T)))
    {W Y' : Subgroup X} (hWY : W ≤ Y') (hY'T : Y' ≤ T) (hDW : D ≤ Subgroup.normalizer (W : Set X))
    (hDY' : D ≤ Subgroup.normalizer (Y' : Set X))
    (hidx : Nat.card Y' = Nat.card (sylowCenter (T : Subgroup X)) * Nat.card W) {d₁ y : X}
    (hd₁ : d₁ ∈ kerD D T) (hy : y ∈ Y') : y⁻¹ * (d₁ * y * d₁⁻¹) ∈ W := by
  classical
  have hconj : ∀ {e : X}, e ∈ D → ∀ {x : X}, x ∈ W → e * x * e⁻¹ ∈ W :=
    fun he _ hx => (Subgroup.mem_normalizer_iff.mp (hDW he) _).mp hx
  by_cases hyW : y ∈ W
  · exact W.mul_mem (W.inv_mem hyW) (hconj hd₁.1 hyW)
  have hyT : y ∈ (T : Subgroup X) := hY'T hy
  have hconjY : ∀ {e : X}, e ∈ D → e * y * e⁻¹ ∈ Y' :=
    fun he => (Subgroup.mem_normalizer_iff.mp (hDY' he) _).mp hy
  have hE : Subgroup.zpowers e₀ ≤ D := Subgroup.zpowers_le.mpr he₀
  have key : ∀ {e e' : X}, e ∈ D → (e * y * e⁻¹)⁻¹ * (e' * y * e'⁻¹) ∈ W →
      y⁻¹ * ((e⁻¹ * e') * y * (e⁻¹ * e')⁻¹) ∈ W := by
    intro e e' he hw
    have h1 := hconj (D.inv_mem he) hw
    have e1 : e⁻¹ * ((e * y * e⁻¹)⁻¹ * (e' * y * e'⁻¹)) * e⁻¹⁻¹ =
        y⁻¹ * ((e⁻¹ * e') * y * (e⁻¹ * e')⁻¹) := by group
    rwa [e1] at h1
  let W' := W.subgroupOf Y'
  let φ : Option (Subgroup.zpowers e₀) → Y' ⧸ W' := fun o =>
    match o with
    | none => ((1 : Y') : Y' ⧸ W')
    | some e => ((⟨(e : X) * y * (e : X)⁻¹, hconjY (hE e.2)⟩ : Y') : Y' ⧸ W')
  have hne1 : ∀ e : Subgroup.zpowers e₀,
      ((⟨(e : X) * y * (e : X)⁻¹, hconjY (hE e.2)⟩ : Y') : Y' ⧸ W') ≠ ((1 : Y') : Y' ⧸ W') := by
    intro e he
    rw [QuotientGroup.eq, mul_one, inv_mem_iff] at he
    have he' : (e : X) * y * (e : X)⁻¹ ∈ W := Subgroup.mem_subgroupOf.mp he
    apply hyW
    have h1 := hconj (D.inv_mem (hE e.2)) he'
    have e1 : (e : X)⁻¹ * ((e : X) * y * (e : X)⁻¹) * (e : X)⁻¹⁻¹ = y := by group
    rwa [e1] at h1
  have hinj : Function.Injective φ := by
    rintro (_ | e) (_ | e') hee'
    · rfl
    · exact absurd hee'.symm (hne1 e')
    · exact absurd hee' (hne1 e)
    · simp only [φ] at hee'
      rw [QuotientGroup.eq] at hee'
      have hw : ((e : X) * y * (e : X)⁻¹)⁻¹ * ((e' : X) * y * (e' : X)⁻¹) ∈ W :=
        Subgroup.mem_subgroupOf.mp hee'
      have hf := key (hE e.2) hw
      have hf1 := h.eq_one_of_fix_coset he₀ hfree (hY'T.trans' hWY) hDW
        ((Subgroup.zpowers e₀).mul_mem ((Subgroup.zpowers e₀).inv_mem e.2) e'.2) hyT hyW hf
      rw [inv_mul_eq_one] at hf1
      exact congrArg some (Subtype.ext hf1)
  have hcardQ : Nat.card (Y' ⧸ W') = Nat.card (sylowCenter (T : Subgroup X)) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup W'
    have h2 : Nat.card W' = Nat.card W := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWY).toEquiv
    rw [h2, hidx] at h1
    exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos h1).symm
  have hq1 : 1 ≤ Nat.card (sylowCenter (T : Subgroup X)) := Nat.card_pos
  have hbij : Function.Bijective φ := by
    refine (Nat.bijective_iff_injective_and_card φ).mpr ⟨hinj, ?_⟩
    rw [Finite.card_option, Nat.card_zpowers, hord, hcardQ]
    omega
  obtain ⟨o, ho⟩ := hbij.2 ((⟨d₁ * y * d₁⁻¹, hconjY hd₁.1⟩ : Y') : Y' ⧸ W')
  rcases o with _ | e
  · exfalso
    have := hne1 1
    simp only [φ] at ho
    apply hyW
    rw [QuotientGroup.eq, inv_one, one_mul] at ho
    have hw : d₁ * y * d₁⁻¹ ∈ W := Subgroup.mem_subgroupOf.mp ho
    have h1 := hconj (D.inv_mem hd₁.1) hw
    have e1 : d₁⁻¹ * (d₁ * y * d₁⁻¹) * d₁⁻¹⁻¹ = y := by group
    rwa [e1] at h1
  · simp only [φ] at ho
    rw [QuotientGroup.eq] at ho
    have hw : ((e : X) * y * (e : X)⁻¹)⁻¹ * (d₁ * y * d₁⁻¹) ∈ W := Subgroup.mem_subgroupOf.mp ho
    have hf := key (hE e.2) hw
    set m₁ := Nat.card (kerD D T) with hm₁
    have hd₁m : d₁ ^ m₁ = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard (kerD D T) hd₁)
    have hcomm : Commute ((e : X)⁻¹) d₁ := (h.comm (D.inv_mem (hE e.2)) hd₁.1)
    have hfpow := coset_pow (hDW (D.mul_mem (D.inv_mem (hE e.2)) hd₁.1)) hf m₁
    rw [hcomm.mul_pow, hd₁m, mul_one] at hfpow
    have he1 : ((e : X)⁻¹) ^ m₁ = 1 := h.eq_one_of_fix_coset he₀ hfree (hY'T.trans' hWY) hDW
      ((Subgroup.zpowers e₀).pow_mem ((Subgroup.zpowers e₀).inv_mem e.2) m₁) hyT hyW hfpow
    have he2 : (e : X) ^ (Nat.card (sylowCenter (T : Subgroup X)) - 1) = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (hord ▸ orderOf_dvd_of_mem_zpowers e.2)
    have he3 : (e : X) ^ m₁ = 1 := by
      rw [inv_pow, inv_eq_one] at he1
      exact he1
    have he4 := pow_gcd_eq_one.mpr ⟨he2, he3⟩
    rw [hcop.gcd_eq_one, pow_one] at he4
    rw [he4, inv_one, one_mul] at hf
    exact hf

theorem false_of_middle [Finite X] {e₀ : X} (he₀ : e₀ ∈ D)
    (hord : orderOf e₀ = Nat.card (sylowCenter (T : Subgroup X)) - 1)
    (hfree : ∀ e ∈ Subgroup.zpowers e₀,
      e ∈ Subgroup.centralizer (sylowCenter (T : Subgroup X) : Set X) → e = 1)
    (hcop : Nat.Coprime (Nat.card (sylowCenter (T : Subgroup X)) - 1) (Nat.card (kerD D T)))
    (hm₁ : 2 ≤ Nat.card (kerD D T)) {Y : Subgroup X} (hZY : sylowCenter (T : Subgroup X) ≤ Y)
    (hYT : Y ≤ T) (hDY : D ≤ Subgroup.normalizer (Y : Set X))
    (hY : Nat.card Y = Nat.card (sylowCenter (T : Subgroup X)) *
      Nat.card (sylowCenter (T : Subgroup X)))
    (hT : Nat.card (T : Subgroup X) = Nat.card (sylowCenter (T : Subgroup X)) * Nat.card Y) :
    False := by
  have hDZ : D ≤ Subgroup.normalizer ((sylowCenter (T : Subgroup X) : Subgroup X) : Set X) := by
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨fun hz => h.conj_mem_center hd hz, fun hz => ?_⟩
    have := h.conj_mem_center (D.inv_mem hd) hz
    simpa [mul_assoc] using this
  have hDT : D ≤ Subgroup.normalizer (((T : Subgroup X) : Subgroup X) : Set X) := h.le
  have hb : ∀ d₁ ∈ kerD D T, ∀ v ∈ Y, d₁ * v = v * d₁ := by
    intro d₁ hd₁ v hv
    refine h.commute_of_coset (sylowCenter_le _) hd₁.1 (fun w hw =>
      ((Subgroup.mem_centralizer_iff.mp hd₁.2) w hw).symm) ?_
    exact h.mem_of_mem_kerD he₀ hord hfree hcop hZY hYT hDZ hDY hY hd₁ hv
  have hc : ∀ d₁ ∈ kerD D T, ∀ t ∈ (T : Subgroup X), d₁ * t = t * d₁ := by
    intro d₁ hd₁ t ht
    refine h.commute_of_coset hYT hd₁.1 (fun w hw => hb d₁ hd₁ w hw) ?_
    exact h.mem_of_mem_kerD he₀ hord hfree hcop hYT le_rfl hDY hDT hT hd₁ ht
  have hbot : kerD D T = ⊥ := by
    rw [eq_bot_iff, ← h.inf_centralizer]
    exact fun d₁ hd₁ => ⟨hd₁.1, Subgroup.mem_centralizer_iff.mpr fun t ht => (hc d₁ hd₁ t ht).symm⟩
  rw [hbot, Subgroup.card_bot] at hm₁
  omega

omit h in
theorem pow_sub_one_dvd_cases {m w : ℕ} (hw : w ≤ 2 * m) (hdvd : 2 ^ m - 1 ∣ 2 ^ w - 1) :
    w = 0 ∨ w = m ∨ w = 2 * m := by
  have hlt : ∀ u < m, 2 ^ m - 1 ∣ 2 ^ u - 1 → u = 0 := by
    intro u hu hd
    have h1 : 2 ^ u < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) hu
    have h2 : 1 ≤ 2 ^ u := Nat.one_le_two_pow
    have h3 : 2 ^ u - 1 = 0 := Nat.eq_zero_of_dvd_of_lt hd (by omega)
    have h4 : 2 ^ u = 2 ^ 0 := by rw [pow_zero]; omega
    exact Nat.pow_right_injective le_rfl h4
  rcases lt_or_ge w m with hwm | hwm
  · exact Or.inl (hlt w hwm hdvd)
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hwm
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have h2 : 1 ≤ 2 ^ u := Nat.one_le_two_pow
  have key : 2 ^ (m + u) - 1 = 2 ^ u * (2 ^ m - 1) + (2 ^ u - 1) := by
    rw [pow_add]
    have h3 : 1 ≤ 2 ^ m * 2 ^ u := Nat.one_le_iff_ne_zero.mpr (by positivity)
    zify [h1, h2, h3]
    ring
  have hd : 2 ^ m - 1 ∣ 2 ^ u - 1 := by
    rw [key] at hdvd
    exact (Nat.dvd_add_right (dvd_mul_left _ _)).mp hdvd
  rcases lt_or_ge u m with hum | hum
  · have := hlt u hum hd
    right; left; omega
  · right; right; omega

theorem eq_or_eq_of_invariant [Finite X]
    (hcase : (Nat.card (T : Subgroup X) = Nat.card (sylowCenter (T : Subgroup X)) ^ 2 ∧
        Nat.card D = Nat.card (sylowCenter (T : Subgroup X)) - 1) ∨
      (Nat.card (T : Subgroup X) = Nat.card (sylowCenter (T : Subgroup X)) ^ 3 ∧
        Nat.card D = (Nat.card (sylowCenter (T : Subgroup X)) ^ 2 - 1) /
          Nat.gcd 3 (Nat.card (sylowCenter (T : Subgroup X)) + 1)))
    {Y : Subgroup X} (hZY : sylowCenter (T : Subgroup X) ≤ Y) (hYT : Y ≤ T)
    (hDY : D ≤ Subgroup.normalizer (Y : Set X)) :
    Y = sylowCenter (T : Subgroup X) ∨ Y = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set q := Nat.card (sylowCenter (T : Subgroup X)) with hq
  have hDm : Nat.card D = (q - 1) * Nat.card (kerD D T) := h.card_eq_mul
  have hq4 : 4 ≤ q := h.four
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (T.isPGroup'.to_le (sylowCenter_le (T : Subgroup X)))
  rw [← hq] at hm
  have hm1 : 1 ≤ m := by
    by_contra hlt
    rw [show m = 0 by omega, pow_zero] at hm
    omega
  have h2m : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h1m : 1 ≤ 2 ^ (m - 1) := Nat.one_le_two_pow
  have hoddq : Odd (q - 1) := ⟨2 ^ (m - 1) - 1, by omega⟩
  have hq1 : 0 < q - 1 := by omega
  obtain ⟨hcop, hcase'⟩ : Nat.Coprime (q - 1) (Nat.card (kerD D T)) ∧
      ((Nat.card (T : Subgroup X) = q ^ 2) ∨
        (Nat.card (T : Subgroup X) = q ^ 3 ∧ 2 ≤ Nat.card (kerD D T))) := by
    rcases hcase with ⟨hT, hD⟩ | ⟨hT, hD⟩
    · have h1 : Nat.card (kerD D T) = 1 := by
        rw [hD] at hDm
        have := Nat.eq_of_mul_eq_mul_left hq1 (hDm.symm.trans (mul_one (q - 1)).symm)
        exact this
      exact ⟨by rw [h1]; exact Nat.coprime_one_right _, Or.inl hT⟩
    · have hδ3 : Nat.gcd 3 (q + 1) ∣ 3 := Nat.gcd_dvd_left 3 (q + 1)
      obtain ⟨c, hc⟩ : Nat.gcd 3 (q + 1) ∣ q + 1 := Nat.gcd_dvd_right 3 (q + 1)
      set δ := Nat.gcd 3 (q + 1) with hδ
      have hδpos : 0 < δ := Nat.gcd_pos_of_pos_left _ (by norm_num)
      have hsq : q ^ 2 - 1 = (q - 1) * (q + 1) := by
        have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
        zify [this, show 1 ≤ q by omega]
        ring
      have hDc : Nat.card D = (q - 1) * c := by
        rw [hD, hsq, hc, show (q - 1) * (δ * c) = ((q - 1) * c) * δ by ring,
          Nat.mul_div_cancel _ hδpos]
      have hm₁c : Nat.card (kerD D T) = c :=
        Nat.eq_of_mul_eq_mul_left hq1 (hDm.symm.trans hDc)
      have hcop2 : Nat.Coprime (q - 1) (q + 1) := by
        have e : q + 1 = 2 + (q - 1) := by omega
        rw [e, Nat.coprime_add_self_right]
        exact Nat.coprime_two_right.mpr hoddq
      refine ⟨hm₁c ▸ hcop2.coprime_dvd_right ⟨δ, by rw [hc]; ring⟩, Or.inr ⟨hT, ?_⟩⟩
      rw [hm₁c]
      rcases (Nat.dvd_prime Nat.prime_three).mp hδ3 with hδ1 | hδ1
      · rw [hδ1, one_mul] at hc
        omega
      · rw [hδ1] at hc
        omega
  obtain ⟨e₀, he₀, hord, hfree⟩ := h.exists_D₀ hcop
  have hdvd := h.dvd_card_sub he₀ hfree hZY hYT hDY
  rw [hord, ← hq] at hdvd
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (T.isPGroup'.to_le hYT)
  have hZYd : q ∣ Nat.card Y := Subgroup.card_dvd_of_le hZY
  have hma : m ≤ a := by
    rw [hm, ha] at hZYd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hZYd
  obtain ⟨w, rfl⟩ := Nat.exists_eq_add_of_le hma
  have hsub : 2 ^ (m + w) - 2 ^ m = 2 ^ m * (2 ^ w - 1) := by rw [pow_add, Nat.mul_sub_one]
  have hcopm : Nat.Coprime (2 ^ m - 1) (2 ^ m) := by
    have := (Nat.coprime_two_right.mpr hoddq).pow_right m
    rwa [hm] at this
  have hdvd' : 2 ^ m - 1 ∣ 2 ^ w - 1 := by
    rw [ha, hm, hsub] at hdvd
    exact hcopm.dvd_of_dvd_mul_left hdvd
  have hYTd : Nat.card Y ∣ Nat.card (T : Subgroup X) := Subgroup.card_dvd_of_le hYT
  have hYZ : Nat.card Y = q → Y = sylowCenter (T : Subgroup X) := fun hY =>
    (Subgroup.eq_of_le_of_card_ge hZY (le_of_eq hY)).symm
  have hYT' : Nat.card Y = Nat.card (T : Subgroup X) → Y = T := fun hY =>
    Subgroup.eq_of_le_of_card_ge hYT (le_of_eq hY.symm)
  rcases hcase' with hT | ⟨hT, hm₁⟩
  · have hw : w ≤ m := by
      rw [hT, hm, ha, ← pow_mul] at hYTd
      have := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hYTd
      omega
    rcases pow_sub_one_dvd_cases (by omega) hdvd' with hw0 | hwm | hw2
    · left
      exact hYZ (by rw [ha, hw0, add_zero, hm])
    · right
      exact hYT' (by rw [ha, hT, hwm, hm, ← pow_mul]; ring_nf)
    · omega
  · have hw : w ≤ 2 * m := by
      rw [hT, hm, ha, ← pow_mul] at hYTd
      have := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hYTd
      omega
    rcases pow_sub_one_dvd_cases hw hdvd' with hw0 | hwm | hw2
    · left
      exact hYZ (by rw [ha, hw0, add_zero, hm])
    · exfalso
      refine h.false_of_middle he₀ hord hfree hcop hm₁ hZY hYT hDY ?_ ?_
      · rw [ha, hwm, ← hq, hm, ← pow_add]
      · rw [ha, hwm, ← hq, hT, hm, ← pow_add, ← pow_mul]
        ring_nf
    · right
      exact hYT' (by rw [ha, hT, hw2, hm, ← pow_mul]; ring_nf)

theorem card_eq [Finite X] :
    Nat.card X = Nat.card (T : Subgroup X) * Nat.card D * (Nat.card (T : Subgroup X) + 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : Nat.card (Subgroup.normalizer ((T : Subgroup X) : Set X)) =
      Nat.card (T : Subgroup X) * Nat.card D := by
    rw [← h.sup]
    exact CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ h.le
      (disjoint_iff.mpr h.inf)
  have hidx : (Subgroup.normalizer ((T : Subgroup X) : Set X)).index = Nat.card (Sylow 2 X) :=
    (Sylow.card_eq_index_normalizer T).symm
  rw [← Subgroup.card_mul_index (Subgroup.normalizer ((T : Subgroup X) : Set X)), hN, hidx,
    h.card]

theorem orders_psl2
    [Finite X] {n : ℕ} (hn : 2 ≤ n) (e : X ≃* PSL(2, GaloisField 2 n)) :
    Nat.card (T : Subgroup X) = 2 ^ n ∧ Nat.card D = 2 ^ n - 1 ∧
      Nat.card (sylowCenter (T : Subgroup X)) = 2 ^ n := by
  have : Finite PSL(2, GaloisField 2 n) := Finite.of_equiv X e.toEquiv
  have hB := (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_1
    n hn).map_mulEquiv e.symm
  obtain ⟨-, -, hZ, hTc⟩ :=
    CFSG.ComponentClassification.AschbacherToolkit.Bender.benderBorel_sylowCenter hB T
  rw [pow_one] at hTc
  have hX : Nat.card X = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Walter.psl2_even_card (by omega)
  have hc := h.card_eq
  rw [hX, hTc] at hc
  refine ⟨hTc, ?_, hZ⟩
  set Q := 2 ^ n with hQ
  have h1 : 1 ≤ Q := Nat.one_le_two_pow
  have hsq : Q ^ 2 - 1 = (Q - 1) * (Q + 1) := by
    have : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [this, h1]
    ring
  rw [hsq] at hc
  generalize Q - 1 = u at hc ⊢
  have key : (Q * (Q + 1)) * Nat.card D = (Q * (Q + 1)) * u := by
    calc (Q * (Q + 1)) * Nat.card D = Q * Nat.card D * (Q + 1) := by ring
      _ = Q * (u * (Q + 1)) := hc.symm
      _ = (Q * (Q + 1)) * u := by ring
  exact Nat.eq_of_mul_eq_mul_left (by positivity) key

theorem orders_sz [Finite X] {n : ℕ} (hn : 1 ≤ n) (e : X ≃* Sz n) :
    Nat.card (sylowCenter (T : Subgroup X)) = 2 ^ (2 * n + 1) ∧
      Nat.card (T : Subgroup X) = (2 ^ (2 * n + 1)) ^ 2 ∧ Nat.card D = 2 ^ (2 * n + 1) - 1 := by
  have : Finite (Sz n) := Finite.of_equiv X e.toEquiv
  have hB := (CFSG.Open.bender_suzuki_borel_full n hn).map_mulEquiv e.symm
  obtain ⟨-, -, hZ, hTc⟩ :=
    CFSG.ComponentClassification.AschbacherToolkit.Bender.benderBorel_sylowCenter hB T
  have hX : Nat.card X = (2 ^ (2 * n + 1)) ^ 2 * ((2 ^ (2 * n + 1)) ^ 2 + 1) *
      (2 ^ (2 * n + 1) - 1) := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_sz n
  have hc := h.card_eq
  rw [hX, hTc] at hc
  refine ⟨hZ, hTc, ?_⟩
  set Q := 2 ^ (2 * n + 1) with hQ
  generalize Q - 1 = u at hc ⊢
  have key : (Q ^ 2 * (Q ^ 2 + 1)) * Nat.card D = (Q ^ 2 * (Q ^ 2 + 1)) * u := by
    calc (Q ^ 2 * (Q ^ 2 + 1)) * Nat.card D = Q ^ 2 * Nat.card D * (Q ^ 2 + 1) := by ring
      _ = Q ^ 2 * (Q ^ 2 + 1) * u := hc.symm
  exact Nat.eq_of_mul_eq_mul_left (by positivity) key

theorem orders_psu3 [Finite X] {n : ℕ} (hn : 2 ≤ n) (e : X ≃* PSU3 2 n) :
    Nat.card (sylowCenter (T : Subgroup X)) = 2 ^ n ∧
      Nat.card (T : Subgroup X) = (2 ^ n) ^ 3 ∧
      Nat.card D = ((2 ^ n) ^ 2 - 1) / Nat.gcd 3 (2 ^ n + 1) := by
  have : Finite (PSU3 2 n) := Finite.of_equiv X e.toEquiv
  have hB := (CFSG.Open.bender_psu3_borel_full n hn).map_mulEquiv e.symm
  obtain ⟨-, -, hZ, hTc⟩ :=
    CFSG.ComponentClassification.AschbacherToolkit.Bender.benderBorel_sylowCenter hB T
  have hX : Nat.card X * Nat.gcd 3 (2 ^ n + 1) =
      (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1)) := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_psu3_mul_gcd (by omega)
  have hc := h.card_eq
  rw [hc, hTc] at hX
  refine ⟨hZ, hTc, ?_⟩
  set Q := 2 ^ n with hQ
  set δ := Nat.gcd 3 (Q + 1) with hδ
  have hδpos : 0 < δ := Nat.gcd_pos_of_pos_left _ (by norm_num)
  generalize Q ^ 2 - 1 = u at hX ⊢
  have key : (Q ^ 3 * (Q ^ 3 + 1)) * (Nat.card D * δ) = (Q ^ 3 * (Q ^ 3 + 1)) * u := by
    calc (Q ^ 3 * (Q ^ 3 + 1)) * (Nat.card D * δ) = Q ^ 3 * Nat.card D * (Q ^ 3 + 1) * δ := by
          ring
      _ = Q ^ 3 * (u * (Q ^ 3 + 1)) := hX
      _ = (Q ^ 3 * (Q ^ 3 + 1)) * u := by ring
  have hDu := Nat.eq_of_mul_eq_mul_left (by positivity) key
  rw [← hDu, Nat.mul_div_cancel _ hδpos]

end BorelSetup

omit [Group X] in
theorem exists_borelSetup
    {X : Type} [Group X] [Finite X] (hX : fusionIsBenderGroup X)
    (T : Sylow 2 X) : ∃ D : Subgroup X, BorelSetup T D := by
  have hD := CFSG.ComponentClassification.AschbacherToolkit.BenderExt.benderData_of_isBenderGroup hX
  obtain ⟨q, k, hq4, hB⟩ := hD.borel
  obtain ⟨hSE, ⟨D, hDcyc, hDodd, hTD, hsup⟩, -, -, -⟩ := hB T
  obtain ⟨-, hZ2, hZcard, -⟩ :=
    CFSG.ComponentClassification.AschbacherToolkit.Bender.benderBorel_sylowCenter hB T
  refine ⟨D, hSE, GoldType.card_sylow_of_bender hX T, ?_, hDcyc, hDodd, hTD, hsup, hZ2,
    fun t ht ht2 =>
      CFSG.ComponentClassification.AschbacherToolkit.Goldschmidt.mem_sylowCenter_of_sq_eq_one hB
        (by omega) T ht ht2, by omega, GoldType.centralizer_le_of_bender hX T⟩
  rw [← hsup]
  exact le_sup_right

end Borel

theorem typeI_models {L : Type} [Group L] [Finite L] [IsSimpleGroup L] (hI : IsGoldTypeI L) :
    fusionIsBenderGroup L ∧
      ((∃ n : ℕ, 3 ≤ n ∧ Nonempty (L ≃* PSL(2, GaloisField 2 n))) ∨
        (∃ n : ℕ, 1 ≤ n ∧ Nonempty (L ≃* Sz n)) ∨
        (∃ n : ℕ, 2 ≤ n ∧ Nonempty (L ≃* PSU3 2 n))) := by
  have hQ : fusionIsBenderGroup (L ⧸ Subgroup.center L) := by
    rcases hI with ⟨n, hn, he⟩ | ⟨n, hn, he⟩ | ⟨n, hn, he⟩
    · exact Or.inl ⟨n, by omega, he⟩
    · exact Or.inr (Or.inr ⟨n, hn, he⟩)
    · exact Or.inr (Or.inl ⟨n, hn, he⟩)
  have : IsSimpleGroup (L ⧸ Subgroup.center L) :=
    CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hQ
  have hZ : Subgroup.center L = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h | h
    · exact h
    · exfalso
      have hsub : Subsingleton (L ⧸ Subgroup.center L) := by
        rw [h]
        exact QuotientGroup.subsingleton_quotient_top
      exact not_subsingleton _ hsub
  refine ⟨CFSG.QuasithinUnique.RankOneRecog.fusionIsBenderGroup_of_center_eq_bot hZ hQ, ?_⟩
  rcases hI with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · exact Or.inl ⟨n, hn, ⟨CFSG.QuasithinUnique.RankOneRecog.mulEquivOfCenterEqBot hZ e⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨CFSG.QuasithinUnique.RankOneRecog.mulEquivOfCenterEqBot hZ e⟩⟩)
  · exact Or.inr (Or.inr ⟨n, hn, ⟨CFSG.QuasithinUnique.RankOneRecog.mulEquivOfCenterEqBot hZ e⟩⟩)

end G3a

open G3a in
theorem G32 : S_G32 := by
  intro L _ _ _ hI T
  obtain ⟨hX, hfam⟩ := typeI_models hI
  obtain ⟨D, h⟩ := exists_borelSetup hX T
  obtain ⟨T', hT'ne, hDT'⟩ := h.exists_fixed
  have hΩ : Omega1 (T : Subgroup L) = (T : Subgroup L) ⊓
      Subgroup.centralizer ((T : Subgroup L) : Set L) :=
    GoldType.omega1_eq_sylowCenter_of_bender hX T
  refine ⟨D, h.le, h.cyc, h.odd, h.inf, h.sup, h.inf_centralizer, h.commutator_eq, hΩ, ?_, ?_,
    ?_, ?_, ?_, fun g hg => h.ti g hg, fun P Q hP hQ => h.exists_smul hP hQ,
    ⟨T', hT'ne, hDT', h.normalizer_inf_eq hT'ne hDT',
      fun P hP => h.eq_of_le_normalizer hT'ne hDT' hP⟩,
    h.isCoatom, fun M hTM hM => h.le_normalizer_of_le hTM hM⟩
  · intro x hx x' hx' hx1 hx'1
    rw [hΩ] at hx hx'
    exact h.trans hx hx' hx1 hx'1
  · intro hab
    have hcase : (Nat.card (T : Subgroup L) =
          Nat.card (CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter
            (T : Subgroup L)) ^ 2 ∧
        Nat.card D = Nat.card (CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter
          (T : Subgroup L)) - 1) ∨
        (Nat.card (T : Subgroup L) =
          Nat.card (CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter
            (T : Subgroup L)) ^ 3 ∧
        Nat.card D = (Nat.card (CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter
          (T : Subgroup L)) ^ 2 - 1) /
          Nat.gcd 3 (Nat.card (CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter
            (T : Subgroup L)) + 1)) := by
      rcases hfam with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
      · exact absurd (GoldType.isMulCommutative_of_psl2_even (by omega) e T) hab
      · obtain ⟨hZc, hTc, hDc⟩ := h.orders_sz hn e
        left
        rw [hZc, hTc, hDc]
        exact ⟨rfl, rfl⟩
      · obtain ⟨hZc, hTc, hDc⟩ := h.orders_psu3 hn e
        right
        rw [hZc, hTc, hDc]
        exact ⟨rfl, rfl⟩
    exact ⟨h.commutator_eq_center hab, fun x hx => h.sq_mem_center hab hx,
      fun Y hZY hYT hDY => h.eq_or_eq_of_invariant hcase hZY hYT hDY⟩
  · rintro n hn ⟨e⟩
    obtain ⟨hTc, hDc, -⟩ := h.orders_psl2 (by omega) e
    exact ⟨hTc, hDc⟩
  · rintro n hn ⟨e⟩
    obtain ⟨hZc, hTc, hDc⟩ := h.orders_sz hn e
    exact ⟨hZc, by rw [hTc, ← pow_mul, mul_comm], hDc⟩
  · rintro n hn ⟨e⟩
    obtain ⟨hZc, hTc, hDc⟩ := h.orders_psu3 hn e
    exact ⟨hZc, by rw [hTc, ← pow_mul, mul_comm], by rw [hDc, ← pow_mul, mul_comm]⟩

end CFSG.Goldschmidt
