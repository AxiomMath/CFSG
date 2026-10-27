module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_6_KernelT
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Struct
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_6_9_1
public import CFSG.LocalAnalysis.GL83PartI.I_6_10
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.PGroupNormalE2
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped Pointwise

section Basic

theorem i116e_isQuasisimple {X : Type*} [Group X] {p : ℕ} (hO : GLAPPrimeCore p X = ⊥)
    {L : Subgroup X} (hL : GLAPComponent p ⊤ L) : CFSG.Open.IsQuasisimple ↥L := by
  have hcore : GLAPPrimeCore p ↥(⊤ : Subgroup X) = ⊥ := by
    have h1 := glaPPrimeCore_map_iso p (Subgroup.topEquiv (G := X))
    rw [hO] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.topEquiv (G := X)).injective).1 h1
  have hq : CFSG.Open.IsQuasisimple ↥(barX p ⊤ L) := hL.2.2.1.2.2
  have hinj : Function.Injective (QuotientGroup.mk' (GLAPPrimeCore p ↥(⊤ : Subgroup X))) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hcore]
  let e1 : ↥(L.subgroupOf (⊤ : Subgroup X)) ≃* ↥(barX p ⊤ L) :=
    Subgroup.equivMapOfInjective _ _ hinj
  let e2 : ↥(L.subgroupOf (⊤ : Subgroup X)) ≃* ↥L := Subgroup.subgroupOfEquivOfLe le_top
  exact CFSG.ComponentClassification.Components.quasisimple_of_equiv (e2.symm.trans e1) hq

theorem i116e_dvd_card {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hO : GLAPPrimeCore p X = ⊥)
    {L : Subgroup X} (hL : GLAPComponent p ⊤ L) : p ∣ Nat.card L := by
  by_contra hndvd
  have hcop : Nat.Coprime p (Nat.card L) := (Nat.Prime.coprime_iff_not_dvd hp).2 hndvd
  have h1 : L ≤ GLAPPrimeCoreOf p (⊤ : Subgroup X) := by
    rw [← glaPPrimeCoreOf_eq_self_of_coprime hcop]
    exact glaPPrimeCoreOf_le_of_isSubnormal hp hL.2.1
  rw [glaPPrimeCoreOf_top_eq_bot_of_eq_bot hO, le_bot_iff] at h1
  have hnt : Nontrivial L :=
    CFSG.ComponentClassification.Quasisimple.nontrivial (i116e_isQuasisimple hO hL)
  exact (Subgroup.nontrivial_iff_ne_bot _).1 hnt h1

theorem i116e_exists_sylow {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {B L : Subgroup X} (hBp : IsPGroup p B) (hBL : B ≤ Subgroup.normalizer (L : Set X)) :
    ∃ P R : Subgroup X, IsPGroup p P ∧ B ≤ P ∧ CFSG.ABGLocalTools.IsSylowOf p R L ∧ R ≤ P ∧
      P ≤ Subgroup.normalizer (R : Set X) := by
  set M : Subgroup X := L ⊔ B with hM
  have hLM : L ≤ M := le_sup_left
  have hBM : B ≤ M := le_sup_right
  have hMnorm : M ≤ Subgroup.normalizer (L : Set X) := sup_le Subgroup.le_normalizer hBL
  have hBp' : IsPGroup p (B.subgroupOf M) := hBp.comap_subtype
  obtain ⟨Q, hQ⟩ := hBp'.exists_le_sylow
  set P : Subgroup X := (Q : Subgroup M).map M.subtype with hP
  have hPM : CFSG.ABGLocalTools.IsSylowOf p P M := ⟨Q, rfl⟩
  have hBP : B ≤ P := by
    intro b hb
    have hb' : (⟨b, hBM hb⟩ : M) ∈ (Q : Subgroup M) := hQ hb
    exact ⟨_, hb', rfl⟩
  have hPM' : P ≤ M := hPM.le
  refine ⟨P, P ⊓ L, hPM.isPGroup, hBP, hPM.inf_of_le_normalizer hLM hMnorm, inf_le_left, ?_⟩
  intro g hg
  have hgM : g ∈ Subgroup.normalizer (L : Set X) := hMnorm (hPM' hg)
  have hgP : g ∈ Subgroup.normalizer (P : Set X) := Subgroup.le_normalizer hg
  rw [Subgroup.mem_normalizer_iff] at hgM hgP ⊢
  intro h
  simp only [Subgroup.mem_inf]
  rw [hgM h, hgP h]

theorem i116e_exists_central {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {P R : Subgroup X} (hP : IsPGroup p P) (hRP : R ≤ P)
    (hnorm : P ≤ Subgroup.normalizer (R : Set X)) (hR : R ≠ ⊥) :
    ∃ w ∈ R, orderOf w = p ∧ ∀ g ∈ P, g * w = w * g := by
  have hN : (R.subgroupOf P).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hRP).2 hnorm
  have hnil : Group.IsNilpotent ↥P := hP.isNilpotent
  have hN'ne : R.subgroupOf P ≠ ⊥ := by
    intro hbot
    apply hR
    rw [eq_bot_iff]
    intro x hx
    have hmem : (⟨x, hRP hx⟩ : ↥P) ∈ R.subgroupOf P := hx
    rw [hbot, Subgroup.mem_bot] at hmem
    simpa using congrArg Subtype.val hmem
  have hcen := Group.IsNilpotent.inf_center_ne_bot_of_normal hN'ne
  have hnt : Nontrivial ↥(R.subgroupOf P ⊓ Subgroup.center ↥P) :=
    (Subgroup.nontrivial_iff_ne_bot _).2 hcen
  have hpZ : IsPGroup p ↥(R.subgroupOf P ⊓ Subgroup.center ↥P) := hP.to_subgroup _
  obtain ⟨n, hn0, hn⟩ := hpZ.nontrivial_iff_card.1 hnt
  have hdvdZ : p ∣ Nat.card ↥(R.subgroupOf P ⊓ Subgroup.center ↥P) := by
    rw [hn]; exact dvd_pow_self p hn0.ne'
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' p hdvdZ
  have hwP : orderOf ((w : ↥P) : X) = p := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw]
  refine ⟨((w : ↥P) : X), (Subgroup.mem_subgroupOf).1 w.2.1, hwP, ?_⟩
  intro g hg
  have hc := Subgroup.mem_center_iff.1 w.2.2 ⟨g, hg⟩
  have := congrArg (fun y : ↥P => (y : X)) hc
  simpa using this

theorem i116e_commutator_lt {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (A P : Subgroup X) (hAp : IsPGroup p A) (hPp : IsPGroup p P)
    (hPA : P ≤ Subgroup.normalizer (A : Set X)) (hAne : A ≠ ⊥) : ⁅A, P⁆ < A := by
  have hle : ⁅A, P⁆ ≤ A := (Subgroup.le_normalizer_iff_commutator_le_left).mp hPA
  refine lt_of_le_of_ne hle ?_
  intro heq
  let S : Subgroup X := A ⊔ P
  have hAnormS : (A.subgroupOf S).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer (H := A) (K := S) le_sup_left).2
    exact sup_le Subgroup.le_normalizer hPA
  have hAPp : IsPGroup p S := IsPGroup.to_sup_of_normal_left' hAp hPp hPA
  have hnil : Group.IsNilpotent ↑S := IsPGroup.isNilpotent (p := p) hAPp
  obtain ⟨n, hn⟩ := (Subgroup.nilpotent_iff_lowerCentralSeries (G := ↑S)).mp hnil
  have hA_le_lcs : ∀ n : ℕ, A.subgroupOf S ≤ (⊤ : Subgroup ↑S).lowerCentralSeries n := by
    intro n
    induction n with
    | zero => simp [Subgroup.lowerCentralSeries_zero]
    | succ n ih =>
        rw [Subgroup.lowerCentralSeries_succ]
        have hcomm_sub : ⁅A.subgroupOf S, P.subgroupOf S⁆ = A.subgroupOf S := by
          apply (Subgroup.map_subtype_inj (H := S)).mp
          calc
            (⁅A.subgroupOf S, P.subgroupOf S⁆).map S.subtype = A := by
              rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le le_sup_left,
                Subgroup.map_subgroupOf_eq_of_le le_sup_right, heq]
            _ = (A.subgroupOf S).map S.subtype :=
              (Subgroup.map_subgroupOf_eq_of_le le_sup_left).symm
        rw [← hcomm_sub]
        exact Subgroup.commutator_mono ih le_top
  have hAsub_bot : A.subgroupOf S = ⊥ := by
    apply bot_unique
    exact (hA_le_lcs n).trans_eq hn
  apply hAne
  calc
    A = (A.subgroupOf S).map S.subtype := (Subgroup.map_subgroupOf_eq_of_le le_sup_left).symm
    _ = ⊥ := by rw [hAsub_bot]; simp

theorem i116e_normalizer_commutator {X : Type*} [Group X] {A P : Subgroup X}
    (hPA : P ≤ Subgroup.normalizer (A : Set X)) : P ≤ Subgroup.normalizer ((⁅A, P⁆ : Subgroup X) : Set X) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (hPA hg),
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer hg)]

theorem i116e_normalizes_of_card_sq {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {B P U : Subgroup X} (hB : IsSCp p ⊤ B) (hP : IsPGroup p P) (hBP : B ≤ P) (hUle : U ≤ P)
    (hUP : P ≤ Subgroup.normalizer (U : Set X)) (hU : IsElemAbelian p U)
    (hcard : Nat.card U = p ^ 2) : U ≤ Subgroup.normalizer (B : Set X) := by
  have hpr : p.Prime := Fact.out
  have hUp : IsPGroup p U := IsPGroup.of_card hcard
  have hUne : U ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hpr.one_lt
    omega
  set C : Subgroup X := ⁅U, P⁆ with hC
  have hClt : C < U := i116e_commutator_lt U P hUp hP hUP hUne
  have hCU : C ≤ U := hClt.le
  have hCnorm : P ≤ Subgroup.normalizer (C : Set X) := i116e_normalizer_commutator hUP
  have hCcard : Nat.card C ∣ p ^ 2 := hcard ▸ Subgroup.card_dvd_of_le hCU
  have hCle : Nat.card C ≠ p ^ 2 := by
    intro h
    exact hClt.ne (Subgroup.eq_of_le_of_card_ge hCU (by rw [h, hcard]))
  have hCcentral : ∀ c ∈ C, ∀ g ∈ P, g * c = c * g := by
    by_cases hCb : C = ⊥
    · intro c hc g _
      rw [hCb, Subgroup.mem_bot] at hc
      rw [hc]; simp
    · obtain ⟨w, hwC, hwo, hwc⟩ := i116e_exists_central hP (hCU.trans hUle) hCnorm hCb
      have hzp : Subgroup.zpowers w = C := by
        apply Subgroup.eq_of_le_of_card_ge
        · exact (Subgroup.zpowers_le).2 hwC
        · rw [Nat.card_zpowers, hwo]
          obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow hpr).1 hCcard
          have hi1 : i ≤ 1 := by
            by_contra h
            exact hCle (by rw [hi']; congr; omega)
          rw [hi']
          calc p ^ i ≤ p ^ 1 := Nat.pow_le_pow_right hpr.pos hi1
            _ = p := pow_one p
      intro c hc g hg
      rw [← hzp] at hc
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
      exact (Commute.zpow_right (hwc g hg) k).eq
  have hCB : ∀ c ∈ C, c ∈ B := by
    intro c hc
    by_cases hc1 : c = 1
    · rw [hc1]; exact B.one_mem
    · have hcp : c ^ p = 1 := hU.2 c (hCU hc)
      have hord : orderOf c = p := orderOf_eq_prime hcp hc1
      refine mem_of_mem_centralizer_orderOf_eq_prime hB ?_ hord
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact hCcentral c hc b (hBP hb)
  have hclaim : ∀ u ∈ U, ∀ b ∈ B, u * b * u⁻¹ ∈ B := by
    intro u hu b hb
    have hcomm : u * b * u⁻¹ * b⁻¹ ∈ C := Subgroup.commutator_mem_commutator hu (hBP hb)
    have : u * b * u⁻¹ = (u * b * u⁻¹ * b⁻¹) * b := by group
    rw [this]
    exact B.mul_mem (hCB _ hcomm) hb
  intro u hu
  rw [Subgroup.mem_normalizer_iff]
  intro b
  refine ⟨fun hb => hclaim u hu b hb, fun hb => ?_⟩
  have := hclaim u⁻¹ (U.inv_mem hu) _ hb
  simpa [mul_assoc] using this

theorem i116e_exists_mem_normalizer_of_not_le {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {A B T : Subgroup X} (hT : IsPGroup p T) (hAT : A ≤ T) (hBT : B ≤ T)
    (hBA : B ≤ Subgroup.normalizer (A : Set X)) (hAB : ¬ A ≤ B) :
    ∃ e ∈ A, e ∈ Subgroup.normalizer (B : Set X) ∧ e ∉ B := by
  set S : Subgroup X := A ⊔ B with hS
  have hAS : A ≤ S := le_sup_left
  have hBS : B ≤ S := le_sup_right
  have hST : S ≤ T := sup_le hAT hBT
  have hSp : IsPGroup p ↥S := hT.to_le hST
  have hnil : Group.IsNilpotent ↥S := hSp.isNilpotent
  have hlt' : B.subgroupOf S < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => hAB fun a ha => ?_
    have : (⟨a, hAS ha⟩ : ↥S) ∈ B.subgroupOf S := by rw [h]; trivial
    exact this
  obtain ⟨g, hg, hgB⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt')
  have hgN : (g : X) ∈ Subgroup.normalizer (B : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact (Subgroup.mem_normalizer_iff.1 hg ⟨y, hBS hy⟩).1 hy
    · intro hy
      have hyS : y ∈ S := by
        have h1 : (g : X)⁻¹ * ((g : X) * y * (g : X)⁻¹) * (g : X) ∈ S :=
          S.mul_mem (S.mul_mem (S.inv_mem g.2) (hBS hy)) g.2
        simpa [mul_assoc] using h1
      exact (Subgroup.mem_normalizer_iff.1 hg ⟨y, hyS⟩).2 hy
  have hmul : (g : X) ∈ (↑(A ⊔ B) : Set X) := g.2
  rw [Subgroup.coe_mul_of_right_le_normalizer_left A B hBA] at hmul
  obtain ⟨a, ha, b, hb, hab⟩ := hmul
  have hae : a = (g : X) * b⁻¹ := by rw [← hab]; group
  refine ⟨a, ha, ?_, ?_⟩
  · rw [hae]
    exact Subgroup.mul_mem _ hgN (Subgroup.le_normalizer (B.inv_mem hb))
  · intro haB
    apply hgB
    have : (g : X) ∈ B := by rw [← hab]; exact B.mul_mem haB hb
    exact this

theorem i116e_exists_mulAut {X : Type*} [Group X] {p : ℕ} {L : Subgroup X} {b : X}
    (hb : b ∈ Subgroup.normalizer (L : Set X)) (hbp : b ^ p = 1) :
    ∃ φ : MulAut ↥L, (∀ y : ↥L, ((φ y : ↥L) : X) = b * y * b⁻¹) ∧
      IsPGroup p ↥(Subgroup.zpowers φ) := by
  let φ : MulAut ↥L :=
    { toFun := fun y => ⟨b * y * b⁻¹, (Subgroup.mem_normalizer_iff.1 hb y).1 y.2⟩
      invFun := fun y => ⟨b⁻¹ * y * b, (Subgroup.mem_normalizer_iff''.1 hb y).1 y.2⟩
      left_inv := fun y => Subtype.ext (by simp [mul_assoc])
      right_inv := fun y => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun y z => Subtype.ext (by simp [mul_assoc]) }
  have hφ : ∀ y : ↥L, ((φ y : ↥L) : X) = b * y * b⁻¹ := fun y => rfl
  have hpow : ∀ (n : ℕ) (y : ↥L), (((φ ^ n) y : ↥L) : X) = b ^ n * y * (b ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [pow_succ, MulAut.mul_apply, ih, hφ]
      simp only [pow_succ]
      group
  have hφp : φ ^ p = 1 := by
    ext y
    rw [hpow, hbp]
    simp
  refine ⟨φ, hφ, ?_⟩
  intro g
  obtain ⟨k, hk⟩ := g.2
  refine ⟨1, ?_⟩
  apply Subtype.ext
  rw [pow_one]
  have hk' : (g : MulAut ↥L) = φ ^ k := hk.symm
  change ((g : MulAut ↥L)) ^ p = 1
  rw [hk', ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hφp, one_zpow]

theorem i116e_isElemAbelian_map {G H : Type*} [Group G] [Group H] {p : ℕ} {E : Subgroup G}
    (hE : IsElemAbelian p E) (f : G →* H) : IsElemAbelian p (E.map f) :=
  CFSG.Open.IsElemAbelian.map hE _

theorem i116e_conj_mem_of_unique {X : Type*} [Group X] {p : ℕ} {L R : Subgroup X} {b : X}
    (hb : b ∈ Subgroup.normalizer (L : Set X)) (hbp : b ^ p = 1)
    (hbR : b ∈ Subgroup.normalizer (R : Set X)) {E : Subgroup ↥L} (hE : IsElemAbelian p E)
    (hER : E ≤ R.subgroupOf L)
    (huniq : ∀ E' : Subgroup ↥L, E' ≤ R.subgroupOf L → IsElemAbelian p E' →
      Nat.card E' = Nat.card E → E' = E) :
    ∀ e ∈ E, ∃ e' ∈ E, ((e' : ↥L) : X) = b * e * b⁻¹ := by
  obtain ⟨φ, hφ, -⟩ := i116e_exists_mulAut hb hbp
  have hEq : E.map φ.toMonoidHom = E := by
    apply huniq
    · rintro _ ⟨y, hy, rfl⟩
      have hyR : (y : X) ∈ R := hER hy
      show ((φ y : ↥L) : X) ∈ R
      rw [hφ]
      exact (Subgroup.mem_normalizer_iff.1 hbR _).1 hyR
    · exact i116e_isElemAbelian_map hE _
    · exact Subgroup.card_map_of_injective φ.injective
  intro e he
  have : φ e ∈ E.map φ.toMonoidHom := ⟨e, he, rfl⟩
  rw [hEq] at this
  exact ⟨φ e, this, hφ e⟩

theorem i116e_isPGroup_center {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hO : GLAPPrimeCore p X = ⊥) {L : Subgroup X} (hL : GLAPComponent p ⊤ L) :
    IsPGroup p ↥(Subgroup.center ↥L) := by
  have h := i112_isPGroup_inf_centralizer hp hO hL.2.1
  intro z
  have hzm : ((z : ↥L) : X) ∈ L ⊓ Subgroup.centralizer (L : Set X) := by
    refine ⟨(z : ↥L).2, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro l hl
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 z.2 ⟨l, hl⟩)
  obtain ⟨n, hn⟩ := h ⟨_, hzm⟩
  exact ⟨n, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hn))⟩

theorem i116e_stepT {X : Type} [Group X] [Finite X] (hT : KernelT) (hX : CFSG.Open.IsKGroup X)
    {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) {B L : Subgroup X} (hB : IsSCp p ⊤ B)
    (hLq : CFSG.Open.IsQuasisimple ↥L) (hBL : B ≤ Subgroup.normalizer (L : Set X))
    (hZp : IsPGroup p ↥(Subgroup.center ↥L))
    (hZ : ∃ U : Subgroup ↥L, U ≤ Subgroup.center ↥L ∧ IsElemAbelian p U ∧ Nat.card U = p ^ 2) :
    ∃ x ∈ L, x ∈ Subgroup.normalizer (B : Set X) ∧ (∃ n : ℕ, x ^ (p ^ n) = 1) ∧
      ∃ l ∈ L, x * l ≠ l * x := by
  have : Fact p.Prime := ⟨hp⟩
  have hact : ∀ b ∈ B, ∃ j ∈ L, ∀ l ∈ L, b * l * b⁻¹ = j * l * j⁻¹ := by
    intro b hb
    obtain ⟨φ, hφ, hφp⟩ := i116e_exists_mulAut (p := p) (hBL hb) (hB.2.1.2 b hb)
    obtain ⟨g, hg⟩ := hT ↥L hLq (isKGroup_subgroup' hX L) p hp hodd hZ φ hφp
    refine ⟨g, g.2, fun l hl => ?_⟩
    have h1 := congrArg Subtype.val (hg ⟨l, hl⟩)
    rw [hφ] at h1
    exact h1
  rcases i116t_alt hB hBL hact hZp with h | h
  · exact h
  · obtain ⟨U, -, -, hUcard⟩ := hZ
    have hdvd : p ∣ Nat.card ↥L := by
      refine dvd_trans ?_ (Subgroup.card_subgroup_dvd_card U)
      rw [hUcard]; exact dvd_pow_self p two_ne_zero
    obtain ⟨x', hx'Q, hx'nc⟩ :=
      i116t_exists_noncentral_pElt hLq hp (Classical.arbitrary (Sylow p ↥L)) hdvd
    refine ⟨(x' : X), x'.2, ?_, ?_, ?_⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro y
      have hc : ∀ b ∈ B, (x' : X) * b * (x' : X)⁻¹ = b := fun b hb => by
        rw [mul_inv_eq_iff_eq_mul]; exact (h b hb x' x'.2).symm
      have hc' : ∀ b ∈ B, (x' : X)⁻¹ * b * (x' : X) = b := fun b hb => by
        calc (x' : X)⁻¹ * b * (x' : X)
            = (x' : X)⁻¹ * ((x' : X) * b * (x' : X)⁻¹) * (x' : X) := by rw [hc b hb]
          _ = b := by group
      refine ⟨fun hy => by rw [hc y hy]; exact hy, fun hy => ?_⟩
      have h1 := hc' _ hy
      have e : (x' : X)⁻¹ * ((x' : X) * y * (x' : X)⁻¹) * (x' : X) = y := by group
      rw [e] at h1
      rw [h1]
      exact hy
    · obtain ⟨n, hn⟩ := (Classical.arbitrary (Sylow p ↥L)).isPGroup' ⟨x', hx'Q⟩
      exact ⟨n, congrArg Subtype.val (congrArg Subtype.val hn)⟩
    · by_contra hcon
      push Not at hcon
      apply hx'nc
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hcon y y.2).symm

theorem exists_noncentral_normalizing_elt (hT : KernelT) {X : Type} [Group X] [Finite X]
    (hX : CFSG.Open.IsKGroup X) {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hO : GLAPPrimeCore p X = ⊥)
    {B : Subgroup X} (hB : IsSCp p ⊤ B) {L : Subgroup X} (hL : GLAPComponent p ⊤ L)
    (hBL : B ≤ Subgroup.normalizer (L : Set X)) :
    ∃ x ∈ L, x ∈ Subgroup.normalizer (B : Set X) ∧ (∃ n : ℕ, x ^ (p ^ n) = 1) ∧
      ∃ l ∈ L, x * l ≠ l * x := by
  have : Fact p.Prime := ⟨hp⟩
  have hLq : CFSG.Open.IsQuasisimple ↥L := i116e_isQuasisimple hO hL
  have hdvd : p ∣ Nat.card L := i116e_dvd_card hp hO hL
  have hBp : IsPGroup p B := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hB.2.1.2 g.1 g.2)⟩
  obtain ⟨P, R, hPp, hBP, hRsyl, hRP, hPR⟩ := i116e_exists_sylow hBp hBL
  have hRL : R ≤ L := hRsyl.le
  have hRne : R ≠ ⊥ := by
    intro h
    have hcard := hRsyl.card_eq
    rw [h, Subgroup.card_bot] at hcard
    have hpos : 0 < (Nat.card L).factorization p :=
      hp.factorization_pos_of_dvd Nat.card_pos.ne' hdvd
    have : 1 < p ^ (Nat.card L).factorization p := Nat.one_lt_pow hpos.ne' hp.one_lt
    omega
  obtain ⟨w, hwR, hwo, hwc⟩ := i116e_exists_central hPp hRP hPR hRne
  have hwB : w ∈ B := by
    refine mem_of_mem_centralizer_orderOf_eq_prime hB ?_ hwo
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hwc b (hBP hb)
  by_cases hw : ∃ l ∈ L, w * l ≠ l * w
  · exact ⟨w, hRL hwR, Subgroup.le_normalizer hwB, ⟨1, by rw [pow_one, ← hwo]; exact pow_orderOf_eq_one w⟩, hw⟩
  push Not at hw
  have hwc' : (⟨w, hRL hwR⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hw y y.2).symm
  have hpZ : p ∣ Nat.card (Subgroup.center ↥L) := by
    have h1 : orderOf (⟨(⟨w, hRL hwR⟩ : ↥L), hwc'⟩ : ↥(Subgroup.center ↥L)) = p := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hwo]
    rw [← h1]
    exact orderOf_dvd_natCard _
  obtain ⟨Q, hQ⟩ := hRsyl.exists_sylow_eq_subgroupOf
  have hnab := (GL83.I_6_10_1_proved ↥L hLq p hp hodd hpZ Q).1
  have hRnc : ¬ IsCyclic ↥R := by
    intro hcyc
    apply hnab
    rw [hQ]
    exact inferInstance
  obtain ⟨U, hUR, hUN, hUel, hUcard⟩ := exists_normal_E2 hodd hPp hRP hPR hRnc
  have hUB : U ≤ Subgroup.normalizer (B : Set X) :=
    i116e_normalizes_of_card_sq hB hPp hBP (hUR.trans hRP) hUN hUel hUcard
  have hUL : U ≤ L := hUR.trans hRL
  by_cases hUc : ∀ u ∈ U, ∀ l ∈ L, u * l = l * u
  · refine i116e_stepT hT hX hp hodd hB hLq hBL (i116e_isPGroup_center hp hO hL)
      ⟨U.subgroupOf L, ?_, ?_, ?_⟩
    · intro u hu
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hUc u hu y y.2).symm
    · have := hUel.1
      refine ⟨inferInstance, ?_⟩
      intro x hx
      exact Subtype.ext (hUel.2 x hx)
    · rw [← hUcard]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUL).toEquiv
  · push Not at hUc
    obtain ⟨u, hu, l, hl, hul⟩ := hUc
    have hu1 : u ≠ 1 := by
      rintro rfl
      exact hul (by simp)
    exact ⟨u, hUL hu, hUB hu, ⟨1, by rw [pow_one]; exact hUel.2 u hu⟩, l, hl, hul⟩

end Basic

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
