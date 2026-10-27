module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29NoF
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29SL2Cent
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Pair
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.ABGLocalTools CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage12 CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Algebra

theorem exists_mul_of_mem_sup_of_commute_aux {Y : Type*} [Group Y] {A B : Subgroup Y}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : Y} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact ⟨y, hy, 1, B.one_mem, by simp⟩
    · exact ⟨1, A.one_mem, y, hy, by simp⟩
  | one => exact ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
  | mul y₁ y₂ _ _ h₁ h₂ =>
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := h₁
    obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := h₂
    refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
    have := h a₂ ha₂ b₁ hb₁
    calc a₁ * b₁ * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by group
      _ = a₁ * (a₂ * b₁) * b₂ := by rw [← this]
      _ = a₁ * a₂ * (b₁ * b₂) := by group
  | inv y _ h₁ =>
    obtain ⟨a, ha, b, hb, rfl⟩ := h₁
    refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    have := h a⁻¹ (A.inv_mem ha) b hb
    calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group
      _ = a⁻¹ * b⁻¹ := by
        have h2 : a⁻¹ * b = b * a⁻¹ := this
        calc b⁻¹ * a⁻¹ = b⁻¹ * (a⁻¹ * b) * b⁻¹ := by group
          _ = b⁻¹ * (b * a⁻¹) * b⁻¹ := by rw [h2]
          _ = a⁻¹ * b⁻¹ := by group

theorem mem_inf_of_central {H : Type*} [Group H] {A B : Subgroup H}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hA : Nat.card ↥(center ↥A) = 2)
    (hI : Nat.card ↥(A ⊓ B) = 2) {x : H} (hx : x ∈ A) (hxc : ∀ a ∈ A, x * a = a * x) :
    x ∈ A ⊓ B := by
  have hfin : Finite ↥(center ↥A) := Nat.finite_of_card_ne_zero (by rw [hA]; norm_num)
  set Z : Subgroup H := (center ↥A).map A.subtype with hZ
  have hZcard : Nat.card ↥Z = 2 := by
    rw [hZ, Subgroup.card_map_of_injective A.subtype_injective, hA]
  have hle : A ⊓ B ≤ Z := by
    intro y hy
    obtain ⟨hyA, hyB⟩ := Subgroup.mem_inf.mp hy
    refine ⟨⟨y, hyA⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro a
    exact Subtype.ext (hcomm a.1 a.2 y hyB)
  have hfZ : Finite ↥Z := Nat.finite_of_card_ne_zero (by rw [hZcard]; norm_num)
  have heq : A ⊓ B = Z := Subgroup.eq_of_le_of_card_ge hle (by rw [hZcard, hI])
  have : x ∈ Z := by
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro a
    exact Subtype.ext (hxc a.1 a.2).symm
  rwa [← heq] at this

end Algebra

section Shape

variable {G : Type} [Group G]

structure PairShape (z : G) (q₁ q₂ : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)) : Prop where
  odd₁ : Odd q₁
  odd₂ : Odd q₂
  gt₁ : 3 < q₁
  gt₂ : 3 < q₂
  ne : L₁ ≠ L₂
  prod : IsCentralProd L₁ L₂ (LBar z)
  sl₁ : HasSL2Model ↥L₁ (fun r => r = q₁)
  sl₂ : HasSL2Model ↥L₂ (fun r => r = q₂)
  comps : {K : Subgroup (CentralizerBar z) | IsComponent K} = {L₁, L₂}
  fitting : generalizedFitting (CentralizerBar z) = LBar z

variable [Finite G] {z : G} {S : Subgroup G} {q q₁ q₂ : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}

theorem PairShape.of_pair (hp : Stage1Pair G z S q L₁ L₂) : PairShape z q q L₁ L₂ :=
  ⟨hp.odd, hp.odd, hp.gt3, hp.gt3, hp.ne, hp.prod, hp.sl₁, hp.sl₂, hp.comps, hp.fitting⟩

omit [Finite G] in
theorem PairShape.isComponent₁ (hp : PairShape z q₁ q₂ L₁ L₂) : IsComponent L₁ := by
  have : L₁ ∈ {K : Subgroup (CentralizerBar z) | IsComponent K} := by rw [hp.comps]; simp
  exact this

omit [Finite G] in
theorem PairShape.isComponent₂ (hp : PairShape z q₁ q₂ L₁ L₂) : IsComponent L₂ := by
  have : L₂ ∈ {K : Subgroup (CentralizerBar z) | IsComponent K} := by rw [hp.comps]; simp
  exact this

theorem centralizer_pair_le_inf (hp : PairShape z q₁ q₂ L₁ L₂) (c : CentralizerBar z)
    (hc₁ : ∀ a ∈ L₁, c * a = a * c) (hc₂ : ∀ b ∈ L₂, c * b = b * c) : c ∈ L₁ ⊓ L₂ := by
  obtain ⟨hsup, hcomm, hcard⟩ := hp.prod
  have h4₁ : 4 ≤ q₁ := by have := hp.gt₁; omega
  have h4₂ : 4 ≤ q₂ := by have := hp.gt₂; omega
  obtain ⟨-, hZ₁, -⟩ := Stage2.Local.sl2_model_facts hp.odd₁ h4₁ hp.sl₁
  obtain ⟨-, hZ₂, -⟩ := Stage2.Local.sl2_model_facts hp.odd₂ h4₂ hp.sl₂
  have hcL : c ∈ centralizer ((LBar z : Subgroup (CentralizerBar z)) : Set (CentralizerBar z)) := by
    rw [← hsup, Subgroup.mem_centralizer_iff]
    intro x hx
    have hcc : (centralizer ({c} : Set (CentralizerBar z))) ≥ L₁ ⊔ L₂ :=
      sup_le (fun a ha => by
        rw [Subgroup.mem_centralizer_singleton_iff]; exact (hc₁ a ha).symm)
        (fun b hb => by
          rw [Subgroup.mem_centralizer_singleton_iff]; exact (hc₂ b hb).symm)
    have := hcc hx
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this
  have hcLB : c ∈ LBar z := by
    have := CFSG.centralizer_generalizedFitting_le (CentralizerBar z)
    rw [hp.fitting] at this
    exact this hcL
  rw [← hsup] at hcLB
  obtain ⟨l₁, hl₁, l₂, hl₂, hc⟩ := exists_mul_of_mem_sup_of_commute_aux hcomm hcLB
  have hl₁c : ∀ a ∈ L₁, l₁ * a = a * l₁ := by
    intro a ha
    have h1 := hc₁ a ha
    rw [hc] at h1
    have h2 := hcomm a ha l₂ hl₂
    have h3 : l₁ * a * l₂ = a * l₁ * l₂ := by
      calc l₁ * a * l₂ = l₁ * (a * l₂) := by group
        _ = l₁ * (l₂ * a) := by rw [h2]
        _ = l₁ * l₂ * a := by group
        _ = a * (l₁ * l₂) := h1
        _ = a * l₁ * l₂ := by group
    exact mul_right_cancel h3
  have hl₂c : ∀ b ∈ L₂, l₂ * b = b * l₂ := by
    intro b hb
    have h1 := hc₂ b hb
    rw [hc] at h1
    have h2 := hcomm l₁ hl₁ b hb
    have h3 : l₁ * (l₂ * b) = l₁ * (b * l₂) := by
      calc l₁ * (l₂ * b) = l₁ * l₂ * b := by group
        _ = b * (l₁ * l₂) := h1
        _ = (b * l₁) * l₂ := by group
        _ = (l₁ * b) * l₂ := by rw [← h2]
        _ = l₁ * (b * l₂) := by group
    exact mul_left_cancel h3
  have hI₁ : l₁ ∈ L₁ ⊓ L₂ := mem_inf_of_central hcomm hZ₁ hcard hl₁ hl₁c
  have hI₂ : l₂ ∈ L₂ ⊓ L₁ :=
    mem_inf_of_central (fun b hb a ha => (hcomm a ha b hb).symm) hZ₂ (by rwa [inf_comm]) hl₂ hl₂c
  rw [inf_comm] at hI₂
  rw [hc]
  exact (L₁ ⊓ L₂).mul_mem hI₁ hI₂

theorem twoNilp_centralizer_bar_of_nonswap {k : Kind} (ctx : Stage2Ctx G z k S)
    (hp : PairShape z q₁ q₂ L₁ L₂) {u : G} (huS : u ∈ S) (hu : u ∈ Cen z) (hu2 : u * u = 1)
    (hn₁ : toBar z ⟨u, hu⟩ ∈ normalizer (L₁ : Set (CentralizerBar z)))
    (hn₂ : toBar z ⟨u, hu⟩ ∈ normalizer (L₂ : Set (CentralizerBar z)))
    (ht₁ : Stage1.Main.actOnK L₁ (toBar z ⟨u, hu⟩) hn₁ ≠ 1)
    (ht₂ : Stage1.Main.actOnK L₂ (toBar z ⟨u, hu⟩) hn₂ ≠ 1) :
    TwoNilp ↥(centralizer ({toBar z ⟨u, hu⟩} : Set (CentralizerBar z))) := by
  have hsq : (⟨u, hu⟩ : ↥(Cen z)) * ⟨u, hu⟩ = 1 := Subtype.ext hu2
  have hu2' : toBar z ⟨u, hu⟩ * toBar z ⟨u, hu⟩ = 1 := by rw [← map_mul, hsq, map_one]
  have key : ∀ (L : Subgroup (CentralizerBar z)) {q : ℕ}, Odd q → 3 < q → IsComponent L →
      HasSL2Model ↥L (fun r => r = q) →
      ∀ (hn : toBar z ⟨u, hu⟩ ∈ normalizer (L : Set (CentralizerBar z))),
      Stage1.Main.actOnK L (toBar z ⟨u, hu⟩) hn ≠ 1 →
      TwoNilp ↥(centralizer ({Stage1.Main.actOnK L (toBar z ⟨u, hu⟩) hn} :
        Set (MulAut ↥L))) := by
    intro L q hodd hgt hL hsl hn ht
    obtain ⟨F, hF, hFin, hq, ⟨e⟩⟩ := hsl
    have hq' : Nat.card F = q := hq
    have hL2 : IVK.L2Field F := ⟨hq' ▸ hodd, hq' ▸ hgt⟩
    exact twoNilp_centralizer_sl2 hL2 (e.trans (specialLinearGroupEquivStatedSL 2 F).symm) _
      (actOnK_mul_self hn hu2') ht
      (not_fixedCond_actOnK ctx hodd (by omega) hL ⟨F, hF, hFin, hq, ⟨e⟩⟩ huS hu hu2 hn ht)
  exact twoNilp_centralizer_of_components L₁ L₂ hp.ne hp.comps hp.prod.2.2.le
    (fun c h₁ h₂ => centralizer_pair_le_inf hp c h₁ h₂) (toBar z ⟨u, hu⟩) hn₁ hn₂
    (key L₁ hp.odd₁ hp.gt₁ hp.isComponent₁ hp.sl₁ hn₁ ht₁)
    (key L₂ hp.odd₂ hp.gt₂ hp.isComponent₂ hp.sl₂ hn₂ ht₂)

end Shape

section Lift

variable {G : Type} [Group G] [Finite G] {z : G}

theorem twoNilp_centralizer_of_bar {U : Subgroup G} {u : G} (hzU : z ∈ U) (huU : u ∈ U)
    (hu : u ∈ Cen z)
    (h : TwoNilp ↥(centralizer ({toBar z ⟨u, hu⟩} : Set (CentralizerBar z)))) :
    TwoNilp ↥(centralizer (U : Set G)) := by
  have hle : centralizer (U : Set G) ≤ Cen z := by
    intro g hg
    show g ∈ centralizer ({z} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hg z hzU).symm
  let f0 : ↥(centralizer (U : Set G)) →* CentralizerBar z :=
    (toBar z).comp (Subgroup.inclusion hle)
  have hrange : ∀ g : ↥(centralizer (U : Set G)),
      f0 g ∈ centralizer ({toBar z ⟨u, hu⟩} : Set (CentralizerBar z)) := by
    intro g
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hgu : (g : G) * u = u * g := (Subgroup.mem_centralizer_iff.mp g.2 u huU).symm
    show toBar z (Subgroup.inclusion hle g) * toBar z ⟨u, hu⟩ =
      toBar z ⟨u, hu⟩ * toBar z (Subgroup.inclusion hle g)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hgu
  let f : ↥(centralizer (U : Set G)) →*
      ↥(centralizer ({toBar z ⟨u, hu⟩} : Set (CentralizerBar z))) :=
    f0.codRestrict _ hrange
  have hker : f.ker = f0.ker := by
    ext g
    simp [f, MonoidHom.mem_ker]
  have hodd : Odd (Nat.card f.ker) := by
    rw [hker]
    let φ : ↥f0.ker →* ↥(toBar z).ker :=
      ((Subgroup.inclusion hle).comp f0.ker.subtype).codRestrict (toBar z).ker fun g => g.2
    have hinj : Function.Injective φ := by
      intro a b hab
      apply Subtype.ext
      apply Subgroup.inclusion_injective hle
      exact congrArg (fun t : ↥(toBar z).ker => (t : ↥(Cen z))) hab
    have hdvd : Nat.card f0.ker ∣ Nat.card (toBar z).ker :=
      Subgroup.card_dvd_of_injective φ hinj
    have hodd0 : Odd (Nat.card (toBar z).ker) := by
      rw [show (toBar z).ker = pPrimeCore 2 ↥(Cen z) from QuotientGroup.ker_mk' _]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    exact Odd.of_dvd_nat hodd0 hdvd
  exact twoNilp_of_odd_ker f hodd h

end Lift

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
