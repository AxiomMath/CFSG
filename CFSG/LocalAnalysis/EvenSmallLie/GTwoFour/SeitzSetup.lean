module

public import CFSG.LocalAnalysis.EvenSmallLie.GTwoFour.SeitzHelpers
public import CFSG.LocalAnalysis.EvenSmallLie.GTwoFour.Centralizers
public import CFSG.LocalAnalysis.EvenSmallLie.StandardForm
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Open.QuasithinDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.GTwoFour

open Subgroup CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open scoped commutatorElement

structure SeitzSetup (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] where
  standard : standardComponentIsStandard L
  cyclic : ∃ S : Sylow 2 (centralizer (L : Set G)),
    IsCyclic (S : Subgroup (centralizer (L : Set G)))
  card_field : Nat.card K = 4
  t : G
  t_mem : t ∈ L
  t_ne_one : t ≠ 1
  mem_center_iff : ∀ l : L, l ∈ center L ↔ l = 1 ∨ (l : G) = t
  ι : L ⧸ center L ≃* adjointGroup .G2 K

namespace SeitzSetup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]
  (S : SeitzSetup G L K)

@[expose] def π : L →* adjointGroup .G2 K :=
  S.ι.toMonoidHom.comp (QuotientGroup.mk' (center L))

theorem π_apply (l : L) : S.π l = S.ι (l : L ⧸ center L) := rfl

theorem π_surjective : Function.Surjective S.π :=
  S.ι.surjective.comp (QuotientGroup.mk'_surjective _)

theorem π_eq_one_iff (l : L) : S.π l = 1 ↔ l ∈ center L := by
  rw [π_apply, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]

theorem π_eq_one_iff' (l : L) : S.π l = 1 ↔ l = 1 ∨ (l : G) = S.t := by
  rw [π_eq_one_iff, S.mem_center_iff]

@[expose] def tL : L := ⟨S.t, S.t_mem⟩

theorem tL_mem_center : S.tL ∈ center L := (S.mem_center_iff _).2 (Or.inr rfl)

theorem tL_ne_one : S.tL ≠ 1 := fun h => S.t_ne_one (congrArg Subtype.val h)

theorem π_eq_one_iff_tL (l : L) : S.π l = 1 ↔ l = 1 ∨ l = S.tL := by
  rw [π_eq_one_iff']
  exact or_congr Iff.rfl ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

theorem ker_le_center : ∀ l, S.π l = 1 → l ∈ center L := fun l h => (S.π_eq_one_iff l).1 h

theorem t_mul_t : S.t * S.t = 1 := by
  have h : S.tL * S.tL ∈ center L := mul_mem S.tL_mem_center S.tL_mem_center
  rcases (S.mem_center_iff _).1 h with h | h
  · exact congrArg Subtype.val h
  · exact absurd (mul_eq_left.1 h) S.t_ne_one

theorem orderOf_t : orderOf S.t = 2 :=
  orderOf_eq_prime (by rw [sq, S.t_mul_t]) S.t_ne_one

theorem t_mem_map_center : S.t ∈ (center L).map L.subtype := ⟨S.tL, S.tL_mem_center, rfl⟩

include S in
theorem commutator_eq_top : commutator L = ⊤ := S.standard.1.1

include S in
theorem isPerfect : Group.IsPerfect L := Group.isPerfect_def.2 S.commutator_eq_top

theorem center_facts :
    S.t ∈ centralizer (L : Set G) ∧
      (∀ x ∈ centralizer (L : Set G), orderOf x = 2 → x = S.t) ∧
      centralizer ({S.t} : Set G) = normalizer (L : Set G) ∧
      L ≤ centralizer ({S.t} : Set G) ∧ centralizer (L : Set G) ≤ centralizer ({S.t} : Set G) :=
  seitz_center_facts S.standard S.cyclic S.orderOf_t S.t_mem_map_center

theorem le_centralizer_t : L ≤ centralizer ({S.t} : Set G) := S.center_facts.2.2.2.1

theorem centralizer_t_eq : centralizer ({S.t} : Set G) = normalizer (L : Set G) :=
  S.center_facts.2.2.1

theorem eq_one_or_eq_t {k : G} (hk : k ∈ centralizer (L : Set G)) (hk2 : k * k = 1) :
    k = 1 ∨ k = S.t := by
  by_cases h1 : k = 1
  · exact Or.inl h1
  · exact Or.inr (S.center_facts.2.1 k hk (orderOf_eq_prime (by rw [sq, hk2]) h1))

theorem conj_mem_L {h : G} (hh : h ∈ centralizer ({S.t} : Set G)) {l : G} (hl : l ∈ L) :
    h * l * h⁻¹ ∈ L := by
  rw [S.centralizer_t_eq] at hh
  exact (mem_normalizer_iff.1 hh l).1 hl

theorem conj_mem_R {h : G} (hh : h ∈ centralizer ({S.t} : Set G)) {r : G}
    (hr : r ∈ centralizer (L : Set G)) : h * r * h⁻¹ ∈ centralizer (L : Set G) := by
  rw [S.centralizer_t_eq] at hh
  exact conj_mem_centralizer_of_mem_normalizer hh hr

theorem exists_act : ∃ α : centralizer ({S.t} : Set G) →* MulAut (adjointGroup .G2 K),
    (∀ (h : centralizer ({S.t} : Set G)) (l l' : L), (l' : G) = h * l * (h : G)⁻¹ →
      α h (S.π l) = S.π l') ∧
    (∀ h, α h = 1 ↔ (h : G) ∈ centralizer (L : Set G)) ∧
    (∀ h, α h ∈ inner (adjointGroup .G2 K) ↔ (h : G) ∈ L ⊔ centralizer (L : Set G)) := by
  obtain ⟨θ, hθ, hθ1, hθinn⟩ :=
    std_automizer_embedding_of_standard S.standard S.orderOf_t S.t_mem_map_center
  refine ⟨(MulAut.congr S.ι).toMonoidHom.comp θ, fun h l l' hl => ?_, fun h => ?_, fun h => ?_⟩
  · change S.ι (θ h (S.ι.symm (S.ι (l : L ⧸ center L)))) = S.ι (l' : L ⧸ center L)
    rw [MulEquiv.symm_apply_apply, hθ h l l' hl]
  · change MulAut.congr S.ι (θ h) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, hθ1]
  · rw [← hθinn h]
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨S.ι.symm x, (MulAut.congr S.ι).injective ?_⟩
      change _ = MulAut.congr S.ι (θ h) at hx
      rw [Setup.congr_conj, MulEquiv.apply_symm_apply, hx]
    · rintro ⟨q, hq⟩
      exact ⟨S.ι q, by
        change MulAut.conj (S.ι q) = MulAut.congr S.ι (θ h)
        rw [hq, Setup.congr_conj]⟩

noncomputable def act : centralizer ({S.t} : Set G) →* MulAut (adjointGroup .G2 K) :=
  S.exists_act.choose

theorem act_π (h : centralizer ({S.t} : Set G)) (l : L) (hl : (h : G) * l * (h : G)⁻¹ ∈ L) :
    S.act h (S.π l) = S.π ⟨(h : G) * l * (h : G)⁻¹, hl⟩ :=
  S.exists_act.choose_spec.1 h l _ rfl

theorem act_eq_one_iff (h : centralizer ({S.t} : Set G)) :
    S.act h = 1 ↔ (h : G) ∈ centralizer (L : Set G) :=
  S.exists_act.choose_spec.2.1 h

theorem act_mem_inner_iff (h : centralizer ({S.t} : Set G)) :
    S.act h ∈ inner (adjointGroup .G2 K) ↔ (h : G) ∈ L ⊔ centralizer (L : Set G) :=
  S.exists_act.choose_spec.2.2 h

theorem act_of_mem (l : L) :
    S.act ⟨l, S.le_centralizer_t l.2⟩ = MulAut.conj (S.π l) := by
  ext x
  obtain ⟨m, rfl⟩ := S.π_surjective x
  rw [S.act_π _ m (mul_mem (mul_mem l.2 m.2) (inv_mem l.2)), MulAut.conj_apply]
  have : (⟨(l : G) * m * (l : G)⁻¹, mul_mem (mul_mem l.2 m.2) (inv_mem l.2)⟩ : L) =
      l * m * l⁻¹ := rfl
  rw [this, map_mul, map_mul, map_inv]

include S in
theorem ringEquiv_mul_comm (σ τ : K ≃+* K) : σ * τ = τ * σ := by
  have h1 := ringEquiv_mul_self S.card_field σ
  have h2 := ringEquiv_mul_self S.card_field τ
  have h3 := ringEquiv_mul_self S.card_field (σ * τ)
  have hσ : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right h1
  have hτ : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right h2
  have h4 : (σ * τ)⁻¹ = σ * τ := inv_eq_of_mul_eq_one_right h3
  rw [mul_inv_rev, hσ, hτ] at h4
  exact h4.symm

theorem le_sup_of_perfect
    {P : Subgroup G} (hP : P ≤ centralizer ({S.t} : Set G))
    (hperf : ⁅P, P⁆ = P) : P ≤ L ⊔ centralizer (L : Set G) := by
  obtain ⟨-, Θ, -, -, hker, -⟩ := even_G2_exact_automorphism_normal_form (f := 2) le_rfl K
    (by rw [S.card_field]; norm_num)
  set Ψ := Θ.comp S.act with hΨ
  intro x hx
  have hxP : x ∈ ⁅P, P⁆ := hperf.symm ▸ hx
  have hle : ⁅P, P⁆ ≤ (Ψ.ker).map (centralizer ({S.t} : Set G)).subtype := by
    rw [commutator_le]
    intro a ha b hb
    refine ⟨⁅(⟨a, hP ha⟩ : centralizer ({S.t} : Set G)), ⟨b, hP hb⟩⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def,
      ringEquiv_mul_comm S (Ψ _) (Ψ _), mul_inv_cancel_right, mul_inv_cancel]
  obtain ⟨h, hh, rfl⟩ := hle hxP
  rw [SetLike.mem_coe, MonoidHom.mem_ker, hΨ, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
    hker] at hh
  exact (S.act_mem_inner_iff h).1 hh

theorem mem_L_of_perfect
    {P : Subgroup G} (hP : P ≤ centralizer ({S.t} : Set G)) (hperf : ⁅P, P⁆ = P) {u : G}
    (hu : u ∈ P) {m : ℕ} (hum : u ^ (2 ^ m) = 1) : u ∈ L := by
  obtain ⟨R, hR⟩ := S.cyclic
  set N := (CFSG.pPrimeCore 2 (centralizer (L : Set G))).map
    (centralizer (L : Set G)).subtype with hN
  have hKK : ⁅centralizer (L : Set G), centralizer (L : Set G)⁆ ≤ N := by
    rw [commutator_le]
    intro a ha b hb
    exact ⟨⁅(⟨a, ha⟩ : centralizer (L : Set G)), ⟨b, hb⟩⁆, seitz_commutator_le_pPrimeCore R hR
      (commutator_mem_commutator (mem_top _) (mem_top _)), rfl⟩
  have hNC : N ≤ centralizer (L : Set G) := by
    rintro _ ⟨k, -, rfl⟩
    exact k.2
  have hPLC := S.le_sup_of_perfect hP hperf
  have hPN : P ≤ L ⊔ N := by
    rw [← hperf]
    exact (commutator_mono hPLC hPLC).trans (seitz_commutator_sup_le_sup le_rfl hKK)
  have hNodd : Odd (Nat.card N) := by
    rw [hN, card_map_of_injective (centralizer (L : Set G)).subtype_injective]
    exact (CFSG.cyclic_sylow_normal_odd_complement R hR).2.2.2.1.2.1
  have hLN : L ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxL, hxN⟩
    have hxZ : (⟨x, hxL⟩ : L) ∈ center L :=
      Subgroup.mem_center_iff.2 fun l => Subtype.ext (mem_centralizer_iff.1 (hNC hxN) l l.2)
    rcases (S.mem_center_iff _).1 hxZ with h | h
    · exact mem_bot.2 (congrArg Subtype.val h)
    · exfalso
      have h2 : 2 ∣ Nat.card N := by
        have := Subgroup.orderOf_dvd_natCard N hxN
        rwa [show x = S.t from h, S.orderOf_t] at this
      exact hNodd.not_two_dvd_nat h2
  exact seitz_mem_of_mem_sup_odd hNC hNodd hLN hum (hPN hu)

end SeitzSetup

end CFSG.EvenSmallLie.GTwoFour
