module

public import CFSG.LocalAnalysis.EvenSmallLie.StandardForm
public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import CFSG.LieType.Chevalley.EvenF4AutomorphismNormalForm
public import CFSG.LocalAnalysis.EvenSmallLie.FFourTwo.Griess

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.FFourTwo

open Subgroup CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

structure Setup (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] where
  std : StandardSetting G L
  card_field : Nat.card K = 2
  t : G
  t_mem : t ∈ L
  t_ne_one : t ≠ 1
  mem_center_iff : ∀ l : L, l ∈ center L ↔ l = 1 ∨ (l : G) = t
  ι : L ⧸ center L ≃* adjointGroup .F4 K

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]
  (S : Setup G L K)

@[expose] def π : L →* adjointGroup .F4 K :=
  S.ι.toMonoidHom.comp (QuotientGroup.mk' (center L))

theorem π_apply (l : L) : S.π l = S.ι (l : L ⧸ center L) := rfl

theorem π_surjective : Function.Surjective S.π :=
  S.ι.surjective.comp (QuotientGroup.mk'_surjective _)

theorem π_eq_one_iff (l : L) : S.π l = 1 ↔ l ∈ center L := by
  rw [π_apply, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]

@[expose] def tL : L := ⟨S.t, S.t_mem⟩

theorem tL_mem_center : S.tL ∈ center L := (S.mem_center_iff _).2 (Or.inr rfl)

theorem tL_ne_one : S.tL ≠ 1 := fun h => S.t_ne_one (congrArg Subtype.val h)

theorem π_eq_one_iff_tL (l : L) : S.π l = 1 ↔ l = 1 ∨ l = S.tL := by
  rw [π_eq_one_iff, S.mem_center_iff]
  exact or_congr Iff.rfl ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

theorem t_mul_t : S.t * S.t = 1 := by
  have h : S.tL * S.tL ∈ center L := mul_mem S.tL_mem_center S.tL_mem_center
  rcases (S.mem_center_iff _).1 h with h | h
  · exact congrArg Subtype.val h
  · exact absurd (mul_eq_left.1 h) S.t_ne_one

theorem orderOf_t : orderOf S.t = 2 :=
  orderOf_eq_prime (by rw [sq, S.t_mul_t]) S.t_ne_one

theorem t_mem_map_center : S.t ∈ (center L).map L.subtype := ⟨S.tL, S.tL_mem_center, rfl⟩

include S in
theorem isPerfect : Group.IsPerfect L := Group.isPerfect_def.2 S.std.standard.1.1

@[expose] def cover : Cover K L where
  card := S.card_field
  π := S.π
  surj := S.π_surjective
  ker_le := fun l hl => (S.π_eq_one_iff l).1 hl
  z := S.tL
  z_ne := S.tL_ne_one
  ker_iff := S.π_eq_one_iff_tL

theorem center_facts :
    S.t ∈ centralizer (L : Set G) ∧ IsCyclic (centralizer (L : Set G)) ∧
      IsPGroup 2 (centralizer (L : Set G)) ∧
      (∀ x ∈ centralizer (L : Set G), orderOf x = 2 → x = S.t) ∧
      centralizer ({S.t} : Set G) = normalizer (L : Set G) ∧
      L ≤ centralizer ({S.t} : Set G) ∧ centralizer (L : Set G) ≤ centralizer ({S.t} : Set G) :=
  std_center_facts S.std S.orderOf_t S.t_mem_map_center

theorem le_centralizer_t : L ≤ centralizer ({S.t} : Set G) := S.center_facts.2.2.2.2.2.1

theorem centralizer_t_eq : centralizer ({S.t} : Set G) = normalizer (L : Set G) :=
  S.center_facts.2.2.2.2.1

theorem conj_mem_L {h : G} (hh : h ∈ centralizer ({S.t} : Set G)) {l : G} (hl : l ∈ L) :
    h * l * h⁻¹ ∈ L := by
  rw [S.centralizer_t_eq] at hh
  exact (mem_normalizer_iff.1 hh l).1 hl

omit [Finite G] in
theorem exists_mul_of_mem_sup {x : G} (hx : x ∈ L ⊔ centralizer (L : Set G)) :
    ∃ l ∈ L, ∃ r ∈ centralizer (L : Set G), l * r = x :=
  CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun a ha _b hb => mem_centralizer_iff.1 hb a ha) hx

theorem congr_conj {A B : Type*} [Group A] [Group B] (ι : A ≃* B) (a : A) :
    MulAut.congr ι (MulAut.conj a) = MulAut.conj (ι a) := by
  ext b
  obtain ⟨a', rfl⟩ := ι.surjective b
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulAut.conj_apply, map_mul, map_inv]

theorem exists_act : ∃ α : centralizer ({S.t} : Set G) →* MulAut (adjointGroup .F4 K),
    (∀ (h : centralizer ({S.t} : Set G)) (l l' : L), (l' : G) = h * l * (h : G)⁻¹ →
      α h (S.π l) = S.π l') ∧
    (∀ h, α h ∈ (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range ↔
      (h : G) ∈ L ⊔ centralizer (L : Set G)) := by
  obtain ⟨θ, hθ, -, hθinn⟩ := std_automizer_embedding S.std S.orderOf_t S.t_mem_map_center
  refine ⟨(MulAut.congr S.ι).toMonoidHom.comp θ, fun h l l' hl => ?_, fun h => ?_⟩
  · change S.ι (θ h (S.ι.symm (S.ι (l : L ⧸ center L)))) = S.ι (l' : L ⧸ center L)
    rw [MulEquiv.symm_apply_apply, hθ h l l' hl]
  · rw [← hθinn h]
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨S.ι.symm x, (MulAut.congr S.ι).injective ?_⟩
      change _ = MulAut.congr S.ι (θ h) at hx
      rw [congr_conj, MulEquiv.apply_symm_apply, hx]
    · rintro ⟨q, hq⟩
      exact ⟨S.ι q, by
        change MulAut.conj (S.ι q) = MulAut.congr S.ι (θ h)
        rw [hq, congr_conj]⟩

noncomputable def act : centralizer ({S.t} : Set G) →* MulAut (adjointGroup .F4 K) :=
  S.exists_act.choose

theorem act_π (h : centralizer ({S.t} : Set G)) (l : L) (hl : (h : G) * l * (h : G)⁻¹ ∈ L) :
    S.act h (S.π l) = S.π ⟨(h : G) * l * (h : G)⁻¹, hl⟩ :=
  S.exists_act.choose_spec.1 h l _ rfl

theorem act_mem_inner_iff (h : centralizer ({S.t} : Set G)) :
    S.act h ∈ (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range ↔
      (h : G) ∈ L ⊔ centralizer (L : Set G) :=
  S.exists_act.choose_spec.2 h

theorem act_of_mem (l : L) :
    S.act ⟨l, S.le_centralizer_t l.2⟩ = MulAut.conj (S.π l) := by
  ext x
  obtain ⟨m, rfl⟩ := S.π_surjective x
  rw [S.act_π _ m (mul_mem (mul_mem l.2 m.2) (inv_mem l.2)), MulAut.conj_apply]
  have : (⟨(l : G) * m * (l : G)⁻¹, mul_mem (mul_mem l.2 m.2) (inv_mem l.2)⟩ : L) =
      l * m * l⁻¹ := rfl
  rw [this, map_mul, map_mul, map_inv]

include S in
theorem finite_K : Finite K := Nat.finite_of_card_ne_zero (by rw [S.card_field]; norm_num)

include S in
theorem charP_K : CharP K 2 :=
  have := S.finite_K
  CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
    (k := 1) le_rfl (by rw [S.card_field, pow_one])

theorem exists_outer
    : ∃ Φ : centralizer ({S.t} : Set G) →* Multiplicative (ZMod 2),
    ∀ h, Φ h = 1 ↔ (h : G) ∈ L ⊔ centralizer (L : Set G) := by
  have := S.finite_K
  have := S.charP_K
  obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ := even_F4_exact_automorphism_normal_form (f := 1) le_rfl K
    (by rw [S.card_field, pow_one])
  have key : ∀ α, Θ α = 1 ↔ α ∈ (MulAut.conj : adjointGroup LieType.Ree.ReeTag.F4.tag K →*
      MulAut (adjointGroup LieType.Ree.ReeTag.F4.tag K)).range := fun α => by
    rw [← MonoidHom.mem_ker, hker]
  exact ⟨Θ.comp S.act, fun h => (key (S.act h)).trans (S.act_mem_inner_iff h)⟩

theorem relIndex_le_two :
    (L ⊔ centralizer (L : Set G)).relIndex (centralizer ({S.t} : Set G)) ≤ 2 := by
  obtain ⟨Φ, hΦ⟩ := S.exists_outer
  have he : (L ⊔ centralizer (L : Set G)).subgroupOf (centralizer ({S.t} : Set G)) = Φ.ker := by
    ext h
    rw [mem_subgroupOf, MonoidHom.mem_ker, hΦ]
  rw [relIndex, he, Subgroup.index_ker]
  calc Nat.card Φ.range ≤ Nat.card (Multiplicative (ZMod 2)) := card_le_card_group _
    _ = 2 := by rw [Nat.card_eq_fintype_card]; rfl

theorem mem_L_of_pow_three
    {h : G} (hh : h ∈ centralizer ({S.t} : Set G)) (h3 : h ^ 3 = 1) :
    h ∈ L := by
  obtain ⟨Φ, hΦ⟩ := S.exists_outer
  have h1 : Φ ⟨h, hh⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨h, hh⟩ : centralizer ({S.t} : Set G)) ^ 3 = 1 := Subtype.ext h3
    rw [this, map_one]
  have h2 : ∀ x : Multiplicative (ZMod 2), x ^ 3 = 1 → x = 1 := by decide
  obtain ⟨l, hl, r, hr, rfl⟩ := exists_mul_of_mem_sup ((hΦ _).1 (h2 _ h1))
  have hc : Commute l r := mem_centralizer_iff.1 hr l hl
  have hr3 : r ^ 3 ∈ L := by
    have e : l ^ 3 * r ^ 3 = 1 := by rw [← hc.mul_pow]; exact h3
    rw [eq_inv_of_mul_eq_one_right e]
    exact inv_mem (pow_mem hl 3)
  obtain ⟨k, hk⟩ := S.center_facts.2.2.1 ⟨r, hr⟩
  have hrk : r ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.gcd 3 (orderOf r) = 1 :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hrk)
      (Nat.Coprime.pow_right k (by norm_num))
  exact mul_mem hl ((Subgroup.zpowers_le.2 hr3) (mem_zpowers_pow_iff.2 hcop))
