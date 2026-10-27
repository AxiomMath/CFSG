module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.SylowProduct
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

public section

namespace CFSG.GroupTheory

open MulAction

class NormalizesSet {G : Type*} [Group G] (A : Subgroup G) (D : Set G) : Prop where
  conj_mem : ∀ a : G, a ∈ A → ∀ x : G, x ∈ D → a * x * a⁻¹ ∈ D

@[expose, instance_reducible]
def conjMulActionOfNormalizesSet {G : Type*} [Group G] (A : Subgroup G) (D : Set G)
    (h : NormalizesSet A D) : MulAction ↥A ↥D where
  smul a x := ⟨(a : G) * (x : G) * (a : G)⁻¹,
    h.conj_mem (a : G) a.2 (x : G) x.2⟩
  one_smul x := by
    apply Subtype.ext
    change (1 : G) * (x : G) * (1 : G)⁻¹ = (x : G)
    simp
  mul_smul a b x := by
    apply Subtype.ext
    change ((a : G) * (b : G)) * (x : G) * ((a : G) * (b : G))⁻¹ =
      (a : G) * ((b : G) * (x : G) * (b : G)⁻¹) * (a : G)⁻¹
    group

@[instance_reducible]
instance instMulActionNormalizesSet {G : Type*} [Group G] {A : Subgroup G} {D : Set G}
    [h : NormalizesSet A D] : MulAction ↥A ↥D :=
  conjMulActionOfNormalizesSet A D h

@[simp] theorem conjMulActionOfNormalizesSet_smul_coe {G : Type*} [Group G] {A : Subgroup G}
    {D : Set G} [h : NormalizesSet A D] (a : ↥A) (x : ↥D) :
    ((a • x : ↥D) : G) = (a : G) * (x : G) * (a : G)⁻¹ := rfl

theorem stabilizer_normalizesSet {G : Type*} [Group G] {A : Subgroup G} {D : Set G}
    [h : NormalizesSet A D] (x : ↥D) :
    MulAction.stabilizer (↥A) x =
      (Subgroup.centralizer ({(x : G)} : Set G)).subgroupOf A := by
  ext a
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hh
    have h' : (a : G) * (x : G) * (a : G)⁻¹ = (x : G) := by
      simpa using congrArg Subtype.val hh
    calc (a : G) * (x : G) = ((a : G) * (x : G) * (a : G)⁻¹) * (a : G) := by group
      _ = (x : G) * (a : G) := by rw [h']
  · intro hh
    apply Subtype.ext
    change (a : G) * (x : G) * (a : G)⁻¹ = (x : G)
    rw [hh]
    group

@[expose, instance_reducible]
def conjMulActionOfTop {G : Type*} [Group G] (D : Set G) (h : NormalizesSet ⊤ D) :
    MulAction G ↥D :=
  letI : MulAction ↥(⊤ : Subgroup G) ↥D :=
    conjMulActionOfNormalizesSet (⊤ : Subgroup G) D h
  MulAction.compHom ↥D ((Subgroup.topEquiv (G := G)).symm : G →* ↥(⊤ : Subgroup G))

@[simp] theorem conjMulActionOfTop_smul_coe {G : Type*} [Group G] (D : Set G)
    (h : NormalizesSet ⊤ D) (g : G) (x : ↥D) :
    (((conjMulActionOfTop D h).smul g x : ↥D) : G) = g * (x : G) * g⁻¹ := rfl

@[instance_reducible]
instance instMulActionConjOfNormalizesTop {G : Type*} [Group G] (D : Set G)
    [h : NormalizesSet ⊤ D] : MulAction G ↥D :=
  conjMulActionOfTop D h

theorem stabilizer_conjMulActionOfTop {G : Type*} [Group G] {D : Set G}
    [h : NormalizesSet ⊤ D] (x : ↥D) :
    MulAction.stabilizer G x = Subgroup.centralizer ({(x : G)} : Set G) := by
  ext g
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hh
    have hh' : (conjMulActionOfTop D h).smul g x = x := hh
    have h' : g * (x : G) * g⁻¹ = (x : G) := by
      simpa using congrArg Subtype.val hh'
    calc g * (x : G) = (g * (x : G) * g⁻¹) * g := by group
      _ = (x : G) * g := by rw [h']
  · intro hh
    apply Subtype.ext
    change g * (x : G) * g⁻¹ = (x : G)
    rw [hh]
    group

theorem isPretransitive_of_forall_conj {G : Type*} [Group G] {N : Subgroup G} {E : Set G}
    [hN : NormalizesSet N E]
    (h : ∀ e f : ↥E, ∃ n ∈ N, n * (e : G) * n⁻¹ = (f : G)) :
    IsPretransitive ↥N ↥E := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨n, hn, hnx⟩ := h x y
  exact ⟨⟨n, hn⟩, by apply Subtype.ext; simpa using hnx⟩

theorem card_orbit_subgroupOf_mul_card_centralizer {G : Type*} [Group G] [Finite G]
    {A : Subgroup G} {D : Set G} [h : NormalizesSet A D] {S : Subgroup G} (hSA : S ≤ A)
    (x : ↥D) :
    Nat.card (MulAction.orbit (↥(S.subgroupOf A)) x) *
      Nat.card (↥(Subgroup.centralizer ({(x : G)} : Set G) ⊓ S)) = Nat.card S := by
  classical
  let C : Subgroup G := Subgroup.centralizer ({(x : G)} : Set G)
  let P : Subgroup ↥A := S.subgroupOf A
  have hPcard : Nat.card P = Nat.card S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSA).toEquiv
  have hstab : MulAction.stabilizer (↥A) x = C.subgroupOf A :=
    stabilizer_normalizesSet x
  have hInf : (MulAction.stabilizer (↥A) x ⊓ P : Subgroup ↥A) = (C ⊓ S).subgroupOf A := by
    rw [hstab]
    ext y
    simp [P, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  have hInfCard : Nat.card (MulAction.stabilizer (↥A) x ⊓ P : Subgroup ↥A) =
      Nat.card (C ⊓ S : Subgroup G) := by
    rw [hInf]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_right.trans hSA)).toEquiv
  have h := CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.card_orbit_mul_card_stabilizer_inf
    (H := ↥A) (P := P) x
  rw [hInfCard, hPcard] at h
  exact h

theorem card_orbit_sylow_mul_card_centralizer {G : Type*} [Group G] [Finite G] (D : Set G)
    [hD : NormalizesSet ⊤ D] (S : Sylow 2 G) (x : ↥D) :
    Nat.card (MulAction.orbit (↥S) x) *
      Nat.card (↥(Subgroup.centralizer ({(x : G)} : Set G) ⊓ S)) = Nat.card S := by
  have h := CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.card_orbit_mul_card_stabilizer_inf
    (H := G) (P := (S : Subgroup G)) x
  rw [stabilizer_conjMulActionOfTop x] at h
  exact h

theorem pow_padicValNat_dvd_card_orbit_of_sylow {N X : Type*} [Group N] [MulAction N X]
    [Finite N] [Finite X] [IsPretransitive N X] {p : ℕ} [Fact p.Prime] (P : Sylow p N)
    (x : X) :
    p ^ padicValNat p (Nat.card X) ∣ Nat.card (MulAction.orbit (↥P) x) := by
  classical
  have hT : ∀ ω : X,
      Nat.card X * Nat.card (MulAction.stabilizer N ω ⊓ ⊤ : Subgroup N) =
        Nat.card (⊤ : Subgroup N) := by
    intro ω
    rw [inf_top_eq, mul_comm, ← MulAction.index_stabilizer_of_transitive (G := N) ω]
    have htop : Nat.card (⊤ : Subgroup N) = Nat.card N :=
      Nat.card_congr Subgroup.topEquiv.toEquiv
    rw [htop]
    exact Subgroup.card_mul_index (MulAction.stabilizer N ω)
  have hPc : ∃ c : ℕ, Nat.card ↥(P : Subgroup N) = p ^ c :=
    P.isPGroup'.exists_card_eq
  have hP : ∀ m : ℕ, p ^ m ∣ Nat.card (⊤ : Subgroup N) →
      p ^ m ∣ Nat.card ↥(P : Subgroup N) := by
    intro m hm
    exact Sylow.pow_dvd_card_of_pow_dvd_card P (by simpa using hm)
  exact CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.pow_dvd_card_orbit_of_le
    (H := N) (Ω := X) (T := ⊤) (P := (P : Subgroup N)) le_top hT hPc hP
    (padicValNat p (Nat.card X)) pow_padicValNat_dvd x

theorem exists_orbit_card_eq_pow_padicValNat_of_sylow {N X : Type*} [Group N] [MulAction N X]
    [Finite N] [Finite X] [IsPretransitive N X] [Nonempty X] {p : ℕ} [Fact p.Prime]
    (P : Sylow p N) :
    ∃ x : X, Nat.card (MulAction.orbit (↥P) x) = p ^ padicValNat p (Nat.card X) := by
  classical
  have hX0 : Nat.card X ≠ 0 := Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩
  exact CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.exists_orbit_card_eq_of_not_dvd
    (K := ↥P) (Ω := X) (p := p) P.isPGroup' (padicValNat p (Nat.card X))
    (fun x => pow_padicValNat_dvd_card_orbit_of_sylow P x)
    (pow_succ_padicValNat_not_dvd hX0)

theorem pow_padicValNat_dvd_card_orbit_of_sylow_of_pretransitive {N X : Type*} [Group N]
    [MulAction N X] [Finite N] [Finite X] (hpre : IsPretransitive N X) {p : ℕ} [Fact p.Prime]
    (P : Sylow p N) (x : X) :
    p ^ padicValNat p (Nat.card X) ∣ Nat.card (MulAction.orbit (↥P) x) :=
  @pow_padicValNat_dvd_card_orbit_of_sylow N X _ _ _ _ hpre p _ P x

theorem exists_orbit_card_eq_pow_padicValNat_of_sylow_of_pretransitive {N X : Type*} [Group N]
    [MulAction N X] [Finite N] [Finite X] (hpre : IsPretransitive N X) (hne : Nonempty X)
    {p : ℕ} [Fact p.Prime] (P : Sylow p N) :
    ∃ x : X, Nat.card (MulAction.orbit (↥P) x) = p ^ padicValNat p (Nat.card X) :=
  @exists_orbit_card_eq_pow_padicValNat_of_sylow N X _ _ _ _ hpre hne p _ P

end CFSG.GroupTheory
