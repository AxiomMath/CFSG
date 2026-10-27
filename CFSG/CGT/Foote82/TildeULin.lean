module

public import CFSG.CGT.Foote82.BlockBasics
public import CFSG.CGT.Foote82.Setup
import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks
import CFSG.LocalAnalysis.ComponentClassification.Asc76S5Basic
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.RankThree.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure TildeULin (J X : Subgroup G) (V : Type) [AddCommGroup V] [Module (ZMod 2) V] where
  π : ↥(blockU J) →* Multiplicative V
  surj : Function.Surjective π
  ker_eq : π.ker = (blockZ J).subgroupOf (blockU J)
  normalizes : X ≤ Subgroup.normalizer (J : Set G)
  ρ : ↥X →* GLV V
  spec : ∀ (x : ↥X) (u v : ↥(blockU J)), (v : G) = x * u * (x : G)⁻¹ →
    Multiplicative.toAdd (π v) = ρ x (Multiplicative.toAdd (π u))

theorem exists_tildeULin {H J X : Subgroup G} (hJ : IsFooteBlock H J)
    (hX : X ≤ Subgroup.normalizer (J : Set G)) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 2) V) (_ : Finite V),
      Nonempty (TildeULin J X V) := by
  classical
  have hcomm : ∀ a b : ↥(blockU J) ⧸ (blockZ J).subgroupOf (blockU J), a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with | H a =>
    induction b using QuotientGroup.induction_on with | H b =>
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have := IsFooteBlock.commutator_mem_blockZ hJ (u := ((b⁻¹ : ↥(blockU J)) : G))
      (v := ((a⁻¹ : ↥(blockU J)) : G)) (b⁻¹).2 (a⁻¹).2
    simpa [commutatorElement_def, mul_assoc] using this
  have hsq : ∀ a : ↥(blockU J) ⧸ (blockZ J).subgroupOf (blockU J), a * a = 1 := by
    intro a
    induction a using QuotientGroup.induction_on with | H a =>
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have := IsFooteBlock.sq_mem_blockZ hJ a.2
    simpa [pow_two] using this
  have hconj : ∀ (x : ↥X) (u : G), u ∈ blockU J → (x : G) * u * (x : G)⁻¹ ∈ blockU J :=
    fun x u hu =>
      (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU (hX x.2)) u).mp hu
  have hconjZ : ∀ (x : ↥X) (u : G), u ∈ blockZ J → (x : G) * u * (x : G)⁻¹ ∈ blockZ J :=
    fun x u hu =>
      (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockZ (hX x.2)) u).mp hu
  set N : Subgroup ↥(blockU J) := (blockZ J).subgroupOf (blockU J) with hN
  letI : CommGroup (↥(blockU J) ⧸ N) :=
    { (inferInstance : Group (↥(blockU J) ⧸ N)) with mul_comm := hcomm }
  have h2 : ∀ x : Additive (↥(blockU J) ⧸ N), (2 : ℕ) • x = 0 := by
    intro x
    rw [two_nsmul]
    exact congrArg Additive.ofMul (hsq (Additive.toMul x))
  letI : Module (ZMod 2) (Additive (↥(blockU J) ⧸ N)) := AddCommGroup.zmodModule h2
  let c : ↥X → (↥(blockU J) →* ↥(blockU J)) := fun x =>
    { toFun := fun u => ⟨(x : G) * u * (x : G)⁻¹, hconj x u u.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  have hc : ∀ (x : ↥X) (u : ↥(blockU J)),
      ((c x u : ↥(blockU J)) : G) = (x : G) * u * (x : G)⁻¹ := fun _ _ => rfl
  let f : ↥X → (↥(blockU J) ⧸ N →* ↥(blockU J) ⧸ N) := fun x =>
    QuotientGroup.map N N (c x) (fun u hu => by
      rw [Subgroup.mem_comap, hN, Subgroup.mem_subgroupOf, hc]
      exact hconjZ x u (Subgroup.mem_subgroupOf.mp hu))
  let a : ↥X → (Additive (↥(blockU J) ⧸ N) →+ Additive (↥(blockU J) ⧸ N)) := fun x =>
    MonoidHom.toAdditive (f x)
  have ha : ∀ (x : ↥X) (u : ↥(blockU J)),
      a x (Additive.ofMul (QuotientGroup.mk u)) = Additive.ofMul (QuotientGroup.mk (c x u)) :=
    fun _ _ => rfl
  have hsurj : ∀ v : Additive (↥(blockU J) ⧸ N), ∃ u : ↥(blockU J),
      v = Additive.ofMul (QuotientGroup.mk u) := fun v => by
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    exact ⟨u, by rw [hu]; rfl⟩
  let φ : ↥X →* Module.End (ZMod 2) (Additive (↥(blockU J) ⧸ N)) :=
    { toFun := fun x => (a x).toZModLinearMap 2
      map_one' := by
        refine LinearMap.ext fun v => ?_
        obtain ⟨u, rfl⟩ := hsurj v
        have h1 : c 1 u = u := Subtype.ext (by simp [hc])
        show a 1 _ = _
        rw [ha, h1]
        rfl
      map_mul' := fun x y => by
        refine LinearMap.ext fun v => ?_
        obtain ⟨u, rfl⟩ := hsurj v
        have h1 : c (x * y) u = c x (c y u) := Subtype.ext (by simp [hc, mul_assoc])
        show a (x * y) _ = a x (a y _)
        rw [ha, ha, ha, h1] }
  let ρ : ↥X →* GLV (Additive (↥(blockU J) ⧸ N)) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2)
      (Additive (↥(blockU J) ⧸ N))).toMonoidHom.comp φ.toHomUnits
  have hρ : ∀ (x : ↥X) (v : Additive (↥(blockU J) ⧸ N)), ρ x v = φ x v := fun _ _ => rfl
  let π : ↥(blockU J) →* Multiplicative (Additive (↥(blockU J) ⧸ N)) :=
    { toFun := fun u => Multiplicative.ofAdd (Additive.ofMul (QuotientGroup.mk u))
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hπ : ∀ u : ↥(blockU J),
      π u = Multiplicative.ofAdd (Additive.ofMul (QuotientGroup.mk u : ↥(blockU J) ⧸ N)) :=
    fun _ => rfl
  refine ⟨Additive (↥(blockU J) ⧸ N), inferInstance, inferInstance, inferInstance, ⟨{
    π := π
    surj := ?_
    ker_eq := ?_
    normalizes := hX
    ρ := ρ
    spec := ?_ }⟩⟩
  · intro w
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (Additive.toMul (Multiplicative.toAdd w))
    exact ⟨u, by rw [hπ, hu]; rfl⟩
  · ext u
    rw [MonoidHom.mem_ker, hπ]
    exact QuotientGroup.eq_one_iff u
  · intro x u v huv
    rw [hπ, hπ, hρ]
    have h1 : c x u = v := Subtype.ext huv.symm
    show Additive.ofMul (QuotientGroup.mk v : ↥(blockU J) ⧸ N) =
      a x (Additive.ofMul (QuotientGroup.mk u))
    rw [ha, h1]

namespace TildeULin

variable {J X : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  (lin : TildeULin J X V)

@[expose] def img (A : Subgroup G) : Subgroup (GLV V) :=
  (A.subgroupOf X).map lin.ρ

@[expose] def vec (u : ↥(blockU J)) : V :=
  Multiplicative.toAdd (lin.π u)

@[expose] def vecImg (A : Subgroup G) : Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2) {v | ∃ u : ↥(blockU J), (u : G) ∈ A ∧ lin.vec u = v}

theorem vec_mul (u v : ↥(blockU J)) : lin.vec (u * v) = lin.vec u + lin.vec v := by
  simp [vec]

private theorem vec_one : lin.vec 1 = 0 := by
  simp [vec]

private theorem vec_inv (u : ↥(blockU J)) : lin.vec u⁻¹ = - lin.vec u := by
  simp [vec]

theorem vec_eq_zero_iff (u : ↥(blockU J)) : lin.vec u = 0 ↔ (u : G) ∈ blockZ J := by
  rw [← Subgroup.mem_subgroupOf, ← lin.ker_eq, MonoidHom.mem_ker]
  simp [vec]

theorem vec_surjective : Function.Surjective lin.vec := fun v => by
  obtain ⟨u, hu⟩ := lin.surj (Multiplicative.ofAdd v)
  exact ⟨u, by simp [vec, hu]⟩

theorem ρ_vec (x : ↥X) (u v : ↥(blockU J)) (h : (v : G) = x * u * (x : G)⁻¹) :
    lin.ρ x (lin.vec u) = lin.vec v :=
  (lin.spec x u v h).symm

theorem mem_vecImg_iff {A : Subgroup G} (hA : A ≤ blockU J) (v : V) :
    v ∈ lin.vecImg A ↔ ∃ u : ↥(blockU J), (u : G) ∈ A ∧ lin.vec u = v := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
  let S : AddSubgroup V :=
    { carrier := {v | ∃ u : ↥(blockU J), (u : G) ∈ A ∧ lin.vec u = v}
      zero_mem' := ⟨1, A.one_mem, lin.vec_one⟩
      add_mem' := by
        rintro _ _ ⟨u₁, hu₁, rfl⟩ ⟨u₂, hu₂, rfl⟩
        exact ⟨u₁ * u₂, A.mul_mem hu₁ hu₂, lin.vec_mul u₁ u₂⟩
      neg_mem' := by
        rintro _ ⟨u, hu, rfl⟩
        exact ⟨u⁻¹, A.inv_mem hu, lin.vec_inv u⟩ }
  have hle : lin.vecImg A ≤ AddSubgroup.toZModSubmodule 2 S :=
    Submodule.span_le.mpr fun w hw => hw
  exact hle h

private theorem vec_eq_vec_iff (u v : ↥(blockU J)) :
    lin.vec u = lin.vec v ↔ (u : G) * (v : G)⁻¹ ∈ blockZ J := by
  have h : lin.vec (u * v⁻¹) = lin.vec u - lin.vec v := by
    rw [lin.vec_mul, lin.vec_inv, sub_eq_add_neg]
  rw [← sub_eq_zero, ← h, lin.vec_eq_zero_iff]
  rfl

theorem ρ_eq_one_iff (x : ↥X) :
    lin.ρ x = 1 ↔ ∀ u ∈ blockU J, (x : G) * u * (x : G)⁻¹ * u⁻¹ ∈ blockZ J := by
  have hconj : ∀ u : G, u ∈ blockU J → (x : G) * u * (x : G)⁻¹ ∈ blockU J := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU (lin.normalizes x.2)) u).mp hu
  constructor
  · intro h u hu
    have h1 := lin.ρ_vec x ⟨u, hu⟩ ⟨(x : G) * u * (x : G)⁻¹, hconj u hu⟩ rfl
    rw [h, LinearEquiv.coe_one, id_eq] at h1
    exact (lin.vec_eq_vec_iff ⟨(x : G) * u * (x : G)⁻¹, hconj u hu⟩ ⟨u, hu⟩).mp h1.symm
  · intro h
    refine LinearEquiv.ext fun w => ?_
    obtain ⟨u, rfl⟩ := lin.vec_surjective w
    rw [lin.ρ_vec x u ⟨(x : G) * u * (x : G)⁻¹, hconj u u.2⟩ rfl, LinearEquiv.coe_one, id_eq]
    exact (lin.vec_eq_vec_iff ⟨(x : G) * u * (x : G)⁻¹, hconj u u.2⟩ u).mpr (h u u.2)

theorem ρ_eq_one_of_mem_blockQ {H : Subgroup G} (hJ : IsFooteBlock H J) (x : ↥X)
    (hx : (x : G) ∈ blockQ J) : lin.ρ x = 1 := by
  rw [lin.ρ_eq_one_iff]
  intro u hu
  have h : ⁅(x : G), u⁆ ∈ ⁅blockQ J, blockU J⁆ := Subgroup.commutator_mem_commutator hx hu
  rw [Subgroup.commutator_comm] at h
  exact IsFooteBlock.commutator_blockU_blockQ_le hJ h

include lin in
theorem nontrivial {H : Subgroup G} (hJ : IsFooteBlock H J) : Nontrivial V := by
  obtain ⟨g, hgU, hgZ⟩ := SetLike.exists_of_lt hJ.chief.1
  exact ⟨⟨lin.vec ⟨g, hgU⟩, 0, fun h => hgZ ((lin.vec_eq_zero_iff ⟨g, hgU⟩).mp h)⟩⟩

private def preU (S : Submodule (ZMod 2) V) : Subgroup G :=
  (AddSubgroup.toSubgroup S.toAddSubgroup |>.comap lin.π).map (blockU J).subtype

private theorem mem_preU {S : Submodule (ZMod 2) V} {g : G} :
    g ∈ lin.preU S ↔ ∃ h : g ∈ blockU J, lin.vec ⟨g, h⟩ ∈ S := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u.2, hu⟩
  · rintro ⟨h, hv⟩
    exact ⟨⟨g, h⟩, hv, rfl⟩

private theorem conj_mem_preU {J₁ : Subgroup G} (hJ₁X : J₁ ≤ X) {S : Submodule (ZMod 2) V}
    (hS : Invariant (lin.img J₁) S) {j g : G} (hj : j ∈ J₁) (hg : g ∈ lin.preU S) :
    j * g * j⁻¹ ∈ lin.preU S := by
  obtain ⟨hgU, hv⟩ := (lin.mem_preU).mp hg
  have hconj : j * g * j⁻¹ ∈ blockU J :=
    (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU (lin.normalizes (hJ₁X hj))) g).mp
      hgU
  refine (lin.mem_preU).mpr ⟨hconj, ?_⟩
  have h := lin.ρ_vec ⟨j, hJ₁X hj⟩ ⟨g, hgU⟩ ⟨j * g * j⁻¹, hconj⟩ rfl
  rw [← h]
  exact hS _ ⟨⟨j, hJ₁X hj⟩, Subgroup.mem_subgroupOf.mpr hj, rfl⟩ _ hv

private theorem preU_dichotomy {H₁ J₁ : Subgroup G} (hJ₁ : IsFooteBlock H₁ J₁) (hJ₁X : J₁ ≤ X)
    {S : Submodule (ZMod 2) V} (hS : Invariant (lin.img J₁) S) (hZ : blockZ J₁ ≤ lin.preU S) :
    lin.preU S ⊓ blockU J₁ = blockZ J₁ ∨ blockU J₁ ≤ lin.preU S := by
  have h := hJ₁.chief.2 (lin.preU S ⊓ blockU J₁) (le_inf hZ (blockZ_le_blockU J₁)) inf_le_right
    (Subgroup.le_normalizer_iff.mpr fun j hj g hg => ⟨lin.conj_mem_preU hJ₁X hS hj hg.1,
      (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU J₁ hj) g).mp hg.2⟩)
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (h ▸ inf_le_left)

theorem isIrr_img {H : Subgroup G} (hJ : IsFooteBlock H J) (hJX : J ≤ X) :
    IsIrr (lin.img J) ⊤ := by
  haveI := lin.nontrivial hJ
  unfold IsIrr IrrSec
  refine ⟨fun _ _ _ _ => Submodule.mem_top, bot_lt_top, ?_⟩
  intro Y hY _ _
  have hZ : blockZ J ≤ lin.preU Y := fun g hg => (lin.mem_preU).mpr
    ⟨blockZ_le_blockU J hg, by
      rw [(lin.vec_eq_zero_iff ⟨g, blockZ_le_blockU J hg⟩).mpr hg]; exact Y.zero_mem⟩
  rcases lin.preU_dichotomy hJ hJX hY hZ with h | h
  · left
    refine (Submodule.eq_bot_iff _).mpr fun y hy => ?_
    obtain ⟨u, rfl⟩ := lin.vec_surjective y
    have hu : (u : G) ∈ lin.preU Y ⊓ blockU J := ⟨(lin.mem_preU).mpr ⟨u.2, hy⟩, u.2⟩
    rw [h] at hu
    exact (lin.vec_eq_zero_iff u).mpr hu
  · right
    refine (Submodule.eq_top_iff').mpr fun y => ?_
    obtain ⟨u, rfl⟩ := lin.vec_surjective y
    obtain ⟨_, hv⟩ := (lin.mem_preU).mp (h u.2)
    exact hv

@[expose] noncomputable def ρbar {H : Subgroup G} (hJ : IsFooteBlock H J) (hJX : J ≤ X) :
    (↥J ⧸ CFSG.pCore 2 ↥J) →* GLV V :=
  QuotientGroup.lift (CFSG.pCore 2 ↥J) (lin.ρ.comp (Subgroup.inclusion hJX)) (by
    intro j hj
    exact lin.ρ_eq_one_of_mem_blockQ hJ (Subgroup.inclusion hJX j) ⟨j, hj, rfl⟩)

theorem ρbar_mk {H : Subgroup G} (hJ : IsFooteBlock H J) (hJX : J ≤ X) (j : ↥J) :
    lin.ρbar hJ hJX (QuotientGroup.mk j) = lin.ρ (Subgroup.inclusion hJX j) :=
  QuotientGroup.lift_mk _ _ j

theorem range_ρbar {H : Subgroup G} (hJ : IsFooteBlock H J) (hJX : J ≤ X) :
    (lin.ρbar hJ hJX).range = lin.img J := by
  ext g
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨Subgroup.inclusion hJX j, Subgroup.mem_subgroupOf.mpr j.2, (lin.ρbar_mk hJ hJX j).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨QuotientGroup.mk ⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, lin.ρbar_mk hJ hJX _⟩

private theorem exists_ρ_ne_one {H : Subgroup G} (hJ : IsFooteBlock H J) (hJX : J ≤ X) :
    ∃ j : ↥J, lin.ρ (Subgroup.inclusion hJX j) ≠ 1 := by
  by_contra hall
  have hall' : ∀ j : ↥J, lin.ρ (Subgroup.inclusion hJX j) = 1 := fun j =>
    not_not.mp fun h => hall ⟨j, h⟩
  have hcomm : ⁅blockU J, J⁆ ≤ blockZ J := by
    rw [Subgroup.commutator_comm, Subgroup.commutator_le]
    intro j hj u hu
    exact (lin.ρ_eq_one_iff (Subgroup.inclusion hJX ⟨j, hj⟩)).mp (hall' ⟨j, hj⟩) u hu
  rw [IsFooteBlock.commutator_blockU hJ] at hcomm
  exact absurd hJ.chief.1 (not_lt_of_ge hcomm)

private theorem ker_ρbar_ne_top {H : Subgroup G} (hJ : IsFooteBlock H J) (hJX : J ≤ X) :
    (lin.ρbar hJ hJX).ker ≠ ⊤ := by
  intro htop
  obtain ⟨j, hj⟩ := lin.exists_ρ_ne_one hJ hJX
  apply hj
  have h : (QuotientGroup.mk j : ↥J ⧸ CFSG.pCore 2 ↥J) ∈ (lin.ρbar hJ hJX).ker := by
    rw [htop]
    exact Subgroup.mem_top _
  rwa [MonoidHom.mem_ker, lin.ρbar_mk] at h

theorem ker_ρbar_le_center {H : Subgroup G} (hJ : IsFooteBlock H J) (hJX : J ≤ X) :
    (lin.ρbar hJ hJX).ker ≤ Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J) :=
  CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hJ.quasisimple _
    (lin.ker_ρbar_ne_top hJ hJX)

theorem odd_card_ker_ρbar {H : Subgroup G} (hJ : IsFooteBlock H J) (hJX : J ≤ X) :
    Odd (Nat.card (lin.ρbar hJ hJX).ker) := by
  by_contra hodd
  rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hodd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := (lin.ρbar hJ hJX).ker) 2 hodd
  have hxc : ((x : (lin.ρbar hJ hJX).ker) : ↥J ⧸ CFSG.pCore 2 ↥J) ∈
      Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J) := lin.ker_ρbar_le_center hJ hJX x.2
  have hord : orderOf ((x : (lin.ρbar hJ hJX).ker) : ↥J ⧸ CFSG.pCore 2 ↥J) = 2 := by
    rw [Subgroup.orderOf_coe, hx]
  have hz : IsPGroup 2
      (Subgroup.zpowers ((x : (lin.ρbar hJ hJX).ker) : ↥J ⧸ CFSG.pCore 2 ↥J)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hle := CFSG.AGLEmbedding.le_pCore_of_isPGroup_of_le_commutative_normal
    (p := 2) (X := ↥J ⧸ CFSG.pCore 2 ↥J) (W := Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J))
    inferInstance (fun a ha b _ => (Subgroup.mem_center_iff.mp ha b).symm)
    ((Subgroup.zpowers_le).mpr hxc) hz
  rw [CFSG.AGLEmbedding.pCore_quotient_pCore_eq_bot' (X := ↥J) 2] at hle
  have h1 := hle (Subgroup.mem_zpowers _)
  rw [Subgroup.mem_bot] at h1
  rw [h1, orderOf_one] at hord
  exact absurd hord (by norm_num)

theorem isQuasisimple_img {H : Subgroup G} (hJ : IsFooteBlock H J) (hJX : J ≤ X) :
    CFSG.Open.IsQuasisimple ↥(lin.img J) := by
  rw [← lin.range_ρbar hJ hJX]
  exact CFSG.ComponentClassification.Quasisimple.range_quasisimple_of_ker_ne_top hJ.quasisimple _
    (lin.ker_ρbar_ne_top hJ hJX)

theorem blockU_le_blockU {J₁ : Subgroup G} (hJ₁J : J₁ ≤ J)
    (hU : blockU J₁ = ⁅blockQ J, J₁⁆) : blockU J₁ ≤ blockU J := by
  rw [hU]
  exact Subgroup.commutator_mono le_rfl hJ₁J

private theorem blockU_le_blockQ' (J : Subgroup G) : blockU J ≤ blockQ J :=
  Subgroup.le_normalizer_iff_commutator_le_left.mp (C1.le_normalizer_blockQ J)

private theorem commutator_mem_blockU_of_blockU_eq {J₁ : Subgroup G}
    (hU : blockU J₁ = ⁅blockQ J, J₁⁆) {y u : G} (hy : y ∈ J₁) (hu : u ∈ blockU J) :
    y * u * y⁻¹ * u⁻¹ ∈ blockU J₁ := by
  have h : ⁅y, u⁆ ∈ ⁅J₁, blockQ J⁆ :=
    Subgroup.commutator_mem_commutator hy (blockU_le_blockQ' J hu)
  rw [Subgroup.commutator_comm, ← hU] at h
  exact h

private theorem vec_mem_fixedSpace_of_mem_blockZ {J₁ : Subgroup G} (hJ₁X : J₁ ≤ X)
    {z : ↥(blockU J)} (hz : (z : G) ∈ blockZ J₁) : lin.vec z ∈ fixedSpace (lin.img J₁) := by
  rintro _ ⟨y, hy, rfl⟩
  have hyJ₁ : (y : G) ∈ J₁ := Subgroup.mem_subgroupOf.mp hy
  have hcomm : (y : G) * z * (y : G)⁻¹ = z := by
    rw [Subgroup.mem_centralizer_iff.mp hz.2 y hyJ₁, mul_inv_cancel_right]
  exact lin.ρ_vec y z z hcomm.symm

include lin in
private theorem conj_mem_blockU' (x : ↥X) {g : G} (hg : g ∈ blockU J) :
    (x : G) * g * (x : G)⁻¹ ∈ blockU J :=
  (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU (lin.normalizes x.2)) g).mp hg

private theorem ρ_vec_sub (x : ↥X) (u : ↥(blockU J)) :
    lin.ρ x (lin.vec u) - lin.vec u =
      lin.vec ⟨(x : G) * u * (x : G)⁻¹ * (u : G)⁻¹,
        (blockU J).mul_mem (lin.conj_mem_blockU' x u.2) ((blockU J).inv_mem u.2)⟩ := by
  have h1 := lin.vec_mul ⟨(x : G) * u * (x : G)⁻¹, lin.conj_mem_blockU' x u.2⟩ u⁻¹
  rw [lin.vec_inv, ← sub_eq_add_neg] at h1
  rw [lin.ρ_vec x u ⟨(x : G) * u * (x : G)⁻¹, lin.conj_mem_blockU' x u.2⟩ rfl]
  exact h1.symm

theorem commSpace_img_eq {H H₁ J₁ : Subgroup G} (hJ : IsFooteBlock H J)
    (hJ₁ : IsFooteBlock H₁ J₁) (hJ₁X : J₁ ≤ X) (hJ₁J : J₁ ≤ J)
    (hU : blockU J₁ = ⁅blockQ J, J₁⁆) : commSpace (lin.img J₁) ⊤ = lin.vecImg (blockU J₁) := by
  have hUU : blockU J₁ ≤ blockU J := blockU_le_blockU hJ₁J hU
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, ⟨y, hy, rfl⟩, w, -, rfl⟩
    have hyJ₁ : (y : G) ∈ J₁ := Subgroup.mem_subgroupOf.mp hy
    obtain ⟨u, rfl⟩ := lin.vec_surjective w
    exact Submodule.subset_span ⟨_, commutator_mem_blockU_of_blockU_eq hU hyJ₁ u.2,
      (lin.ρ_vec_sub y u).symm⟩
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨u, hu, rfl⟩
    have hsub : blockU J₁ ≤ lin.preU (commSpace (lin.img J₁) ⊤) := by
      refine (IsFooteBlock.commutator_blockU hJ₁).symm.le.trans ?_
      rw [Subgroup.commutator_comm, Subgroup.commutator_le]
      intro b hb a ha
      have haJ : a ∈ blockU J := hUU ha
      refine (lin.mem_preU).mpr ⟨(blockU J).mul_mem (lin.conj_mem_blockU' ⟨b, hJ₁X hb⟩ haJ)
        ((blockU J).inv_mem haJ), ?_⟩
      have h2 := lin.ρ_vec_sub ⟨b, hJ₁X hb⟩ ⟨a, haJ⟩
      have h3 : lin.ρ ⟨b, hJ₁X hb⟩ (lin.vec ⟨a, haJ⟩) - lin.vec ⟨a, haJ⟩ ∈
          commSpace (lin.img J₁) ⊤ :=
        Submodule.subset_span ⟨_, ⟨⟨b, hJ₁X hb⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩,
          lin.vec ⟨a, haJ⟩, Submodule.mem_top, rfl⟩
      rw [h2] at h3
      exact h3
    exact ((lin.mem_preU).mp (hsub hu)).2

theorem vec_mem_tildeVBot_iff {H H₁ J₁ : Subgroup G} (hJ : IsFooteBlock H J)
    (hJ₁ : IsFooteBlock H₁ J₁) (hJ₁X : J₁ ≤ X) (hJ₁J : J₁ ≤ J)
    (hU : blockU J₁ = ⁅blockQ J, J₁⁆) (u : ↥(blockU J)) (hu : (u : G) ∈ blockU J₁) :
    lin.vec u ∈ tildeVBot (lin.img J₁) ↔ (u : G) ∈ blockZ J₁ := by
  have hUU : blockU J₁ ≤ blockU J := blockU_le_blockU hJ₁J hU
  have hcomm := lin.commSpace_img_eq hJ hJ₁ hJ₁X hJ₁J hU
  constructor
  · rintro ⟨hfix, -⟩
    have hS : Invariant (lin.img J₁) (fixedSpace (lin.img J₁)) := fun k hk v hv => by
      rw [hv k hk]
      exact hv
    have hZ : blockZ J₁ ≤ lin.preU (fixedSpace (lin.img J₁)) := fun z hz =>
      (lin.mem_preU).mpr ⟨hUU (blockZ_le_blockU J₁ hz),
        lin.vec_mem_fixedSpace_of_mem_blockZ hJ₁X (z := ⟨z, hUU (blockZ_le_blockU J₁ hz)⟩) hz⟩
    rcases lin.preU_dichotomy hJ₁ hJ₁X hS hZ with h | h
    · have hmem : (u : G) ∈ lin.preU (fixedSpace (lin.img J₁)) ⊓ blockU J₁ :=
        ⟨(lin.mem_preU).mpr ⟨u.2, hfix⟩, hu⟩
      rwa [h] at hmem
    ·
      exfalso
      have h1 : ⁅blockU J₁, J₁⁆ ≤ blockZ J := by
        rw [Subgroup.commutator_comm, Subgroup.commutator_le]
        intro j hj a ha
        obtain ⟨haJ, hv⟩ := (lin.mem_preU).mp (h ha)
        have hrho : lin.ρ ⟨j, hJ₁X hj⟩ (lin.vec ⟨a, haJ⟩) = lin.vec ⟨a, haJ⟩ :=
          hv _ ⟨⟨j, hJ₁X hj⟩, Subgroup.mem_subgroupOf.mpr hj, rfl⟩
        have h2 := lin.ρ_vec_sub ⟨j, hJ₁X hj⟩ ⟨a, haJ⟩
        rw [hrho, sub_self] at h2
        exact (lin.vec_eq_zero_iff _).mp h2.symm
      have h2 : ⁅⁅blockU J₁, J₁⁆, J₁⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        exact h1.trans (inf_le_right.trans (Subgroup.centralizer_le hJ₁J))
      have h3 : ⁅blockU J₁, J₁⁆ = ⊥ :=
        CFSG.ComponentClassification.Asc76.Sec5.commutator_eq_bot_of_commutator_commutator_eq_bot
          (IsFooteBlock.commutator_eq hJ₁) h2
      have hbot : blockU J₁ = ⊥ := (IsFooteBlock.commutator_blockU hJ₁).symm.trans h3
      have hlt := hJ₁.chief.1
      rw [hbot] at hlt
      exact not_lt_bot hlt
  · intro hz
    exact ⟨lin.vec_mem_fixedSpace_of_mem_blockZ hJ₁X hz, by
      rw [hcomm]
      exact Submodule.subset_span ⟨u, hu, rfl⟩⟩

theorem hasIrrTildeV_img {H H₁ J₁ : Subgroup G} (hJ : IsFooteBlock H J)
    (hJ₁ : IsFooteBlock H₁ J₁) (hJ₁X : J₁ ≤ X) (hJ₁J : J₁ ≤ J)
    (hU : blockU J₁ = ⁅blockQ J, J₁⁆) : HasIrrTildeV (lin.img J₁) := by
  have hUU : blockU J₁ ≤ blockU J := blockU_le_blockU hJ₁J hU
  have hcomm := lin.commSpace_img_eq hJ hJ₁ hJ₁X hJ₁J hU
  have hiff := fun (u : ↥(blockU J)) (hu : (u : G) ∈ blockU J₁) =>
    lin.vec_mem_tildeVBot_iff hJ hJ₁ hJ₁X hJ₁J hU u hu
  unfold HasIrrTildeV IrrSec
  refine ⟨?_, ?_⟩
  · obtain ⟨g, hgU, hgZ⟩ := SetLike.exists_of_lt hJ₁.chief.1
    refine lt_of_le_of_ne inf_le_right fun h => hgZ ?_
    have hv : lin.vec ⟨g, hUU hgU⟩ ∈ commSpace (lin.img J₁) ⊤ := by
      rw [hcomm]
      exact Submodule.subset_span ⟨_, hgU, rfl⟩
    rw [← h] at hv
    exact (hiff ⟨g, hUU hgU⟩ hgU).mp hv
  · intro Y hY hCY hYL
    have hZ : blockZ J₁ ≤ lin.preU Y := fun z hz => (lin.mem_preU).mpr
      ⟨hUU (blockZ_le_blockU J₁ hz),
        hCY ((hiff ⟨z, hUU (blockZ_le_blockU J₁ hz)⟩ (blockZ_le_blockU J₁ hz)).mpr hz)⟩
    rcases lin.preU_dichotomy hJ₁ hJ₁X hY hZ with h | h
    · left
      refine le_antisymm (fun y hy => ?_) hCY
      have hy2 : y ∈ lin.vecImg (blockU J₁) := hcomm ▸ hYL hy
      obtain ⟨u, hu, rfl⟩ := (lin.mem_vecImg_iff hUU y).mp hy2
      have hmem : (u : G) ∈ lin.preU Y ⊓ blockU J₁ := ⟨(lin.mem_preU).mpr ⟨u.2, hy⟩, hu⟩
      rw [h] at hmem
      exact (hiff u hu).mpr hmem
    · right
      refine le_antisymm hYL ?_
      rw [hcomm]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨u, hu, rfl⟩
      exact ((lin.mem_preU).mp (h hu)).2

theorem commutator_mem_blockZ_of_ρ_eq_one {H H₁ J₁ : Subgroup G} (hJ : IsFooteBlock H J)
    (hJ₁ : IsFooteBlock H₁ J₁) (hJ₁X : J₁ ≤ X) (hJ₁J : J₁ ≤ J)
    (hU : blockU J₁ = ⁅blockQ J, J₁⁆) (x : ↥X) (hx : (x : G) ∈ J₁) (h1 : lin.ρ x = 1)
    (u : G) (hu : u ∈ blockU J₁) : (x : G) * u * (x : G)⁻¹ * u⁻¹ ∈ blockZ J₁ := by
  have hUU : blockU J₁ ≤ blockU J := blockU_le_blockU hJ₁J hU
  have h2 : (x : G) * u * (x : G)⁻¹ * u⁻¹ ∈ blockZ J := (lin.ρ_eq_one_iff x).mp h1 u (hUU hu)
  have h3 : (x : G) * u * (x : G)⁻¹ * u⁻¹ ∈ blockU J₁ :=
    (blockU J₁).mul_mem ((Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU J₁ hx) u).mp hu)
      ((blockU J₁).inv_mem hu)
  exact ⟨h3, Subgroup.centralizer_le hJ₁J h2.2⟩

end TildeULin

end CFSG.CGT.Foote82
