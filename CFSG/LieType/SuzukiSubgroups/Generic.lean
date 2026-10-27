module

public import CFSG.Open.LocalVocabulary
public import CFSG.Monster.GroupTheory

public section

namespace CFSG.LieType.SuzukiSubgroups

open CFSG.Open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem eq_bot_of_elemAbelian_four {M E : Subgroup G}
    (hME : E ≤ normalizer (M : Set G)) (hE : IsElemAbelian 2 E) (hE4 : Nat.card E = 4)
    (hfix : ∀ e ∈ E, e ≠ 1 → ∀ m ∈ M, e * m = m * e → m = 1) : M = ⊥ := by
  let φ : E →* MulAut M :=
    (MulDistribMulAction.toMulAut (normalizer (M : Set G)) M).comp (Subgroup.inclusion hME)
  have hexp : ∀ e : E, e * e = 1 := by
    intro e
    apply Subtype.ext
    have h := hE.2 (e : G) e.2
    simpa [pow_two] using h
  have hfree : ∀ e : E, e ≠ 1 → ∀ n : M, φ e n = n → n = 1 := by
    intro e he n hn
    have hcomm : (e : G) * (n : G) = (n : G) * (e : G) := by
      have h : (e : G) * (n : G) * (e : G)⁻¹ = (n : G) := by
        have hc := congrArg (fun y : M => (y : G)) hn
        change ((Subgroup.inclusion hME e : normalizer (M : Set G)) : G) * (n : G) *
          ((Subgroup.inclusion hME e : normalizer (M : Set G)) : G)⁻¹ = (n : G) at hc
        simpa using hc
      calc
        (e : G) * (n : G) = ((e : G) * (n : G) * (e : G)⁻¹) * (e : G) := by group
        _ = (n : G) * (e : G) := by rw [h]
    exact Subtype.ext (by
      simpa using hfix (e : G) e.2 (fun h => he (Subtype.ext h)) (n : G) n.2 hcomm)
  refine eq_bot_iff.2 fun m hm => ?_
  simpa using congrArg (fun x : M => (x : G))
    (CFSG.Monster.eq_one_of_fourGroup_fixedPointFree hE4 hexp φ hfree ⟨m, hm⟩)

@[instance_reducible] private def conjAction (S Z : Subgroup G)
    (e : S →* normalizer (Z : Set G)) : MulAction S Z :=
  MulAction.compHom Z e

private theorem card_stabilizer_le_of_le {S T Z : Subgroup G}
    (e : S →* normalizer (Z : Set G)) {z : G} (hz : z ∈ Z)
    (hC : S ⊓ centralizer ({z} : Set G) ≤ T)
    (he : ∀ s : S, ((e s : normalizer (Z : Set G)) : G) = (s : G)) :
    letI : MulAction S Z := conjAction S Z e
    Nat.card (MulAction.stabilizer S (⟨z, hz⟩ : Z)) ≤ Nat.card T := by
  letI : MulAction S Z := conjAction S Z e
  have hsmul : ∀ s : S, ((s • (⟨z, hz⟩ : Z) : Z) : G) = (s : G) * z * (s : G)⁻¹ := by
    intro s
    change ((e s : normalizer (Z : Set G)) : G) * z *
      ((e s : normalizer (Z : Set G)) : G)⁻¹ = (s : G) * z * (s : G)⁻¹
    rw [he s]
  have hcomm : ∀ s : MulAction.stabilizer S (⟨z, hz⟩ : Z),
      ((s.1 : S) : G) * z = z * ((s.1 : S) : G) := by
    intro s
    have h := congrArg (fun y : Z => (y : G)) s.2
    rw [hsmul] at h
    calc
      ((s.1 : S) : G) * z =
          (((s.1 : S) : G) * z * ((s.1 : S) : G)⁻¹) * ((s.1 : S) : G) := by group
      _ = z * ((s.1 : S) : G) := by rw [h]
  refine (Nat.card_le_card_of_injective
    (fun s : MulAction.stabilizer S (⟨z, hz⟩ : Z) =>
      (⟨((s.1 : S) : G), s.1.2,
        Subgroup.mem_centralizer_singleton_iff.2 (hcomm s)⟩ :
        ↥(S ⊓ centralizer ({z} : Set G)))) ?_).trans (Subgroup.card_le_of_le hC)
  intro s t hst
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun x : ↥(S ⊓ centralizer ({z} : Set G)) => (x.1 : G)) hst

private theorem card_orbit_le_sub_one {S Z : Subgroup G} (e : S →* normalizer (Z : Set G))
    {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1) :
    letI : MulAction S Z := conjAction S Z e
    Nat.card (MulAction.orbit S (⟨z, hz⟩ : Z)) ≤ Nat.card Z - 1 := by
  letI : MulAction S Z := conjAction S Z e
  have hsub : (MulAction.orbit S (⟨z, hz⟩ : Z) : Set Z) ⊆ {w : Z | w ≠ 1} := by
    rintro w ⟨s, rfl⟩
    intro hw
    apply hz1
    have h := congrArg (fun y : Z => s⁻¹ • y) hw
    have h1 : s⁻¹ • (1 : Z) = 1 := by
      apply Subtype.ext
      show ((e s⁻¹ : normalizer (Z : Set G)) : G) * 1 *
        ((e s⁻¹ : normalizer (Z : Set G)) : G)⁻¹ = 1
      group
    simpa [h1] using h
  have hcardZ : ({w : Z | w ≠ 1} : Set Z).ncard = Nat.card Z - 1 := by
    rw [show ({w : Z | w ≠ 1} : Set Z) = (Set.univ \ {1}) by ext; simp,
      Set.ncard_sdiff_singleton_of_mem (Set.mem_univ (1 : Z)), Set.ncard_univ]
  rw [Nat.card_coe_set_eq, ← hcardZ]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

theorem card_le_mul_card_sub_one {S T Z : Subgroup G} (hSZ : S ≤ normalizer (Z : Set G))
    {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1) (hC : S ⊓ centralizer ({z} : Set G) ≤ T) :
    Nat.card S ≤ Nat.card T * (Nat.card Z - 1) := by
  classical
  let e : S →* normalizer (Z : Set G) := S.subtype.codRestrict _ (fun s => hSZ s.2)
  letI : MulAction S Z := conjAction S Z e
  let zZ : Z := ⟨z, hz⟩
  have hOS : Nat.card (MulAction.orbit S zZ) * Nat.card (MulAction.stabilizer S zZ) =
      Nat.card S := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup S zZ)
  have horb := card_orbit_le_sub_one e hz hz1
  have hstab := card_stabilizer_le_of_le e hz hC (fun s => rfl)
  calc
    Nat.card S = Nat.card (MulAction.orbit S zZ) * Nat.card (MulAction.stabilizer S zZ) :=
      hOS.symm
    _ ≤ (Nat.card Z - 1) * Nat.card T := Nat.mul_le_mul horb hstab
    _ = Nat.card T * (Nat.card Z - 1) := Nat.mul_comm _ _

end CFSG.LieType.SuzukiSubgroups
