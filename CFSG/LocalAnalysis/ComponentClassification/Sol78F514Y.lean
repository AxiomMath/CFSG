module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78F514CH
public import CFSG.LocalAnalysis.ComponentClassification.Sol78F514Sig

public noncomputable section

namespace CFSG.ComponentClassification.Sol78.F514

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ABGLocalTools
  CFSG.ComponentClassification.UnbalancedLayer

theorem isSolvable_centralizer_of_inf {G : Type} [Group G] {C : Subgroup G} {a : C}
    (h : Group.IsSolvable ↥(C ⊓ centralizer ({(a : G)} : Set G))) :
    Group.IsSolvable ↥(centralizer ({a} : Set C)) := by
  let φ : ↥(centralizer ({a} : Set C)) →* ↥(C ⊓ centralizer ({(a : G)} : Set G)) :=
    { toFun := fun x => ⟨((x : C) : G), mem_inf.mpr ⟨(x : C).2, mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.2))⟩⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine Group.isSolvable_of_isSolvable_injective (f := φ) fun x y hxy => ?_
  have h1 := congrArg (fun w : ↥(C ⊓ centralizer ({(a : G)} : Set G)) => (w : G)) hxy
  exact Subtype.ext (Subtype.ext h1)

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem le_oddCoreOfCentralizer_of_normal {a : Y} {N : Subgroup Y}
    (hN : N ≤ centralizer ({a} : Set Y))
    (hn : ∀ c ∈ centralizer ({a} : Set Y), ∀ n ∈ N, c * n * c⁻¹ ∈ N)
    (hodd : Odd (Nat.card N)) : N ≤ oddCoreOfCentralizer a := by
  intro x hx
  refine ⟨⟨x, hN hx⟩, ?_, rfl⟩
  have hNn : (N.subgroupOf (centralizer ({a} : Set Y))).Normal :=
    ⟨fun n hn' c => hn c c.2 n hn'⟩
  have hcop : Nat.Coprime 2 (Nat.card (N.subgroupOf (centralizer ({a} : Set Y)))) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hN).toEquiv]
    exact Nat.coprime_two_left.mpr hodd
  exact (le_sSup ⟨hNn, hcop⟩ : N.subgroupOf _ ≤ pPrimeCore 2 _) hx

theorem le_normalizer_sup_of_sylow {R W L₀ N₀ C : Subgroup Y} (hRsyl : IsSylowOf 2 R L₀)
    (hL₀ : L₀ ≤ N₀ ⊔ R) (hN₀W : N₀ ≤ W) (hCL : C ≤ normalizer (L₀ : Set Y))
    (hNRW : normalizer (R : Set Y) ≤ normalizer (W : Set Y)) :
    C ≤ normalizer ((R ⊔ W : Subgroup Y) : Set Y) := by
  intro x hx
  have hxL := hCL hx
  have hconjL : conjugate L₀ x⁻¹ = L₀ := by
    ext y
    rw [mem_conjugate_iff]
    exact ((mem_normalizer_iff.mp (inv_mem hxL)) y).symm
  have hR' : IsSylowOf 2 (conjugate R x⁻¹) L₀ := hconjL ▸ isSylowOf_conjugate hRsyl x⁻¹
  obtain ⟨l, hlL, hl⟩ := Foote5.exists_conj_eq_of_isSylowOf hRsyl hR'
  rw [conjugate_conjugate] at hl
  have hgN : x⁻¹ * l ∈ normalizer (R : Set Y) := by
    rw [mem_normalizer_iff]
    intro r
    rw [← mem_conjugate_iff, hl]
  have hlK : l ∈ normalizer ((R ⊔ W : Subgroup Y) : Set Y) :=
    le_normalizer ((hL₀.trans (sup_le (hN₀W.trans le_sup_right) le_sup_left)) hlL)
  have hgK : (x⁻¹ * l)⁻¹ ∈ normalizer ((R ⊔ W : Subgroup Y) : Set Y) :=
    mem_normalizer_sup (inv_mem hgN) (hNRW (inv_mem hgN))
  rw [show x = l * (x⁻¹ * l)⁻¹ by group]
  exact mul_mem hlK hgK

end CFSG.ComponentClassification.Sol78.F514
