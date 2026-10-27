module

public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticEndNode
public import CFSG.Assembly.LargeEvenGLABridge

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172B.Cent

open CFSG.Open

section Commutator

variable {Γ : Type*} [Group Γ] {X H : Subgroup Γ}

theorem commutator_le_subgroupOf_of_commutator_le (h : ⁅X, X⁆ ≤ H) :
    commutator ↥X ≤ H.subgroupOf X := by
  rw [commutator_def, Subgroup.commutator_le]
  intro g _ k _
  rw [Subgroup.mem_subgroupOf]
  exact h (Subgroup.commutator_mem_commutator g.2 k.2)

theorem normal_subgroupOf_of_commutator_le (h : ⁅X, X⁆ ≤ H) : (H.subgroupOf X).Normal :=
  Subgroup.Normal.of_commutator_le ↥X (commutator_le_subgroupOf_of_commutator_le h)

theorem isSolvable_quotient_of_commutator_le [(H.subgroupOf X).Normal] (h : ⁅X, X⁆ ≤ H) :
    Group.IsSolvable (↥X ⧸ H.subgroupOf X) := by
  haveI : IsMulCommutative (↥X ⧸ H.subgroupOf X) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.2 (commutator_le_subgroupOf_of_commutator_le h)
  infer_instance

end Commutator

section Layer

variable {G : Type*} [Group G]

theorem glaLayer_eq_of_commutator_le {X D : Subgroup G} (hDX : D ≤ X) (hcomm : ⁅X, X⁆ ≤ D)
    (hD : CFSG.IsQuasisimple ↥D) : GLALayer X = D ∧ IsComponentOf D X := by
  obtain ⟨h1, h2⟩ := CFSG.StandardType.TableBSymp.largeEvenLayer_eq_of_commutator_mem hDX
    (fun g hg k hk => hcomm (Subgroup.commutator_mem_commutator hg hk)) hD
  exact ⟨by rw [← CFSG.Assembly.LargeEven.largeEvenLayer_eq_glaLayer, h1],
    CFSG.Assembly.isComponentOf_iff_open.1 h2⟩

end Layer

section Centralizer

variable {G : Type*} [Group G]

theorem centralizer_pair_eq_of_mul_zpow (a b : G) (k : ℤ) :
    Subgroup.centralizer ({a * b ^ k, b} : Set G) = Subgroup.centralizer ({a, b} : Set G) := by
  ext g
  simp only [Subgroup.mem_centralizer_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq]
  constructor
  · rintro ⟨h1, h2⟩
    have hb : Commute b g := h2
    have hk : Commute (b ^ k) g := hb.zpow_left k
    have hab : Commute (a * b ^ k) g := h1
    have : Commute a g := by
      have := hab.mul_left hk.inv_left
      simpa using this
    exact ⟨this, h2⟩
  · rintro ⟨h1, h2⟩
    have hb : Commute b g := h2
    exact ⟨(show Commute a g from h1).mul_left (hb.zpow_left k), h2⟩

theorem nonempty_mulEquiv_inf_centralizer {G' : Type*} [Group G'] {H : Subgroup G} (φ : ↥H ≃* G')
    {a : G} (ha : a ∈ H) :
    Nonempty (↥(H ⊓ Subgroup.centralizer ({a} : Set G)) ≃*
      ↥(Subgroup.centralizer ({φ ⟨a, ha⟩} : Set G'))) := by
  let f₀ : ↥(H ⊓ Subgroup.centralizer ({a} : Set G)) →* G' :=
    φ.toMonoidHom.comp (Subgroup.inclusion (inf_le_left : H ⊓ Subgroup.centralizer ({a} : Set G) ≤ H))
  have hf₀ : ∀ x, f₀ x ∈ Subgroup.centralizer ({φ ⟨a, ha⟩} : Set G') := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff]
    show φ (Subgroup.inclusion _ x) * φ ⟨a, ha⟩ = φ ⟨a, ha⟩ * φ (Subgroup.inclusion _ x)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 x.2).2)
  refine ⟨MulEquiv.ofBijective (f₀.codRestrict _ hf₀) ⟨fun x y hxy => ?_, fun y => ?_⟩⟩
  · have h1 : f₀ x = f₀ y := congrArg Subtype.val hxy
    have h2 := φ.injective h1
    have h4 : ((Subgroup.inclusion (inf_le_left : H ⊓ Subgroup.centralizer ({a} : Set G) ≤ H) x : ↥H) : G) =
        ((Subgroup.inclusion (inf_le_left : H ⊓ Subgroup.centralizer ({a} : Set G) ≤ H) y : ↥H) : G) :=
      congrArg Subtype.val h2
    exact Subtype.ext h4
  · obtain ⟨y, hy⟩ := y
    have hc := Subgroup.mem_centralizer_singleton_iff.1 hy
    have h3 := congrArg φ.symm hc
    simp only [map_mul, MulEquiv.symm_apply_apply] at h3
    refine ⟨⟨((φ.symm y : ↥H) : G), Subgroup.mem_inf.2 ⟨(φ.symm y).2,
      Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val h3)⟩⟩, Subtype.ext ?_⟩
    show φ ⟨((φ.symm y : ↥H) : G), _⟩ = y
    exact φ.apply_symm_apply y

end Centralizer

end CFSG.LocalAnalysis.GLTheoremA.S172B.Cent

end
