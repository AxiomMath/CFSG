module

public import CFSG.CharacterTheory.Semidihedral.UnitaryDValueGWLocal

public section

open scoped Classical

namespace CFSG.Semidihedral.UnitaryDValue.GW

open CFSG.Semidihedral.UnitaryDValue CFSG.Semidihedral.UnitaryDValue.DValueData

variable {G : Type} [Group G] [Fintype G] (D : DValueData G)

theorem T_le_centralizer {w : G} (hwC : w ∈ D.C) : D.T ≤ Subgroup.centralizer {w} :=
  fun v hv => Subgroup.mem_centralizer_singleton_iff.mpr (D.C_comm v (D.T_le_C hv) w hwC)

theorem exists_mem_C_of_quotient_commute {w : G} (hw : w ∈ D.W) (hw1 : w ≠ 1)
    (htw : D.t * w = w * D.t) (O : Subgroup (Subgroup.centralizer ({w} : Set G))) [O.Normal]
    (hO : CFSG.oddCore (Subgroup.centralizer ({w} : Set G)) = O)
    (k : Subgroup.centralizer ({w} : Set G))
    (hk : ∀ (v : G) (hv : v ∈ D.T),
      QuotientGroup.mk' O ⟨v, T_le_centralizer D (D.W_le hw) hv⟩ * QuotientGroup.mk' O k =
        QuotientGroup.mk' O k * QuotientGroup.mk' O ⟨v, T_le_centralizer D (D.W_le hw) hv⟩) :
    ∃ c : Subgroup.centralizer ({w} : Set G), (c : G) ∈ D.C ∧ c⁻¹ * k ∈ O := by
  subst hO
  let K := Subgroup.centralizer ({w} : Set G)
  let O := CFSG.oddCore K
  have hTK : D.T ≤ K := T_le_centralizer D (D.W_le hw)
  let : MulDistribMulAction D.T K :=
    MulDistribMulAction.compHom K (MulAut.conj.comp (Subgroup.inclusion hTK))
  have hsmul : ∀ (b : D.T) (g : K), b • g = Subgroup.inclusion hTK b * g *
      (Subgroup.inclusion hTK b)⁻¹ := fun b g => by
    change (MulAut.conj (Subgroup.inclusion hTK b)) g = _
    rw [MulAut.conj_apply]
  have hinv : CFSG.IsInvariant D.T K O := ⟨fun b g => by
    rw [hsmul]
    constructor
    · intro hg
      exact (inferInstance : O.Normal).conj_mem g hg _
    · intro hg
      have := (inferInstance : O.Normal).conj_mem _ hg (Subgroup.inclusion hTK b)⁻¹
      simpa [mul_assoc] using this⟩
  have hOC := oddCore_le_C D hw hw1 htw
  have hOcomm : ∀ a b : O, a * b = b * a := fun a b => Subtype.ext (Subtype.ext
    (D.C_comm _ (hOC a a.2) _ (hOC b b.2)))
  have hsolv : Group.IsSolvable O := Group.isSolvable_of_comm hOcomm
  have hcop : Nat.Coprime (Nat.card D.T) (Nat.card O) := by
    rw [card_T, show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr CFSG.ABGLocalTools.odd_card_oddCore)
  have hg : ∀ b : D.T, k⁻¹ * (b • k) ∈ O := by
    intro b
    have hb := hk b b.2
    rw [hsmul, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    change (QuotientGroup.mk' O k)⁻¹ * (QuotientGroup.mk' O (Subgroup.inclusion hTK b) *
      QuotientGroup.mk' O k * (QuotientGroup.mk' O (Subgroup.inclusion hTK b))⁻¹) = 1
    have hb' : QuotientGroup.mk' O (Subgroup.inclusion hTK b) * QuotientGroup.mk' O k =
        QuotientGroup.mk' O k * QuotientGroup.mk' O (Subgroup.inclusion hTK b) := hb
    rw [hb']
    group
  obtain ⟨c, hc, hck⟩ := CFSG.SolvableHall.exists_fixed_of_coset_fixed O hinv hsolv hcop k hg
  refine ⟨c, ?_, hck⟩
  have hfix : ∀ v (hv : v ∈ D.T), (c : G) * v = v * c := by
    intro v hv
    have h := hc ⟨v, hv⟩
    rw [hsmul] at h
    have h' := congrArg (fun y : K => (y : G)) h
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion] at h'
    calc (c : G) * v = v * c * v⁻¹ * v := by rw [h']
      _ = v * c := by group
  exact D.mem_C_iff.mpr ⟨hfix _ D.x_mem_T, hfix _ D.z_mem_T⟩

end CFSG.Semidihedral.UnitaryDValue.GW
