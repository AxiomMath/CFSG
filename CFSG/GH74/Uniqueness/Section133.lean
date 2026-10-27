module

public import CFSG.GH74.Uniqueness.Bender.UnitaryFixed
public import CFSG.GH74.Uniqueness.Section132W

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem A6.sup_eq_top
    (S : ZDSetup X Z M) {c : Ctx12 Z M} {n e e' : ℕ} (hL : LData c n 1)
    {Lu LA : Subgroup X} (hBu : BenderSub Z M Lu n 3 e) (hBA : BenderSub Z M LA n 3 e')
    (hLu : c.L ≤ Lu) (hnotle : ¬ LA ≤ Lu) : Lu ⊔ LA = ⊤ := by
  by_contra hne
  have hZ := S.invariant
  set X₁ := Lu ⊔ LA with hX₁
  have hmono : ∀ {H K : Subgroup X}, H ≤ K → zHull Z H ≤ zHull Z K := fun hHK =>
    closure_mono (Set.inter_subset_inter_right Z hHK)
  have hX₁Z : zHull Z X₁ = X₁ := by
    apply le_antisymm (Cor713.zHull_le X₁)
    refine sup_le ?_ ?_
    · calc Lu = zHull Z Lu := hBu.zhull.symm
        _ ≤ zHull Z X₁ := hmono le_sup_left
    · calc LA = zHull Z LA := hBA.zhull.symm
        _ ≤ zHull Z X₁ := hmono le_sup_right
  have hLX : c.L ≤ X₁ := hLu.trans le_sup_left
  have hFM : ¬ X₁ ≤ M := fun h => c.htM (h (hLX c.t_mem_L))
  have hne' : (Z ∩ ((X₁ ⊓ M : Subgroup X) : Set X)).Nonempty :=
    ⟨c.z, c.hz, mem_inf.mpr ⟨hLX c.z_mem_L, c.hzM⟩⟩
  have hns : ¬ Group.IsSolvable ↥(zHull Z X₁) := by
    intro hsol
    rw [hX₁Z] at hsol
    have : IsSimpleGroup ↥c.L := hL.bender.isSimple
    have hLsol : Group.IsSolvable ↥c.L :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hLX)
        (Subgroup.inclusion_injective hLX)
    exact hL.bender.isSimpleBenderGroup.not_commutative
      ((IsSimpleGroup.comm_iff_isSolvable (G := ↥c.L)).mpr hLsol)
  obtain ⟨m, j, e₁, hB₁⟩ := S.benderSub_exists hne hFM hne' hns
  rw [hX₁Z] at hB₁
  have hZM : Z ∩ ((X₁ ⊓ M : Subgroup X) : Set X) = Z ∩ (M : Set X) := by
    ext x
    constructor
    · rintro ⟨hxZ, hxLM⟩
      exact ⟨hxZ, (mem_inf.mp hxLM).2⟩
    · rintro ⟨hxZ, hxM⟩
      exact ⟨hxZ, mem_inf.mpr ⟨hLX (IsProductDisconnected.inter_le_lSubgroup hZ S.prodDisc c.ht
        c.htM c.hz c.hzM ⟨hxZ, hxM⟩), hxM⟩⟩
  have hm : m = n := by
    have h1 := A2.ncard_inter_of_benderSub S hB₁
    rw [hZM, A2.ncard_zM hL] at h1
    have h2 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h3 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    exact Nat.pow_right_injective le_rfl (by omega : 2 ^ m = 2 ^ n)
  subst hm
  have hj : j ≤ 3 := by
    rcases hB₁.bender.cases' with ⟨hj, -⟩ | ⟨hj, -⟩ | ⟨hj, -⟩ <;> omega
  have hcard : (Z ∩ (X₁ : Set X)).ncard ≤ (Z ∩ (Lu : Set X)).ncard := by
    rw [A6.ncard_Z_inter S hB₁, A6.ncard_Z_inter S hBu]
    exact Nat.mul_le_mul_left _ (Nat.add_le_add_right
      (Nat.pow_le_pow_right (Nat.one_le_two_pow) hj) 1)
  have heq : Lu = X₁ := A6.eq_of_le_of_ncard_le hBu.zhull hX₁Z le_sup_left hcard
  have hle : LA ≤ Lu := by rw [heq]; exact le_sup_right
  exact hnotle hle

theorem A6.lemma133
    (S : ZDSetup X Z M) {c : Ctx12 Z M} {n e e' : ℕ} (hL : LData c n 1)
    {u : X} (hu2 : orderOf u = 2) (hBu : BenderSub Z M (cenHull Z u) n 3 e) (hLu : c.L ≤ cenHull Z u)
    {A : Subgroup X} (hAu : A ≤ cenHull Z u)
    (hBA : BenderSub Z M (zHull Z (centralizer (A : Set X))) n 3 e')
    (hnotle : ¬ zHull Z (centralizer (A : Set X)) ≤ cenHull Z u)
    (hun : u ∈ normalizer (zHull Z (centralizer (A : Set X)) : Set X))
    (hα2 : A6.barHom _ ⟨u, hun⟩ * A6.barHom _ ⟨u, hun⟩ = 1)
    (hout : ¬ ∃ k, ∀ x, A6.barHom _ ⟨u, hun⟩ x = k * x * k⁻¹)
    (hfix : ∀ k ∈ Bender.autFixed (A6.barHom _ ⟨u, hun⟩),
      ∃ y, ∃ hy : y ∈ zHull Z (centralizer (A : Set X)), y ∈ c.L ∧
        QuotientGroup.mk' (center ↥(zHull Z (centralizer (A : Set X)))) ⟨y, hy⟩ = k)
    {b : X} (hbu : b * u = u * b) (hbL : ∀ y ∈ cenHull Z u, b * y = y * b) : b = 1 ∨ b = u := by
  set LA := zHull Z (centralizer (A : Set X)) with hLAdef
  have hZ := S.invariant
  have hsup := A6.sup_eq_top S hL hBu hBA hLu hnotle
  have hbC : b ∈ centralizer (A : Set X) := mem_centralizer_iff.mpr fun a ha => (hbL a (hAu ha)).symm
  have hbN : b ∈ normalizer (LA : Set X) := A6.mem_normalizer_zHull hZ (le_normalizer hbC)
  set α := A6.barHom LA ⟨u, hun⟩ with hα
  set σ := A6.barHom LA ⟨b, hbN⟩ with hσ
  have hcomm : σ * α = α * σ := by
    rw [hσ, hα, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hbu
  have hσfix : ∀ x ∈ Bender.autFixed α, σ x = x := by
    intro k hk
    obtain ⟨y, hy, hyL, rfl⟩ := hfix k hk
    rw [hσ, A6.barHom_mk' _ _ hy hy]
    rw [hbL y (hLu hyL), mul_inv_cancel_right]
  have htriv : ∀ g : X, (∀ y ∈ cenHull Z u, g * y = y * g) → g ∈ centralizer (LA : Set X) →
      g = 1 := by
    intro g hg1 hg2
    refine A2.eq_one_of_forall_commute S fun x => ?_
    have hle : cenHull Z u ⊔ LA ≤ centralizer ({g} : Set X) := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · exact mem_centralizer_singleton_iff.mpr (hg1 y hy).symm
      · exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hg2 y hy)
    have hx : x ∈ centralizer ({g} : Set X) := hle (by rw [hsup]; exact mem_top x)
    exact mem_centralizer_singleton_iff.mp hx
  have hodd := A2.odd_card_center_of_benderSub hBA
  rcases hBA.bender.centralizer_unitary α hα2 hout σ hcomm hσfix with h1 | h1
  · left
    refine htriv b hbL ?_
    exact A6.mem_centralizer_of_barHom_eq_one LA (fun z hz => hZ.mul_self_eq_one hz) hBA.zhull hodd
      ⟨b, hbN⟩ (fun z _ hzF => by rw [← hσ, h1, MulAut.one_apply])
  · right
    have hbuN : b * u ∈ normalizer (LA : Set X) := mul_mem hbN hun
    have hbu1 : A6.barHom LA ⟨b * u, hbuN⟩ = 1 := by
      have e1 : (⟨b * u, hbuN⟩ : ↥(normalizer (LA : Set X))) = ⟨b, hbN⟩ * ⟨u, hun⟩ := rfl
      rw [e1, map_mul, ← hσ, h1]
      exact hα2
    have hcen := A6.mem_centralizer_of_barHom_eq_one LA (fun z hz => hZ.mul_self_eq_one hz)
      hBA.zhull hodd ⟨b * u, hbuN⟩ (fun z _ hzF => by rw [hbu1, MulAut.one_apply])
    have hbu' : b * u = 1 := htriv (b * u) (fun y hy => by
      have h2 : u * y = y * u := mul_comm_of_mem_cenHull hy
      calc b * u * y = b * (y * u) := by rw [mul_assoc, h2]
        _ = (b * y) * u := by group
        _ = y * b * u := by rw [hbL y hy]
        _ = y * (b * u) := by group) hcen
    have huu : u * u = 1 := sec126_involution_mul_self hu2
    calc b = b * u * u := by rw [mul_assoc, huu, mul_one]
      _ = u := by rw [hbu', one_mul]

end CFSG.GH74.Uniqueness
