module

public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Lower
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LpEpsJoin

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Timmesfeld.Balance.Alt

variable {G : Type*} [Group G] [Finite G]

theorem exists_twoLocal_lower_central {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X B L : Subgroup G}
    (hBX : B ≤ X) (hB : IsElemAbelian p B) (hL : GLAPComponent p X L)
    (E' T' : Subgroup (barOf p L)) (q : ℕ)
    (hZ : ∀ x ∈ E', (∀ y, x * y = y * x) → x = 1)
    (hE' : IsMulCommutative E' ∧ (∀ x ∈ E', x ^ p = 1) ∧ Nat.card E' = p ^ q)
    (hT' : T' ≠ ⊥ ∧ IsPGroup 2 T') (hET : E' ≤ Subgroup.centralizer (T' : Set (barOf p L))) :
    ∃ P S : Subgroup ↥X, IsMulCommutative P ∧ (∀ x ∈ P, x ^ p = 1) ∧
      Nat.card P = Nat.card (centB p B L) *
        p ^ (q * (B ⊓ Subgroup.normalizer (L : Set G)).relIndex B) ∧
      S ≠ ⊥ ∧ IsPGroup 2 S ∧ P ≤ Subgroup.normalizer (S : Set ↥X) := by
  classical
  set π : ↥X →* ↥X ⧸ GLAPPrimeCore p ↥X := QuotientGroup.mk' _ with hπ
  set θ := barTheta p hL.1 hL.2.1 with hθ
  have hθinj := barTheta_injective p hL.1 hL.2.1
  let πB : ↥B →* ↥X ⧸ GLAPPrimeCore p ↥X := π.comp (Subgroup.inclusion hBX)
  have hBc : IsMulCommutative B := hB.1
  let I := ↥B ⧸ ((B ⊓ Subgroup.normalizer (L : Set G)).subgroupOf B)
  have : Fintype I := Fintype.ofFinite I
  obtain ⟨r, hr⟩ : ∃ r : I → ↥B, ∀ i, (QuotientGroup.mk (r i) : I) = i :=
    ⟨fun i => (QuotientGroup.mk_surjective i).choose,
      fun i => (QuotientGroup.mk_surjective i).choose_spec⟩
  let ψ : I → (barOf p L →* ↥X ⧸ GLAPPrimeCore p ↥X) :=
    fun i => (MulAut.conj (πB (r i))⁻¹).toMonoidHom.comp θ
  have hψ : ∀ i, Function.Injective (ψ i) := fun i =>
    (MulAut.conj (πB (r i))⁻¹).injective.comp hθinj
  let Y : I → Subgroup (↥X ⧸ GLAPPrimeCore p ↥X) := fun i => (ψ i).range
  let E : I → Subgroup (↥X ⧸ GLAPPrimeCore p ↥X) := fun i => E'.map (ψ i)
  have hYbar : ∀ i, Y i = barX p X (GLBConj ((r i : ↥B) : G) L) := by
    intro i
    rw [barX_gLBConj p (hBX (r i).2) L, ← barTheta_range p hL.1 hL.2.1]
    exact MonoidHom.range_comp _ _
  have hcomp : ∀ i, GLAPComponent p X (GLBConj ((r i : ↥B) : G) L) := by
    intro i
    have h := glaPComponent_gLBConj hL ((r i : ↥B) : G)
    rwa [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer (hBX (r i).2))] at h
  have hYcomm : ∀ i j, i ≠ j → Y i ≤ Subgroup.centralizer (Y j : Set (↥X ⧸ GLAPPrimeCore p ↥X)) := by
    intro i j hij
    have hne : barX p X (GLBConj ((r i : ↥B) : G) L) ≠ barX p X (GLBConj ((r j : ↥B) : G) L) := by
      intro h
      have h1 := glaPComponent_uniqueAux (hcomp i) (hcomp j) h
      have h2 := (gLBConj_eq_iff_mem_normalizer L _ _).1 h1
      apply hij
      rw [← hr i, ← hr j]
      apply QuotientGroup.eq.2
      rw [Subgroup.mem_subgroupOf]
      have h3 : (((r i)⁻¹ * r j : ↥B)) = r j * (r i)⁻¹ := hBc.is_comm.comm _ _
      rw [h3]
      exact ⟨((r j * (r i)⁻¹ : ↥B)).2, h2⟩
    have this : ⁅barX p X (GLBConj ((r i : ↥B) : G) L), barX p X (GLBConj ((r j : ↥B) : G) L)⁆ =
        ⊥ :=
      CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ (hcomp i).2.2.1
        (hcomp j).2.2.1 hne
    rw [← hYbar i, ← hYbar j] at this
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 this
  have hEY : ∀ i, E i ≤ Y i := fun i => Subgroup.map_le_range (ψ i) E'
  have hYz : ∀ i, ∀ y ∈ E i, (∀ y' ∈ Y i, y * y' = y' * y) → y = 1 := by
    intro i y hy hc
    obtain ⟨x, hx, rfl⟩ := hy
    have : x = 1 := hZ x hx fun z => hψ i (by
      rw [map_mul, map_mul]
      exact hc (ψ i z) ⟨z, rfl⟩)
    rw [this, map_one]
  let C0 : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X) := (c0Hom p B L hBX).range
  have hC0Y : ∀ i, C0 ≤ Subgroup.centralizer (Y i : Set (↥X ⧸ GLAPPrimeCore p ↥X)) := by
    intro i
    rintro _ ⟨c, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨z, rfl⟩
    obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk_surjective z
    have hcX : ((c : ↥(centB p B L)) : G) ∈ X := hBX (centB_le p B L c.2)
    have h1 := centB_comm_theta (X := X) hL c.2 hcX ℓ
    have h2 : Commute (c0Hom p B L hBX c) (πB (r i)) := by
      show π _ * π _ = π _ * π _
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      show (c : G) * ((r i : ↥B) : G) = ((r i : ↥B) : G) * (c : G)
      exact congrArg Subtype.val (hBc.is_comm.comm (⟨(c : G), centB_le p B L c.2⟩ : ↥B) (r i))
    have h3 : Commute (c0Hom p B L hBX c) (θ (QuotientGroup.mk ℓ)) := h1
    have h4 : Commute (c0Hom p B L hBX c) (ψ i (QuotientGroup.mk ℓ)) := by
      show Commute _ ((πB (r i))⁻¹ * θ (QuotientGroup.mk ℓ) * (πB (r i))⁻¹⁻¹)
      exact (h2.inv_right.mul_right h3).mul_right h2.inv_right.inv_right
    exact h4.symm.eq
  have hCc : IsMulCommutative ↥(centB p B L) := by
    refine ⟨⟨fun a b => ?_⟩⟩
    have := hBc.is_comm.comm (⟨(a : G), centB_le p B L a.2⟩ : ↥B)
      ⟨(b : G), centB_le p B L b.2⟩
    have h2 : (a : G) * (b : G) = (b : G) * (a : G) := by
      have := congrArg Subtype.val this
      simpa using this
    exact Subtype.ext h2
  have hC : IsMulCommutative C0 ∧ ∀ x ∈ C0, x ^ p = 1 := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨x, hx⟩ := a.2
      obtain ⟨y, hy⟩ := b.2
      apply Subtype.ext
      show (a : ↥X ⧸ GLAPPrimeCore p ↥X) * b = b * a
      rw [← hx, ← hy, ← map_mul, ← map_mul, hCc.is_comm.comm x y]
    · rintro _ ⟨c, rfl⟩
      rw [← map_pow]
      have : c ^ p = 1 := Subtype.ext (hB.2 _ (centB_le p B L c.2))
      rw [this, map_one]
  have hCcard : Nat.card C0 = Nat.card (centB p B L) :=
    (Nat.card_congr (MonoidHom.ofInjective (c0Hom_injective L hBX hB)).toEquiv).symm
  have hE : ∀ i, IsMulCommutative (E i) ∧ (∀ x ∈ E i, x ^ p = 1) ∧ Nat.card (E i) = p ^ q := by
    intro i
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_, ?_⟩
    · obtain ⟨x, hx, hxa⟩ := a.2
      obtain ⟨y, hy, hyb⟩ := b.2
      apply Subtype.ext
      show (a : ↥X ⧸ GLAPPrimeCore p ↥X) * b = b * a
      rw [← hxa, ← hyb, ← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val (hE'.1.is_comm.comm (⟨x, hx⟩ : E') ⟨y, hy⟩)
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hE'.2.1 x hx, map_one]
    · rw [Subgroup.card_map_of_injective (hψ i)]
      exact hE'.2.2
  obtain ⟨Pbar, hPc, hPe, hPcard, hPT⟩ := exists_elemAbelian_join' hp Y E C0 q hYcomm hEY hYz hC0Y hC hE
  have hI : Nonempty I := ⟨1⟩
  obtain ⟨i0⟩ := hI
  let Tbar : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X) := T'.map (ψ i0)
  have hTY : Tbar ≤ Y i0 := Subgroup.map_le_range (ψ i0) T'
  have hTbar : Tbar ≠ ⊥ := fun h => hT'.1 ((Subgroup.map_eq_bot_iff_of_injective T' (hψ i0)).1 h)
  have hTbar2 : IsPGroup 2 Tbar := hT'.2.map (ψ i0)
  have hCT : C0 ≤ Subgroup.centralizer (Tbar : Set (↥X ⧸ GLAPPrimeCore p ↥X)) := fun x hx =>
    Subgroup.centralizer_le hTY (hC0Y i0 hx)
  have hET' : ∀ i, E i ≤ Subgroup.centralizer (Tbar : Set (↥X ⧸ GLAPPrimeCore p ↥X)) := by
    intro i
    by_cases hi : i = i0
    · subst hi
      rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨t, ht, rfl⟩
      have := Subgroup.mem_centralizer_iff.1 (hET hx) t ht
      rw [← map_mul, ← map_mul, this]
    · exact (Subgroup.centralizer_le hTY).trans' (hEY i |>.trans (hYcomm i i0 hi))
  have hPcent := hPT Tbar hCT hET'
  obtain ⟨P, S, hPc', hPe', hPcard', hS, hS2, hPS⟩ := exists_lift_twoLocal hp hp2
    (GLAPPrimeCore p ↥X) (coprime_card_gLAPPrimeCore_aux p ↥X) Pbar Tbar ⟨hPc, hPe⟩
    ⟨hTbar, hTbar2⟩ hPcent
  refine ⟨P, S, hPc', hPe', ?_, hS, hS2, hPS⟩
  have hidx : Fintype.card I = (B ⊓ Subgroup.normalizer (L : Set G)).relIndex B := by
    rw [← Nat.card_eq_fintype_card, Subgroup.relIndex, Subgroup.index_eq_card]
  rw [hPcard', hPcard, hCcard, hidx]

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
