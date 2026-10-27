module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.GLTheoremB.BarXTools

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

theorem exists_mul_mem_fixed_of_coset {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P X : Subgroup G} (hP : IsPGroup p P)
    (hX : ∀ b ∈ P, ∀ x ∈ X, b * x * b⁻¹ ∈ X) (hXp : ¬ p ∣ Nat.card X)
    {g : G} (hg : ∀ b ∈ P, g⁻¹ * (b * g * b⁻¹) ∈ X) :
    ∃ x ∈ X, ∀ b ∈ P, b * (g * x) * b⁻¹ = g * x := by
  let α := {y : G // g⁻¹ * y ∈ X}
  have hstab : ∀ (b : P) (y : α), g⁻¹ * ((b : G) * y.1 * (b : G)⁻¹) ∈ X := by
    intro b y
    have h1 := mul_mem (hg b b.2) (hX b b.2 _ y.2)
    convert h1 using 1
    group
  let _ : MulAction P α :=
    { smul := fun b y => ⟨(b : G) * y.1 * (b : G)⁻¹, hstab b y⟩
      one_smul := fun y => Subtype.ext (by
        change ((1 : P) : G) * y.1 * ((1 : P) : G)⁻¹ = y.1
        simp)
      mul_smul := fun a b y => Subtype.ext (by
        change ((a * b : P) : G) * y.1 * ((a * b : P) : G)⁻¹ =
          (a : G) * ((b : G) * y.1 * (b : G)⁻¹) * (a : G)⁻¹
        simp [mul_assoc]) }
  have hcard : Nat.card α = Nat.card X :=
    Nat.card_congr (Equiv.subtypeEquiv (Equiv.mulLeft g⁻¹) (fun a => Iff.rfl))
  obtain ⟨⟨y, hy⟩, hfix⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card (α := α)
    (by rw [hcard]; exact hXp)
  refine ⟨g⁻¹ * y, hy, fun b hb => ?_⟩
  have h := congrArg Subtype.val (hfix ⟨b, hb⟩)
  have h' : b * y * b⁻¹ = y := h
  calc b * (g * (g⁻¹ * y)) * b⁻¹ = b * y * b⁻¹ := by simp
    _ = y := h'
    _ = g * (g⁻¹ * y) := by simp

theorem centralizer_barX_eq {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {N A : Subgroup G} (hAN : A ≤ N) (hA : IsPGroup p A) :
    Subgroup.centralizer (barX p N A : Set (↥N ⧸ GLAPPrimeCore p ↥N)) =
      barX p N (N ⊓ Subgroup.centralizer (A : Set G)) := by
  have : Fact p.Prime := ⟨hp⟩
  ext y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro hy
    have hcore : ∀ a ∈ A, g⁻¹ * (a * g * a⁻¹) ∈ GLAPPrimeCoreOf p N := by
      intro a ha
      have haN : a ∈ N := hAN ha
      have hmem : (QuotientGroup.mk (⟨a, haN⟩ : ↥N) : ↥N ⧸ GLAPPrimeCore p ↥N) ∈ barX p N A :=
        ⟨⟨a, haN⟩, (Subgroup.mem_subgroupOf).2 ha, rfl⟩
      have h1 := hy _ hmem
      have h2 : (QuotientGroup.mk (g : ↥N) : ↥N ⧸ GLAPPrimeCore p ↥N) =
          QuotientGroup.mk (⟨a, haN⟩ * g * ⟨a, haN⟩⁻¹ : ↥N) := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, h1, mul_assoc, ← QuotientGroup.mk_mul,
          ← QuotientGroup.mk_mul]
        simp
      have h3 := QuotientGroup.eq.1 h2
      exact ⟨_, h3, by simp⟩
    have hX : ∀ b ∈ A, ∀ x ∈ GLAPPrimeCoreOf p N, b * x * b⁻¹ ∈ GLAPPrimeCoreOf p N :=
      fun b hb x hx =>
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_glaPPrimeCoreOf p N (hAN hb)) x).mp hx
    obtain ⟨x, hx, hfix⟩ := exists_mul_mem_fixed_of_coset (p := p) hA hX
      (not_dvd_card_glaPPrimeCoreOf hp N) (g := (g : G)) hcore
    obtain ⟨x', hx', rfl⟩ := hx
    refine ⟨g * x', ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      refine ⟨(g * x').2, ?_⟩
      show _ ∈ Subgroup.centralizer (A : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have := hfix h hh
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
    · rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq.2 (by simpa using hx'))
  · rintro ⟨w, hw, hwy⟩ h hh
    obtain ⟨a, ha, rfl⟩ := hh
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at ha hw
    rw [← hwy, QuotientGroup.mk'_apply]
    change QuotientGroup.mk a * QuotientGroup.mk w = QuotientGroup.mk w * QuotientGroup.mk a
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.1 hw.2 _ ha

theorem card_barX_of_isPGroup {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {N E : Subgroup G} (hEN : E ≤ N) (hE : IsPGroup p E) :
    Nat.card (barX p N E) = Nat.card E := by
  have hfi := injective_barX_comp hp hE hEN
  have hrange : barX p N E = ((QuotientGroup.mk' (GLAPPrimeCore p ↥N)).comp
      (E.subgroupOf N).subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  rw [hrange, ← Nat.card_congr (MonoidHom.ofInjective hfi).toEquiv]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv

theorem elemAbelian_barX {G : Type*} [Group G] [Finite G] {p : ℕ} (_hp : p.Prime)
    {N E : Subgroup G} (_hEN : E ≤ N) (hE : IsElemAbelian p E) :
    IsElemAbelian p (barX p N E) :=
  isElemAbelian_barX hE

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
