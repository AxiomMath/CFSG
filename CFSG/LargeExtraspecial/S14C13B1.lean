module

public import CFSG.LargeExtraspecial.S14C13B1Defs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LargeExtraspecial.S14C10Apply
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial.S4

section Lifts

variable {Y : Type} [Group Y] {M : Subgroup Y} {M0 : Subgroup M} {t0 : M0}

theorem map_eq_one_iff_of_ker {N : Subgroup Y} {P : Type*} [Group P]
    (hmap : (timmesfeldFStar (centralizer ({t0} : Set M0))).map (inclC M0 t0) = N)
    {Φ : centralizer ({t0} : Set M0) →* Equiv.Perm (Fin 3) × P}
    (hΦk : Φ.ker = timmesfeldFStar (centralizer ({t0} : Set M0)))
    (c : centralizer ({t0} : Set M0)) : Φ c = 1 ↔ inclC M0 t0 c ∈ N := by
  rw [← MonoidHom.mem_ker, hΦk]
  exact mem_fstar_iff hmap c

theorem map_comm_eq_one {P : Type*} [Group P] {A : Type*} [Group A]
    (Φ : A →* Equiv.Perm (Fin 3) × P) {c a : A} {σ : Equiv.Perm (Fin 3)} (ha : Φ a = (σ, 1))
    (hc : (Φ c).1 = 1) : Φ (c * a * c⁻¹ * a⁻¹) = 1 := by
  simp only [map_mul, map_inv, ha]
  ext
  · simp [hc]
  · simp

variable {N : Subgroup Y} {P : Type*} [Group P]
  {Φ : centralizer ({t0} : Set M0) →* Equiv.Perm (Fin 3) × P}

theorem mul_self_mem_of_map_eq
    (hmap : (timmesfeldFStar (centralizer ({t0} : Set M0))).map (inclC M0 t0) = N)
    (hΦk : Φ.ker = timmesfeldFStar (centralizer ({t0} : Set M0)))
    {a : centralizer ({t0} : Set M0)} {σ : Equiv.Perm (Fin 3)} (ha : Φ a = (σ, 1))
    (hσ : σ * σ = 1) : inclC M0 t0 a * inclC M0 t0 a ∈ N := by
  rw [← inclC_mul, ← map_eq_one_iff_of_ker hmap hΦk, map_mul, ha]
  ext <;> simp [hσ]

theorem mul_not_mem_of_map_eq
    (hmap : (timmesfeldFStar (centralizer ({t0} : Set M0))).map (inclC M0 t0) = N)
    (hΦk : Φ.ker = timmesfeldFStar (centralizer ({t0} : Set M0)))
    {a b : centralizer ({t0} : Set M0)} {σ τ : Equiv.Perm (Fin 3)} (ha : Φ a = (σ, 1))
    (hb : Φ b = (τ, 1)) (hστ : σ * τ ≠ 1) : inclC M0 t0 a * inclC M0 t0 b ∉ N := by
  rw [← inclC_mul, ← map_eq_one_iff_of_ker hmap hΦk, map_mul, ha, hb]
  intro h
  exact hστ (congrArg Prod.fst h)

theorem pow_three_mem_of_map_eq
    (hmap : (timmesfeldFStar (centralizer ({t0} : Set M0))).map (inclC M0 t0) = N)
    (hΦk : Φ.ker = timmesfeldFStar (centralizer ({t0} : Set M0)))
    {a b : centralizer ({t0} : Set M0)} {σ τ : Equiv.Perm (Fin 3)} (ha : Φ a = (σ, 1))
    (hb : Φ b = (τ, 1)) (hστ : (σ * τ) ^ 3 = 1) :
    (inclC M0 t0 a * inclC M0 t0 b) ^ 3 ∈ N := by
  rw [← inclC_mul, ← map_pow (inclC M0 t0), ← map_eq_one_iff_of_ker hmap hΦk, map_pow, map_mul,
    ha, hb]
  refine Prod.ext ?_ ?_
  · simpa using hστ
  · simp

theorem comm_mem_of_map_eq {R : Subgroup Y} (hR0 : R ≤ Ct0 M0 ((t0 : M) : Y))
    (hmap : (timmesfeldFStar (centralizer ({t0} : Set M0))).map (inclC M0 t0) = N)
    (hΦk : Φ.ker = timmesfeldFStar (centralizer ({t0} : Set M0)))
    (hK1 : ∀ c ∈ R.comap (inclC M0 t0), (Φ c).1 = 1)
    {a : centralizer ({t0} : Set M0)} {σ : Equiv.Perm (Fin 3)} (ha : Φ a = (σ, 1)) :
    ∀ r ∈ R, inclC M0 t0 a * r * (inclC M0 t0 a)⁻¹ * r⁻¹ ∈ N := by
  intro r hr
  rw [← map_comap_inclC hR0] at hr
  obtain ⟨k, hk, hkr⟩ := hr
  rw [← hkr, ← inclC_inv, ← inclC_mul, ← inclC_inv, ← inclC_mul, ← inclC_mul,
    ← map_eq_one_iff_of_ker hmap hΦk]
  simp only [map_mul, map_inv, ha]
  ext
  · simp [hK1 k hk]
  · simp

theorem comm_mem_of_fst_eq_one
    (hmap : (timmesfeldFStar (centralizer ({t0} : Set M0))).map (inclC M0 t0) = N)
    (hΦk : Φ.ker = timmesfeldFStar (centralizer ({t0} : Set M0)))
    {c a : centralizer ({t0} : Set M0)} {σ : Equiv.Perm (Fin 3)} (ha : Φ a = (σ, 1))
    (hc : (Φ c).1 = 1) :
    inclC M0 t0 c * inclC M0 t0 a * (inclC M0 t0 c)⁻¹ * (inclC M0 t0 a)⁻¹ ∈ N := by
  rw [← inclC_mul, ← inclC_inv, ← inclC_mul, ← inclC_inv, ← inclC_mul,
    ← map_eq_one_iff_of_ker hmap hΦk]
  exact map_comm_eq_one Φ ha hc

theorem mem_of_fst_eq_one_of_sym3 {R : Subgroup Y} (hΦs : Function.Surjective Φ)
    (hmap : (timmesfeldFStar (centralizer ({t0} : Set M0))).map (inclC M0 t0) = N)
    (hΦk : Φ.ker = timmesfeldFStar (centralizer ({t0} : Set M0)))
    (hY : ∀ α β : centralizer ({t0} : Set M0), Φ α = (Equiv.swap 0 1, 1) →
      Φ β = (Equiv.swap 1 2, 1) → ∀ y ∈ M ⊓ centralizer ({((t0 : M) : Y)} : Set Y),
        y * inclC M0 t0 α * y⁻¹ * (inclC M0 t0 α)⁻¹ ∈ N →
        y * inclC M0 t0 β * y⁻¹ * (inclC M0 t0 β)⁻¹ ∈ N → y ∈ R) :
    ∀ c, (Φ c).1 = 1 → inclC M0 t0 c ∈ R := by
  intro c hc
  obtain ⟨α, hα⟩ := hΦs (Equiv.swap 0 1, 1)
  obtain ⟨β, hβ⟩ := hΦs (Equiv.swap 1 2, 1)
  exact hY α β hα hβ _ (inclC_mem c) (comm_mem_of_fst_eq_one hmap hΦk hα hc)
    (comm_mem_of_fst_eq_one hmap hΦk hβ hc)

end Lifts

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem b1_ybar (hYb : Ybar13Stmt) [IsSimpleGroup G] {t0 : Mbar0 S}
    (hSt : Stage S g ((t0 : S.Mbar) : S.O))
    (hocc : Config.omegaPlus8b.Occurs S g ((t0 : S.Mbar) : S.O))
    (hext : IsExtraspecialPGroup 2 (Nbar S g ((t0 : S.Mbar) : S.O)))
    (h7 : Concl14_7 S g ((t0 : S.Mbar) : S.O))
    (hF : FCt S ((t0 : S.Mbar) : S.O) = Nbar S g ((t0 : S.Mbar) : S.O))
    (hR0 : Rbar S g ((t0 : S.Mbar) : S.O) ≤ Ct0 (Mbar0 S) ((t0 : S.Mbar) : S.O))
    (hmap : (timmesfeldFStar (centralizer ({t0} : Set (Mbar0 S)))).map (inclC (Mbar0 S) t0) =
      Nbar S g ((t0 : S.Mbar) : S.O))
    {P : Type} [Group P] {Φ : centralizer ({t0} : Set (Mbar0 S)) →* Equiv.Perm (Fin 3) × P}
    (hΦk : Φ.ker = timmesfeldFStar (centralizer ({t0} : Set (Mbar0 S))))
    (hK1 : ∀ c ∈ (Rbar S g ((t0 : S.Mbar) : S.O)).comap (inclC (Mbar0 S) t0), (Φ c).1 = 1)
    {α β : centralizer ({t0} : Set (Mbar0 S))} (hα : Φ α = (Equiv.swap 0 1, 1))
    (hβ : Φ β = (Equiv.swap 1 2, 1)) :
    ∀ y ∈ Ct S ((t0 : S.Mbar) : S.O),
      y * inclC (Mbar0 S) t0 α * y⁻¹ * (inclC (Mbar0 S) t0 α)⁻¹ ∈
        Nbar S g ((t0 : S.Mbar) : S.O) →
      y * inclC (Mbar0 S) t0 β * y⁻¹ * (inclC (Mbar0 S) t0 β)⁻¹ ∈
        Nbar S g ((t0 : S.Mbar) : S.O) → y ∈ Rbar S g ((t0 : S.Mbar) : S.O) :=
  hYb G S g _ hSt hocc hext h7 hF _ (inclC_mem α) _ (inclC_mem β)
    (mul_self_mem_of_map_eq hmap hΦk hα (by decide))
    (mul_self_mem_of_map_eq hmap hΦk hβ (by decide))
    (mul_not_mem_of_map_eq hmap hΦk hα hβ (by decide))
    (pow_three_mem_of_map_eq hmap hΦk hα hβ (by decide))
    (fun r hr => ⟨comm_mem_of_map_eq hR0 hmap hΦk hK1 hα r hr,
      comm_mem_of_map_eq hR0 hmap hΦk hK1 hβ r hr⟩)

theorem b1_structure (hYb : Ybar13Stmt) [IsSimpleGroup G] {t0 : Mbar0 S}
    (hSt : Stage S g ((t0 : S.Mbar) : S.O))
    (hocc : Config.omegaPlus8b.Occurs S g ((t0 : S.Mbar) : S.O))
    (hext : IsExtraspecialPGroup 2 (Nbar S g ((t0 : S.Mbar) : S.O)))
    (h7 : Concl14_7 S g ((t0 : S.Mbar) : S.O))
    (hF : FCt S ((t0 : S.Mbar) : S.O) = Nbar S g ((t0 : S.Mbar) : S.O))
    (hR0 : Rbar S g ((t0 : S.Mbar) : S.O) ≤ Ct0 (Mbar0 S) ((t0 : S.Mbar) : S.O))
    (hmap : (timmesfeldFStar (centralizer ({t0} : Set (Mbar0 S)))).map (inclC (Mbar0 S) t0) =
      Nbar S g ((t0 : S.Mbar) : S.O))
    {P : Type} [Group P] (Φ : centralizer ({t0} : Set (Mbar0 S)) →* Equiv.Perm (Fin 3) × P)
    (hΦs : Function.Surjective Φ)
    (hΦk : Φ.ker = timmesfeldFStar (centralizer ({t0} : Set (Mbar0 S))))
    (hK1 : ∀ c ∈ (Rbar S g ((t0 : S.Mbar) : S.O)).comap (inclC (Mbar0 S) t0), (Φ c).1 = 1) :
    ∀ c, (Φ c).1 = 1 → inclC (Mbar0 S) t0 c ∈ Rbar S g ((t0 : S.Mbar) : S.O) :=
  mem_of_fst_eq_one_of_sym3 hΦs hmap hΦk fun _ _ hα hβ =>
    b1_ybar hYb hSt hocc hext h7 hF hR0 hmap hΦk hK1 hα hβ

end CFSG.LargeExtraspecial.S14
