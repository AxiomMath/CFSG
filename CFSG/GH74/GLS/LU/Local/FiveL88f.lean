module

public import CFSG.GH74.GLS.LU.Local.FiveL88e
public import CFSG.GH74.GLS.LU.Local.FiveE125b

public section

open Subgroup CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local.Five

section Frame

variable {G : Type} [Group G]

theorem exists_zpowers_of_card_five [Finite G] (A : Subgroup G) (h : Nat.card ↥A = 5) :
    ∃ a : G, A = zpowers a := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : IsCyclic ↥A := isCyclic_of_prime_card h
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥A)
  refine ⟨(g : G), le_antisymm ?_ (Subgroup.zpowers_le.mpr g.2)⟩
  intro y hy
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem exists_frame3 [Finite G] (A B C : Subgroup G) (hA : Nat.card ↥A = 5) (hB : Nat.card ↥B = 5)
    (hC : Nat.card ↥C = 5) (hcomm : ∀ a ∈ A ⊔ B ⊔ C, ∀ b ∈ A ⊔ B ⊔ C, a * b = b * a)
    (hexp : ∀ a ∈ A ⊔ B ⊔ C, a ^ 5 = 1) :
    ∃ x : Fin 3 → G, A = zpowers (x 0) ∧ B = zpowers (x 1) ∧ C = zpowers (x 2) ∧
      Subgroup.closure (Set.range x) = A ⊔ B ⊔ C ∧ (∀ i j, x i * x j = x j * x i) ∧
      ∀ i, x i ^ 5 = 1 := by
  obtain ⟨a, rfl⟩ := exists_zpowers_of_card_five A hA
  obtain ⟨b, rfl⟩ := exists_zpowers_of_card_five B hB
  obtain ⟨c, rfl⟩ := exists_zpowers_of_card_five C hC
  have ha : a ∈ zpowers a ⊔ zpowers b ⊔ zpowers c :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
  have hb : b ∈ zpowers a ⊔ zpowers b ⊔ zpowers c :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))
  have hc : c ∈ zpowers a ⊔ zpowers b ⊔ zpowers c := Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
  have hx : ∀ i, (![a, b, c] : Fin 3 → G) i ∈ zpowers a ⊔ zpowers b ⊔ zpowers c := by
    intro i
    fin_cases i
    · exact ha
    · exact hb
    · exact hc
  refine ⟨![a, b, c], rfl, rfl, rfl, ?_, fun i j => hcomm _ (hx i) _ (hx j), fun i => hexp _ (hx i)⟩
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact hx i
  · refine sup_le (sup_le ?_ ?_) ?_ <;> rw [Subgroup.zpowers_le]
    · exact Subgroup.subset_closure ⟨0, rfl⟩
    · exact Subgroup.subset_closure ⟨1, rfl⟩
    · exact Subgroup.subset_closure ⟨2, rfl⟩

end Frame

section L88f

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ H : Subgroup G}
  {t u w₁ v : G} {X₁ Y : Subgroup G}

theorem Cfg8.transv (c : Cfg8 G p f z S K₁ K₂ t u H w₁ X₁ Y v) {g : G}
    (hg : g ∈ normalizer ((EE v t w₁ X₁ : Subgroup G) : Set G)) :
    cjL g (RR t X₁) ≤ normalizer ((EE v t w₁ X₁ : Subgroup G) : Set G) ∧
    (∀ r ∈ cjL g (RR t X₁), ∀ a ∈ cjL g (XB t X₁), r * a * r⁻¹ = a) ∧
    (∀ r ∈ cjL g (RR t X₁), ∀ e ∈ EE v t w₁ X₁, r * e * r⁻¹ * e⁻¹ ∈ cjL g (XB t X₁)) ∧
    Nat.card ↥(cjL g (RR t X₁) ⊔ EE v t w₁ X₁) = 5 ^ 5 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨r, hr, rfl⟩
    have hr' : (MulAut.conj g).toMonoidHom r = g * r * g⁻¹ := by simp
    rw [hr']
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg (c.RR_N hr)) (Subgroup.inv_mem _ hg)
  · intro r hr a ha
    have hr' : g⁻¹ * r * g ∈ RR t X₁ := mem_cjL.mp hr
    have ha' : g⁻¹ * a * g ∈ XB t X₁ := mem_cjL.mp ha
    have hcomm := c.X2_central _ hr' _ ha'
    calc r * a * r⁻¹ = g * ((g⁻¹ * r * g) * (g⁻¹ * a * g)) * g⁻¹ * r⁻¹ := by group
      _ = g * ((g⁻¹ * a * g) * (g⁻¹ * r * g)) * g⁻¹ * r⁻¹ := by rw [hcomm]
      _ = a := by group
  · intro r hr e he
    have hr' : g⁻¹ * r * g ∈ RR t X₁ := mem_cjL.mp hr
    have he' : g⁻¹ * e * g ∈ EE v t w₁ X₁ := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) e).mp he
      simpa using this
    have h1 := c.z_inv_R.2 _ hr' _ (c.E_le_R2 he')
    rw [mem_cjL]
    have e1 : g⁻¹ * (r * e * r⁻¹ * e⁻¹) * g =
        (g⁻¹ * r * g) * (g⁻¹ * e * g) * (g⁻¹ * r * g)⁻¹ * (g⁻¹ * e * g)⁻¹ := by group
    rw [e1]
    exact h1
  · have h1 : cjL g (RR t X₁) ⊔ EE v t w₁ X₁ = cjL g (RR t X₁ ⊔ EE v t w₁ X₁) := by
      rw [cjL_sup, cjL_eq_of_mem_normalizer hg]
    rw [h1, sup_eq_left.mpr c.E_le_R2, card_cjL, c.R_card]

theorem Cfg8.exists_phi (c : Cfg8 G p f z S K₁ K₂ t u H w₁ X₁ Y v)
    (hbound : Nat.card ↥(normalizer ((EE v t w₁ X₁ : Subgroup G) : Set G)) ≤ 125 * 372000) :
    ∃ phi : ↥(normalizer ((EE v t w₁ X₁ : Subgroup G) : Set G)) →* SL(3, ZMod 5),
      Function.Surjective phi ∧ ∀ m, phi m = 1 ↔ (m : G) ∈ EE v t w₁ X₁ := by
  have hEcomm := c.E_comm c.b86
  have hEexp := c.E_pow c.b86
  obtain ⟨x, hx0, hx1, hx2, hclos, hxcomm, hxord⟩ := exists_frame3 (XB t X₁) (X4 v t X₁)
    (X6 v t w₁ X₁) c.card_X2 c.card_X4 c.card_X6 hEcomm hEexp
  let g : Fin 3 → G := ![1, v, w₁ * v]
  have hgN : ∀ i, g i ∈ normalizer ((EE v t w₁ X₁ : Subgroup G) : Set G) := by
    intro i
    fin_cases i
    · exact Subgroup.one_mem _
    · exact c.v_N
    · exact c.P_N
  have hXi : ∀ i, cjL (g i) (XB t X₁) = zpowers (x i) := by
    intro i
    fin_cases i
    · show cjL 1 (XB t X₁) = _
      rw [cjL_one]; exact hx0
    · show cjL v (XB t X₁) = _
      exact hx1
    · show cjL (w₁ * v) (XB t X₁) = _
      rw [← X6_eq]; exact hx2
  have hxE : ∀ j, x j ∈ EE v t w₁ X₁ := fun j => by
    have : x j ∈ Subgroup.closure (Set.range x) := Subgroup.subset_closure ⟨j, rfl⟩
    rwa [hclos] at this
  have hcard : Nat.card ↥(EE v t w₁ X₁) = 125 := by rw [c.E_card c.b86]; norm_num
  have hC : ∀ m ∈ normalizer ((EE v t w₁ X₁ : Subgroup G) : Set G),
      (∀ e ∈ EE v t w₁ X₁, m * e = e * m) → m ∈ EE v t w₁ X₁ := by
    intro m _ hcm
    have : m ∈ centralizer ((EE v t w₁ X₁ : Subgroup G) : Set G) :=
      Subgroup.mem_centralizer_iff.mpr (fun e he => (hcm e he).symm)
    rwa [c.C_E] at this
  refine normalizer_quot_sl3_of_card (EE v t w₁ X₁) x hclos hxcomm hxord hcard hC
    (fun i => cjL (g i) (RR t X₁)) (fun i => (c.transv (hgN i)).1) ?_ ?_ ?_ hbound
  · intro i r hr
    exact (c.transv (hgN i)).2.1 r hr (x i) (by rw [hXi i]; exact Subgroup.mem_zpowers (x i))
  · intro i r hr j
    have h1 := (c.transv (hgN i)).2.2.1 r hr (x j) (hxE j)
    rw [hXi i] at h1
    obtain ⟨n, hn⟩ := Submonoid.mem_powers_iff _ _ |>.mp (mem_powers_iff_mem_zpowers.mpr h1)
    refine ⟨n, ?_⟩
    have hcij : x i ^ n * x j = x j * x i ^ n := (Commute.pow_left (hxcomm i j) n)
    calc r * x j * r⁻¹ = (r * x j * r⁻¹ * (x j)⁻¹) * x j := by group
      _ = x i ^ n * x j := by rw [← hn]
      _ = x j * x i ^ n := hcij
  · intro i
    exact (c.transv (hgN i)).2.2.2

end L88f

end CFSG.GH74.GLS.LU.Local.Five
