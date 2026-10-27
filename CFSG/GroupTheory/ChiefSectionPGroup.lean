module

public import CFSG.GroupTheory.Commutator.ThreeSubgroupsModNormal
public import CFSG.GroupTheory.CoprimeActionSupport.FiniteMinimalSubgroup
public import CFSG.GroupTheory.HuppertProduct.Quotient
public import CFSG.GroupTheory.SteinbergCBFTPSolvable

public section

namespace CFSG.GroupTheory

open scoped commutatorElement

theorem le_normalizer_closure_pow {G : Type*} [Group G] {N X : Subgroup G} {n : ℕ}
    (hNX : N ≤ Subgroup.normalizer (X : Set G)) :
    N ≤ Subgroup.normalizer (Subgroup.closure {x ^ n | x ∈ X} : Set G) := by
  let P : Subgroup G := Subgroup.closure {x ^ n | x ∈ X}
  have key : ∀ g ∈ N, ∀ x ∈ P, g * x * g⁻¹ ∈ P := by
    intro g hg x hx
    refine Subgroup.closure_induction (fun y hy => ?_) ?_ (fun a b _ _ ha hb => ?_)
      (fun a _ ha => ?_) hx
    · obtain ⟨z, hz, rfl⟩ := hy
      have hzX : g * z * g⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hNX hg) z).mp hz
      rw [← conj_pow]
      exact Subgroup.subset_closure ⟨g * z * g⁻¹, hzX, rfl⟩
    · simpa using P.one_mem
    · rw [show g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) by group]
      exact P.mul_mem ha hb
    · rw [show g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ by group]
      exact P.inv_mem ha
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key h hh x
  · intro hx
    have := key h⁻¹ (N.inv_mem hh) (h * x * h⁻¹) hx
    simpa [mul_assoc] using this

theorem commutator_sup_lt_of_isPGroup {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {X Q V : Subgroup G} (hXQ : X ≤ Q) (hQ : IsPGroup p Q)
    (hQX : Q ≤ Subgroup.normalizer (X : Set G))
    (hQV : Q ≤ Subgroup.normalizer (V : Set G)) (hVX : V ≤ X) (hne : V ≠ X) :
    ⁅X, Q⁆ ⊔ V < X := by
  have hcommX : ⁅X, Q⁆ ≤ X := Subgroup.le_normalizer_iff_commutator_le_left.mp hQX
  have hcommQ : ⁅X, Q⁆ ≤ Q := hcommX.trans hXQ
  have hVQ : V ≤ Q := hVX.trans hXQ
  refine lt_of_le_of_ne (sup_le hcommX hVX) ?_
  intro hEq
  let Qg := ↥Q
  let Xq : Subgroup Qg := X.subgroupOf Q
  let Vq : Subgroup Qg := V.subgroupOf Q
  haveI hVqN : Vq.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hQV
  have hVqcomm : ⁅Vq, ⊤⁆ ≤ Vq := Subgroup.commutator_le_left (H₁ := Vq) (H₂ := ⊤)
  let C : Subgroup Qg := ⁅Xq, ⊤⁆
  have hmap : C.map Q.subtype = ⁅X, Q⁆ := by
    rw [Subgroup.map_commutator]
    congr 1
    · exact Subgroup.map_subgroupOf_eq_of_le hXQ
    · simpa [MonoidHom.range_eq_map] using (Q.range_subtype : Q.subtype.range = Q)
  have hcommSub : ⁅X, Q⁆.subgroupOf Q = C :=
    Subgroup.map_injective (f := Q.subtype) Q.subtype_injective
      (by rw [Subgroup.map_subgroupOf_eq_of_le hcommQ, hmap])
  have hXq_eq : Xq = C ⊔ Vq := by
    have h1 : (⁅X, Q⁆ ⊔ V).subgroupOf Q = Xq := by rw [hEq]
    have h2 : (⁅X, Q⁆ ⊔ V).subgroupOf Q = ⁅X, Q⁆.subgroupOf Q ⊔ Vq :=
      Subgroup.subgroupOf_sup hcommQ hVQ
    rw [← h1, h2, hcommSub]
  have hnil : Group.IsNilpotent Qg := hQ.isNilpotent
  obtain ⟨n, hn⟩ := (Subgroup.nilpotent_iff_lowerCentralSeries (G := Qg)).mp hnil
  have key : ∀ i, Xq ≤ (⊤ : Subgroup Qg).lowerCentralSeries i ⊔ Vq := by
    intro i
    induction i with
    | zero =>
        rw [Subgroup.lowerCentralSeries_zero]
        simp
    | succ i ih =>
        calc Xq = C ⊔ Vq := hXq_eq
          _ ≤ ⁅(⊤ : Subgroup Qg).lowerCentralSeries i ⊔ Vq, ⊤⁆ ⊔ Vq :=
              sup_le_sup (Subgroup.commutator_mono (H₁ := Xq) (H₂ := ⊤) ih le_rfl) le_rfl
          _ = (⊤ : Subgroup Qg).lowerCentralSeries (i + 1) ⊔ Vq := by
              rw [Subgroup.commutator_sup_right, Subgroup.lowerCentralSeries_succ,
                sup_assoc, sup_eq_right.mpr hVqcomm]
  have hXV : X ≤ V := by
    have hle : Xq ≤ Vq := by simpa [hn] using key n
    intro x hx
    exact hle (show (⟨x, hXQ hx⟩ : Qg) ∈ Xq from hx)
  exact hne (le_antisymm hVX hXV)

theorem sup_pow_closure_lt_of_isPGroup {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {X V : Subgroup G} (hVX : V ≤ X) (hX : IsPGroup p X) (hne : V ≠ X) :
    V ⊔ Subgroup.closure {x ^ p | x ∈ X} < X := by
  have hPX : Subgroup.closure {x ^ p | x ∈ X} ≤ X := by
    refine (Subgroup.closure_le (K := X)).2 ?_
    rintro _ ⟨x, hx, rfl⟩
    exact X.pow_mem hx p
  refine lt_of_le_of_ne (sup_le hVX hPX) ?_
  intro hEq
  let Xg := ↥X
  let Vx : Subgroup Xg := V.subgroupOf X
  let T : Set Xg := Set.range fun x : Xg => x ^ p
  let : Fact (IsPGroup p Xg) := ⟨hX⟩
  have hT : Subgroup.closure T ≤ frattini Xg := by
    refine (Subgroup.closure_le (K := frattini Xg)).2 ?_
    rintro _ ⟨x, rfl⟩
    exact CFSG.pth_power_mem_frattini_of_isPGroup (R := Xg) (p := p) x
  have hmap : (Subgroup.closure T).map X.subtype = Subgroup.closure {x ^ p | x ∈ X} := by
    rw [MonoidHom.map_closure]
    congr 1
    ext z
    constructor
    · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
      exact ⟨(x : G), x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩ ^ p, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
  have hcl : (Subgroup.closure {x ^ p | x ∈ X}).subgroupOf X = Subgroup.closure T := by
    refine le_antisymm ?_ ?_
    · intro z hz
      have hz' : (z : G) ∈ (Subgroup.closure T).map X.subtype := by rwa [hmap]
      obtain ⟨w, hw, hwz⟩ := hz'
      rwa [← Subtype.ext hwz]
    · refine (Subgroup.closure_le (K := (Subgroup.closure {x ^ p | x ∈ X}).subgroupOf X)).2 ?_
      rintro _ ⟨x, rfl⟩
      exact Subgroup.subset_closure ⟨(x : G), x.2, rfl⟩
  have hsub : (V ⊔ Subgroup.closure {x ^ p | x ∈ X}).subgroupOf X = Vx ⊔ Subgroup.closure T := by
    rw [Subgroup.subgroupOf_sup hVX hPX, hcl]
  have htop : Vx ⊔ Subgroup.closure T = ⊤ := by
    rw [← hsub, hEq]
    simp
  have hfratt : Vx ⊔ frattini Xg = ⊤ :=
    top_le_iff.mp (htop ▸ sup_le_sup le_rfl hT)
  have hVx : Vx = ⊤ := CFSG.lemma_1_7_a (R := Xg) (p := p) Vx hfratt
  have hVeqX : V = X := by
    refine le_antisymm hVX ?_
    intro x hx
    exact (show (⟨x, hx⟩ : Xg) ∈ Vx from by rw [hVx]; exact Subgroup.mem_top _)
  exact hne hVeqX

private theorem not_commutator_le_of_perfect {G : Type*} [Group G] {H L X Y V : Subgroup G}
    (hLH : L ≤ H) (hXH : X ≤ H) (hVH : V ≤ H) (hHV : H ≤ Subgroup.normalizer (V : Set G))
    (hL : ⁅L, L⁆ = L) (hXL : ¬ ⁅X, L⁆ ≤ V) (hYL : ⁅Y, L⁆ ≤ V) : ¬ ⁅X, L⁆ ≤ Y := by
  intro hXY
  apply hXL
  have h1 : ⁅⁅L, X⁆, L⁆ ≤ V := by
    rw [Subgroup.commutator_comm L X]
    exact (Subgroup.commutator_mono hXY le_rfl).trans hYL
  have h2 : ⁅⁅X, L⁆, L⁆ ≤ V := (Subgroup.commutator_mono hXY le_rfl).trans hYL
  have h3 : ⁅⁅L, L⁆, X⁆ ≤ V :=
    commutator_commutator_le_of_rotate_normal (M := H) (A := L) (B := X) (N := V)
      hLH hXH hVH hHV h1 h2
  rw [hL] at h3
  rw [Subgroup.commutator_comm X L]
  exact h3

theorem exists_section_of_not_commutator_le {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {H L Q P V : Subgroup G} (hLH : L ≤ H) (hQH : Q ≤ H) (hVP : V ≤ P)
    (hPQ : P ≤ Q) (hQ : IsPGroup p Q) (hHP : H ≤ Subgroup.normalizer (P : Set G))
    (hHQ : H ≤ Subgroup.normalizer (Q : Set G))
    (hHV : H ≤ Subgroup.normalizer (V : Set G)) (hL : ⁅L, L⁆ = L)
    (hPL : ¬ ⁅P, L⁆ ≤ V) :
    ∃ X Y : Subgroup G, V ≤ Y ∧ Y ≤ X ∧ X ≤ P ∧ H ≤ Subgroup.normalizer (X : Set G) ∧
      H ≤ Subgroup.normalizer (Y : Set G) ∧ (∀ x ∈ X, x ^ p ∈ Y) ∧ ⁅X, Q⁆ ≤ Y ∧
      ¬ ⁅X, L⁆ ≤ Y := by
  classical
  obtain ⟨X, ⟨hVX, hXP, hHX, hXL⟩, hXmin⟩ :=
    CoprimeActionSupport.FiniteMinimalSubgroup.exists_minimal_subgroup
      (fun W => V ≤ W ∧ W ≤ P ∧ H ≤ Subgroup.normalizer (W : Set G) ∧ ¬ ⁅W, L⁆ ≤ V)
      ⟨P, hVP, le_rfl, hHP, hPL⟩
  have hXQ : X ≤ Q := hXP.trans hPQ
  have hXH : X ≤ H := hXQ.trans hQH
  have hVH : V ≤ H := hVP.trans (hPQ.trans hQH)
  have hQNX : Q ≤ Subgroup.normalizer (X : Set G) := hQH.trans hHX
  have hQNV : Q ≤ Subgroup.normalizer (V : Set G) := hQH.trans hHV
  have hVL : ⁅V, L⁆ ≤ V :=
    (Subgroup.commutator_mono le_rfl hLH).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp hHV)
  have hVne : V ≠ X := by
    intro h
    exact hXL (by rw [← h]; exact hVL)
  have hY1lt : ⁅X, Q⁆ ⊔ V < X := commutator_sup_lt_of_isPGroup hXQ hQ hQNX hQNV hVX hVne
  let Y1 : Subgroup G := ⁅X, Q⁆ ⊔ V
  let PX : Subgroup G := Subgroup.closure {x ^ p | x ∈ X}
  let Y : Subgroup G := Y1 ⊔ PX
  have hXp : IsPGroup p X := hQ.to_le hXQ
  have hYlt : Y < X :=
    sup_pow_closure_lt_of_isPGroup (X := X) (V := Y1) hY1lt.le hXp hY1lt.ne
  have hYX : Y ≤ X := hYlt.le
  have hYP : Y ≤ P := hYX.trans hXP
  have hVY : V ≤ Y := (le_sup_right : V ≤ Y1).trans (le_sup_left : Y1 ≤ Y)
  have hHcomm : H ≤ Subgroup.normalizer ((⁅X, Q⁆ : Subgroup G) : Set G) :=
    FT63ChII.le_normalizer_commutator hHX hHQ
  have hHY1 : H ≤ Subgroup.normalizer (Y1 : Set G) :=
    HuppertProduct.le_normalizer_sup (A := ⁅X, Q⁆) (B := V) hHcomm hHV
  have hHPX : H ≤ Subgroup.normalizer (PX : Set G) := by
    exact le_normalizer_closure_pow (n := p) hHX
  have hHY : H ≤ Subgroup.normalizer (Y : Set G) :=
    HuppertProduct.le_normalizer_sup (A := Y1) (B := PX) hHY1 hHPX
  have hYL : ⁅Y, L⁆ ≤ V := by
    by_contra h
    exact hYlt.ne (hXmin Y ⟨hVY, hYP, hHY, h⟩ hYX)
  refine ⟨X, Y, hVY, hYX, hXP, hHX, hHY, ?_, ?_,
    not_commutator_le_of_perfect hLH hXH hVH hHV hL hXL hYL⟩
  · intro x hx
    exact (le_sup_right : PX ≤ Y) (Subgroup.subset_closure ⟨x, hx, rfl⟩)
  · exact (le_sup_left : ⁅X, Q⁆ ≤ Y1).trans (le_sup_left : Y1 ≤ Y)

end CFSG.GroupTheory
