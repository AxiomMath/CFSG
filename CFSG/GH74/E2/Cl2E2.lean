module

public import CFSG.GH74.E2.Cl2Cl3
public import CFSG.GH74.E2.Cl2E2Alg

public section

namespace CFSG.GH74.E2

open Subgroup
open scoped commutatorElement

namespace E2Aux

section Calculus

variable {G : Type*} [Group G]

theorem comm_mul_left (g g' h : G) : ⁅g * g', h⁆ = g * ⁅g', h⁆ * g⁻¹ * ⁅g, h⁆ := by
  simp only [commutatorElement_def]
  group

theorem comm_mul_right (g h h' : G) : ⁅g, h * h'⁆ = ⁅g, h⁆ * (h * ⁅g, h'⁆ * h⁻¹) := by
  simp only [commutatorElement_def]
  group

variable (hz : ∀ g h : G, ⁅g, h⁆ ∈ Subgroup.center G)
include hz

theorem cm_left (g g' h : G) : ⁅g * g', h⁆ = ⁅g, h⁆ * ⁅g', h⁆ := by
  rw [comm_mul_left]
  have h1 : g * ⁅g', h⁆ * g⁻¹ = ⁅g', h⁆ := by
    have := Subgroup.mem_center_iff.1 (hz g' h) g
    calc g * ⁅g', h⁆ * g⁻¹ = (⁅g', h⁆ * g) * g⁻¹ := by rw [this]
      _ = ⁅g', h⁆ := by group
  rw [h1]
  exact Subgroup.mem_center_iff.1 (hz g h) _

theorem cm_right (g h h' : G) : ⁅g, h * h'⁆ = ⁅g, h⁆ * ⁅g, h'⁆ := by
  rw [comm_mul_right]
  have h1 : h * ⁅g, h'⁆ * h⁻¹ = ⁅g, h'⁆ := by
    have := Subgroup.mem_center_iff.1 (hz g h') h
    calc h * ⁅g, h'⁆ * h⁻¹ = (⁅g, h'⁆ * h) * h⁻¹ := by rw [this]
      _ = ⁅g, h'⁆ := by group
  rw [h1]

theorem cm_inv_left (g h : G) : ⁅g⁻¹, h⁆ = ⁅g, h⁆⁻¹ := by
  have h1 : ⁅g⁻¹ * g, h⁆ = 1 := by
    simp [commutatorElement_def]
  rw [cm_left hz] at h1
  exact eq_inv_of_mul_eq_one_left h1

theorem cm_inv_right (g h : G) : ⁅g, h⁻¹⁆ = ⁅g, h⁆⁻¹ := by
  have h1 : ⁅g, h⁻¹ * h⁆ = 1 := by
    simp [commutatorElement_def]
  rw [cm_right hz] at h1
  exact eq_inv_of_mul_eq_one_left h1

theorem dsub_le_closure {x₁ x₂ y₁ y₂ : G}
    (hgen : Subgroup.closure ({x₁, x₂, y₁, y₂} : Set G) = ⊤) :
    ⁅(⊤ : Subgroup G), ⊤⁆ ≤ Subgroup.closure
      ({⁅x₁, x₂⁆, ⁅y₁, y₂⁆, ⁅x₁, y₁⁆, ⁅x₁, y₂⁆, ⁅x₂, y₁⁆, ⁅x₂, y₂⁆} : Set G) := by
  set S := Subgroup.closure
    ({⁅x₁, x₂⁆, ⁅y₁, y₂⁆, ⁅x₁, y₁⁆, ⁅x₁, y₂⁆, ⁅x₂, y₁⁆, ⁅x₂, y₂⁆} : Set G) with hS
  have invm : ∀ a b : G, ⁅a, b⁆ ∈ S → ⁅b, a⁆ ∈ S := fun a b h => by
    rw [← commutatorElement_inv]
    exact S.inv_mem h
  have g1 : ⁅x₁, x₂⁆ ∈ S := Subgroup.subset_closure (by simp)
  have g2 : ⁅y₁, y₂⁆ ∈ S := Subgroup.subset_closure (by simp)
  have g3 : ⁅x₁, y₁⁆ ∈ S := Subgroup.subset_closure (by simp)
  have g4 : ⁅x₁, y₂⁆ ∈ S := Subgroup.subset_closure (by simp)
  have g5 : ⁅x₂, y₁⁆ ∈ S := Subgroup.subset_closure (by simp)
  have g6 : ⁅x₂, y₂⁆ ∈ S := Subgroup.subset_closure (by simp)
  have hself : ∀ a : G, ⁅a, a⁆ ∈ S := fun a => by
    rw [commutatorElement_self]
    exact S.one_mem
  have hmem : ∀ p q : G, p ∈ ({x₁, x₂, y₁, y₂} : Set G) → q ∈ ({x₁, x₂, y₁, y₂} : Set G) →
      ⁅p, q⁆ ∈ S := by
    intro p q hp hq
    rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
      first | exact hself _ | exact g1 | exact g2 | exact g3 | exact g4 | exact g5 | exact g6 |
        exact invm _ _ g1 | exact invm _ _ g2 | exact invm _ _ g3 | exact invm _ _ g4 |
        exact invm _ _ g5 | exact invm _ _ g6
  have hstep2 : ∀ g q : G, q ∈ ({x₁, x₂, y₁, y₂} : Set G) → ⁅g, q⁆ ∈ S := by
    intro g q hq
    have hg : g ∈ Subgroup.closure ({x₁, x₂, y₁, y₂} : Set G) := by
      rw [hgen]
      trivial
    induction hg using Subgroup.closure_induction with
    | mem p hp => exact hmem p q hp hq
    | one =>
      rw [show ⁅(1 : G), q⁆ = 1 by simp [commutatorElement_def]]
      exact S.one_mem
    | mul g g' _ _ hg hg' =>
      rw [cm_left hz]
      exact S.mul_mem hg hg'
    | inv g _ hg =>
      rw [cm_inv_left hz]
      exact S.inv_mem hg
  have hstep3 : ∀ g h : G, ⁅g, h⁆ ∈ S := by
    intro g h
    have hh : h ∈ Subgroup.closure ({x₁, x₂, y₁, y₂} : Set G) := by
      rw [hgen]
      trivial
    induction hh using Subgroup.closure_induction with
    | mem q hq => exact hstep2 g q hq
    | one =>
      rw [show ⁅g, (1 : G)⁆ = 1 by simp [commutatorElement_def]]
      exact S.one_mem
    | mul h h' _ _ hh hh' =>
      rw [cm_right hz]
      exact S.mul_mem hh hh'
    | inv h _ hh =>
      rw [cm_inv_right hz]
      exact S.inv_mem hh
  exact Subgroup.commutator_le.2 (fun g _ h _ => hstep3 g h)

omit hz in
theorem comm_central_one {c : G} (hc : c ∈ Subgroup.center G) (g : G) : ⁅g, c⁆ = 1 :=
  commutatorElement_eq_one_iff_commute.2 (Subgroup.mem_center_iff.1 hc g)

theorem cyc {γ : MulAut G} {w : G} (hε : eps γ w ∈ Subgroup.center G) :
    γ ⁅w, γ w⁆ = ⁅w, γ w⁆ := by
  have hγγ : γ (γ w) = (w * γ w)⁻¹ * eps γ w := by
    simp only [eps]
    group
  rw [map_commutatorElement, hγγ, cm_right hz, comm_central_one hε, mul_one, cm_inv_right hz,
    cm_right hz, commutatorElement_self, mul_one, commutatorElement_inv]

theorem act_second {β : MulAut G} {y g : G} (hg : β g = g) (hεy : eps β y ∈ Subgroup.center G) :
    β ⁅g, y⁆ = ⁅g, β y⁆ ∧ β ⁅g, β y⁆ = (⁅g, y⁆ * ⁅g, β y⁆)⁻¹ := by
  have hββ : β (β y) = (y * β y)⁻¹ * eps β y := by
    simp only [eps]
    group
  refine ⟨by rw [map_commutatorElement, hg], ?_⟩
  rw [map_commutatorElement, hg, hββ, cm_right hz, comm_central_one hεy, mul_one, cm_inv_right hz,
    cm_right hz]

end Calculus

theorem dsub_map_mem {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Surjective f) {d : G} (hd : d ∈ dsub G) : f d ∈ dsub G' := by
  have h1 : f d ∈ (dsub G).map f := Subgroup.mem_map_of_mem f hd
  have h2 : (dsub G).map f = dsub G' := by
    unfold dsub
    rw [Subgroup.map_commutator, Subgroup.map_top, MonoidHom.range_eq_top.2 hf]
  rwa [h2] at h1

end E2Aux

section Main

variable {Q : Type*} [Group Q] [Finite Q] {a b : MulAut Q} {N : Subgroup Q}

theorem e2_main (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) {u : Q} (hu : u ∈ dsub Q)
    (h1 : b u * u⁻¹ ∈ N) (h2 : eps a u ∈ N) : u ∈ N := by
  classical
  have ha3 := h.bpair.a_cube
  have hb3 := h.bpair.b_cube
  have hab := h.bpair.comm
  have hNn : N.Normal := Subgroup.normal_of_le_center h.N_central
  have hNa : ∀ x, a x ∈ N ↔ x ∈ N := by
    intro x
    refine ⟨fun hx => ?_, h.N_inva x⟩
    have h3 : a (a (a x)) = x := Cl2Wt.cube_apply ha3 x
    rw [← h3]
    exact h.N_inva _ (h.N_inva _ hx)
  have hNb : ∀ x, b x ∈ N ↔ x ∈ N := by
    intro x
    refine ⟨fun hx => ?_, h.N_invb x⟩
    have h3 : b (b (b x)) = x := Cl2Wt.cube_apply hb3 x
    rw [← h3]
    exact h.N_invb _ (h.N_invb _ hx)
  let mk : Q →* Q ⧸ N := QuotientGroup.mk' N
  have hmk : Function.Surjective mk := QuotientGroup.mk'_surjective N
  let α : MulAut (Q ⧸ N) := quotAut a N hNa
  let β : MulAut (Q ⧸ N) := quotAut b N hNb
  have hα : ∀ q : Q, α (mk q) = mk (a q) := fun q => quotAut_mk a N hNa q
  have hβ : ∀ q : Q, β (mk q) = mk (b q) := fun q => quotAut_mk b N hNb q
  have hG2 : IsPGroup 2 (Q ⧸ N) := hQ.to_quotient N
  have hαβ : ∀ g : Q ⧸ N, α (β g) = β (α g) := by
    intro g
    obtain ⟨q, rfl⟩ := hmk g
    have h3 : a (b q) = b (a q) := by
      have := congrArg (fun f : MulAut Q => f q) hab
      simpa [MulAut.mul_apply] using this
    rw [hβ, hα, hα, hβ, h3]
  have hz : ∀ g k : Q ⧸ N, ⁅g, k⁆ ∈ Subgroup.center (Q ⧸ N) := by
    intro g k
    obtain ⟨g', rfl⟩ := hmk g
    obtain ⟨k', rfl⟩ := hmk k
    rw [Subgroup.mem_center_iff]
    intro l
    obtain ⟨l', rfl⟩ := hmk l
    have hc : ⁅g', k'⁆ ∈ dsub Q :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    have h4 : ⁅⁅g', k'⁆, l'⁆ ∈ N := h.comm_mem hQ hc l'
    have h5 : ⁅mk ⁅g', k'⁆, mk l'⁆ = 1 := by
      rw [← map_commutatorElement, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact h4
    have h6 := (commutatorElement_eq_one_iff_commute.1 h5).eq
    rw [← map_commutatorElement]
    exact h6.symm
  obtain ⟨x, hx, y, hy, hgen⟩ := BPair.exists_gens hQ h.four h.bpair
  have hy' : a y = y := commSub_le_fixSub_a h.bpair hy
  have hx' : b x = x := hx
  have hDz : dsub (Q ⧸ N) ≤ Subgroup.center (Q ⧸ N) :=
    Subgroup.commutator_le.2 (fun g _ k _ => hz g k)
  have hεx : eps α (mk x) ∈ Subgroup.center (Q ⧸ N) := by
    have h3 : eps α (mk x) = mk (eps a x) := by
      simp only [eps, map_mul, hα]
    rw [h3]
    exact hDz (E2Aux.dsub_map_mem mk hmk (Cl3.eps_a_mem_dsub hQ h hx))
  have hεy : eps β (mk y) ∈ Subgroup.center (Q ⧸ N) := by
    have h3 : eps β (mk y) = mk (eps b y) := by
      simp only [eps, map_mul, hβ]
    rw [h3]
    exact hDz (E2Aux.dsub_map_mem mk hmk (Cl3.eps_b_mem_dsub hQ h hy'))
  have hβx : β (mk x) = mk x := by rw [hβ, hx']
  have hαy : α (mk y) = mk y := by rw [hα, hy']
  have hgenG : Subgroup.closure ({mk x, α (mk x), mk y, β (mk y)} : Set (Q ⧸ N)) = ⊤ := by
    have h3 := MonoidHom.map_closure mk ({x, a x, y, b y} : Set Q)
    rw [hgen, Subgroup.map_top, MonoidHom.range_eq_top.2 hmk] at h3
    simp only [Set.image_insert_eq, Set.image_singleton] at h3
    rw [hα, hβ]
    exact h3.symm
  let X : Fin 2 → Q ⧸ N := ![mk x, α (mk x)]
  let Y : Fin 2 → Q ⧸ N := ![mk y, β (mk y)]
  have hXβ : ∀ i, β (X i) = X i := by
    intro i
    fin_cases i
    · exact hβx
    · show β (α (mk x)) = α (mk x)
      rw [← hαβ, hβx]
  have hDb : ∀ d ∈ dsub (Q ⧸ N), β d ∈ dsub (Q ⧸ N) :=
    fun d hd => E2Aux.dsub_map_mem β.toMonoidHom β.surjective hd
  have hgenD : Subgroup.closure (({⁅mk x, α (mk x)⁆, ⁅mk y, β (mk y)⁆} : Set (Q ⧸ N)) ∪
      Set.range (fun p : Fin 2 × Fin 2 => ⁅X p.1, Y p.2⁆)) = dsub (Q ⧸ N) := by
    refine le_antisymm ((Subgroup.closure_le _).2 ?_)
      ((E2Aux.dsub_le_closure hz hgenG).trans (Subgroup.closure_mono ?_))
    · rintro w (hw | ⟨⟨i, j⟩, rfl⟩)
      · rcases hw with rfl | hw
        · exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
        · rw [Set.mem_singleton_iff.1 hw]
          exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      · exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    · intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl (Set.mem_insert _ _)
      · exact Or.inl (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      · exact Or.inr ⟨(0, 0), rfl⟩
      · exact Or.inr ⟨(0, 1), rfl⟩
      · exact Or.inr ⟨(1, 0), rfl⟩
      · exact Or.inr ⟨(1, 1), rfl⟩
  have hexa : α ⁅mk x, α (mk x)⁆ = ⁅mk x, α (mk x)⁆ := E2Aux.cyc hz hεx
  have hexb : β ⁅mk x, α (mk x)⁆ = ⁅mk x, α (mk x)⁆ := by
    rw [map_commutatorElement, hβx, ← hαβ, hβx]
  have heya : α ⁅mk y, β (mk y)⁆ = ⁅mk y, β (mk y)⁆ := by
    rw [map_commutatorElement, hαy, hαβ, hαy]
  have heyb : β ⁅mk y, β (mk y)⁆ = ⁅mk y, β (mk y)⁆ := E2Aux.cyc hz hεy
  have hbz0 : ∀ i, β ⁅X i, Y 0⁆ = ⁅X i, Y 1⁆ := fun i =>
    (E2Aux.act_second hz (hXβ i) hεy).1
  have hbz1 : ∀ i, β ⁅X i, Y 1⁆ = (⁅X i, Y 0⁆ * ⁅X i, Y 1⁆)⁻¹ := fun i =>
    (E2Aux.act_second hz (hXβ i) hεy).2
  have hu' : mk u ∈ dsub (Q ⧸ N) := E2Aux.dsub_map_mem mk hmk hu
  have hbu' : β (mk u) = mk u := by
    rw [hβ]
    change ((b u : Q) : Q ⧸ N) = (u : Q ⧸ N)
    exact QuotientGroup.eq_iff_div_mem.2 (by simpa [div_eq_mul_inv] using h1)
  have hnu' : eps α (mk u) = 1 := by
    have h3 : eps α (mk u) = mk (eps a u) := by
      simp only [eps, map_mul, hα]
    rw [h3]
    change ((eps a u : Q) : Q ⧸ N) = 1
    exact (QuotientGroup.eq_one_iff _).2 h2
  have hfin := e2_alg (G := Q ⧸ N) hG2 (a := α) (b := β) (dsub (Q ⧸ N)) hDz hDb
    ⁅mk x, α (mk x)⁆ ⁅mk y, β (mk y)⁆ (fun i j => ⁅X i, Y j⁆) hgenD hexa hexb heya heyb hbz0 hbz1
    hu' hbu' hnu'
  exact (QuotientGroup.eq_one_iff u).1 hfin

theorem Cl3.E2_a (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) {u : Q} (hu : u ∈ dsub Q)
    (h1 : b u * u⁻¹ ∈ N) (h2 : eps a u ∈ N) : u ∈ N :=
  e2_main hQ h hu h1 h2

theorem Cl3.E2_b (hQ : IsPGroup 2 Q) (h : Cl3 Q a b N) {u : Q} (hu : u ∈ dsub Q)
    (h1 : a u * u⁻¹ ∈ N) (h2 : eps b u ∈ N) : u ∈ N :=
  e2_main hQ h.swap hu h1 h2

end Main

end CFSG.GH74.E2
