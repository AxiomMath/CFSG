module

public import CFSG.LieType.SeitzGeneration.HyperCoverLift
public import CFSG.LieType.SeitzGeneration.ExcHigh.FrameLayer

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311o

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley
open CFSG.LieType.SeitzGeneration.ExcHigh (card_sup_eq_mul_of_commute_disjoint)

theorem exists_rElement_preimage {G H : Type*} [Group G] [Group H] [Finite G] (f : G →* H)
    {r : ℕ} (hr : r.Prime) (x : G) {n : ℕ} (hx : f x ^ r ^ n = 1) :
    ∃ y : G, f y = f x ∧ ∃ m : ℕ, y ^ r ^ m = 1 := by
  obtain ⟨a, m', hm', hN⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' r hr.ne_one
  have hcop : Nat.Coprime m' (r ^ (n + 1)) := Nat.Prime.coprime_pow_of_not_dvd hr hm'
  obtain ⟨u, -, hu⟩ :=
    Nat.exists_mul_mod_eq_one_of_coprime hcop (Nat.one_lt_pow (by omega) hr.one_lt)
  refine ⟨x ^ (m' * u), ?_, a, ?_⟩
  · have h1 : f x ^ r ^ (n + 1) = 1 := by rw [pow_succ, pow_mul, hx, one_pow]
    rw [map_pow, ← Nat.mod_add_div (m' * u) (r ^ (n + 1)), hu, pow_add, pow_one, pow_mul, h1,
      one_pow, mul_one]
  · rw [← pow_mul, show m' * u * r ^ a = r ^ a * m' * u by ring, ← hN, pow_mul,
      pow_orderOf_eq_one, one_pow]

theorem map_closure_hyperRSet_le {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Injective f) (C A : Subgroup G) (r p : ℕ) :
    (Subgroup.closure (hyperRSet C A r p)).map f ≤
      Subgroup.closure (hyperRSet (C.map f) (A.map f) r p) := by
  rw [MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨x, ⟨hxC, ⟨n, hn⟩, B, hBA, hBi, hxB⟩, rfl⟩
  refine ⟨Subgroup.mem_map_of_mem f hxC, ⟨n, by rw [← map_pow, hn, map_one]⟩, B.map f,
    Subgroup.map_mono hBA, by rw [Subgroup.relIndex_map_map_of_injective _ _ hf, hBi], ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hxB b hb]

theorem top_le_closure_hyperRSet_of_central_lift {G H : Type*} [Group G] [Group H] [Finite G]
    [Group.IsPerfect G] {p r : ℕ} (hr : r.Prime) (hpr : Nat.Coprime p r) (π : G →* H)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center G) {B : Subgroup G}
    (hBp : ∀ x ∈ B, x ^ p = 1)
    (hgen : (⊤ : Subgroup H) ≤ Subgroup.closure (hyperRSet ⊤ (B.map π) r p)) :
    (⊤ : Subgroup G) ≤ Subgroup.closure (hyperRSet ⊤ B r p) := by
  have hmap : (Subgroup.closure (hyperRSet ⊤ B r p)).map π = ⊤ := by
    rw [eq_top_iff, MonoidHom.map_closure]
    refine hgen.trans (Subgroup.closure_mono ?_)
    rintro s ⟨-, ⟨n, hn⟩, C, -, hCi, hsC⟩
    obtain ⟨s₀, rfl⟩ := hπ s
    obtain ⟨y, hy, m, hm⟩ := exists_rElement_preimage π hr s₀ hn
    refine ⟨y, ⟨Subgroup.mem_top y, ⟨m, hm⟩, C.comap π ⊓ B, inf_le_right, ?_, ?_⟩, hy⟩
    · rw [Subgroup.inf_relIndex_right, Subgroup.relIndex_comap, hCi]
    · rw [Subgroup.mem_centralizer_iff]
      rintro b ⟨hbC, hbB⟩
      have hc : Commute (π b) (π y) := by
        rw [hy]
        exact Subgroup.mem_centralizer_iff.1 hsC (π b) hbC
      exact (commute_lift_of_coprime π hcen (Nat.Coprime.pow_right n hpr) hc (hBp b hbB)
        (by rw [hy]; exact hn)).eq
  exact (eq_top_of_map_eq_top_of_perfect π hcen hmap).ge

theorem le_closure_hyperRSet_of_layer {G : Type*} [Group G] {p r : ℕ} (hp : p.Prime)
    {A B L : Subgroup G} (hAc : Nat.card A = p) (hBc : Nat.card B = p ^ 3) (hd : Disjoint A B)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hLA : ∀ l ∈ L, ∀ a ∈ A, l * a = a * l)
    (hgen : L ≤ Subgroup.closure (hyperRSet L B r p)) :
    L ≤ Subgroup.closure (hyperRSet ⊤ (A ⊔ B) r p) := by
  refine hgen.trans (Subgroup.closure_mono ?_)
  rintro k ⟨hkL, hkr, F, hFB, hFi, hFk⟩
  have hFc : Nat.card F = p ^ 2 := by
    have h1 := Subgroup.relIndex_mul_card F B
    rw [inf_of_le_left hFB, hFi, hBc] at h1
    have : p * Nat.card F = p * p ^ 2 := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_left hp.pos this
  have hV : Nat.card ↥(A ⊔ B) = p ^ 4 := by
    rw [card_sup_eq_mul_of_commute_disjoint hAB hd, hAc, hBc]
    ring
  have hAF : Nat.card ↥(A ⊔ F) = p ^ 3 := by
    rw [card_sup_eq_mul_of_commute_disjoint (fun a ha f hf => hAB a ha f (hFB hf))
      (hd.mono_right hFB), hAc, hFc]
    ring
  have hle : A ⊔ F ≤ A ⊔ B := sup_le_sup_left hFB A
  refine ⟨Subgroup.mem_top k, hkr, A ⊔ F, hle, ?_, ?_⟩
  · have h2 := Subgroup.relIndex_mul_card (A ⊔ F) (A ⊔ B)
    rw [inf_of_le_left hle, hAF, hV] at h2
    have : (A ⊔ F).relIndex (A ⊔ B) * p ^ 3 = p * p ^ 3 := by rw [h2]; ring
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos 3) this
  · have hcent : A ⊔ F ≤ Subgroup.centralizer ({k} : Set G) := by
      refine sup_le (fun a ha => ?_) (fun f hf => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hLA k hkL a ha).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.1 hFk f hf
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.1 (hcent hx)

theorem le_closure_hyperRSet_of_frame {G : Type*} [Group G] {p r : ℕ} (hp : p.Prime)
    {V₁ V₂ X : Subgroup G} (hV₁c : Nat.card V₁ = p ^ 2) (hV₂c : Nat.card V₂ = p ^ 2)
    (hd : Disjoint V₁ V₂) (hcomm : ∀ a ∈ V₁, ∀ b ∈ V₂, a * b = b * a)
    (hpow : ∀ x ∈ V₁, x ^ p = 1) (hXV₂ : ∀ g ∈ X, ∀ b ∈ V₂, g * b = b * g)
    (hgen : X ≤ Subgroup.closure
      {g | g ∈ X ∧ (∃ n : ℕ, g ^ r ^ n = 1) ∧ ∃ x ∈ V₁, x ≠ 1 ∧ g * x = x * g}) :
    X ≤ Subgroup.closure (hyperRSet ⊤ (V₁ ⊔ V₂) r p) := by
  haveI := Fact.mk hp
  refine hgen.trans (Subgroup.closure_mono ?_)
  rintro g ⟨hgX, hgr, x, hxV, hx1, hgx⟩
  have hzx : Nat.card (Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hpow x hxV) hx1]
  have hzV : Subgroup.zpowers x ≤ V₁ := (Subgroup.zpowers_le).2 hxV
  have hDc : Nat.card ↥(Subgroup.zpowers x ⊔ V₂) = p ^ 3 := by
    rw [card_sup_eq_mul_of_commute_disjoint (fun a ha b hb => hcomm a (hzV ha) b hb)
      (hd.mono_left hzV), hzx, hV₂c]
    ring
  have hV : Nat.card ↥(V₁ ⊔ V₂) = p ^ 4 := by
    rw [card_sup_eq_mul_of_commute_disjoint hcomm hd, hV₁c, hV₂c]
    ring
  have hDV : Subgroup.zpowers x ⊔ V₂ ≤ V₁ ⊔ V₂ := sup_le_sup_right hzV V₂
  refine ⟨Subgroup.mem_top g, hgr, Subgroup.zpowers x ⊔ V₂, hDV, ?_, ?_⟩
  · have h2 := Subgroup.relIndex_mul_card (Subgroup.zpowers x ⊔ V₂) (V₁ ⊔ V₂)
    rw [inf_of_le_left hDV, hDc, hV] at h2
    have : (Subgroup.zpowers x ⊔ V₂).relIndex (V₁ ⊔ V₂) * p ^ 3 = p * p ^ 3 := by
      rw [h2]; ring
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos 3) this
  · have hcent : Subgroup.zpowers x ⊔ V₂ ≤ Subgroup.centralizer ({g} : Set G) := by
      refine sup_le (fun a ha => ?_) (fun b hb => ?_)
      · obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Commute.zpow_left (show Commute x g from hgx.symm) n).eq
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hXV₂ g hgX b hb).symm
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.1 (hcent hy)

theorem map_le_closure_hyperRSet {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    {P V : Subgroup G} {r p : ℕ} (h : P ≤ Subgroup.closure (hyperRSet ⊤ V r p)) :
    P.map e.toMonoidHom ≤ Subgroup.closure (hyperRSet ⊤ (V.map e.toMonoidHom) r p) := by
  have h1 := map_closure_hyperRSet_le e.toMonoidHom e.injective ⊤ V r p
  rw [Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at h1
  exact (Subgroup.map_mono h).trans h1

theorem top_le_closure_hyperRSet_of_frame_layer {G : Type*} [Group G] {p r o : ℕ} (hp : p.Prime)
    {V₁ V₂ X₁ X₂ P : Subgroup G} (hV₁ : IsElemAbelian p V₁) (hV₂ : IsElemAbelian p V₂)
    (hV₁c : Nat.card V₁ = p ^ 2) (hV₂c : Nat.card V₂ = p ^ 2) (hd : Disjoint V₁ V₂)
    (hcomm : ∀ a ∈ V₁, ∀ b ∈ V₂, a * b = b * a) (hX₁V₂ : ∀ g ∈ X₁, ∀ b ∈ V₂, g * b = b * g)
    (hX₂V₁ : ∀ g ∈ X₂, ∀ b ∈ V₁, g * b = b * g)
    (hX₁ : X₁ ≤ Subgroup.closure
      {g | g ∈ X₁ ∧ (∃ n : ℕ, g ^ r ^ n = 1) ∧ ∃ x ∈ V₁, x ≠ 1 ∧ g * x = x * g})
    (hX₂ : X₂ ≤ Subgroup.closure
      {g | g ∈ X₂ ∧ (∃ n : ℕ, g ^ r ^ n = 1) ∧ ∃ x ∈ V₂, x ≠ 1 ∧ g * x = x * g})
    (hclose : ∀ H P : Subgroup G, X₁ ⊔ X₂ ≤ H → P ≤ H → CFSG.Open.IsQuasisimple ↥P →
      o < Nat.card ↥P → H = ⊤)
    (hQ : CFSG.Open.IsQuasisimple ↥P) (ho : o < Nat.card ↥P)
    (hP : P ≤ Subgroup.closure (hyperRSet ⊤ (V₁ ⊔ V₂) r p)) :
    (⊤ : Subgroup G) ≤ Subgroup.closure (hyperRSet ⊤ (V₁ ⊔ V₂) r p) := by
  have h₁ := le_closure_hyperRSet_of_frame hp hV₁c hV₂c hd hcomm (fun x hx => hV₁.2 x hx)
    hX₁V₂ hX₁
  have h₂ := le_closure_hyperRSet_of_frame hp hV₂c hV₁c hd.symm
    (fun a ha b hb => (hcomm b hb a ha).symm) (fun x hx => hV₂.2 x hx) hX₂V₁ hX₂
  rw [sup_comm V₂ V₁] at h₂
  exact (hclose _ P (sup_le h₁ h₂) hP hQ ho).ge

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311o
