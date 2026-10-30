module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Tactic.Linarith.Frontend

public section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

section Closing

variable {G : Type*} [Group G]

abbrev planeCl (E : Subgroup G) : Subgroup G :=
  Subgroup.closure {k | ∃ x ∈ E, x ≠ 1 ∧ Commute k x}

theorem le_planeCl_of_le_centralizer {E : Subgroup G} {x : G} (hx : x ∈ E) (hx1 : x ≠ 1)
    {X : Subgroup G} (hX : X ≤ Subgroup.centralizer ({x} : Set G)) : X ≤ planeCl E := by
  intro k hk
  refine Subgroup.subset_closure ⟨x, hx, hx1, ?_⟩
  exact Subgroup.mem_centralizer_singleton_iff.1 (hX hk)

theorem planeCl_eq_top_of_two_frames {E : Subgroup G} {a b : G} (ha : a ∈ E) (hb : b ∈ E)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) {X Y : Subgroup G}
    (hXa : X ≤ Subgroup.centralizer ({a} : Set G)) (hYb : Y ≤ Subgroup.centralizer ({b} : Set G))
    (hclose : ∀ H : Subgroup G, X ≤ H → ¬ H ≤ Subgroup.normalizer (X : Set G) → H = ⊤)
    (hYX : ¬ Y ≤ Subgroup.normalizer (X : Set G)) : planeCl E = ⊤ := by
  have hX := le_planeCl_of_le_centralizer ha ha1 hXa
  have hY := le_planeCl_of_le_centralizer hb hb1 hYb
  refine hclose _ hX fun hN => hYX (hY.trans hN)


theorem planeCl_eq_top_of_generated {E N : Subgroup G}
    (hN : N ≤ Subgroup.closure {g | g ∈ N ∧ ∃ x ∈ E, x ≠ 1 ∧ Commute g x})
    {e : G} (he : e ∈ E) (he1 : e ≠ 1)
    (hgen : Subgroup.closure
      ((N : Set G) ∪ (Subgroup.centralizer ({e} : Set G) : Set G)) = ⊤) :
    planeCl E = ⊤ := by
  have hNM : N ≤ planeCl E := hN.trans (Subgroup.closure_mono fun g ⟨_, hg⟩ => hg)
  have hC : Subgroup.centralizer ({e} : Set G) ≤ planeCl E :=
    le_planeCl_of_le_centralizer he he1 le_rfl
  rw [eq_top_iff, ← hgen, Subgroup.closure_le]
  exact Set.union_subset (fun g hg => hNM hg) (fun g hg => hC hg)

theorem closure_union_centralizer_eq_top_of_maximal {N : Subgroup G}
    (hmax : ∀ H : Subgroup G, N ≤ H → H = N ∨ H = ⊤) {e : G}
    (hout : ¬ Subgroup.centralizer ({e} : Set G) ≤ N) :
    Subgroup.closure ((N : Set G) ∪ (Subgroup.centralizer ({e} : Set G) : Set G)) = ⊤ := by
  set M := Subgroup.closure ((N : Set G) ∪ (Subgroup.centralizer ({e} : Set G) : Set G)) with hM
  have hNM : N ≤ M := fun g hg => Subgroup.subset_closure (Or.inl hg)
  rcases hmax M hNM with h | h
  · exfalso
    apply hout
    intro k hk
    have : k ∈ M := Subgroup.subset_closure (Or.inr hk)
    rw [h] at this
    exact this
  · exact h

theorem mem_normalizer_map_conj_iff (X : Subgroup G) (g g' : G) :
    g' ∈ Subgroup.normalizer ((X.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ↔
      g⁻¹ * g' * g ∈ Subgroup.normalizer (X : Set G) := by
  have key : ∀ x : G, x ∈ X.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ X := by
    intro x
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
    · intro hx
      exact ⟨g⁻¹ * x * g, hx, by group⟩
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    have := h (g * y * g⁻¹)
    rw [key, key] at this
    simpa [mul_assoc] using this
  · intro h y
    rw [key, key]
    have := h (g⁻¹ * y * g)
    simpa [mul_assoc] using this

theorem map_conj_eq_iff_mem_normalizer (R : Subgroup G) (g : G) :
    R.map (MulAut.conj g).toMonoidHom = R ↔ g ∈ Subgroup.normalizer (R : Set G) := by
  have key : ∀ x : G, x ∈ R.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ R := by
    intro x
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
    · intro hx
      exact ⟨g⁻¹ * x * g, hx, by group⟩
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    have := (Subgroup.ext_iff.1 h (g * y * g⁻¹))
    rw [key] at this
    simpa [mul_assoc] using this
  · intro h
    ext x
    rw [key]
    have := h (g⁻¹ * x * g)
    simpa [mul_assoc] using this

theorem isSolvable_iff_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Group.IsSolvable A ↔ Group.IsSolvable B :=
  ⟨fun h => by haveI := h; exact solvable_of_surjective (f := e.toMonoidHom) e.surjective,
   fun h => by haveI := h; exact solvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective⟩

theorem isSolvable_map_iff {H : Type*} [Group H] (f : G →* H) (hf : Function.Injective f)
    (X : Subgroup G) : Group.IsSolvable ↥(X.map f) ↔ Group.IsSolvable ↥X :=
  (isSolvable_iff_of_mulEquiv (X.equivMapOfInjective f hf)).symm

structure ClosingFrameAt (a : G) (X : Subgroup G) : Prop where
  centralizes : X ≤ Subgroup.centralizer ({a} : Set G)
  nonsolvable : ¬ Group.IsSolvable ↥X
  closing : ∀ H : Subgroup G, X ≤ H → ¬ H ≤ Subgroup.normalizer (X : Set G) → H = ⊤
  normalizer_solvable : ∀ P : Subgroup G, P ≤ Subgroup.normalizer (X : Set G) →
    Group.IsSolvable ↥(P ⊓ X) → Group.IsSolvable ↥P

theorem ClosingFrameAt.conj {a : G} {X : Subgroup G} (h : ClosingFrameAt a X) (g : G) :
    ClosingFrameAt (g * a * g⁻¹) (X.map (MulAut.conj g).toMonoidHom) where
  centralizes := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxa := Subgroup.mem_centralizer_singleton_iff.1 (h.centralizes hx)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc (g * x * g⁻¹) * (g * a * g⁻¹) = g * (x * a) * g⁻¹ := by group
      _ = g * (a * x) * g⁻¹ := by rw [hxa]
      _ = (g * a * g⁻¹) * (g * x * g⁻¹) := by group
  nonsolvable := fun hs =>
    h.nonsolvable ((isSolvable_map_iff _ (MulAut.conj g).injective X).1 hs)
  closing := by
    intro H hXH hHN
    set H₀ : Subgroup G := H.map (MulAut.conj g⁻¹).toMonoidHom with hH₀
    have hmem : ∀ x : G, x ∈ H₀ ↔ g * x * g⁻¹ ∈ H := by
      intro x
      simp only [hH₀, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa [mul_assoc] using hy
      · intro hx
        exact ⟨g * x * g⁻¹, hx, by group⟩
    have hXH₀ : X ≤ H₀ := fun x hx => (hmem x).2 (hXH ⟨x, hx, rfl⟩)
    have hH₀N : ¬ H₀ ≤ Subgroup.normalizer (X : Set G) := by
      intro hle
      apply hHN
      intro y hy
      rw [mem_normalizer_map_conj_iff]
      exact hle ((hmem _).2 (by simpa [mul_assoc] using hy))
    have htop := h.closing H₀ hXH₀ hH₀N
    rw [eq_top_iff]
    intro y _
    have : g⁻¹ * y * g ∈ H₀ := by rw [htop]; exact Subgroup.mem_top _
    simpa [mul_assoc] using (hmem _).1 this
  normalizer_solvable := by
    intro P hP hPX
    set P' : Subgroup G := P.map (MulAut.conj g⁻¹).toMonoidHom with hP'
    have hP'N : P' ≤ Subgroup.normalizer (X : Set G) := by
      rintro _ ⟨p, hp, rfl⟩
      have := (mem_normalizer_map_conj_iff X g p).1 (hP hp)
      simpa [MulAut.conj_apply] using this
    have hcomp : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id G := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
    have hinf : P' ⊓ X = (P ⊓ X.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective, Subgroup.map_map, hcomp,
        Subgroup.map_id]
    have hsol : Group.IsSolvable ↥(P' ⊓ X) := by
      rw [hinf]
      exact (isSolvable_map_iff _ (MulAut.conj g⁻¹).injective _).2 hPX
    exact (isSolvable_map_iff _ (MulAut.conj g⁻¹).injective P).1 (h.normalizer_solvable P' hP'N hsol)

theorem not_le_normalizer_of_solvable_centralizer {a b : G} {X Y : Subgroup G}
    (hXa : X ≤ Subgroup.centralizer ({a} : Set G)) (hYb : Y ≤ Subgroup.centralizer ({b} : Set G))
    (hN : ∀ P : Subgroup G, P ≤ Subgroup.normalizer (X : Set G) →
      Group.IsSolvable ↥(P ⊓ X) → Group.IsSolvable ↥P)
    (hY : ¬ Group.IsSolvable ↥Y)
    (hC : Group.IsSolvable ↥(Subgroup.centralizer ({a, b} : Set G))) :
    ¬ Y ≤ Subgroup.normalizer (X : Set G) := by
  intro hYN
  apply hY
  refine hN Y hYN ?_
  have hle : Y ⊓ X ≤ Subgroup.centralizer ({a, b} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    rintro y (rfl | rfl)
    · exact (Subgroup.mem_centralizer_singleton_iff.1 (hXa hx.2)).symm
    · exact (Subgroup.mem_centralizer_singleton_iff.1 (hYb hx.1)).symm
  haveI := hC
  exact solvable_of_solvable_injective (Subgroup.inclusion_injective hle)

theorem planeCl_eq_top_of_closingFrames {E : Subgroup G} {a b : G} (ha : a ∈ E) (hb : b ∈ E)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hgen : E ≤ Subgroup.closure {a, b}) {X Y : Subgroup G}
    (hX : ClosingFrameAt a X) (hY : ClosingFrameAt b Y)
    (hCE : Group.IsSolvable ↥(Subgroup.centralizer (E : Set G))) : planeCl E = ⊤ := by
  refine planeCl_eq_top_of_two_frames ha hb ha1 hb1 hX.centralizes hY.centralizes hX.closing ?_
  refine not_le_normalizer_of_solvable_centralizer hX.centralizes hY.centralizes
    hX.normalizer_solvable hY.nonsolvable ?_
  have hle : Subgroup.centralizer ({a, b} : Set G) ≤ Subgroup.centralizer (E : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro h hh
    have hcl : Subgroup.closure ({a, b} : Set G) ≤ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.closure_le]
      rintro y (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (hx _ (by simp))
      · exact Subgroup.mem_centralizer_singleton_iff.2 (hx _ (by simp))
    exact Subgroup.mem_centralizer_singleton_iff.1 (hcl (hgen hh))
  haveI := hCE
  exact solvable_of_solvable_injective (Subgroup.inclusion_injective hle)

theorem planeCl_eq_top_of_embedding {F : Type*} [Group F] (ι : F →* G)
    (hι : Function.Injective ι) {E₃ : Subgroup F} (h3 : planeCl E₃ = ⊤) {e : F} (he : e ∈ E₃)
    (he1 : e ≠ 1)
    (hgen : Subgroup.closure
      ((ι.range : Set G) ∪ (Subgroup.centralizer ({ι e} : Set G) : Set G)) = ⊤) :
    planeCl (E₃.map ι) = ⊤ := by
  refine planeCl_eq_top_of_generated ?_ (Subgroup.mem_map_of_mem ι he)
    (fun h => he1 (hι (by simpa using h))) hgen
  rintro _ ⟨f, rfl⟩
  have hf : f ∈ planeCl E₃ := by rw [h3]; exact Subgroup.mem_top _
  have hmem : ι f ∈ (planeCl E₃).map ι := ⟨f, hf, rfl⟩
  rw [MonoidHom.map_closure] at hmem
  refine Subgroup.closure_mono ?_ hmem
  rintro _ ⟨k, ⟨x, hx, hx1, hkx⟩, rfl⟩
  exact ⟨⟨k, rfl⟩, ι x, ⟨x, hx, rfl⟩, fun h => hx1 (hι (h.trans (map_one ι).symm)), hkx.map ι⟩

theorem exists_gens_of_plane {p : ℕ} [hp : Fact p.Prime] {E : Subgroup G}
    (hexp : ∀ x ∈ E, x ^ p = 1) (hcard : Nat.card E = p ^ 2) :
    ∃ a ∈ E, ∃ b ∈ E, a ≠ 1 ∧ b ≠ 1 ∧ E ≤ Subgroup.closure {a, b} := by
  have hfin : Finite E :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hp.out.ne_zero)
  have hnt : Nontrivial E := by
    refine Finite.one_lt_card_iff_nontrivial.1 ?_
    rw [hcard]
    exact Nat.one_lt_pow (by norm_num) hp.out.one_lt
  obtain ⟨⟨a, haE⟩, ha1⟩ := exists_ne (1 : E)
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hao : orderOf a = p := orderOf_eq_prime (hexp a haE) ha1'
  have hZa : Nat.card (Subgroup.zpowers a) = p := by
    rw [Nat.card_zpowers, hao]
  have hfZ : Finite (Subgroup.zpowers a) :=
    finite_zpowers.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨p, hp.out.pos, hexp a haE⟩)
  have hZE : Subgroup.zpowers a ≤ E := (Subgroup.zpowers_le).2 haE
  have hex : ∃ b ∈ E, b ∉ Subgroup.zpowers a := by
    by_contra hcon
    push Not at hcon
    have heq : E ≤ Subgroup.zpowers a := fun x hx => hcon x hx
    have := Subgroup.card_le_of_le heq
    rw [hcard, hZa] at this
    have hp2 : p < p ^ 2 := by
      have := hp.out.one_lt
      nlinarith
    omega
  obtain ⟨b, hbE, hb⟩ := hex
  have hb1 : b ≠ 1 := fun h => hb (h ▸ Subgroup.one_mem _)
  refine ⟨a, haE, b, hbE, ha1', hb1, ?_⟩
  set C := Subgroup.closure ({a, b} : Set G) with hC
  have hCE : C ≤ E := by
    rw [hC, Subgroup.closure_le]
    rintro y (rfl | rfl)
    exacts [haE, hbE]
  have hfC : Finite C := Finite.of_injective (Subgroup.inclusion hCE) (Subgroup.inclusion_injective hCE)
  have hZC : Subgroup.zpowers a ≤ C := (Subgroup.zpowers_le).2 (Subgroup.subset_closure (by simp))
  have hbC : b ∈ C := Subgroup.subset_closure (by simp)
  have hCd : Nat.card C ∣ p ^ 2 := hcard ▸ Subgroup.card_dvd_of_le hCE
  have hpC : p ∣ Nat.card C := hZa ▸ Subgroup.card_dvd_of_le hZC
  have hCcard : Nat.card C = p ^ 2 := by
    rcases (Nat.dvd_prime_pow hp.out).1 hCd with ⟨k, hk, hkC⟩
    interval_cases k
    · rw [pow_zero] at hkC
      rw [hkC] at hpC
      exact absurd (Nat.dvd_one.1 hpC) hp.out.ne_one
    · rw [pow_one] at hkC
      exfalso
      have hle := Subgroup.eq_of_le_of_card_ge hZC (by rw [hZa, hkC])
      exact hb (hle ▸ hbC)
    · exact hkC
  exact (Subgroup.eq_of_le_of_card_ge hCE (by rw [hCcard, hcard])).ge

@[expose] def NormalizesRIn (r : ℕ) {M : Type*} [Group M] (E : Subgroup M) : Prop :=
  ∃ R : Subgroup M, R ≠ ⊥ ∧ IsPGroup r R ∧ E ≤ Subgroup.normalizer (R : Set M)

end Closing

end CFSG.LieType.SeitzGeneration.ExcHighThree
