module

public import CFSG.CGT.T75JM.N6Main
public import CFSG.CGT.T75JM.M22PresInputs
public import CFSG.CGT.T75I.JankoStmt

public section

namespace CFSG.CGT.T75JM

open CFSG.CosetTable CFSG.CGT.Timmesfeld75 CFSG.CGT.T75I

@[expose] def evalWord7 {H : Type*} [Group H] (e : Fin 7 → H) (w : M22Word) : H :=
  FreeGroup.lift e (FreeGroup.mk w)

@[expose] def liftWord (w : List (Fin 6 × Bool)) : M22Word :=
  w.map fun p => (Fin.castSucc p.1, p.2)

@[expose] def invWord {m : ℕ} (w : List (Fin m × Bool)) : List (Fin m × Bool) :=
  (w.reverse).map fun p => (p.1, !p.2)

@[expose] def dGen : Fin 2 → List (Fin 6 × Bool) :=
  ![[(0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true)],
    [(0, true), (2, true), (1, true), (1, true), (0, true)]]

@[expose] def dTheta : Fin 2 → List (Fin 6 × Bool) :=
  ![[(0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true),
      (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (4, true)],
    [(0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (1, false), (2, true),
      (1, false), (0, true), (1, true), (0, true)]]

@[expose] def bGen : Fin 2 → List (Fin 6 × Bool) :=
  ![[(0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false),
      (0, true), (1, true), (0, true), (1, true), (3, true), (0, true), (1, false)],
    [(1, true), (1, true), (0, true), (1, false), (0, true), (2, true), (1, true), (0, true),
      (1, true), (1, true)]]

@[expose] def eGen : Fin 3 → List (Fin 6 × Bool) :=
  ![[(2, true), (3, true), (4, true)],
    [(0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true),
      (0, true), (1, true)],
    [(0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true),
      (0, true), (1, false), (0, true), (1, true), (0, true), (1, false)]]

@[expose] def vGen : Fin 2 → List (Fin 6 × Bool) :=
  ![[(0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false)],
    [(5, true), (1, true), (1, true)]]

@[expose] def thetaRels : List M22Word :=
  [(6, true), (6, true)] ::
    List.ofFn fun i : Fin 2 =>
      [(6, true)] ++ liftWord (dGen i) ++ [(6, true)] ++ liftWord (invWord (dTheta i))

@[expose] def pRels : List M22Word :=
  [[(0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (0, true),
    (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (1, true),
    (0, true), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (5, false),
    (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (1, true),
    (0, false), (1, false), (1, false), (0, false), (1, false), (0, false), (5, true), (1, true),
    (1, true)],
   [(0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (6, true),
    (6, true), (1, true), (0, false), (1, false), (1, false), (0, false), (1, false), (0, false),
    (1, false), (1, false), (5, false), (6, false), (6, true), (5, true), (1, true), (1, true)],
   [(0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (5, true),
    (1, true), (1, true), (6, true), (1, false), (1, false), (5, false), (1, true), (0, false),
    (1, false), (1, false), (0, false), (1, false), (0, false), (6, false), (1, false), (1, false),
    (5, false), (6, false), (6, true), (5, true), (1, true), (1, true)],
   [(0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (5, true),
    (1, true), (1, true), (6, false), (1, true), (0, false), (1, false), (1, false), (0, false),
    (1, false), (0, false), (1, false), (1, false), (5, false), (6, true), (1, false), (1, false),
    (5, false), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false),
    (6, false), (1, false), (1, false), (5, false)],
   [(0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (6, true),
    (5, true), (1, true), (1, true), (6, true), (0, true), (1, true), (0, true), (1, true),
    (1, true), (0, true), (1, false), (1, false), (1, false), (5, false), (6, true), (1, true),
    (0, false), (1, false), (1, false), (0, false), (1, false), (0, false), (6, false),
    (1, false), (1, false), (5, false)]]

@[expose] def m22RelsPD : List M22Word := m22RelsN ++ thetaRels ++ pRels

structure M22CtxHyp {G : Type} [Group G] (T T₁ : Subgroup G) : Prop where
  nonab : ∃ a b : G, a * b ≠ b * a
  wc : IsWC T
  card16 : Nat.card T = 16
  inf_bot : T ⊓ T₁ = ⊥
  conj : ∃ s : G, T₁ = conjSubgroup s T
  norm1 : Nat.card (normIn T T₁) = 4
  norm2 : Nat.card (normIn T₁ T) = 4
  cent_le : ∀ d ∈ T, d ≠ 1 → Subgroup.centralizer ({d} : Set G) ≤ Subgroup.normalizer (T : Set G)
  cent_eq : Subgroup.centralizer (T : Set G) = T
  trans : ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 →
    ∃ g ∈ Subgroup.normalizer (T : Set G), g * x * g⁻¹ = y
  gen : Subgroup.normalizer (T : Set G) ⊔ T₁ = ⊤
  quot : Nonempty (NQuot T ≃* alternatingGroup (Fin 6))

@[expose] def genTuple {G : Type} [Group G] {T : Subgroup G}
    (ψ : PG 6 rels6 ≃* ↥(Subgroup.normalizer (T : Set G))) (g : G) : Fin 7 → G :=
  fun i => if h : i.val < 6 then ((ψ (PresentedGroup.of ⟨i.val, h⟩) : ↥(Subgroup.normalizer
    (T : Set G))) : G) else g

structure T1Config {G : Type} [Group G] (T T₁ : Subgroup G) where
  ψ : PG 6 rels6 ≃* ↥(Subgroup.normalizer (T : Set G))
  map_t : Subgroup.map ψ.toMonoidHom (Subgroup.closure (Set.range tGen)) =
    T.subgroupOf (Subgroup.normalizer (T : Set G))
  g : G
  conj_g : conjSubgroup g T = T₁
  rel : ∀ r ∈ thetaRels, evalWord7 (genTuple ψ g) r = 1

@[expose] def T1Config.gens {G : Type} [Group G] {T T₁ : Subgroup G} (c : T1Config T T₁) :
    Fin 7 → G :=
  genTuple c.ψ c.g

@[expose] def L2Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (T T₁ : Subgroup G),
    M22CtxHyp T T₁ → Nonempty (T1Config T T₁)

@[expose] def PStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (T T₁ : Subgroup G),
    M22CtxHyp T T₁ → ∀ c : T1Config T T₁, ∀ r ∈ pRels, evalWord7 c.gens r = 1

@[expose] def R22PDStatement : Prop :=
  ∀ (H : Type) [Group H] (e : Fin 7 → H), (∀ r ∈ m22RelsPD, evalWord7 e r = 1) →
    Subgroup.closure (Set.range e) ≠ ⊥ →
      Nonempty (Subgroup.closure (Set.range e) ≃* CFSG.Blueprint.NativeSporadic.M22)

theorem m22RelsN_eq : m22RelsN = rels6.map liftWord := by decide +kernel

theorem evalWord7_liftWord {H : Type*} [Group H] (e : Fin 7 → H) (w : List (Fin 6 × Bool)) :
    evalWord7 e (liftWord w) = FreeGroup.lift (fun i : Fin 6 => e (Fin.castSucc i))
      (FreeGroup.mk w) := by
  rw [evalWord7, FreeGroup.lift_mk, FreeGroup.lift_mk, liftWord, List.map_map]
  rfl

theorem T1Config.rels_N {G : Type} [Group G] {T T₁ : Subgroup G} (c : T1Config T T₁) :
    ∀ r ∈ m22RelsN, evalWord7 c.gens r = 1 := by
  intro r hr
  rw [m22RelsN_eq, List.mem_map] at hr
  obtain ⟨r0, hr0, rfl⟩ := hr
  rw [evalWord7_liftWord]
  have h1 : (PresentedGroup.mk {r : FreeGroup (Fin 6) | r ∈ rels6.map FreeGroup.mk}
      (FreeGroup.mk r0)) = 1 :=
    PresentedGroup.one_of_mem (List.mem_map_of_mem hr0)
  have h2 : (FreeGroup.lift (fun i : Fin 6 => c.gens (Fin.castSucc i)) : FreeGroup (Fin 6) →* G) =
      (Subgroup.normalizer (T : Set G)).subtype.comp
        (c.ψ.toMonoidHom.comp (PresentedGroup.mk {r : FreeGroup (Fin 6) |
          r ∈ rels6.map FreeGroup.mk})) := by
    apply FreeGroup.ext_hom
    intro i
    simp [T1Config.gens, genTuple, PresentedGroup.mk]
    rfl
  rw [h2]
  simp [h1]

theorem T1Config.closure_gens {G : Type} [Group G] {T T₁ : Subgroup G} (c : T1Config T T₁)
    (hgen : Subgroup.normalizer (T : Set G) ⊔ T₁ = ⊤) :
    Subgroup.closure (Set.range c.gens) = ⊤ := by
  have hN : ∀ n : ↥(Subgroup.normalizer (T : Set G)),
      (n : G) ∈ Subgroup.closure (Set.range c.gens) := by
    intro n
    have hw : c.ψ.symm n ∈ Subgroup.closure (Set.range
        (PresentedGroup.of : Fin 6 → PG 6 rels6)) := by
      rw [PresentedGroup.closure_range_of]; exact Subgroup.mem_top _
    have key : ∀ w : PG 6 rels6, w ∈ Subgroup.closure (Set.range
        (PresentedGroup.of : Fin 6 → PG 6 rels6)) →
        ((c.ψ w : ↥(Subgroup.normalizer (T : Set G))) : G) ∈
          Subgroup.closure (Set.range c.gens) := by
      intro w hw
      induction hw using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        refine Subgroup.subset_closure ⟨Fin.castSucc i, ?_⟩
        simp [T1Config.gens, genTuple]
      | one => simp
      | mul x y _ _ hx hy =>
        simpa using (Subgroup.closure (Set.range c.gens)).mul_mem hx hy
      | inv x _ hx => simpa using (Subgroup.closure (Set.range c.gens)).inv_mem hx
    have := key _ hw
    simpa using this
  have hg : c.g ∈ Subgroup.closure (Set.range c.gens) :=
    Subgroup.subset_closure ⟨6, by simp [T1Config.gens, genTuple]⟩
  have hT1 : T₁ ≤ Subgroup.closure (Set.range c.gens) := by
    intro x hx
    rw [← c.conj_g, mem_conjSubgroup] at hx
    have hT : c.g⁻¹ * x * c.g ∈ Subgroup.normalizer (T : Set G) := Subgroup.le_normalizer hx
    have := hN ⟨_, hT⟩
    have h3 := (Subgroup.closure (Set.range c.gens)).mul_mem
      ((Subgroup.closure (Set.range c.gens)).mul_mem hg this)
      ((Subgroup.closure (Set.range c.gens)).inv_mem hg)
    simpa [mul_assoc] using h3
  have hNle : Subgroup.normalizer (T : Set G) ≤ Subgroup.closure (Set.range c.gens) :=
    fun x hx => hN ⟨x, hx⟩
  rw [eq_top_iff, ← hgen]
  exact sup_le hNle hT1

theorem jankoM22CtxInput_of_parts (hL2 : L2Statement) (hP : PStatement)
    (hR : R22PDStatement) : JankoM22CtxInput := by
  intro G _ _ _ hnab T T₁ hwc h16 hinf hconj hn1 hn2 hcd hC htr hgen hq
  have hyp : M22CtxHyp T T₁ :=
    ⟨hnab, hwc, h16, hinf, hconj, hn1, hn2, hcd, hC, htr, hgen, hq⟩
  obtain ⟨c⟩ := hL2 G T T₁ hyp
  have hpr := hP G T T₁ hyp c
  have hall : ∀ r ∈ m22RelsPD, evalWord7 c.gens r = 1 := by
    intro r hr
    simp only [m22RelsPD, List.mem_append] at hr
    rcases hr with (hr | hr) | hr
    · exact c.rels_N r hr
    · exact c.rel r hr
    · exact hpr r hr
  have htop := c.closure_gens hgen
  have hne : Subgroup.closure (Set.range c.gens) ≠ ⊥ := by
    rw [htop]
    obtain ⟨a, b, hab⟩ := hnab
    intro h
    have ha : a ∈ (⊤ : Subgroup G) := Subgroup.mem_top a
    have hb : b ∈ (⊤ : Subgroup G) := Subgroup.mem_top b
    rw [h] at ha hb
    exact hab (by rw [(Subgroup.mem_bot.1 ha), (Subgroup.mem_bot.1 hb)])
  obtain ⟨φ⟩ := hR G c.gens hall hne
  exact ⟨(Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)).trans φ⟩

end CFSG.CGT.T75JM
