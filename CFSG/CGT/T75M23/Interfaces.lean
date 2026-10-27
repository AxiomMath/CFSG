module

public import CFSG.CGT.T75M23.N7Main
public import CFSG.CGT.T75JM.Interfaces
public import CFSG.CGT.T75M23.M23PresInputs

public section

namespace CFSG.CGT.T75M23

open CFSG.CosetTable CFSG.CGT.Timmesfeld75 CFSG.CGT.T75I
open CFSG.CGT.T75JM (evalWord7 evalWord7_liftWord)

structure M23CtxHyp {G : Type} [Group G] (T T₁ : Subgroup G) : Prop where
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
  quot : Nonempty (NQuot T ≃* alternatingGroup (Fin 7))

@[expose] def genTuple7 {G : Type} [Group G] {T : Subgroup G}
    (ψ : PG 6 rels7 ≃* ↥(Subgroup.normalizer (T : Set G))) (g : G) : Fin 7 → G :=
  fun i => if h : i.val < 6 then ((ψ (PresentedGroup.of ⟨i.val, h⟩) : ↥(Subgroup.normalizer
    (T : Set G))) : G) else g

structure T1Config7 {G : Type} [Group G] (T T₁ : Subgroup G) where
  ψ : PG 6 rels7 ≃* ↥(Subgroup.normalizer (T : Set G))
  map_t : Subgroup.map ψ.toMonoidHom (Subgroup.closure (Set.range tGen7)) =
    T.subgroupOf (Subgroup.normalizer (T : Set G))
  g : G
  conj_g : conjSubgroup g T = T₁
  rel : ∀ r ∈ thetaRels7, evalWord7 (genTuple7 ψ g) r = 1

@[expose] def T1Config7.gens {G : Type} [Group G] {T T₁ : Subgroup G} (c : T1Config7 T T₁) :
    Fin 7 → G :=
  genTuple7 c.ψ c.g

@[expose] def L2Statement7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (T T₁ : Subgroup G),
    M23CtxHyp T T₁ → Nonempty (T1Config7 T T₁)

@[expose] def PStatement7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (T T₁ : Subgroup G),
    M23CtxHyp T T₁ → ∀ c : T1Config7 T T₁, ∀ r ∈ pRels7, evalWord7 c.gens r = 1

@[expose] def R23Statement : Prop :=
  ∀ (H : Type) [Group H] (e : Fin 7 → H), (∀ r ∈ m23Rels, evalWord7 e r = 1) →
    Subgroup.closure (Set.range e) ≠ ⊥ →
      Nonempty (Subgroup.closure (Set.range e) ≃* CFSG.Blueprint.NativeSporadic.M23)

theorem liftWord7_eq : liftWord7 = CFSG.CGT.T75JM.liftWord := rfl

theorem T1Config7.rels_N {G : Type} [Group G] {T T₁ : Subgroup G} (c : T1Config7 T T₁) :
    ∀ r ∈ m23RelsN, evalWord7 c.gens r = 1 := by
  intro r hr
  rw [m23RelsN, List.mem_map] at hr
  obtain ⟨r0, hr0, rfl⟩ := hr
  rw [liftWord7_eq, evalWord7_liftWord]
  have h1 : (PresentedGroup.mk {r : FreeGroup (Fin 6) | r ∈ rels7.map FreeGroup.mk}
      (FreeGroup.mk r0)) = 1 :=
    PresentedGroup.one_of_mem (List.mem_map_of_mem hr0)
  have h2 : (FreeGroup.lift (fun i : Fin 6 => c.gens (Fin.castSucc i)) : FreeGroup (Fin 6) →* G) =
      (Subgroup.normalizer (T : Set G)).subtype.comp
        (c.ψ.toMonoidHom.comp (PresentedGroup.mk {r : FreeGroup (Fin 6) |
          r ∈ rels7.map FreeGroup.mk})) := by
    apply FreeGroup.ext_hom
    intro i
    simp [T1Config7.gens, genTuple7, PresentedGroup.mk]
    rfl
  rw [h2]
  simp [h1]

theorem T1Config7.closure_gens {G : Type} [Group G] {T T₁ : Subgroup G} (c : T1Config7 T T₁)
    (hgen : Subgroup.normalizer (T : Set G) ⊔ T₁ = ⊤) :
    Subgroup.closure (Set.range c.gens) = ⊤ := by
  have hN : ∀ n : ↥(Subgroup.normalizer (T : Set G)),
      (n : G) ∈ Subgroup.closure (Set.range c.gens) := by
    intro n
    have hw : c.ψ.symm n ∈ Subgroup.closure (Set.range
        (PresentedGroup.of : Fin 6 → PG 6 rels7)) := by
      rw [PresentedGroup.closure_range_of]; exact Subgroup.mem_top _
    have key : ∀ w : PG 6 rels7, w ∈ Subgroup.closure (Set.range
        (PresentedGroup.of : Fin 6 → PG 6 rels7)) →
        ((c.ψ w : ↥(Subgroup.normalizer (T : Set G))) : G) ∈
          Subgroup.closure (Set.range c.gens) := by
      intro w hw
      induction hw using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        refine Subgroup.subset_closure ⟨Fin.castSucc i, ?_⟩
        simp [T1Config7.gens, genTuple7]
      | one => simp
      | mul x y _ _ hx hy =>
        simpa using (Subgroup.closure (Set.range c.gens)).mul_mem hx hy
      | inv x _ hx => simpa using (Subgroup.closure (Set.range c.gens)).inv_mem hx
    have := key _ hw
    simpa using this
  have hg : c.g ∈ Subgroup.closure (Set.range c.gens) :=
    Subgroup.subset_closure ⟨6, by simp [T1Config7.gens, genTuple7]⟩
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

theorem jankoM23CtxInput_of_parts (hL2 : L2Statement7) (hP : PStatement7)
    (hR : R23Statement) : JankoM23CtxInput := by
  intro G _ _ _ hnab T T₁ hwc h16 hinf hconj hn1 hn2 hcd hC htr hgen hq
  have hyp : M23CtxHyp T T₁ :=
    ⟨hnab, hwc, h16, hinf, hconj, hn1, hn2, hcd, hC, htr, hgen, hq⟩
  obtain ⟨c⟩ := hL2 G T T₁ hyp
  have hpr := hP G T T₁ hyp c
  have hall : ∀ r ∈ m23Rels, evalWord7 c.gens r = 1 := by
    intro r hr
    simp only [m23Rels, List.mem_append] at hr
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

end CFSG.CGT.T75M23
