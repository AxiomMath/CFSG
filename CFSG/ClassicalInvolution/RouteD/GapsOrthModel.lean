module

public import CFSG.ClassicalInvolution.RouteD.GapsOrthFacts
public import CFSG.ClassicalInvolution.RouteD.GapsOrthExcl
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Signs
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthConj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthIso

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.WeakCT
open CFSG.ClassicalInvolution.Generic (Commutes conjSub)
open scoped commutatorElement MatrixGroups

section Geometry

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

@[expose] def fundSet (Q : QuadraticForm K V) : Set (Subgroup (V ≃ₗ[K] V)) :=
  {L | ∃ i, IsFundamental Q L i}

omit [FiniteDimensional K V] in
theorem invOf_eq (hodd : Odd (Nat.card K)) {L : Subgroup (V ≃ₗ[K] V)} {i r : V ≃ₗ[K] V}
    (h : IsFundamental Q L i) (hr : InvOf L r) : r = i :=
  h.eq_of_orderOf_eq_two hodd hr.1 hr.2

theorem commute_of_commutator_mem_scalars (hodd : Odd (Nat.card K))
    (hdim : 9 ≤ Module.finrank K V) {L₁ L₂ : Subgroup (V ≃ₗ[K] V)} {i₁ i₂ : V ≃ₗ[K] V}
    (h₁ : IsFundamental Q L₁ i₁) (h₂ : IsFundamental Q L₂ i₂) (hc : ⁅i₁, i₂⁆ ∈ scalars K V) :
    i₁ * i₂ = i₂ * i₁ := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨F₁, rfl, rfl⟩ := h₁
  obtain ⟨F₂, rfl, rfl⟩ := h₂
  have hd₁ := ModelFacts.finrank_perp_add_four F₁
  have hd₂ := ModelFacts.finrank_perp_add_four F₂
  have hsup : Module.finrank K ↥(F₁.perp ⊔ F₂.perp) ≤ Module.finrank K V :=
    Submodule.finrank_le _
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq F₁.perp F₂.perp
  have hpos : 0 < Module.finrank K ↥(F₁.perp ⊓ F₂.perp) := by omega
  have hne : F₁.perp ⊓ F₂.perp ≠ ⊥ := fun h =>
    (Nat.pos_iff_ne_zero.mp hpos) (Submodule.finrank_eq_zero.mpr h)
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hw1 : F₁.La (-1) w = w := (Frame.mem_perp_iff_fix F₁ h2).mp hw.1
  have hw2 : F₂.La (-1) w = w := (Frame.mem_perp_iff_fix F₂ h2).mp hw.2
  obtain ⟨c, hcv⟩ := mem_scalars.mp hc
  have hcomm : ⁅F₁.La (-1), F₂.La (-1)⁆ w = w := by
    have e1 : (F₁.La (-1))⁻¹ = F₁.La (-1) := inv_eq_of_mul_eq_one_right F₁.La_neg_one_mul_self
    have e2 : (F₂.La (-1))⁻¹ = F₂.La (-1) := inv_eq_of_mul_eq_one_right F₂.La_neg_one_mul_self
    simp only [commutatorElement_def, e1, e2, LinearEquiv.mul_apply, hw1, hw2]
  have hc1 : c = 1 := by
    have := (hcv w).symm.trans hcomm
    have h' : (c - 1) • w = 0 := by rw [sub_smul, this, one_smul, sub_self]
    rcases smul_eq_zero.mp h' with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hw0
  have : ⁅F₁.La (-1), F₂.La (-1)⁆ = 1 := LinearEquiv.ext fun v => by rw [hcv v, hc1, one_smul]; rfl
  exact commutatorElement_eq_one_iff_mul_comm.mp this

theorem adj_data (hodd : Odd (Nat.card K)) (hdim : 9 ≤ Module.finrank K V)
    {c l : Subgroup (V ≃ₗ[K] V)} {ic il : V ≃ₗ[K] V} (hc : IsFundamental Q c ic)
    (hl : IsFundamental Q l il) (h : ModelAdj (scalars K V) c l) :
    ic * il = il * ic ∧ il ∈ Subgroup.normalizer (c : Set (V ≃ₗ[K] V)) ∧
      il ∉ Subgroup.centralizer (c : Set (V ≃ₗ[K] V)) := by
  obtain ⟨hne, hnc, rc, rl, hrc, hrl, hcen, hnorm⟩ := h
  have e1 := invOf_eq hodd hc hrc
  have e2 := invOf_eq hodd hl hrl
  subst e1 e2
  have hcomm := commute_of_commutator_mem_scalars hodd hdim hc hl hcen
  refine ⟨hcomm, ?_, fun hcent => hnc ((IsFundamental.commute_iff hodd hc hl hcomm hne).mpr hcent)⟩
  have hmul : rl * rl = 1 := hl.mul_self
  have hinv : rl⁻¹ = rl := inv_eq_of_mul_eq_one_right hmul
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hnorm x, fun hx => ?_⟩
  have := hnorm _ hx
  rwa [show rl * (rl * x * rl⁻¹) * rl⁻¹ = x by
    rw [hinv]
    calc rl * (rl * x * rl) * rl = (rl * rl) * x * (rl * rl) := by group
      _ = x := by rw [hmul]; group] at this

omit [FiniteDimensional K V] in
theorem orth_or_twin (hodd : Odd (Nat.card K)) {Li Lj : Subgroup (V ≃ₗ[K] V)}
    {ii ij : V ≃ₗ[K] V} (hi : IsFundamental Q Li ii) (hj : IsFundamental Q Lj ij)
    (hk : Commutes Li Lj) :
    (∀ x ∈ negSpace ii, ∀ y ∈ negSpace ij, polar Q x y = 0) ∨ ij = ii := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨F₁, rfl, rfl⟩ := hi
  obtain ⟨F₂, rfl, rfl⟩ := hj
  have hc : F₂.La (-1) * F₁.La (-1) = F₁.La (-1) * F₂.La (-1) :=
    (hk _ ⟨-1, rfl⟩ _ ⟨-1, rfl⟩).symm
  have hcent : ∀ A : SL(2, K), F₂.La (-1) * F₁.La A = F₁.La A * F₂.La (-1) := fun A =>
    (hk _ ⟨A, rfl⟩ _ ⟨-1, rfl⟩).symm
  rcases Frame.orth_or_eq h2 hc hcent with h | h
  · left
    rw [negSpace_La_neg_one h2, negSpace_La_neg_one h2]
    rintro _ ⟨X, rfl⟩ _ ⟨Y, rfl⟩
    exact h X Y
  · right
    exact h

theorem indist_of_eq (hodd : Odd (Nat.card K)) (hdim : 9 ≤ Module.finrank K V)
    {Li Lj : Subgroup (V ≃ₗ[K] V)} {ii ij : V ≃ₗ[K] V} (hi : IsFundamental Q Li ii)
    (hj : IsFundamental Q Lj ij) (hne : Li ≠ Lj) (heq : ij = ii) :
    ModelIndist (scalars K V) (fundSet Q) Li Lj := by
  refine ⟨hne, fun S hS hSi hSj hI hJ => ?_⟩
  obtain ⟨iS, hSf⟩ := hS
  obtain ⟨rs, ri, hrs, hri, hcen⟩ := hI
  obtain ⟨rs', rj, hrs', hrj, hcen'⟩ := hJ
  have e1 := invOf_eq hodd hSf hrs
  have e2 := invOf_eq hodd hSf hrs'
  have e3 := invOf_eq hodd hi hri
  have e4 := invOf_eq hodd hj hrj
  subst e1 e3 e4
  subst e2
  have hci := commute_of_commutator_mem_scalars hodd hdim hSf hi hcen
  have hcj := commute_of_commutator_mem_scalars hodd hdim hSf hj hcen'
  have e1 : Commutes S Li ↔ ri ∈ Subgroup.centralizer (S : Set (V ≃ₗ[K] V)) :=
    IsFundamental.commute_iff hodd hSf hi hci hSi
  have e2 : Commutes S Lj ↔ rj ∈ Subgroup.centralizer (S : Set (V ≃ₗ[K] V)) :=
    IsFundamental.commute_iff hodd hSf hj hcj hSj
  rw [e1, e2, heq]

omit [FiniteDimensional K V] in
theorem finrank_negSpace {L : Subgroup (V ≃ₗ[K] V)} {i : V ≃ₗ[K] V}
    (hodd : Odd (Nat.card K)) (h : IsFundamental Q L i) : Module.finrank K (negSpace i) = 4 := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨F, rfl, rfl⟩ := h
  rw [negSpace_La_neg_one h2]
  exact F.finrank_span

omit [Finite K] in
theorem not_three_orth_planes {W P₁ P₂ P₃ : Submodule K V} (hW4 : Module.finrank K W = 4)
    (h₁ : P₁ ≤ W) (h₂ : P₂ ≤ W) (h₃ : P₃ ≤ W) (f₁ : Module.finrank K P₁ = 2)
    (f₂ : Module.finrank K P₂ = 2) (f₃ : Module.finrank K P₃ = 2) (n₁ : PolarNondegOn Q P₁)
    (n₃ : PolarNondegOn Q P₃) (o12 : ∀ x ∈ P₁, ∀ y ∈ P₂, polar Q x y = 0)
    (o13 : ∀ x ∈ P₁, ∀ y ∈ P₃, polar Q x y = 0) (o23 : ∀ x ∈ P₂, ∀ y ∈ P₃, polar Q x y = 0) :
    False := by
  have hdis : Disjoint P₁ P₂ := by
    rw [Submodule.disjoint_def]
    intro x hx1 hx2
    refine n₁ x hx1 fun y hy => ?_
    rw [polar_comm]
    exact o12 y hy x hx2
  have hsup := Frame.finrank_sup_of_disjoint hdis
  have heq : P₁ ⊔ P₂ = W :=
    Submodule.eq_of_le_of_finrank_eq (sup_le h₁ h₂) (by rw [hsup, f₁, f₂, hW4])
  have h3zero : P₃ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    refine n₃ x hx fun y hy => ?_
    have hyW : y ∈ P₁ ⊔ P₂ := heq ▸ h₃ hy
    obtain ⟨u, hu, u', hu', rfl⟩ := Submodule.mem_sup.mp hyW
    rw [polar_add_right]
    rw [polar_comm Q x u, polar_comm Q x u', o13 u hu x hx, o23 u' hu' x hx, add_zero]
  rw [h3zero, finrank_bot] at f₃
  omega

theorem orthGeom_star (hodd : Odd (Nat.card K)) (hdim : 9 ≤ Module.finrank K V) :
    ∀ c ∈ fundSet Q, ∀ l₁ ∈ fundSet Q, ∀ l₂ ∈ fundSet Q, ∀ l₃ ∈ fundSet Q,
      ModelAdj (scalars K V) c l₁ → ModelAdj (scalars K V) c l₂ → ModelAdj (scalars K V) c l₃ →
      l₁ ≠ l₂ → l₁ ≠ l₃ → l₂ ≠ l₃ → Commutes l₁ l₂ → Commutes l₁ l₃ → Commutes l₂ l₃ →
      ModelIndist (scalars K V) (fundSet Q) l₁ l₂ ∨ ModelIndist (scalars K V) (fundSet Q) l₁ l₃ ∨
        ModelIndist (scalars K V) (fundSet Q) l₂ l₃ := by
  rintro c ⟨ic, hc⟩ l₁ ⟨i₁, h₁⟩ l₂ ⟨i₂, h₂⟩ l₃ ⟨i₃, h₃⟩ a₁ a₂ a₃ n12 n13 n23 k12 k13 k23
  obtain ⟨cm₁, N₁, C₁⟩ := adj_data hodd hdim hc h₁ a₁
  obtain ⟨cm₂, N₂, C₂⟩ := adj_data hodd hdim hc h₂ a₂
  obtain ⟨cm₃, N₃, C₃⟩ := adj_data hodd hdim hc h₃ a₃
  have pd₁ := (lemma_6_10 hodd hc h₁ cm₁ N₁ C₁).1
  have pd₂ := (lemma_6_10 hodd hc h₂ cm₂ N₂ C₂).1
  have pd₃ := (lemma_6_10 hodd hc h₃ cm₃ N₃ C₃).1
  rcases orth_or_twin hodd h₁ h₂ k12 with o12 | t12
  swap
  · exact Or.inl (indist_of_eq hodd hdim h₁ h₂ n12 t12)
  rcases orth_or_twin hodd h₁ h₃ k13 with o13 | t13
  swap
  · exact Or.inr (Or.inl (indist_of_eq hodd hdim h₁ h₃ n13 t13))
  rcases orth_or_twin hodd h₂ h₃ k23 with o23 | t23
  swap
  · exact Or.inr (Or.inr (indist_of_eq hodd hdim h₂ h₃ n23 t23))
  exfalso
  refine not_three_orth_planes (Q := Q) (W := negSpace ic)
    (P₁ := negSpace ic ⊓ negSpace i₁) (P₂ := negSpace ic ⊓ negSpace i₂)
    (P₃ := negSpace ic ⊓ negSpace i₃) (finrank_negSpace hodd hc) inf_le_left inf_le_left
    inf_le_left pd₁.finrank_U₂ pd₂.finrank_U₂ pd₃.finrank_U₂ pd₁.nondeg₂ pd₃.nondeg₂ ?_ ?_ ?_
  · exact fun x hx y hy => o12 x (Submodule.mem_inf.mp hx).2 y (Submodule.mem_inf.mp hy).2
  · exact fun x hx y hy => o13 x (Submodule.mem_inf.mp hx).2 y (Submodule.mem_inf.mp hy).2
  · exact fun x hx y hy => o23 x (Submodule.mem_inf.mp hx).2 y (Submodule.mem_inf.mp hy).2


section Signs

variable {p f : ℕ} [Fact p.Prime] {K' : Type} [Field K'] [Finite K'] [CharP K' p]

theorem orthGeom_sign (hK : Nat.card K = p ^ f) (hK' : Nat.card K' = (p ^ f) ^ 2)
    (hodd : Odd (Nat.card K)) (hdim : 9 ≤ Module.finrank K V) :
    ∀ R₁ ∈ fundSet Q, ∀ R₂ ∈ fundSet Q, ∀ R₃ ∈ fundSet Q, ModelAdj (scalars K V) R₁ R₂ →
      ModelAdj (scalars K V) R₃ R₂ → Commutes R₁ R₃ →
      (∃ W, WeakCT.LinearBlockStandardPair K W R₁ R₂) →
        ∃ W, WeakCT.LinearBlockStandardPair K W R₂ R₃ := by
  rintro R₁ ⟨i₁, h₁⟩ R₂ ⟨i₂, h₂⟩ R₃ ⟨i₃, h₃⟩ a₁ a₃ k13 ⟨W, hW⟩
  obtain ⟨cm₁, N₁, C₁⟩ := adj_data hodd hdim h₁ h₂ a₁
  obtain ⟨cm₃, N₃, C₃⟩ := adj_data hodd hdim h₃ h₂ a₃
  have hc13 : i₁ * i₃ = i₃ * i₁ := k13 _ h₁.mem _ h₃.mem
  rcases lemma_6_11_signs hK hK' hodd h₁ h₂ h₃ cm₁ cm₃ hc13 k13 N₁ N₃ C₁ C₃ with
    ⟨-, -, -, hl⟩ | ⟨-, -, hu, -⟩
  · exact ⟨_, hl⟩
  · exfalso
    have hW' : WeakCT.LinearBlockStandardPair K (R₁ ⊔ R₂) R₁ R₂ := linear_eq_sup hW ▸ hW
    exact not_linear_and_unitary hK hK' hodd hW' hu

end Signs

section Perp

theorem exists_hypPair_orth (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 9 ≤ Module.finrank K V) (F₁ : Models.OrthogonalPairs.Frame Q) (P : HypPair Q) (he : P.e ∈ F₁.perp)
    (hf : P.f ∈ F₁.perp) :
    ∃ P' : HypPair Q, P'.e ∈ F₁.perp ∧ P'.f ∈ F₁.perp ∧ P.Orth P' := by
  have hnd : PolarNondegOn Q (F₁.perp ⊓ P.perp) :=
    (ModelFacts.polarNondegOn_perp hQ F₁).inf_perp P he hf
  have hd1 := ModelFacts.finrank_perp_add_four F₁
  have hd2 := ModelFacts.finrank_hypPair_perp hQ P
  have hsup : F₁.perp ⊔ P.perp = ⊤ := by
    rw [eq_top_iff]
    intro v _
    refine Submodule.mem_sup.mpr ⟨v - F₁.incl (F₁.coords v), ?_, F₁.incl (F₁.coords v), ?_,
      by abel⟩
    · rw [Frame.mem_perp_iff, map_sub, Frame.coords_incl, sub_self]
    · rw [HypPair.mem_perp]
      refine ⟨?_, ?_⟩
      · exact (Frame.mem_perp_iff_forall_incl F₁).mp he (F₁.coords v)
      · exact (Frame.mem_perp_iff_forall_incl F₁).mp hf (F₁.coords v)
  have hdimC : 3 ≤ Module.finrank K ↥(F₁.perp ⊓ P.perp) := by
    have := Submodule.finrank_sup_add_finrank_inf_eq F₁.perp P.perp
    rw [hsup, finrank_top] at this
    omega
  have hnd' : (polarBilin (Q.restrict (F₁.perp ⊓ P.perp))).Nondegenerate :=
    nondegenerate_polarBilin_restrict hnd
  obtain ⟨v, hv0, hvQ⟩ := ModelFacts.exists_isotropic_of_finrank_ge_three hodd
    (Q.restrict (F₁.perp ⊓ P.perp)) hnd' hdimC
  have hQe : Q (v : V) = 0 := by simpa using hvQ
  have hve : (v : V) ≠ 0 := fun h => hv0 (Subtype.ext h)
  obtain ⟨y, hy, hey⟩ := hnd.exists_polar_ne_zero v.2 hve
  have h1 : polar Q (v : V) ((polar Q (v : V) y)⁻¹ • y) = 1 := by
    rw [polar_smul_right_eq, inv_mul_cancel₀ hey]
  let P' : HypPair Q := HypPair.ofPolarEqOne hQe h1
  have hP'e : P'.e ∈ F₁.perp ⊓ P.perp := v.2
  have hP'f : P'.f ∈ F₁.perp ⊓ P.perp :=
    Submodule.sub_mem _ (Submodule.smul_mem _ _ hy) (Submodule.smul_mem _ _ v.2)
  have h3 := HypPair.mem_perp.mp (Submodule.mem_inf.mp hP'e).2
  have h4 := HypPair.mem_perp.mp (Submodule.mem_inf.mp hP'f).2
  exact ⟨P', (Submodule.mem_inf.mp hP'e).1, (Submodule.mem_inf.mp hP'f).1,
    ⟨h3.1, h4.1, h3.2, h4.2⟩⟩

omit [FiniteDimensional K V] in
theorem not_commutes_of_nonorth (hodd : Odd (Nat.card K)) {L S : Subgroup (V ≃ₗ[K] V)}
    {iL iS : V ≃ₗ[K] V} (hL : IsFundamental Q L iL) (hS : IsFundamental Q S iS) (hne : iS ≠ iL)
    {x y : V} (hx : x ∈ negSpace iL) (hy : y ∈ negSpace iS) (hxy : polar Q x y ≠ 0) :
    ¬ Commutes L S := fun hc => by
  rcases orth_or_twin hodd hL hS hc with h | h
  · exact hxy (h x hx y hy)
  · exact hne h

variable {p f : ℕ} [Fact p.Prime] {K' : Type} [Field K'] [Finite K'] [CharP K' p]

theorem orthGeom_perp2 (hK : Nat.card K = p ^ f) (hK' : Nat.card K' = (p ^ f) ^ 2)
    (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 9 ≤ Module.finrank K V) :
    ∀ R₁ ∈ fundSet Q, ∀ R₂ ∈ fundSet Q, ModelAdj (scalars K V) R₁ R₂ →
      (∃ W, WeakCT.LinearBlockStandardPair K W R₁ R₂) →
      ∃ S₁ ∈ fundSet Q, ∃ S₂ ∈ fundSet Q, S₁ ≠ S₂ ∧ Commutes R₁ S₁ ∧ Commutes R₁ S₂ ∧
        ¬ Commutes R₂ S₁ ∧ ¬ Commutes R₂ S₂ := by
  rintro R₁ ⟨i₁, h₁⟩ R₂ ⟨i₂, h₂⟩ hadj ⟨W, hW⟩
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨cm, N, C⟩ := adj_data hodd hdim h₁ h₂ hadj
  obtain ⟨pd, hdich⟩ := lemma_6_10_dichotomy hK hK' hodd h₁ h₂ cm N C
  have hs₂ : HasSingularVector Q (negSpace i₁ ⊓ negSpace i₂) := by
    rcases hdich with ⟨hs, -⟩ | ⟨-, hu⟩
    · exact hs
    · exfalso
      have hW' : WeakCT.LinearBlockStandardPair K (R₁ ⊔ R₂) R₁ R₂ := linear_eq_sup hW ▸ hW
      exact not_linear_and_unitary hK hK' hodd hW' hu
  have hs₃ : HasSingularVector Q (posSpace i₁ ⊓ negSpace i₂) := pd.type₂₃.mp hs₂
  obtain ⟨P, hPe, hPf, hPU⟩ := exists_hypPair_of_hasSingularVector pd.nondeg₃ pd.finrank_U₃ hs₃
  have hnegdec := pd.negSpace_i₂
  obtain ⟨F₁, rfl, rfl⟩ := h₁
  obtain ⟨F₂, rfl, rfl⟩ := h₂
  have hP₁e : P.e ∈ F₁.perp := by
    have := (Submodule.mem_inf.mp hPe).1
    rwa [posSpace_La_neg_one h2] at this
  have hP₁f : P.f ∈ F₁.perp := by
    have := (Submodule.mem_inf.mp hPf).1
    rwa [posSpace_La_neg_one h2] at this
  obtain ⟨P', hP'e, hP'f, hort⟩ := exists_hypPair_orth hodd hQ hdim F₁ P hP₁e hP₁f
  let FS : Models.OrthogonalPairs.Frame Q := ⟨P, P', hort⟩
  have hSperp : ∀ y ∈ FS.span, y ∈ F₁.perp := by
    rintro _ ⟨X, rfl⟩
    rw [Frame.incl_apply]
    exact add_mem (add_mem (add_mem (Submodule.smul_mem _ _ hP₁e) (Submodule.smul_mem _ _ hP₁f))
      (Submodule.smul_mem _ _ hP'e)) (Submodule.smul_mem _ _ hP'f)
  have hcomm : ∀ G : Models.OrthogonalPairs.Frame Q, (∀ y ∈ G.span, y ∈ F₁.perp) →
      Commutes F₁.La.range G.La.range := by
    intro G hG
    have horth : ∀ X Y, polar Q (F₁.incl X) (G.incl Y) = 0 := fun X Y => by
      rw [polar_comm]
      exact (Frame.mem_perp_iff_forall_incl F₁).mp (hG _ ⟨Y, rfl⟩) X
    rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
    exact Frame.La_comm_of_orth horth A B
  have hne : FS.La (-1) ≠ F₂.La (-1) := by
    intro heq
    have hspanS : FS.span = F₂.span := by
      rw [← negSpace_La_neg_one h2, ← negSpace_La_neg_one h2, heq]
    have he' : P'.e ∈ F₂.span := hspanS ▸ FS.e₂_mem_span
    have hf' : P'.f ∈ F₂.span := hspanS ▸ FS.f₂_mem_span
    have hU₃ : (posSpace (F₁.La (-1)) ⊓ negSpace (F₂.La (-1))) ≤
        LinearMap.ker (polarBilin Q P'.e) := by
      rw [hPU, Submodule.span_le]
      rintro _ (rfl | rfl)
      · show polarBilin Q P'.e P.e = 0
        rw [polarBilin_apply_apply, polar_comm]
        exact hort.ee
      · show polarBilin Q P'.e P.f = 0
        rw [polarBilin_apply_apply, polar_comm]
        exact hort.fe
    have horth : ∀ w ∈ F₂.span, polar Q P'.e w = 0 := by
      intro w hw
      have hw' : w ∈ negSpace (F₂.La (-1)) := by rwa [negSpace_La_neg_one h2]
      rw [hnegdec] at hw'
      obtain ⟨u, hu, u', hu', rfl⟩ := Submodule.mem_sup.mp hw'
      rw [polar_add_right]
      have hu1 : u ∈ F₁.span := by
        have := (Submodule.mem_inf.mp hu).1
        rwa [negSpace_La_neg_one h2] at this
      have h1 : polar Q P'.e u = 0 := by
        obtain ⟨Y, rfl⟩ := hu1
        exact (Frame.mem_perp_iff_forall_incl F₁).mp hP'e Y
      have h3 : polar Q P'.e u' = 0 := by
        have := hU₃ hu'
        rwa [LinearMap.mem_ker, polarBilin_apply_apply] at this
      rw [h1, h3, add_zero]
    have := horth _ hf'
    rw [P'.polar_ef] at this
    exact one_ne_zero this
  have hx : P.e ∈ negSpace (F₂.La (-1)) := (Submodule.mem_inf.mp hPe).2
  have hy : P.f ∈ negSpace (FS.La (-1)) := by
    rw [negSpace_La_neg_one h2]
    exact FS.f₁_mem_span
  have hxy : polar Q P.e P.f ≠ 0 := by
    rw [P.polar_ef]
    exact one_ne_zero
  refine ⟨FS.La.range, ⟨_, IsFundamental.of_frame FS⟩, FS.swap.La.range,
    ⟨_, IsFundamental.of_frame_swap FS⟩, Frame.La_range_ne_swap_La_range FS, hcomm FS hSperp,
    hcomm FS.swap (fun y hy => hSperp y (by rwa [Frame.span_eq_swap_span] at hy)),
    not_commutes_of_nonorth hodd (IsFundamental.of_frame F₂) (IsFundamental.of_frame FS) hne hx hy hxy,
    not_commutes_of_nonorth hodd (IsFundamental.of_frame F₂) (IsFundamental.of_frame_swap FS) hne hx hy hxy⟩

theorem orthGeom_model (hK : Nat.card K = p ^ f) (hK' : Nat.card K' = (p ^ f) ^ 2)
    (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 9 ≤ Module.finrank K V) : OrthGeom (scalars K V) (fundSet Q) K :=
  ⟨orthGeom_star hodd hdim, orthGeom_sign hK hK' hodd hdim, orthGeom_perp2 hK hK' hodd hQ hdim⟩

end Perp

end Geometry

end CFSG.ClassicalInvolution.RouteD.Gaps
