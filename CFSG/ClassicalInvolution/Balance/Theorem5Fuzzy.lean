module

public import CFSG.ClassicalInvolution.Balance.Theorem5Untouched
public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyBalance
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero

public section

namespace CFSG.ClassicalInvolution.Balance.Theorem5

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

section Frames

theorem mem_trivialOnQuot_of_centralizes {J : Subgroup G} {a : G}
    (h : ∀ x ∈ J, a * x = x * a) : a ∈ trivialOnQuot J := by
  have hfix : ∀ y ∈ J, a * y * a⁻¹ = y := fun y hy => by rw [h y hy]; group
  refine ⟨?_, fun x hx => ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => by rw [hfix x hx]; exact hx, fun hx => ?_⟩
    have h2 : a * (a * x * a⁻¹) * a⁻¹ = a * x * a⁻¹ := hfix _ hx
    have h3 : a * x * a⁻¹ = x := by
      calc a * x * a⁻¹ = a⁻¹ * (a * (a * x * a⁻¹) * a⁻¹) * a := by group
        _ = a⁻¹ * (a * x * a⁻¹) * a := by rw [h2]
        _ = x := by group
    exact h3 ▸ hx
  · rw [(commutatorElement_eq_one_iff_mul_comm).mpr (h x hx)]
    exact one_mem _

@[expose] def FuzzyFrameOn (p f : ℕ) [Fact p.Prime] (Ω : Set (Subgroup G)) (A : Subgroup G) :
    Prop :=
  ∃ (J : Fin 3 → Subgroup G) (z : Fin 3 → G),
    (∀ i, J i ∈ Ω ∧ IsClassicalMember p f (J i) (z i)) ∧ A = Subgroup.closure (Set.range z) ∧
      IsElemAbelian 2 A ∧ Nat.card A = 8 ∧ ∀ i, A ≤ trivialOnQuot (J i)

@[expose] def fuzzyVertices (p f : ℕ) [Fact p.Prime] (Ω : Set (Subgroup G)) (A : Subgroup G) :
    Set G :=
  {z | z ∈ A ∧ ∃ J ∈ Ω, IsClassicalMember p f J z ∧ A ≤ trivialOnQuot J}

theorem FuzzyFrameOn.exists_vertex {A : Subgroup G} (h : FuzzyFrameOn p f Ω A) :
    ∃ z, z ∈ fuzzyVertices p f Ω A := by
  obtain ⟨J, z, hJ, hA, -, -, htriv⟩ := h
  exact ⟨z 0, hA ▸ Subgroup.subset_closure ⟨0, rfl⟩, J 0, (hJ 0).1, (hJ 0).2, htriv 0⟩

theorem mem_trivialOnQuot_conj_of_mem {J : Subgroup G} {a : G} (h : a ∈ trivialOnQuot J) (g : G) :
    g * a * g⁻¹ ∈ trivialOnQuot (conjSub g J) := by
  obtain ⟨hnorm, hcomm⟩ := h
  refine ⟨?_, fun y hy => ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro u
    have h1 := Subgroup.mem_normalizer_iff.mp hnorm (g⁻¹ * u * g)
    have e : g * a * g⁻¹ * u * (g * a * g⁻¹)⁻¹ = g * (a * (g⁻¹ * u * g) * a⁻¹) * g⁻¹ := by
      group
    rw [mem_conjSub_iff, e, mem_conjSub_iff]
    have e2 : g⁻¹ * (g * (a * (g⁻¹ * u * g) * a⁻¹) * g⁻¹) * g = a * (g⁻¹ * u * g) * a⁻¹ := by
      group
    rw [e2]
    exact h1
  · have hy' : g⁻¹ * y * g ∈ J := mem_conjSub_iff.mp hy
    have h1 := hcomm _ hy'
    rw [oddCoreIn_conjSub_eq, mem_conjSub_iff]
    have e : g⁻¹ * ⁅g * a * g⁻¹, y⁆ * g = ⁅a, g⁻¹ * y * g⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact h1

theorem FuzzyFrameOn.map (hΩ : ConjInvariant Ω) {A : Subgroup G} (h : FuzzyFrameOn p f Ω A)
    (g : G) : FuzzyFrameOn p f Ω (A.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨J, z, hJ, hAdef, hel, hcard, htriv⟩ := h
  refine ⟨fun i => conjSub g (J i), fun i => g * z i * g⁻¹, fun i => ⟨hΩ g _ (hJ i).1,
    (hJ i).2.conj g⟩, ?_, isElemAbelian_two_map hel g, ?_, ?_⟩
  · rw [hAdef, MonoidHom.map_closure]
    congr 1
    ext w
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨z i, ⟨i, rfl⟩, rfl⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hcard
  · intro i x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    exact mem_trivialOnQuot_conj_of_mem (htriv i ha) g

theorem mem_fuzzyVertices_map (hΩ : ConjInvariant Ω) {A : Subgroup G} {z : G}
    (h : z ∈ fuzzyVertices p f Ω A) (g : G) :
    g * z * g⁻¹ ∈ fuzzyVertices p f Ω (A.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hzA, J, hJΩ, hJ, htriv⟩ := h
  refine ⟨⟨z, hzA, rfl⟩, conjSub g J, hΩ g J hJΩ, hJ.conj g, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  exact mem_trivialOnQuot_conj_of_mem (htriv ha) g

theorem fuzzyFrameOn_of_indepTripleOn {A : Subgroup G} (h : IndepTripleOn p f Ω A) :
    FuzzyFrameOn p f Ω A := by
  obtain ⟨K, z, hK, hcomm, hAdef, hel, hcard⟩ := h
  refine ⟨K, z, hK, hAdef, hel, hcard, fun i a ha => ?_⟩
  have hKA : K i ≤ Subgroup.centralizer ((Subgroup.closure (Set.range z) : Subgroup G) : Set G) :=
    triple_centralizes hK hcomm i
  rw [hAdef] at ha
  exact mem_trivialOnQuot_of_centralizes fun x hx =>
    Subgroup.mem_centralizer_iff.mp (hKA hx) a ha

end Frames

section Bridge

theorem mem_centralizer_of_alphaCore_eq_bot {J : Subgroup G} {z₁ z₂ : G}
    (hJ : IsClassicalMember p f J z₁) (hz₂ : z₂ ∈ trivialOnQuot J) (hz₂sq : z₂ * z₂ = 1)
    (hz₁ne : z₁ ≠ 1) (hα : alphaCore (Subgroup.closure ({z₁, z₂} : Set G)) = ⊥) :
    ∀ x ∈ J, z₂ * x = x * z₂ := by
  intro x hx
  have hA : IsPGroup 2 (Subgroup.zpowers z₂) := isPGroup_zpowers_of_mul_self_eq_one hz₂sq
  have hAJ : Subgroup.zpowers z₂ ≤ trivialOnQuot J := Subgroup.zpowers_le.mpr hz₂
  obtain ⟨h, hh, n, hn, hxhn⟩ := exists_mem_inf_centralizer_mul hA hAJ hx
  have hn1 : n ∈ oddCoreIn (Subgroup.centralizer ({z₁} : Set G)) :=
    oddCoreIn_le_of_isSubnormal hJ.subnormal hn
  have hz₁F : z₁ ∈ Subgroup.closure ({z₁, z₂} : Set G) := Subgroup.subset_closure (by simp)
  have hz₂F : z₂ ∈ Subgroup.closure ({z₁, z₂} : Set G) := Subgroup.subset_closure (by simp)
  have hcomm : ⁅n, z₂⁆ ∈ alphaCore (Subgroup.closure ({z₁, z₂} : Set G)) :=
    commutator_le_alphaCore (Subgroup.commutator_mem_commutator
      (involutionOddCore_le_uCore hz₁F hz₁ne hn1) hz₂F)
  rw [hα, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hcomm
  have hh' : z₂ * h = h * z₂ :=
    Subgroup.mem_centralizer_iff.mp hh.2 z₂ (Subgroup.mem_zpowers z₂)
  calc z₂ * x = z₂ * (h * n) := by rw [hxhn]
    _ = (z₂ * h) * n := by rw [mul_assoc]
    _ = (h * z₂) * n := by rw [hh']
    _ = h * (z₂ * n) := by rw [mul_assoc]
    _ = h * (n * z₂) := by rw [← hcomm]
    _ = x * z₂ := by rw [← mul_assoc, ← hxhn]

theorem exactMembers_of_alphaCore_eq_bot_edge [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h9 : p ^ f ≠ 9)
    (hΩ : InClass p f Ω) (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hIH : LocalLieSystems p f Ω) {J : Subgroup G} {z₁ z₂ : G} (hJΩ : J ∈ Ω)
    (hJ : IsClassicalMember p f J z₁) (hz₂ : z₂ ∈ trivialOnQuot J) (hz₂sq : z₂ * z₂ = 1)
    (hz₁z₂ : z₁ * z₂ = z₂ * z₁) (hα : alphaCore (Subgroup.closure ({z₁, z₂} : Set G)) = ⊥) :
    ExactMembers Ω := by
  have hc := hJ.isCentralInvolution
  have hz₁ne : z₁ ≠ 1 := hc.ne_one
  have hcent := mem_centralizer_of_alphaCore_eq_bot hJ hz₂ hz₂sq hz₁ne hα
  have hF : IsElemAbelian 2 (Subgroup.closure ({z₁, z₂} : Set G)) :=
    isElemAbelian_closure_of_commuting_involutions (by
      rintro s (rfl | hs)
      · exact hc.sq
      · rw [Set.mem_singleton_iff.mp hs]
        exact hz₂sq) (by
      rintro s (rfl | hs) t (rfl | ht)
      · rfl
      · rw [Set.mem_singleton_iff.mp ht]
        exact hz₁z₂
      · rw [Set.mem_singleton_iff.mp hs]
        exact hz₁z₂.symm
      · rw [Set.mem_singleton_iff.mp hs, Set.mem_singleton_iff.mp ht])
  have hKF : J ≤ Subgroup.centralizer ((Subgroup.closure ({z₁, z₂} : Set G) : Subgroup G) :
      Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hle : Subgroup.closure ({z₁, z₂} : Set G) ≤ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.closure_le]
      rintro s (rfl | hs)
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        exact hc.central x hx
      · rw [Set.mem_singleton_iff.mp hs, SetLike.mem_coe,
          Subgroup.mem_centralizer_singleton_iff]
        exact hcent x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg)
  have hΔ : deltaCore (Subgroup.closure ({z₁, z₂} : Set G)) = ⊥ := by
    have := deltaCore_le_alphaCore (F := Subgroup.closure ({z₁, z₂} : Set G))
    rw [hα] at this
    exact le_bot_iff.mp this
  exact exactMembers_of_deltaCore_eq_bot hnab hp2 hq h9 ModelFacts.modelClauseZero
    fundamentalWholeA1 hΩ hsingle hIH hJΩ hJ hF hKF hΔ

end Bridge

section Connectivity

@[expose] def ShareFourIn (𝒯 : Set (Subgroup G)) (X Y : Subgroup G) : Prop :=
  X ∈ 𝒯 ∧ Y ∈ 𝒯 ∧ ShareFour X Y

@[expose] def FrameAdj (𝒯 : Set (Subgroup G)) (cl : Subgroup G → Set G) (z w : G) : Prop :=
  ∃ A ∈ 𝒯, z ∈ cl A ∧ w ∈ cl A

omit [Finite G] in
theorem shareFour_connected_of_vertexGraph {𝒯 : Set (Subgroup G)} (cl : Subgroup G → Set G)
    (hne : ∀ A ∈ 𝒯, (cl A).Nonempty)
    (hvert : ∀ A ∈ 𝒯, ∀ A' ∈ 𝒯, ∀ a ∈ cl A, ∀ a' ∈ cl A',
      Relation.ReflTransGen (FrameAdj 𝒯 cl) a a')
    (hlink : ∀ a : G, ∀ A ∈ 𝒯, ∀ A' ∈ 𝒯, a ∈ cl A → a ∈ cl A' →
      Relation.ReflTransGen (ShareFourIn 𝒯) A A') :
    ∀ A ∈ 𝒯, ∀ A' ∈ 𝒯, Relation.ReflTransGen (ShareFourIn 𝒯) A A' := by
  intro A hA A' hA'
  obtain ⟨a, ha⟩ := hne A hA
  obtain ⟨a', ha'⟩ := hne A' hA'
  have key : ∀ b, Relation.ReflTransGen (FrameAdj 𝒯 cl) a b →
      ∀ B ∈ 𝒯, b ∈ cl B → Relation.ReflTransGen (ShareFourIn 𝒯) A B := by
    intro b hb
    induction hb with
    | refl => exact fun B hB hbB => hlink a A hA B hB ha hbB
    | @tail b c _ hstep ih =>
      obtain ⟨C, hC, hbC, hcC⟩ := hstep
      exact fun B hB hcB => (ih C hC hbC).trans (hlink c C hC B hB hcC hcB)
  exact key a' (hvert A hA A' hA' a ha a' ha') A' hA' ha'

theorem reflTransGen_frameAdj_of_adj (hp2 : p ≠ 2) (hf : 0 < f) (E : Subgroup G → Subgroup G → Prop)
    (hcls : ∀ M ∈ Ω, ∃ z, IsClassicalMember p f M z)
    (hconn : ∀ L ∈ Ω, ∀ L' ∈ Ω,
      Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ E M N) L L')
    {𝒯 : Set (Subgroup G)} (cl : Subgroup G → Set G)
    (hedge : ∀ M ∈ Ω, ∀ N ∈ Ω, ∀ zM zN : G, IsClassicalMember p f M zM →
      IsClassicalMember p f N zN → E M N → zM ≠ zN → FrameAdj 𝒯 cl zM zN)
    {M M' : Subgroup G} (hM : M ∈ Ω) (hM' : M' ∈ Ω) {a a' : G}
    (ha : IsClassicalMember p f M a) (ha' : IsClassicalMember p f M' a') :
    Relation.ReflTransGen (FrameAdj 𝒯 cl) a a' := by
  have key : ∀ X, Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ E M N) M X →
      X ∈ Ω ∧ ∀ z, IsClassicalMember p f X z → Relation.ReflTransGen (FrameAdj 𝒯 cl) a z := by
    intro X hX
    induction hX with
    | refl =>
      refine ⟨hM, fun z hz => ?_⟩
      have hza : z = a := ha.eq_of_isCentralInvolution hp2 hf hz.isCentralInvolution
      rw [hza]
    | @tail b c _ hstep ih =>
      obtain ⟨hbΩ, hb⟩ := ih
      refine ⟨hstep.1, fun z hz => ?_⟩
      obtain ⟨zb, hzb⟩ := hcls b hbΩ
      by_cases hzz : zb = z
      · rw [← hzz]
        exact hb zb hzb
      · exact (hb zb hzb).tail (hedge b hbΩ c hstep.1 zb z hzb hz hstep.2 hzz)
  exact (key M' (hconn M hM M' hM')).2 a' ha'

theorem shareFour_connected_of_local (hp2 : p ≠ 2) (hf : 0 < f) (hΩ : InClass p f Ω)
    (hconn : OmegaConnected Ω) {𝒯 : Set (Subgroup G)} (cl : Subgroup G → Set G)
    (hcl : ∀ A ∈ 𝒯, ∀ z ∈ cl A, ∃ J ∈ Ω, IsClassicalMember p f J z)
    (hne : ∀ A ∈ 𝒯, (cl A).Nonempty)
    (hedge : ∀ M ∈ Ω, ∀ N ∈ Ω, ∀ zM zN : G, IsClassicalMember p f M zM →
      IsClassicalMember p f N zN → Commutes M N → zM ≠ zN →
        ∃ A ∈ 𝒯, zM ∈ cl A ∧ zN ∈ cl A)
    (hlink : ∀ a : G, ∀ A ∈ 𝒯, ∀ A' ∈ 𝒯, a ∈ cl A → a ∈ cl A' →
      Relation.ReflTransGen (ShareFourIn 𝒯) A A') :
    ∀ A ∈ 𝒯, ∀ A' ∈ 𝒯, Relation.ReflTransGen (ShareFourIn 𝒯) A A' :=
  shareFour_connected_of_vertexGraph cl hne (fun A hA A' hA' a ha a' ha' => by
    obtain ⟨M, hMΩ, hMa⟩ := hcl A hA a ha
    obtain ⟨M', hM'Ω, hM'a'⟩ := hcl A' hA' a' ha'
    exact reflTransGen_frameAdj_of_adj hp2 hf Commutes (fun b hb => hΩ.classical b hb) hconn cl
      hedge hMΩ hM'Ω hMa hM'a') hlink

theorem reflTransGen_shareFour_map_of_mem_oddCoreIn {𝒯 : Set (Subgroup G)}
    (hinv : ∀ A ∈ 𝒯, ∀ g : G, A.map (MulAut.conj g).toMonoidHom ∈ 𝒯) {A : Subgroup G}
    (hA : A ∈ 𝒯) (hel : IsElemAbelian 2 A) (hcard : Nat.card A = 8) {b : G} (hb : b ∈ A)
    {y : G} (hy : y ∈ oddCoreIn (Subgroup.centralizer ({b} : Set G))) :
    Relation.ReflTransGen (ShareFourIn 𝒯) A (A.map (MulAut.conj y).toMonoidHom) := by
  set X := oddCoreIn (Subgroup.centralizer ({b} : Set G)) with hX
  have hcomm : ∀ {x w : G}, x ∈ A → w ∈ A → x * w = w * x := fun hx hw =>
    congrArg Subtype.val (hel.1.is_comm.comm (⟨_, hx⟩ : A) ⟨_, hw⟩)
  have hAC : A ≤ Subgroup.centralizer ({b} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm ha hb)
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := fun a ha => normalizer_oddCoreIn _ (hAC ha)
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 2
    Nat.prime_two A X hel (by rw [hcard]; norm_num) hAX
    (Nat.coprime_two_left.mpr (odd_card_oddCoreIn _))
  have hle : X ≤ rankTwoSpan A := by
    conv_lhs => rw [← hgen]
    exact iSup₂_mono fun F _ => inf_le_right
  exact reflTransGen_shareFour_map_of_mem_rankTwoSpan hinv hA (hle hy)

@[expose] def LinkMove (𝒯 : Set (Subgroup G)) (cl : Subgroup G → Set G) (a : G)
    (X Y : Subgroup G) : Prop :=
  X ∈ 𝒯 ∧ Y ∈ 𝒯 ∧ a ∈ cl X ∧ a ∈ cl Y ∧ (ShareFour X Y ∨
    ∃ y ∈ oddCoreIn (Subgroup.centralizer ({a} : Set G)),
      Y = X.map (MulAut.conj y).toMonoidHom)

theorem reflTransGen_shareFourIn_of_linkMove {𝒯 : Set (Subgroup G)}
    (hinv : ∀ A ∈ 𝒯, ∀ g : G, A.map (MulAut.conj g).toMonoidHom ∈ 𝒯)
    (hfr : ∀ A ∈ 𝒯, IsElemAbelian 2 A ∧ Nat.card A = 8) (cl : Subgroup G → Set G)
    (hclA : ∀ A ∈ 𝒯, ∀ z ∈ cl A, z ∈ A) {a : G} {A B : Subgroup G}
    (h : Relation.ReflTransGen (LinkMove 𝒯 cl a) A B) :
    Relation.ReflTransGen (ShareFourIn 𝒯) A B := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    refine ih.trans ?_
    obtain ⟨hX, hY, hXa, hYa, hXY | ⟨y, hy, rfl⟩⟩ := hbc
    · exact Relation.ReflTransGen.single ⟨hX, hY, hXY⟩
    · exact reflTransGen_shareFour_map_of_mem_oddCoreIn hinv hX (hfr _ hX).1 (hfr _ hX).2
        (hclA _ hX a hXa) hy

theorem shareFour_connected_of_vertexGraph_modOdd {𝒯 : Set (Subgroup G)}
    (hinv : ∀ A ∈ 𝒯, ∀ g : G, A.map (MulAut.conj g).toMonoidHom ∈ 𝒯)
    (hfr : ∀ A ∈ 𝒯, IsElemAbelian 2 A ∧ Nat.card A = 8) (cl : Subgroup G → Set G)
    (hclA : ∀ A ∈ 𝒯, ∀ z ∈ cl A, z ∈ A) (hne : ∀ A ∈ 𝒯, (cl A).Nonempty)
    (hvert : ∀ A ∈ 𝒯, ∀ A' ∈ 𝒯, ∀ a ∈ cl A, ∀ a' ∈ cl A',
      Relation.ReflTransGen (FrameAdj 𝒯 cl) a a')
    (hlink : ∀ a : G, ∀ A ∈ 𝒯, ∀ A' ∈ 𝒯, a ∈ cl A → a ∈ cl A' →
      Relation.ReflTransGen (LinkMove 𝒯 cl a) A A') :
    ∀ A ∈ 𝒯, ∀ A' ∈ 𝒯, Relation.ReflTransGen (ShareFourIn 𝒯) A A' :=
  shareFour_connected_of_vertexGraph cl hne hvert fun a A hA A' hA' ha ha' =>
    reflTransGen_shareFourIn_of_linkMove hinv hfr cl hclA (hlink a A hA A' hA' ha ha')

theorem shareFour_connected_of_local_modOdd (hp2 : p ≠ 2) (hf : 0 < f) (hΩ : InClass p f Ω)
    (hconn : OmegaConnected Ω) {𝒯 : Set (Subgroup G)}
    (hinv : ∀ A ∈ 𝒯, ∀ g : G, A.map (MulAut.conj g).toMonoidHom ∈ 𝒯)
    (hfr : ∀ A ∈ 𝒯, IsElemAbelian 2 A ∧ Nat.card A = 8) (cl : Subgroup G → Set G)
    (hclA : ∀ A ∈ 𝒯, ∀ z ∈ cl A, z ∈ A)
    (hcl : ∀ A ∈ 𝒯, ∀ z ∈ cl A, ∃ J ∈ Ω, IsClassicalMember p f J z)
    (hne : ∀ A ∈ 𝒯, (cl A).Nonempty)
    (hedge : ∀ M ∈ Ω, ∀ N ∈ Ω, ∀ zM zN : G, IsClassicalMember p f M zM →
      IsClassicalMember p f N zN → Commutes M N → zM ≠ zN →
        ∃ A ∈ 𝒯, zM ∈ cl A ∧ zN ∈ cl A)
    (hlink : ∀ a : G, ∀ A ∈ 𝒯, ∀ A' ∈ 𝒯, a ∈ cl A → a ∈ cl A' →
      Relation.ReflTransGen (LinkMove 𝒯 cl a) A A') :
    ∀ A ∈ 𝒯, ∀ A' ∈ 𝒯, Relation.ReflTransGen (ShareFourIn 𝒯) A A' :=
  shareFour_connected_of_local hp2 hf hΩ hconn cl hcl hne hedge fun a A hA A' hA' ha ha' =>
    reflTransGen_shareFourIn_of_linkMove hinv hfr cl hclA (hlink a A hA A' hA' ha ha')

omit [Finite G] in
theorem linkMove_connected_of_graph {𝒯 : Set (Subgroup G)} (cl : Subgroup G → Set G) {a : G}
    (hinv : ∀ A ∈ 𝒯, ∀ g : G, A.map (MulAut.conj g).toMonoidHom ∈ 𝒯)
    (hclmap : ∀ A ∈ 𝒯, ∀ z ∈ cl A, ∀ g : G,
      g * z * g⁻¹ ∈ cl (A.map (MulAut.conj g).toMonoidHom))
    (hfix : ∀ y ∈ oddCoreIn (Subgroup.centralizer ({a} : Set G)), y * a * y⁻¹ = a)
    {V : Type*} (four : V → Subgroup G) (hfour : ∀ v, Nat.card (four v) = 4)
    (Adj : V → V → Prop) (hcover : ∀ A ∈ 𝒯, a ∈ cl A → ∃ v, four v ≤ A)
    (hadj : ∀ v w, Adj v w → ∃ B ∈ 𝒯, ∃ y ∈ oddCoreIn (Subgroup.centralizer ({a} : Set G)),
      a ∈ cl B ∧ four v ≤ B ∧ conjSub y (four w) ≤ B)
    (hconn : ∀ v w, Relation.ReflTransGen Adj v w) :
    ∀ A ∈ 𝒯, ∀ A' ∈ 𝒯, a ∈ cl A → a ∈ cl A' →
      Relation.ReflTransGen (LinkMove 𝒯 cl a) A A' := by
  have hshare : ∀ {X Y : Subgroup G} {F : Subgroup G}, X ∈ 𝒯 → Y ∈ 𝒯 → a ∈ cl X → a ∈ cl Y →
      F ≤ X → F ≤ Y → Nat.card F = 4 → Relation.ReflTransGen (LinkMove 𝒯 cl a) X Y := by
    intro X Y F hX hY hXa hYa hFX hFY hF
    refine Relation.ReflTransGen.single ⟨hX, hY, hXa, hYa, Or.inl ⟨F, ⟨hFX, ?_⟩, ⟨hFY, ?_⟩⟩⟩
    · rw [hF]; norm_num
    · rw [hF]; norm_num
  have hconjmove : ∀ {X : Subgroup G}, X ∈ 𝒯 → a ∈ cl X →
      ∀ y ∈ oddCoreIn (Subgroup.centralizer ({a} : Set G)),
        Relation.ReflTransGen (LinkMove 𝒯 cl a) X (X.map (MulAut.conj y).toMonoidHom) := by
    intro X hX hXa y hy
    have hya := hclmap X hX a hXa y
    rw [hfix y hy] at hya
    exact Relation.ReflTransGen.single ⟨hX, hinv X hX y, hXa, hya, Or.inr ⟨y, hy, rfl⟩⟩
  have hstep : ∀ v w, Adj v w → ∃ B ∈ 𝒯, a ∈ cl B ∧ four v ≤ B ∧
      ∀ Y ∈ 𝒯, a ∈ cl Y → four w ≤ Y → Relation.ReflTransGen (LinkMove 𝒯 cl a) B Y := by
    intro v w hvw
    obtain ⟨B, hB, y, hy, hBa, hvB, hwB⟩ := hadj v w hvw
    refine ⟨B, hB, hBa, hvB, fun Y hY hYa hwY => ?_⟩
    have hy' : y⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({a} : Set G)) := inv_mem hy
    have hB'a : a ∈ cl (B.map (MulAut.conj y⁻¹).toMonoidHom) := by
      have h := hclmap B hB a hBa y⁻¹
      rwa [hfix y⁻¹ hy'] at h
    have hwB' : four w ≤ B.map (MulAut.conj y⁻¹).toMonoidHom := by
      have h := conjSub_mono (n := y⁻¹) hwB
      rwa [conjSub_inv_conjSub] at h
    exact (hconjmove hB hBa y⁻¹ hy').trans
      (hshare (hinv B hB y⁻¹) hY hB'a hYa hwB' hwY (hfour w))
  intro A hA A' hA' haA haA'
  obtain ⟨v, hv⟩ := hcover A hA haA
  obtain ⟨w, hw⟩ := hcover A' hA' haA'
  have key : ∀ u, Relation.ReflTransGen Adj v u →
      ∀ Z ∈ 𝒯, a ∈ cl Z → four u ≤ Z → Relation.ReflTransGen (LinkMove 𝒯 cl a) A Z := by
    intro u hu
    induction hu with
    | refl => exact fun Z hZ hZa hvZ => hshare hA hZ haA hZa hv hvZ (hfour v)
    | @tail b c _ hbc ih =>
      intro Z hZ hZa hcZ
      obtain ⟨B, hB, hBa, hbB, hBZ⟩ := hstep b c hbc
      exact (ih B hB hBa hbB).trans (hBZ Z hZ hZa hcZ)
  exact key w (hconn v w) A' hA' haA' hw

end Connectivity

section Assembly

theorem exactMembers_and_localOddCentral_of_balancedFamily [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h9 : p ^ f ≠ 9)
    (hΩ : InClass p f Ω) (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hIH : LocalLieSystems p f Ω)
    (hlay : ∀ A' : Subgroup G, IndepTripleOn p f Ω A' → ∀ a ∈ A', a ≠ 1 →
      ComponentLayersAt Ω A' a)
    {𝒯 : Set (Subgroup G)} (hbal : ∀ A ∈ 𝒯, RankThreeBalance A)
    (hinv : ∀ A ∈ 𝒯, ∀ g : G, A.map (MulAut.conj g).toMonoidHom ∈ 𝒯)
    (hcon : ∀ A ∈ 𝒯, ∀ A' ∈ 𝒯, Relation.ReflTransGen (ShareFourIn 𝒯) A A')
    {K : Fin 3 → Subgroup G} {z : Fin 3 → G}
    (hK : ∀ i, K i ∈ Ω ∧ IsClassicalMember p f (K i) (z i))
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, x * y = y * x) {A : Subgroup G}
    (hAdef : A = Subgroup.closure (Set.range z)) (hel : IsElemAbelian 2 A)
    (hcard : Nat.card A = 8) (hA : A ∈ 𝒯) :
    ExactMembers Ω ∧ ∀ L ∈ Ω, ∀ w : G, IsClassicalMember p f L w → LocalOddCentral Ω {w} := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hO := componentClassificationOddCore_eq_bot_of_simple hnab
  have hα := alphaCore_eq_bot_of_connected_frames hO hinv hbal hcon
  have hΔ := deltaCore_eq_bot_of_connected_frames hO hinv hbal hcon
  obtain ⟨F₀, hF₀⟩ := exists_mem_signalizerFunctorEk (hbal A hA)
  have hK0A : K 0 ≤ Subgroup.centralizer (A : Set G) := by
    rw [hAdef]
    exact triple_centralizes hK hcomm 0
  have hex : ExactMembers Ω :=
    exactMembers_of_deltaCore_eq_bot hnab hp2 hq h9 ModelFacts.modelClauseZero
      fundamentalWholeA1 hΩ hsingle hIH (hK 0).1 (hK 0).2
      (CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le 2 hel hF₀.1)
      (hK0A.trans (Subgroup.centralizer_le hF₀.1)) (hΔ A hA F₀ hF₀)
  have hP1 : LocalOddCentral Ω {z 0} :=
    localOddCentral_of_indepTriple_pair hnab hp2 hq hΩ hIH hex hlay hK hcomm hAdef hel hcard hF₀
      (hα A hA F₀ hF₀) (i := 0) (j := 1) (by decide) (x := z 0)
      (Subgroup.subset_closure (by simp)) (hK 0).2.ne_one
  exact ⟨hex, localOddCentral_of_classicalMember hp2 hf hΩ hsingle (hK 0).1 (hK 0).2 hP1⟩

end Assembly

section AxisFrames

theorem FuzzyFrameOn.exists_axisTriangle {A : Subgroup G} (h : FuzzyFrameOn p f Ω A) :
    ∃ (J₁ J₂ J₃ : Subgroup G) (z₁ z₂ z₃ : G), J₁ ∈ Ω ∧ J₂ ∈ Ω ∧ J₃ ∈ Ω ∧
      AxisTriangle p f J₁ J₂ J₃ z₁ z₂ z₃ ∧ z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃ ∧ z₁ * z₂ ≠ z₃ ∧
        triangleAxis z₁ z₂ z₃ = A := by
  obtain ⟨J, z, hJ, hAdef, hel, hcard, htriv⟩ := h
  have hzA : ∀ i, z i ∈ A := fun i => hAdef ▸ Subgroup.subset_closure ⟨i, rfl⟩
  have hAc : ∀ {x y : G}, x ∈ A → y ∈ A → x * y = y * x := fun hx hy =>
    congrArg Subtype.val (hel.1.is_comm.comm (⟨_, hx⟩ : A) ⟨_, hy⟩)
  have hsq : ∀ i, z i * z i = 1 := fun i => sq_eq_one (hJ i).2
  have hrange : Set.range z = ({z 0, z 1, z 2} : Set G) := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
  have hle4 : ∀ i j : Fin 3, (∀ k, z k ∈ Subgroup.closure ({z i, z j} : Set G)) → False := by
    intro i j hk
    have hAle : A ≤ Subgroup.closure ({z i, z j} : Set G) := by
      rw [hAdef, Subgroup.closure_le]
      rintro _ ⟨k, rfl⟩
      exact hk k
    have h8 := Subgroup.card_le_of_le hAle
    have h4 := card_closure_pair_le_four (hsq i) (hsq j) (hAc (hzA i) (hzA j))
    omega
  have m0 : ∀ i j : Fin 3, z i ∈ Subgroup.closure ({z i, z j} : Set G) := fun i j =>
    Subgroup.subset_closure (by simp)
  have m1 : ∀ i j : Fin 3, z j ∈ Subgroup.closure ({z i, z j} : Set G) := fun i j =>
    Subgroup.subset_closure (by simp)
  refine ⟨J 0, J 1, J 2, z 0, z 1, z 2, (hJ 0).1, (hJ 1).1, (hJ 2).1,
    ⟨(hJ 0).2, (hJ 1).2, (hJ 2).2, hAc (hzA 0) (hzA 1), hAc (hzA 0) (hzA 2),
      hAc (hzA 1) (hzA 2), htriv 0 (hzA 1), htriv 0 (hzA 2), htriv 1 (hzA 0), htriv 1 (hzA 2),
      htriv 2 (hzA 0), htriv 2 (hzA 1)⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro h01
    refine hle4 0 2 fun k => ?_
    fin_cases k
    · exact m0 0 2
    · rw [show z ⟨1, by norm_num⟩ = z 0 from h01.symm]
      exact m0 0 2
    · exact m1 0 2
  · intro h02
    refine hle4 0 1 fun k => ?_
    fin_cases k
    · exact m0 0 1
    · exact m1 0 1
    · rw [show z ⟨2, by norm_num⟩ = z 0 from h02.symm]
      exact m0 0 1
  · intro h12
    refine hle4 0 1 fun k => ?_
    fin_cases k
    · exact m0 0 1
    · exact m1 0 1
    · rw [show z ⟨2, by norm_num⟩ = z 1 from h12.symm]
      exact m1 0 1
  · intro h012
    refine hle4 0 1 fun k => ?_
    fin_cases k
    · exact m0 0 1
    · exact m1 0 1
    · rw [show z ⟨2, by norm_num⟩ = z 0 * z 1 from h012.symm]
      exact Subgroup.mul_mem _ (m0 0 1) (m1 0 1)
  · rw [triangleAxis, hAdef, hrange]

theorem rankThreeBalance_of_fuzzyFrameOn
    [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hBelow : CITBelowU p f (Nat.card G)) {A : Subgroup G}
    (hA : FuzzyFrameOn p f Ω A)
    (hI : ∀ (J₁ J₂ J₃ : Subgroup G) (z₁ z₂ z₃ : G), J₁ ∈ Ω → J₂ ∈ Ω → J₃ ∈ Ω →
      AxisTriangle p f J₁ J₂ J₃ z₁ z₂ z₃ → triangleAxis z₁ z₂ z₃ = A →
        ∀ b ∈ A, b ≠ 1 → FuzzyInputs p f (triangleSecFamily J₁ J₂ J₃ b) b) :
    RankThreeBalance A := by
  obtain ⟨J₁, J₂, J₃, z₁, z₂, z₃, h1, h2, h3, hT, hne12, hne13, hne23, hind, hax⟩ :=
    hA.exists_axisTriangle
  have hB := hT.rankThreeBalance hnab hp2 hq ModelFacts.modelClauseZero fundamentalWholeA1 hBelow
    hne12 hne13 hne23 hind fun b hb hb1 =>
      hI J₁ J₂ J₃ z₁ z₂ z₃ h1 h2 h3 hT hax b (hax ▸ hb) hb1
  rwa [hax] at hB

end AxisFrames

section Inputs

@[expose] def fuzzyFrames (p f : ℕ) [Fact p.Prime] (Ω : Set (Subgroup G)) : Set (Subgroup G) :=
  {A | FuzzyFrameOn p f Ω A}

abbrev MemberClass : Type 1 := ∀ {H : Type} [Group H], Subgroup H → Set (Subgroup H)

@[expose] def conjMembers : MemberClass := fun K => CoreAssembly.conjClass K

omit [Finite G] in
theorem conjInvariant_conjMembers (K : Subgroup G) : ConjInvariant (conjMembers K) := by
  rintro n _ ⟨g, rfl⟩
  exact ⟨n * g, conjSub_mul n g K⟩

@[expose] def FuzzyModelInputs (p f : ℕ) [Fact p.Prime] (𝒞 : MemberClass) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z → CITBelowU p f (Nat.card G) →
      RouteD.DeltaConnected (CoreAssembly.conjClass K) →
        CoreAssembly.IndepTriple p f (CoreAssembly.conjClass K) →
        ∀ (J₁ J₂ J₃ : Subgroup G) (z₁ z₂ z₃ : G), J₁ ∈ 𝒞 K → J₂ ∈ 𝒞 K → J₃ ∈ 𝒞 K →
          AxisTriangle p f J₁ J₂ J₃ z₁ z₂ z₃ → ∀ b ∈ triangleAxis z₁ z₂ z₃, b ≠ 1 →
            FuzzyInputs p f (triangleSecFamily J₁ J₂ J₃ b) b

@[expose] def FuzzyFrameBalance (p f : ℕ) [Fact p.Prime] (𝒞 : MemberClass) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z → CITBelowU p f (Nat.card G) →
      RouteD.DeltaConnected (CoreAssembly.conjClass K) →
        CoreAssembly.IndepTriple p f (CoreAssembly.conjClass K) →
        ∀ A ∈ fuzzyFrames p f (𝒞 K), RankThreeBalance A

theorem fuzzyFrameBalance_of_modelInputs
    {𝒞 : MemberClass} (hin : FuzzyModelInputs p f 𝒞) :
    FuzzyFrameBalance p f 𝒞 := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hind A hA
  exact rankThreeBalance_of_fuzzyFrameOn hnab hp2 hq hBelow hA fun J₁ J₂ J₃ z₁ z₂ z₃ h1 h2 h3 hT hax
    b hb hb1 => hin G hnab hp2 hq K z hz hBelow hconn hind J₁ J₂ J₃ z₁ z₂ z₃ h1 h2 h3 hT b
      (hax ▸ hb) hb1

@[expose] def FuzzyAxisExact (p f : ℕ) [Fact p.Prime] (𝒞 : MemberClass) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z → CITBelowU p f (Nat.card G) →
      RouteD.DeltaConnected (CoreAssembly.conjClass K) →
        ∀ A, IndepTripleOn p f (CoreAssembly.conjClass K) A → A ∈ fuzzyFrames p f (𝒞 K)

theorem fuzzyAxisExact_conjMembers : FuzzyAxisExact p f conjMembers := by
  intro G _ _ _ _ _ _ K _ _ _ _ A hA
  exact fuzzyFrameOn_of_indepTripleOn hA

@[expose] def FuzzyVertexConn (p f : ℕ) [Fact p.Prime] (𝒞 : MemberClass) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z → CITBelowU p f (Nat.card G) →
      RouteD.DeltaConnected (CoreAssembly.conjClass K) →
        CoreAssembly.IndepTriple p f (CoreAssembly.conjClass K) →
        ∀ z₁ z₂ : G, (∃ J ∈ 𝒞 K, IsClassicalMember p f J z₁) →
          (∃ J ∈ 𝒞 K, IsClassicalMember p f J z₂) →
          Relation.ReflTransGen (FrameAdj (fuzzyFrames p f (𝒞 K)) (fuzzyVertices p f (𝒞 K))) z₁ z₂

abbrev MemberAdj : Type 1 := ∀ {H : Type} [Group H], Subgroup H → Subgroup H → Prop

@[expose] def commuteAdj : MemberAdj := fun M N => Commutes M N

@[expose] def FuzzyMemberConn (p f : ℕ) [Fact p.Prime] (𝒞 : MemberClass) (E : MemberAdj) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z → CITBelowU p f (Nat.card G) →
      RouteD.DeltaConnected (CoreAssembly.conjClass K) →
        CoreAssembly.IndepTriple p f (CoreAssembly.conjClass K) →
        (∀ M ∈ 𝒞 K, ∃ w, IsClassicalMember p f M w) ∧
          ∀ L ∈ 𝒞 K, ∀ L' ∈ 𝒞 K,
            Relation.ReflTransGen (fun M N : Subgroup G => N ∈ 𝒞 K ∧ E M N) L L'

theorem fuzzyMemberConn_conjMembers : FuzzyMemberConn p f conjMembers commuteAdj := by
  intro G _ _ _ _ _ _ K z hz _ hconn _
  exact ⟨fun M hM => (inClass_conjugates hz).classical M hM, omegaConnected_of_deltaConnected hconn⟩

@[expose] def FuzzyEdgeInFrame (p f : ℕ) [Fact p.Prime] (𝒞 : MemberClass) (E : MemberAdj) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z → CITBelowU p f (Nat.card G) →
      RouteD.DeltaConnected (CoreAssembly.conjClass K) →
        CoreAssembly.IndepTriple p f (CoreAssembly.conjClass K) →
        ∀ M ∈ 𝒞 K, ∀ N ∈ 𝒞 K, ∀ zM zN : G, IsClassicalMember p f M zM →
          IsClassicalMember p f N zN → E M N → zM ≠ zN →
            FrameAdj (fuzzyFrames p f (𝒞 K)) (fuzzyVertices p f (𝒞 K)) zM zN

theorem fuzzyVertexConn_of_adj {𝒞 : MemberClass} {E : MemberAdj}
    (hmem : FuzzyMemberConn p f 𝒞 E) (hedge : FuzzyEdgeInFrame p f 𝒞 E) :
    FuzzyVertexConn p f 𝒞 := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hind z₁ z₂ ⟨M, hM, hMz⟩ ⟨M', hM', hM'z⟩
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  obtain ⟨hcls, hc⟩ := hmem G hnab hp2 hq K z hz hBelow hconn hind
  exact reflTransGen_frameAdj_of_adj hp2 hf (fun M N => E M N) hcls hc (fuzzyVertices p f (𝒞 K))
    (hedge G hnab hp2 hq K z hz hBelow hconn hind) hM hM' hMz hM'z

@[expose] def FuzzyLinkConn (p f : ℕ) [Fact p.Prime] (𝒞 : MemberClass) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z → CITBelowU p f (Nat.card G) →
      RouteD.DeltaConnected (CoreAssembly.conjClass K) →
        CoreAssembly.IndepTriple p f (CoreAssembly.conjClass K) →
        ∀ a : G, ∀ A ∈ fuzzyFrames p f (𝒞 K), ∀ A' ∈ fuzzyFrames p f (𝒞 K),
          a ∈ fuzzyVertices p f (𝒞 K) A → a ∈ fuzzyVertices p f (𝒞 K) A' →
            Relation.ReflTransGen
              (LinkMove (fuzzyFrames p f (𝒞 K)) (fuzzyVertices p f (𝒞 K)) a) A A'

end Inputs

section BootTriple

theorem bootTriple_of_fuzzyFrames (𝒞 : MemberClass) (hlay : TriangleLayers p f)
    (hinv : ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G), ConjInvariant (𝒞 K))
    (hbal : FuzzyFrameBalance p f 𝒞) (hexact : FuzzyAxisExact p f 𝒞)
    (hvert : FuzzyVertexConn p f 𝒞) (hlink : FuzzyLinkConn p f 𝒞)
    (hcov9 : p ^ f = 9 → ConnectedFramesExist p f) (hexotic : ExoticLeviBlock p f) :
    CoreAssembly.BootTriple p f := by
  by_cases h9 : p ^ f = 9
  · exact bootTriple_of_triangleLayers hlay (hcov9 h9) hexotic
  · intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hind
    have hΩ : InClass p f (CoreAssembly.conjClass K) := inClass_conjugates hz
    have hIH := localLieSystems_of_citBelowU hΩ hBelow
    have hind' := hind
    obtain ⟨K', z', hK', hcomm, hel, hcard⟩ := hind
    have hAex : IndepTripleOn p f (CoreAssembly.conjClass K) (Subgroup.closure (Set.range z')) :=
      ⟨K', z', hK', hcomm, rfl, hel, hcard⟩
    have hA : Subgroup.closure (Set.range z') ∈ fuzzyFrames p f (𝒞 K) :=
      hexact G hnab hp2 hq K z hz hBelow hconn _ hAex
    have hf : 0 < f := by
      rcases Nat.eq_zero_or_pos f with rfl | h
      · simp at hq
      · exact h
    have hmap : ∀ A ∈ fuzzyFrames p f (𝒞 K), ∀ g : G,
        A.map (MulAut.conj g).toMonoidHom ∈ fuzzyFrames p f (𝒞 K) := fun A hA g =>
      FuzzyFrameOn.map (hinv G K) hA g
    have hcon := shareFour_connected_of_vertexGraph_modOdd (𝒯 := fuzzyFrames p f (𝒞 K)) hmap
      (fun A hA => by
        obtain ⟨J, z, -, -, hel, hcard, -⟩ := hA
        exact ⟨hel, hcard⟩)
      (fuzzyVertices p f (𝒞 K)) (fun A _ z hz => hz.1) (fun A hA => hA.exists_vertex)
      (fun A _ A' _ a ha a' ha' =>
        hvert G hnab hp2 hq K z hz hBelow hconn hind' a a'
          (by obtain ⟨-, J, hJ, hJa, -⟩ := ha; exact ⟨J, hJ, hJa⟩)
          (by obtain ⟨-, J, hJ, hJa, -⟩ := ha'; exact ⟨J, hJ, hJa⟩))
      (fun a A hA A' hA' ha ha' =>
        hlink G hnab hp2 hq K z hz hBelow hconn hind' a A hA A' hA' ha ha')
    obtain ⟨hex, hP1⟩ := exactMembers_and_localOddCentral_of_balancedFamily hnab hp2 hq h9 hΩ
      (CoreAssembly.exists_single_class K) hIH
      (fun A' hA' => hlay G hnab hp2 hq K z hz hBelow hconn A' hA')
      (fun A hA => hbal G hnab hp2 hq K z hz hBelow hconn hind' A hA) hmap hcon hK' hcomm rfl hel
      hcard hA
    exact ⟨hex, hP1 K (CoreAssembly.mem_conjClass_self K) z hz⟩

theorem bootTriple_of_fuzzyConjFrames (hlay : TriangleLayers p f)
    (hin : FuzzyModelInputs p f conjMembers) (hedge : FuzzyEdgeInFrame p f conjMembers commuteAdj)
    (hlink : FuzzyLinkConn p f conjMembers) (hcov9 : p ^ f = 9 → ConnectedFramesExist p f)
    (hexotic : ExoticLeviBlock p f) : CoreAssembly.BootTriple p f :=
  bootTriple_of_fuzzyFrames conjMembers hlay (fun _ _ _ K => conjInvariant_conjMembers K)
    (fuzzyFrameBalance_of_modelInputs hin) fuzzyAxisExact_conjMembers
    (fuzzyVertexConn_of_adj fuzzyMemberConn_conjMembers hedge) hlink hcov9 hexotic

end BootTriple

end CFSG.ClassicalInvolution.Balance.Theorem5
