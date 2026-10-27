module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignSteiner3
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.MathieuExtPlane

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.MathieuExt

open MulAction CFSG.ComponentClassification.WittDesign
open scoped Pointwise

variable (N : Type*) [Group N] {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [MulAction N Ω]

@[expose] def fixFinset (n : N) : Finset Ω := Finset.univ.filter fun x => n • x = x

@[expose] def IsHughesInvolution (x y z : Ω) (n : N) : Prop :=
  n • x = x ∧ n • y = y ∧ n • z = z ∧ n * n = 1 ∧ (fixFinset N n : Finset Ω).card = 6

open scoped Classical in
@[expose] def hughesBlock (x y z : Ω) : Finset Ω :=
  Finset.univ.filter fun w => ∀ n : N, IsHughesInvolution N x y z n → n • w = w

@[expose] def distinctTriples : Finset (Ω × Ω × Ω) :=
  Finset.univ.filter fun t => t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2

@[expose] def hughesBlocks : Finset (Finset Ω) :=
  (distinctTriples (Ω := Ω)).image fun t => hughesBlock N t.1 t.2.1 t.2.2

variable {N}

theorem mem_fixFinset {n : N} {x : Ω} : x ∈ (fixFinset N n : Finset Ω) ↔ n • x = x := by
  simp [fixFinset]

theorem mem_hughesBlock {x y z w : Ω} :
    w ∈ hughesBlock N x y z ↔ ∀ n : N, IsHughesInvolution N x y z n → n • w = w := by
  simp [hughesBlock]

theorem mem_distinctTriples {t : Ω × Ω × Ω} :
    t ∈ distinctTriples ↔ t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 := by
  simp [distinctTriples]

theorem self_mem_hughesBlock (x y z : Ω) :
    x ∈ hughesBlock N x y z ∧ y ∈ hughesBlock N x y z ∧ z ∈ hughesBlock N x y z :=
  ⟨mem_hughesBlock.2 fun _ hn => hn.1, mem_hughesBlock.2 fun _ hn => hn.2.1,
    mem_hughesBlock.2 fun _ hn => hn.2.2.1⟩

theorem fixFinset_conj (g n : N) : (fixFinset N (g * n * g⁻¹) : Finset Ω) =
    (fixFinset N n : Finset Ω).map (MulAction.toPerm g).toEmbedding := by
  ext x
  rw [Finset.mem_map_equiv, mem_fixFinset, mem_fixFinset]
  change (g * n * g⁻¹) • x = x ↔ n • (g⁻¹ • x) = g⁻¹ • x
  rw [mul_smul, mul_smul, ← eq_inv_smul_iff]

theorem card_fixFinset_conj (g n : N) :
    (fixFinset N (g * n * g⁻¹) : Finset Ω).card = (fixFinset N n : Finset Ω).card := by
  rw [fixFinset_conj, Finset.card_map]

theorem isHughesInvolution_conj (g n : N) {x y z : Ω} :
    IsHughesInvolution N (g • x) (g • y) (g • z) (g * n * g⁻¹) ↔ IsHughesInvolution N x y z n := by
  have hfix : ∀ w : Ω, (g * n * g⁻¹) • (g • w) = g • w ↔ n • w = w := fun w => by
    rw [mul_smul, mul_smul, inv_smul_smul, smul_left_cancel_iff]
  have hsq : g * n * g⁻¹ * (g * n * g⁻¹) = 1 ↔ n * n = 1 := by
    rw [show g * n * g⁻¹ * (g * n * g⁻¹) = g * (n * n) * g⁻¹ by group]
    constructor
    · intro h
      have := congrArg (fun m => g⁻¹ * m * g) h
      simpa [mul_assoc] using this
    · intro h
      rw [h, mul_one, mul_inv_cancel]
  simp only [IsHughesInvolution, hfix, hsq, card_fixFinset_conj]

theorem hughesBlock_smul (g : N) (x y z : Ω) :
    hughesBlock N (g • x) (g • y) (g • z) = g • hughesBlock N x y z := by
  ext w
  rw [← Finset.inv_smul_mem_iff, mem_hughesBlock, mem_hughesBlock]
  constructor
  · intro h m hm
    have h1 := congrArg (g⁻¹ • ·) (h (g * m * g⁻¹) ((isHughesInvolution_conj g m).2 hm))
    simp only [smul_smul] at h1 ⊢
    rwa [show g⁻¹ * (g * m * g⁻¹) = m * g⁻¹ by group] at h1
  · intro h n hn
    have hm : IsHughesInvolution N x y z (g⁻¹ * n * g) := by
      rw [← isHughesInvolution_conj g, show g * (g⁻¹ * n * g) * g⁻¹ = n by group]
      exact hn
    have h1 := congrArg (g • ·) (h _ hm)
    simp only [smul_smul] at h1
    rwa [show g * (g⁻¹ * n * g * g⁻¹) = n by group, mul_inv_cancel, one_smul] at h1

section Base

variable {P : Type*} [Fintype P] [DecidableEq P] {𝓛 : Finset (Finset P)} {o : Ω} {ι : P → Ω}

omit [DecidableEq P] in
theorem eq_or_exists_of_card (hΩ : Fintype.card Ω = 22) (h𝓛 : IsSteinerPlane 𝓛)
    (hι : Function.Injective ι) (hιo : ∀ p, ι p ≠ o) (x : Ω) : x = o ∨ ∃ p, ι p = x := by
  have hcard : (insert o (Finset.univ.map ⟨ι, hι⟩)).card = Fintype.card Ω := by
    rw [Finset.card_insert_of_notMem, Finset.card_map, Finset.card_univ, h𝓛.card_points, hΩ]
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk, not_exists]
    exact hιo
  have hx := (Finset.eq_univ_of_card _ hcard).symm ▸ Finset.mem_univ x
  simpa [eq_comm] using hx

theorem fixFinset_eq_of_acts (hΩ : Fintype.card Ω = 22) (h𝓛 : IsSteinerPlane 𝓛)
    (hι : Function.Injective ι) (hιo : ∀ p, ι p ≠ o) {n : N} (hno : n • o = o)
    {σ : Equiv.Perm P} (hσ : ∀ p, n • ι p = ι (σ p)) :
    (fixFinset N n : Finset Ω) = insert o ((Finset.univ.filter fun p => σ p = p).map ⟨ι, hι⟩) := by
  ext x
  rw [mem_fixFinset, Finset.mem_insert, Finset.mem_map]
  rcases eq_or_exists_of_card hΩ h𝓛 hι hιo x with rfl | ⟨p, rfl⟩
  · simp [hno]
  · rw [hσ, hι.eq_iff]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
    constructor
    · exact fun h => Or.inr ⟨p, h, rfl⟩
    · rintro (h | ⟨q, hq, e⟩)
      · exact absurd h (hιo p)
      · rw [← hι e]
        exact hq

theorem card_fixFinset_of_acts (hΩ : Fintype.card Ω = 22) (h𝓛 : IsSteinerPlane 𝓛)
    (hι : Function.Injective ι) (hιo : ∀ p, ι p ≠ o) {n : N} (hno : n • o = o)
    {σ : Equiv.Perm P} (hσ : ∀ p, n • ι p = ι (σ p)) :
    (fixFinset N n : Finset Ω).card = (Finset.univ.filter fun p => σ p = p).card + 1 := by
  rw [fixFinset_eq_of_acts hΩ h𝓛 hι hιo hno hσ, Finset.card_insert_of_notMem, Finset.card_map]
  simp only [Finset.mem_map, Function.Embedding.coeFn_mk, not_exists, not_and]
  exact fun p _ => hιo p

theorem hughesBlock_base (hΩ : Fintype.card Ω = 22) (h𝓛 : IsSteinerPlane 𝓛)
    (hι : Function.Injective ι) (hιo : ∀ p, ι p ≠ o)
    (hA : ∀ n : N, n • o = o → ∃ σ ∈ blockAut 𝓛, ∀ p, n • ι p = ι (σ p))
    (hB : ∀ L ∈ 𝓛, ∃ n : N, n • o = o ∧ n * n = 1 ∧ ∀ p, n • ι p = ι p ↔ p ∈ L)
    {L : Finset P} (hL : L ∈ 𝓛) {α β : P} (hαβ : α ≠ β) (hα : α ∈ L) (hβ : β ∈ L) :
    hughesBlock N o (ι α) (ι β) = insert o (L.map ⟨ι, hι⟩) := by
  ext w
  constructor
  · intro hw
    obtain ⟨n₀, hn₀o, hn₀2, hn₀L⟩ := hB L hL
    have hfix : (fixFinset N n₀ : Finset Ω) = insert o (L.map ⟨ι, hι⟩) := by
      ext x
      rw [mem_fixFinset, Finset.mem_insert, Finset.mem_map]
      rcases eq_or_exists_of_card hΩ h𝓛 hι hιo x with rfl | ⟨p, rfl⟩
      · simp [hn₀o]
      · rw [hn₀L]
        simp only [Function.Embedding.coeFn_mk]
        constructor
        · exact fun h => Or.inr ⟨p, h, rfl⟩
        · rintro (h | ⟨q, hq, e⟩)
          · exact absurd h (hιo p)
          · rwa [← hι e]
    have hn₀ : IsHughesInvolution N o (ι α) (ι β) n₀ := by
      refine ⟨hn₀o, (hn₀L α).2 hα, (hn₀L β).2 hβ, hn₀2, ?_⟩
      rw [hfix, Finset.card_insert_of_notMem, Finset.card_map, h𝓛.card_line hL]
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk, not_exists, not_and]
      exact fun p _ => hιo p
    rw [← hfix, mem_fixFinset]
    exact (mem_hughesBlock.1 hw) n₀ hn₀
  · intro hw
    rw [mem_hughesBlock]
    rintro n ⟨hno, hnα, hnβ, hn2, hn6⟩
    obtain ⟨σ, hσ, hnσ⟩ := hA n hno
    have hσα : σ α = α := hι (by rw [← hnσ, hnα])
    have hσβ : σ β = β := hι (by rw [← hnσ, hnβ])
    have hσ2 : σ * σ = 1 := by
      ext p
      have : ι (σ (σ p)) = ι p := by
        rw [← hnσ, ← hnσ, ← mul_smul, hn2, one_smul]
      rw [Equiv.Perm.mul_apply, hι this, Equiv.Perm.one_apply]
    have h5 : (Finset.univ.filter fun p => σ p = p).card = 5 := by
      have := card_fixFinset_of_acts hΩ h𝓛 hι hιo hno hnσ
      omega
    have hfixL := fixes_line_of_involution h𝓛 hσ hσ2 h5 hL hαβ hα hβ hσα hσβ
    rcases Finset.mem_insert.1 hw with rfl | hw
    · exact hno
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_map.1 hw
      change n • ι p = ι p
      rw [hnσ, hfixL p hp]

variable [IsPretransitive N Ω]

theorem card_hughesBlock (hΩ : Fintype.card Ω = 22) (h𝓛 : IsSteinerPlane 𝓛)
    (hι : Function.Injective ι) (hιo : ∀ p, ι p ≠ o)
    (hA : ∀ n : N, n • o = o → ∃ σ ∈ blockAut 𝓛, ∀ p, n • ι p = ι (σ p))
    (hB : ∀ L ∈ 𝓛, ∃ n : N, n • o = o ∧ n * n = 1 ∧ ∀ p, n • ι p = ι p ↔ p ∈ L)
    {x y z : Ω} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : (hughesBlock N x y z).card = 6 := by
  obtain ⟨g, hg⟩ := exists_smul_eq N x o
  have hgy : g • y ≠ o := fun e => hxy (smul_left_cancel g (hg.trans e.symm))
  have hgz : g • z ≠ o := fun e => hxz (smul_left_cancel g (hg.trans e.symm))
  obtain ⟨α, hα⟩ := (eq_or_exists_of_card hΩ h𝓛 hι hιo (g • y)).resolve_left hgy
  obtain ⟨β, hβ⟩ := (eq_or_exists_of_card hΩ h𝓛 hι hιo (g • z)).resolve_left hgz
  have hαβ : α ≠ β := fun e => hyz (smul_left_cancel g (hα.symm.trans (e ▸ hβ)))
  obtain ⟨L, ⟨hL, hαL, hβL⟩, -⟩ := h𝓛.existsUnique_line hαβ
  have e := hughesBlock_smul (N := N) g x y z
  rw [hg, ← hα, ← hβ, hughesBlock_base hΩ h𝓛 hι hιo hA hB hL hαβ hαL hβL] at e
  rw [← Finset.card_smul_finset g, ← e, Finset.card_insert_of_notMem, Finset.card_map,
    h𝓛.card_line hL]
  simp only [Finset.mem_map, Function.Embedding.coeFn_mk, not_exists, not_and]
  exact fun p _ => hιo p

theorem hughesBlock_eq_of_mem (hΩ : Fintype.card Ω = 22) (h𝓛 : IsSteinerPlane 𝓛)
    (hι : Function.Injective ι) (hιo : ∀ p, ι p ≠ o)
    (hA : ∀ n : N, n • o = o → ∃ σ ∈ blockAut 𝓛, ∀ p, n • ι p = ι (σ p))
    (hB : ∀ L ∈ 𝓛, ∃ n : N, n • o = o ∧ n * n = 1 ∧ ∀ p, n • ι p = ι p ↔ p ∈ L)
    {x y z x' y' z' : Ω} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hxy' : x' ≠ y')
    (hxz' : x' ≠ z') (hyz' : y' ≠ z') (hx' : x' ∈ hughesBlock N x y z)
    (hy' : y' ∈ hughesBlock N x y z) (hz' : z' ∈ hughesBlock N x y z) :
    hughesBlock N x' y' z' = hughesBlock N x y z := by
  refine Finset.eq_of_subset_of_card_le (fun w hw => ?_) ?_
  · rw [mem_hughesBlock] at hw ⊢
    intro n hn
    refine hw n ⟨mem_hughesBlock.1 hx' n hn, mem_hughesBlock.1 hy' n hn,
      mem_hughesBlock.1 hz' n hn, hn.2.2.2⟩
  · rw [card_hughesBlock hΩ h𝓛 hι hιo hA hB hxy hxz hyz,
      card_hughesBlock hΩ h𝓛 hι hιo hA hB hxy' hxz' hyz']

theorem isSteinerTriple_hughesBlocks (hΩ : Fintype.card Ω = 22) (h𝓛 : IsSteinerPlane 𝓛)
    (hι : Function.Injective ι) (hιo : ∀ p, ι p ≠ o)
    (hA : ∀ n : N, n • o = o → ∃ σ ∈ blockAut 𝓛, ∀ p, n • ι p = ι (σ p))
    (hB : ∀ L ∈ 𝓛, ∃ n : N, n • o = o ∧ n * n = 1 ∧ ∀ p, n • ι p = ι p ↔ p ∈ L) :
    IsSteinerTriple (hughesBlocks N (Ω := Ω)) := by
  refine ⟨hΩ, fun B hB' => ?_, fun T hT => ?_⟩
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hB'
    obtain ⟨h1, h2, h3⟩ := mem_distinctTriples.1 ht
    exact card_hughesBlock hΩ h𝓛 hι hιo hA hB h1 h2 h3
  · obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.1 hT
    obtain ⟨hx, hy, hz⟩ := self_mem_hughesBlock (N := N) x y z
    have hsub : ({x, y, z} : Finset Ω) ⊆ hughesBlock N x y z := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl <;> assumption
    refine ⟨hughesBlock N x y z, ⟨Finset.mem_image.2 ⟨(x, y, z),
      mem_distinctTriples.2 ⟨hxy, hxz, hyz⟩, rfl⟩, hsub⟩, ?_⟩
    rintro C ⟨hC, hTC⟩
    obtain ⟨⟨x', y', z'⟩, ht, rfl⟩ := Finset.mem_image.1 hC
    obtain ⟨h1, h2, h3⟩ := mem_distinctTriples.1 ht
    have hmem : ∀ w ∈ ({x, y, z} : Finset Ω), w ∈ hughesBlock N x' y' z' := fun w hw => hTC hw
    exact (hughesBlock_eq_of_mem hΩ h𝓛 hι hιo hA hB h1 h2 h3 hxy hxz hyz (hmem x (by simp))
      (hmem y (by simp)) (hmem z (by simp))).symm

omit [IsPretransitive N Ω] in
theorem smul_mem_hughesBlocks (n : N) {B : Finset Ω} (hB : B ∈ hughesBlocks N (Ω := Ω)) :
    n • B ∈ hughesBlocks N (Ω := Ω) := by
  obtain ⟨⟨x, y, z⟩, ht, rfl⟩ := Finset.mem_image.1 hB
  obtain ⟨h1, h2, h3⟩ := mem_distinctTriples.1 ht
  refine Finset.mem_image.2 ⟨(n • x, n • y, n • z), mem_distinctTriples.2 ⟨?_, ?_, ?_⟩,
    hughesBlock_smul n x y z⟩
  · exact fun e => h1 (smul_left_cancel n e)
  · exact fun e => h2 (smul_left_cancel n e)
  · exact fun e => h3 (smul_left_cancel n e)

theorem exists_steinerTriple (hΩ : Fintype.card Ω = 22) (h𝓛 : IsSteinerPlane 𝓛)
    (hι : Function.Injective ι) (hιo : ∀ p, ι p ≠ o)
    (hA : ∀ n : N, n • o = o → ∃ σ ∈ blockAut 𝓛, ∀ p, n • ι p = ι (σ p))
    (hB : ∀ L ∈ 𝓛, ∃ n : N, n • o = o ∧ n * n = 1 ∧ ∀ p, n • ι p = ι p ↔ p ∈ L) :
    ∃ 𝓑 : Finset (Finset Ω), IsSteinerTriple 𝓑 ∧ (∀ n : N, ∀ B ∈ 𝓑, n • B ∈ 𝓑) ∧
      ∀ L ∈ 𝓛, insert o (L.map ⟨ι, hι⟩) ∈ 𝓑 := by
  refine ⟨hughesBlocks N, isSteinerTriple_hughesBlocks hΩ h𝓛 hι hιo hA hB,
    fun n B hB' => smul_mem_hughesBlocks n hB', fun L hL => ?_⟩
  obtain ⟨α, hα, β, hβ, hαβ⟩ := Finset.one_lt_card.1 (by rw [h𝓛.card_line hL]; norm_num)
  rw [← hughesBlock_base hΩ h𝓛 hι hιo hA hB hL hαβ hα hβ]
  exact Finset.mem_image.2 ⟨(o, ι α, ι β), mem_distinctTriples.2 ⟨Ne.symm (hιo α),
    Ne.symm (hιo β), hι.ne hαβ⟩, rfl⟩

end Base

end CFSG.EvenSmallLie.UnitarySix.MathieuExt
