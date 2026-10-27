module

public import CFSG.Fischer.NoF25.Strong
public import CFSG.Fischer.NoF25.Count
public import CFSG.Fischer.NoF25.StarRigid

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer

variable {X Y : Type} [Group X] [Group Y] {E : Set X} {F : Set Y}

section Blocks

variable (hE : Pair X E) (hF : Pair Y F)
  (hrig : ∀ σ : tauGroup hF, σ ∈ (innerTau hF).range)
  {B : Set X} (hBE : B ⊆ E) (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
  {b : X} (hb : b ∈ B) (S : StrongPoints hF E b)

@[expose] def starImg (S : StrongPoints hF E b) (G : Set X) : Set Y :=
  (fun f : LocalClass E b => (S.L.χ f : Y)) '' {f | (f : X) ∈ G}

include hBE hBc hb in
theorem mem_localClass_of_mem {y : X} (hy : y ∈ B) (hyb : y ≠ b) : y ∈ LocalClass E b :=
  ⟨hBE hy, hyb, hBc y hy b hb⟩

include hrig in
theorem exists_model_conj {x : X} (hxb : x * b * x⁻¹ = b) :
    ∃ r : Y, ∀ f : LocalClass E b,
      (S.L.χ (starConjTo hE x hxb f) : Y) = r * S.L.χ f * r⁻¹ := by
  set π : Equiv.Perm F := S.L.χ.symm.trans ((starConjTo hE x hxb).trans S.L.χ) with hπ
  have hmem : π ∈ tauGroup hF := by
    rw [mem_tauGroup]
    intro u v
    set f := S.L.χ.symm u
    set g := S.L.χ.symm v
    have hu : S.L.χ f = u := Equiv.apply_symm_apply _ _
    have hv : S.L.χ g = v := Equiv.apply_symm_apply _ _
    have h1 : tauE hF u v =
        S.L.χ ⟨(f : X) * g * f, LocalPoints.mul_mul_mem_localClass hE f g⟩ := by
      rw [S.L.tau f g, ← hu, ← hv]
      rfl
    have h2 : starConjTo hE x hxb ⟨(f : X) * g * f, LocalPoints.mul_mul_mem_localClass hE f g⟩ =
        ⟨(starConjTo hE x hxb f : X) * starConjTo hE x hxb g * starConjTo hE x hxb f,
          LocalPoints.mul_mul_mem_localClass hE _ _⟩ := by
      apply Subtype.ext
      show x * ((f : X) * g * f) * x⁻¹ = (x * f * x⁻¹) * (x * g * x⁻¹) * (x * f * x⁻¹)
      group
    have h5 : π (S.L.χ ⟨(f : X) * g * f, LocalPoints.mul_mul_mem_localClass hE f g⟩) =
        S.L.χ (starConjTo hE x hxb
          ⟨(f : X) * g * f, LocalPoints.mul_mul_mem_localClass hE f g⟩) := by
      show S.L.χ (starConjTo hE x hxb (S.L.χ.symm (S.L.χ _))) = _
      rw [Equiv.symm_apply_apply]
    have h3 : π u = S.L.χ (starConjTo hE x hxb f) := rfl
    have h4 : π v = S.L.χ (starConjTo hE x hxb g) := rfl
    rw [h1, h3, h4, h5, h2, S.L.tau]
    rfl
  obtain ⟨r, hr⟩ := hrig ⟨π, hmem⟩
  refine ⟨r, fun f => ?_⟩
  have h6 : π (S.L.χ f) = S.L.χ (starConjTo hE x hxb f) := by
    show S.L.χ (starConjTo hE x hxb (S.L.χ.symm (S.L.χ f))) = _
    rw [Equiv.symm_apply_apply]
  rw [← h6, ← innerTau_apply hF r, hr]

include hBE hBc hb in
theorem ncard_eq_starImg_add_one (hBf : B.Finite) {G : Set X} (hGB : G ⊆ B) (hbG : b ∈ G) :
    G.ncard = (starImg hF S G).ncard + 1 := by
  have hinj : Function.Injective fun f : LocalClass E b => (S.L.χ f : Y) :=
    fun f g h => S.L.χ.injective (Subtype.ext h)
  have h1 : (starImg hF S G).ncard = (G \ {b}).ncard := by
    rw [starImg, Set.ncard_image_of_injective _ hinj,
      ← Set.ncard_image_of_injective _ Subtype.val_injective]
    congr 1
    ext y
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact ⟨hf, f.2.2.1⟩
    · rintro ⟨hy, hyb⟩
      exact ⟨⟨y, mem_localClass_of_mem hBE hBc hb (hGB hy) hyb⟩, hy, rfl⟩
  rw [h1, Set.ncard_sdiff_singleton_add_one hbG ((hBf.subset hGB))]

theorem starImg_fix {x : X} (hxb : x * b * x⁻¹ = b) {r : Y}
    (hr : ∀ f : LocalClass E b, (S.L.χ (starConjTo hE x hxb f) : Y) = r * S.L.χ f * r⁻¹) :
    starImg hF S {y | y ∈ B ∧ x * y * x⁻¹ = y} =
      {c | c ∈ starImg hF S B ∧ r * c * r⁻¹ = c} := by
  ext c
  constructor
  · rintro ⟨f, ⟨hfB, hfx⟩, rfl⟩
    refine ⟨⟨f, hfB, rfl⟩, ?_⟩
    rw [← hr f]
    congr 2
    exact Subtype.ext hfx
  · rintro ⟨⟨f, hfB, rfl⟩, hc⟩
    refine ⟨f, ⟨hfB, ?_⟩, rfl⟩
    rw [← hr f] at hc
    have := congrArg Subtype.val (S.L.χ.injective (Subtype.ext hc))
    exact this

include hE hrig hBE hBc hb in
theorem ncard_blocks_through (hBf : B.Finite) :
    {G | G ∈ Oset B 9 ∧ b ∈ G}.ncard = (Oset (starImg hF S B) 8).ncard := by
  classical
  have hinj : Function.Injective fun f : LocalClass E b => (S.L.χ f : Y) :=
    fun f g h => S.L.χ.injective (Subtype.ext h)
  have hsub : ∀ {x : X}, {y | y ∈ B ∧ x * y * x⁻¹ = y} ⊆ B := fun h => h.1
  have hinto : ∀ G, G ∈ Oset B 9 ∧ b ∈ G → starImg hF S G ∈ Oset (starImg hF S B) 8 := by
    rintro G ⟨⟨x, hn, hi, rfl, hk⟩, hbG⟩
    have hxb : x * b * x⁻¹ = b := hbG.2
    obtain ⟨r, hr⟩ := exists_model_conj hE hF hrig S hxb
    have hσσ : ∀ f : LocalClass E b, (f : X) ∈ B →
        starConjTo hE x hxb (starConjTo hE x hxb f) = f := fun f hf =>
      Subtype.ext (hi f hf)
    refine ⟨r, ?_, ?_, starImg_fix hE hF S hxb hr, ?_⟩
    · rintro _ ⟨f, hf, rfl⟩
      exact ⟨starConjTo hE x hxb f, hn _ hf, hr f⟩
    · rintro _ ⟨f, hf, rfl⟩
      rw [← hr f, ← hr (starConjTo hE x hxb f), hσσ f hf]
    · have := ncard_eq_starImg_add_one hF hBE hBc hb S hBf hsub hbG
      omega
  have hinjOn : Set.InjOn (starImg hF S) {G | G ∈ Oset B 9 ∧ b ∈ G} := by
    rintro G₁ ⟨⟨x₁, -, -, rfl, -⟩, hb₁⟩ G₂ ⟨⟨x₂, -, -, rfl, -⟩, hb₂⟩ h
    ext y
    by_cases hyb : y = b
    · subst hyb
      exact ⟨fun _ => hb₂, fun _ => hb₁⟩
    constructor
    · intro hy
      have hf := mem_localClass_of_mem hBE hBc hb hy.1 hyb
      have hm : (S.L.χ ⟨y, hf⟩ : Y) ∈ starImg hF S {y | y ∈ B ∧ x₂ * y * x₂⁻¹ = y} :=
        h ▸ ⟨⟨y, hf⟩, hy, rfl⟩
      obtain ⟨f', hf', he⟩ := hm
      rw [hinj he] at hf'
      exact hf'
    · intro hy
      have hf := mem_localClass_of_mem hBE hBc hb hy.1 hyb
      have hm : (S.L.χ ⟨y, hf⟩ : Y) ∈ starImg hF S {y | y ∈ B ∧ x₁ * y * x₁⁻¹ = y} :=
        h ▸ ⟨⟨y, hf⟩, hy, rfl⟩
      obtain ⟨f', hf', he⟩ := hm
      rw [hinj he] at hf'
      exact hf'
  have honto : starImg hF S '' {G | G ∈ Oset B 9 ∧ b ∈ G} = Oset (starImg hF S B) 8 := by
    apply Set.Subset.antisymm
    · rintro _ ⟨G, hG, rfl⟩
      exact hinto G hG
    · rintro H ⟨r, hn', hi', rfl, hk⟩
      obtain ⟨x, hxb, hx⟩ := S.lift r
      have hr : ∀ f : LocalClass E b,
          (S.L.χ (starConjTo hE x hxb f) : Y) = r * S.L.χ f * r⁻¹ :=
        fun f => hx f _ rfl
      have hstep : ∀ f : LocalClass E b, (f : X) ∈ B → (x : X) * f * x⁻¹ ∈ B := by
        intro f hf
        obtain ⟨f', hf', he⟩ := hn' _ ⟨f, hf, rfl⟩
        rw [← hr f] at he
        have : f' = starConjTo hE x hxb f := S.L.χ.injective (Subtype.ext he)
        rw [this] at hf'
        exact hf'
      have hn : ∀ y ∈ B, x * y * x⁻¹ ∈ B := by
        intro y hy
        by_cases hyb : y = b
        · rw [hyb, hxb]; exact hb
        · exact hstep ⟨y, mem_localClass_of_mem hBE hBc hb hy hyb⟩ hy
      have hi : ∀ y ∈ B, x * (x * y * x⁻¹) * x⁻¹ = y := by
        intro y hy
        by_cases hyb : y = b
        · rw [hyb, hxb, hxb]
        · set f : LocalClass E b := ⟨y, mem_localClass_of_mem hBE hBc hb hy hyb⟩
          have h1 := hi' _ ⟨f, hy, rfl⟩
          rw [← hr f, ← hr (starConjTo hE x hxb f)] at h1
          exact congrArg Subtype.val (S.L.χ.injective (Subtype.ext h1))
      refine ⟨{y | y ∈ B ∧ x * y * x⁻¹ = y}, ⟨⟨x, hn, hi, rfl, ?_⟩, hb, hxb⟩,
        starImg_fix hE hF S hxb hr⟩
      have hbG : b ∈ {y | y ∈ B ∧ x * y * x⁻¹ = y} := ⟨hb, hxb⟩
      have h1 := ncard_eq_starImg_add_one hF hBE hBc hb S hBf hsub hbG
      rw [starImg_fix hE hF S hxb hr, hk] at h1
      exact h1
  rw [← honto, hinjOn.ncard_image]

end Blocks

end CFSG.Fischer
