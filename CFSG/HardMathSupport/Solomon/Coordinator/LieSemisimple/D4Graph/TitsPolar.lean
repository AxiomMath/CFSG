module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnFinal

public section

open scoped Pointwise

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Steinberg Multiplicative
  CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem eq_bot_or_isSolvable_quotient_of_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : ∀ (N : Subgroup A) [N.Normal], N = ⊥ ∨ Group.IsSolvable (A ⧸ N)) :
    ∀ (N : Subgroup B) [N.Normal], N = ⊥ ∨ Group.IsSolvable (B ⧸ N) := by
  intro N hN
  haveI : (N.comap e.toMonoidHom).Normal := hN.comap e.toMonoidHom
  have hmap : (N.comap e.toMonoidHom).map e.toMonoidHom = N :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective N
  rcases h (N.comap e.toMonoidHom) with hb | hs
  · left
    rw [← hmap, hb, Subgroup.map_bot]
  · right
    let q : A ⧸ N.comap e.toMonoidHom ≃* B ⧸ N :=
      QuotientGroup.congr (N.comap e.toMonoidHom) N e hmap
    exact Group.isSolvable_of_surjective (f := q.toMonoidHom) q.surjective

theorem normalCore_eq_bot_of_cells {G : Type*} [Group G] (B U : Subgroup G)
    (hUnorm : ∀ b ∈ B, ∀ u ∈ U, b * u * b⁻¹ ∈ U) (c₀ : G)
    (hmeet : ∀ u ∈ U, c₀ * u * c₀⁻¹ ∈ B → u = 1)
    (hKC : ∀ k ∈ B, (∀ u ∈ U, k * u = u * k) → k ∈ U) : B.normalCore = ⊥ := by
  have hKU : ∀ u ∈ U, u ∈ B.normalCore → u = 1 := fun u hu hK => hmeet u hu (hK c₀)
  refine eq_bot_iff.mpr fun k hk => ?_
  have hkB : k ∈ B := Subgroup.normalCore_le B hk
  have hcomm : ∀ u ∈ U, k * u = u * k := by
    intro u hu
    have h1 : k * u * k⁻¹ * u⁻¹ ∈ B.normalCore := by
      have h2 : u * k⁻¹ * u⁻¹ ∈ B.normalCore :=
        (Subgroup.normalCore_normal B).conj_mem k⁻¹ (B.normalCore.inv_mem hk) u
      simpa [mul_assoc] using B.normalCore.mul_mem hk h2
    have h3 : k * u * k⁻¹ * u⁻¹ ∈ U := U.mul_mem (hUnorm k hkB u hu) (U.inv_mem hu)
    have h4 := hKU _ h3 h1
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h4
    exact h4
  exact Subgroup.mem_bot.mpr (hKU k (hKC k hkB hcomm) hk)

theorem exists_mul_mul_of_two_cells {G : Type*} [Group G] (B U : Subgroup G) (c₀ : G)
    (hcell : ∀ g : G, g ∈ B ∨ ∃ b ∈ B, ∃ u ∈ U, g = b * c₀ * u) {a₁ a₂ : G} (h₁ : a₁ ∉ B)
    (h₂ : a₂ ∉ B) : ∃ b ∈ B, ∃ u ∈ U, a₂ = b * a₁ * u := by
  obtain ⟨b₁, hb₁, u₁, hu₁, rfl⟩ := (hcell a₁).resolve_left h₁
  obtain ⟨b₂, hb₂, u₂, hu₂, rfl⟩ := (hcell a₂).resolve_left h₂
  refine ⟨b₂ * b₁⁻¹, B.mul_mem hb₂ (B.inv_mem hb₁), u₁⁻¹ * u₂,
    U.mul_mem (U.inv_mem hu₁) hu₂, ?_⟩
  simp [mul_assoc]

theorem exists_mul_eq_of_two_cells {G : Type*} [Group G] (B U : Subgroup G) (hUB : U ≤ B)
    (c₀ : G) (hcell : ∀ g : G, g ∈ B ∨ ∃ b ∈ B, ∃ u ∈ U, g = b * c₀ * u) (A : Subgroup G)
    [A.Normal] {a : G} (haA : a ∈ A) (haB : a ∉ B) (g : G) : ∃ x ∈ A, ∃ y ∈ B, g = x * y := by
  by_cases hg : g ∈ B
  · exact ⟨1, A.one_mem, g, hg, (one_mul g).symm⟩
  · obtain ⟨b, hb, u, hu, hbu⟩ := exists_mul_mul_of_two_cells B U c₀ hcell haB hg
    refine ⟨b * a * b⁻¹, ‹A.Normal›.conj_mem a haA b, b * u, B.mul_mem hb (hUB hu), ?_⟩
    rw [hbu]
    simp [mul_assoc]

theorem eq_bot_or_isSolvable_of_two_cells {G : Type*} [Group G] (B U : Subgroup G) (hUB : U ≤ B)
    (hUnorm : ∀ b ∈ B, ∀ u ∈ U, b * u * b⁻¹ ∈ U) (c₀ : G)
    (hcell : ∀ g : G, g ∈ B ∨ ∃ b ∈ B, ∃ u ∈ U, g = b * c₀ * u)
    (hmeet : ∀ u ∈ U, c₀ * u * c₀⁻¹ ∈ B → u = 1)
    (hKC : ∀ k ∈ B, (∀ u ∈ U, k * u = u * k) → k ∈ U) (hBsolv : Group.IsSolvable ↥B)
    (A : Subgroup G) [A.Normal] : A = ⊥ ∨ Group.IsSolvable (G ⧸ A) := by
  have hK : B.normalCore = ⊥ := normalCore_eq_bot_of_cells B U hUnorm c₀ hmeet hKC
  by_cases hAB : A ≤ B
  · exact Or.inl (le_bot_iff.mp (hK ▸ Subgroup.normal_le_normalCore.mpr hAB))
  · right
    obtain ⟨a, haA, haB⟩ := SetLike.not_le_iff_exists.mp hAB
    have hfac := exists_mul_eq_of_two_cells B U hUB c₀ hcell A haA haB
    have hsurj : Function.Surjective ((QuotientGroup.mk' A).comp B.subtype) := by
      intro q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨x, hx, y, hy, rfl⟩ := hfac g
      refine ⟨⟨y, hy⟩, ?_⟩
      show (QuotientGroup.mk y : G ⧸ A) = QuotientGroup.mk (x * y)
      rw [QuotientGroup.eq]
      have := (inferInstance : A.Normal).conj_mem x hx y⁻¹
      simpa [mul_assoc] using this
    haveI := hBsolv
    exact Group.isSolvable_of_surjective hsurj

theorem eq_bot_or_isSolvable_foldFix_of_polarity {X : Type*} [Group X] [Finite X]
    (D : RankTwoSystem X 3) (hBsolv : Group.IsSolvable ↥D.B)
    {θ : X ≃* X} (hθ : D.IsPolarity θ) {c₀ : X} (hc₀ : c₀ ∈ dc D.B D.N D.w₀)
    (hc₀f : θ c₀ = c₀)
    (hKC : ∀ k ∈ D.B, θ k = k → (∀ u ∈ D.U, θ u = u → k * u = u * k) → k ∈ D.U)
    (A : Subgroup ↥(foldFix θ)) [A.Normal] : A = ⊥ ∨ Group.IsSolvable (↥(foldFix θ) ⧸ A) := by
  have hmemB : ∀ g : ↥(foldFix θ), g ∈ D.B.subgroupOf (foldFix θ) ↔ (g : X) ∈ D.B :=
    fun g => Subgroup.mem_subgroupOf
  have hmemU : ∀ g : ↥(foldFix θ), g ∈ D.U.subgroupOf (foldFix θ) ↔ (g : X) ∈ D.U :=
    fun g => Subgroup.mem_subgroupOf
  let c : ↥(foldFix θ) := ⟨c₀, hc₀f⟩
  have hUB : D.U.subgroupOf (foldFix θ) ≤ D.B.subgroupOf (foldFix θ) := fun g hg =>
    (hmemB g).2 (D.U_le_B ((hmemU g).1 hg))
  have hcell : ∀ g : ↥(foldFix θ), g ∈ D.B.subgroupOf (foldFix θ) ∨
      ∃ b ∈ D.B.subgroupOf (foldFix θ), ∃ u ∈ D.U.subgroupOf (foldFix θ), g = b * c * u := by
    intro g
    rcases hθ.fixed_mem_B_or_top (mem_foldFix.1 g.2) with hg | hg
    · exact Or.inl ((hmemB g).2 hg)
    · obtain ⟨b, hb, hbf, u, hu, huf, hgbu⟩ :=
        hθ.top_decomp hc₀ hg hc₀f (mem_foldFix.1 g.2)
      exact Or.inr ⟨⟨b, hbf⟩, (hmemB _).2 hb, ⟨u, huf⟩, (hmemU _).2 hu, Subtype.ext hgbu⟩
  have hUnorm : ∀ b ∈ D.B.subgroupOf (foldFix θ), ∀ u ∈ D.U.subgroupOf (foldFix θ),
      b * u * b⁻¹ ∈ D.U.subgroupOf (foldFix θ) := fun b hb u hu =>
    (hmemU _).2 (D.conj_mem_U_of_mem_B ((hmemB b).1 hb) ((hmemU u).1 hu))
  have hmeet : ∀ u ∈ D.U.subgroupOf (foldFix θ), c * u * c⁻¹ ∈ D.B.subgroupOf (foldFix θ) →
      u = 1 := fun u hu h =>
    Subtype.ext (RankTwoSystem.U_meet_top hc₀ ((hmemU u).1 hu) ((hmemB _).1 h))
  have hKC' : ∀ k ∈ D.B.subgroupOf (foldFix θ),
      (∀ u ∈ D.U.subgroupOf (foldFix θ), k * u = u * k) → k ∈ D.U.subgroupOf (foldFix θ) := by
    intro k hk hcomm
    refine (hmemU k).2 (hKC k ((hmemB k).1 hk) (mem_foldFix.1 k.2) fun u hu huf => ?_)
    exact congrArg Subtype.val (hcomm ⟨u, huf⟩ ((hmemU _).2 hu))
  have hBsolv' : Group.IsSolvable ↥(D.B.subgroupOf (foldFix θ)) := by
    haveI := hBsolv
    let f : ↥(D.B.subgroupOf (foldFix θ)) →* ↥D.B :=
      ((foldFix θ).subtype.comp (D.B.subgroupOf (foldFix θ)).subtype).codRestrict D.B
        fun g => (hmemB g.1).1 g.2
    exact solvable_of_solvable_injective (f := f) fun a b hab =>
      Subtype.ext (Subtype.ext (congrArg (fun z : ↥D.B => (z : X)) hab))
  exact eq_bot_or_isSolvable_of_two_cells (D.B.subgroupOf (foldFix θ))
    (D.U.subgroupOf (foldFix θ)) hUB hUnorm c hcell hmeet hKC' hBsolv' A

theorem un_final_T {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 0 < f)
    {X : Type*} [Group X] [Finite X] (D : RankTwoSystem X 3) (hBsolv : Group.IsSolvable ↥D.B)
    (τ e : X ≃* X) (hτ : D.IsOpposition τ) (hτe : ∀ y, τ (τ y) = e y)
    (he : ∀ b ∈ D.B, e b ∈ D.B) (hτ4 : ∀ y, τ (τ (τ (τ y))) = y)
    {k : Type} [Field k] [Finite k] [CharP k p] (hk : Nat.card k = (p ^ f) ^ 4)
    (ε : k ≃+* k) (hε : ∀ a, ε a = a ^ (p ^ f))
    (ρ : Matrix.SpecialLinearGroup (Fin 2) k →* X) (hρinj : Function.Injective ρ) (κ : kˣ)
    (hu : ∀ a, τ (ρ (sl2Upper a)) = ρ (sl2Lower ((κ : k) * ε a)))
    (hl : ∀ a, τ (ρ (sl2Lower a)) = ρ (sl2Upper (((κ⁻¹ : kˣ) : k) * ε a)))
    (hρ2 : ∀ a, ρ (sl2Upper a) ∈ D.root 2) (hρ2' : ∀ y ∈ D.root 2, ∃ a, y = ρ (sl2Upper a))
    (hρm2 : ∀ a, ρ (sl2Lower a) ∈ D.root (-2))
    (hρN : ∃ m₀ : D.N, (m₀ : X) = ρ unSL2W ∧ (m₀ : D.Weyl) = D.w₀)
    (hρH : ∀ u : kˣ, ρ (unSL2Diag u) ∈ D.B ⊓ D.N)
    (x₁ : Multiplicative k →* X) (hx₁inj : Function.Injective x₁)
    (hx₁ : ∀ a, x₁ a ∈ D.root 1) (hx₁s : ∀ y ∈ D.root 1, ∃ a, y = x₁ a)
    (hx₁torus : ∀ h ∈ D.B ⊓ D.N, ∃ χ : kˣ,
      ∀ a : k, h * x₁ (ofAdd a) * h⁻¹ = x₁ (ofAdd ((χ : k) * a)))
    (hx₁e : ∀ a : k, e (x₁ (ofAdd a)) = x₁ (ofAdd (ε (ε a))))
    (hab₁ : ∀ a ∈ D.root 1, ∀ b ∈ D.root 1, a * b = b * a)
    (hab₃ : ∀ a ∈ D.root 3, ∀ b ∈ D.root 3, a * b = b * a)
    (hTor : ∀ h ∈ D.B ⊓ D.N, ∀ y ∈ D.root 1, y ≠ 1 → ∀ z ∈ D.root 3, z ≠ 1 →
      h * y = y * h → h * z = z * h → h = 1)
    (hĉ : ∃ c ∈ D.B ⊓ D.N, τ c = c ∧ c * c = 1 ∧ ∀ y ∈ D.root (-2), c * y * c⁻¹ = y⁻¹) :
    ∀ (A : Subgroup ↥(foldFix τ)) [A.Normal], A = ⊥ ∨ Group.IsSolvable (↥(foldFix τ) ⧸ A) := by
  obtain ⟨t, ht⟩ := un_norm_solution hf hk ε hε κ (un_norm_eq ρ hρinj τ hτ4 ε κ hu hl)
  have hg : (ρ (sl2Lower (t : k)))⁻¹ * τ (ρ (sl2Lower (t : k))) *
      ((D.lift D.w₀ : D.N) : X) ∈ D.B := un_adapted_mem_B D ρ τ ε κ hl hρ2 hρN hρH t ht
  have hθpol := hτ.isPolarity hg
  have hθapp := un_theta_apply τ (ρ (sl2Lower (t : k)))
  have hθ4 := un_theta_four τ hτ4 (ρ (sl2Lower (t : k)))
  obtain ⟨l₂, hθ₂⟩ := un_theta_x2 ρ τ ε κ hu hl t ht
  obtain ⟨ν, hθ₁₁⟩ := un_theta_sq_x1 D τ e hτ hτe he ε x₁ hx₁ hx₁torus hx₁e hab₁ hab₃ hg
  have hθ₁ := fun y (hy : y ∈ D.root 1) => hτ.theta_root₁ hg hy
  have hθ₃ := fun z (hz : z ∈ D.root 3) => hτ.theta_root₃ hg hz
  have hU1 : D.root 1 ≤ D.U := D.root_le_U (by norm_num) (by norm_num)
  have hU2 : D.root 2 ≤ D.U := D.root_le_U (by norm_num) (by norm_num)
  have hU3 : D.root 3 ≤ D.U := D.root_le_U (by norm_num) (by norm_num)
  set x : X := ρ (sl2Lower (t : k))
  set θ : X ≃* X := τ.trans (MulAut.conj (x⁻¹ * τ x))
  have hx₂inj : Function.Injective (ρ.comp (unSL2UpperHom k)) := fun a b h =>
    Multiplicative.toAdd.injective
      (@un_sl2Upper_injective k _ (toAdd a) (toAdd b) (hρinj h))
  obtain ⟨hcard, hfix⟩ := un_heis_fixed D hp2 hf hk ε hε x₁ (ρ.comp (unSL2UpperHom k)) hx₁inj
    hx₂inj hx₁ (fun a => hρ2 _) hx₁s
    (fun y hy => by
      obtain ⟨a, ha⟩ := hρ2' y hy
      exact ⟨ofAdd a, ha⟩) hab₁ hab₃ θ hθpol.mem_U hθ4 l₂ ν hθ₂ hθ₁ hθ₃ hθ₁₁
  have hKC := un_hKC D hab₁ hab₃ hTor θ hfix
  have hnt : ∃ u ∈ D.U, u ≠ 1 ∧ θ u = u := by
    obtain ⟨y, hy, hy1, b, hb, z, hz, hz1, hfx⟩ := hfix
    refine ⟨y * b * z, D.U.mul_mem (D.U.mul_mem (hU1 hy) (hU2 hb)) (hU3 hz), fun h1 => hy1 ?_,
      hfx⟩
    exact (un_unique D hy (D.root 1).one_mem hb (D.root 2).one_mem hz (D.root 3).one_mem
      (by rw [h1]; simp)).1
  obtain ⟨c, hcH, hcτ, -, hcinv⟩ := hĉ
  have hc₀ := un_c0_mem_dc D ρ hρ2 hρm2 hρN hρH (un_two_ne_zero hp2) hcH hcinv t
  have hc₀f : θ (x⁻¹ * c * x) = x⁻¹ * c * x := by
    rw [hθapp]
    have e : x * (x⁻¹ * c * x) * x⁻¹ = c := by group
    rw [e, hcτ]
  have hNA : ∀ (A : Subgroup ↥(foldFix θ)) [A.Normal],
      A = ⊥ ∨ Group.IsSolvable (↥(foldFix θ) ⧸ A) := fun A _ =>
    eq_bot_or_isSolvable_foldFix_of_polarity D hBsolv hθpol hc₀ hc₀f hKC A
  exact eq_bot_or_isSolvable_quotient_of_equiv (unFixEquiv τ θ x hθapp) hNA

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual
