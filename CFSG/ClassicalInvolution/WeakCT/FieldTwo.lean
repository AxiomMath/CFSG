module

public import CFSG.ClassicalInvolution.WeakCT.FieldTwoAux2

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras CFSG.ClassicalGroups.SpecialLinear
open Matrix
open scoped MatrixGroups commutatorElement

section FieldTwo

variable {K : Type} [Field K] [Finite K] {X : Type} [Group X]

theorem weylTwo_agree (hK : Nat.card K = 2) (s t : Fin 2) {θ₁ θ₂ : SL(3, K) →* X}
    (h₁ : θ₁.ker ≤ Subgroup.center SL(3, K)) (h₂ : θ₂.ker ≤ Subgroup.center SL(3, K))
    (hM : (Bs K s).map θ₁ = (Bs K t).map θ₂)
    (hcomm : ∀ x ∈ (Bs K s.rev).map θ₁, ∀ y ∈ (Bs K t.rev).map θ₂, x * y = y * x) :
    θ₁ (blk K s (weylTwo K)) = θ₂ (blk K t (weylTwo K)) := by
  classical
  have hx_mem : θ₁ (blk K s (weylTwo K)) ∈ (Bs K s).map θ₁ :=
    ⟨blk K s (weylTwo K), blk_mem_Bs s (weylTwo K), rfl⟩
  rw [hM] at hx_mem
  obtain ⟨x, hx, hxθ⟩ := Subgroup.mem_map.mp hx_mem
  rw [show Bs K t = (blk K t).range from rfl] at hx
  obtain ⟨A, rfl⟩ := hx
  have hA : θ₂ (blk K t A) = θ₁ (blk K s (weylTwo K)) := hxθ
  by_cases hAw : A = weylTwo K
  · rw [hAw] at hA
    exact hA.symm
  exfalso
  have hinj : Function.Injective (θ₂.comp (blk K t)) := comp_blk_injective h₂ t
  have hA2 : A * A = 1 := by
    have hAA : (θ₂.comp (blk K t)) (A * A) = 1 := by
      rw [map_mul]
      change θ₂ (blk K t A) * θ₂ (blk K t A) = 1
      rw [hA]
      calc θ₁ (blk K s (weylTwo K)) * θ₁ (blk K s (weylTwo K))
          = θ₁ (blk K s (weylTwo K) * blk K s (weylTwo K)) := (map_mul θ₁ _ _).symm
        _ = θ₁ (blk K s (weylTwo K * weylTwo K)) := by rw [← map_mul (blk K s)]
        _ = 1 := by rw [weylTwo_mul_self hK, map_one (blk K s), map_one θ₁]
    apply hinj
    simpa using hAA
  have hA1 : A ≠ 1 := by
    intro h1
    have hx1 : θ₁ (blk K s (weylTwo K)) = 1 := by
      rw [← hA, h1, map_one, map_one]
    have hinj₁ : Function.Injective (θ₁.comp (blk K s)) := comp_blk_injective h₁ s
    have hw1 : weylTwo K = 1 := by
      apply hinj₁
      simpa using hx1
    exact weylTwo_ne_one hK hw1
  have hAcases : A = tv 0 1 (1 : K) ∨ A = tv 1 0 (1 : K) := by
    rcases eq_one_or_tv_of_mul_self hK hA2 with h | h | h | h
    · exact absurd h hA1
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hAw
  have key : ∀ c : SL(3, K), c ∈ Bs K t.rev → c ≠ 1 →
      c * blk K t A = blk K t A * c → False := by
    intro c hcB hc1 hcA
    have hθ₂c_mem : θ₂ c ∈ (Bs K t.rev).map θ₂ := ⟨c, hcB, rfl⟩
    have hAc : ∀ z ∈ Bs K s, θ₂ c * θ₁ z = θ₁ z * θ₂ c := by
      intro z hz
      have hzH : z ∈ Subgroup.closure ((Bs K s.rev : Set SL(3, K)) ∪
          {blk K s (weylTwo K)}) := Bs_le_closure_rev_weylTwo hK s hz
      have hbase : ∀ y ∈ ((Bs K s.rev : Set SL(3, K)) ∪ {blk K s (weylTwo K)}),
          θ₂ c * θ₁ y = θ₁ y * θ₂ c := by
        intro y hy
        rcases hy with hy | hy
        · exact (hcomm (θ₁ y) ⟨y, hy, rfl⟩ (θ₂ c) hθ₂c_mem).symm
        · rw [Set.mem_singleton_iff] at hy
          subst hy
          have h := congrArg θ₂ hcA
          rw [map_mul, map_mul, hA] at h
          exact h
      have hle : Subgroup.closure ((Bs K s.rev : Set SL(3, K)) ∪
          {blk K s (weylTwo K)}) ≤ (Subgroup.centralizer ({θ₂ c} : Set X)).comap θ₁ := by
        rw [Subgroup.closure_le]
        intro y hy
        change θ₁ y ∈ Subgroup.centralizer ({θ₂ c} : Set X)
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        rw [Set.mem_singleton_iff] at hg
        subst hg
        exact hbase y hy
      have hz' : θ₁ z ∈ Subgroup.centralizer ({θ₂ c} : Set X) := hle hzH
      exact Subgroup.mem_centralizer_iff.mp hz' _ rfl
    have hcommAll : ∀ b ∈ Bs K t, c * b = b * c := by
      intro b hb
      have hb' : θ₂ b ∈ (Bs K s).map θ₁ := by
        rw [hM]
        exact ⟨b, hb, rfl⟩
      obtain ⟨z, hz, hzb⟩ := hb'
      have hθ : θ₂ c * θ₂ b = θ₂ b * θ₂ c := by
        rw [← hzb]
        exact hAc z hz
      have hker : c * b * c⁻¹ * b⁻¹ ∈ θ₂.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hθ]
        group
      have hz1 : c * b * c⁻¹ * b⁻¹ = 1 := by
        have := h₂ hker
        rwa [center_SL_three_eq_bot hK, Subgroup.mem_bot] at this
      have h1 : c * b * c⁻¹ = b := mul_inv_eq_one.mp hz1
      have hcb : c * b = b * c := by
        calc c * b = (c * b * c⁻¹) * c := by group
          _ = b * c := by rw [h1]
      exact hcb
    exact hc1 (eq_one_of_mem_Bs_rev_comm t hcB hcommAll)
  rcases hAcases with hAu | hAv
  · exact key _ (blk_mem_Bs t.rev (tv 1 0 1)) (blk_rev_tv10_ne_one t)
      (by rw [hAu]; exact (blk_tv01_comm_blk_rev_tv10 t).symm)
  · exact key _ (blk_mem_Bs t.rev (tv 0 1 1)) (blk_rev_tv01_ne_one t)
      (by rw [hAv]; exact (blk_tv10_comm_blk_rev_tv01 t).symm)

theorem exists_adjust_side_two (hK : Nat.card K = 2) (s : Fin 2) {θ₀ : SL(3, K) →* X}
    (hθ₀ : θ₀.ker ≤ Subgroup.center SL(3, K)) {ρ : SL(2, K) →* X} (hρ : Function.Injective ρ)
    (hrange : ρ.range = (Bs K s).map θ₀) (hw : ρ (weylTwo K) = θ₀ (blk K s (weylTwo K))) :
    ∃ θ' : SL(3, K) →* X, θ'.ker ≤ Subgroup.center SL(3, K) ∧ θ'.comp (blk K s) = ρ ∧
      (Bs K s.rev).map θ' = (Bs K s.rev).map θ₀ ∧
      θ' (blk K s.rev (weylTwo K)) = θ₀ (blk K s.rev (weylTwo K)) := by
  classical
  have hinj : Function.Injective (θ₀.comp (blk K s)) := comp_blk_injective hθ₀ s
  have hu_mem : ρ (tv 0 1 (1 : K)) ∈ (θ₀.comp (blk K s)).range := by
    rw [← map_Bs θ₀ s, ← hrange]
    exact ⟨_, rfl⟩
  obtain ⟨a, ha⟩ := hu_mem
  have hv_mem : ρ (tv 1 0 (1 : K)) ∈ (θ₀.comp (blk K s)).range := by
    rw [← map_Bs θ₀ s, ← hrange]
    exact ⟨_, rfl⟩
  obtain ⟨b, hb⟩ := hv_mem
  have ha2 : a * a = 1 := by
    have ha' : θ₀ (blk K s a) = ρ (tv 0 1 (1 : K)) := ha
    apply hinj
    change θ₀ (blk K s (a * a)) = θ₀ (blk K s 1)
    rw [map_mul (blk K s) a a, map_mul θ₀, ha', map_one (blk K s), map_one θ₀]
    rw [← map_mul, tv01_mul_self hK, map_one]
  have hb2 : b * b = 1 := by
    have hb' : θ₀ (blk K s b) = ρ (tv 1 0 (1 : K)) := hb
    apply hinj
    change θ₀ (blk K s (b * b)) = θ₀ (blk K s 1)
    rw [map_mul (blk K s) b b, map_mul θ₀, hb', map_one (blk K s), map_one θ₀]
    rw [← map_mul, tv10_mul_self hK, map_one]
  have haw : a ≠ weylTwo K := by
    intro h
    have h1 : ρ (tv 0 1 (1 : K)) = ρ (weylTwo K) := by
      rw [← ha, h]
      simpa using hw.symm
    exact tv01_ne_weylTwo hK (hρ h1)
  have hbw : b ≠ weylTwo K := by
    intro h
    have h1 : ρ (tv 1 0 (1 : K)) = ρ (weylTwo K) := by
      rw [← hb, h]
      simpa using hw.symm
    exact tv10_ne_weylTwo hK (hρ h1)
  have hab : a ≠ b := by
    intro h
    have h1 : ρ (tv 0 1 (1 : K)) = ρ (tv 1 0 (1 : K)) := by rw [← ha, h, hb]
    exact tv01_ne_tv10 (hρ h1)
  have ha_cases : a = tv 0 1 (1 : K) ∨ a = tv 1 0 (1 : K) := by
    rcases eq_one_or_tv_of_mul_self hK ha2 with h | h | h | h
    · exfalso
      have h1 : ρ (tv 0 1 (1 : K)) = 1 := by
        rw [← ha, h]; simp
      exact tv01_ne_one (hρ (by simpa using h1))
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h haw
  have hb_cases : b = tv 0 1 (1 : K) ∨ b = tv 1 0 (1 : K) := by
    rcases eq_one_or_tv_of_mul_self hK hb2 with h | h | h | h
    · exfalso
      have h1 : ρ (tv 1 0 (1 : K)) = 1 := by
        rw [← hb, h]; simp
      exact tv10_ne_one (hρ (by simpa using h1))
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hbw
  have hτB : (Bs K s.rev).map (invTransposeSL 3).toMonoidHom = Bs K s.rev := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨A, rfl⟩ := hy
      show invTransposeSL 3 ((blk K s.rev) A) ∈ Bs K s.rev
      rw [invTransposeSL_blk]
      exact ⟨_, rfl⟩
    · intro hx
      obtain ⟨A, rfl⟩ := hx
      refine ⟨blk K s.rev ((invTransposeSL 2).symm A), ⟨_, rfl⟩, ?_⟩
      show invTransposeSL 3 ((blk K s.rev) ((invTransposeSL 2).symm A)) = (blk K s.rev) A
      rw [invTransposeSL_blk, MulEquiv.apply_symm_apply]
  rcases ha_cases with hau | hav <;> rcases hb_cases with hbu | hbv
  · exact absurd (hau.trans hbu.symm) hab
  · refine ⟨θ₀, hθ₀, ?_, rfl, rfl⟩
    apply hom_ext_sl2_two hK
    · change θ₀ (blk K s (tv 0 1 (1 : K))) = ρ (tv 0 1 (1 : K))
      conv_lhs => rw [← hau]
      exact ha
    · change θ₀ (blk K s (tv 1 0 (1 : K))) = ρ (tv 1 0 (1 : K))
      conv_lhs => rw [← hbv]
      exact hb
  · refine ⟨θ₀.comp (invTransposeSL 3).toMonoidHom,
      ker_comp_mulEquiv_le_center hθ₀ (invTransposeSL 3), ?_, ?_, ?_⟩
    · apply hom_ext_sl2_two hK
      · change θ₀ (invTransposeSL 3 (blk K s (tv 0 1 (1 : K)))) =
          ρ (tv 0 1 (1 : K))
        rw [invTransposeSL_blk, invTransposeSL_tv01_one hK]
        conv_lhs => rw [← hav]
        exact ha
      · change θ₀ (invTransposeSL 3 (blk K s (tv 1 0 (1 : K)))) =
          ρ (tv 1 0 (1 : K))
        rw [invTransposeSL_blk, invTransposeSL_tv10_one hK]
        conv_lhs => rw [← hbu]
        exact hb
    · rw [map_comp_mulEquiv, hτB]
    · change θ₀ (invTransposeSL 3 (blk K s.rev (weylTwo K))) = θ₀ (blk K s.rev (weylTwo K))
      rw [invTransposeSL_blk, invTransposeSL_weylTwo hK]
  · exact absurd (hav.trans hbv.symm) hab

variable {r : ℕ} {adj : Fin r → Fin r → Prop} {par : Fin r → Fin r} {dep : Fin r → ℕ}
  {k₀ : Fin r}

theorem exists_frame_of_tree_two (hK : Nat.card K = 2) (hT : RootedTree adj par dep k₀)
    (hroot : ∃ c, adj k₀ c ∨ adj c k₀) {U : Fin r → Subgroup X}
    (hcomm : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x)
    (hpair : ∀ i j, adj i j → ∃ W, LinearBlockStandardPair K W (U i) (U j)) :
    ∃ ρ : Fin r → SL(2, K) →* X, (∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k) ∧
      ∀ i j, adj i j → ∃ ψ : SL(3, K) →* X, ψ.comp (blk K 0) = ρ i ∧ ψ.comp (blk K 1) = ρ j := by
  classical
  have hnorm : ∀ i j, adj i j → ∃ θ : SL(3, K) →* X, θ.ker ≤ Subgroup.center SL(3, K) ∧
      (Bs K 0).map θ = U i ∧ (Bs K 1).map θ = U j := by
    intro i j h
    obtain ⟨W, hW⟩ := hpair i j h
    obtain ⟨θ, -, hker, h0, h1⟩ := pair_normalize hW
    exact ⟨θ, hker, h0, h1⟩
  choose θ hθk hθ0 hθ1 using hnorm
  have hnb : ∀ k a b, (adj k a ∨ adj a k) → (adj k b ∨ adj b k) → a ≠ b →
      ∀ x ∈ U a, ∀ y ∈ U b, x * y = y * x := by
    intro k a b hka hkb hab x hx y hy
    refine hcomm a b hab (fun h => hT.no_triangle hka hkb (Or.inl h) hab) (fun h =>
      hT.no_triangle hka hkb (Or.inr h) hab) x hx y hy
  have agree : ∀ k, (∀ a b (ha : adj k a) (hb : adj k b),
        (θ k a ha) (blk K 0 (weylTwo K)) = (θ k b hb) (blk K 0 (weylTwo K))) ∧
      (∀ a b (ha : adj k a) (hb : adj b k),
        (θ k a ha) (blk K 0 (weylTwo K)) = (θ b k hb) (blk K 1 (weylTwo K))) ∧
      (∀ a b (ha : adj a k) (hb : adj b k),
        (θ a k ha) (blk K 1 (weylTwo K)) = (θ b k hb) (blk K 1 (weylTwo K))) := by
    intro k
    refine ⟨fun a b ha hb => ?_, fun a b ha hb => ?_, fun a b ha hb => ?_⟩
    · by_cases hab : a = b
      · subst hab; rfl
      · exact weylTwo_agree hK 0 0 (hθk k a ha) (hθk k b hb)
          (by rw [hθ0, hθ0])
          (fun x hx y hy => by
            rw [show (0 : Fin 2).rev = 1 from rfl, hθ1] at hx hy
            exact hnb k a b (Or.inl ha) (Or.inl hb) hab x hx y hy)
    · have hab : a ≠ b := fun h => by subst h; exact hT.asymm _ _ ha hb
      exact weylTwo_agree hK 0 1 (hθk k a ha) (hθk b k hb)
        (by rw [hθ0, hθ1])
        (fun x hx y hy => by
          rw [show (0 : Fin 2).rev = 1 from rfl, hθ1] at hx
          rw [show (1 : Fin 2).rev = 0 from rfl, hθ0] at hy
          exact hnb k a b (Or.inl ha) (Or.inr hb) hab x hx y hy)
    · by_cases hab : a = b
      · subst hab; rfl
      · exact weylTwo_agree hK 1 1 (hθk a k ha) (hθk b k hb)
          (by rw [hθ1, hθ1])
          (fun x hx y hy => by
            rw [show (1 : Fin 2).rev = 0 from rfl, hθ0] at hx hy
            exact hnb k a b (Or.inr ha) (Or.inr hb) hab x hx y hy)
  let WeylGood : Fin r → X → Prop := fun k t =>
    (∀ q (h : adj k q), (θ k q h) (blk K 0 (weylTwo K)) = t) ∧
      (∀ q (h : adj q k), (θ q k h) (blk K 1 (weylTwo K)) = t)
  have weylGood_first : ∀ k a (ha : adj k a), WeylGood k ((θ k a ha) (blk K 0 (weylTwo K))) :=
    fun k a ha => ⟨fun q h => (agree k).1 q a h ha, fun q h => ((agree k).2.1 a q ha h).symm⟩
  have weylGood_second : ∀ k a (ha : adj a k), WeylGood k ((θ a k ha) (blk K 1 (weylTwo K))) :=
    fun k a ha => ⟨fun q h => (agree k).2.1 q a h ha, fun q h => (agree k).2.2 q a h ha⟩
  let N : Fin r → (SL(2, K) →* X) → Prop := fun k ρ =>
    Function.Injective ρ ∧ ρ.range = U k ∧ ∀ t, WeylGood k t → ρ (weylTwo K) = t
  let E : Fin r → (SL(2, K) →* X) → (SL(2, K) →* X) → Prop := fun k ρp ρc =>
    (adj (par k) k → ∃ ψ : SL(3, K) →* X, ψ.comp (blk K 0) = ρp ∧ ψ.comp (blk K 1) = ρc) ∧
      (adj k (par k) → ∃ ψ : SL(3, K) →* X, ψ.comp (blk K 0) = ρc ∧ ψ.comp (blk K 1) = ρp)
  have h₀ : ∃ ρ₀, N k₀ ρ₀ := by
    obtain ⟨c, hc | hc⟩ := hroot
    · refine ⟨(θ k₀ c hc).comp (blk K 0), comp_blk_injective (hθk _ _ hc) 0, ?_,
        fun t ht => ?_⟩
      · rw [← map_Bs, hθ0]
      · exact ht.1 c hc
    · refine ⟨(θ c k₀ hc).comp (blk K 1), comp_blk_injective (hθk _ _ hc) 1, ?_,
        fun t ht => ?_⟩
      · rw [← map_Bs, hθ1]
      · exact ht.2 c hc
  obtain ⟨ρ₀, hρ₀⟩ := h₀
  have hf : ∀ k, k ≠ k₀ → ∀ ρp, N (par k) ρp → ∃ ρc, N k ρc ∧ E k ρp ρc := by
    intro k hk ρp ⟨hinj, hrange, hweyl⟩
    rcases hT.adj_par k hk with h | h
    · obtain ⟨θ', hθ'k, hθ'0, hθ'B, hθ'w⟩ := exists_adjust_side_two hK 0 (hθk _ _ h) hinj
        (by rw [hrange, ← hθ0 _ _ h]) (hweyl _ (weylGood_first _ _ h))
      have hθ'w1 : θ' (blk K 1 (weylTwo K)) = (θ (par k) k h) (blk K 1 (weylTwo K)) := by
        simpa only [show (0 : Fin 2).rev = 1 from rfl] using hθ'w
      refine ⟨θ'.comp (blk K 1), ⟨comp_blk_injective hθ'k 1, ?_, fun t ht => ?_⟩,
        fun _ => ⟨θ', hθ'0, rfl⟩, fun h' => absurd h (hT.asymm _ _ h')⟩
      · rw [← map_Bs]
        exact hθ'B.trans (hθ1 _ _ h)
      · rw [MonoidHom.comp_apply, hθ'w1]
        exact ht.2 (par k) h
    · obtain ⟨θ', hθ'k, hθ'1, hθ'B, hθ'w⟩ := exists_adjust_side_two hK 1 (hθk _ _ h) hinj
        (by rw [hrange, ← hθ1 _ _ h]) (hweyl _ (weylGood_second _ _ h))
      have hθ'w0 : θ' (blk K 0 (weylTwo K)) = (θ k (par k) h) (blk K 0 (weylTwo K)) := by
        simpa only [show (1 : Fin 2).rev = 0 from rfl] using hθ'w
      refine ⟨θ'.comp (blk K 0), ⟨comp_blk_injective hθ'k 0, ?_, fun t ht => ?_⟩,
        fun h' => absurd h (hT.asymm _ _ h'), fun _ => ⟨θ', rfl, hθ'1⟩⟩
      · rw [← map_Bs]
        exact hθ'B.trans (hθ0 _ _ h)
      · rw [MonoidHom.comp_apply, hθ'w0]
        exact ht.1 (par k) h
  obtain ⟨ρ, -, hρN, hρE⟩ := exists_tree_family N E par dep k₀ hT.lt hf hρ₀
  refine ⟨ρ, fun k => ⟨(hρN k).1, (hρN k).2.1⟩, fun i j hij => ?_⟩
  rcases hT.par_of_adj i j hij with ⟨hj, hpj⟩ | ⟨hi, hpi⟩
  · have := (hρE j hj).1
    rw [hpj] at this
    exact this hij
  · have := (hρE i hi).2
    rw [hpi] at this
    exact this hij

end FieldTwo

end CFSG.ClassicalInvolution.WeakCT
