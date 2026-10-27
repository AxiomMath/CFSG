module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRigidity
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherNormShell

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial
open Module Submodule
open scoped Pointwise

universe u

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem eq_smul_of_isotropic_orth (h : UnitaryFieldData p f K) {W : Type u} [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] {B : W →ₛₗ[h.bar] W →ₗ[K] K} (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) (hn : 3 ≤ finrank K W) {u u' : W} (hu : B u u ≠ 0)
    (horth : ∀ w, B w w = 0 → B w u = 0 → B w u' = 0) : ∃ c : K, u' = c • u := by
  have hker : LinearMap.ker (B u) ≤ LinearMap.ker (B u') := by
    rw [← ((isotropic_vectors_span h hB hBl (by omega)).2 u hu hn), Submodule.span_le]
    rintro w ⟨hw, hww⟩
    have hwu : B w u = 0 := by rw [← hB.eq u w, LinearMap.mem_ker.mp hw, map_zero]
    have h1 := horth w hww hwu
    rw [SetLike.mem_coe, LinearMap.mem_ker, ← hB.eq w u', h1, map_zero]
  set c := B u' u / B u u with hc
  refine ⟨h.bar c, sub_eq_zero.mp (hBl _ fun w => ?_)⟩
  have hw0 : w - (B u w / B u u) • u ∈ LinearMap.ker (B u) := by
    rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hu, sub_self]
  have h1 := LinearMap.mem_ker.mp (hker hw0)
  rw [map_sub, map_smul, smul_eq_mul] at h1
  have hBuu : B u' u = c * B u u := by rw [hc, div_mul_cancel₀ _ hu]
  have hval : B u' w = c * B u w := by
    rw [sub_eq_zero.mp h1, hBuu, div_mul_eq_mul_div, eq_comm, eq_div_iff hu]
    ring
  rw [map_sub, LinearMap.sub_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, h.bar_bar,
    smul_eq_mul, hval, sub_self]

section HypH

variable (K r ε) in
abbrev hypH : Submodule K (HypIndex r ε → K) :=
  hypX K r ε ⊔ hypY K r ε

theorem mem_hypH {v : HypIndex r ε → K} :
    v ∈ hypH K r ε ↔ ∃ a b : Fin r → K, v = hypXEmb r ε a + hypYEmb r ε b := by
  constructor
  · intro hv
    obtain ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, hab⟩ := Submodule.mem_sup.mp hv
    exact ⟨a, b, hab.symm⟩
  · rintro ⟨a, b, rfl⟩
    exact Submodule.add_mem_sup ⟨a, rfl⟩ ⟨b, rfl⟩

theorem finrank_hypH : finrank K (hypH K r ε) = 2 * r := by
  change finrank K ↥(hypX K r ε ⊔ hypY K r ε) = 2 * r
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (hypX K r ε) (hypY K r ε)
  rw [hypX_inf_hypY, finrank_bot, finrank_hypX, finrank_hypY] at h1
  omega

variable (h : UnitaryFieldData p f K)

noncomputable abbrev hypHForm :
    hypH K r ε →ₛₗ[h.bar] hypH K r ε →ₗ[K] K :=
  (hypForm h r ε).domRestrict₁₂ (hypH K r ε) (hypH K r ε)

theorem hypHForm_isSymm : (hypHForm (r := r) (ε := ε) h).IsSymm :=
  (hypForm_isSymm h).domRestrict _

theorem hypHForm_separatingLeft : (hypHForm (r := r) (ε := ε) h).SeparatingLeft := by
  rintro ⟨v, hv⟩ hx
  obtain ⟨a, b, rfl⟩ := mem_hypH.mp hv
  have hyi : ∀ i, hypYEmb r ε (Pi.single i 1) ∈ hypH K r ε := fun i =>
    Submodule.mem_sup_right ⟨_, rfl⟩
  have hxi : ∀ i, hypXEmb r ε (Pi.single i 1) ∈ hypH K r ε := fun i =>
    Submodule.mem_sup_left ⟨_, rfl⟩
  have ha : a = 0 := funext fun i => by
    have := hx ⟨_, hyi i⟩
    rw [LinearMap.domRestrict₁₂_apply] at this
    change hypForm h r ε (hypXEmb r ε a + hypYEmb r ε b) (hypYEmb r ε (Pi.single i 1)) = 0
      at this
    rw [show hypYEmb r ε (Pi.single i 1) = hypXEmb r ε 0 + hypYEmb r ε (Pi.single i (1 : K)) by
      rw [map_zero, zero_add], hypForm_xy, hdot_single_right, hdot_zero_right, add_zero] at this
    exact (UnitaryFieldData.bar_eq_zero_iff h).mp this
  have hb : b = 0 := funext fun i => by
    have := hx ⟨_, hxi i⟩
    rw [LinearMap.domRestrict₁₂_apply] at this
    change hypForm h r ε (hypXEmb r ε a + hypYEmb r ε b) (hypXEmb r ε (Pi.single i 1)) = 0
      at this
    rw [show hypXEmb r ε (Pi.single i 1) = hypXEmb r ε (Pi.single i (1 : K)) + hypYEmb r ε 0 by
      rw [map_zero, add_zero], hypForm_xy, hdot_single_right, hdot_zero_right, zero_add] at this
    exact (UnitaryFieldData.bar_eq_zero_iff h).mp this
  subst ha hb
  exact Subtype.ext (by simp)

end HypH

section FixH

variable (h : UnitaryFieldData p f K)

theorem hdot_fin_one (g g' : Fin 1 → K) : hdot h g g' = h.bar (g 0) * g' 0 := by
  simp [hdot, dotProduct]

theorem exists_middle_coeff (hr : 2 ≤ r) {ψ : Equiv.Perm (hypIsotropicLines h r 1)}
    (hψ : ∀ L M : hypIsotropicLines h r 1, LineOrth h L M ↔ LineOrth h (ψ L) (ψ M))
    (hH : ∀ L : hypIsotropicLines h r 1,
      (L : Submodule K (HypIndex r 1 → K)) ≤ hypH K r 1 → ψ L = L)
    {a b : Fin r → K} (hab : hdot h a b + hdot h b a = -1) :
    ∃ g : Fin 1 → K, hdot h g g = 1 ∧
      MapsSpan h ψ (hypXEmb r 1 a + hypZEmb r 1 1 + hypYEmb r 1 b)
        (hypXEmb r 1 a + hypZEmb r 1 g + hypYEmb r 1 b) := by
  set v := hypXEmb r 1 a + hypZEmb r 1 1 + hypYEmb r 1 b with hv
  have h11 : hdot h (1 : Fin 1 → K) 1 = 1 := by rw [hdot_fin_one]; simp
  have hvv : hypForm h r 1 v v = 0 := by
    rw [hv, hypForm_split, h11]
    linear_combination hab
  have hv0 : v ≠ 0 := fun h0 => by
    have := congrFun h0 (Sum.inr (Sum.inl 0))
    simp [hv, hypXEmb, hypYEmb, hypZEmb] at this
  let L : hypIsotropicLines h r 1 := ⟨K ∙ v, span_mem_hypIsotropicLines h hv0 hvv⟩
  obtain ⟨v', hv'0, hv'v', hψv'⟩ := exists_eq_span_of_mem_hypIsotropicLines h (ψ L).2
  set a' : Fin r → K := fun i => v' (Sum.inl i)
  set t' : Fin 1 → K := fun k => v' (Sum.inr (Sum.inl k))
  set b' : Fin r → K := fun i => v' (Sum.inr (Sum.inr i))
  have hv' : v' = hypXEmb r 1 a' + hypZEmb r 1 t' + hypYEmb r 1 b' := hypSplit v'
  set u : hypH K r 1 := ⟨hypXEmb r 1 a + hypYEmb r 1 b, mem_hypH.mpr ⟨a, b, rfl⟩⟩ with hu
  set u' : hypH K r 1 := ⟨hypXEmb r 1 a' + hypYEmb r 1 b', mem_hypH.mpr ⟨a', b', rfl⟩⟩ with hu'
  have hform : ∀ w : HypIndex r 1 → K, w ∈ hypH K r 1 → ∀ (x y : Fin r → K) (t : Fin 1 → K),
      hypForm h r 1 w (hypXEmb r 1 x + hypZEmb r 1 t + hypYEmb r 1 y) =
        hypForm h r 1 w (hypXEmb r 1 x + hypYEmb r 1 y) := by
    intro w hw x y t
    obtain ⟨a₂, b₂, rfl⟩ := mem_hypH.mp hw
    rw [hypForm_xy, show hypXEmb r 1 a₂ + hypYEmb r 1 b₂ =
      hypXEmb r 1 a₂ + hypZEmb r 1 0 + hypYEmb r 1 b₂ by rw [map_zero, add_zero],
      hypForm_split, hdot_zero_left, add_zero]
  have huu : hypHForm h u u ≠ 0 := by
    rw [LinearMap.domRestrict₁₂_apply, hu, hypForm_xy, hab]
    exact neg_ne_zero.mpr one_ne_zero
  have hdimH : 3 ≤ finrank K (hypH K r 1) := by rw [finrank_hypH]; omega
  obtain ⟨c, hc⟩ := eq_smul_of_isotropic_orth (u := u) (u' := u') h (hypHForm_isSymm h)
    (hypHForm_separatingLeft h) hdimH huu fun w hww hwu => by
      by_cases hw0 : w = 0
      · rw [hw0, map_zero, LinearMap.zero_apply]
      have hw0' : (w : HypIndex r 1 → K) ≠ 0 := fun h0 => hw0 (Subtype.ext h0)
      let P : hypIsotropicLines h r 1 := ⟨K ∙ (w : HypIndex r 1 → K),
        span_mem_hypIsotropicLines h hw0' hww⟩
      have hPH : (P : Submodule K (HypIndex r 1 → K)) ≤ hypH K r 1 :=
        (span_singleton_le_iff_mem _ _).mpr w.2
      have hPP : (ψ P : Submodule K (HypIndex r 1 → K)) = K ∙ (w : HypIndex r 1 → K) := by
        rw [hH P hPH]
      have h1 := (rigid_pair h hψ (L := P) (M := L) rfl rfl hPP hψv').mp (by
        rw [hv, hform _ w.2]
        exact hwu)
      rw [hv', hform _ w.2] at h1
      exact h1
  have hc' : hypXEmb r 1 a' + hypYEmb r 1 b' = hypXEmb r 1 (c • a) + hypYEmb r 1 (c • b) := by
    have := congrArg Subtype.val hc
    rw [map_smul, map_smul, ← smul_add]
    exact this
  have ha' : a' = c • a := funext fun i => by
    have := congrFun hc' (Sum.inl i)
    simpa [hypXEmb, hypYEmb] using this
  have hb' : b' = c • b := funext fun i => by
    have := congrFun hc' (Sum.inr (Sum.inr i))
    simpa [hypXEmb, hypYEmb] using this
  have hv'2 : v' = c • (hypXEmb r 1 a + hypYEmb r 1 b) + hypZEmb r 1 t' := by
    rw [hv', ha', hb', smul_add, map_smul, map_smul]
    abel
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul, zero_add] at hv'2
    apply hv'0
    rw [hv'2]
    have h1 := hv'v'
    rw [hv'2] at h1
    have h2 : hypForm h r 1 (hypZEmb r 1 t') (hypZEmb r 1 t') = hdot h t' t' := by
      have := hypForm_split (r := r) h 0 0 0 0 t' t'
      simpa using this
    rw [h2] at h1
    rw [eq_zero_of_hdot_self h le_rfl h1, map_zero]
  have hvg : c⁻¹ • v' = hypXEmb r 1 a + hypZEmb r 1 (c⁻¹ • t') + hypYEmb r 1 b := by
    rw [hv'2, smul_add, smul_smul, inv_mul_cancel₀ hc0, one_smul, map_smul]
    abel
  refine ⟨c⁻¹ • t', ?_, fun L₁ hL₁ => ?_⟩
  · have hmem : hypXEmb r 1 a + hypZEmb r 1 (c⁻¹ • t') + hypYEmb r 1 b ∈
        (ψ L : Submodule K (HypIndex r 1 → K)) := by
      rw [hψv', ← hvg]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v')
    have h1 := (mem_hypIsotropicLines.mp (ψ L).2).2 _ hmem
    rw [hypForm_split] at h1
    linear_combination h1 - hab
  · have hLL : L₁ = L := Subtype.ext hL₁
    rw [hLL, hψv', ← span_singleton_smul_eq (IsUnit.mk0 _ (inv_ne_zero hc0)), hvg]

end FixH

theorem hypH_coords (x : hypH K r ε) :
    (x : HypIndex r ε → K) = hypXEmb r ε (fun i => (x : HypIndex r ε → K) (Sum.inl i)) +
      hypYEmb r ε (fun i => (x : HypIndex r ε → K) (Sum.inr (Sum.inr i))) := by
  obtain ⟨a, b, hab⟩ := mem_hypH.mp x.2
  rw [hab]
  funext c
  rcases c with i | k | i <;> simp [hypXEmb, hypYEmb]

section Const

variable (h : UnitaryFieldData p f K)

theorem exists_mid_pt {a b : Fin r → K} (hab : hdot h a b + hdot h b a = -1) :
    ∃ L : hypIsotropicLines h r 1, (L : Submodule K (HypIndex r 1 → K)) =
      K ∙ (hypXEmb r 1 a + hypZEmb r 1 1 + hypYEmb r 1 b) := by
  have h11 : hdot h (1 : Fin 1 → K) 1 = 1 := by rw [hdot_fin_one]; simp
  have hvv : hypForm h r 1 (hypXEmb r 1 a + hypZEmb r 1 1 + hypYEmb r 1 b)
      (hypXEmb r 1 a + hypZEmb r 1 1 + hypYEmb r 1 b) = 0 := by
    rw [hypForm_split, h11]
    linear_combination hab
  have hv0 : hypXEmb r 1 a + hypZEmb r 1 1 + hypYEmb r 1 b ≠ 0 := fun h0 => by
    have := congrFun h0 (Sum.inr (Sum.inl 0))
    simp [hypXEmb, hypYEmb, hypZEmb] at this
  exact ⟨⟨_, span_mem_hypIsotropicLines h hv0 hvv⟩, rfl⟩

theorem exists_const_middle (hr : 2 ≤ r) {ψ : Equiv.Perm (hypIsotropicLines h r 1)}
    (hψ : ∀ L M : hypIsotropicLines h r 1, LineOrth h L M ↔ LineOrth h (ψ L) (ψ M))
    (hH : ∀ L : hypIsotropicLines h r 1,
      (L : Submodule K (HypIndex r 1 → K)) ≤ hypH K r 1 → ψ L = L) :
    ∃ γ : Fin 1 → K, hdot h γ γ = 1 ∧ ∀ a b : Fin r → K, hdot h a b + hdot h b a = -1 →
      MapsSpan h ψ (hypXEmb r 1 a + hypZEmb r 1 1 + hypYEmb r 1 b)
        (hypXEmb r 1 a + hypZEmb r 1 γ + hypYEmb r 1 b) := by
  classical
  have hex : ∀ a b : Fin r → K, ∃ g : Fin 1 → K, hdot h a b + hdot h b a = -1 →
      hdot h g g = 1 ∧ MapsSpan h ψ (hypXEmb r 1 a + hypZEmb r 1 1 + hypYEmb r 1 b)
        (hypXEmb r 1 a + hypZEmb r 1 g + hypYEmb r 1 b) := fun a b => by
    by_cases hab : hdot h a b + hdot h b a = -1
    · obtain ⟨g, hg⟩ := exists_middle_coeff h hr hψ hH hab
      exact ⟨g, fun _ => hg⟩
    · exact ⟨0, fun h0 => absurd h0 hab⟩
  choose G hG using hex
  have h11 : hdot h (1 : Fin 1 → K) 1 = 1 := by rw [hdot_fin_one]; simp
  have hadj : ∀ a b a₂ b₂ : Fin r → K, hdot h a b + hdot h b a = -1 →
      hdot h a₂ b₂ + hdot h b₂ a₂ = -1 → hdot h a b₂ + hdot h b a₂ = -1 →
      G a₂ b₂ = G a b := by
    intro a b a₂ b₂ hab hab₂ hpair
    obtain ⟨L, hL⟩ := exists_mid_pt h hab
    obtain ⟨M, hM⟩ := exists_mid_pt h hab₂
    obtain ⟨hg, hL'⟩ := hG a b hab
    obtain ⟨hg₂, hM'⟩ := hG a₂ b₂ hab₂
    have h1 := (rigid_pair h hψ hL hM (hL' L hL) (hM' M hM)).mp (by
      rw [hypForm_split, h11]
      linear_combination hpair)
    rw [hypForm_split] at h1
    have h2 : hdot h (G a b) (G a₂ b₂) = 1 := by linear_combination h1 - hpair
    rw [hdot_fin_one] at hg h2
    have hb0 : h.bar (G a b 0) ≠ 0 := fun h0 => by
      rw [h0, zero_mul] at hg
      exact zero_ne_one hg
    funext k
    obtain rfl : k = 0 := Subsingleton.elim _ _
    exact mul_left_cancel₀ hb0 (h2.trans hg.symm)
  obtain ⟨c₀, hc₀⟩ := exists_add_bar_eq_neg_one h
  set i₀ : Fin r := ⟨0, by omega⟩
  set a₀ : Fin r → K := Pi.single i₀ 1 with ha₀
  set b₀ : Fin r → K := c₀ • Pi.single i₀ 1 with hb₀
  have hab₀ : hdot h a₀ b₀ + hdot h b₀ a₀ = -1 := by
    rw [ha₀, hb₀, hdot_smul_right, hdot_single_left, hdot_smul_left, hdot_single_left,
      Pi.single_eq_same, mul_one, mul_one, ← hc₀]
  refine ⟨G a₀ b₀, (hG a₀ b₀ hab₀).1, fun a b hab => ?_⟩
  have hBH := hypHForm_isSymm (r := r) (ε := 1) h
  have hBlH := hypHForm_separatingLeft (r := r) (ε := 1) h
  have hdH : 4 ≤ finrank K (hypH K r 1) := by rw [finrank_hypH]; omega
  set coA : hypH K r 1 → Fin r → K := fun x i => (x : HypIndex r 1 → K) (Sum.inl i)
  set coB : hypH K r 1 → Fin r → K := fun x i => (x : HypIndex r 1 → K) (Sum.inr (Sum.inr i))
  have hBco : ∀ x y : hypH K r 1,
      hypHForm h x y = hdot h (coA x) (coB y) + hdot h (coB x) (coA y) := fun x y => by
      rw [LinearMap.domRestrict₁₂_apply, hypH_coords x, hypH_coords y, hypForm_xy]
  let u₀ : hypH K r 1 := ⟨hypXEmb r 1 a₀ + hypYEmb r 1 b₀, mem_hypH.mpr ⟨_, _, rfl⟩⟩
  let u : hypH K r 1 := ⟨hypXEmb r 1 a + hypYEmb r 1 b, mem_hypH.mpr ⟨_, _, rfl⟩⟩
  have hcoA : ∀ a b : Fin r → K, coA ⟨hypXEmb r 1 a + hypYEmb r 1 b, mem_hypH.mpr ⟨_, _, rfl⟩⟩ =
      a := fun a b => funext fun i => by simp [coA, hypXEmb, hypYEmb]
  have hcoB : ∀ a b : Fin r → K, coB ⟨hypXEmb r 1 a + hypYEmb r 1 b, mem_hypH.mpr ⟨_, _, rfl⟩⟩ =
      b := fun a b => funext fun i => by simp [coB, hypXEmb, hypYEmb]
  have hu₀ : hypHForm h u₀ u₀ = -1 := by rw [hBco, hcoA, hcoB, hab₀]
  have hu : hypHForm h u u = -1 := by rw [hBco, hcoA, hcoB, hab]
  have hm1 : h.bar (-1 : K) = -1 := by rw [map_neg, map_one]
  obtain ⟨⟨m, -, w, hw0, hwl, hwn, hwp⟩, -⟩ := norm_shell_graph_connected h hBH hBlH hdH hm1
    (neg_ne_zero.mpr one_ne_zero) hu₀ hu
  have hpath : ∀ i : Fin (m + 1), G (coA (w i)) (coB (w i)) = G a₀ b₀ := by
    intro i
    induction i using Fin.induction with
    | zero => rw [hw0, hcoA, hcoB]
    | succ i ih =>
      rw [← ih]
      refine hadj _ _ _ _ ?_ ?_ ?_
      · rw [← hBco]
        exact hwn _
      · rw [← hBco]
        exact hwn _
      · rw [← hBco]
        exact hwp i
  have := hpath (Fin.last m)
  rw [hwl, hcoA, hcoB] at this
  rw [← this]
  exact (hG a b hab).2

end Const

theorem diagFun_split (c d : K) (a b : Fin r → K) (t : Fin ε → K) :
    diagFun c d (hypXEmb r ε a + hypZEmb r ε t + hypYEmb r ε b) =
      hypXEmb r ε a + hypZEmb r ε (d • t) + hypYEmb r ε (c • b) := by
  funext x
  rcases x with i | k | i <;> simp [diagFun, hypXEmb, hypYEmb, hypZEmb]

theorem lineOrth_inv_mul (h : UnitaryFieldData p f K) (x : semilinearSimilitudes h r ε)
    {ψ : Equiv.Perm (hypIsotropicLines h r ε)}
    (hψ : ∀ L M : hypIsotropicLines h r ε, LineOrth h L M ↔ LineOrth h (ψ L) (ψ M)) :
    ∀ L M : hypIsotropicLines h r ε, LineOrth h L M ↔
      LineOrth h (((semilinearPointAction h r ε x)⁻¹ * ψ) L)
        (((semilinearPointAction h r ε x)⁻¹ * ψ) M) := by
  intro L M
  rw [hψ L M]
  have := lineOrth_semilinearPointAction h x⁻¹ (ψ L) (ψ M)
  rw [map_inv] at this
  exact this.symm

theorem realize_of_fix_hypH (h : UnitaryFieldData p f K) (hr : 2 ≤ r) (hε : ε ≤ 1)
    {ψ : Equiv.Perm (hypIsotropicLines h r ε)}
    (hψ : ∀ L M : hypIsotropicLines h r ε, LineOrth h L M ↔ LineOrth h (ψ L) (ψ M))
    (hH : ∀ L : hypIsotropicLines h r ε,
      (L : Submodule K (HypIndex r ε → K)) ≤ hypH K r ε → ψ L = L) :
    ∃ x : semilinearSimilitudes h r ε, ψ = semilinearPointAction h r ε x := by
  obtain rfl | rfl : ε = 0 ∨ ε = 1 := by omega
  ·
    refine ⟨1, Equiv.ext fun L => ?_⟩
    rw [map_one, Equiv.Perm.one_apply]
    refine hH L fun v _ => mem_hypH.mpr
      ⟨fun i => v (Sum.inl i), fun i => v (Sum.inr (Sum.inr i)), ?_⟩
    conv_lhs => rw [hypSplit v]
    rw [show (fun k : Fin 0 => v (Sum.inr (Sum.inl k))) = 0 from
      funext fun k => k.elim0, map_zero, add_zero]
  obtain ⟨γ, hγ, hγL⟩ := exists_const_middle h hr hψ hH
  rw [hdot_fin_one] at hγ
  have hN : h.norm (γ 0) = 1 := by rw [UnitaryFieldData.norm, mul_comm, hγ]
  have hγ0 : γ 0 ≠ 0 := fun h0 => by
    rw [h0, map_zero, zero_mul] at hγ
    exact zero_ne_one hγ
  have hD := hypDiag_similitude (r := r) (ε := 1) h one_ne_zero hγ0 (map_one _) hN
  refine ⟨⟨⟨glOfLinearEquiv (hypDiagEquiv (r := r) (ε := 1) one_ne_zero hγ0), 1⟩,
    1, one_ne_zero, map_one _, hD⟩, Equiv.ext fun L => Subtype.ext ?_⟩
  obtain ⟨v, -, -, hLv⟩ := exists_eq_span_of_mem_hypIsotropicLines h L.2
  change (ψ L : Submodule K (HypIndex r 1 → K)) =
    (⟨glOfLinearEquiv (hypDiagEquiv (r := r) (ε := 1) one_ne_zero hγ0), 1⟩ :
      SemiGL (HypIndex r 1) K) • (L : Submodule K (HypIndex r 1 → K))
  rw [hLv, semiGL_smul_eq_map, Submodule.map_span, Set.image_singleton, semiLin_apply]
  change _ = K ∙ (((glOfLinearEquiv (hypDiagEquiv (r := r) (ε := 1) one_ne_zero hγ0) :
    GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) *ᵥ v)
  rw [glOfLinearEquiv_mulVec, hypDiagEquiv_apply]
  set a : Fin r → K := fun i => v (Sum.inl i)
  set t : Fin 1 → K := fun k => v (Sum.inr (Sum.inl k))
  set b : Fin r → K := fun i => v (Sum.inr (Sum.inr i))
  have hv : v = hypXEmb r 1 a + hypZEmb r 1 t + hypYEmb r 1 b := hypSplit v
  rw [hv, diagFun_split, one_smul]
  by_cases ht : t 0 = 0
  ·
    have ht0 : t = 0 := funext fun k => by
      obtain rfl : k = 0 := Subsingleton.elim _ _
      exact ht
    have hLH : (L : Submodule K (HypIndex r 1 → K)) ≤ hypH K r 1 := by
      rw [hLv, span_singleton_le_iff_mem, hv, ht0, map_zero, add_zero]
      exact mem_hypH.mpr ⟨_, _, rfl⟩
    rw [hH L hLH, hLv, hv, ht0, smul_zero]
  ·
    have hts : t = t 0 • (1 : Fin 1 → K) := funext fun k => by
      obtain rfl : k = 0 := Subsingleton.elim _ _
      simp
    have hγ1 : γ = γ 0 • (1 : Fin 1 → K) := funext fun k => by
      obtain rfl : k = 0 := Subsingleton.elim _ _
      simp
    set a₁ := (t 0)⁻¹ • a with ha₁
    set b₁ := (t 0)⁻¹ • b with hb₁
    have hvt : v = t 0 • (hypXEmb r 1 a₁ + hypZEmb r 1 1 + hypYEmb r 1 b₁) := by
      rw [hv, smul_add, smul_add, ← map_smul, ← map_smul, ← map_smul, ha₁, hb₁, smul_smul,
        smul_smul, mul_inv_cancel₀ ht, one_smul, one_smul, ← hts]
    have hL₁ : (L : Submodule K (HypIndex r 1 → K)) =
        K ∙ (hypXEmb r 1 a₁ + hypZEmb r 1 1 + hypYEmb r 1 b₁) := by
      rw [hLv, hvt, span_singleton_smul_eq (IsUnit.mk0 _ ht)]
    have hab₁ : hdot h a₁ b₁ + hdot h b₁ a₁ = -1 := by
      have h1 := hypForm_self_of_span h L hL₁
      rw [hypForm_split, hdot_fin_one] at h1
      simp only [Pi.one_apply, map_one, mul_one] at h1
      linear_combination h1
    have hrhs : hypXEmb r 1 a + hypZEmb r 1 (γ 0 • t) + hypYEmb r 1 b =
        t 0 • (hypXEmb r 1 a₁ + hypZEmb r 1 γ + hypYEmb r 1 b₁) := by
      funext x
      rcases x with i | k | i
      · simp [hypXEmb, hypYEmb, hypZEmb, ha₁, mul_inv_cancel_left₀ ht]
      · obtain rfl : k = 0 := Subsingleton.elim _ _
        simp [hypXEmb, hypYEmb, hypZEmb, mul_comm]
      · simp [hypXEmb, hypYEmb, hypZEmb, hb₁, mul_inv_cancel_left₀ ht]
    rw [hγL a₁ b₁ hab₁ L hL₁, hrhs, span_singleton_smul_eq (IsUnit.mk0 _ ht)]


theorem unitary_higher_geometric_semilinear_realization (h : UnitaryFieldData p f K)
    (hr : 3 ≤ r) (hε : ε ≤ 1) :
    (∀ φ : Equiv.Perm (hypIsotropicLines h r ε),
      (∀ L M : hypIsotropicLines h r ε, LineOrth h L M ↔ LineOrth h (φ L) (φ M)) →
      ∃ x : semilinearSimilitudes h r ε, φ = semilinearPointAction h r ε x) ∧
    {φ : Equiv.Perm (hypIsotropicLines h r ε) |
        ∀ L M : hypIsotropicLines h r ε, LineOrth h L M ↔ LineOrth h (φ L) (φ M)} =
      (semilinearPointGroup h r ε : Set (Equiv.Perm (hypIsotropicLines h r ε))) := by
  have hreal : ∀ φ : Equiv.Perm (hypIsotropicLines h r ε),
      (∀ L M : hypIsotropicLines h r ε, LineOrth h L M ↔ LineOrth h (φ L) (φ M)) →
      ∃ x : semilinearSimilitudes h r ε, φ = semilinearPointAction h r ε x := by
    intro φ hφ
    obtain ⟨x₁, -, hx₁⟩ := unitary_opposite_space_normalization h hr hε φ hφ
    obtain ⟨φ₁, hφ₁def⟩ : ∃ φ₁ : Equiv.Perm (hypIsotropicLines h r ε),
        φ₁ = (semilinearPointAction h r ε x₁)⁻¹ * φ := ⟨_, rfl⟩
    have hφ₁ : ∀ L M, LineOrth h L M ↔ LineOrth h (φ₁ L) (φ₁ M) := by
      rw [hφ₁def]
      exact lineOrth_inv_mul h x₁ hφ
    have hfix₁ : ∀ L : hypIsotropicLines h r ε,
        ((L : Submodule K (HypIndex r ε → K)) ≤ hypX K r ε ∨
          (L : Submodule K (HypIndex r ε → K)) ≤ hypY K r ε) → φ₁ L = L := fun L hL => by
      rw [hφ₁def, Equiv.Perm.mul_apply, hx₁ L hL, Equiv.Perm.inv_eq_iff_eq]
    obtain ⟨c, d, hc, hd, -, -, hD, hDL⟩ := unitary_hyperbolic_point_rigidity h hr hε φ₁ hφ₁
      (fun L hL => hfix₁ L (Or.inl hL)) (fun L hL => hfix₁ L (Or.inr hL))
    set x₂ : semilinearSimilitudes h r ε := ⟨_, hD⟩ with hx₂
    obtain ⟨φ₂, hφ₂def⟩ : ∃ φ₂ : Equiv.Perm (hypIsotropicLines h r ε),
        φ₂ = (semilinearPointAction h r ε x₂)⁻¹ * φ₁ := ⟨_, rfl⟩
    have hφ₂ : ∀ L M, LineOrth h L M ↔ LineOrth h (φ₂ L) (φ₂ M) := by
      rw [hφ₂def]
      exact lineOrth_inv_mul h x₂ hφ₁
    have hfix₂ : ∀ L : hypIsotropicLines h r ε,
        (L : Submodule K (HypIndex r ε → K)) ≤ hypH K r ε → φ₂ L = L := fun L hL => by
      rw [hφ₂def, Equiv.Perm.mul_apply, hDL L hL, Equiv.Perm.inv_eq_iff_eq]
    obtain ⟨x₃, hx₃⟩ := realize_of_fix_hypH h (by omega) hε hφ₂ hfix₂
    refine ⟨x₁ * x₂ * x₃, ?_⟩
    rw [map_mul, map_mul, ← hx₃, hφ₂def, hφ₁def]
    group
  refine ⟨hreal, Set.ext fun φ => ⟨fun hφ => ?_, ?_⟩⟩
  · obtain ⟨x, rfl⟩ := hreal φ hφ
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩ L M
    exact (lineOrth_semilinearPointAction h x L M).symm

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
