
module

public import CFSG.Certificates.Kernel.ThDemp.ChainExBase

public import CFSG.Certificates.Kernel.ThDemp.Sound
import CFSG.Certificates.Kernel.Th.Spec.FwdSlp

public section

namespace CFSG.Certificates.ThDemp

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.KC.Th.Spec.FwdRel CFSG.KC.ThDemp
  CFSG.Certificates.ThDemp.Chain

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

theorem exists_chain {D : DempData} (hF : DempFacts D) {J : Subgroup (GL (Fin 248) (ZMod 2))}
    {a b : J} (ha : 𝕄 a = pkMat D.SA) (hb : 𝕄 b = pkMat D.SB) :
    (∀ r, 0 < r → r < D.nreg → ∃ x : J, 𝕄 x = pkMat (D.RB r)) ∧
    ∃ d₀ d₁ : J, 𝕄 d₀ = pkMat (D.RB (regAt D.rd 0)) ∧ 𝕄 d₁ = pkMat (D.RB (regAt D.rd 1)) ∧
      ∃ t : ℕ → ℕ → J,
        (∀ l < 6, ∀ i < D.oszL l, t l i ∈ Subgroup.closure ({d₀, d₁} : Set J) ∧
          𝕄 (t l i) = pkMat (D.T l i)) ∧
        (∀ x ∈ Subgroup.closure ({d₀, d₁} : Set J), ∃! y : Coords, chainProd t y = x) ∧
        Nat.card (Subgroup.closure ({d₀, d₁} : Set J)) = 319979520 ∧
        (∀ x ∈ Subgroup.closure ({d₀, d₁} : Set J),
          (∀ l < 5, Matrix.vecMul (pkVec (D.bvL l)) (𝕄 x) = pkVec (D.bvL l)) →
          ∃ z < 32, x = t 5 z) := by
  have hk := hF.consts
  have hr1 : 0 < D.r1 := lt_of_le_of_lt (Nat.zero_le _) (hF.rd 0 (by norm_num)).2
  have hn : 0 < D.nreg := lt_of_le_of_lt (Nat.zero_le _) (hF.pr 0 (by have := hF.npr2; omega)).2
  have hreg1 : ∀ r, 0 < r → r < D.r1 → RegIn (⊤ : Subgroup J) D.RB r := by
    have hS : ∀ k, 0 < k → k < 3 → RegIn (⊤ : Subgroup J) D.RB k := by
      intro k hk0 hk3
      obtain rfl | rfl : k = 1 ∨ k = 2 := by omega
      · exact ⟨a, Subgroup.mem_top a, by rw [ha, hF.rb1]⟩
      · exact ⟨b, Subgroup.mem_top b, by rw [hb, hF.rb2]⟩
    have := FwdSlp.runSlp_induct (RegIn (⊤ : Subgroup J) D.RB)
      (fun _ _ _ hx hy e => regIn_mul hk hx hy e) (fun _ _ _ hx _ he e => regIn_pow hk hx he e)
      (fun _ _ hx e => regIn_inv hk hx e) D.cs1 3 hS (by rw [hF.slp1]; exact hr1)
    rwa [hF.slp1] at this
  have hreg : ∀ r, 0 < r → r < D.nreg → RegIn (⊤ : Subgroup J) D.RB r := by
    have := FwdSlp.runSlp_induct (RegIn (⊤ : Subgroup J) D.RB)
      (fun _ _ _ hx hy e => regIn_mul hk hx hy e) (fun _ _ _ hx _ he e => regIn_pow hk hx he e)
      (fun _ _ hx e => regIn_inv hk hx e) D.cs2 D.r1 hreg1 (by rw [hF.slp2]; exact hn)
    rwa [hF.slp2] at this
  refine ⟨fun r h0 h1 => by
    obtain ⟨x, -, e⟩ := hreg r h0 h1
    exact ⟨x, e⟩, ?_⟩
  obtain ⟨d₀, -, hd₀⟩ := hreg1 _ (hF.rd 0 (by norm_num)).1 (hF.rd 0 (by norm_num)).2
  obtain ⟨d₁, -, hd₁⟩ := hreg1 _ (hF.rd 1 (by norm_num)).1 (hF.rd 1 (by norm_num)).2
  set Dg : Subgroup J := Subgroup.closure ({d₀, d₁} : Set J) with hDg
  have hmk : ∀ k, marked D.marks k = true → RegIn Dg D.RB k := by
    intro k hk'
    rcases marked_marks hk' with rfl | rfl
    · exact ⟨d₀, Subgroup.subset_closure (by simp), hd₀⟩
    · exact ⟨d₁, Subgroup.subset_closure (by simp), hd₁⟩
  have hm := (FwdSlp.runMarked_induct (RegIn Dg D.RB)
    (fun _ _ _ hx hy e => regIn_mul hk hx hy e) (fun _ _ _ hx _ he e => regIn_pow hk hx he e)
    (fun _ _ hx e => regIn_inv hk hx e) D.cs2 D.r1 D.marks hmk (by rw [hF.slp2]; exact hn)
    (by rw [hF.slp2]; exact hF.nreg_lt)).2
  have hprD : ∀ g < D.npr, RegIn Dg D.RB (regAt D.pr g) := fun g hg => hm _ (hF.marks_ok g hg)
  have hs : ∀ g, ∃ x : J, x ∈ Dg ∧ (g < D.npr → 𝕄 x = pkMat (D.S g)) := by
    intro g
    by_cases hg : g < D.npr
    · obtain ⟨x, hx, ex⟩ := hprD g hg
      exact ⟨x, hx, fun _ => ex⟩
    · exact ⟨1, Subgroup.one_mem _, fun h => absurd h hg⟩
  choose s hsD hsM using hs
  have ht : ∀ l i, ∃ x : J, l < D.L → i < D.oszL l → 𝕄 x = pkMat (D.T l i) := by
    intro l i
    by_cases h : l < D.L ∧ i < D.oszL l
    · rcases Nat.eq_zero_or_pos i with rfl | hi
      · refine ⟨1, fun _ _ => ?_⟩
        rw [T_of_zero (hF.tr0 l h.1), pkMat_one hk]
        rfl
      · obtain ⟨par, g, -, -, -, h0, hlt, -, -⟩ := hF.tree l h.1 i hi h.2
        obtain ⟨x, -, ex⟩ := hreg _ h0 hlt
        exact ⟨x, fun _ _ => by rw [ex, T_of_pos h0]⟩
    · exact ⟨1, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose t htM using ht
  let act : (Fin 248 → ZMod 2) → J → (Fin 248 → ZMod 2) := fun v x => Matrix.vecMul v (𝕄 x)
  have hpt_lt : ∀ l < D.L, ∀ i < D.oszL l, D.P l i < 2 ^ 248 := by
    intro l hl i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [hF.P0 l hl]
      exact hF.bv_lt l hl
    · obtain ⟨par, g, -, -, -, -, -, -, e⟩ := hF.tree l hl i hi0 hi
      rw [e]
      exact vecB_lt hk _ _
  have hlev_le : ∀ l k, l ≤ k → k ≤ D.L →
      lev D.frL D.npr s k ≤ lev D.frL D.npr s l := by
    intro l k hlk hkL
    have hfrm : D.frL l ≤ D.frL k := by
      induction k, hlk using Nat.le_induction with
      | base => exact le_rfl
      | succ k hlk ih => exact (ih (by omega)).trans (hF.mono k (by omega))
    refine Subgroup.closure_mono ?_
    rintro x ⟨g, hg1, hg2, rfl⟩
    exact ⟨g, le_trans hfrm hg1, hg2, rfl⟩
  have hsl : ∀ l g, D.frL l ≤ g → g < D.npr → s g ∈ lev D.frL D.npr s l :=
    fun l g h1 h2 => Subgroup.subset_closure ⟨g, h1, h2, rfl⟩
  have htree : ∀ l < D.L, ∀ i < D.oszL l, t l i ∈ lev D.frL D.npr s l ∧
      act (pkVec (D.bvL l)) (t l i) = pkVec (D.P l i) := by
    intro l hl i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · have e1 : t l 0 = 1 := mat_injective (by
          change 𝕄 (t l 0) = 1
          rw [htM l 0 hl hi, T_of_zero (hF.tr0 l hl), pkMat_one hk])
        refine ⟨by rw [e1]; exact Subgroup.one_mem _, ?_⟩
        change Matrix.vecMul _ (𝕄 (t l 0)) = _
        rw [e1, hF.P0 l hl]
        exact Matrix.vecMul_one _
      · obtain ⟨par, g, hpar, hg1, hg2, h0, hlt, eR, eP⟩ := hF.tree l hl i hi0 hi
        obtain ⟨ihm, ihp⟩ := ih par hpar (by omega)
        have e1 : t l i = t l par * s g := mat_injective (by
          change 𝕄 (t l i) = 𝕄 (t l par * s g)
          rw [htM l i hl hi, T_of_pos h0, eR, DempData.mul, pkMat_mulB hk, mat_mul,
            htM l par hl (by omega), hsM g hg2])
        refine ⟨by rw [e1]; exact Subgroup.mul_mem _ ihm (hsl l g hg1 hg2), ?_⟩
        change Matrix.vecMul _ (𝕄 (t l i)) = _
        rw [e1, mat_mul, ← Matrix.vecMul_vecMul]
        change Matrix.vecMul (act (pkVec (D.bvL l)) (t l par)) _ = _
        rw [ihp, hsM g hg2, ← pkVec_vecB hk, eP]
  have hsift : ∀ l < D.L, ∀ e : ℕ,
      (∀ q, l + 1 + q < D.L → bitsN e (8 * (q + 1)) 8 < D.oszL (l + 1 + q)) → ∀ X : ℕ,
      ∃ u ∈ lev D.frL D.npr s (l + 1), pkMat (D.sift l e X) = 𝕄 u * pkMat X := by
    intro l hl e hy X
    have key : ∀ q, q ≤ D.L - l - 1 → ∃ u ∈ lev D.frL D.npr s (l + 1),
        pkMat (Nat.rec (motive := fun _ => Nat) X
          (fun q acc => D.stepY (Nat.add (Nat.add l (nat_lit 1)) q)
            (bitsN e (Nat.mul (nat_lit 8) (Nat.succ q)) (nat_lit 8)) acc) q) = 𝕄 u * pkMat X := by
      intro q
      induction q with
      | zero =>
        intro _
        refine ⟨1, Subgroup.one_mem _, ?_⟩
        change pkMat X = (1 : Matrix (Fin 248) (Fin 248) (ZMod 2)) * pkMat X
        rw [Matrix.one_mul]
      | succ q ih =>
        intro hq
        obtain ⟨u, hu, eu⟩ := ih (by omega)
        have hyl : bitsN e (Nat.mul 8 (Nat.succ q)) 8 < D.oszL (l + 1 + q) := hy q (by omega)
        rw [Nat.rec_add_one]
        generalize hY : bitsN e (Nat.mul 8 (Nat.succ q)) 8 = y at hyl
        generalize hR : Nat.rec (motive := fun _ => Nat) X
          (fun q acc => D.stepY (Nat.add (Nat.add l (nat_lit 1)) q)
            (bitsN e (Nat.mul (nat_lit 8) (Nat.succ q)) (nat_lit 8)) acc) q = R at eu
        change ∃ u ∈ lev D.frL D.npr s (l + 1), pkMat (D.stepY (l + 1 + q) y R) = 𝕄 u * pkMat X
        unfold DempData.stepY
        cases hb : Nat.beq y 0
        · refine ⟨t (l + 1 + q) y * u, Subgroup.mul_mem _ ?_ hu, ?_⟩
          · exact hlev_le (l + 1) (l + 1 + q) (by omega) (by omega)
              (htree (l + 1 + q) (by omega) y hyl).1
          · change pkMat (D.mul (D.T (l + 1 + q) y) R) = _
            rw [DempData.mul, pkMat_mulB hk, eu, mat_mul, htM _ _ (by omega) hyl, Matrix.mul_assoc]
        · exact ⟨u, hu, eu⟩
    exact key _ le_rfl
  have hpos : ∀ l < D.L, 0 < D.oszL l := by
    intro l hl
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hF.osz
    have h6 : l < 6 := by rw [← hF.L6]; exact hl
    rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
      rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h0]; norm_num
    · rw [h1]; norm_num
    · rw [h2]; norm_num
    · rw [h3]; norm_num
    · rw [h4]; norm_num
    · rw [h5]; norm_num
  have hact1 : ∀ v, act v 1 = v := fun v => Matrix.vecMul_one v
  have hact2 : ∀ v (g h : J), act v (g * h) = act (act v g) h := by
    intro v g h
    change Matrix.vecMul v (𝕄 (g * h)) = Matrix.vecMul (Matrix.vecMul v (𝕄 g)) (𝕄 h)
    rw [mat_mul, Matrix.vecMul_vecMul]
  have ht0 : ∀ l < D.L, t l 0 = 1 := by
    intro l hl
    refine mat_injective ?_
    change 𝕄 (t l 0) = 1
    rw [htM l 0 hl (hpos l hl), T_of_zero (hF.tr0 l hl), pkMat_one hk]
  have hfix : ∀ l < D.L, ∀ g, D.frL (l + 1) ≤ g → g < D.npr →
      act (pkVec (D.bvL l)) (s g) = pkVec (D.bvL l) := by
    intro l hl g hg1 hg2
    change Matrix.vecMul _ (𝕄 (s g)) = _
    rw [hsM g hg2, ← pkVec_vecB hk, hF.fix l hl g hg1 hg2]
  have hres : ∀ l < D.L, ∀ i < D.oszL l, ∀ g, D.frL l ≤ g → g < D.npr → ∃ z < D.oszL l,
      t l i * s g * (t l z)⁻¹ ∈ lev D.frL D.npr s (l + 1) := by
    intro l hl i hi g hg1 hg2
    obtain ⟨z, hz, e, hy, heq⟩ := hF.res l hl i hi g hg1 hg2
    obtain ⟨u, hu, eu⟩ := hsift l hl e hy (D.T l z)
    refine ⟨z, hz, ?_⟩
    have e1 : t l i * s g = u * t l z := by
      refine mat_injective ?_
      change 𝕄 (t l i * s g) = 𝕄 (u * t l z)
      rw [mat_mul, mat_mul, htM l i hl hi, hsM g hg2, ← pkMat_mulB hk, ← DempData.mul, heq, eu,
        htM l z hl hz]
    rw [e1, mul_inv_cancel_right]
    exact hu
  have hH : ChainHyp act D.L D.npr D.frL D.oszL (fun l => pkVec (D.bvL l)) s
      (fun l i => pkVec (D.P l i)) t :=
    { act_one := hact1
      act_mul := hact2
      frL := hF.frL
      mono := hF.mono
      pos := hpos
      t0 := ht0
      O0 := fun l hl => by rw [hF.P0 l hl]
      tmem := fun l hl i hi => (htree l hl i hi).1
      tpt := fun l hl i hi => (htree l hl i hi).2
      inj := fun l hl i j hi hj e => hF.inj l hl i j hi hj
        (pkVec_inj (hpt_lt l hl i hi) (hpt_lt l hl j hj) e)
      fix := hfix
      res := hres }
  have hlev0 : lev D.frL D.npr s 0 = Dg := by
    apply le_antisymm
    · rw [lev, Subgroup.closure_le]
      rintro x ⟨g, -, hg, rfl⟩
      exact hsD g
    · rw [hDg, Subgroup.closure_le]
      have hnpr := hF.npr2
      have e0 : s 0 = d₀ := mat_injective (by
        change 𝕄 (s 0) = 𝕄 d₀
        rw [hsM 0 (by omega), hd₀, DempData.S, hF.pr0])
      have e1 : s 1 = d₁ := mat_injective (by
        change 𝕄 (s 1) = 𝕄 d₁
        rw [hsM 1 (by omega), hd₁, DempData.S, hF.pr1])
      rintro x (rfl | rfl)
      · rw [← e0]
        exact hsl 0 0 (by rw [hF.fr0]) (by omega)
      · rw [← e1]
        exact hsl 0 1 (by rw [hF.fr0]; omega) (by omega)
  have hcard : Nat.card Dg = 319979520 := by
    rw [← hlev0, hH.card_lev_zero, hF.L6]
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hF.osz
    simp [Finset.prod_range_succ, h0, h1, h2, h3, h4, h5]
  have hL6 := hF.L6
  obtain ⟨o0, o1, o2, o3, o4, o5⟩ := hF.osz
  have hmemD : ∀ l < 6, ∀ i < D.oszL l, t l i ∈ Dg := by
    intro l hl i hi
    rw [← hlev0]
    exact hlev_le 0 l (by omega) (by omega) (htree l (by omega) i hi).1
  have hprodD : ∀ y : Coords, chainProd t y ∈ Dg := by
    intro y
    unfold chainProd
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ (hmemD 5 (by omega) _ (by rw [o5]; exact y.2.2.2.2.2.isLt))
        (hmemD 4 (by omega) _ (by rw [o4]; exact y.2.2.2.2.1.isLt)))
      (hmemD 3 (by omega) _ (by rw [o3]; exact y.2.2.2.1.isLt)))
      (hmemD 2 (by omega) _ (by rw [o2]; exact y.2.2.1.isLt)))
      (hmemD 1 (by omega) _ (by rw [o1]; exact y.2.1.isLt)))
      (hmemD 0 (by omega) _ (by rw [o0]; exact y.1.isLt))
  have hsurj : ∀ x ∈ Dg, ∃ y : Coords, chainProd t y = x := by
    intro x hx
    rw [← hlev0] at hx
    obtain ⟨h1, hh1, z0, hz0, rfl⟩ := hH.decomp (by omega) hx
    obtain ⟨h2, hh2, z1, hz1, rfl⟩ := hH.decomp (by omega) hh1
    obtain ⟨h3, hh3, z2, hz2, rfl⟩ := hH.decomp (by omega) hh2
    obtain ⟨h4, hh4, z3, hz3, rfl⟩ := hH.decomp (by omega) hh3
    obtain ⟨h5, hh5, z4, hz4, rfl⟩ := hH.decomp (by omega) hh4
    obtain ⟨h6, hh6, z5, hz5, rfl⟩ := hH.decomp (by omega) hh5
    have e6 : h6 = 1 := by
      have := hH.lev_L
      rw [hL6] at this
      rw [this] at hh6
      exact (Subgroup.mem_bot.mp hh6)
    subst e6
    refine ⟨(⟨z0, by rw [← o0]; exact hz0⟩, ⟨z1, by rw [← o1]; exact hz1⟩, ⟨z2, by rw [← o2]; exact hz2⟩,
      ⟨z3, by rw [← o3]; exact hz3⟩, ⟨z4, by rw [← o4]; exact hz4⟩, ⟨z5, by rw [← o5]; exact hz5⟩), ?_⟩
    simp only [chainProd, one_mul]
  let φ : Coords → Dg := fun y => ⟨chainProd t y, hprodD y⟩
  have hφs : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨y, hy⟩ := hsurj x hx
    exact ⟨y, Subtype.ext hy⟩
  have hφi : Function.Injective φ := by
    have : Finite Dg := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
    have : Fintype Dg := Fintype.ofFinite Dg
    have hc : Fintype.card Coords = Fintype.card Dg := by
      rw [← Nat.card_eq_fintype_card (α := Dg), hcard]
      simp [Coords]
    exact ((Fintype.bijective_iff_surjective_and_card φ).mpr ⟨hφs, hc⟩).1
  have hlevfix : ∀ l ≤ 5, ∀ x ∈ Dg, (∀ k < l, act (pkVec (D.bvL k)) x = pkVec (D.bvL k)) →
      x ∈ lev D.frL D.npr s l := by
    intro l
    induction l with
    | zero =>
      intro _ x hx _
      rw [hlev0]
      exact hx
    | succ l ih =>
      intro hl x hx hfx
      obtain ⟨h, hh, z, hz, rfl⟩ := hH.decomp (by omega) (ih (by omega) _ hx
        (fun k hk => hfx k (by omega)))
      have e1 := hH.act_ht (by omega) hh hz
      rw [hfx l (by omega), ← hH.O0 l (by omega)] at e1
      have hz0 : z = 0 := hH.inj l (by omega) z 0 hz (hpos l (by omega)) e1.symm
      subst hz0
      rw [ht0 l (by omega), mul_one]
      exact hh
  refine ⟨d₀, d₁, hd₀, hd₁, t, fun l hl i hi => ⟨hmemD l hl i hi, htM l i (by omega) hi⟩, ?_, hcard,
    ?_⟩
  · intro x hx
    obtain ⟨y, hy⟩ := hsurj x hx
    refine ⟨y, hy, fun y' hy' => hφi (Subtype.ext ?_)⟩
    change chainProd t y' = chainProd t y
    rw [hy, hy']
  · intro x hx hfx
    obtain ⟨h, hh, z, hz, rfl⟩ := hH.decomp (by omega) (hlevfix 5 le_rfl x hx hfx)
    have e6 : h = 1 := by
      have := hH.lev_L
      rw [hL6] at this
      rw [this] at hh
      exact (Subgroup.mem_bot.mp hh)
    subst e6
    exact ⟨z, by rw [← o5]; exact hz, one_mul _⟩

end CFSG.Certificates.ThDemp

end
