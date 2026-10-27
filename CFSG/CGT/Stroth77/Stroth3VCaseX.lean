module

public import CFSG.CGT.Stroth77.Stroth3VCase
public import CFSG.CGT.Stroth77.Stroth39

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)

theorem four_nsmul_zmod {e : ℕ} (he : e ≤ 2) (z : ZMod (2 ^ e)) : 4 • z = 0 := by
  have h4 : ((4 : ℕ) : ZMod (2 ^ e)) = 0 := (ZMod.natCast_eq_zero_iff 4 (2 ^ e)).mpr
    (by calc 2 ^ e ∣ 2 ^ 2 := pow_dvd_pow 2 he
          _ = 4 := by norm_num)
  rw [nsmul_eq_mul, h4, zero_mul]

theorem four_nsmul_torus_t100_one (x : Torus (StrothTypeIndex.t100 1).k) : 4 • x = 0 := by
  funext i
  fin_cases i <;>
  · simp only [Pi.smul_apply, Pi.zero_apply]
    exact four_nsmul_zmod (by simp [StrothTypeIndex.k, Type100.k]) _

namespace StrothWeakTypeData

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {τ : StrothTypeIndex}
  (dD : StrothWeakTypeData D τ)

theorem crdT_pow {a : G} (ha : a ∈ D) (n : ℕ) : crdT dD.e (a ^ n) = n • crdT dD.e a := by
  induction n with
  | zero => rw [pow_zero, crdT_one, zero_nsmul]
  | succ n ih => rw [pow_succ, crdT_mul dD.e (pow_mem ha n) ha, ih, succ_nsmul]

theorem val_crdT_even_of_pow_four (hk : 3 ≤ τ.k 0) {a : G} (ha : a ∈ D) (h4 : a ^ 4 = 1) :
    (crdT dD.e a 0).val % 2 = 0 := by
  have h := dD.crdT_pow ha 4
  rw [h4, crdT_one] at h
  have h0 := congrFun h 0
  rw [Pi.zero_apply, Pi.smul_apply] at h0
  set z := crdT dD.e a 0
  have hz : ((4 * z.val : ℕ) : ZMod (2 ^ τ.k 0)) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, ← nsmul_eq_mul]
    exact h0.symm
  have hd := (ZMod.natCast_eq_zero_iff _ _).mp hz
  have h8 : 8 ∣ 2 ^ τ.k 0 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ∣ 2 ^ τ.k 0 := pow_dvd_pow 2 hk
  have := dvd_trans h8 hd
  omega

theorem eq_of_inv_mul_mem (hk : 1 ≤ τ.k 0) {x y : G} (hx : x ∈ Subgroup.normalizer (D : Set G))
    (hy : y ∈ Subgroup.normalizer (D : Set G)) {a b : Torus τ.k} (ha : InW a) (hb : InW b)
    (hθx : ∀ v, dD.thetaT hx v = nuMap a v) (hθy : ∀ v, dD.thetaT hy v = nuMap b v)
    (hxy : x⁻¹ * y ∈ D) : a = b := by
  have key : ∀ v, nuMap (b + a) v = nuMap 0 v := fun v => by
    rw [nuMap_zero, ← nuMap_nuMap ha.1, ← hθy, ← dD.thetaT_inv_of_nu hx ha hθx,
      ← dD.thetaT_mul (inv_mem hx) hy]
    exact dD.thetaT_of_mem _ hxy v
  have := nuMap_injective hk key
  rw [add_eq_zero_iff_eq_neg] at this
  rw [this, neg_eq_of_add_eq_zero_left ha.2]

theorem conj_eq_iff_even {g : G} (hg : g ∈ Subgroup.normalizer (D : Set G)) {v : Torus τ.k}
    (hv : InW v) (hv0 : v ≠ 0) (hθ : ∀ x, dD.thetaT hg x = nuMap v x) {d : G} (hd : d ∈ D) :
    g⁻¹ * d * g = d ↔ (crdT dD.e d 0).val % 2 = 0 := by
  have hd' := (Subgroup.mem_normalizer_iff''.mp hg d).mp hd
  rw [← nuMap_eq_self_iff hv.2 hv0, ← hθ, dD.thetaT_crdT hg hd]
  exact ⟨fun h => by rw [h], fun h => crdT_inj dD.e hd' hd h⟩

theorem mul_comm_iff_conj {g x : G} : x * g = g * x ↔ g⁻¹ * x * g = x := by
  constructor
  · intro h; rw [mul_assoc, h, inv_mul_cancel_left]
  · intro h
    calc x * g = g * (g⁻¹ * x * g) := by group
      _ = g * x := by rw [h]

end StrothWeakTypeData

namespace StrothFrame.IsD

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
  {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}

theorem exists_X_of_comm_pair (h : F.IsD D dD) (hτ : VFacts τ)
    (hS : Local.Setting (F.S : Subgroup G) D) {e f : G} (he : e ∈ hS.R) (hf : f ∈ hS.R)
    {w : Torus τ.k} (hw : InW w) (hw0 : w ≠ 0) (hPw : τ.action.φρ w ≠ w) (hef : e * f = f * e)
    (hθe : ∀ x, dD.thetaT (hS.R_le_normalizer he) x = nuMap w x)
    (hθf : ∀ x, dD.thetaT (hS.R_le_normalizer hf) x = nuMap (τ.action.φρ w) x) :
    ∃ X : Subgroup G, IsMulCommutative X ∧ F.A ≤ X ∧ X ≤ (F.S : Subgroup G) ∧
      F.dA.L ≤ Subgroup.normalizer ((X ⊔ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) ∧
      Nat.card D < Nat.card X := by
  classical
  have hk := hτ.one_le
  set w' := τ.action.φρ w with hw'def
  have hw' : InW w' := hτ.inW_ρ hw
  have hw'0 : w' ≠ 0 := fun h0 => hw0 (by
    have := DFunLike.congr_fun τ.action.rels.rho_cube w
    change τ.action.φρ (τ.action.φρ (τ.action.φρ w)) = w at this
    rw [← hw'def, h0, map_zero, map_zero] at this
    exact this.symm)
  have heN := hS.R_le_normalizer he
  have hfN := hS.R_le_normalizer hf
  have hDcomm : ∀ {x y : G}, x ∈ D → y ∈ D → x * y = y * x := fun hx hy =>
    congrArg Subtype.val (dD.isMulCommutative.is_comm.comm (⟨_, hx⟩ : D) ⟨_, hy⟩)
  set D₀ : Subgroup G := D ⊓ Subgroup.centralizer ({e} : Set G) with hD₀
  have hD₀D : D₀ ≤ D := inf_le_left
  have hmemD₀ : ∀ {d : G}, d ∈ D → (d ∈ D₀ ↔ (crdT dD.e d 0).val % 2 = 0) := fun {d} hd => by
    rw [hD₀, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq, hd, true_and]
    rw [eq_comm, StrothWeakTypeData.mul_comm_iff_conj]
    exact dD.conj_eq_iff_even heN hw hw0 hθe hd
  have hD₀f : ∀ {d : G}, d ∈ D₀ → d * f = f * d := fun {d} hd => by
    rw [StrothWeakTypeData.mul_comm_iff_conj]
    exact (dD.conj_eq_iff_even hfN hw' hw'0 hθf (hD₀D hd)).mpr ((hmemD₀ (hD₀D hd)).mp hd)
  have hD₀e : ∀ {d : G}, d ∈ D₀ → d * e = e * d := fun {d} hd =>
    ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hd).2) e rfl).symm
  set X : Subgroup G := Subgroup.closure ((D₀ : Set G) ∪ {e, f}) with hX
  have heX : e ∈ X := Subgroup.subset_closure (Or.inr (Or.inl rfl))
  have hfX : f ∈ X := Subgroup.subset_closure (Or.inr (Or.inr rfl))
  have hD₀X : D₀ ≤ X := fun d hd => Subgroup.subset_closure (Or.inl hd)
  have hXR : X ≤ hS.R := by
    rw [hX, Subgroup.closure_le]
    rintro x (hx | hx | hx)
    · exact hS.D_le_R (hD₀D hx)
    · rw [hx]; exact he
    · rw [Set.mem_singleton_iff.mp hx]; exact hf
  have hXcomm : IsMulCommutative X := by
    rw [hX]
    refine Subgroup.isMulCommutative_closure ?_
    rintro x (hx | hx | hx) y (hy | hy | hy) -
    · exact hDcomm (hD₀D hx) (hD₀D hy)
    · rw [hy]; exact hD₀e hx
    · rw [Set.mem_singleton_iff.mp hy]; exact hD₀f hx
    · rw [hx]; exact (hD₀e hy).symm
    · rw [hx, hy]
    · rw [hx, Set.mem_singleton_iff.mp hy]; exact hef
    · rw [Set.mem_singleton_iff.mp hx]; exact (hD₀f hy).symm
    · rw [Set.mem_singleton_iff.mp hx, hy]; exact hef.symm
    · rw [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff.mp hy]
  have hAD₀ : F.A ≤ D₀ := by
    have hk2 := hτ.two_le
    obtain ⟨hv2, -, hvρ, -⟩ := h.crd_x1
    have hv : InW (crdT dD.e (((F.dA.a : F.A) : G) ^ 2)) := ⟨hτ.sq_W _ hv2 hvρ, hv2⟩
    have hevD : ∀ {g : G}, g ∈ D → (crdT dD.e (g * g)) 0 = 0 →
        (crdT dD.e g 0).val % 2 = 0 := fun {g} hg h0 => by
      rw [crdT_mul dD.e hg hg, Pi.add_apply] at h0
      exact val_mod_two_eq_zero_of_add_self hk2 h0
    have haD := h.A_le F.dA.a.2
    have hbD := h.A_le F.dA.b.2
    have hcD := h.A_le F.dA.c.2
    have ha : ((F.dA.a : F.A) : G) ∈ D₀ :=
      (hmemD₀ haD).mpr (hevD haD (by rw [← pow_two]; exact hv.1))
    have hb : ((F.dA.b : F.A) : G) ∈ D₀ := by
      refine (hmemD₀ hbD).mpr (hevD hbD ?_)
      have hx₁ : ((F.dA.a : F.A) : G) ^ 2 = F.dA.ofTorus (2 • Torus.a) := by
        rw [F.dA.ofTorus_nsmul]; rfl
      have hy₁ : ((F.dA.b : F.A) : G) ^ 2 = F.dA.ofTorus (2 • Torus.b) := by
        rw [F.dA.ofTorus_nsmul]; rfl
      have hρx : F.dA.ρ⁻¹ * ((F.dA.a : F.A) : G) ^ 2 * F.dA.ρ = ((F.dA.b : F.A) : G) ^ 2 := by
        rw [hx₁, hy₁, F.dA.conj_ofTorus F.dA.ρ_mem F.dA.ρ_conj]
        congr 1
        decide
      have cρ := crdT_conj dD.e dD.ρ_mem dD.ρ_conj (h.A_le (F.A.pow_mem F.dA.a.2 2))
      rw [h.ρ_eq, hρx] at cρ
      rw [← pow_two, cρ]
      exact hτ.W_ρ _ hv
    have hc : ((F.dA.c : F.A) : G) ∈ D₀ := by
      refine (hmemD₀ hcD).mpr (hevD hcD ?_)
      have hcc : ((F.dA.c : F.A) : G) * ((F.dA.c : F.A) : G) = 1 := by
        rw [show ((F.dA.c : F.A) : G) = F.dA.ofTorus Torus.c from rfl, ← F.dA.ofTorus_add,
          show (Torus.c + Torus.c : Torus (StrothTypeIndex.t100 1).k) = 0 by decide,
          F.dA.ofTorus_zero]
      rw [hcc, crdT_one]
      rfl
    intro a haA
    obtain ⟨i, j, l, hx⟩ := torus_eq_zsmul_gens _ (crdT F.dA.e a)
    have hdec : a = ((F.dA.c : F.A) : G) ^ i * ((F.dA.a : F.A) : G) ^ j *
        ((F.dA.b : F.A) : G) ^ l := by
      conv_lhs => rw [← F.dA.ofT_crdT haA, hx, F.dA.ofT_add, F.dA.ofT_add, F.dA.ofT_zsmul,
        F.dA.ofT_zsmul, F.dA.ofT_zsmul]
      rfl
    rw [hdec]
    exact mul_mem (mul_mem (zpow_mem hc i) (zpow_mem ha j)) (zpow_mem hb l)
  have hθ1 : ∀ x, dD.thetaT (hS.R_le_normalizer (one_mem hS.R)) x = nuMap 0 x := fun x => by
    rw [nuMap_zero]; exact dD.thetaT_of_mem _ (one_mem D) x
  have hθef : ∀ x, dD.thetaT (hS.R_le_normalizer (mul_mem he hf)) x = nuMap (w + w') x :=
    fun x => by
      rw [dD.thetaT_congr _ (mul_mem heN hfN) rfl, dD.thetaT_mul heN hfN, hθe, hθf,
        nuMap_nuMap hw.1, add_comm]
  have hW0 : InW (0 : Torus τ.k) := ⟨rfl, add_zero 0⟩
  have hWww : InW (w + w') := ⟨by rw [Pi.add_apply, hw.1, hw'.1, add_zero],
    by rw [add_add_add_comm, hw.2, hw'.2, add_zero]⟩
  have hne1 : w + w' ≠ 0 := fun h0 =>
    hPw ((eq_neg_of_add_eq_zero_right h0).trans (neg_eq_of_add_eq_zero_left hw.2))
  have hne2 : w + w' ≠ w := fun h0 => hw'0 (by rwa [add_eq_left] at h0)
  have hne3 : w + w' ≠ w' := fun h0 => hw0 (by rwa [add_eq_right] at h0)
  have hidx : (D₀.subgroupOf D).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨dD.ofT (gen τ.k 0), dD.ofT_mem _⟩, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    rw [hmemD₀ (mul_mem b.2 (dD.ofT_mem _)), hmemD₀ b.2, crdT_mul dD.e b.2 (dD.ofT_mem _),
      dD.crdT_ofT, Pi.add_apply, val_add_mod_two hk, gen_zero_val hk]
    rcases Nat.mod_two_eq_zero_or_one (crdT dD.e (b : G) 0).val with h0 | h1
    · simp [Nat.add_mod, h0]
    · simp [Nat.add_mod, h1]
  have hcardD : Nat.card D = Nat.card D₀ * 2 := by
    rw [← Subgroup.card_mul_index (D₀.subgroupOf D), hidx,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD₀D).toEquiv]
  have hidxX : 4 ≤ (D.subgroupOf X).index := by
    rw [Subgroup.index_eq_card]
    let xs : Fin 4 → X := ![1, ⟨e, heX⟩, ⟨f, hfX⟩, ⟨e * f, mul_mem heX hfX⟩]
    let vs : Fin 4 → Torus τ.k := ![0, w, w', w + w']
    have hvs_inj : Function.Injective vs := by
      intro i j hij
      fin_cases i <;> fin_cases j
      all_goals first
        | rfl
        | (exfalso
           simp only [vs, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero,
             Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
             Matrix.head_cons] at hij
           first
             | exact hw0 hij.symm | exact hw0 hij | exact hw'0 hij.symm | exact hw'0 hij
             | exact hne1 hij.symm | exact hne1 hij | exact hPw hij.symm | exact hPw hij
             | exact hne2 hij.symm | exact hne2 hij | exact hne3 hij.symm | exact hne3 hij)
    have hxsR : ∀ i, ((xs i : X) : G) ∈ hS.R := fun i => hXR (xs i).2
    have hθxs : ∀ i x, dD.thetaT (hS.R_le_normalizer (hxsR i)) x = nuMap (vs i) x := by
      intro i x
      fin_cases i
      · exact hθ1 x
      · exact hθe x
      · exact hθf x
      · exact hθef x
    have hvsW : ∀ i, InW (vs i) := by
      intro i; fin_cases i
      · exact hW0
      · exact hw
      · exact hw'
      · exact hWww
    have hinj : Function.Injective
        (fun i => (QuotientGroup.mk (xs i) : X ⧸ D.subgroupOf X)) := by
      intro i j hij
      have hm := QuotientGroup.eq.mp hij
      rw [Subgroup.mem_subgroupOf] at hm
      push_cast at hm
      have := dD.eq_of_inv_mul_mem hk (hS.R_le_normalizer (hxsR i))
        (hS.R_le_normalizer (hxsR j)) (hvsW i) (hvsW j) (hθxs i) (hθxs j) hm
      exact hvs_inj this
    calc 4 = Nat.card (Fin 4) := by simp
      _ ≤ _ := Nat.card_le_card_of_injective _ hinj
  have hcardX : Nat.card D₀ * 4 ≤ Nat.card X := by
    rw [← Subgroup.card_mul_index (D.subgroupOf X)]
    refine Nat.mul_le_mul ?_ hidxX
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD₀X).toEquiv]
    exact Subgroup.card_le_of_le fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hD₀D (Subgroup.mem_subgroupOf.mp hx))
  have hD₀pos : 0 < Nat.card D₀ := Nat.card_pos
  set H : Subgroup G := X ⊔ Subgroup.centralizer (D : Set G) with hH
  have hDH : D ≤ H := fun d hd =>
    Subgroup.mem_sup_right (Subgroup.mem_centralizer_iff.mpr fun y hy => hDcomm hy hd)
  have hXH : X ≤ H := le_sup_left
  have hnuH : ∀ {y : G} (hy : y ∈ hS.R) {v : Torus τ.k}, InW v →
      (∀ x, dD.thetaT (hS.R_le_normalizer hy) x = nuMap v x) → y ∈ H := by
    intro y hy v hv hθy
    have key : ∀ {z : G} (hz : z ∈ hS.R), z ∈ X →
        (∀ x, dD.thetaT (hS.R_le_normalizer hz) x = nuMap v x) → y ∈ H := by
      intro z hz hzX hθz
      have hyz : y * z⁻¹ ∈ D := by
        apply dD.mem_of_thetaT_id hS (hS.R_le_S (mul_mem hy (inv_mem hz)))
          (hS.R_le_normalizer (mul_mem hy (inv_mem hz)))
        intro x
        rw [dD.thetaT_congr _ (mul_mem (hS.R_le_normalizer hy)
            (inv_mem (hS.R_le_normalizer hz))) rfl,
          dD.thetaT_mul (hS.R_le_normalizer hy) (inv_mem (hS.R_le_normalizer hz)),
          dD.thetaT_inv_of_nu (hS.R_le_normalizer hz) hv hθz, hθy, nuMap_nuMap hv.1, hv.2,
          nuMap_zero]
      rw [show y = (y * z⁻¹) * z by group]
      exact mul_mem (hDH hyz) (hXH hzX)
    rcases hτ.W_orbit w v hw hw0 hv with rfl | rfl | rfl | rfl
    · exact key (one_mem _) (one_mem _) hθ1
    · exact key he heX hθe
    · exact key hf hfX hθf
    · exact key (mul_mem he hf) (mul_mem heX hfX) hθef
  have hgen : ∀ {g : G} (hgN : g ∈ Subgroup.normalizer (D : Set G)),
      (∀ x, ((dD.thetaT hgN x) 0).val % 2 = (x 0).val % 2) →
      (∀ v, InW v → InW (dD.thetaT (inv_mem hgN) v)) →
      g ∈ Subgroup.normalizer (H : Set G) := by
    intro g hgN hpar hW
    have hnu_conj : ∀ {y : G} (hy : y ∈ hS.R) {v : Torus τ.k},
        (∀ x, dD.thetaT (hS.R_le_normalizer hy) x = nuMap v x) → InW v →
        g * y * g⁻¹ ∈ H := by
      intro y hy v hθy hv
      obtain ⟨hp, o, ho, hpo⟩ := hS.proj_spec (inv_mem hgN) hy
      have hθp : ∀ x, dD.thetaT (hS.R_le_normalizer hp) x =
          nuMap (dD.thetaT (inv_mem hgN) v) x := fun x => by
        rw [dD.thetaT_proj hS (inv_mem hgN) hy,
          dD.thetaT_conj (hS.R_le_normalizer hy) (inv_mem hgN),
          dD.thetaT_congr (inv_mem (inv_mem hgN)) hgN (inv_inv g), hθy, nuMap, map_add,
          map_nsmul, dD.thetaT_inv_thetaT hgN, nuMap]
        congr 1
        exact nsmul_eq_of_mod_two (hW v hv).2 (hpar x)
      have hpH := hnuH hp (hW v hv) hθp
      have hoH : o ∈ H := Subgroup.mem_sup_right (hS.O_le_centralizer ho)
      rw [inv_inv] at hpo
      rw [hpo]
      exact mul_mem hpH hoH
    have hcomap : H ≤ H.comap (MulAut.conj g).toMonoidHom := by
      refine sup_le ?_ ?_
      · rw [hX, Subgroup.closure_le]
        rintro x (hx | hx | hx)
        · show g * x * g⁻¹ ∈ H
          exact hDH ((Subgroup.mem_normalizer_iff.mp hgN x).mp (hD₀D hx))
        · rw [hx]
          exact hnu_conj he hθe hw
        · rw [Set.mem_singleton_iff.mp hx]
          exact hnu_conj hf hθf hw'
      · intro c hc
        show g * c * g⁻¹ ∈ H
        apply Subgroup.mem_sup_right
        rw [Subgroup.mem_centralizer_iff] at hc ⊢
        intro y hy
        have hy' : g⁻¹ * y * g ∈ D := (Subgroup.mem_normalizer_iff''.mp hgN y).mp hy
        have hcy := hc _ hy'
        calc y * (g * c * g⁻¹) = g * ((g⁻¹ * y * g) * c) * g⁻¹ := by group
          _ = g * (c * (g⁻¹ * y * g)) * g⁻¹ := by rw [hcy]
          _ = g * c * g⁻¹ * y := by group
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.map_le_iff_le_comap]
      exact hcomap
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hL : F.dA.L ≤ Subgroup.normalizer (H : Set G) := by
    rw [← h.L_eq, StrothWeakTypeData.L, Subgroup.closure_le]
    rintro g (rfl | rfl | rfl | rfl)
    · refine hgen dD.uv_mem (fun x => by rw [dD.thetaT_uv]; exact hτ.par_uv x) fun v hv => ?_
      have hinv := dD.thetaT_inv_thetaT dD.uv_mem v
      rw [dD.thetaT_uv, hτ.W_uv v hv] at hinv
      rw [hinv]
      exact hv
    · refine hgen dD.t_mem (fun x => by rw [dD.thetaT_t]; exact hτ.par_t x) fun v hv => ?_
      have hinv := dD.thetaT_inv_thetaT dD.t_mem v
      rw [dD.thetaT_t, hτ.W_t v hv] at hinv
      rw [hinv]
      exact hv
    · refine hgen dD.u_mem (fun x => by rw [dD.thetaT_u]; exact hτ.par_u x) fun v hv => ?_
      rw [dD.thetaT_congr (inv_mem dD.u_mem) dD.u_mem (inv_eq_of_mul_eq_one_right dD.u_sq),
        dD.thetaT_u]
      exact hτ.inW_u hv
    · refine hgen dD.ρ_mem (fun x => by rw [dD.thetaT_ρ]; exact hτ.par_ρ x) fun v hv => ?_
      rw [dD.thetaT_ρ_inv]
      exact hτ.inW_ρ (hτ.inW_ρ hv)
  refine ⟨X, hXcomm, hAD₀.trans hD₀X, hXR.trans hS.R_le_S, hL, ?_⟩
  rw [hcardD]
  omega

theorem exists_X_of_vcase (h : F.IsD D dD) (hτ : VFacts τ)
    (hns : IsSylowIn 2 (Subgroup.normalizer (D : Set G))
      ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)))
    (hkill : ∀ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
      e⁻¹ * dD.uv * e * dD.uv⁻¹ ∈ D → e⁻¹ * dD.t * e * dD.t⁻¹ ∈ D →
      (∀ d ∈ D, (dD.ρ⁻¹ * e * dD.ρ)⁻¹ * d * (dD.ρ⁻¹ * e * dD.ρ) = e⁻¹ * d * e) → e ∈ D)
    (hlt : D < (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G)) :
    ∃ X : Subgroup G, IsMulCommutative X ∧ F.A ≤ X ∧ X ≤ (F.S : Subgroup G) ∧
      F.dA.L ≤ Subgroup.normalizer ((X ⊔ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) ∧
      Nat.card D < Nat.card X := by
  have hS := h.setting hns
  obtain ⟨e₀, he₀R, he₀D, huv, ht⟩ := h.exists_mem_R_conj_mem hlt
  obtain ⟨e₁, he₁, he₁D, hsq⟩ :=
    hS.exists_sq_mem (x := dD.uv) (y := dD.t) ⟨he₀R, huv, ht⟩ he₀D
  obtain ⟨e, he, f, hf, w, hw, hw0, hPw, hθe, hθf⟩ :=
    dD.exists_nu_pair hτ hS hkill he₁ he₁D hsq
  obtain ⟨e', he', f', hf', hef, hθe', hθf'⟩ :=
    dD.exists_comm_nu_pair hτ hS h.uv_mem_S h.t_mem_S he hf hw hw0 hPw hθe hθf
  exact h.exists_X_of_comm_pair hτ hS he' hf' hw hw0 hPw hef hθe' hθf'

theorem stroth_3_9_t321_of_vFacts (hτ : VFacts StrothTypeIndex.t321)
    {dD : StrothWeakTypeData D StrothTypeIndex.t321} (h : F.IsD D dD)
    (hns : IsSylowIn 2 (Subgroup.normalizer (D : Set G))
      ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G))) :
    (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ∨
      ∃ X : Subgroup G, IsMulCommutative X ∧ F.A ≤ X ∧ X ≤ (F.S : Subgroup G) ∧
        F.dA.L ≤ Subgroup.normalizer
          ((X ⊔ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) ∧
        Nat.card D < Nat.card X :=
  h.stroth_3_9_t321 hns fun ⟨e, he, heD, _⟩ hkill => h.exists_X_of_vcase hτ hns hkill
    (SetLike.lt_iff_le_and_exists.mpr ⟨(h.setting hns).D_le_R, e, he, heD⟩)

theorem stroth_3_9_t331_of_vFacts (hτ : VFacts StrothTypeIndex.t331)
    {dD : StrothWeakTypeData D StrothTypeIndex.t331} (h : F.IsD D dD)
    (hns : IsSylowIn 2 (Subgroup.normalizer (D : Set G))
      ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G))) :
    (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ∨
      ∃ X : Subgroup G, IsMulCommutative X ∧ F.A ≤ X ∧ X ≤ (F.S : Subgroup G) ∧
        F.dA.L ≤ Subgroup.normalizer
          ((X ⊔ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) ∧
        Nat.card D < Nat.card X :=
  h.stroth_3_9_t331 hns fun ⟨e, he, heD, _⟩ hkill => h.exists_X_of_vcase hτ hns hkill
    (SetLike.lt_iff_le_and_exists.mpr ⟨(h.setting hns).D_le_R, e, he, heD⟩)

end StrothFrame.IsD

end CFSG.CGT.Stroth77
