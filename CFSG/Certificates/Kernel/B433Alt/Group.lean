module

public import CFSG.YGroups.DCE.B433Rules

public section

namespace CFSG.KC.B433Alt

open CFSG.YGroups CFSG.YGroups.DCE.B433 CFSG.Certificates.CosetEnumeration

@[expose] def swapL : ℕ → ℕ
  | 5 => 8
  | 6 => 9
  | 7 => 10
  | 8 => 5
  | 9 => 6
  | 10 => 7
  | c => c

theorem swapL_swapL (c : ℕ) : swapL (swapL c) = c := by
  match c with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 => rfl
  | c + 11 => rfl

theorem swapL_lt11 : ∀ c < 11, swapL c < 11 := by decide

theorem swapL_lt10 : ∀ c < 10, c ≠ 7 → swapL c < 10 := by decide

@[expose] def swSpider : List ℕ := (List.replicate 10 [0, 1, 2, 0, 8, 9, 0, 5, 6]).flatten

theorem swapL_rels : ∀ w ∈ yRels 4 3 3, w.map swapL ∈ yRels 4 3 3 ∨
    (w.map swapL).reverse ∈ yRels 4 3 3 ∨ w.map swapL = swSpider := by
  decide

theorem swSpider_lt : ∀ c ∈ swSpider, c < 10 := by decide

theorem evalWord_reverse {G : Type*} [Group G] {g : ℕ → G} (hg : ∀ c, g c * g c = 1)
    (w : List ℕ) : evalWord g w.reverse = (evalWord g w)⁻¹ := by
  induction w with
  | nil => simp [evalWord]
  | cons c w ih =>
    rw [List.reverse_cons, evalWord, List.map_append, List.prod_append, ← evalWord, ih,
      evalWord_cons, mul_inv_rev]
    simp [inv_eq_of_mul_eq_one_right (hg c)]

@[expose] def T432 : Subgroup (YGroup 4 3 2) :=
  Subgroup.closure (yGen 4 3 2 '' {c | c < 10 ∧ c ≠ 7})

theorem evalWord_comp {G : Type*} [Group G] (g : ℕ → G) (f : ℕ → ℕ) (w : List ℕ) :
    evalWord (fun c => g (f c)) w = evalWord g (w.map f) := by
  induction w with
  | nil => rfl
  | cons c w ih => rw [evalWord_cons, List.map_cons, evalWord_cons, ih]

theorem evalWord_map_hom {G K : Type*} [Group G] [Group K] (f : G →* K) (g : ℕ → G)
    (w : List ℕ) : f (evalWord g w) = evalWord (fun c => f (g c)) w := by
  induction w with
  | nil => simp
  | cons c w ih => rw [evalWord_cons, map_mul, ih, evalWord_cons]

@[expose] noncomputable def swGen (c : ℕ) : B433 := qB (yGen 4 3 3 (swapL c))

section
variable (hsw : psi (evalWord (yGen 4 3 2) swSpider) = 1)
include hsw

theorem swGen_rels : ∀ w ∈ yRels 4 3 3, evalWord swGen w = 1 := by
  intro w hw
  have h1 : evalWord swGen w = qB (evalWord (yGen 4 3 3) (w.map swapL)) := by
    rw [← evalWord_comp, evalWord_map_hom]
    rfl
  rw [h1]
  rcases swapL_rels w hw with h | h | h
  · rw [evalWord_yGen_of_mem h, map_one]
  · rw [← List.reverse_reverse (w.map swapL), evalWord_reverse (yGen_mul_self 4 3 3),
      evalWord_yGen_of_mem h, inv_one, map_one]
  · rw [h, ← hsw, psi, MonoidHom.comp_apply, evalWord_map_hom psiU, evalWord_map_hom qB,
      evalWord_map_hom qB]
    refine evalWord_congr fun c hc => ?_
    rw [psiU_yGen (swSpider_lt c hc)]

@[expose] noncomputable def sigmaU : U433 →* B433 :=
  PresentedGroup.toGroup (f := fun c : Fin (ngen 4 3 3) => swGen c) (by
    rintro x ⟨w, hw, rfl⟩
    rw [lift_wordFG, evalWord_congr (g' := swGen)]
    · exact swGen_rels hsw w hw
    · intro c hc
      simp [lt_ngen_of_mem_yRels hw c hc])

theorem sigmaU_yGen {c : ℕ} (hc : c < 11) : sigmaU hsw (yGen 4 3 3 c) = swGen c := by
  rw [yGen_of_lt (by simp only [ngen]; omega), sigmaU, PresentedGroup.toGroup.of]

theorem sigmaU_F213 : sigmaU hsw (F433 2 1 3) = qB (F433 3 1 2) := by
  have h : ∀ c < 11, sigmaU hsw (yGen 4 3 3 c) = qB (yGen 4 3 3 (swapL c)) :=
    fun c hc => sigmaU_yGen hsw hc
  simp only [F433, U433.A, U433.B, U433.C, U433.D, U433.armStart, Nat.reduceAdd, map_pow, map_mul,
    h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 5 (by norm_num),
    h 6 (by norm_num), h 7 (by norm_num), h 8 (by norm_num)]
  rfl

theorem sigmaU_F312 : sigmaU hsw (F433 3 1 2) = qB (F433 2 1 3) := by
  have h : ∀ c < 11, sigmaU hsw (yGen 4 3 3 c) = qB (yGen 4 3 3 (swapL c)) :=
    fun c hc => sigmaU_yGen hsw hc
  simp only [F433, U433.A, U433.B, U433.C, U433.D, U433.armStart, Nat.reduceAdd, map_pow, map_mul,
    h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 5 (by norm_num),
    h 8 (by norm_num), h 9 (by norm_num), h 10 (by norm_num)]
  rfl

@[expose] noncomputable def sigmaHom : B433 →* B433 :=
  QuotientGroup.lift _ (sigmaU hsw) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro x (rfl | rfl)
    · exact (sigmaU_F213 hsw).trans qB_F433_312
    · exact (sigmaU_F312 hsw).trans qB_F433_213)

theorem sigmaHom_qB (x : U433) : sigmaHom hsw (qB x) = sigmaU hsw x := rfl

theorem sigmaHom_letter {c : ℕ} (hc : c < 11) :
    sigmaHom hsw (qB (yGen 4 3 3 c)) = qB (yGen 4 3 3 (swapL c)) := by
  rw [sigmaHom_qB, sigmaU_yGen hsw hc, swGen]

theorem sigmaHom_sigmaHom (b : B433) : sigmaHom hsw (sigmaHom hsw b) = b := by
  obtain ⟨x, rfl⟩ := qB_surjective b
  have h : (sigmaHom hsw).comp ((sigmaHom hsw).comp qB) = qB := by
    refine PresentedGroup.ext fun c => ?_
    have hc : (c : ℕ) < 11 := c.2
    have hs : swapL c < 11 := swapL_lt11 c hc
    change sigmaHom hsw (sigmaHom hsw (qB (PresentedGroup.of c))) = qB (PresentedGroup.of c)
    rw [← yGen_of_lt c.2, sigmaHom_letter hsw hc, sigmaHom_letter hsw hs, swapL_swapL]
  exact DFunLike.congr_fun h x

@[expose] noncomputable def sigma : MulAut B433 :=
  MulEquiv.mk' (Function.Involutive.toPerm _ (sigmaHom_sigmaHom hsw)) (map_mul (sigmaHom hsw))

theorem sigma_apply (b : B433) : sigma hsw b = sigmaHom hsw b := rfl

theorem sigma_mul_self : sigma hsw * sigma hsw = 1 := by
  ext b
  exact sigmaHom_sigmaHom hsw b

theorem sigma_psi {c : ℕ} (hc : c < 10) (h7 : c ≠ 7) :
    sigma hsw (psi (yGen 4 3 2 c)) = psi (yGen 4 3 2 (swapL c)) := by
  have hs : swapL c < 10 := swapL_lt10 c hc h7
  rw [sigma_apply, psi_yGen hc, sigmaHom_letter hsw (by omega), psi_yGen hs]

theorem sigma_psi7 : sigma hsw (psi (yGen 4 3 2 7)) = tB := by
  rw [sigma_apply, psi_yGen (by norm_num), sigmaHom_letter hsw (by norm_num)]
  rfl

@[expose] noncomputable def act : Multiplicative (ZMod 2) →* MulAut B433 where
  toFun z := if Multiplicative.toAdd z = 0 then 1 else sigma hsw
  map_one' := by simp
  map_mul' a b := by
    have key : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    have h2 : (1 : ZMod 2) + 1 = 0 := by decide
    rcases key (Multiplicative.toAdd a) with ha | ha <;>
      rcases key (Multiplicative.toAdd b) with hb | hb <;>
      simp [ha, hb, h2, sigma_mul_self hsw]

abbrev Ghat : Type := B433 ⋊[act hsw] Multiplicative (ZMod 2)

@[expose] noncomputable def u : Ghat hsw := SemidirectProduct.inr (Multiplicative.ofAdd 1)

@[expose] noncomputable def psiG : YGroup 4 3 2 →* Ghat hsw := SemidirectProduct.inl.comp psi

theorem u_mul_self : u hsw * u hsw = 1 := by
  rw [u, ← map_mul, ← ofAdd_add]
  have : (1 + 1 : ZMod 2) = 0 := by decide
  rw [this, ofAdd_zero, map_one]

theorem u_inv : (u hsw)⁻¹ = u hsw := inv_eq_of_mul_eq_one_right (u_mul_self hsw)

theorem u_conj_inl (b : B433) :
    u hsw * SemidirectProduct.inl b * u hsw = SemidirectProduct.inl (sigma hsw b) := by
  have h := SemidirectProduct.inl_aut (φ := act hsw) (Multiplicative.ofAdd 1) b
  have h1 : act hsw (Multiplicative.ofAdd 1) = sigma hsw := by
    simp [act]
  rw [h1, map_inv] at h
  rw [h]
  change u hsw * _ * u hsw = u hsw * _ * (u hsw)⁻¹
  rw [u_inv]

theorem u_conj {c : ℕ} (hc : c < 10) (h7 : c ≠ 7) :
    u hsw * psiG hsw (yGen 4 3 2 c) * u hsw = psiG hsw (yGen 4 3 2 (swapL c)) := by
  rw [psiG, MonoidHom.comp_apply, u_conj_inl, sigma_psi hsw hc h7, MonoidHom.comp_apply]

theorem rel47 : (psiG hsw (yGen 4 3 2 7) * u hsw) ^ 4 = 1 := by
  have ht : u hsw * psiG hsw (yGen 4 3 2 7) * u hsw = SemidirectProduct.inl tB := by
    rw [psiG, MonoidHom.comp_apply, u_conj_inl, sigma_psi7]
  have hc : Commute (yGen 4 3 3 7) (yGen 4 3 3 10) := yGen_commute_D3 (by norm_num)
  have hc' : psiG hsw (yGen 4 3 2 7) * SemidirectProduct.inl tB =
      SemidirectProduct.inl tB * psiG hsw (yGen 4 3 2 7) := by
    rw [psiG, MonoidHom.comp_apply, ← map_mul, ← map_mul, psi_yGen (by norm_num), tB, ← map_mul,
      ← map_mul, hc.eq]
  have h7sq : psiG hsw (yGen 4 3 2 7) * psiG hsw (yGen 4 3 2 7) = 1 := by
    rw [← map_mul, yGen_mul_self, map_one]
  have htsq : (SemidirectProduct.inl tB : Ghat hsw) * SemidirectProduct.inl tB = 1 := by
    rw [← map_mul, tB_mul_self, map_one]
  calc (psiG hsw (yGen 4 3 2 7) * u hsw) ^ 4
      = psiG hsw (yGen 4 3 2 7) * (u hsw * psiG hsw (yGen 4 3 2 7) * u hsw) *
          psiG hsw (yGen 4 3 2 7) * (u hsw * psiG hsw (yGen 4 3 2 7) * u hsw) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = psiG hsw (yGen 4 3 2 7) * (SemidirectProduct.inl tB * psiG hsw (yGen 4 3 2 7)) *
          SemidirectProduct.inl tB := by rw [ht]; group
    _ = psiG hsw (yGen 4 3 2 7) * (psiG hsw (yGen 4 3 2 7) * SemidirectProduct.inl tB) *
          SemidirectProduct.inl tB := by rw [hc']
    _ = (psiG hsw (yGen 4 3 2 7) * psiG hsw (yGen 4 3 2 7)) *
          (SemidirectProduct.inl tB * SemidirectProduct.inl tB) := by group
    _ = 1 := by rw [h7sq, htsq, one_mul]

@[expose] noncomputable def Hh : Subgroup (Ghat hsw) := (psiG hsw).range

@[expose] noncomputable def Th : Subgroup (Ghat hsw) := T432.map (psiG hsw)

theorem closure_Hh_u : Subgroup.closure ((Hh hsw : Set (Ghat hsw)) ∪ {u hsw}) = ⊤ := by
  set K := Subgroup.closure ((Hh hsw : Set (Ghat hsw)) ∪ {u hsw})
  have hH : ∀ y, psiG hsw y ∈ K := fun y => Subgroup.subset_closure (Or.inl ⟨y, rfl⟩)
  have hu : u hsw ∈ K := Subgroup.subset_closure (Or.inr rfl)
  have hinl : ∀ b : B433, (SemidirectProduct.inl b : Ghat hsw) ∈ K := by
    intro b
    have hb : b ∈ Subgroup.closure ((psi.range : Set B433) ∪ {tB}) := by
      rw [closure_psi_t]
      exact Subgroup.mem_top b
    induction hb using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with ⟨y, rfl⟩ | hx
      · exact hH y
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        rw [← sigma_psi7 hsw, ← u_conj_inl]
        exact K.mul_mem (K.mul_mem hu (hH _)) hu
    | one => rw [map_one]; exact K.one_mem
    | mul x y _ _ hx hy => rw [map_mul]; exact K.mul_mem hx hy
    | inv x _ hx => rw [map_inv]; exact K.inv_mem hx
  have hinr : ∀ z : Multiplicative (ZMod 2), (SemidirectProduct.inr z : Ghat hsw) ∈ K := by
    intro z
    have key : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    rcases key (Multiplicative.toAdd z) with h | h
    · have : z = 1 := h
      rw [this, map_one]
      exact K.one_mem
    · have : z = Multiplicative.ofAdd 1 := h
      rw [this]
      exact hu
  rw [eq_top_iff]
  intro g _
  rw [← SemidirectProduct.inl_left_mul_inr_right g]
  exact K.mul_mem (hinl _) (hinr _)

theorem u_conj_Th : ∀ c ∈ Th hsw, (u hsw)⁻¹ * c * u hsw ∈ Hh hsw := by
  rintro _ ⟨y, hy, rfl⟩
  rw [u_inv]
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, ⟨hc, h7⟩, rfl⟩ := hx
    rw [u_conj hsw hc h7]
    exact ⟨_, rfl⟩
  | one => rw [map_one, mul_one, u_mul_self]; exact (Hh hsw).one_mem
  | mul x y _ _ hx hy =>
    have e : u hsw * psiG hsw (x * y) * u hsw =
        (u hsw * psiG hsw x * u hsw) * (u hsw * psiG hsw y * u hsw) := by
      rw [map_mul]
      calc u hsw * (psiG hsw x * psiG hsw y) * u hsw
          = u hsw * psiG hsw x * 1 * psiG hsw y * u hsw := by group
        _ = _ := by rw [← u_mul_self hsw]; group
    rw [e]
    exact (Hh hsw).mul_mem hx hy
  | inv x _ hx =>
    have e : u hsw * psiG hsw x⁻¹ * u hsw = (u hsw * psiG hsw x * u hsw)⁻¹ := by
      rw [map_inv]
      calc u hsw * (psiG hsw x)⁻¹ * u hsw = (u hsw)⁻¹ * (psiG hsw x)⁻¹ * (u hsw)⁻¹ := by
            rw [u_inv]
        _ = _ := by group
    rw [e]
    exact (Hh hsw).inv_mem hx

theorem card_Ghat : Nat.card (Ghat hsw) = Nat.card B433 * 2 := by
  rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
  congr 1
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem card_Hh : Nat.card (Hh hsw) = Nat.card psi.range := by
  rw [Hh, psiG, MonoidHom.range_comp]
  exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ SemidirectProduct.inl_injective).symm.toEquiv

end

end CFSG.KC.B433Alt

end
