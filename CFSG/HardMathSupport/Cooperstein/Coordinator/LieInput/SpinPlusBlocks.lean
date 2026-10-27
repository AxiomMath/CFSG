module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinPlusMat
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SUEmbed

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

section P134
open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Spin QuadraticMap
  CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg.SpinPlus CFSG.LieType.RootSystem
  CFSG.LieType.Universal.Spin.PlusCT CFSG.LieType.Steinberg.SpinFrame


section RootMat

variable {n : ℕ} {F : Type} [Field F] [CharP F 2]

theorem Smat_injective : Function.Injective (Smat (n := n) (F := F)) := by
  intro x y h
  have h2 : spinMatrix (quadPlus n F) x = spinMatrix (quadPlus n F) y := Units.ext h
  have hk := ker_spinMatrix_quadPlus_eq_bot (n := n) (K := F) CharTwo.two_eq_zero
  have : x⁻¹ * y ∈ (spinMatrix (quadPlus n F)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h2, inv_mul_cancel]
  rw [hk, Subgroup.mem_bot] at this
  exact inv_mul_eq_one.mp this

theorem mem_rootGroup_Dgamma_iff (hn : 3 ≤ n) {x y : Fin n ⊕ Fin n} (hxy : x ≠ y)
    (hyx : y ≠ x.swap) {u : spinGroup (quadPlus n F)} :
    u ∈ (plusDatum n F hn).rootGroup (Dgamma x y) ↔
      ∃ c : F, Smat u = 1 + c • (Matrix.single x y 1 + Matrix.single y.swap x.swap 1) := by
  constructor
  · intro hu
    set i := zi x with hi
    set s := zs x with hs
    set j := zi y with hj
    set t := !(zs y) with ht
    have hx : plusIdx i s = x := plusIdx_zi_zs x
    have hy : plusIdx j (!t) = y := by
      rw [ht, Bool.not_not]; exact plusIdx_zi_zs y
    have hij : i ≠ j := by
      intro h
      have h1 : y = plusIdx i (!t) := by rw [← hy, ← h]
      by_cases hst : (!t) = s
      · exact hxy (by rw [h1, hst, hx])
      · have hb : ∀ a b : Bool, (!a) ≠ b → (!a) = !b := by decide
        have : (!t) = !s := hb t s hst
        exact hyx (by rw [h1, this, ← swap_plusIdx, hx])
    have he : plusWt x - plusWt y = Pi.single i (boolSign s) + Pi.single j (boolSign t) := by
      rw [plusWt_eq, plusWt_eq]
      have e1 : zi y = j := hj.symm
      have e2 : zs y = !t := by rw [ht, Bool.not_not]
      rw [← hi, ← hs, e1, e2, boolSign_not, Pi.single_neg, sub_neg_eq_add]
    have hγ : toStdD n (Dgamma x y) = Pi.single i (boolSign s) + Pi.single j (boolSign t) := by
      rw [toStdD_Dgamma hn, he]
    obtain ⟨c, hc⟩ := (mem_plusRootGroup_iff hn hij s t hγ).mp hu
    refine ⟨c, ?_⟩
    have := coe_spinMatrix_longRoot (isCoordFrame_plusFrame (n := n) (K := F) (hn := hn)) hij s t c
    unfold Smat
    rw [hc]
    rw [this]
    unfold longMat
    have hys : y.swap = plusIdx j t := by rw [← hy, swap_plusIdx, Bool.not_not]
    have hxs : x.swap = plusIdx i (!s) := by rw [← hx, swap_plusIdx]
    rw [hys, hxs, hx, hy, sub_eq_add_neg, Matrix.single_neg, CharTwo.neg_eq]
  · rintro ⟨c, hc⟩
    obtain ⟨u₀, -, hu₀, hS⟩ := exists_rootElt hn hxy hyx c
    have : u = u₀ := Smat_injective (hc.trans hS.symm)
    rw [this]; exact hu₀


theorem matDe_eq_rootMatrix (e : Equiv.Perm (Fin (n + n)))
    (he : ∀ t, e (Fin.rev t) = Fin.rev (e t)) {a b : Fin (n + n)} (hab : a ≠ b)
    (hba : b ≠ Fin.rev a) {u : spinGroup (quadPlus n F)} {c : F}
    (hS : Smat u = 1 + c • (Matrix.single ((posEquiv n).symm (e a)) ((posEquiv n).symm (e b)) 1 +
      Matrix.single ((posEquiv n).symm (e b)).swap ((posEquiv n).symm (e a)).swap 1)) :
    matDe e u = rootMatrix (RingEquiv.refl F) a b c := by
  set Q : Fin (n + n) → Fin n ⊕ Fin n := fun w => (posEquiv n).symm (e w) with hQ
  have hQinj : Function.Injective Q := (posEquiv n).symm.injective.comp e.injective
  have hQs : ∀ w, (Q w).swap = Q (Fin.rev w) := fun w => by
    simp only [hQ, swap_posEquiv_symm, he]
  ext a' b'
  have : matDe e u a' b' = Smat u (Q a') (Q b') := by
    rw [matDe_apply, matD_apply]
  rw [this, hS, hQs, hQs]
  simp only [rootMatrix, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.single_apply, hQinj.eq_iff, RingEquiv.refl_apply, smul_eq_mul]
  have hrb : Fin.rev b ≠ a := fun h => hba (by rw [← h, Fin.rev_rev])
  have hn2 : ∀ x : F, -x = x := fun x => CharTwo.neg_eq x
  split_ifs <;> simp_all [sub_eq_add_neg, hn2] <;> ring

end RootMat


section Gamma2b
variable {n : ℕ}

theorem matD_one_eq {F : Type} [Field F] (g : spinGroup (quadPlus n F)) (a b : Fin (n + n)) :
    matDe (1 : Equiv.Perm (Fin (n + n))) g a b = matD n F g a b := by
  simp [matDe_apply]

theorem matDe_one' {F : Type} [Field F] (g : spinGroup (quadPlus n F)) :
    matDe (1 : Equiv.Perm (Fin (n + n))) g = matD n F g := by
  ext a b
  exact matD_one_eq g a b

end Gamma2b

section RootLemmas

variable {n : ℕ} {F : Type} [Field F] [CharP F 2]

theorem exists_pair_of_toStdD (hn : 3 ≤ n) {γ : Fin n → ℤ} {i j : Fin n} (hij : i ≠ j) (s t : Bool)
    (hγ : toStdD n γ = Pi.single i (boolSign s) + Pi.single j (boolSign t)) :
    ∃ x y : Fin n ⊕ Fin n, x ≠ y ∧ y ≠ x.swap ∧ Dgamma x y = γ := by
  refine ⟨plusIdx i s, plusIdx j (!t), ?_, ?_, ?_⟩
  · intro h
    apply hij
    have := congrArg zi h
    simpa [plusIdx, zi] using (by cases s <;> cases t <;> simpa [plusIdx, zi] using this : i = j)
  · intro h
    apply hij
    have := congrArg zi h
    rw [zi_swap] at this
    cases s <;> cases t <;> simpa [plusIdx, zi] using this.symm
  · apply toStdD_injective n
    rw [toStdD_Dgamma hn, hγ, plusWt_plusIdx, plusWt_plusIdx, boolSign_not, Pi.single_neg,
      sub_neg_eq_add]

theorem exists_Dgamma_of_root (hn : 3 ≤ n) {γ : Fin n → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanD n) ∅) :
    ∃ x y : Fin n ⊕ Fin n, x ≠ y ∧ y ≠ x.swap ∧ Dgamma x y = γ := by
  obtain ⟨i, j, hij, s, t, h⟩ := exists_toStdD_eq_of_mem_rootsD (by omega) hγ
  exact exists_pair_of_toStdD hn hij s t h

theorem rootMat_of_mem (hn : 3 ≤ n) {x y : Fin n ⊕ Fin n} (hxy : x ≠ y) (hyx : y ≠ x.swap)
    {t : spinGroup (quadPlus n F)} (ht : t ∈ (plusDatum n F hn).rootGroup (Dgamma x y)) :
    ∃ c : F, matD n F t = rootMatrix (RingEquiv.refl F) (posEquiv n x) (posEquiv n y) c := by
  obtain ⟨c, hc⟩ := (mem_rootGroup_Dgamma_iff hn hxy hyx).mp ht
  refine ⟨c, ?_⟩
  rw [← matDe_one']
  refine matDe_eq_rootMatrix 1 (fun _ => rfl) (fun h => hxy ((posEquiv n).injective h)) ?_ ?_
  · intro h
    apply hyx
    apply (posEquiv n).injective
    rw [posEquiv_swap]; exact h
  · simpa using hc

theorem exists_rootMat (hn : 3 ≤ n) {x y : Fin n ⊕ Fin n} (hxy : x ≠ y) (hyx : y ≠ x.swap) (c : F) :
    ∃ t : spinGroup (quadPlus n F), Dgamma x y ∈ (plusDatum n F hn).roots ∧
      t ∈ (plusDatum n F hn).rootGroup (Dgamma x y) ∧
      matD n F t = rootMatrix (RingEquiv.refl F) (posEquiv n x) (posEquiv n y) c := by
  obtain ⟨t, hr, ht, hS⟩ := exists_rootElt hn hxy hyx c
  refine ⟨t, hr, ht, ?_⟩
  rw [← matDe_one']
  refine matDe_eq_rootMatrix 1 (fun _ => rfl) (fun h => hxy ((posEquiv n).injective h)) ?_ ?_
  · intro h
    apply hyx
    apply (posEquiv n).injective
    rw [posEquiv_swap]; exact h
  · simpa using hS

end RootLemmas


end P134

section P135
open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Spin QuadraticMap
  CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg.SpinPlus CFSG.LieType.RootSystem
  CFSG.LieType.Universal.Spin.PlusCT CFSG.LieType.Steinberg.SpinFrame
  CFSG.AGLEmbeddingD2.ParabLevi CFSG.LieType.BorelTits


section Lift

variable {n : ℕ} {F : Type} [Field F] [CharP F 2] (hn : 3 ≤ n)
  {X : Type} [Group X] (μ : X →* Matrix (Fin (n + n)) (Fin (n + n)) F) (J : Set (Fin (plusDatum n F hn).rank))
  (E1 : ∀ x, ∃ t ∈ leviM (plusDatum n F hn) J, matD n F t = μ x)

@[expose] noncomputable def liftFun (x : X) : spinGroup (quadPlus n F) := Classical.choose (E1 x)

theorem liftFun_mem (x : X) : liftFun hn μ J E1 x ∈ leviM (plusDatum n F hn) J :=
  (Classical.choose_spec (E1 x)).1

theorem matD_liftFun (x : X) : matD n F (liftFun hn μ J E1 x) = μ x :=
  (Classical.choose_spec (E1 x)).2

theorem liftFun_eq (x : X) (t : spinGroup (quadPlus n F)) (ht : matD n F t = μ x) :
    liftFun hn μ J E1 x = t :=
  matD_injective (CharTwo.two_eq_zero) ((matD_liftFun hn μ J E1 x).trans ht.symm)

@[expose] noncomputable def liftHom : X →* ↥(leviM (plusDatum n F hn) J) where
  toFun x := ⟨liftFun hn μ J E1 x, liftFun_mem hn μ J E1 x⟩
  map_one' := Subtype.ext (liftFun_eq hn μ J E1 1 1 (by rw [map_one, map_one]))
  map_mul' x y := Subtype.ext (liftFun_eq hn μ J E1 (x * y) (liftFun hn μ J E1 x * liftFun hn μ J E1 y) (by
    rw [map_mul, map_mul, matD_liftFun, matD_liftFun]))

theorem matD_liftHom (x : X) : matD n F (liftHom hn μ J E1 x : spinGroup (quadPlus n F)) = μ x :=
  matD_liftFun hn μ J E1 x

theorem liftHom_injective (hμ : Function.Injective μ) : Function.Injective (liftHom hn μ J E1) := by
  intro x y h
  apply hμ
  rw [← matD_liftHom hn μ J E1 x, ← matD_liftHom hn μ J E1 y, h]

theorem liftHom_surjective
    (E2 : ∀ i ∈ J, ∀ t ∈ CFSG.LieType.CurtisTits.rankOne (plusDatum n F hn).rootGroup i, ∃ x, μ x = matD n F t) :
    Function.Surjective (liftHom hn μ J E1) := by
  have hle : leviM (plusDatum n F hn) J ≤ (liftHom hn μ J E1).range.map
      (leviM (plusDatum n F hn) J).subtype := by
    refine iSup₂_le fun i hi t ht => ?_
    obtain ⟨x, hx⟩ := E2 i hi t ht
    have htm : t ∈ leviM (plusDatum n F hn) J := rankOne_le_leviM hi ht
    refine ⟨liftHom hn μ J E1 x, ⟨x, rfl⟩, ?_⟩
    apply matD_injective (CharTwo.two_eq_zero)
    show matD n F (liftHom hn μ J E1 x : spinGroup (quadPlus n F)) = matD n F t
    rw [matD_liftHom, hx]
  intro t
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := hle t.2
  exact ⟨x, Subtype.ext hx⟩

@[expose] noncomputable def liftEquiv (hμ : Function.Injective μ)
    (E2 : ∀ i ∈ J, ∀ t ∈ CFSG.LieType.CurtisTits.rankOne (plusDatum n F hn).rootGroup i, ∃ x, μ x = matD n F t) :
    X ≃* ↥(leviM (plusDatum n F hn) J) :=
  MulEquiv.ofBijective (liftHom hn μ J E1) ⟨liftHom_injective hn μ J E1 hμ,
    liftHom_surjective hn μ J E1 E2⟩

end Lift


end P135

section P136
open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Spin QuadraticMap
  CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg.SpinPlus CFSG.LieType.RootSystem
  CFSG.LieType.Universal.Spin.PlusCT CFSG.LieType.Steinberg.SpinFrame
  CFSG.AGLEmbeddingD2.ParabLevi CFSG.LieType.BorelTits CFSG.AGLEmbeddingD2.SquareLinear
  CFSG.AGLEmbedding.LeviBlock


section Gamma2

variable {n : ℕ}

theorem Dgamma_add (x y z : Fin n ⊕ Fin n) : Dgamma x y + Dgamma y z = Dgamma x z := by
  funext k
  have h1 := two_mul_Dgamma x y k
  have h2 := two_mul_Dgamma y z k
  have h3 := two_mul_Dgamma x z k
  simp only [Pi.add_apply]
  omega

theorem Dgamma_neg (x y : Fin n ⊕ Fin n) : Dgamma y x = - Dgamma x y := by
  funext k
  have h1 := two_mul_Dgamma x y k
  have h2 := two_mul_Dgamma y x k
  simp only [Pi.neg_apply]
  omega

end Gamma2

section Block

variable {n : ℕ}

structure DBlk (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] where
  pos : ι → Fin n ⊕ Fin n
  nodes : Set (Fin n)
  pos_inj : Function.Injective pos
  pos_swap : ∀ i j, pos i ≠ (pos j).swap
  supp : ∀ u v, ∀ k, k ∉ nodes → Dgamma (pos u) (pos v) k = 0
  gen : ∀ i ∈ nodes, ∃ u v, u ≠ v ∧ Dgamma (pos u) (pos v) = Pi.single i 1

namespace DBlk

variable {ι : Type} [Fintype ι] [DecidableEq ι] (ch : DBlk n ι)

@[expose] def idx : ι → Fin (n + n) := fun i => posEquiv n (ch.pos i)

theorem idx_injective : Function.Injective ch.idx :=
  (posEquiv n).injective.comp ch.pos_inj

theorem idx_disj (i j : ι) : ch.idx i ≠ Fin.rev (ch.idx j) := by
  intro h
  apply ch.pos_swap i j
  apply (posEquiv n).injective
  rw [posEquiv_swap]
  exact h

end DBlk

end Block


end P136

section P137
open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Spin QuadraticMap
  CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg.SpinPlus CFSG.LieType.RootSystem
  CFSG.LieType.Universal.Spin.PlusCT CFSG.LieType.Steinberg.SpinFrame
  CFSG.AGLEmbeddingD2.ParabLevi CFSG.LieType.BorelTits CFSG.AGLEmbeddingD2.SquareLinear
  CFSG.AGLEmbedding.LeviBlock


section ChainGroup

variable {n : ℕ} {F : Type} [Field F] [CharP F 2] (hn : 3 ≤ n) {ι : Type} [Fintype ι]
  [DecidableEq ι] (ch : DBlk n ι)

@[expose] noncomputable def chMu : Matrix.SpecialLinearGroup ι F →*
    Matrix (Fin (n + n)) (Fin (n + n)) F where
  toFun := levMat (RingEquiv.refl F) ch.idx_injective
  map_one' := levMat_one _
  map_mul' := levMat_mul _ ch.idx_disj

theorem chMu_injective : Function.Injective (chMu (F := F) ch) := by
  intro g h hgh
  have key : ∀ g : Matrix.SpecialLinearGroup ι F,
      (chMu ch g).submatrix ch.idx ch.idx = (g : Matrix ι ι F) := by
    intro g
    ext i j
    have haj : ch.idx j ∉ Set.range (Fin.rev ∘ ch.idx) := fun ⟨k, hk⟩ => ch.idx_disj j k hk.symm
    simp only [Matrix.submatrix_apply]
    show levMat (RingEquiv.refl F) ch.idx_injective g (ch.idx i) (ch.idx j) = _
    unfold levMat
    rw [Matrix.mul_apply, Finset.sum_eq_single (ch.idx j)]
    · rw [extendMat_apply_map ch.idx_injective, extendMat_apply_of_not_mem _ _ (Or.inr haj)]
      simp
    · intro t _ ht
      rw [extendMat_apply_of_not_mem _ _ (Or.inr haj), Matrix.one_apply_ne ht, mul_zero]
    · simp
  have h2 := congrArg (fun A => A.submatrix ch.idx ch.idx) hgh
  simp only [key] at h2
  exact Subtype.ext h2

theorem chain_E1 (g : Matrix.SpecialLinearGroup ι F) :
    ∃ t ∈ leviM (plusDatum n F hn) ch.nodes, matD n F t = chMu ch g := by
  classical
  have hct := plusDatum_isCTGroupDatum (K := F) hn (plusDatum_iSup_eq_top n F hn)
  have hg : g ∈ Subgroup.closure (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
      Matrix.TransvectionStruct ι F → Matrix.SpecialLinearGroup ι F)) := by
    rw [Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field]
    exact Subgroup.mem_top _
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨t, rfl⟩ := hx
    obtain ⟨u, v, huv, c⟩ := t
    rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk]
    have hq : ∀ i, (posEquiv n).symm ((1 : Equiv.Perm (Fin (n + n))) (ch.idx i)) = ch.pos i :=
      fun i => by simp [DBlk.idx]
    have hab : ch.idx u ≠ ch.idx v := fun h => huv (ch.idx_injective h)
    have hba : ch.idx v ≠ Fin.rev (ch.idx u) := ch.idx_disj v u
    obtain ⟨t, hr, ht, hm⟩ := exists_rootElt_e hn 1 (fun _ => rfl) hab hba c
    rw [hq, hq] at hr ht
    refine ⟨t, rootGroup_le_leviM hct hr (fun k hk => ch.supp u v k hk) ht, ?_⟩
    rw [matDe_one'] at hm
    show matD n F t = levMat (RingEquiv.refl F) ch.idx_injective _
    rw [levMat_transvection _ ch.idx_disj]
    exact hm
  | one => exact ⟨1, one_mem _, by rw [map_one, map_one]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨t1, h1, e1⟩ := hx
    obtain ⟨t2, h2, e2⟩ := hy
    exact ⟨t1 * t2, mul_mem h1 h2, by rw [map_mul, map_mul, e1, e2]⟩
  | inv x _ hx =>
    obtain ⟨t, ht, e⟩ := hx
    refine ⟨t⁻¹, inv_mem ht, ?_⟩
    have h1 : chMu ch x * chMu ch x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    calc matD n F t⁻¹ = matD n F t⁻¹ * (chMu ch x * chMu ch x⁻¹) := by rw [h1, mul_one]
      _ = (matD n F t⁻¹ * matD n F t) * chMu ch x⁻¹ := by rw [← e, mul_assoc]
      _ = chMu ch x⁻¹ := by rw [← map_mul, inv_mul_cancel, map_one, one_mul]

theorem chain_rootMat {i j : ι} (hij : i ≠ j) {t : spinGroup (quadPlus n F)}
    (ht : t ∈ (plusDatum n F hn).rootGroup (Dgamma (ch.pos i) (ch.pos j))) :
    ∃ c : F, matD n F t = rootMatrix (RingEquiv.refl F) (ch.idx i) (ch.idx j) c :=
  rootMat_of_mem hn (fun h => hij (ch.pos_inj h)) (ch.pos_swap j i) ht

theorem chain_E2 (i : Fin n) (hi : i ∈ ch.nodes) (t : spinGroup (quadPlus n F))
    (ht : t ∈ CFSG.LieType.CurtisTits.rankOne (plusDatum n F hn).rootGroup i) :
    ∃ g, chMu ch g = matD n F t := by
  classical
  obtain ⟨u, v, huv, hdg⟩ := ch.gen i hi
  let T : Subgroup (spinGroup (quadPlus n F)) :=
    { carrier := {t | ∃ g, chMu ch g = matD n F t}
      mul_mem' := by
        rintro a b ⟨g1, h1⟩ ⟨g2, h2⟩
        exact ⟨g1 * g2, by rw [map_mul, map_mul, h1, h2]⟩
      one_mem' := ⟨1, by rw [map_one, map_one]⟩
      inv_mem' := by
        rintro a ⟨g, hg⟩
        refine ⟨g⁻¹, ?_⟩
        have h1 : chMu ch g⁻¹ * chMu ch g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
        calc chMu ch g⁻¹ = chMu ch g⁻¹ * (matD n F a * matD n F a⁻¹) := by
              rw [← map_mul, mul_inv_cancel, map_one, mul_one]
          _ = (chMu ch g⁻¹ * chMu ch g) * matD n F a⁻¹ := by rw [hg, mul_assoc]
          _ = matD n F a⁻¹ := by rw [h1, one_mul] }
  have hpos : CFSG.LieType.CurtisTits.rankOne (plusDatum n F hn).rootGroup i ≤ T := by
    refine sup_le ?_ ?_
    · intro t ht
      have key : ∀ γ : Fin n → ℤ, γ = Dgamma (ch.pos u) (ch.pos v) →
          t ∈ (plusDatum n F hn).rootGroup γ → t ∈ T := by
        intro γ hγ ht
        subst hγ
        obtain ⟨c, hc⟩ := chain_rootMat hn ch huv ht
        refine ⟨Matrix.SpecialLinearGroup.transvection huv c, ?_⟩
        show levMat (RingEquiv.refl F) ch.idx_injective _ = _
        rw [levMat_transvection _ ch.idx_disj, hc]
      exact key _ hdg.symm ht
    · intro t ht
      have key : ∀ γ : Fin n → ℤ, γ = Dgamma (ch.pos v) (ch.pos u) →
          t ∈ (plusDatum n F hn).rootGroup γ → t ∈ T := by
        intro γ hγ ht
        subst hγ
        obtain ⟨c, hc⟩ := chain_rootMat hn ch huv.symm ht
        refine ⟨Matrix.SpecialLinearGroup.transvection huv.symm c, ?_⟩
        show levMat (RingEquiv.refl F) ch.idx_injective _ = _
        rw [levMat_transvection _ ch.idx_disj, hc]
      refine key _ ?_ ht
      rw [Dgamma_neg, hdg]
      rfl
  exact hpos ht

@[expose] noncomputable def chEquiv : Matrix.SpecialLinearGroup ι F ≃*
    ↥(leviM (plusDatum n F hn) ch.nodes) :=
  liftEquiv hn (chMu ch) ch.nodes (chain_E1 hn ch) (chMu_injective ch) (chain_E2 hn ch)

end ChainGroup


end P137

section P138
open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Spin QuadraticMap
  CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg.SpinPlus CFSG.LieType.RootSystem
  CFSG.LieType.Universal.Spin.PlusCT CFSG.LieType.Steinberg.SpinFrame
  CFSG.AGLEmbeddingD2.ParabLevi CFSG.LieType.BorelTits CFSG.AGLEmbeddingD2.SquareLinear
  CFSG.AGLEmbedding.LeviBlock


section SimpleDgamma

variable {n : ℕ}

theorem Dgamma_inl_succ (c : Fin n) (hc : c.val + 1 < n) :
    Dgamma (Sum.inl c : Fin n ⊕ Fin n) (Sum.inl ⟨c.val + 1, hc⟩) = Pi.single c 1 := by
  funext k
  have h1 := two_mul_Dgamma (Sum.inl c : Fin n ⊕ Fin n) (Sum.inl ⟨c.val + 1, hc⟩) k
  have hk := k.isLt
  simp only [mvec, Sum.elim_inl] at h1
  rw [Pi.single_apply]
  split_ifs at h1 with a1 a2 a3 a4 a5 a6 <;> simp_all [Fin.ext_iff] <;> omega

theorem Dgamma_flag (hn : 3 ≤ n) :
    Dgamma (Sum.inl ⟨n - 2, by omega⟩ : Fin n ⊕ Fin n) (Sum.inr ⟨n - 1, by omega⟩) =
      Pi.single ⟨n - 1, by omega⟩ 1 := by
  funext k
  have h1 := two_mul_Dgamma (Sum.inl ⟨n - 2, by omega⟩ : Fin n ⊕ Fin n) (Sum.inr ⟨n - 1, by omega⟩) k
  have hk := k.isLt
  simp only [mvec, Sum.elim_inl, Sum.elim_inr] at h1
  rw [Pi.single_apply]
  split_ifs at h1 with a1 a2 a3 a4 a5 a6 <;> simp_all [Fin.ext_iff] <;> omega

end SimpleDgamma


end P138

section P139
open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Spin QuadraticMap
  CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg.SpinPlus CFSG.LieType.RootSystem
  CFSG.LieType.Universal.Spin.PlusCT CFSG.LieType.Steinberg.SpinFrame
  CFSG.AGLEmbeddingD2.ParabLevi CFSG.LieType.BorelTits CFSG.AGLEmbeddingD2.SquareLinear
  CFSG.AGLEmbedding.LeviBlock


section DBlock

variable {n a k : ℕ} (h : a + k = n)

include h

@[expose] def embD : Fin k → Fin n := fun c => ⟨a + c.val, by have := c.isLt; omega⟩

theorem embD_injective : Function.Injective (embD h) := fun c d e => by
  apply Fin.ext
  have := congrArg Fin.val e
  simp only [embD] at this
  omega

@[expose] def tauD : Fin k ⊕ Fin k → Fin n ⊕ Fin n := Sum.map (embD h) (embD h)

theorem tauD_injective : Function.Injective (tauD h) :=
  Sum.map_injective.mpr ⟨embD_injective h, embD_injective h⟩

theorem tauD_swap (z : Fin k ⊕ Fin k) : tauD h z.swap = (tauD h z).swap := by
  rcases z with c | c <;> rfl

@[expose] def iotaD : Fin (k + k) → Fin (n + n) :=
  fun w => posEquiv n (tauD h ((posEquiv k).symm w))

theorem iotaD_injective : Function.Injective (iotaD h) :=
  (posEquiv n).injective.comp ((tauD_injective h).comp (posEquiv k).symm.injective)

theorem iotaD_rev (w : Fin (k + k)) : iotaD h (Fin.rev w) = Fin.rev (iotaD h w) := by
  unfold iotaD
  have : (posEquiv k).symm (Fin.rev w) = ((posEquiv k).symm w).swap := by
    apply (posEquiv k).injective
    rw [Equiv.apply_symm_apply, posEquiv_swap, Equiv.apply_symm_apply]
  rw [this, tauD_swap, posEquiv_swap]

end DBlock




section DBlockMu

variable {n a k : ℕ} {F : Type} [Field F] [CharP F 2] (h : a + k = n) (hn : 3 ≤ n) (hk : 3 ≤ k)

include h

@[expose] noncomputable def blkMu : spinGroup (quadPlus k F) →* Matrix (Fin (n + n)) (Fin (n + n)) F :=
  (extendHom (F := F) (iotaD_injective h)).comp (matD k F)

theorem blkMu_apply (s : spinGroup (quadPlus k F)) :
    blkMu h s = extendMat (iotaD_injective h) (matD k F s) := rfl

theorem blkMu_injective : Function.Injective (blkMu (F := F) h) := by
  intro s s' hss
  apply matD_injective CharTwo.two_eq_zero
  have h2 := congrArg (fun A => A.submatrix (iotaD h) (iotaD h)) hss
  simp only [blkMu_apply, submatrix_extendMat] at h2
  exact h2

@[expose] def blkNodes (n a : ℕ) : Set (Fin n) := {j | a ≤ j.val}

theorem mvec_tauD_zero (z : Fin k ⊕ Fin k) (j : Fin n) (hj : j.val < a) (hk3 : 3 ≤ k) :
    mvec (tauD h z) j = 0 := by
  have := j.isLt
  rcases z with c | c <;>
  · simp only [tauD, Sum.map_inl, Sum.map_inr, mvec, embD, Sum.elim_inl, Sum.elim_inr]
    split_ifs <;> omega

theorem Dgamma_tauD_supp (x y : Fin k ⊕ Fin k) (j : Fin n) (hj : j.val < a) (hk3 : 3 ≤ k) :
    Dgamma (tauD h x) (tauD h y) j = 0 := by
  have h1 := two_mul_Dgamma (tauD h x) (tauD h y) j
  rw [mvec_tauD_zero h x j hj hk3, mvec_tauD_zero h y j hj hk3] at h1
  omega

end DBlockMu


section DBlockE

variable {n a k : ℕ} {F : Type} [Field F] [CharP F 2] (h : a + k = n) (hn : 3 ≤ n) (hk : 3 ≤ k)

include h

theorem tauD_ne {x y : Fin k ⊕ Fin k} (hxy : x ≠ y) (hyx : y ≠ x.swap) :
    tauD h x ≠ tauD h y ∧ tauD h y ≠ (tauD h x).swap :=
  ⟨fun e => hxy (tauD_injective h e), fun e => hyx (tauD_injective h (by rw [tauD_swap]; exact e))⟩

theorem posEquiv_tauD (x : Fin k ⊕ Fin k) :
    posEquiv n (tauD h x) = iotaD h (posEquiv k x) := by
  simp [iotaD]

theorem blkMu_rootMatrix {x y : Fin k ⊕ Fin k} (c : F) :
    extendMat (iotaD_injective h) (rootMatrix (RingEquiv.refl F) (posEquiv k x) (posEquiv k y) c) =
      rootMatrix (RingEquiv.refl F) (posEquiv n (tauD h x)) (posEquiv n (tauD h y)) c := by
  rw [extendMat_rootMatrix (iotaD_injective h) (iotaD_rev h), posEquiv_tauD h, posEquiv_tauD h]

include hk in
theorem blk_E1 (s : spinGroup (quadPlus k F)) :
    ∃ t ∈ leviM (plusDatum n F hn) (blkNodes n a), matD n F t = blkMu h s := by
  classical
  have hct := plusDatum_isCTGroupDatum (K := F) hn (plusDatum_iSup_eq_top n F hn)
  let S : Subgroup (spinGroup (quadPlus k F)) :=
    { carrier := {s | ∃ t ∈ leviM (plusDatum n F hn) (blkNodes n a), matD n F t = blkMu h s}
      mul_mem' := by
        rintro s1 s2 ⟨t1, h1, e1⟩ ⟨t2, h2, e2⟩
        exact ⟨t1 * t2, mul_mem h1 h2, by rw [map_mul, map_mul, e1, e2]⟩
      one_mem' := ⟨1, one_mem _, by rw [map_one, map_one]⟩
      inv_mem' := by
        rintro s1 ⟨t1, h1, e1⟩
        refine ⟨t1⁻¹, inv_mem h1, ?_⟩
        have h3 : blkMu h s1 * blkMu h s1⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
        calc matD n F t1⁻¹ = matD n F t1⁻¹ * (blkMu h s1 * blkMu h s1⁻¹) := by rw [h3, mul_one]
          _ = (matD n F t1⁻¹ * matD n F t1) * blkMu h s1⁻¹ := by rw [← e1, mul_assoc]
          _ = blkMu h s1⁻¹ := by rw [← map_mul, inv_mul_cancel, map_one, one_mul] }
  have hgen := plusDatum_iSup_eq_top k F hk
  have htop : (⊤ : Subgroup (spinGroup (quadPlus k F))) ≤ S := by
    rw [← hgen]
    refine iSup₂_le fun γ hγ s hs => ?_
    obtain ⟨x, y, hxy, hyx, rfl⟩ := exists_Dgamma_of_root hk hγ
    obtain ⟨c, hc⟩ := rootMat_of_mem hk hxy hyx hs
    obtain ⟨hne1, hne2⟩ := tauD_ne h hxy hyx
    obtain ⟨t, hr, ht, hm⟩ := exists_rootMat hn hne1 hne2 c
    refine ⟨t, rootGroup_le_leviM hct hr (fun j hj => ?_) ht, ?_⟩
    · have : j.val < a := by
        by_contra hcon
        exact hj (show a ≤ j.val by omega)
      exact Dgamma_tauD_supp h x y j this hk
    · rw [hm, blkMu_apply, hc, blkMu_rootMatrix h]
  exact htop (Subgroup.mem_top s)




include hn hk in
theorem blk_simple (i : Fin n) (hi : a ≤ i.val) :
    ∃ x' y' : Fin k ⊕ Fin k, x' ≠ y' ∧ y' ≠ x'.swap ∧
      Dgamma (tauD h x') (tauD h y') = Pi.single i 1 := by
  have hi' := i.isLt
  by_cases hc : i.val + 1 < n
  · refine ⟨Sum.inl ⟨i.val - a, by omega⟩, Sum.inl ⟨i.val + 1 - a, by omega⟩, ?_, ?_, ?_⟩
    · intro e; have := Sum.inl.inj e; simp [Fin.ext_iff] at this; omega
    · intro e; simp at e
    · have e1 : tauD h (Sum.inl ⟨i.val - a, by omega⟩) = Sum.inl i := by
        simp only [tauD, Sum.map_inl, embD]; congr 1; apply Fin.ext; simp; omega
      have e2 : tauD h (Sum.inl ⟨i.val + 1 - a, by omega⟩ : Fin k ⊕ Fin k) =
          Sum.inl ⟨i.val + 1, hc⟩ := by
        simp only [tauD, Sum.map_inl, embD]; congr 1; apply Fin.ext; simp; omega
      rw [e1, e2]
      exact Dgamma_inl_succ i hc
  · have hin : i.val + 1 = n := by omega
    refine ⟨Sum.inl ⟨n - 2 - a, by omega⟩, Sum.inr ⟨n - 1 - a, by omega⟩, ?_, ?_, ?_⟩
    · intro e; simp at e
    · intro e; simp at e; omega
    · have e1 : tauD h (Sum.inl ⟨n - 2 - a, by omega⟩ : Fin k ⊕ Fin k) =
          Sum.inl ⟨n - 2, by omega⟩ := by
        simp only [tauD, Sum.map_inl, embD]; congr 1; apply Fin.ext; simp; omega
      have e2 : tauD h (Sum.inr ⟨n - 1 - a, by omega⟩ : Fin k ⊕ Fin k) =
          Sum.inr ⟨n - 1, by omega⟩ := by
        simp only [tauD, Sum.map_inr, embD]; congr 1; apply Fin.ext; simp; omega
      rw [e1, e2, Dgamma_flag hn]
      have : i = ⟨n - 1, by omega⟩ := Fin.ext (by simp; omega)
      rw [this]

include hk in
theorem blk_pair {x' y' : Fin k ⊕ Fin k} (hxy : x' ≠ y') (hyx : y' ≠ x'.swap)
    {t : spinGroup (quadPlus n F)}
    (ht : t ∈ (plusDatum n F hn).rootGroup (Dgamma (tauD h x') (tauD h y'))) :
    ∃ s, blkMu h s = matD n F t := by
  obtain ⟨hne1, hne2⟩ := tauD_ne h hxy hyx
  obtain ⟨c, hc⟩ := rootMat_of_mem hn hne1 hne2 ht
  obtain ⟨s, -, -, hs⟩ := exists_rootMat (n := k) (F := F) hk hxy hyx c
  refine ⟨s, ?_⟩
  rw [blkMu_apply, hs, blkMu_rootMatrix h, hc]

end DBlockE

section DBlockE2

variable {n a k : ℕ} {F : Type} [Field F] [CharP F 2] (h : a + k = n) (hn : 3 ≤ n) (hk : 3 ≤ k)

include h hk

theorem blk_E2 (i : Fin n) (hi : i ∈ blkNodes n a) (t : spinGroup (quadPlus n F))
    (ht : t ∈ CFSG.LieType.CurtisTits.rankOne (plusDatum n F hn).rootGroup i) :
    ∃ s, blkMu h s = matD n F t := by
  classical
  let T : Subgroup (spinGroup (quadPlus n F)) :=
    { carrier := {t | ∃ s, blkMu h s = matD n F t}
      mul_mem' := by
        rintro a1 b ⟨g1, h1⟩ ⟨g2, h2⟩
        exact ⟨g1 * g2, by rw [map_mul, map_mul, h1, h2]⟩
      one_mem' := ⟨1, by rw [map_one, map_one]⟩
      inv_mem' := by
        rintro a1 ⟨g, hg⟩
        refine ⟨g⁻¹, ?_⟩
        have h1 : blkMu h g⁻¹ * blkMu h g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
        calc blkMu h g⁻¹ = blkMu h g⁻¹ * (matD n F a1 * matD n F a1⁻¹) := by
              rw [← map_mul, mul_inv_cancel, map_one, mul_one]
          _ = (blkMu h g⁻¹ * blkMu h g) * matD n F a1⁻¹ := by rw [hg, mul_assoc]
          _ = matD n F a1⁻¹ := by rw [h1, one_mul] }
  obtain ⟨x', y', hxy, hyx, hdg⟩ := blk_simple h hn hk i hi
  have hyx' : x' ≠ y'.swap := fun e => hyx (by rw [e]; simp)
  have hle : CFSG.LieType.CurtisTits.rankOne (plusDatum n F hn).rootGroup i ≤ T := by
    refine sup_le ?_ ?_
    · intro t ht
      have key : ∀ γ : Fin n → ℤ, γ = Dgamma (tauD h x') (tauD h y') →
          t ∈ (plusDatum n F hn).rootGroup γ → t ∈ T := by
        intro γ hγ ht
        subst hγ
        exact blk_pair h hn hk hxy hyx ht
      exact key _ hdg.symm ht
    · intro t ht
      have key : ∀ γ : Fin n → ℤ, γ = Dgamma (tauD h y') (tauD h x') →
          t ∈ (plusDatum n F hn).rootGroup γ → t ∈ T := by
        intro γ hγ ht
        subst hγ
        exact blk_pair h hn hk hxy.symm hyx' ht
      refine key _ ?_ ht
      rw [Dgamma_neg, hdg]
      rfl
  exact hle ht


@[expose] noncomputable def blkEquiv : spinGroup (quadPlus k F) ≃* ↥(leviM (plusDatum n F hn) (blkNodes n a)) :=
  liftEquiv hn (blkMu (F := F) h) (blkNodes n a) (blk_E1 h hn hk) (blkMu_injective h) (blk_E2 (F := F) h hn hk)

end DBlockE2


end P139

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
